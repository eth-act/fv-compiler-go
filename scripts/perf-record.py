#!/usr/bin/env python3
"""Per-module Lean build profile of one commit, appended to perf/history.tsv (docs/PERF.md).

usage: scripts/perf-record.py [options] [TARGET...]

TARGET is a module (`GoFV.SSA.Op`), a prefix ending in `.` (`GoFV.Rules.`) or a library name
(default: every lean_lib in lakefile.toml). The targets and their local imports are built one
module at a time, in import order, each in its own scripts/memcap.sh scope:

    scripts/memcap.sh python3 scripts/perf-record.py --probe OUT.json -- lake build M

The probe runs inside the scope and records wall time, CPU time (user+sys of lake and lean),
max RSS of the largest process (ru_maxrss, i.e. the lean process) and the scope's cgroup
`memory.peak` (empty when memcap.sh had to use its /proc watchdog fallback). Module selection
and import parsing follow clifv's scripts/lake-serial-build.py.

Modules Lake restores from the shared cache (no "Built M" line) are not rebuilt: if the history
already holds a measurement for the same Lake input hash (`depHash` of M's .trace), its numbers
are copied with status `cached`; otherwise the module is re-elaborated once into tmp/ with
`lake env lean` (status `remeasured`), so every row of a recorded commit carries numbers.

A module killed at its cap is retried once at --retry-cap under `flock ../gofv-heavy.lock`
(AGENTS.md: scopes above 8G only under that lock). Nothing starts while MemAvailable is below
--min-avail; the recorder waits instead.

Columns of perf/history.tsv (one row per commit and module, plus `_total`):
  date commit module status wall_s cpu_s maxrss_mb cgpeak_mb olean_kb dep_hash measured_at load1
"""
import argparse, datetime, json, os, pathlib, re, resource, subprocess, sys, time, tomllib

GiB = 1024 ** 3
COLUMNS = ["date", "commit", "module", "status", "wall_s", "cpu_s", "maxrss_mb", "cgpeak_mb",
           "olean_kb", "dep_hash", "measured_at", "load1"]
MEASURED = ("built", "remeasured")


def size(s):
    s = s.strip().upper()
    mult = {"G": GiB, "M": 1024 ** 2, "K": 1024}
    return int(float(s[:-1]) * mult[s[-1]]) if s[-1] in mult else int(s)


def mem_available():
    for line in open("/proc/meminfo"):
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    return 0


# ---------------------------------------------------------------------------------------------
# probe: runs inside the memcap scope


def own_scope():
    """cgroup directory of this process if it is a memcap.sh systemd scope, else None."""
    try:
        cg = next(l[3:] for l in open("/proc/self/cgroup").read().splitlines() if l.startswith("0::"))
    except (OSError, StopIteration):
        return None
    d = pathlib.Path("/sys/fs/cgroup" + cg)
    if not re.search(r"\.slice/run-[^/]+\.scope$", cg) or not (d / "memory.peak").exists():
        return None
    return d


def lean_hwm(me):
    """Largest VmHWM (peak RSS) among the `lean` processes below pid `me`."""
    best, todo = 0, [me]
    while todo:
        p = todo.pop()
        try:
            for t in os.listdir(f"/proc/{p}/task"):
                with open(f"/proc/{p}/task/{t}/children") as f:
                    todo.extend(map(int, f.read().split()))
            if p != me and open(f"/proc/{p}/comm").read().strip() == "lean":
                st = open(f"/proc/{p}/status").read()
                best = max(best, int(re.search(r"VmHWM:\s+(\d+)", st).group(1)) * 1024)
        except (OSError, AttributeError):
            pass
    return best


def probe(out, cmd):
    """Run cmd; peak RSS of the lean process (VmHWM polled every 0.1 s: lake itself holds
    ~0.45 GB, which ru_maxrss would report for every small module) and the scope's memory.peak."""
    scope = own_scope()
    t0 = time.monotonic()
    child = subprocess.Popen(cmd)
    hwm = 0
    while child.poll() is None:
        hwm = max(hwm, lean_hwm(os.getpid()))
        time.sleep(0.1)
    rc = child.returncode
    wall = time.monotonic() - t0
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    peak = None
    if scope is not None:
        try:
            peak = int((scope / "memory.peak").read_text())
        except (OSError, ValueError):
            pass
    pathlib.Path(out).write_text(json.dumps({
        "rc": rc, "wall_s": wall, "cpu_s": ru.ru_utime + ru.ru_stime,
        "maxrss": hwm or ru.ru_maxrss * 1024, "cgpeak": peak}))
    return rc if rc >= 0 else 128 - rc


# ---------------------------------------------------------------------------------------------
# module graph (as clifv's lake-serial-build.py, plus Lake's glob semantics: `X.+` is X's
# submodules without X, `X.*` X and its submodules, a bare name one module; no globs: the
# lib's roots and their local imports)

IMPORT = re.compile(r"^(?:public\s+|meta\s+|private\s+)*import\s+(?:all\s+)?(\S+)")


def parse_imports(p):
    return [mm.group(1) for line in p.read_text(errors="replace").splitlines()
            if (mm := IMPORT.match(line))]


def load_modules(root):
    cfg = tomllib.loads((root / "lakefile.toml").read_text())
    libs, mods = {}, {}
    for lib in cfg.get("lean_lib", []):
        base = root / lib.get("srcDir", ".")

        def path(m):
            return base / pathlib.Path(*m.split(".")).with_suffix(".lean")

        def below(n):
            d = base / pathlib.Path(*n.split("."))
            return {".".join(p.relative_to(base).with_suffix("").parts): p
                    for p in d.rglob("*.lean")} if d.is_dir() else {}
        sel = {}
        if "globs" in lib:
            for g in lib["globs"]:
                n = g[:-2] if g.endswith((".+", ".*")) else g
                if not g.endswith(".+") and path(n).exists():
                    sel[n] = path(n)
                if g.endswith((".+", ".*")):
                    sel.update(below(n))
        else:
            todo = list(lib.get("roots", [lib["name"]]))
            while todo:
                m = todo.pop()
                if m not in sel and path(m).exists():
                    sel[m] = path(m)
                    todo.extend(parse_imports(sel[m]))
        libs[lib["name"]] = set(sel)
        mods.update(sel)
    imports = {m: [d for d in parse_imports(p) if d in mods] for m, p in mods.items()}
    return libs, mods, imports


def select(targets, libs, mods, imports):
    roots = set()
    for t in targets:
        if t in libs:
            roots |= libs[t]
        elif t.endswith("."):
            roots |= {m for m in mods if m.startswith(t)}
        elif t in mods:
            roots.add(t)
        else:
            sys.exit(f"perf-record: unknown target {t}")
    order, state = [], {}

    def visit(m):  # iterative DFS post-order: imports before importers
        stack = [(m, iter(sorted(imports[m])))]
        state[m] = 1
        while stack:
            x, it = stack[-1]
            d = next(it, None)
            if d is None:
                stack.pop(); state[x] = 2; order.append(x)
            elif d not in state:
                state[d] = 1
                stack.append((d, iter(sorted(imports[d]))))
            elif state[d] == 1:
                sys.exit(f"perf-record: import cycle through {d}")
    for m in sorted(roots):
        if m not in state:
            visit(m)
    return order


# ---------------------------------------------------------------------------------------------
# history


def read_history(path):
    rows = []
    if path.exists():
        for line in path.read_text().splitlines():
            if line and not line.startswith(("#", "date\t")):
                f = line.split("\t")
                rows.append(dict(zip(COLUMNS, f + [""] * (len(COLUMNS) - len(f)))))
    return rows


def append_rows(path, rows):
    new = not path.exists()
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "a") as f:
        if new:
            f.write("\t".join(COLUMNS) + "\n")
        for r in rows:
            f.write("\t".join(str(r.get(c, "")) for c in COLUMNS) + "\n")


# ---------------------------------------------------------------------------------------------


def git(root, *args):
    return subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True,
                          text=True).stdout.strip()


def build_dir(root):
    return root / ".lake" / "build"


def olean_kb(root, m):
    d = build_dir(root) / "lib" / "lean" / pathlib.Path(*m.split(".")).parent
    stem = m.split(".")[-1]
    n = sum(p.stat().st_size for p in d.glob(stem + ".olean*") if not p.name.endswith(".hash"))
    return round(n / 1024) if n else ""


def dep_hash(root, m):
    t = build_dir(root) / "lib" / "lean" / pathlib.Path(*m.split(".")).with_suffix(".trace")
    try:
        return json.loads(t.read_text()).get("depHash", "")
    except (OSError, ValueError):
        return ""


def main():
    if len(sys.argv) > 2 and sys.argv[1] == "--probe":
        if sys.argv[3] != "--":
            sys.exit("usage: perf-record.py --probe OUT.json -- CMD...")
        return probe(sys.argv[2], sys.argv[4:])

    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("targets", nargs="*")
    ap.add_argument("--root", default=".", help="worktree to build (default: cwd)")
    here = pathlib.Path(__file__).resolve().parent.parent
    ap.add_argument("--history", default=str(here / "perf/history.tsv"))
    ap.add_argument("--raw", default=None, help="log dir (default <history dir>/raw/<commit>)")
    ap.add_argument("--cap", default="8G", help="memcap per module")
    ap.add_argument("--retry-cap", default="16G", help="cap of the one retry after an OOM kill")
    ap.add_argument("--min-avail", default="10G", help="wait while MemAvailable is below")
    ap.add_argument("--force", action="store_true", help="record even if the commit has rows")
    ap.add_argument("--no-remeasure", action="store_true",
                    help="leave cache-restored modules without a known measurement empty")
    a = ap.parse_args()

    root = pathlib.Path(a.root).resolve()
    memcap = root / "scripts" / "memcap.sh"
    if not memcap.exists():
        memcap = here / "scripts" / "memcap.sh"
    history = pathlib.Path(a.history).resolve()
    commit = git(root, "rev-parse", "--short=12", "HEAD")
    if git(root, "status", "--porcelain", "--untracked-files=no"):
        commit += "+dirty"
    raw = pathlib.Path(a.raw or history.parent / "raw" / commit).resolve()
    raw.mkdir(parents=True, exist_ok=True)
    scratch = root / "tmp" / "perf-record"
    scratch.mkdir(parents=True, exist_ok=True)

    libs, mods, imports = load_modules(root)
    order = select(a.targets or list(libs), libs, mods, imports)
    old = read_history(history)
    if not a.force and any(r["commit"] == commit for r in old):
        print(f"perf-record: {commit} already in {history} (--force to re-record)")
        return 0
    known = {}  # depHash -> latest measured row
    for r in old:
        if r["status"] in MEASURED and r["dep_hash"]:
            known[r["dep_hash"]] = r
    log = open(raw / "record.log", "a")

    def say(s):
        line = time.strftime("%H:%M:%S ") + s
        log.write(line + "\n"); log.flush()
        print(line, flush=True)

    def gate(need):
        waited = False
        while mem_available() < need:
            if not waited:
                say(f"waiting: MemAvailable {mem_available() / GiB:.1f}G < {need / GiB:.0f}G")
                waited = True
            time.sleep(60)

    def run(m, cmd, cap, heavy=False):
        out = scratch / f"{m}.json"
        out.unlink(missing_ok=True)
        full = [str(memcap), sys.executable, str(pathlib.Path(__file__).resolve()),
                "--probe", str(out), "--", *cmd]
        if heavy:  # next to the shared Lake cache: ../gofv-heavy.lock of the main checkout
            main_root = git(root, "worktree", "list", "--porcelain").splitlines()[0].split(" ", 1)[1]
            full = ["flock", str(pathlib.Path(main_root).parent / "gofv-heavy.lock"), *full]
        env = dict(os.environ, FV_MEMCAP=cap)
        log_path = raw / f"{m}.log"
        with open(log_path, "a") as f:
            start = f.tell()
            f.write(f"$ {' '.join(full)}\n"); f.flush()
            rc = subprocess.run(full, cwd=root, env=env, stdout=f, stderr=subprocess.STDOUT).returncode
        with open(log_path, errors="replace") as f:
            f.seek(start)
            text = f.read()
        try:
            res = json.loads(out.read_text())
        except (OSError, ValueError):
            res = None  # the scope was killed with the probe in it
        return rc, res, text

    say(f"record {commit} in {root}: {len(order)} modules -> {history}")
    rows, status = [], {}
    min_avail = size(a.min_avail)
    for m in order:
        if any(status.get(d) != "ok" for d in imports[m]):
            status[m] = "blocked"
            rows.append(dict(module=m, status="blocked"))
            say(f"{m}: blocked")
            continue
        gate(min_avail)
        load1 = os.getloadavg()[0]
        # `+M` names the module (a bare `GoFV` would be the library)
        rc, res, text = run(m, ["lake", "build", "+" + m], a.cap)
        killed = rc in (137, 143) or res is None or re.search(r"signal 9|exit code 137|Killed", text)
        if rc != 0 and killed:
            say(f"{m}: killed at {a.cap}, retrying alone at {a.retry_cap}")
            gate(size(a.retry_cap) + 2 * GiB)
            load1 = os.getloadavg()[0]
            rc, res, text = run(m, ["lake", "build", "+" + m], a.retry_cap, heavy=True)
            killed = rc in (137, 143) or res is None
        built = re.search(r"Built " + re.escape(m) + r"(?![\w.])", text) is not None
        row = dict(module=m, load1=f"{load1:.1f}")
        if rc != 0:
            status[m] = "fail"
            row["status"] = "oom" if killed else "fail"
            if res:
                row.update(wall_s=f"{res['wall_s']:.1f}", maxrss_mb=res["maxrss"] // 2 ** 20)
            rows.append(row)
            say(f"{m}: {row['status']} rc={rc} (log {raw / (m + '.log')})")
            continue
        status[m] = "ok"
        h = dep_hash(root, m)
        row.update(olean_kb=olean_kb(root, m), dep_hash=h)
        if not built and h in known:
            k = known[h]
            row.update({c: k[c] for c in ("wall_s", "cpu_s", "maxrss_mb", "cgpeak_mb", "load1")},
                       status="cached", measured_at=k["measured_at"] or k["commit"])
        elif not built and a.no_remeasure:
            row["status"] = "cached"
        else:
            if not built:  # restored from the cache, never measured: elaborate once into tmp/
                gate(min_avail)
                row["load1"] = f"{os.getloadavg()[0]:.1f}"
                stem = scratch / m
                rc2, res, _ = run(m, ["lake", "env", "lean", str(mods[m].relative_to(root)),
                                      "-o", f"{stem}.olean", "-i", f"{stem}.ilean",
                                      "-c", f"{stem}.c"], a.cap)
                for ext in (".olean", ".ilean", ".c"):
                    pathlib.Path(f"{stem}{ext}").unlink(missing_ok=True)
                if rc2 != 0 or res is None:
                    row["status"] = "cached"
                    say(f"{m}: cached; remeasure failed rc={rc2}")
                    rows.append(row)
                    continue
            row.update(status="built" if built else "remeasured", measured_at=commit,
                       wall_s=f"{res['wall_s']:.1f}", cpu_s=f"{res['cpu_s']:.1f}",
                       maxrss_mb=res["maxrss"] // 2 ** 20,
                       cgpeak_mb="" if res["cgpeak"] is None else res["cgpeak"] // 2 ** 20)
            known[h] = dict(row, commit=commit)
        rows.append(row)
        say(f"{m}: {row['status']} {row.get('wall_s', '?')}s cpu {row.get('cpu_s', '?')}s "
            f"rss {row.get('maxrss_mb', '?')}M cg {row.get('cgpeak_mb', '?')}M "
            f"olean {row.get('olean_kb', '?')}K")

    num = [r for r in rows if r.get("wall_s") not in (None, "") and r["status"] in
           ("built", "remeasured", "cached")]
    total = dict(module="_total", status="ok" if all(v == "ok" for v in status.values()) else "fail",
                 wall_s=f"{sum(float(r['wall_s']) for r in num):.1f}",
                 cpu_s=f"{sum(float(r['cpu_s'] or 0) for r in num):.1f}",
                 maxrss_mb=max((int(r["maxrss_mb"]) for r in num), default=""),
                 cgpeak_mb=max((int(r["cgpeak_mb"]) for r in num if r["cgpeak_mb"] != ""), default=""),
                 olean_kb=sum(int(r["olean_kb"] or 0) for r in rows if r.get("olean_kb") not in (None, "")),
                 measured_at=commit)
    rows.append(total)
    date = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    for r in rows:
        r.setdefault("commit", commit)
        r["date"] = date
    append_rows(history, rows)
    bad = [m for m, s in status.items() if s != "ok"]
    say(f"END {commit}: {len(order) - len(bad)}/{len(order)} ok; module sum {total['wall_s']}s, "
        f"max rss {total['maxrss_mb']}M" + (f"; not ok: {' '.join(bad)}" if bad else ""))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
