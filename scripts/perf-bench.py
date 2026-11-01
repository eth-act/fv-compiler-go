#!/usr/bin/env python3
"""Runtime benchmarks of compiled Lean executables, appended to perf/bench-history.tsv
(docs/PERF.md).

usage: scripts/perf-bench.py [--root DIR] [--registry perf/bench.tsv] [--runs 1] [NAME...]

The registry lists one benchmark per line: `name<TAB>lake target<TAB>shell command`. For each,
`lake build <target>` runs first (status `missing` if that fails, e.g. at commits before the
executable existed); then the command runs --runs times from the worktree root, each in its own
scripts/memcap.sh scope via perf-record.py's probe. The row keeps the median wall time, the CPU
time of that run and the largest max RSS. Run the binary directly (`.lake/build/bin/x`), not
through `lake exe`: lake's own ~0.45 GB would dominate the RSS of small runs.

A benchmark whose binary (`.lake/build/bin/<target>`, sha256), command and corpus were already
measured is not rerun: the earlier numbers are copied with status `cached` (--force reruns).

Corpus: commands read `$GOFV_BENCH_CORPUS` (e.g. `"$GOFV_BENCH_CORPUS/plain"`), a private copy of
the newest quick export corpus (`../gofv-corpus/<pin12>/plain`, as scripts/parity.sh picks it;
since #116 a symlink to a versioned `quick-vN/plain` whose directory holds stats.txt and
manifest.txt) under <profiler worktree>/tmp/bench-corpus/<id>, id = hash of stats.txt and
manifest.txt. Old versions can be removed while a benchmark runs, so benchmarks never read the
original; a new corpus gives a new snapshot, and perf-compare.py only compares rows of the
same corpus.
Exit status 1 of a command means "ran, found mismatches" for the difftest/parity runners; wrap
them as `cmd || [ $? -eq 1 ]` so only crashes count as `fail`.

Columns: date commit bench status wall_s cpu_s maxrss_mb runs load1 bin_hash corpus
"""
import argparse, datetime, hashlib, json, os, pathlib, re, shutil, subprocess, sys, time

here = pathlib.Path(__file__).resolve().parent.parent
COLUMNS = ["date", "commit", "bench", "status", "wall_s", "cpu_s", "maxrss_mb", "runs", "load1",
           "bin_hash", "corpus"]
GiB = 1024 ** 3


def mem_available():
    for line in open("/proc/meminfo"):
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    return 0


def corpus_id(src):
    h = hashlib.sha256()
    for f in ("stats.txt", "manifest.txt"):
        h.update((src / f).read_bytes())
    return h.hexdigest()[:12]


def snapshot(src):
    """Private copy of corpus `src` (its plain/ tree); returns (dir, id)."""
    if src is None:
        main_root = pathlib.Path(subprocess.run(
            ["git", "-C", str(here), "worktree", "list", "--porcelain"], check=True,
            capture_output=True, text=True).stdout.splitlines()[0].split(" ", 1)[1])
        pins = [d for d in (main_root.parent / "gofv-corpus").glob("*")
                if re.fullmatch(r"[0-9a-f]{12}", d.name) and (d / "plain").is_dir()]
        if not pins:
            sys.exit("perf-bench: no corpus under ../gofv-corpus")
        src = max(pins, key=lambda d: d.stat().st_mtime)
    src = pathlib.Path(src)
    if (src / "plain").is_symlink():  # versioned layout: <pin>/plain -> quick-vN/plain
        src = (src / "plain").resolve().parent
    base = here / "tmp" / "bench-corpus"

    def newest_complete(why):
        done = [d for d in base.glob("*") if (d / "COMPLETE").exists()] if base.is_dir() else []
        if not done:
            sys.exit(f"perf-bench: {why}, and no earlier snapshot")
        d = max(done, key=lambda d: (d / "COMPLETE").stat().st_mtime)
        print(f"perf-bench: {why}; using the previous snapshot {d.name}")
        return d, d.name
    try:
        cid = corpus_id(src)
    except OSError:  # being regenerated (stats.txt/manifest.txt are written last)
        return newest_complete(f"corpus {src} incomplete")
    dst = base / cid
    if not (dst / "COMPLETE").exists():
        shutil.rmtree(dst, ignore_errors=True)
        dst.mkdir(parents=True)
        try:
            shutil.copytree(src / "plain", dst / "plain", symlinks=True)
            for f in ("stats.txt", "manifest.txt"):
                shutil.copy2(src / f, dst / f)
            same = corpus_id(src) == cid
        except (OSError, shutil.Error):
            same = False
        if not same:  # regenerated while copying
            shutil.rmtree(dst)
            return newest_complete(f"corpus {src} changed while copying")
        (dst / "COMPLETE").write_text(f"{src}\n")
        for old in sorted(base.iterdir(), key=lambda d: d.stat().st_mtime)[:-2]:
            shutil.rmtree(old)  # keep the two newest snapshots
    return dst, cid


PASS_COLUMNS = ["date", "commit", "bench", "pass", "time_s", "runs", "corpus", "bin_hash"]


def pass_times(text):
    """Per-pass times from the last markdown table with a `pass time (s)` column (pass-parity
    prints one per run: time spent in each registered pass instance, parsing excluded)."""
    out, cols = {}, None
    for line in text.splitlines():
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if "pass time (s)" in cells:
            cols, out = cells, {}
        elif cols and len(cells) == len(cols) and not cells[0].startswith("---"):
            try:
                out[cells[cols.index("pass")]] = float(cells[cols.index("pass time (s)")])
            except ValueError:
                pass
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("names", nargs="*")
    ap.add_argument("--root", default=".")
    ap.add_argument("--registry", default=str(here / "perf/bench.tsv"))
    ap.add_argument("--history", default=str(here / "perf/bench-history.tsv"))
    ap.add_argument("--pass-history", default=str(here / "perf/pass-history.tsv"))
    ap.add_argument("--pass-abs", type=float, default=1.0,
                    help="s; a pass time moving more than this and 25%% triggers extra runs")
    ap.add_argument("--runs", type=int, default=1)
    ap.add_argument("--cap", default="8G")
    ap.add_argument("--min-avail", type=float, default=10, help="GB; wait while below")
    ap.add_argument("--force", action="store_true", help="rerun benchmarks of known binaries")
    ap.add_argument("--gate-max-fail", type=float, default=0.01,
                    help="fraction of corpus files the gate may fail (default 1%%)")
    ap.add_argument("--corpus", default=None,
                    help="export corpus to snapshot (default: newest ../gofv-corpus/<pin12>)")
    a = ap.parse_args()
    root = pathlib.Path(a.root).resolve()
    memcap = root / "scripts/memcap.sh"
    memcap = memcap if memcap.exists() else here / "scripts/memcap.sh"
    commit = subprocess.run(["git", "-C", str(root), "rev-parse", "--short=12", "HEAD"],
                            check=True, capture_output=True, text=True).stdout.strip()
    if subprocess.run(["git", "-C", str(root), "status", "--porcelain", "--untracked-files=no"],
                      capture_output=True, text=True).stdout.strip():
        commit += "+dirty"
    benches, gate = [], None
    for line in pathlib.Path(a.registry).read_text().splitlines():
        if line.strip() and not line.startswith("#"):
            name, target, cmd = line.split("\t", 2)
            gate = gate or name  # the first entry: the corpus must parse at this commit
            if not a.names or name in a.names:
                benches.append((name, target, cmd))
    if not benches:
        print(f"perf-bench: no benchmarks selected from {a.registry}")
        return 0
    scratch = root / "tmp" / "perf-bench"
    scratch.mkdir(parents=True, exist_ok=True)
    cdir, cid = snapshot(a.corpus)
    env = dict(os.environ, FV_MEMCAP=a.cap, GOFV_BENCH_CORPUS=str(cdir), TMPDIR=str(scratch))
    hist = pathlib.Path(a.history)
    known = {}  # (bench, bin_hash) -> latest ok row
    prev_cpu = {}  # (bench, corpus) -> CPU of the latest ok measurement
    if hist.exists():
        lines = hist.read_text().splitlines()
        for line in lines[1:]:
            r = dict(zip(lines[0].split("\t"), line.split("\t")))
            if r.get("status") == "ok" and r.get("bin_hash"):
                known[(r["bench"], r["bin_hash"])] = r
                prev_cpu[(r["bench"], r.get("corpus"))] = float(r["cpu_s"])
        if lines and lines[0].split("\t") != COLUMNS:
            sys.exit(f"perf-bench: {hist} has columns {lines[0].split()}; expected {COLUMNS}")
    phist = pathlib.Path(a.pass_history)
    pknown = {}  # (bench, bin_hash) -> {pass: row}
    prev_pass = {}  # (bench, corpus, pass) -> latest time
    if phist.exists():
        lines = phist.read_text().splitlines()
        if lines and lines[0].split("\t") != PASS_COLUMNS:
            sys.exit(f"perf-bench: {phist} has columns {lines[0].split()}; expected {PASS_COLUMNS}")
        for line in lines[1:]:
            r = dict(zip(PASS_COLUMNS, line.split("\t")))
            pknown.setdefault((r["bench"], r["bin_hash"]), {})[r["pass"]] = r
            prev_pass[(r["bench"], r["corpus"], r["pass"])] = float(r["time_s"])
    rows, prows, bad = [], [], 0
    gate_failed = False
    for name, target, cmd in benches:
        log = open(scratch / f"{name}.log", "w")
        row = dict(bench=name, runs=0, corpus=cid)
        if gate_failed:
            row["status"] = "skipped"
            rows.append(row)
            print(f"{name}: skipped (gate {gate} failed: corpus not parsable at this commit?)")
            continue
        if subprocess.run([str(memcap), "lake", "build", target], cwd=root, env=env,
                          stdout=log, stderr=subprocess.STDOUT).returncode != 0:
            row["status"] = "missing"
        else:
            exe = root / ".lake/build/bin" / target
            h = hashlib.sha256()
            h.update(cmd.encode() + b"\0" + cid.encode() + b"\0")
            if exe.is_file():
                h.update(exe.read_bytes())
            row["bin_hash"] = h.hexdigest()[:16]
            k = known.get((name, row["bin_hash"]))
            if k and not a.force:
                row.update({c: k[c] for c in ("wall_s", "cpu_s", "maxrss_mb", "runs", "load1")},
                           status="cached")
                rows.append(row)
                for pr in pknown.get((name, row["bin_hash"]), {}).values():
                    prows.append(dict(pr))
                print(f"{name}: cached (binary measured at {k['commit']})")
                continue
            results, per_pass = [], []
            i = 0
            while i < a.runs:
                i += 1
                while mem_available() < a.min_avail * GiB:
                    time.sleep(60)
                row["load1"] = f"{os.getloadavg()[0]:.1f}"
                out = scratch / f"{name}.json"
                out.unlink(missing_ok=True)
                log.flush()
                start = log.seek(0, 2)  # children write to the fd directly
                rc = subprocess.run([str(memcap), sys.executable, str(here / "scripts/perf-record.py"),
                                     "--probe", str(out), "--", "bash", "-c", cmd],
                                    cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT).returncode
                try:
                    res = json.loads(out.read_text())
                except (OSError, ValueError):
                    res = None
                if rc != 0 or res is None:
                    row["status"] = "oom" if rc in (137, 143) or res is None else "fail"
                    break
                results.append(res)
                with open(scratch / f"{name}.log", errors="replace") as lf:
                    lf.seek(start)
                    pt = pass_times(lf.read())
                if pt:
                    per_pass.append(pt)
                p = prev_cpu.get((name, cid))
                moved = [s for s, t in pt.items()
                         if (q := prev_pass.get((name, cid, s))) is not None
                         and abs(t - q) > max(0.25 * q, a.pass_abs)]
                if i == a.runs and len(results) < 3 and (
                        (p and abs(res["cpu_s"] - p) > 0.25 * p) or moved):
                    # single runs vary by ~30% under load (pass-parity: 71.5 vs 99.6 s CPU on the
                    # same binary): confirm a move past the threshold with a median of three
                    print(f"{name}: CPU {p} -> {res['cpu_s']:.1f}s"
                          + (f", passes moved: {', '.join(moved)}" if moved else "")
                          + "; two more runs")
                    i -= 3 - len(results)
            if per_pass:
                for s in per_pass[-1]:
                    ts = sorted(pp[s] for pp in per_pass if s in pp)
                    prows.append(dict(bench=name, **{"pass": s}, time_s=f"{ts[len(ts) // 2]:.2f}",
                                      runs=len(ts), corpus=cid, bin_hash=row["bin_hash"]))
            if results:
                results.sort(key=lambda r: r["cpu_s"])
                med = results[len(results) // 2]
                row.update(wall_s=f"{med['wall_s']:.2f}", cpu_s=f"{med['cpu_s']:.2f}",
                           maxrss_mb=max(r["maxrss"] for r in results) // 2 ** 20, runs=len(results))
            row.setdefault("status", "ok")
            if name == gate and row["status"] == "ok":
                # the gate command accepts exit 1 (some files fail); judge its summary line
                # `ssa-roundtrip: N files, M failed`: the exporter can run ahead of main's parser
                # (37/9297 files with new `zvar` lines), which must not void every benchmark
                text = (scratch / f"{name}.log").read_text(errors="replace")
                mm = re.findall(r"(\d+) files, (\d+) failed", text)
                if mm and int(mm[-1][1]) > a.gate_max_fail * int(mm[-1][0]):
                    row["status"] = "unparsable"
                    print(f"{name}: {mm[-1][1]}/{mm[-1][0]} files failed "
                          f"(> {a.gate_max_fail:.0%}): corpus not parsable at this commit")
        bad += row["status"] != "ok"
        gate_failed = name == gate and row["status"] != "ok"
        rows.append(row)
        print(f"{name}: {row['status']} {row.get('wall_s', '-')}s cpu {row.get('cpu_s', '-')}s "
              f"rss {row.get('maxrss_mb', '-')}M ({row['runs']} runs; log {scratch / (name + '.log')})")
    hist = pathlib.Path(a.history)
    new = not hist.exists()
    date = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    with open(hist, "a") as f:
        if new:
            f.write("\t".join(COLUMNS) + "\n")
        for r in rows:
            r.update(date=date, commit=commit)
            f.write("\t".join(str(r.get(c, "")) for c in COLUMNS) + "\n")
    if prows:
        new = not phist.exists()
        with open(phist, "a") as f:
            if new:
                f.write("\t".join(PASS_COLUMNS) + "\n")
            for r in prows:
                r.update(date=date, commit=commit)
                f.write("\t".join(str(r.get(c, "")) for c in PASS_COLUMNS) + "\n")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
