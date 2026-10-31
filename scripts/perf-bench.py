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
the newest export corpus (`../gofv-corpus/<pin12>`, as scripts/parity.sh picks it) under
<profiler worktree>/tmp/bench-corpus/<id>, id = hash of its stats.txt and manifest.txt. The
exporter regenerates the corpus in place of the original, so benchmarks never read it directly;
a new corpus gives a new snapshot, and perf-compare.py only compares rows of the same corpus.
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
    cid = corpus_id(src)
    base = here / "tmp" / "bench-corpus"
    dst = base / cid
    if not (dst / "COMPLETE").exists():
        shutil.rmtree(dst, ignore_errors=True)
        dst.mkdir(parents=True)
        shutil.copytree(src / "plain", dst / "plain", symlinks=True)
        for f in ("stats.txt", "manifest.txt"):
            shutil.copy2(src / f, dst / f)
        if corpus_id(src) != cid:  # regenerated while copying
            shutil.rmtree(dst)
            sys.exit(f"perf-bench: corpus {src} changed while copying; retry later")
        (dst / "COMPLETE").write_text(f"{src}\n")
        for old in sorted(base.iterdir(), key=lambda d: d.stat().st_mtime)[:-2]:
            shutil.rmtree(old)  # keep the two newest snapshots
    return dst, cid


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("names", nargs="*")
    ap.add_argument("--root", default=".")
    ap.add_argument("--registry", default=str(here / "perf/bench.tsv"))
    ap.add_argument("--history", default=str(here / "perf/bench-history.tsv"))
    ap.add_argument("--runs", type=int, default=1)
    ap.add_argument("--cap", default="8G")
    ap.add_argument("--min-avail", type=float, default=10, help="GB; wait while below")
    ap.add_argument("--force", action="store_true", help="rerun benchmarks of known binaries")
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
    env = dict(os.environ, FV_MEMCAP=a.cap, GOFV_BENCH_CORPUS=str(cdir))
    hist = pathlib.Path(a.history)
    known = {}  # (bench, bin_hash) -> latest ok row
    if hist.exists():
        lines = hist.read_text().splitlines()
        for line in lines[1:]:
            r = dict(zip(lines[0].split("\t"), line.split("\t")))
            if r.get("status") == "ok" and r.get("bin_hash"):
                known[(r["bench"], r["bin_hash"])] = r
        if lines and lines[0].split("\t") != COLUMNS:
            sys.exit(f"perf-bench: {hist} has columns {lines[0].split()}; expected {COLUMNS}")
    rows, bad = [], 0
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
                print(f"{name}: cached (binary measured at {k['commit']})")
                continue
            results = []
            for i in range(a.runs):
                while mem_available() < a.min_avail * GiB:
                    time.sleep(60)
                row["load1"] = f"{os.getloadavg()[0]:.1f}"
                out = scratch / f"{name}.json"
                out.unlink(missing_ok=True)
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
            if results:
                results.sort(key=lambda r: r["wall_s"])
                med = results[len(results) // 2]
                row.update(wall_s=f"{med['wall_s']:.2f}", cpu_s=f"{med['cpu_s']:.2f}",
                           maxrss_mb=max(r["maxrss"] for r in results) // 2 ** 20, runs=len(results))
            row.setdefault("status", "ok")
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
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
