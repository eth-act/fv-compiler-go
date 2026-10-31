#!/usr/bin/env python3
"""Runtime benchmarks of compiled Lean executables, appended to perf/bench-history.tsv
(docs/PERF.md).

usage: scripts/perf-bench.py [--root DIR] [--registry perf/bench.tsv] [--runs 3] [NAME...]

The registry lists one benchmark per line: `name<TAB>lake target<TAB>shell command`. For each,
`lake build <target>` runs first (status `missing` if that fails, e.g. at commits before the
executable existed); then the command runs --runs times from the worktree root, each in its own
scripts/memcap.sh scope via perf-record.py's probe. The row keeps the median wall time, the CPU
time of that run and the largest max RSS. Run the binary directly (`.lake/build/bin/x`), not
through `lake exe`: lake's own ~0.45 GB would dominate the RSS of small runs.

Columns: date commit bench status wall_s cpu_s maxrss_mb runs load1
"""
import argparse, datetime, json, os, pathlib, subprocess, sys, time

here = pathlib.Path(__file__).resolve().parent.parent
COLUMNS = ["date", "commit", "bench", "status", "wall_s", "cpu_s", "maxrss_mb", "runs", "load1"]
GiB = 1024 ** 3


def mem_available():
    for line in open("/proc/meminfo"):
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("names", nargs="*")
    ap.add_argument("--root", default=".")
    ap.add_argument("--registry", default=str(here / "perf/bench.tsv"))
    ap.add_argument("--history", default=str(here / "perf/bench-history.tsv"))
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--cap", default="8G")
    ap.add_argument("--min-avail", type=float, default=10, help="GB; wait while below")
    a = ap.parse_args()
    root = pathlib.Path(a.root).resolve()
    memcap = root / "scripts/memcap.sh"
    memcap = memcap if memcap.exists() else here / "scripts/memcap.sh"
    commit = subprocess.run(["git", "-C", str(root), "rev-parse", "--short=12", "HEAD"],
                            check=True, capture_output=True, text=True).stdout.strip()
    if subprocess.run(["git", "-C", str(root), "status", "--porcelain", "--untracked-files=no"],
                      capture_output=True, text=True).stdout.strip():
        commit += "+dirty"
    benches = []
    for line in pathlib.Path(a.registry).read_text().splitlines():
        if line.strip() and not line.startswith("#"):
            name, target, cmd = line.split("\t", 2)
            if not a.names or name in a.names:
                benches.append((name, target, cmd))
    if not benches:
        print(f"perf-bench: no benchmarks selected from {a.registry}")
        return 0
    scratch = root / "tmp" / "perf-bench"
    scratch.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, FV_MEMCAP=a.cap)
    rows, bad = [], 0
    for name, target, cmd in benches:
        log = open(scratch / f"{name}.log", "w")
        row = dict(bench=name, runs=0)
        if subprocess.run([str(memcap), "lake", "build", target], cwd=root, env=env,
                          stdout=log, stderr=subprocess.STDOUT).returncode != 0:
            row["status"] = "missing"
        else:
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
