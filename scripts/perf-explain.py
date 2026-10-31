#!/usr/bin/env python3
"""Name the declarations that make a module slow (docs/PERF.md).

usage: scripts/perf-explain.py [--root DIR] [--threshold MS] [--top N] [--cap 8G] MODULE

Builds MODULE's imports (`lake build +MODULE`, free when cached), then elaborates the file once
more under scripts/memcap.sh with `-Dtrace.profiler=true -Dprofiler=true`, and prints the
top-level trace.profiler entries (one per declaration step: elaboration, kernel check of
`foo._proof_1`, …) above the threshold, slowest first, followed by Lean's cumulative profile
by category. Raw output: tmp/perf-explain/<MODULE>.log.
"""
import argparse, os, pathlib, re, subprocess, sys

here = pathlib.Path(__file__).resolve().parent.parent
LINE = re.compile(r"^\[([\w.]+)\] \[([\d.]+)\] \S+\s+(.*)$")
# An Elab.command message is the command's source; skip doc comments/attributes to its keyword.
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|"
                  r"nonrec)\s+)*((?:inductive|structure|class|def|theorem|lemma|abbrev|instance|"
                  r"opaque|axiom|example|deriving instance|#eval|#guard_msgs|#print)\b.*)$")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("module")
    ap.add_argument("--root", default=".")
    ap.add_argument("--threshold", type=int, default=100, help="ms")
    ap.add_argument("--top", type=int, default=15)
    ap.add_argument("--cap", default="8G")
    a = ap.parse_args()
    root = pathlib.Path(a.root).resolve()
    memcap = root / "scripts/memcap.sh"
    memcap = memcap if memcap.exists() else here / "scripts/memcap.sh"
    src = pathlib.Path(*a.module.split(".")).with_suffix(".lean")
    if not (root / src).exists():
        sys.exit(f"perf-explain: {root / src} not found")
    env = dict(os.environ, FV_MEMCAP=a.cap)
    out = root / "tmp" / "perf-explain"
    out.mkdir(parents=True, exist_ok=True)
    log = out / f"{a.module}.log"
    r = subprocess.run([str(memcap), "lake", "build", "+" + a.module], cwd=root, env=env,
                       capture_output=True, text=True)
    if r.returncode != 0:
        print(r.stdout[-3000:] + r.stderr[-3000:], file=sys.stderr)
        sys.exit(f"perf-explain: lake build +{a.module} failed ({r.returncode})")
    with open(log, "w") as f:
        rc = subprocess.run([str(memcap), "lake", "env", "lean", "-Dtrace.profiler=true",
                             f"-Dtrace.profiler.threshold={a.threshold}", "-Dprofiler=true",
                             f"-Dprofiler.threshold={a.threshold}", str(src)],
                            cwd=root, env=env, stdout=f, stderr=subprocess.STDOUT).returncode
    text = log.read_text(errors="replace")
    entries = []
    lines = text.splitlines()
    for i, line in enumerate(lines):
        m = LINE.match(line)  # unindented: top-level entries only
        if m:
            what = m.group(3)
            if not DECL.match(what):
                for cont in lines[i + 1:i + 40]:
                    if not cont.startswith("    "):
                        break
                    d = DECL.match(cont)
                    if d:
                        what = d.group(1)
                        break
            entries.append((float(m.group(2)), m.group(1), what[:160]))
    entries.sort(reverse=True)
    print(f"{a.module}: {len(entries)} top-level profiler entries >= {a.threshold} ms "
          f"(sum {sum(e[0] for e in entries):.1f} s); lean exit {rc}; log {log}")
    for secs, cls, what in entries[:a.top]:
        print(f"  {secs:8.2f}s  {cls:22} {what}")
    if "cumulative profiling times:" in text:
        cum = text.split("cumulative profiling times:", 1)[1].strip().splitlines()
        vals = []
        for l in cum:
            m = re.match(r"\s*(.+?) ([\d.]+)(ms|s)$", l)
            if m:
                vals.append((float(m.group(2)) / (1000 if m.group(3) == "ms" else 1), m.group(1)))
        vals.sort(reverse=True)
        print("  cumulative: " + ", ".join(f"{n} {v:.1f}s" for v, n in vals[:6]))
    return rc


if __name__ == "__main__":
    sys.exit(main())
