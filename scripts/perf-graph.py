#!/usr/bin/env python3
"""Import-graph view of a recorded commit (docs/PERF.md): the critical path and rebuild cones.

usage: scripts/perf-graph.py [--top N] COMMIT

Reads the import graph of COMMIT from git (every tracked *.lean file; no checkout needed) and
the commit's CPU times from perf/history.tsv, and prints

  * the critical path: the import chain with the largest summed CPU time, i.e. the modelled
    cold-build time with unlimited parallelism, module by module;
  * the costliest rebuild cones: for each module, how many modules import it transitively and
    their summed CPU time (what any change to it, e.g. a statement edit, costs every worktree
    that rebuilds). clifv cut its cold build 1,370 → 425 s by removing unused imports and
    moving shared lemmas into lower modules, guided by exactly these two lists (eth-act/clifv#726).
"""
import argparse, pathlib, re, subprocess, sys

here = pathlib.Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^(?:public\s+|meta\s+|private\s+)*import\s+(?:all\s+)?(\S+)", re.M)


def graph_at(repo, commit):
    """module -> list of imported local modules, from the tracked files of `commit`."""
    files = subprocess.run(["git", "-C", str(repo), "ls-tree", "-r", "--name-only", commit],
                           check=True, capture_output=True, text=True).stdout.split()
    files = [f for f in files if f.endswith(".lean")]
    req = "".join(f"{commit}:{f}\n" for f in files)
    out = subprocess.run(["git", "-C", str(repo), "cat-file", "--batch"], input=req.encode(),
                         check=True, capture_output=True).stdout
    texts, pos = {}, 0
    for f in files:
        nl = out.index(b"\n", pos)
        n = int(out[pos:nl].split()[2])
        texts[f] = out[nl + 1:nl + 1 + n].decode(errors="replace")
        pos = nl + 1 + n + 1
    mods = {f[:-5].replace("/", "."): t for f, t in texts.items()}
    return {m: [d for d in IMPORT.findall(t) if d in mods and d != m] for m, t in mods.items()}


def load_cpu(history, commit):
    lines = pathlib.Path(history).read_text().splitlines()
    cols = lines[0].split("\t")
    rows = [dict(zip(cols, l.split("\t"))) for l in lines[1:] if l]
    mine = [r for r in rows if r["commit"] == commit]
    if not mine:
        return None
    last = max(r["date"] for r in mine)
    cpu = {}
    for r in mine:
        if r["date"] == last and r["module"] != "_total":
            try:
                cpu[r["module"]] = float(r["cpu_s"])
            except ValueError:
                cpu[r["module"]] = 0.0
    return cpu


def critical(imports, cpu):
    """(chain from the first import to the sink, its total CPU) over the recorded modules."""
    best, prev = {}, {}

    def visit(m):
        if m not in best:
            ds = [d for d in imports.get(m, []) if d in cpu]
            for d in ds:
                visit(d)
            p = max(ds, key=lambda d: best[d], default=None)
            prev[m], best[m] = p, cpu[m] + (best[p] if p else 0.0)
    sys.setrecursionlimit(max(1000, 4 * len(cpu)))
    for m in cpu:
        visit(m)
    if not best:
        return [], 0.0
    m = max(best, key=lambda x: best[x])
    total, chain = best[m], []
    while m:
        chain.append(m)
        m = prev[m]
    return chain[::-1], total


def chain_for(commit, history=here / "perf/history.tsv", repo=here):
    cpu = load_cpu(history, commit)
    if not cpu:
        return []
    return critical(graph_at(repo, commit), cpu)[0]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("commit")
    ap.add_argument("--top", type=int, default=10)
    ap.add_argument("--history", default=str(here / "perf/history.tsv"))
    ap.add_argument("--repo", default=str(here))
    a = ap.parse_args()
    commit = subprocess.run(["git", "-C", a.repo, "rev-parse", "--short=12", a.commit],
                            check=True, capture_output=True, text=True).stdout.strip()
    cpu = load_cpu(a.history, commit)
    if cpu is None:
        sys.exit(f"perf-graph: {commit} not recorded in {a.history}")
    imports = graph_at(a.repo, commit)
    chain, total = critical(imports, cpu)
    print(f"{commit}: {len(cpu)} modules, serial CPU {sum(cpu.values()):.0f} s, "
          f"critical path {total:.0f} s CPU over {len(chain)} modules:")
    for m in chain:
        print(f"  {cpu[m]:7.1f} s  {m}")
    rdeps = {m: [] for m in imports}
    for m, ds in imports.items():
        for d in ds:
            rdeps[d].append(m)
    cones = []
    for m in cpu:
        seen, todo = set(), [m]
        while todo:
            x = todo.pop()
            for r in rdeps.get(x, []):
                if r not in seen:
                    seen.add(r); todo.append(r)
        cones.append((cpu[m] + sum(cpu.get(r, 0.0) for r in seen), len(seen), m))
    cones.sort(reverse=True)
    print(f"\nCostliest rebuild cones (a change to M rebuilds M and its importers):")
    for cost, n, m in cones[:a.top]:
        print(f"  {cost:7.0f} s CPU  {n:4} importers  {m}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
