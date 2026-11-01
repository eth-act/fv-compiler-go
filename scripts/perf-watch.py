#!/usr/bin/env python3
"""One pass of the profiler's watch loop (docs/PERF.md).

usage: scripts/perf-watch.py [--dry-run] [--only main|PR_NUMBER ...]

Fetches origin, then profiles origin/main and the head of every open PR against main that has
no recording yet in perf/history.tsv: each commit is checked out (detached) in the profiler's
build worktree ../fv-compiler-go-wt/lean-profiler-run and recorded with scripts/perf-record.py
(shared Lake cache: unchanged modules cost a cache restore) and scripts/perf-bench.py. Then:

  * main: compared with the latest recorded first-parent ancestor;
  * PR:   compared with its merge base with origin/main (recorded first if needed).

Each comparison is written to perf/raw/reports/<main|prN>-<commit>.md; the paths of new
reports, and whether they flag a regression, are printed. Posting them is up to the caller.
"""
import argparse, json, os, pathlib, re, subprocess, sys

here = pathlib.Path(__file__).resolve().parent.parent
HISTORY = here / "perf/history.tsv"
REPORTS = here / "perf/raw/reports"


def sh(*cmd, cwd=here, check=True):
    return subprocess.run(cmd, cwd=cwd, check=check, capture_output=True, text=True).stdout.strip()


def recorded():
    if not HISTORY.exists():
        return set()
    return {l.split("\t")[1] for l in HISTORY.read_text().splitlines()[1:] if l and "\t" in l}


def short(sha):
    return sh("git", "rev-parse", "--short=12", sha)


def run_worktree():
    main_root = pathlib.Path(sh("git", "worktree", "list", "--porcelain").splitlines()[0].split(" ", 1)[1])
    wt = main_root.parent / "fv-compiler-go-wt" / "lean-profiler-run"
    if not wt.exists():
        sh("git", "worktree", "add", "--detach", str(wt), "origin/main")
    for d in ("go", "go-build"):  # as scripts/agent-worktree.sh
        src, dst = main_root / "third_party" / d, wt / "third_party" / d
        if src.exists() and not dst.exists():
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.symlink_to(src)
    return wt


def record(wt, sha, dry):
    s = short(sha)
    if s in recorded():
        return True
    print(f"perf-watch: recording {s}", flush=True)
    if dry:
        return False
    sh("git", "checkout", "--quiet", "--detach", "--force", sha, cwd=wt)
    r1 = subprocess.run([sys.executable, str(here / "scripts/perf-record.py"), "--root", str(wt),
                         "--history", str(HISTORY)], cwd=wt)
    # the profiler's registry (not the commit's): benchmarks added later apply to older commits too
    subprocess.run([sys.executable, str(here / "scripts/perf-bench.py"), "--root", str(wt),
                    "--registry", str(here / "perf/bench.tsv")], cwd=wt)
    return s in recorded() or r1.returncode == 0


def ab_cpu(wt, base, head, module, rounds=2):
    """Interleaved A/B re-timing (base, head, base, head, …) of one module's elaboration in the
    build worktree; returns (min CPU at base, min CPU at head). Back-to-back confirmation runs of
    the recorder share one load period; alternating commits cancels it."""
    import importlib.util, json, re as _re
    spec = importlib.util.spec_from_file_location("perf_record", here / "scripts/perf-record.py")
    pr = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(pr)
    tmp = wt / "tmp" / "perf-ab"
    tmp.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, TMPDIR=str(tmp), FV_MEMCAP="8G")
    memcap = here / "scripts/memcap.sh"
    times = {base: [], head: []}
    for _ in range(rounds):
        for c in (base, head):
            sh("git", "checkout", "--quiet", "--detach", "--force", c, cwd=wt)
            libs, mods, _imp = pr.load_modules(wt)
            if module not in mods:
                return None
            extra = pr.lib_args(wt, libs).get(module, [])
            subprocess.run([str(memcap), "lake", "build", "+" + module], cwd=wt, env=env,
                           capture_output=True)
            out = tmp / "probe.json"
            out.unlink(missing_ok=True)
            subprocess.run([str(memcap), sys.executable, str(here / "scripts/perf-record.py"),
                            "--probe", str(out), "--", "lake", "lean",
                            str(mods[module].relative_to(wt)), "--", *extra,
                            "-o", str(tmp / "x.olean")], cwd=wt, env=env, capture_output=True)
            try:
                times[c].append(json.loads(out.read_text())["cpu_s"])
            except (OSError, ValueError, KeyError):
                return None
    return min(times[base]), min(times[head])


def compare(base, head, label, header, wt=None):
    REPORTS.mkdir(parents=True, exist_ok=True)
    out = REPORTS / f"{label}-{short(head)}.md"
    if out.exists():
        return None
    cmd = [sys.executable, str(here / "scripts/perf-compare.py"), short(base), short(head)]
    r = subprocess.run(cmd, capture_output=True, text=True)
    notes = []
    if r.returncode == 1 and wt is not None:
        # module time flags: confirm by interleaved A/B; drop the ones that do not reproduce
        flagged = re.findall(r"^\| `([\w.]+)` \| time \|", r.stdout, re.M)
        noise = []
        for m in flagged:
            ab = ab_cpu(wt, base, head, m)
            if ab is None:
                continue
            cb, ch = ab
            real = ch > cb * 1.25 and ch - cb > 5
            notes.append(f"- A/B re-timing of `{m}` (interleaved, min of 2 each): "
                         f"{cb:.1f} s → {ch:.1f} s CPU: {'confirmed' if real else 'noise, dropped'}")
            if not real:
                noise.append(m)
        if noise:
            r = subprocess.run(cmd + [f"--ignore={m}" for m in noise], capture_output=True, text=True)
    out.write_text(header + "\n\n" + r.stdout + r.stderr + ("\n" + "\n".join(notes) + "\n" if notes else ""))
    return out, r.returncode == 1


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--only", nargs="*", help="main and/or PR numbers")
    a = ap.parse_args()
    sh("git", "fetch", "--quiet", "--prune", "origin")
    prs = json.loads(sh("gh", "pr", "list", "--state", "open", "--base", "main", "--json",
                        "number,headRefOid,headRefName,title,url"))
    wt = run_worktree()
    new = []
    main_sha = sh("git", "rev-parse", "origin/main")
    if a.only is None or "main" in a.only:
        record(wt, main_sha, a.dry_run)
        prev = next((c for c in sh("git", "rev-list", "--first-parent", "--max-count=200",
                                   main_sha).split()[1:] if short(c) in recorded()), None)
        if prev and short(main_sha) in recorded():
            log = sh("git", "log", "--oneline", "--first-parent", f"{prev}..{main_sha}")
            res = compare(prev, main_sha, "main", f"main `{short(prev)}` → `{short(main_sha)}`:\n"
                          + "\n".join("    " + l for l in log.splitlines()), wt=wt)
            if res:
                new.append(res)
    for pr in prs:
        if a.only is not None and str(pr["number"]) not in a.only:
            continue
        head = pr["headRefOid"]
        if subprocess.run(["git", "cat-file", "-e", head + "^{commit}"], cwd=here).returncode != 0:
            sh("git", "fetch", "--quiet", "origin", f"pull/{pr['number']}/head")
        base = sh("git", "merge-base", main_sha, head)
        if (REPORTS / f"pr{pr['number']}-{short(head)}.md").exists():
            continue
        if not (record(wt, base, a.dry_run) and record(wt, head, a.dry_run)):
            continue
        res = compare(base, head, f"pr{pr['number']}",
                      f"PR #{pr['number']} ({pr['headRefName']}: {pr['title']}) {pr['url']}", wt=wt)
        if res:
            new.append(res)
    for path, regressed in new:
        print(f"perf-watch: {'REGRESSION' if regressed else 'ok'} {path}")
    if not new:
        print("perf-watch: nothing new")
    return 0


if __name__ == "__main__":
    sys.exit(main())
