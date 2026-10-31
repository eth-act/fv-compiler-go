#!/usr/bin/env python3
"""Compare two recorded commits of perf/history.tsv (and perf/bench-history.tsv); docs/PERF.md.

usage: scripts/perf-compare.py [options] BASE HEAD

BASE/HEAD are git refs (resolved in --repo) or commit ids as written in the history
(12 hex digits, optionally `+dirty`). The latest recording of each commit is used.
Prints a Markdown report (for PR comments) and exits 1 when it flags a regression:

  * module peak RSS (lean VmHWM, `maxrss_mb`) grew > --pct % and > --rss-abs MB;
  * module time grew > --pct % and > --time-abs s, in wall time *and* CPU time (CPU filters
    wall-clock noise from machine load);
  * a module that failed or was killed at its cap in HEAD but built in BASE;
  * a new module above --new-rss MB or --new-time s;
  * a benchmark whose wall time or max RSS grew > --pct % and > --bench-time-abs s /
    --bench-rss-abs MB.
Shrinks past the same thresholds are listed as wins.
"""
import argparse, pathlib, subprocess, sys

here = pathlib.Path(__file__).resolve().parent.parent


def load(path):
    rows = []
    if path.exists():
        lines = path.read_text().splitlines()
        cols = lines[0].split("\t") if lines else []
        for line in lines[1:]:
            if line and not line.startswith("#"):
                f = line.split("\t")
                rows.append(dict(zip(cols, f + [""] * (len(cols) - len(f)))))
    return rows


def latest(rows, commit, key):
    """key -> row of the latest recording (largest date) of `commit`."""
    mine = [r for r in rows if r["commit"] == commit]
    if not mine:
        return None
    last = max(r["date"] for r in mine)
    return {r[key]: r for r in mine if r["date"] == last}


def resolve(repo, ref, known):
    if ref in known:
        return ref
    try:
        return subprocess.run(["git", "-C", str(repo), "rev-parse", "--short=12", ref + "^{commit}"],
                              check=True, capture_output=True, text=True).stdout.strip()
    except subprocess.CalledProcessError:
        sys.exit(f"perf-compare: unknown commit {ref}")


def num(r, k):
    try:
        return float(r[k])
    except (KeyError, ValueError, TypeError):
        return None


def grew(b, h, pct, absolute):
    return b is not None and h is not None and h > b * (1 + pct / 100) and h - b > absolute


def fmt(v, unit):
    if v is None:
        return "–"
    return f"{v / 1024:.2f} GB" if unit == "MB" and v >= 1024 else f"{v:.0f} MB" if unit == "MB" \
        else f"{v:.1f} s"


def change(b, h):
    return f"{(h - b) / b * 100:+.0f}%" if b else "new"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("base")
    ap.add_argument("head")
    ap.add_argument("--history", default=str(here / "perf/history.tsv"))
    ap.add_argument("--bench-history", default=str(here / "perf/bench-history.tsv"))
    ap.add_argument("--repo", default=str(here))
    ap.add_argument("--pct", type=float, default=25)
    ap.add_argument("--rss-abs", type=float, default=512, help="MB")
    ap.add_argument("--time-abs", type=float, default=5, help="s")
    ap.add_argument("--new-rss", type=float, default=2048, help="MB")
    ap.add_argument("--new-time", type=float, default=60, help="s")
    ap.add_argument("--bench-time-abs", type=float, default=1, help="s")
    ap.add_argument("--bench-rss-abs", type=float, default=256, help="MB")
    ap.add_argument("--all", action="store_true", help="also list unflagged changed modules")
    a = ap.parse_args()

    hist = load(pathlib.Path(a.history))
    bhist = load(pathlib.Path(a.bench_history))
    known = {r["commit"] for r in hist + bhist}
    base, head = resolve(a.repo, a.base, known), resolve(a.repo, a.head, known)
    B, H = latest(hist, base, "module"), latest(hist, head, "module")
    if B is None or H is None:
        sys.exit(f"perf-compare: no recording of {base if B is None else head} in {a.history}")

    reg, win, info = [], [], []
    for m in sorted(H.keys() - {"_total"}):
        h, b = H[m], B.get(m)
        if b is None:
            r, t = num(h, "maxrss_mb"), num(h, "wall_s")
            bad = h["status"] in ("fail", "oom", "blocked")
            if bad or (r or 0) > a.new_rss or (t or 0) > a.new_time:
                reg.append((m, "new module", "–", (h["status"] + ", " if bad else "")
                            + f"{fmt(t, 's')}, {fmt(r, 'MB')}", "new"))
            continue
        if h["status"] in ("fail", "oom") and b["status"] not in ("fail", "oom", "blocked"):
            reg.append((m, "build", b["status"], f"{h['status']} (rss {h['maxrss_mb'] or '?'} MB)", "broken"))
            continue
        if h.get("measured_at") and h.get("measured_at") == b.get("measured_at"):
            continue  # same measurement (module unchanged, numbers copied from the cache)
        rb, rh = num(b, "maxrss_mb"), num(h, "maxrss_mb")
        wb, wh, cb, ch = num(b, "wall_s"), num(h, "wall_s"), num(b, "cpu_s"), num(h, "cpu_s")
        cpu_ok = cb is None or ch is None
        for (x, y, lst) in ((rb, rh, reg), (rh, rb, win)):
            if grew(x, y, a.pct, a.rss_abs):
                lst.append((m, "peak RSS", fmt(rb, "MB"), fmt(rh, "MB"), change(rb, rh)))
        for (x, y, cx, cy, lst) in ((wb, wh, cb, ch, reg), (wh, wb, ch, cb, win)):
            if grew(x, y, a.pct, a.time_abs) and (cpu_ok or grew(cx, cy, a.pct, 0)):
                lst.append((m, "time", f"{fmt(wb, 's')} (cpu {fmt(cb, 's')})",
                            f"{fmt(wh, 's')} (cpu {fmt(ch, 's')})", change(wb, wh)))
        if a.all and (rb, wb) != (rh, wh):
            info.append((m, "changed", f"{fmt(wb, 's')}, {fmt(rb, 'MB')}",
                         f"{fmt(wh, 's')}, {fmt(rh, 'MB')}", change(wb, wh) if wb and wh else ""))
    removed = sorted(B.keys() - H.keys() - {"_total"})

    bB, bH = latest(bhist, base, "bench") or {}, latest(bhist, head, "bench") or {}
    for n in sorted(bH.keys() & bB.keys()):
        b, h = bB[n], bH[n]
        rb, rh, wb, wh = num(b, "maxrss_mb"), num(h, "maxrss_mb"), num(b, "wall_s"), num(h, "wall_s")
        for (x, y, lst) in ((wb, wh, reg), (wh, wb, win)):
            if grew(x, y, a.pct, a.bench_time_abs):
                lst.append((f"bench {n}", "time", fmt(wb, "s"), fmt(wh, "s"), change(wb, wh)))
        for (x, y, lst) in ((rb, rh, reg), (rh, rb, win)):
            if grew(x, y, a.pct, a.bench_rss_abs):
                lst.append((f"bench {n}", "max RSS", fmt(rb, "MB"), fmt(rh, "MB"), change(rb, rh)))
        if h.get("status") != "ok" and b.get("status") == "ok":
            reg.append((f"bench {n}", "run", "ok", h.get("status", "?"), "broken"))

    print(f"### perf-compare `{base}` → `{head}`\n")
    tb, th = B.get("_total", {}), H.get("_total", {})
    print(f"{len(H) - 1} modules ({len(H.keys() - B.keys())} new, {len(removed)} removed); "
          f"serial module time {fmt(num(tb, 'wall_s'), 's')} → {fmt(num(th, 'wall_s'), 's')}, "
          f"largest module peak {fmt(num(tb, 'maxrss_mb'), 'MB')} → {fmt(num(th, 'maxrss_mb'), 'MB')}. "
          f"Thresholds: +{a.pct:.0f}% and +{a.rss_abs:g} MB / +{a.time_abs:g} s; "
          f"new modules > {a.new_rss / 1024:.0f} GB or > {a.new_time:.0f} s.\n")
    for title, lst in (("Regressions", reg), ("Wins", win), ("Other changes", info)):
        if lst:
            print(f"**{title}**\n\n| module | metric | base | head | change |\n|---|---|---|---|---|")
            for row in lst:
                print("| " + " | ".join(f"`{row[0]}`" if i == 0 else str(x) for i, x in enumerate(row)) + " |")
            print()
    if not reg:
        print("No regressions.")
    if removed:
        print(f"Removed modules: {', '.join(removed)}")
    return 1 if reg else 0


if __name__ == "__main__":
    sys.exit(main())
