#!/usr/bin/env python3
"""Compare two recorded commits of perf/history.tsv (and perf/bench-history.tsv); docs/PERF.md.

usage: scripts/perf-compare.py [options] BASE HEAD

BASE/HEAD are git refs (resolved in --repo) or commit ids as written in the history
(12 hex digits, optionally `+dirty`). The latest recording of each commit is used.
Prints a Markdown report (for PR comments) and exits 1 when it flags a regression:

  * module peak RSS (lean VmHWM, `maxrss_mb`) grew > --pct % and > --rss-abs MB;
  * module time grew > --pct % and > --time-abs s, in wall time *and* CPU time (under load
    120 on 32 cores, wall times of unchanged small modules grew 2-10x and CPU ~1.5x);
  * a module that failed or was killed at its cap in HEAD but built in BASE;
  * a new module above --new-rss MB, --new-time s (CPU) or --new-olean MB of .olean;
  * a module whose .olean grew > --pct % and > --olean-abs MB (a proof-only module should stay
    well under 1 MB; tens of MB are generated equations or bv_decide certificates, see
    scripts/olean-top.lean);
  * a module whose .olean is newly not reproducible (`repro` = differs, perf-record.py);
  * the CPU critical path (`crit_s` of `_total`) grew > --pct % and > --crit-abs s; the report
    then names the chain (scripts/perf-graph.py);
  * a registered pass whose time in pass-parity (`pass time (s)`, perf/pass-history.tsv) grew
    > --pct % and > --pass-abs s on the same corpus (#147);
  * a benchmark whose wall time grew > --pct % and > --bench-time-abs s (and CPU > --pct %),
    or whose max RSS grew > --pct % and > --bench-rss-abs MB.
Shrinks past the same thresholds are listed as wins.
"""
import argparse, importlib.util, pathlib, subprocess, sys

here = pathlib.Path(__file__).resolve().parent.parent


def critical_chain(history, repo, commit):
    spec = importlib.util.spec_from_file_location("perf_graph", here / "scripts/perf-graph.py")
    g = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(g)
    try:
        return g.chain_for(commit, history, repo)
    except subprocess.CalledProcessError:
        return []


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
    ap.add_argument("--pass-history", default=str(here / "perf/pass-history.tsv"))
    ap.add_argument("--pass-abs", type=float, default=1, help="s, per-pass time (#147)")
    ap.add_argument("--repo", default=str(here))
    ap.add_argument("--pct", type=float, default=25)
    ap.add_argument("--rss-abs", type=float, default=512, help="MB")
    ap.add_argument("--time-abs", type=float, default=5, help="s")
    ap.add_argument("--new-rss", type=float, default=2048, help="MB")
    ap.add_argument("--new-time", type=float, default=60, help="s")
    ap.add_argument("--bench-time-abs", type=float, default=1, help="s")
    ap.add_argument("--bench-rss-abs", type=float, default=256, help="MB")
    ap.add_argument("--all", action="store_true", help="also list unflagged changed modules")
    ap.add_argument("--crit-abs", type=float, default=30, help="s, critical path (CPU)")
    ap.add_argument("--ignore", action="append", default=[],
                    help="module whose time flag an A/B re-timing showed to be noise")
    ap.add_argument("--new-olean", type=float, default=10, help="MB, new module .olean")
    ap.add_argument("--olean-abs", type=float, default=5, help="MB, .olean growth")
    a = ap.parse_args()

    hist = load(pathlib.Path(a.history))
    bhist = load(pathlib.Path(a.bench_history))
    known = {r["commit"] for r in hist + bhist}
    base, head = resolve(a.repo, a.base, known), resolve(a.repo, a.head, known)
    B, H = latest(hist, base, "module"), latest(hist, head, "module")
    if B is None or H is None:  # benchmark-only recordings (e.g. a #147 baseline) still compare
        print(f"(no module recording of {base if B is None else head}; benchmarks only)",
              file=sys.stderr)
        B, H = {}, {}

    reg, win, info = [], [], []
    for m in sorted(H.keys() - {"_total"}):
        h, b = H[m], B.get(m)
        if h.get("repro") == "differs" and (b is None or b.get("repro") != "differs"):
            reg.append((m, "non-reproducible .olean", (b or {}).get("repro") or "–", "differs",
                        "importers miss the shared cache"))
        if b is None:
            r, t, c = num(h, "maxrss_mb"), num(h, "wall_s"), num(h, "cpu_s")
            bad = h["status"] in ("fail", "oom", "blocked")
            # CPU when known: under load wall time alone flagged a 22 s-CPU module at 101 s
            slow = (c if c is not None else t or 0) > a.new_time
            big = (num(h, "olean_kb") or 0) / 1024 > a.new_olean
            if bad or (r or 0) > a.new_rss or slow or big:
                reg.append((m, "new module", "–", (h["status"] + ", " if bad else "")
                            + f"{fmt(t, 's')} (cpu {fmt(c, 's')}), {fmt(r, 'MB')}, "
                            + f"olean {fmt((num(h, 'olean_kb') or 0) / 1024, 'MB')}", "new"))
            continue
        if h["status"] in ("fail", "oom") and b["status"] not in ("fail", "oom", "blocked"):
            reg.append((m, "build", b["status"], f"{h['status']} (rss {h['maxrss_mb'] or '?'} MB)", "broken"))
            continue
        ob, oh = num(b, "olean_kb"), num(h, "olean_kb")
        for (x, y, lst) in ((ob, oh, reg), (oh, ob, win)):
            if grew(x, y, a.pct, a.olean_abs * 1024):  # .olean bytes are exact, not load noise
                lst.append((m, ".olean size", fmt(ob / 1024, "MB"), fmt(oh / 1024, "MB"), change(ob, oh)))
        if h.get("measured_at") and h.get("measured_at") == b.get("measured_at"):
            continue  # same measurement (module unchanged, numbers copied from the cache)
        rb, rh = num(b, "maxrss_mb"), num(h, "maxrss_mb")
        wb, wh, cb, ch = num(b, "wall_s"), num(h, "wall_s"), num(b, "cpu_s"), num(h, "cpu_s")
        cpu_ok = cb is None or ch is None
        for (x, y, lst) in ((rb, rh, reg), (rh, rb, win)):
            if grew(x, y, a.pct, a.rss_abs):
                lst.append((m, "peak RSS", fmt(rb, "MB"), fmt(rh, "MB"), change(rb, rh)))
        for (x, y, cx, cy, lst) in ((wb, wh, cb, ch, reg), (wh, wb, ch, cb, win)):
            if grew(x, y, a.pct, a.time_abs) and (cpu_ok or grew(cx, cy, a.pct, a.time_abs)):
                if lst is reg and m in a.ignore:  # interleaved A/B re-timing said: noise
                    info.append((m, "time (A/B: noise)", f"{fmt(wb, 's')} (cpu {fmt(cb, 's')})",
                                 f"{fmt(wh, 's')} (cpu {fmt(ch, 's')})", change(wb, wh)))
                    continue
                lst.append((m, "time", f"{fmt(wb, 's')} (cpu {fmt(cb, 's')})",
                            f"{fmt(wh, 's')} (cpu {fmt(ch, 's')})", change(wb, wh)))
        if a.all and (rb, wb) != (rh, wh):
            info.append((m, "changed", f"{fmt(wb, 's')}, {fmt(rb, 'MB')}",
                         f"{fmt(wh, 's')}, {fmt(rh, 'MB')}", change(wb, wh) if wb and wh else ""))
    removed = sorted(B.keys() - H.keys() - {"_total"})
    tb, th = B.get("_total", {}), H.get("_total", {})
    kb, kh = num(tb, "crit_s"), num(th, "crit_s")
    for (x, y, lst) in ((kb, kh, reg), (kh, kb, win)):
        if grew(x, y, a.pct, a.crit_abs):
            path = [] if lst is win else critical_chain(a.history, a.repo, head)
            lst.append(("_total", "critical path (CPU)", fmt(kb, "s"), fmt(kh, "s"),
                        change(kb, kh) + (f"; chain {' → '.join(path)}" if path else "")))

    bB, bH = latest(bhist, base, "bench") or {}, latest(bhist, head, "bench") or {}
    for n in sorted(bH.keys() & bB.keys()):
        b, h = bB[n], bH[n]
        if b.get("bin_hash") and b.get("bin_hash") == h.get("bin_hash"):
            continue  # same binary, command and corpus: same measurement
        if b.get("corpus") != h.get("corpus"):
            info.append((f"bench {n}", "corpus changed", b.get("corpus") or "–",
                         h.get("corpus") or "–", "not compared"))
            continue
        if not {b.get("status"), h.get("status")} <= {"ok", "cached"}:
            # a gate-failed (`unparsable`) run stops early: its time is not comparable
            if h.get("status") not in ("ok", "cached", "skipped") and b.get("status") in ("ok", "cached"):
                reg.append((f"bench {n}", "run", "ok", h.get("status", "?"), "broken"))
            continue
        rb, rh, wb, wh = num(b, "maxrss_mb"), num(h, "maxrss_mb"), num(b, "wall_s"), num(h, "wall_s")
        cb, ch = num(b, "cpu_s"), num(h, "cpu_s")
        cpu_ok = cb is None or ch is None
        for (x, y, cx, cy, lst) in ((wb, wh, cb, ch, reg), (wh, wb, ch, cb, win)):
            if grew(x, y, a.pct, a.bench_time_abs) and (cpu_ok or grew(cx, cy, a.pct, a.bench_time_abs)):
                lst.append((f"bench {n}", "time", f"{fmt(wb, 's')} (cpu {fmt(cb, 's')})",
                            f"{fmt(wh, 's')} (cpu {fmt(ch, 's')})", change(wb, wh)))
        for (x, y, lst) in ((rb, rh, reg), (rh, rb, win)):
            if grew(x, y, a.pct, a.bench_rss_abs):
                lst.append((f"bench {n}", "max RSS", fmt(rb, "MB"), fmt(rh, "MB"), change(rb, rh)))
        if h.get("status") not in ("ok", "cached", "skipped") and b.get("status") in ("ok", "cached"):
            reg.append((f"bench {n}", "run", "ok", h.get("status", "?"), "broken"))

    # per-pass runtime (pass-parity's `pass time (s)` column, perf-bench.py; issue #147)
    phist = load(pathlib.Path(a.pass_history))
    for r in phist:
        r["key"] = r["bench"] + "\0" + r["pass"]
    pB, pH = latest(phist, base, "key") or {}, latest(phist, head, "key") or {}
    for k in sorted(pH.keys() & pB.keys()):
        b, h = pB[k], pH[k]
        if b["corpus"] != h["corpus"] or b["bin_hash"] == h["bin_hash"]:
            continue
        sb, sh = num(b, "time_s"), num(h, "time_s")
        for (x, y, lst) in ((sb, sh, reg), (sh, sb, win)):
            if grew(x, y, a.pct, a.pass_abs):
                lst.append((f"pass {h['pass']}", "runtime (quick corpus)", fmt(sb, "s"),
                            fmt(sh, "s"), change(sb, sh)))

    print(f"### perf-compare `{base}` → `{head}`\n")
    print(f"{len(H.keys() - {'_total'})} modules ({len(H.keys() - B.keys() - {'_total'})} new, {len(removed)} removed); "
          f"serial module time {fmt(num(tb, 'wall_s'), 's')} → {fmt(num(th, 'wall_s'), 's')} "
          f"(cpu {fmt(num(tb, 'cpu_s'), 's')} → {fmt(num(th, 'cpu_s'), 's')}), "
          f"critical path (CPU) {fmt(kb, 's')} → {fmt(kh, 's')}, "
          f"largest module peak {fmt(num(tb, 'maxrss_mb'), 'MB')} → {fmt(num(th, 'maxrss_mb'), 'MB')}. "
          f"Thresholds: +{a.pct:.0f}% and +{a.rss_abs:g} MB / +{a.time_abs:g} s; "
          f"new modules > {a.new_rss / 1024:.0f} GB, > {a.new_time:.0f} s CPU or > {a.new_olean:g} MB .olean; "
          f".olean +{a.olean_abs:g} MB; "
          f"critical path +{a.crit_abs:g} s.\n")
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
