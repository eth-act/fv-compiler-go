#!/usr/bin/env python3
"""Throwaway (#69/#385/#553): rank what blocks the functions whose back end passes on stock
but whose Phase 1/2 pipeline is not fully verified.

usage: rank.py TARGETS FIRE LOWERDUMP LOWEROUT [--invalid FILES] [--json OUT]
  TARGETS   TSV: path, `gen=` (Phase 1 unverified runs, `; `-separated), `low=` (runs from
            lower on), vac (stock entryVacuous: `-` or reason), lowwhy= (rejected lower / late
            lower / lowered deadcode: why), sched= (rejected schedule class), diff= (first
            difference from stock: pass: verdict)
  FIRE      rule-fire-probe output (OFF rules path)
  LOWERDUMP lower-probe --dump (ceil-class same fired path proven-class)
  LOWEROUT  lower-probe stdout (PROVEN key)
  --invalid files whose stock section before `lower` has an OpInvalid value (lowerGuard's
            `f.lowered` holds of them: the guard would reject them once the rules complete)
"""
import sys, collections, re, json

tpath, fpath, dpath, opath = sys.argv[1:5]
def opt(name):
    return sys.argv[sys.argv.index(name) + 1] if name in sys.argv else None
jout = opt('--json')
invalid = set(l.strip() for l in open(opt('--invalid'))) if opt('--invalid') else set()

off = {}
for l in open(fpath, encoding='utf-8', errors='replace'):
    p = l.rstrip('\n').split('\t')
    if p[0] == 'OFF':
        off[p[2]] = [r for r in p[1].split(',') if r]
    elif p[0] == 'VONLY':
        off.setdefault(p[1], [])
proven = set()
for l in open(opath, encoding='utf-8', errors='replace'):
    if l.startswith('PROVEN\t'):
        proven.add(l.rstrip('\n').split('\t', 1)[1])
low = {}
for l in open(dpath, encoding='utf-8', errors='replace'):
    p = l.rstrip('\n').split('\t')
    if len(p) < 5: continue
    w, same, fired, path, pw = p[:5]
    low[path] = (w, same == '1', [k for k in fired.split('|') if k], pw)

REWRITE = ('opt', 'middle opt', 'late opt', 'divisible', 'divmod')

def p1_classes(path, run, diff):
    pas = run.split(':')[0]
    if pas in REWRITE and 'checked variant incomplete' in run:
        rules = off.get(path)
        if rules is None:
            # the probe (stock input) is at stock: the chain's input differs, by the first difference
            if 'skipped' in diff or 'unverified' in diff:
                return [f'P1 chain: {diff} (then {pas} incomplete)']
            return [f'P1 {pas}: incomplete on the chain only ({diff})']
        if not rules:
            return [f'P1 {pas}: validator only']
        return [f'P1 rule {r}' for r in rules]
    return [f'P1 {run}']

GUARD_INVALID = 'P2 lower guard: lowered input: op OpInvalid'

def lower_classes(path, run, why):
    if 'rejected' in run:
        g = [w for w in why if not w.startswith(('late lower:', 'lowered deadcode:'))]
        return [f'P2 lower guard: {g[0]}' if g else 'P2 lower guard: ?']
    d = low.get(path)
    if d is None:
        return [f'P2 {run} (no lower-probe row)']
    w, same, fired, pw = d
    unp = sorted({k for k in fired if k not in proven})
    out = [f'P2 rule {k}' for k in unp]
    if w != 'ok':
        out.append(f'P2 ceiling: {w}')
    if not out:
        out.append(f'P2 lower: proven table rejects ({pw})' if pw != 'ok' else f'P2 {run} (probe at stock)')
    if path in invalid:
        out.append(GUARD_INVALID)
    return out

def blockers(path, gen, lowr, why, sched, diff):
    b = set()
    for r in gen:
        b.update(p1_classes(path, r, diff))
    for r in lowr:
        if r.startswith('lower:'):
            b.update(lower_classes(path, r, why))
        elif r.startswith('late lower:') and 'rejected' in r:
            w = [x for x in why if x.startswith('late lower:')]
            b.add(f'P2 {w[0]}' if w else f'P2 {r}')
        elif r.startswith('lowered deadcode:') and 'rejected' in r:
            w = [x for x in why if x.startswith('lowered deadcode:')]
            b.add(f'P2 {w[0]}' if w else f'P2 {r}')
        elif r.startswith('schedule:') and sched != '-':
            b.add(f'P2 schedule: {sched}')
        else:
            b.add(f'P2 {r}')
    return frozenset(b)

def deferred(c):
    m = re.match(r'P2 rule ARM64:(\d+) (\S+)', c)
    if m:
        n, op = int(m.group(1)), m.group(2)
        if op == 'Move' and 380 <= n <= 428: return 'Move -> MOV*store (#689, deferred)'
        if n in (1197, 1198) and op == 'SUB': return 'SUB 1197/1198 (false)'
        if n == 134: return 'OrB 134 (model limit)'
        if 'Tail' in op: return 'tail calls (no semantics)'
    if c.startswith('P2 ceiling: atoms: Move -> MOV') and 'store' in c:
        return 'Move -> MOV*store (#689, deferred)'
    if c.startswith('P2 ceiling: rule ARM64:1197 SUB') or c.startswith('P2 ceiling: rule ARM64:1198 SUB'):
        return 'SUB 1197/1198 (false)'
    if 'Tail' in c: return 'tail calls (no semantics)'
    m = re.match(r'P1 rule generic:(\d+) ', c)
    if m and int(m.group(1)) in (919, 924): return "'not disjoint' (kept open)"
    return None

# #69's false/skipped Phase 1 rules (comment 6794563223; rules.md Findings), informational
P1_FALSE = {1071: 'false under the semantics (rules.md: Convert/AddPtr provenance)',
            1075: 'false under the semantics (rules.md: Convert/AddPtr provenance)',
            2159: 'false/skipped (#69)', 2167: 'false/skipped (#69)', 579: 'false/skipped (#69)',
            2342: 'false/skipped (#69, CondSelect)'}
def note(c):
    d = deferred(c)
    if d: return d
    m = re.match(r'P1 rule generic:(\d+) ', c)
    if m and int(m.group(1)) in P1_FALSE: return P1_FALSE[int(m.group(1))]
    if c.startswith('P1 rule divmod:148 '): return 'false/skipped (#69)'
    if c.startswith('P1 rule generic:') and 'CondSelect' in c: return 'CondSelect (#69 skipped)'
    if c.startswith('P2 rule ARM64:133 '): return 'S1 approved (#385)'
    if re.match(r'P2 rule ARM64:181[1-7] ', c): return 'R1 approved (#385)'
    if re.match(r'P2 (rule|ceiling: rule) ARM64:(99|100) ', c): return 'skipped (#385: atom-value invariant)'
    return ''

fns = {}
vac = {}
for l in open(tpath, encoding='utf-8', errors='replace'):
    p = l.rstrip('\n').split('\t')
    path, gen, lowr, v = p[0], p[1], p[2], p[3]
    why = [x.strip() for x in p[4][len('lowwhy='):].split(';') if x.strip() and x.strip() != '-'] if len(p) > 4 else []
    sched = p[5][len('sched='):] if len(p) > 5 else '-'
    diff = p[6][len('diff='):] if len(p) > 6 else '-'
    gen = [x.strip() for x in gen[len('gen='):].split(';') if x.strip()]
    lowr = [x.strip() for x in lowr[len('low='):].split(';') if x.strip()]
    fns[path] = blockers(path, gen, lowr, why, sched, diff)
    vac[path] = v != '-'

FLOAT = re.compile(r'^(F(?!LDPQ|STPQ|MOVQ)[A-Z]|Cvt|Round|Floor|Ceil|Trunc|Sqrt|Abs|Copysign|Min(32|64)F|Max(32|64)F|LessThanF|LessEqualF|GreaterThanF|GreaterEqualF|NotEqualF|EqualF)|(32|64)F$')
def family(c):
    d = deferred(c)
    if d: return d
    if c.startswith('P2 lower guard: lowered input: op OpInvalid'): return 'lower guard: OpInvalid in the input (writebarrier leftovers)'
    if c.startswith('P2 lower guard'): return 'lower guard: other'
    m = re.match(r'P2 (?:rule|ceiling: rule|ceiling: blockRule) ARM64:(\d+) (?:block )?(\S+)', c)
    if m:
        n, op = int(m.group(1)), m.group(2)
        if n in (99, 100): return '99/100 FMOVD<->MOVD forwarding (skipped, #385)'
        if 1811 <= n <= 1817: return 'RO loads 1811-1817 (R1 approved, #385)'
        if n == 133: return '133 AndB (S1 approved, #385)'
        if FLOAT.search(op) or (op.startswith('F') and n >= 1300 and 'block' in c): return 'lower: float rules'
        if c.startswith('P2 rule'): return 'lower: other unproven rules'
        return 'lower: validator ceiling, rule shape'
    if c.startswith('P2 ceiling: final:'): return 'lower: validator ceiling, final'
    if c.startswith('P2 ceiling: atoms:'): return 'lower: validator ceiling, atoms (not Move)'
    if c.startswith('P2 ceiling: not lowered'): return 'lower: validator ceiling, not lowered'
    if c.startswith('P2 ceiling'): return 'lower: validator ceiling, other'
    if c.startswith('P2 late lower'): return 'late lower validator'
    if c.startswith('P2 lowered deadcode'): return 'lowered deadcode fragment'
    if c.startswith('P2 schedule'): return 'schedule validator'
    if c.startswith('P2 '): return 'P2 other'
    m = re.match(r'P1 rule generic:(\d+) (\S+)', c)
    if m:
        n, op = int(m.group(1)), m.group(2)
        if n in (1071, 1075): return 'P1 Convert 1071/1075 (false under the semantics)'
        if op == 'CondSelect': return 'P1 CondSelect rules (#69 skipped)'
        return 'P1 other unproven rules'
    if c.startswith('P1 rule'): return 'P1 other unproven rules'
    if c.startswith('P1 chain'): return 'P1 chain: a skipped optional pass makes a checked pass incomplete'
    if 'validator only' in c: return 'P1 rewrite validator only'
    if 'fragment' in c: return 'P1 fragment (decompose/expand calls/deadcode)'
    return 'P1 other'

def greedy(sets, limit, exclude=lambda c: False):
    chosen, rows = set(), []
    pending = {f: b for f, b in sets.items() if not any(exclude(c) for c in b)}
    for step in range(1, limit + 1):
        cand = collections.Counter()
        for f, b in pending.items():
            rest = b - chosen
            if len(rest) == 1: cand[next(iter(rest))] += 1
        if not cand: break
        bg = max(cand.values())
        best = sorted(c for c, n in cand.items() if n == bg)[0]
        chosen.add(best)
        gained = [f for f, b in pending.items() if b <= chosen]
        for f in gained: del pending[f]
        rows.append((step, best, len(gained)))
    return rows, chosen

def table(sets, rows, limit, label, notef):
    anyc = collections.Counter(c for b in sets.values() for c in b)
    sole = collections.Counter(next(iter(b)) for b in sets.values() if len(b) == 1)
    print(f'\n| step | {label} | greedy gain | cumulative | sole | blocks (any) | note |')
    print('|---:|---|---:|---:|---:|---:|---|')
    cum = 0
    for step, c, g in rows[:limit]:
        cum += g
        print(f'| {step} | `{c}` | {g} | {cum} | {sole[c]} | {anyc[c]} | {notef(c)} |')
    return anyc, sole

def report(title, S, tsv=None):
    print(f'## {title}: {len(S)} functions')
    sets = {f: fns[f] for f in S}
    nb = collections.Counter(min(len(b), 4) for b in sets.values())
    print('blockers per function (4 = 4+):', dict(sorted(nb.items())))
    rows, _ = greedy(sets, 60)
    anyc, sole = table(sets, rows, 60, 'class', note)
    # actionable: classes not deferred and not false
    bad = lambda c: bool(deferred(c)) or 'false' in note(c) or 'skipped' in note(c)
    arows, achosen = greedy({f: frozenset(c for c in b) for f, b in sets.items()}, 60, exclude=bad)
    top20 = {c for _, c, _ in arows[:20]}
    print(f'\nactionable greedy (functions with a deferred or false class left out): top 20 complete '
          f'{sum(g for _, _, g in arows[:20])}, top 60 {sum(g for _, _, g in arows)}')
    print('\n### Actionable greedy (no deferred, false or skipped class)')
    table(sets, arows, 20, 'class', note)
    fsets = {f: frozenset(family(c) for c in b) for f, b in sets.items()}
    frows, _ = greedy(fsets, 40)
    print('\n### By family')
    table(fsets, frows, 40, 'family', lambda c: '')
    print('\n### Deferred / out-of-scope classes')
    fam = collections.defaultdict(set)
    for c in anyc:
        d = deferred(c)
        if d: fam[d].add(c)
    alldef = set().union(*fam.values()) if fam else set()
    print('| class | blocks (any) | sole (family alone) | with the actionable top 20 fixed | with every other non-deferred class fixed | members |')
    print('|---|---:|---:|---:|---:|---|')
    for d, cs in sorted(fam.items(), key=lambda x: -sum(1 for b in sets.values() if b & x[1])):
        anyn = sum(1 for b in sets.values() if b & cs)
        solen = sum(1 for b in sets.values() if b and b <= cs)
        w20 = sum(1 for b in sets.values() if (b & cs) and b <= (cs | top20))
        withnd = sum(1 for b in sets.values() if (b & cs) and not (b & (alldef - cs)))
        mem = ', '.join(f'`{c}` {anyc[c]}' for c in sorted(cs, key=lambda c: -anyc[c])[:8])
        print(f'| {d} | {anyn} | {solen} | {w20} | {withnd} | {mem} |')
    blocked_def = sum(1 for b in sets.values() if b & alldef)
    print(f'\nany deferred class: {blocked_def}; deferred classes only: '
          f'{sum(1 for b in sets.values() if b and b <= alldef)}; no deferred class: {len(sets) - blocked_def}')
    print('\n### Top classes by functions blocked (any)')
    for c, n in anyc.most_common(30):
        print(f'- `{c}`: {n} (sole {sole[c]}) {note(c)}')
    if tsv:
        with open(tsv, 'w') as o:
            step = {c: (s, g) for s, c, g in rows}
            for c in anyc:
                s, g = step.get(c, ('', ''))
                o.write(f'class\t{c}\t{sole[c]}\t{anyc[c]}\t{s}\t{g}\t{note(c)}\n')
            fany = collections.Counter(x for b in fsets.values() for x in b)
            fsole = collections.Counter(next(iter(b)) for b in fsets.values() if len(b) == 1)
            fstep = {c: (s, g) for s, c, g in frows}
            for c in fany:
                s, g = fstep.get(c, ('', ''))
                o.write(f'family\t{c}\t{fsole[c]}\t{fany[c]}\t{s}\t{g}\t\n')
            for d, cs in fam.items():
                o.write(f'deferred\t{d}\t{sum(1 for b in sets.values() if b and b <= cs)}\t'
                        f'{sum(1 for b in sets.values() if b & cs)}\t'
                        f'{sum(1 for b in sets.values() if (b & cs) and b <= (cs | top20))}\t'
                        f'{sum(1 for b in sets.values() if (b & cs) and not (b & (alldef - cs)))}\t\n')

allS = sorted(fns)
nonvac = [f for f in allS if not vac[f]]
tsvp = opt('--tsv')
report('stock: back-end premises hold, pipeline not fully verified', allS, tsvp and tsvp + '-all.tsv')
print()
report('… and not vacuous at the entry on stock (would count end to end)', nonvac, tsvp and tsvp + '-nonvac.tsv')
if jout:
    json.dump({'all': {f: sorted(fns[f]) for f in allS}, 'vac': vac}, open(jout, 'w'))
