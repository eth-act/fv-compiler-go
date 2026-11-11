#!/usr/bin/env python3
"""Throwaway: merge rank.py --tsv outputs of quick-v10 and full-v11 into the posted tables.
usage: merge.py QUICK.tsv FULL.tsv [N]"""
import sys

def load(p):
    d = {}
    for l in open(p):
        k, name, *rest = l.rstrip('\n').split('\t')
        d[(k, name)] = rest
    return d

q, f = load(sys.argv[1]), load(sys.argv[2])
n = int(sys.argv[3]) if len(sys.argv) > 3 else 20

def rows(d, kind):
    out = [(int(v[2]), name, v) for (k, name), v in d.items() if k == kind and v[2]]
    return sorted(out)

def show(kind, primary, other, pname, oname, label):
    print(f'| # | {label} | {pname} greedy gain | {pname} cumulative | {pname} sole | {pname} any | '
          f'{oname} greedy step / gain | {oname} sole | {oname} any | note |')
    print('|---:|---|---:|---:|---:|---:|---:|---:|---:|---|')
    cum = 0
    for step, name, v in rows(primary, kind)[:n]:
        cum += int(v[3])
        o = other.get((kind, name), ['0', '0', '', '', ''])
        ostep = f'{o[2]} / {o[3]}' if o[2] else '–'
        note = v[4] if len(v) > 4 else ''
        print(f'| {step} | `{name}` | {v[3]} | {cum} | {v[0]} | {v[1]} | {ostep} | {o[0]} | {o[1]} | {note} |')

which = sys.argv[4] if len(sys.argv) > 4 else 'qf'
if which == 'qf':
    show('class', q, f, 'quick', 'full', 'class')
elif which == 'fq':
    show('class', f, q, 'full', 'quick', 'class')
elif which == 'fam':
    show('family', f, q, 'full', 'quick', 'family')
elif which == 'def':
    print('| deferred class | quick any | quick sole | quick with actionable top 20 | quick with all else fixed | full any | full sole | full with actionable top 20 | full with all else fixed |')
    print('|---|---:|---:|---:|---:|---:|---:|---:|---:|')
    names = sorted({name for (k, name) in list(q) + list(f) if k == 'deferred'},
                   key=lambda x: -int(f.get(('deferred', x), ['0', '0'])[1]))
    for name in names:
        a = q.get(('deferred', name), ['0'] * 4)
        b = f.get(('deferred', name), ['0'] * 4)
        print(f'| {name} | {a[1]} | {a[0]} | {a[2]} | {a[3]} | {b[1]} | {b[0]} | {b[2]} | {b[3]} |')
