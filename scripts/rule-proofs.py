#!/usr/bin/env python3
"""Rule-lemma bookkeeping (docs/proofs/rules.md).

  scripts/rule-proofs.py classify           # run the Lean classifier -> tmp/rules/class.tsv
  scripts/rule-proofs.py probe FAM... [-j N] [--all]
                                            # try `rule_auto` on the pending P1 rules of the
                                            # op families -> tmp/rules/probe-<FAM>.tsv
  scripts/rule-proofs.py emit FAM [--chunk N]
                                            # append theorems for the probed-OK rules to
                                            # GoFV/Proof/Rules/<FAM>[N].lean
  scripts/rule-proofs.py table              # rewrite the tables of docs/proofs/rules.md

Every Lean command runs under scripts/memcap.sh. Temporary files live in tmp/rules/.
"""
import argparse
import collections
import concurrent.futures
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TMP = os.path.join(ROOT, "tmp", "rules")
GEN = os.path.join(ROOT, "GoFV", "Rules", "Generated")
PROOF = os.path.join(ROOT, "GoFV", "Proof", "Rules")
DOC = os.path.join(ROOT, "docs", "proofs", "rules.md")
FILES = ["Generic", "Dec", "Divisible", "Divmod"]
INFRA = {"Den", "Tactic", "Comm", "NonVacuous"}


def lean(*args, capture=True):
    cmd = [os.path.join(ROOT, "scripts", "memcap.sh"), "lake", "env", "lean", *args]
    return subprocess.run(cmd, cwd=ROOT, capture_output=capture, text=True)


def rule_names():
    """(file, key) -> (qualified def name, module, doc) where key is `<Op>#<i>`."""
    out = {}
    for f in FILES:
        d = os.path.join(GEN, f)
        for mod in sorted(os.listdir(d)):
            path = os.path.join(d, mod)
            src = open(path).read()
            docs = dict(re.findall(r"/-- (`[^\n]*?) -/\ndef (r_\w+)", src))
            docs = {v: k for k, v in docs.items()}
            modname = f"GoFV.Rules.Generated.{f}.{mod[:-5]}"
            for m in re.finditer(r"^def (?:ops|blocks)_(\w+) : List (?:Block)?Rule := \[(.*)\]$",
                                 src, re.M):
                op, names = m.group(1), [n.strip() for n in m.group(2).split(",") if n.strip()]
                for i, n in enumerate(names):
                    out[(f.lower(), f"{op}#{i}")] = (
                        f"GoFV.Rules.Generated.{f}.{n}", modname, docs.get(n, ""))
    return out


def classify():
    os.makedirs(TMP, exist_ok=True)
    r = lean("--run", "GoFVTest/Proof/RuleClass.lean", "--list")
    if r.returncode != 0:
        sys.exit(r.stderr + r.stdout)
    names = rule_names()
    rows = []
    for line in r.stdout.splitlines():
        parts = line.split()
        if len(parts) != 4 or "#" not in parts[1]:
            continue
        f, key, cls, fam = parts
        q, mod, doc = names[(f, key)]
        rows.append((q, f, key.split("#")[0], cls, fam, mod, doc))
    with open(os.path.join(TMP, "class.tsv"), "w") as fh:
        for row in rows:
            fh.write("\t".join(row) + "\n")
    print(f"{len(rows)} rules classified")


def load_class():
    path = os.path.join(TMP, "class.tsv")
    if not os.path.exists(path):
        classify()
    rows = []
    for line in open(path):
        q, f, op, cls, fam, mod, doc = line.rstrip("\n").split("\t")
        rows.append(dict(q=q, file=f, op=op, cls=cls, fam=fam, mod=mod, doc=doc))
    return rows


def proven():
    """Short rule name -> proof module, from `theorem <name>_sound`."""
    out = {}
    for fn in os.listdir(PROOF):
        if not fn.endswith(".lean") or fn[:-5] in INFRA:
            continue
        for m in re.finditer(r"^theorem (r_\w+)_sound\b", open(os.path.join(PROOF, fn)).read(),
                             re.M):
            out[m.group(1)] = fn[:-5]
    return out


def false_rules():
    """Short rule name -> issue, from `-- FALSE r_x #N` lines of the proof modules."""
    out = {}
    for fn in os.listdir(PROOF):
        if fn.endswith(".lean"):
            for m in re.finditer(r"-- FALSE (r_\w+) (#\d+)", open(os.path.join(PROOF, fn)).read(),
                                 re.M):
                out[m.group(1)] = m.group(2)
    return out


def short(q):
    return q.rsplit(".", 1)[1]


PROBE_HDR = """import Lean
import GoFV.Proof.Rules.Tactic
{imports}
open Lean Elab Command

elab "#probe " ids:ident* : command => do
  for id in ids do
    let t0 ← IO.monoMsNow
    let msgs0 := (← get).messages
    modify fun s => {{ s with messages := {{}} }}
    withoutModifyingEnv do
      elabCommand (← `(theorem probe : GoFV.Proof.Rules.Rule.Sound $id := by rule_auto))
    let ms := (← get).messages
    let ok := !ms.hasErrors
    let t1 ← IO.monoMsNow
    let mut err := ""
    for m in ms.toList do
      if m.severity == .error && err == "" then
        err := (← m.data.toString).replace "\\n" " ⏎ "
    modify fun s => {{ s with messages := msgs0 }}
    logInfo m!"PROBE {{id}} {{if ok then "OK" else "FAIL"}} {{t1 - t0}}ms {{(err.take 600).toString}}"

set_option Elab.async false
"""


def probe_one(fam, rules, idx):
    mods = sorted({r["mod"] for r in rules})
    src = PROBE_HDR.format(imports="\n".join(f"import {m}" for m in mods))
    src += "#probe " + " ".join(r["q"] for r in rules) + "\n"
    path = os.path.join(TMP, f"Probe_{fam}_{idx}.lean")
    open(path, "w").write(src)
    r = lean(os.path.relpath(path, ROOT))
    res = []
    for line in (r.stdout + r.stderr).splitlines():
        m = re.search(r"PROBE (\S+) (OK|FAIL) (\d+)ms ?(.*)", line)
        if m:
            res.append((m.group(1), m.group(2), m.group(3), m.group(4)))
    if not res:
        res = [(r_["q"], "FAIL", "0", "probe crashed: " + (r.stderr + r.stdout)[-300:].replace("\n", " "))
               for r_ in rules]
    return res


def probe(fams, jobs, include_proven, chunk, fails_only=False):
    rows = load_class()
    done = proven()
    tasks = []
    for fam in fams:
        rules = [r for r in rows if r["fam"] == fam and r["cls"] == "P1"
                 and (include_proven or short(r["q"]) not in done)]
        prev = os.path.join(TMP, f"probe-{fam}.tsv")
        if fails_only and os.path.exists(prev):
            okq = {l.split("\t")[0] for l in open(prev) if l.split("\t")[1] == "OK"}
            rules = [r for r in rules if r["q"] not in okq]
        for i in range(0, len(rules), chunk):
            tasks.append((fam, rules[i:i + chunk], i // chunk))
    results = collections.defaultdict(list)
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        futs = {ex.submit(probe_one, *t): t[0] for t in tasks}
        for fu in concurrent.futures.as_completed(futs):
            results[futs[fu]].extend(fu.result())
    for fam in fams:
        res = results[fam]
        prev = os.path.join(TMP, f"probe-{fam}.tsv")
        if fails_only and os.path.exists(prev):
            newq = {r[0] for r in res}
            res = [tuple(l.rstrip("\n").split("\t")) for l in open(prev)
                   if l.split("\t")[0] not in newq] + res
        with open(prev, "w") as fh:
            for row in res:
                fh.write("\t".join(row) + "\n")
        ok = sum(1 for r in res if r[1] == "OK")
        print(f"{fam}: {ok}/{len(res)} OK")


MOD_HDR = """import GoFV.Proof.Rules.Tactic
{imports}

/-!
# Rule lemmas: `{fam}` rules{part}

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`{fam}` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

-- `bv_decide` proofs fail nondeterministically under parallel elaboration here (`grind failed`
-- after a `bv_decide` that succeeds sequentially); the probe runs sequentially too.
set_option Elab.async false

"""


def emit(fam, chunk):
    rows = {r["q"]: r for r in load_class()}
    path = os.path.join(TMP, f"probe-{fam}.tsv")
    ok = [line.split("\t")[0] for line in open(path) if line.split("\t")[1] == "OK"]
    done = proven()
    ok = [q for q in ok if short(q) not in done]
    # keep the rule-file order
    order = {r["q"]: i for i, r in enumerate(load_class())}
    ok.sort(key=lambda q: order[q])
    existing = sorted(fn for fn in os.listdir(PROOF)
                      if re.fullmatch(re.escape(fam) + r"\d*\.lean", fn))
    part = len(existing)
    for i in range(0, len(ok), chunk):
        group = ok[i:i + chunk]
        part += 1
        name = fam if part == 1 else f"{fam}{part}"
        mods = sorted({rows[q]["mod"] for q in group})
        src = MOD_HDR.format(imports="\n".join(f"import {m}" for m in mods), fam=fam,
                             part="" if part == 1 else f" (part {part})")
        for q in group:
            doc = rows[q]["doc"]
            src += f"/-- {doc} -/\n" if doc else ""
            src += f"theorem {short(q)}_sound : Rule.Sound {q} := by rule_auto\n\n"
        src += "end GoFV.Proof.Rules\n"
        out = os.path.join(PROOF, name + ".lean")
        assert not os.path.exists(out), out
        open(out, "w").write(src)
        print(f"wrote {out}: {len(group)} lemmas")


def table():
    rows = load_class()
    done = proven()
    bad = false_rules()
    classes = ["P1", "mem", "call", "float", "ptr", "phi", "block"]
    lines = ["| File | " + " | ".join(classes) + " | Total |",
             "| --- |" + " --: |" * (len(classes) + 1)]
    for f in [x.lower() for x in FILES] + ["all"]:
        mine = [r for r in rows if f == "all" or r["file"] == f]
        cnt = [sum(1 for r in mine if r["cls"] == c) for c in classes]
        name = "all" if f == "all" else f"`{f}`"
        lines.append(f"| {name} | " + " | ".join(map(str, cnt)) + f" | {len(mine)} |")
    class_table = "\n".join(lines)
    fams = collections.OrderedDict()
    for r in rows:
        fams.setdefault((r["file"], r["fam"]), []).append(r)
    lines = ["| File | Family | Proven | Pending (P1) | False | Not P1 | Total |",
             "| --- | --- | --: | --: | --: | --: | --: |"]
    tot = [0, 0, 0, 0, 0]
    for (f, fam), rs in sorted(fams.items()):
        p = sum(1 for r in rs if short(r["q"]) in done)
        fl = sum(1 for r in rs if short(r["q"]) in bad)
        pend = sum(1 for r in rs if r["cls"] == "P1" and short(r["q"]) not in done
                   and short(r["q"]) not in bad)
        np = sum(1 for r in rs if r["cls"] != "P1")
        for i, x in enumerate([p, pend, fl, np, len(rs)]):
            tot[i] += x
        lines.append(f"| `{f}` | {fam} | {p} | {pend} | {fl} | {np} | {len(rs)} |")
    lines.append("| all | | " + " | ".join(map(str, tot)) + " |")
    cov_table = "\n".join(lines)
    doc = open(DOC).read()
    for tag, body in [("classes", class_table), ("coverage", cov_table)]:
        doc = re.sub(rf"(<!-- BEGIN {tag} -->\n).*?(<!-- END {tag} -->)",
                     lambda m: m.group(1) + "<!-- Generated by scripts/rule-proofs.py table. -->\n\n"
                     + body + "\n\n" + m.group(2), doc, flags=re.S)
    open(DOC, "w").write(doc)
    print(f"proven {tot[0]}, pending {tot[1]}, false {tot[2]}, not P1 {tot[3]}, total {tot[4]}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["classify", "probe", "emit", "table"])
    ap.add_argument("fams", nargs="*")
    ap.add_argument("-j", "--jobs", type=int, default=2)
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--chunk", type=int, default=40)
    ap.add_argument("--fails", action="store_true", help="re-probe only the rules that failed")
    a = ap.parse_args()
    if a.cmd == "classify":
        classify()
    elif a.cmd == "probe":
        probe(a.fams, a.jobs, a.all, a.chunk, a.fails)
    elif a.cmd == "emit":
        for fam in a.fams:
            emit(fam, a.chunk)
    else:
        table()


if __name__ == "__main__":
    main()
