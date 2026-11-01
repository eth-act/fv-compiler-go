#!/usr/bin/env python3
"""Rule-lemma bookkeeping (docs/proofs/rules.md).

  scripts/rule-proofs.py classify           # run the Lean classifier -> tmp/rules/class.tsv
  scripts/rule-proofs.py probe FAM... [-j N] [--all] [--tactic T]
                                            # try `rule_auto` (or tactic T of TACTICS) on the
                                            # pending P1/P2 rules of the op families
                                            # -> tmp/rules/probe-<FAM>.tsv
  scripts/rule-proofs.py emit FAM [--chunk N] [--tactic T]
                                            # append theorems for the probed-OK rules to
                                            # GoFV/Proof/Rules/<FAM>[N].lean
  scripts/rule-proofs.py table              # rewrite the tables of docs/proofs/rules.md
  scripts/rule-proofs.py sat                # run `lake exe rule-sat` (satisfying instance per
                                            # rule) -> tmp/rules/sat.tsv; fails if a proven
                                            # rule has no instance or a counterexample
  scripts/rule-proofs.py axioms             # `#print axioms` of every theorem of the proof
                                            # modules; fails on non-standard axioms
  scripts/rule-proofs.py proven             # the proven-only rule sets GoFV/Rules/Proven.lean
                                            # and their soundness GoFV/Proof/Rules/Proven.lean
  scripts/rule-proofs.py fire [CORPUS]      # `lake exe rule-fire-probe` on the quick corpus ->
                                            # tmp/rules/fire.tsv and the firing table of the doc

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
INFRA = {"Den", "DenT", "OpVal", "Tactic", "Comm", "NonVacuous", "Proven", "AllSound"}
# Classes `Rule.Sound` covers: every op has an `evalPure` arm (`GoFVTest/Proof/RuleClass.lean`).
PURE = ("P1", "P2")


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
    return {r: mod for r, (mod, _) in proven_kinds().items()}


def proven_kinds():
    """Short rule name -> (proof module, obligation), from `theorem <name>_sound : <obligation>`
    (`Rule.Sound`, `Rule.SoundT`, `BlockRule.Sound`, `EffectRule.NilElim`, `EffectRule.LoadFwd`,
    `EffectRule.StructLoad`)."""
    out = {}
    for fn in os.listdir(PROOF):
        if not fn.endswith(".lean") or fn[:-5] in INFRA:
            continue
        for m in re.finditer(r"^theorem (r_\w+)_sound\s*:\s*([\w.]+)",
                             open(os.path.join(PROOF, fn)).read(), re.M):
            out[m.group(1)] = (fn[:-5], m.group(2))
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


# The rule-lemma tactics and the module defining each (`--tactic`).
TACTICS = {"rule_auto": "GoFV.Proof.Rules.Tactic", "rule_range": "GoFV.Proof.Rules.TacticRange"}

PROBE_HDR = """import Lean
import {tacmod}
{imports}
open Lean Elab Command

/-- Distinct subterms of a proof (its share of the `.olean`, ~25 bytes each). -/
partial def dagSize (e : Lean.Expr) : Nat := Id.run do
  let mut seen : Std.HashSet Lean.Expr := {{}}
  let mut stack := [e]
  while true do
    match stack with
    | [] => break
    | t :: rest =>
      stack := rest
      if seen.contains t then continue
      seen := seen.insert t
      match t with
      | .app f a => stack := f :: a :: stack
      | .lam _ d b _ | .forallE _ d b _ => stack := d :: b :: stack
      | .letE _ t v b _ => stack := t :: v :: b :: stack
      | .mdata _ b | .proj _ _ b => stack := b :: stack
      | _ => pure ()
  return seen.size

elab "#probe " ids:ident* : command => do
  for id in ids do
    let t0 ← IO.monoMsNow
    let msgs0 := (← get).messages
    modify fun s => {{ s with messages := {{}} }}
    let ((size : Nat), (certs : Nat)) ← withoutModifyingEnv do
      elabCommand (← `(theorem $(mkIdent `probe) : GoFV.Proof.Rules.Rule.Sound $id := by {tactic}))
      let env ← getEnv
      let size : Nat := match env.find? `probe with
        | some c => dagSize ((c.value? (allowOpaque := true)).getD (.sort .zero))
        | none => 0
      let certs : Nat := env.constants.map₂.foldl (fun n k _ =>
        if (`probe).isPrefixOf k && (k.toString.splitOn "_cert").length > 1 then n + 1 else n) 0
      return (size, certs)
    let ms := (← get).messages
    let ok := !ms.hasErrors
    let t1 ← IO.monoMsNow
    let mut err := ""
    for m in ms.toList do
      if m.severity == .error && err == "" then
        err := (← m.data.toString).replace "\\n" " ⏎ "
    modify fun s => {{ s with messages := msgs0 }}
    logInfo m!"PROBE {{id}} {{if ok then "OK" else "FAIL"}} {{t1 - t0}}ms {{size}} {{certs}} {{(err.take 600).toString}}"

-- Sequential: an asynchronously elaborated proof would report its errors after `#probe` has
-- read the messages.
set_option Elab.async false
"""


def probe_one(fam, rules, idx, tactic):
    mods = sorted({r["mod"] for r in rules})
    src = PROBE_HDR.format(imports="\n".join(f"import {m}" for m in mods), tacmod=TACTICS[tactic],
                           tactic=tactic)
    src += "#probe " + " ".join(r["q"] for r in rules) + "\n"
    path = os.path.join(TMP, f"Probe_{fam}_{idx}.lean")
    open(path, "w").write(src)
    r = lean(os.path.relpath(path, ROOT))
    res = []
    for line in (r.stdout + r.stderr).splitlines():
        m = re.search(r"PROBE (\S+) (OK|FAIL) (\d+)ms (\d+) (\d+) ?(.*)", line)
        if m:
            ok = m.group(2)
            if ok == "OK" and m.group(5) != "0":
                ok = "BV"  # closed by `bv_decide`: an LRAT certificate in the `.olean`
            res.append((m.group(1), ok, m.group(3), m.group(4), m.group(6)))
    if not res:
        res = [(r_["q"], "FAIL", "0", "0",
                "probe crashed: " + (r.stderr + r.stdout)[-300:].replace("\n", " "))
               for r_ in rules]
    return res


def probe(fams, jobs, include_proven, chunk, fails_only=False, tactic="rule_auto"):
    rows = load_class()
    done = proven()
    tasks = []
    for fam in fams:
        rules = [r for r in rows if r["fam"] == fam and r["cls"] in PURE
                 and (include_proven or short(r["q"]) not in done)]
        prev = os.path.join(TMP, f"probe-{fam}.tsv")
        if fails_only and os.path.exists(prev):
            okq = {l.split("\t")[0] for l in open(prev) if l.split("\t")[1] == "OK"}
            rules = [r for r in rules if r["q"] not in okq]
        for i in range(0, len(rules), chunk):
            tasks.append((fam, rules[i:i + chunk], i // chunk, tactic))
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


MOD_HDR = """import {tacmod}
{imports}

/-!
# Rule lemmas: `{fam}` rules{part}

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P1/P2 rules whose top op is in the
`{fam}` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

"""


def emit(fam, chunk, tactic="rule_auto"):
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
                             tacmod=TACTICS[tactic],
                             part="" if part == 1 else f" (part {part})")
        for q in group:
            doc = rows[q]["doc"]
            src += f"/-- {doc} -/\n" if doc else ""
            src += f"theorem {short(q)}_sound : Rule.Sound {q} := by {tactic}\n\n"
        src += "end GoFV.Proof.Rules\n"
        out = os.path.join(PROOF, name + ".lean")
        assert not os.path.exists(out), out
        open(out, "w").write(src)
        print(f"wrote {out}: {len(group)} lemmas")


PROVEN_DATA = os.path.join(ROOT, "GoFV", "Rules", "Proven.lean")
PROVEN_THM = os.path.join(PROOF, "Proven.lean")
PROVEN_SETS = [("Generic", "generic"), ("Divisible", "divisible"), ("Divmod", "divmod")]


def proven_sets():
    """Write the proven-only rule sets (GoFV/Rules/Proven.lean) and their soundness theorems
    (GoFV/Proof/Rules/Proven.lean) from the `r_*_sound` theorems."""
    kinds = proven_kinds()
    done = proven()
    hdr = "-- Generated by scripts/rule-proofs.py proven from the `r_*_sound` theorems of " \
          "GoFV/Proof/Rules. Do not edit.\n"
    data = hdr + "".join(f"import GoFV.Rules.Generated.{f}\n" for f, _ in PROVEN_SETS) + """
/-!
# Proven-only rule sets

The rule sets of `opt`, `divisible` and `divmod` restricted to the rules with a merged
`Rule.Sound` or `Rule.SoundT` lemma (value rules), `BlockRule.Sound` lemma (block rules),
`EffectRule.NilElim` lemma (nil-check eliminations), `EffectRule.LoadFwd` lemma (Load-of-Store
forwardings) or `EffectRule.StructLoad` lemma (struct-load expansions; issue #151,
`docs/proofs/rules.md`), in matching order: the rule sets of the proven-only rewrite passes
(`GoFV.Opt.optProven`, …; issue #113).
-/

namespace GoFV.Rules.Proven

open GoFV.Rules
"""
    thm = hdr + "import GoFV.Rules.Proven\nimport GoFV.Proof.Rules.AllSound\n" + "".join(
        f"import GoFV.Proof.Rules.{m}\n" for m in sorted(set(done.values()))) + """
/-!
# Every rule of the proven-only rule sets is sound

The proven-only rule sets (`GoFV.Rules.Proven`) satisfy `RuleSet.AllSound` by the rule lemmas.
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

"""
    total = 0
    for f, low in PROVEN_SETS:
        src = open(os.path.join(GEN, f + ".lean")).read()
        order = re.findall(r"\(\.(\w+), ops_(\w+)\)", src)
        ops = {}
        for mod in sorted(os.listdir(os.path.join(GEN, f))):
            s = open(os.path.join(GEN, f, mod)).read()
            for m in re.finditer(r"^def ops_(\w+) : List Rule := \[(.*)\]$", s, re.M):
                ops[m.group(1)] = [n.strip() for n in m.group(2).split(",") if n.strip()]
        border = re.findall(r"\(\.(\w+), blocks_(\w+)\)", src)
        blks = {}
        for mod in sorted(os.listdir(os.path.join(GEN, f))):
            s = open(os.path.join(GEN, f, mod)).read()
            for m in re.finditer(r"^def blocks_(\w+) : List BlockRule := \[(.*)\]$", s, re.M):
                blks[m.group(1)] = [n.strip() for n in m.group(2).split(",") if n.strip()]
        effects = ("EffectRule.NilElim", "EffectRule.LoadFwd", "EffectRule.StructLoad")
        vals, bvals, nils, loads, sloads = [], [], [], [], []
        for op, key in order:
            rs = [n for n in ops[key] if n in done and kinds[n][1] not in effects]
            nils += [n for n in ops[key] if n in done and kinds[n][1] == "EffectRule.NilElim"]
            loads += [n for n in ops[key] if n in done and kinds[n][1] == "EffectRule.LoadFwd"]
            sloads += [n for n in ops[key] if n in done and kinds[n][1] == "EffectRule.StructLoad"]
            if rs:
                vals.append((op, rs))
        for k, key in border:
            rs = [n for n in blks[key] if n in done]
            if rs:
                bvals.append((k, rs))
        n = sum(len(rs) for _, rs in vals)
        nb = sum(len(rs) for _, rs in bvals)
        total += n + nb + len(nils) + len(loads) + len(sloads)
        q = f"Generated.{f}"
        body = ",\n    ".join(f"(.{op}, [{', '.join(q + '.' + r for r in rs)}])" for op, rs in vals)
        bbody = ",\n    ".join(f"(.{k}, [{', '.join(q + '.' + r for r in rs)}])" for k, rs in bvals)
        data += f"""
/-- `{low}.rules` restricted to its {n} proven value rules, {nb} proven block rules, {len(nils)}
nil-check eliminations, {len(loads)} Load-of-Store forwardings and {len(sloads)} struct-load
expansions. -/
def {low} : RuleSet where
  name := "{low}"
  values := [{body}]
  blocks := [{bbody}]
  nilChecks := [{', '.join(q + '.' + r for r in nils)}]
  loads := [{', '.join(q + '.' + r for r in loads)}]
  structLoads := [{', '.join(q + '.' + r for r in sloads)}]
"""
        def conj(groups):
            if not groups:
                return f"(by simp [Proven.{low}, ForallL])"
            def pf(r):
                if kinds[r][1] == "Rule.Sound":
                    return f"Rule.soundT_of_sound {r}_sound rfl"
                return f"{r}_sound"
            proofs = ",\n    ".join(
                "⟨" + ", ".join(pf(r) for r in rs) + ", trivial⟩" for _, rs in groups)
            return f"""(by
    simp only [Proven.{low}, ForallL]
    exact ⟨{proofs}, trivial⟩)"""
        thm += f"""/-- Every rule of `Proven.{low}` is sound. -/
theorem {low}_allSound : Proven.{low}.AllSound :=
  RuleSet.allSound_of {conj(vals)}
    {conj(bvals)}

"""
    data += "\nend GoFV.Rules.Proven\n"
    thm += "end GoFV.Proof.Rules\n"
    open(PROVEN_DATA, "w").write(data)
    open(PROVEN_THM, "w").write(thm)
    print(f"wrote {PROVEN_DATA} and {PROVEN_THM}: {total} rules")


def table():
    rows = load_class()
    done = proven()
    bad = false_rules()
    classes = ["P1", "P2", "mem", "call", "float", "ptr", "phi", "block"]
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
    lines = ["| File | Family | Proven | Pending (P1/P2) | False | Not pure | Total |",
             "| --- | --- | --: | --: | --: | --: | --: |"]
    tot = [0, 0, 0, 0, 0]
    for (f, fam), rs in sorted(fams.items()):
        p = sum(1 for r in rs if short(r["q"]) in done)
        fl = sum(1 for r in rs if short(r["q"]) in bad)
        pend = sum(1 for r in rs if r["cls"] in PURE and short(r["q"]) not in done
                   and short(r["q"]) not in bad)
        np = sum(1 for r in rs if r["cls"] not in PURE)
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
    print(f"proven {tot[0]}, pending {tot[1]}, false {tot[2]}, not pure {tot[3]}, total {tot[4]}")


def sat():
    """Satisfying instances (`GoFVTest/Proof/RuleSat.lean`) joined with the classification."""
    names = rule_names()
    cmd = [os.path.join(ROOT, "scripts", "memcap.sh"), "lake", "exe", "rule-sat"]
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(r.stderr + r.stdout)
    cls = {r_["q"]: r_ for r_ in load_class()}
    done = proven()
    bad = false_rules()
    rows = []
    for line in r.stdout.splitlines():
        parts = line.split(" ", 3)
        if len(parts) < 3:
            continue
        q = names[(parts[0], parts[1])][0]
        rows.append((q, parts[2], parts[3] if len(parts) > 3 else ""))
    with open(os.path.join(TMP, "sat.tsv"), "w") as fh:
        for row in rows:
            fh.write("\t".join(row) + "\n")
    cnt = collections.Counter((cls[q]["cls"] in PURE, st) for q, st, _ in rows)
    print(f"P1/P2: SAT {cnt[(True, 'SAT')]}, CEX {cnt[(True, 'CEX')]}, NONE {cnt[(True, 'NONE')]}; "
          f"other: SAT {cnt[(False, 'SAT')]}, CEX {cnt[(False, 'CEX')]}, "
          f"NONE {cnt[(False, 'NONE')]}")
    for q, st, inst in rows:
        if st == "CEX" and cls[q]["cls"] in PURE:
            mark = " (false: " + bad[short(q)] + ")" if short(q) in bad else ""
            print(f"CEX {short(q)}{mark}: {cls[q]['doc']}\n    {inst}")
    fails = [(q, st) for q, st, _ in rows if short(q) in done and st != "SAT"]
    for q, st in fails:
        print(f"proven but {st}: {short(q)}")
    print(f"proven: {len(done)}, with an instance: {len(done) - len(fails)}")
    if fails:
        sys.exit(1)


def fire(corpus):
    """Firing frequencies and obstacles of the proven-only passes (`GoFVTest/RuleFireProbe.lean`)
    joined with the rule names and classes; rewrites the `fire` table of docs/proofs/rules.md."""
    if corpus is None:
        main_root = subprocess.run(["git", "worktree", "list", "--porcelain"], cwd=ROOT,
                                   capture_output=True, text=True).stdout.split("\n")[0].split()[1]
        corpus = os.path.realpath(sorted(
            __import__("glob").glob(os.path.join(os.path.dirname(main_root), "gofv-corpus", "*",
                                                 "plain")))[-1])
    cmd = [os.path.join(ROOT, "scripts", "memcap.sh"), "lake", "exe", "rule-fire-probe", corpus]
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(r.stderr + r.stdout)
    idx = collections.defaultdict(list)
    for row in load_class():
        if m := re.match(r"`(\w+)\.rules:(\d+)`", row["doc"]):
            idx[(m.group(1), m.group(2), row["op"])].append(row)
    summary, rows = "", []
    for line in r.stdout.splitlines():
        if line.startswith("SUMMARY"):
            summary = line
        elif line.startswith("RULE\t"):
            _, k, pr, n, sole, unb = line.split("\t")
            loc, op = k.split(" ", 1)
            f, ln = loc.split(":")
            if op.startswith("block "):
                rows.append((f"{f}.rules:{ln} {op}", f"r_{f}_{ln}", "block", pr == "true", int(n),
                             int(sole), int(unb)))
                continue
            rs = idx.get((f, ln, op), [])
            name = "/".join(short(x["q"]) for x in rs) or "?"
            cls = rs[0]["cls"] if rs else "?"
            rows.append((f"{f}.rules:{ln} {op}", name, cls, pr == "true", int(n), int(sole), int(unb)))
    rows.sort(key=lambda x: (-x[6], -x[5], -x[4]))
    with open(os.path.join(TMP, "fire.tsv"), "w") as fh:
        for row in rows:
            fh.write("\t".join(map(str, row)) + "\n")
    m = re.search(r"functions (\d+) proven-only-at-stock (\d+) checked-at-stock (\d+) "
                  r"validator-only (\d+) off-stock-by-unproven-count #\[(\d+), (\d+), (\d+), (\d+)\]",
                  summary)
    fns, pa, ca, vo, c0, c1, c2, c3 = map(int, m.groups())
    lines = [f"Corpus `{os.path.basename(os.path.dirname(corpus))}/{os.path.basename(corpus)}`: "
             f"{fns} functions with a rewrite section; every section at stock under the proven-only "
             f"passes {pa}, under the checked passes {ca} (validator the only obstacle: {vo}). "
             f"Functions off stock by the number of unproven rules the full passes fire on their "
             f"sections off stock: 0: {c0}, 1: {c1}, 2: {c2}, 3 or more: {c3}.", "",
             "| Rule | Lemma | Class | Firings | Sole obstacle | Unblocks |",
             "| --- | --- | --- | --: | --: | --: |"]
    unproven = [x for x in rows if not x[3]]
    shown = [x for x in unproven if x[6] > 0 or x[5] > 0]
    shown += sorted([x for x in unproven if x[6] == 0 and x[5] == 0], key=lambda x: -x[4])[:15]
    for k, name, cls, _, n, sole, unb in shown:
        lines.append(f"| `{k}` | `{name}` | {cls} | {n} | {sole} | {unb} |")
    doc = open(DOC).read()
    doc = re.sub(r"(<!-- BEGIN fire -->\n).*?(<!-- END fire -->)",
                 lambda mm: mm.group(1) + "<!-- Generated by scripts/rule-proofs.py fire. -->\n\n"
                 + "\n".join(lines) + "\n\n" + mm.group(2), doc, flags=re.S)
    open(DOC, "w").write(doc)
    print(summary)
    print(f"{len(shown)} rows; top: " + ", ".join(f"{x[0]} ({x[6]})" for x in shown[:8]))


STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def axioms():
    """`#print axioms` of every theorem of the proof modules (built first); fails on any axiom
    other than the standard three and `bv_decide`'s `_native` ones."""
    mods, thms = [], []
    for fn in sorted(os.listdir(PROOF)):
        if not fn.endswith(".lean"):
            continue
        mods.append(f"GoFV.Proof.Rules.{fn[:-5]}")
        ns = []  # the namespaces open at each `theorem` (helper lemmas of a module may live
        # in a sub-namespace, e.g. `GoFV.Proof.Rules.Divisible`)
        for line in open(os.path.join(PROOF, fn)):
            if m := re.match(r"namespace (\S+)", line):
                ns.append(m.group(1))
            elif re.match(r"end (\S+)", line) and ns and line.split()[1] == ns[-1]:
                ns.pop()
            elif m := re.match(r"theorem (\S+)", line):
                thms.append(".".join(ns + [m.group(1)]))
    os.makedirs(TMP, exist_ok=True)
    path = os.path.join(TMP, "Axioms.lean")
    open(path, "w").write("".join(f"import {m}\n" for m in mods) +
                          "".join(f"#print axioms {t}\n" for t in thms))
    r = lean(os.path.relpath(path, ROOT))
    out = r.stdout + r.stderr
    bad, seen = [], 0
    for m in re.finditer(r"'(\S+)' depends on axioms: \[(.*?)\]", out, re.S):
        seen += 1
        ax = {a.strip() for a in m.group(2).split(",") if a.strip()}
        other = {a for a in ax - STD_AXIOMS if "_native.bv_decide.ax_" not in a}
        if other:
            bad.append((m.group(1), sorted(other)))
    seen += len(re.findall(r"does not depend on any axioms", out))
    for t, ax in bad:
        print(f"{t}: {', '.join(ax)}")
    print(f"{seen}/{len(thms)} theorems checked, {len(bad)} with other axioms")
    if bad or seen != len(thms) or r.returncode != 0:
        sys.exit(out[-2000:] if seen != len(thms) else 1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd",
                    choices=["classify", "probe", "emit", "table", "sat", "axioms", "proven",
                             "fire"])
    ap.add_argument("fams", nargs="*")
    ap.add_argument("-j", "--jobs", type=int, default=2)
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--chunk", type=int, default=40)
    ap.add_argument("--fails", action="store_true", help="re-probe only the rules that failed")
    ap.add_argument("--tactic", choices=sorted(TACTICS), default="rule_auto")
    a = ap.parse_args()
    if a.cmd == "classify":
        classify()
    elif a.cmd == "probe":
        probe(a.fams, a.jobs, a.all, a.chunk, a.fails, a.tactic)
    elif a.cmd == "emit":
        for fam in a.fams:
            emit(fam, a.chunk, a.tactic)
    elif a.cmd == "sat":
        sat()
    elif a.cmd == "axioms":
        axioms()
    elif a.cmd == "proven":
        proven_sets()
    elif a.cmd == "fire":
        fire(a.fams[0] if a.fams else None)
    else:
        table()


if __name__ == "__main__":
    main()
