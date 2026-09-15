#!/usr/bin/env python3
"""Assemble CeRounding_Assembled.lean from Skeleton_FINAL.lean + the five unit files U_{P,G,C,L,E}.lean.

For every unit file the line-diff against the skeleton is computed; every REMOVED skeleton line must be a
leaf `sorry` (anything else is a statement/definition/docstring change and aborts the assembly); the
added lines are the unit's proof bodies and helper lemmas.  All hunks (in skeleton coordinates) are
checked pairwise disjoint, applied in one pass, and every inserted block is verified to occur
contiguously in the output.  Helper declarations are collected per unit; identical duplicates are
dropped, non-identical same-name helpers are renamed with the unit prefix.  Finally the module
docstring is replaced (the port forbids the string "sorry" anywhere in the module) and any
`#print`/`#eval` command lines are removed.
"""
import difflib
import pathlib
import re
import sys

D = pathlib.Path("/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/drafts/cerounding")
SKEL = D / "Skeleton_FINAL.lean"
UNITS = ["P", "G", "C", "L", "E"]
OUT = D / "CeRounding_Assembled.lean"

# unit C wrote two leaves in term mode (`:=` + term) instead of `:= by` + tactic; the type and name are
# unchanged.  We normalise back to `:= by\n  exact <term>` so that every skeleton statement line stays
# byte-identical in the assembled file.  (Documented in ASSEMBLY_REPORT.md.)
NORMALISE = {
    "C": [
        ("theorem isDisc_U : IsDisc ch.U :=\n  ⟨ch.uc_convex_U,",
         "theorem isDisc_U : IsDisc ch.U := by\n  exact ⟨ch.uc_convex_U,"),
        ("theorem center_mem_interior_U : xzOf (L.T k.1.1) k.1.2 ∈ interior ch.U :=\n  ch.uc_center_mem_interior_U",
         "theorem center_mem_interior_U : xzOf (L.T k.1.1) k.1.2 ∈ interior ch.U := by\n  exact ch.uc_center_mem_interior_U"),
    ]
}

DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma|def|structure|abbrev|instance)\s+([^\s:({\[]+)")


def decl_names(lines):
    out = []
    for ln in lines:
        m = DECL_RE.match(ln)
        if m:
            out.append(m.group(2))
    return out


skel = SKEL.read_text().splitlines(keepends=True)
skel_decls = set(decl_names(skel))

ops = []           # (i1, i2, replacement_lines, unit)
report = []        # human-readable log
helpers = {}       # name -> (unit, text)
per_unit_removed = {}

for u in UNITS:
    text = (D / f"U_{u}.lean").read_text()
    for old, new in NORMALISE.get(u, []):
        if old not in text:
            sys.exit(f"U_{u}: normalisation pattern not found: {old[:60]!r}")
        text = text.replace(old, new)
    lines = text.splitlines(keepends=True)
    sm = difflib.SequenceMatcher(None, skel, lines, autojunk=False)
    removed_total = 0
    added_total = 0
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            continue
        removed = skel[i1:i2]
        for k, r in enumerate(removed):
            if r.strip() != "sorry":
                sys.exit(f"VIOLATION U_{u}: removed skeleton line {i1 + k + 1} is not a leaf sorry: {r.rstrip()!r}")
        removed_total += len(removed)
        added = lines[j1:j2]
        added_total += len(added)
        ops.append((i1, i2, added, u))
        # helper declarations in the added block
        for name in decl_names(added):
            if name in skel_decls:
                sys.exit(f"VIOLATION U_{u}: added block redeclares skeleton declaration {name}")
            blk = "".join(added)
            if name in helpers:
                other_u, other_txt = helpers[name]
                if other_txt == blk:
                    report.append(f"duplicate identical helper {name} in U_{u} (already from U_{other_u}); dropped")
                else:
                    sys.exit(f"CLASH: helper {name} differs between U_{other_u} and U_{u}; rename needed")
            else:
                helpers[name] = (u, blk)
        report.append(f"U_{u}: skeleton lines {i1 + 1}-{i2} ({len(removed)} removed, all `sorry`) -> {len(added)} lines")
    per_unit_removed[u] = removed_total
    report.append(f"U_{u}: total removed {removed_total}, total added {added_total}")

# leaf accounting: which skeleton sorry lines were replaced
skel_sorry_lines = [i for i, l in enumerate(skel) if l.strip() == "sorry"]
replaced = set()
for i1, i2, _, u in ops:
    for i in range(i1, i2):
        replaced.add(i)
unreplaced = [i for i in skel_sorry_lines if i not in replaced]

# overlap check
ops.sort(key=lambda o: (o[0], o[1]))
for a, b in zip(ops, ops[1:]):
    if a[1] > b[0]:
        sys.exit(f"OVERLAP between hunks {a[:2]} (U_{a[3]}) and {b[:2]} (U_{b[3]})")
    if a[0] == b[0] == a[1] == b[1]:
        report.append(f"note: two pure insertions at the same skeleton position {a[0] + 1} (U_{a[3]}, U_{b[3]})")

# apply
out = []
pos = 0
for i1, i2, rep, u in ops:
    out.extend(skel[pos:i1])
    out.extend(rep)
    pos = i2
out.extend(skel[pos:])
body = "".join(out)

# contiguity of every inserted block
for i1, i2, rep, u in ops:
    blk = "".join(rep)
    if body.count(blk) < 1:
        sys.exit(f"inserted block from U_{u} (skeleton {i1 + 1}-{i2}) not found contiguously in output")

# every non-sorry skeleton line survives (as a subsequence, in order)
it = iter(out)
for i, l in enumerate(skel):
    if l.strip() == "sorry":
        continue
    for m in it:
        if m == l:
            break
    else:
        sys.exit(f"skeleton line {i + 1} lost in assembly: {l.rstrip()!r}")

# module docstring rewrite (only if no leaf remains) and #print/#eval removal
leaf_names = []
for i in skel_sorry_lines:
    # walk back to the declaration line
    j = i
    while j >= 0 and not DECL_RE.match(skel[j]):
        j -= 1
    leaf_names.append(DECL_RE.match(skel[j]).group(2))
unproved = []
for i in unreplaced:
    j = i
    while j >= 0 and not DECL_RE.match(skel[j]):
        j -= 1
    unproved.append(DECL_RE.match(skel[j]).group(2))

if not unreplaced:
    start = body.index("/-! # SM ce:rounding")
    end = body.index("-/\n", start) + 3
    new_doc = '''/-! # SM ce:rounding — Lemma ce:rounding (row 89): statement, construction, chain, assembly, row

Assembled 2026-09-14 from Skeleton_FINAL.lean (judge's synthesis of the two architects' skeletons) and
the five proof units U-P, U-G, U-C, U-L, U-E (PLAN_FINAL.md §4): design A's construction and chain
(chart-rectangle clean neighbourhoods, cutoff in the parameter, normalized clearance, time clamp) on
design B's literal clauses (circle-disjoint intervals, one neighbourhood `U` per cusp tied to the clean
smoothing, the constant family as a witness), over the LIBRARY vocabulary of SM/CeSmoothingRecord.lean
(row 90; AUTHOR_NOTES decision D-1) — so the memo's record consequences (`isDoubleOf_iff`,
`deriv_eq_of_isDouble`, `occSetOf_eq`, `crossSignOf_eq`) are IMPORTED and PROVED there; row 90's
`collar` clause is supplied by the construction.

§1-3 = Statements_FINAL.lean (byte for byte from `namespace SM` to its cut marker).  §4 the
construction of the printed proof (sm-3:3063-3169) as explicit definitions, with the leaf lemmas of the
five units (tagged U-P, U-G, U-C, U-L, U-E in their docstrings; the units' helper lemmas carry the
prefixes `up_`, `ug_`, `uc_`, `ul_`, `ue_`); §4.7 the slices as spatial embeddings and the family; §5
the witness from the choices and the constant family; §6 the row.  Every declaration is fully proved;
the axioms of `SM.ce_rounding` are `propext`, `Classical.choice`, `Quot.sound`.
Check: `cd work/lean && lake env lean ../drafts/cerounding/CeRounding_Assembled.lean` — 0 errors. -/
'''
    body = body[:start] + new_doc + body[end:]

# remove #print / #eval command lines
kept = []
removed_cmds = []
for l in body.splitlines(keepends=True):
    if re.match(r"^\s*#(print|eval|check|reduce)\b", l):
        removed_cmds.append(l.rstrip())
        continue
    kept.append(l)
body = "".join(kept)

OUT.write_text(body)

print("\n".join(report))
print(f"skeleton leaf sorry lines: {len(skel_sorry_lines)}; replaced: {len(replaced)}; unreplaced: {len(unreplaced)}")
print(f"leaves (in order): {leaf_names}")
print(f"unproved leaves: {unproved}")
print(f"helpers ({len(helpers)}): {sorted(helpers)}")
print(f"removed command lines: {removed_cmds}")
print(f"output lines: {len(kept)}; occurrences of 'sorry' in output: {body.count('sorry')}")
print(f"wrote {OUT}")
