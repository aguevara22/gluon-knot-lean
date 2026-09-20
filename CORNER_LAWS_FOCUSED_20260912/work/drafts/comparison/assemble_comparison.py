#!/usr/bin/env python3
"""Assemble Comparison_Assembled.lean from Statements_FINAL.lean + the unit file(s) of the comparison lane.

Assembly rule (PLAN_FINAL.md §4): the FINAL file IS the skeleton — the unit replaces the ONE leaf's `sorry`
(`cusp_deletion_generic`, sm-6:335-359) by its proof and inserts `cu_`-prefixed helpers before it; the
three §5 row-theorem placeholders (`prop_anchor_values`, `thm_comparison`, `cor_C_inherits`) stay `sorry`
until rows 110/112 land.  For every unit file the line diff against the skeleton is re-derived (difflib,
autojunk off); every REMOVED skeleton line must be the leaf's `sorry` (anything else is a statement /
definition / name / docstring change and aborts); every ADDED declaration must carry the unit's prefix and
must not redeclare a skeleton name.  Hunks are checked pairwise disjoint, applied in one pass, every
inserted block is verified to occur contiguously in the output, every non-sorry skeleton line is verified
to survive in order, and every skeleton declaration statement (declaration line through its `:= by` / `:=`
/ `where` terminator, or the whole `structure` block) is verified to be a contiguous byte-identical
substring of the output.  Identical duplicate helpers across units are dropped; differing same-name
helpers abort.  Finally the module docstring's state paragraph is rewritten (exact-match replacement,
aborts if the paragraph is not found verbatim) and any `#print` / `#eval` / `#check` / `#reduce` command
lines are removed (none are expected).
"""
import difflib
import pathlib
import re
import sys

D = pathlib.Path("/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/drafts/comparison")
SKEL = D / "Statements_FINAL.lean"
UNITS = [("CUSPGEN", "cu_", ["cusp_deletion_generic"])]   # (unit suffix, helper prefix, leaves it owns)
OUT = D / "Comparison_Assembled.lean"
PLACEHOLDERS = ["prop_anchor_values", "thm_comparison", "cor_C_inherits"]   # §5, must keep their sorry

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|structure|abbrev|instance|class|inductive|axiom|opaque)\s+([^\s:({\[]+)")
TOP_RE = re.compile(r"^(theorem|lemma|def|noncomputable def|structure|instance|example|abbrev|/-|end |section|"
                    r"namespace|open|variable|--|#|set_option|@\[|class|inductive|axiom)")


def decl_names(lines):
    return [(i, m.group(1), m.group(2)) for i, ln in enumerate(lines) if (m := DECL_RE.match(ln))]


def owning_decl(lines, i):
    """Name of the declaration whose body contains line i (walk back to the declaration line)."""
    j = i
    while j >= 0 and not DECL_RE.match(lines[j]):
        j -= 1
    return DECL_RE.match(lines[j]).group(2) if j >= 0 else None


def statement_text(lines, i):
    """The statement of the declaration starting at line i: through the first line ending in `:= by`, `:=`
    or `where` (the terminator line included); for a `structure … where` the whole block (all fields,
    up to the next top-level line)."""
    kind = DECL_RE.match(lines[i]).group(1)
    j = i
    if kind in ("structure", "class", "inductive"):
        j = i + 1
        while j < len(lines) and (lines[j].strip() == "" or not TOP_RE.match(lines[j])):
            j += 1
        while j > i and lines[j - 1].strip() == "":
            j -= 1
        return "".join(lines[i:j])
    # scan forward for the first `:=` or ` where` at bracket depth 0 (binders such as
    # `(by have := hf.1; omega)` contain `:=` at depth > 0 and are part of the statement)
    text = "".join(lines[i:])
    depth = 0
    k = 0
    while k < len(text):
        c = text[k]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif depth == 0 and text.startswith(":=", k):
            return text[: k + 2]
        elif depth == 0 and text.startswith(" where", k) and text[k + 6: k + 7] in ("\n", " ", ""):
            return text[: k + 6]
        k += 1
    sys.exit(f"no statement terminator found for declaration at skeleton line {i + 1}")


skel = SKEL.read_text(encoding="utf-8").splitlines(keepends=True)
skel_decls = decl_names(skel)
skel_names = {n for _, _, n in skel_decls}
skel_sorry_lines = [i for i, l in enumerate(skel) if l.strip() == "sorry"]
skel_sorry_owner = {i: owning_decl(skel, i) for i in skel_sorry_lines}

ops = []           # (i1, i2, replacement_lines, unit)
report = []
helpers = {}       # name -> (unit, kind, text)
leaves_filled = {} # leaf name -> unit

for u, prefix, owned in UNITS:
    upath = D / f"U_{u}.lean"
    lines = upath.read_text(encoding="utf-8").splitlines(keepends=True)
    sm = difflib.SequenceMatcher(None, skel, lines, autojunk=False)
    removed_total = added_total = 0
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            continue
        removed = skel[i1:i2]
        for k, r in enumerate(removed):
            if r.strip() != "sorry":
                sys.exit(f"VIOLATION U_{u}: removed skeleton line {i1 + k + 1} is not a leaf sorry: {r.rstrip()!r}")
            owner = skel_sorry_owner[i1 + k]
            if owner in PLACEHOLDERS:
                sys.exit(f"VIOLATION U_{u}: touched the §5 placeholder `{owner}` (skeleton line {i1 + k + 1})")
            if owner not in owned:
                sys.exit(f"VIOLATION U_{u}: filled a leaf it does not own: `{owner}` (skeleton line {i1 + k + 1})")
            leaves_filled[owner] = u
        removed_total += len(removed)
        added = lines[j1:j2]
        added_total += len(added)
        ops.append((i1, i2, added, u))
        for _, kind, name in decl_names(added):
            if name in skel_names:
                sys.exit(f"VIOLATION U_{u}: added block redeclares skeleton declaration `{name}`")
            if not name.startswith(prefix):
                sys.exit(f"VIOLATION U_{u}: helper `{name}` lacks the unit prefix `{prefix}`")
            blk = "".join(added)
            if name in helpers:
                ou, okind, otxt = helpers[name]
                if otxt == blk:
                    report.append(f"duplicate identical helper `{name}` in U_{u} (already from U_{ou}); dropped")
                else:
                    sys.exit(f"CLASH: helper `{name}` differs between U_{ou} and U_{u}; rename needed")
            else:
                helpers[name] = (u, kind, blk)
        kind_desc = "pure insertion" if i1 == i2 else f"{len(removed)} removed (all `sorry`)"
        report.append(f"U_{u}: hunk at skeleton {i1 + 1}{'' if i1 == i2 else '-' + str(i2)}: {kind_desc} -> {len(added)} lines added"
                      + (f" (leaf `{skel_sorry_owner[i1]}`)" if i1 != i2 else ""))
    report.append(f"U_{u}: total removed {removed_total}, total added {added_total}")

# leaf accounting
replaced = {i for i1, i2, _, _ in ops for i in range(i1, i2)}
unreplaced = [i for i in skel_sorry_lines if i not in replaced]
unproved = [skel_sorry_owner[i] for i in unreplaced if skel_sorry_owner[i] not in PLACEHOLDERS]
placeholders_left = [skel_sorry_owner[i] for i in unreplaced if skel_sorry_owner[i] in PLACEHOLDERS]
if sorted(placeholders_left) != sorted(PLACEHOLDERS):
    sys.exit(f"VIOLATION: §5 placeholders not all intact: {placeholders_left}")

# overlap check
ops.sort(key=lambda o: (o[0], o[1]))
for a, b in zip(ops, ops[1:]):
    if a[1] > b[0]:
        sys.exit(f"OVERLAP between hunks {a[:2]} (U_{a[3]}) and {b[:2]} (U_{b[3]})")

# apply
out, pos = [], 0
for i1, i2, rep, u in ops:
    out.extend(skel[pos:i1])
    out.extend(rep)
    pos = i2
out.extend(skel[pos:])
body = "".join(out)

# contiguity of every inserted block
for i1, i2, rep, u in ops:
    if body.count("".join(rep)) < 1:
        sys.exit(f"inserted block from U_{u} (skeleton {i1 + 1}-{i2}) not found contiguously in output")

# every non-sorry skeleton line survives, in order
it = iter(out)
for i, l in enumerate(skel):
    if l.strip() == "sorry":
        continue
    for m in it:
        if m == l:
            break
    else:
        sys.exit(f"skeleton line {i + 1} lost in assembly: {l.rstrip()!r}")

# every skeleton declaration statement is a contiguous byte-identical substring of the output
stmt_checked = 0
for i, kind, name in skel_decls:
    st = statement_text(skel, i)
    if body.count(st) != 1:
        sys.exit(f"statement of `{name}` (skeleton line {i + 1}) not found exactly once in output (count {body.count(st)})")
    stmt_checked += 1
# every skeleton docstring block (`/-- … -/`) survives verbatim
doc_checked = 0
skel_text = "".join(skel)
for m in re.finditer(r"/--.*?-/\n", skel_text, re.S):
    if m.group(0) not in body:
        sys.exit(f"docstring lost: {m.group(0)[:60]!r}")
    doc_checked += 1

# module docstring: rewrite ONLY the state paragraph and the title line (exact match; abort if drifted)
OLD_TITLE = "/-! # Statements_FINAL — comparison lane: rows 122 prop:anchor-values, 127 thm:comparison,\n128 cor:C-inherits (judge's decision, 2026-09-15)\n"
NEW_TITLE = ("/-! # Comparison_Assembled — comparison lane: rows 122 prop:anchor-values, 127 thm:comparison,\n"
             "128 cor:C-inherits (judge's decision, 2026-09-15; assembled 2026-09-15 by assemble_comparison.py from\n"
             "Statements_FINAL.lean + unit U-CM-CUSPGEN, work/drafts/comparison/ASSEMBLY_REPORT.md)\n")
OLD_STATE = ("Every `sorry` is either (a) the ONE LEAF of PLAN_FINAL.md §4 (`cusp_deletion_generic`, sm-6:335-359,\n"
             "frozen statement, unit U-CM-CUSPGEN), or (b) one of the three ROW THEOREMS of §5, which become one-liners\n"
             "once rows 110 (`SM.thm_C_S7 : CS7Data`) and 112 (`SM.thm_C_soft : CSoftData`) land (D-F11/D-F14: declared\n"
             "and mapped only then).  Everything else is PROVED from accepted declarations: the whole of row 122 modulo\n")
NEW_STATE = ("The ONE LEAF of PLAN_FINAL.md §4 (`cusp_deletion_generic`, sm-6:335-359, frozen statement, unit U-CM-CUSPGEN)\n"
             "is PROVED (helpers `cu_*`, §4; axioms `propext`, `Classical.choice`, `Quot.sound`).  The only remaining\n"
             "`sorry` bodies are the three ROW THEOREMS of §5, which become one-liners once rows 110\n"
             "(`SM.thm_C_S7 : CS7Data`) and 112 (`SM.thm_C_soft : CSoftData`) land (D-F11/D-F14: declared and mapped\n"
             "only then).  Everything else is PROVED from accepted declarations: the whole of row 122 modulo\n")
OLD_CHECK = "Check: `cd work/lean && lake env lean ../drafts/comparison/Statements_FINAL.lean`."
NEW_CHECK = "Check: `cd work/lean && lake env lean ../drafts/comparison/Comparison_Assembled.lean`."
for old, new, what in ((OLD_TITLE, NEW_TITLE, "title"), (OLD_STATE, NEW_STATE, "state paragraph"), (OLD_CHECK, NEW_CHECK, "check line")):
    if body.count(old) != 1:
        sys.exit(f"module docstring {what} not found exactly once; header drifted — refusing to rewrite")
    body = body.replace(old, new)

# remove #print / #eval / #check / #reduce command lines
kept, removed_cmds = [], []
for l in body.splitlines(keepends=True):
    if re.match(r"^\s*#(print|eval|check|reduce|exit)\b", l):
        removed_cmds.append(l.rstrip())
        continue
    kept.append(l)
body = "".join(kept)
OUT.write_text(body, encoding="utf-8")

print("\n".join(report))
print(f"skeleton sorry lines: {len(skel_sorry_lines)} = leaves {[skel_sorry_owner[i] for i in skel_sorry_lines if skel_sorry_owner[i] not in PLACEHOLDERS]} + placeholders {PLACEHOLDERS}")
print(f"leaves filled: {leaves_filled}")
print(f"unproved leaves: {unproved}")
print(f"§5 placeholders intact (sorry kept): {placeholders_left}")
print(f"helpers ({len(helpers)}): " + ", ".join(f"{n} ({k})" for n, (u, k, _) in helpers.items()))
print(f"skeleton declaration statements verified byte-identical & unique in output: {stmt_checked}/{len(skel_decls)}")
print(f"skeleton docstring blocks verified present: {doc_checked}")
print(f"removed command lines: {removed_cmds}")
print(f"output lines: {len(kept)}; occurrences of 'sorry' in output: {body.count('sorry')}; lines containing sorry: "
      f"{[i + 1 for i, l in enumerate(kept) if 'sorry' in l]}")
print(f"wrote {OUT}")
