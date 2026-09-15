#!/usr/bin/env python3
"""Assemble TN_Assembled.lean from TN_Skeleton.lean + the unit files TN_U_{A..F}.lean.

Pass 1 (faithful assembly).  For each unit, `diff skeleton unit` (normal format) is parsed hunk by
hunk.  Allowed hunks: `c` replacing exactly one `  sorry` line; `a` inserting helper lines; `d` only
when every removed non-`sorry`/non-blank line reappears verbatim and contiguously inside an `a`
hunk of the SAME unit (a relocation — unit D moved LEAF D4 below LEAF A7, which it uses).  Any
other removal is a statement/docstring violation and aborts.  Overlaps between units abort.  The
hunks are then applied in one pass over the skeleton; every inserted block is checked to occur
exactly once, contiguously; helper names are checked for duplicates across units.

Pass 2 (repair of the false leaf C2, see TN_U_C_REPORT.md §2).  `hasCompactSupport_Yfield` is
FALSE (the first component `χ_τ(τ)` of `Yfield` is `1` on `{0} × ℝ × ℝ²`; kernel-checked as
`tc2_not_hasCompactSupport_Yfield`).  The leaf is removed and the two skeleton theorems built on it
are re-proved from the unit-C helpers: `isGlobalFlow_Theta` from `tc2_exists_isGlobalFlow`
(bounded + Lipschitz), `contDiff_Theta` from `tc2_exists_bound` + `tc9_contDiff_uncurry_of_bounded`
(whose `section tc9_localization` is moved up in front of them; it depends on nothing in this file).
Statements of both theorems are unchanged.  Every edit is an exact-match text replacement that
asserts the old text occurs exactly once.

Outputs: TN_Assembled.lean (final), /tmp/tn_assembly/TN_Assembled_pass1.lean (before pass 2).
"""
import re, subprocess, sys, os, collections

D = "/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/drafts/fd"
SKEL = f"{D}/TN_Skeleton.lean"
UNITS = ["A", "B", "C", "D", "E", "F"]
OUT = f"{D}/TN_Assembled.lean"
TMP = "/tmp/tn_assembly"
os.makedirs(TMP, exist_ok=True)

skel = open(SKEL).read().split("\n")
hunk_re = re.compile(r"^(\d+)(?:,(\d+))?([acd])(\d+)(?:,(\d+))?$")


def parse_hunks(unit_path):
    p = subprocess.run(["diff", SKEL, unit_path], capture_output=True, text=True)
    lines = p.stdout.split("\n")
    unit = open(unit_path).read().split("\n")
    hunks = []
    i = 0
    while i < len(lines):
        m = hunk_re.match(lines[i])
        if not m:
            i += 1
            continue
        s1, s2, op, u1, u2 = m.groups()
        s1 = int(s1); s2 = int(s2) if s2 else s1
        u1 = int(u1); u2 = int(u2) if u2 else u1
        i += 1
        removed, added = [], []
        while i < len(lines) and lines[i].startswith("< "):
            removed.append(lines[i][2:]); i += 1
        if i < len(lines) and lines[i] == "---":
            i += 1
        while i < len(lines) and lines[i].startswith("> "):
            added.append(lines[i][2:]); i += 1
        if op != "d":
            assert added == unit[u1 - 1:u2], f"{unit_path}: hunk {m.group(0)} added-lines mismatch"
        hunks.append(dict(op=op, s1=s1, s2=s2, removed=removed, added=added, hdr=m.group(0)))
    return hunks


def is_sublist(small, big):
    n = len(small)
    return any(big[k:k + n] == small for k in range(len(big) - n + 1))


all_hunks = {}
violations = []
moves = []
for u in UNITS:
    path = f"{D}/TN_U_{u}.lean"
    hs = parse_hunks(path)
    for h in hs:
        if h["op"] == "c":
            if h["s2"] != h["s1"] or h["removed"] != ["  sorry"]:
                violations.append(f"unit {u} hunk {h['hdr']}: replaces something other than one `  sorry` line: {h['removed']!r}")
        elif h["op"] == "d":
            core = [r for r in h["removed"] if r not in ("  sorry", "")]
            homes = [g["hdr"] for g in hs if g["op"] == "a" and is_sublist(core, g["added"])]
            if not homes:
                violations.append(f"unit {u} hunk {h['hdr']}: deletes lines not re-inserted verbatim: {core!r}")
            else:
                moves.append((u, h["hdr"], homes[0], len(core)))
        # 'a' hunks: pure insertions, always fine for the freeze
    all_hunks[u] = hs
    print(f"unit {u}: {len(hs)} hunks: " + ", ".join(h['hdr'] for h in hs))
for mv in moves:
    print(f"  relocation recognised: unit {mv[0]} deletion {mv[1]} re-inserted verbatim inside {mv[2]} ({mv[3]} lines)")

# overlap check between units (skeleton coordinates)
touched = {}
for u, hs in all_hunks.items():
    for h in hs:
        for s in range(h["s1"], h["s2"] + 1):
            k = (h["op"], s)
            if k in touched and touched[k] != u:
                violations.append(f"overlap at skeleton line {s} ({h['op']}): units {touched[k]} and {u}")
            touched[k] = u
# a 'c'/'d' on a line that another unit also 'c'/'d's
for (op, s), u in list(touched.items()):
    for op2 in "cd":
        if op2 != op and (op2, s) in touched:
            violations.append(f"line {s}: {op} by {u} and {op2} by {touched[(op2, s)]}")

if violations:
    print("VIOLATIONS:"); [print("  " + v) for v in violations]
    sys.exit(1)
print("freeze check: every removed skeleton line is `  sorry` or relocated verbatim; no overlaps")

# helper names (top-level declarations added by units)
decl_re = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma|def|abbrev|structure|instance|noncomputable def)\s+([^\s:({\[]+)")
helpers = collections.OrderedDict()
for u, hs in all_hunks.items():
    for h in hs:
        for ln in h["added"]:
            m = decl_re.match(ln)
            if m:
                helpers.setdefault(m.group(2), []).append(u)
# the relocated D4 statement is re-declared inside an 'a' hunk of D: not a helper
leaf_names = set()
for ln in skel:
    m = decl_re.match(ln)
    if m:
        leaf_names.add(m.group(2))
helpers_only = {n: us for n, us in helpers.items() if n not in leaf_names}
dups = {n: us for n, us in helpers_only.items() if len(us) > 1}
print(f"helpers: {len(helpers_only)} distinct names; per unit: " +
      ", ".join(f"{u}={sum(1 for us in helpers_only.values() if u in us)}" for u in UNITS))
if dups:
    print("DUPLICATE helper names across units:", dups); sys.exit(2)
redecl = {n: us for n, us in helpers.items() if n in leaf_names}
print("skeleton names re-declared inside insertions (must be exactly the relocated D4):", redecl)
assert redecl == {"Hmap_pullback": ["D"]}, redecl

# apply
repl = {}; ins = {}; dele = set()
for u, hs in all_hunks.items():
    for h in hs:
        if h["op"] == "c":
            assert skel[h["s1"] - 1] == "  sorry"
            repl[h["s1"]] = (u, h["added"])
        elif h["op"] == "a":
            ins.setdefault(h["s1"], []).append((u, h["added"]))
        else:
            for s in range(h["s1"], h["s2"] + 1):
                assert skel[s - 1] in h["removed"]
                dele.add(s)
out = []
for i, ln in enumerate(skel, start=1):
    if i in dele:
        pass
    elif i in repl:
        out.extend(repl[i][1])
    else:
        out.append(ln)
    for (u, block) in ins.get(i, []):
        out.extend(block)
text1 = "\n".join(out)
open(f"{TMP}/TN_Assembled_pass1.lean", "w").write(text1)
print(f"pass 1: {len(out)} lines (skeleton {len(skel)}); remaining `sorry` lines: "
      f"{sum(1 for l in out if l.strip() == 'sorry')}")

# contiguity check: every added block appears verbatim, contiguously, exactly once
outs = "\n" + text1 + "\n"
for u, hs in all_hunks.items():
    for h in hs:
        if not h["added"]:
            continue
        blk = "\n" + "\n".join(h["added"]) + "\n"
        c = outs.count(blk)
        if c != 1:
            print(f"CONTIGUITY FAIL unit {u} hunk {h['hdr']}: occurrences={c}"); sys.exit(3)
print("contiguity: every hunk block occurs exactly once, contiguously")
# order check: pullback_chart (A7) declared before Hmap_pullback (D4)
i_a7 = next(i for i, l in enumerate(out) if l.startswith("theorem pullback_chart"))
i_d4 = next(i for i, l in enumerate(out) if l.startswith("theorem Hmap_pullback"))
assert i_a7 < i_d4, "A7 must precede D4"
print(f"order: pullback_chart at line {i_a7+1} < Hmap_pullback at line {i_d4+1}")


# ---------------- pass 2: repair of the false leaf C2 ----------------
def replace_once(text, old, new, what):
    c = text.count(old)
    assert c == 1, f"{what}: expected exactly one occurrence, found {c}"
    return text.replace(old, new)


text = text1
# (a) remove the false leaf C2 and say why
old_c2 = (
    "/-- LEAF C2.  `Y` has compact support (`|τ| ≤ 3`, `|θ| ≤ 21`, `‖w‖ ≤ ρ`). -/\n"
    "theorem hasCompactSupport_Yfield {ρ : ℝ} (hρ : GoodRadius T ρ) :\n"
    "    HasCompactSupport (Yfield T ρ) := by\n"
    "  sorry\n\n")
new_c2 = (
    "/-! The skeleton's LEAF C2 (`hasCompactSupport_Yfield : HasCompactSupport (Yfield T ρ)`) is FALSE as\n"
    "stated: the first component `χ_τ(τ)` of `Yfield` does not depend on `p` and equals `1` on the unbounded\n"
    "set `{0} × ℝ × ℝ²` (kernel-checked above, `tc2_not_hasCompactSupport_Yfield`).  Only the second\n"
    "component is compactly supported (`tc2_hasCompactSupport_Yfield_snd`).  The leaf is therefore dropped;\n"
    "`isGlobalFlow_Theta` and `contDiff_Theta` below are built on boundedness and global Lipschitz\n"
    "continuity instead (`tc2_exists_isGlobalFlow`, `tc2_exists_bound`, `tc9_contDiff_uncurry_of_bounded`),\n"
    "with their statements unchanged.  Cutting off the first component as well would make C3 (`τ = t` for\n"
    "every `p`) and C5 (`Φ₁` a global diffeomorphism) false, so this is the right repair. -/\n\n")
text = replace_once(text, old_c2, new_c2, "remove leaf C2")

# (b) isGlobalFlow_Theta from bounded + Lipschitz
old_b = (
    "  Classical.epsilon_spec (ContactMotions.exists_isGlobalFlow_of_hasCompactSupport'\n"
    "    (hasCompactSupport_Yfield hρ) ((contDiff_Yfield hT hρ).of_le (by simp)))\n")
new_b = "  Classical.epsilon_spec (tc2_exists_isGlobalFlow hT hρ)\n"
text = replace_once(text, old_b, new_b, "isGlobalFlow_Theta body")
old_bdoc = "/-- `Θ` is a global flow of `Y` (row 86's existence theorem). -/\n"
new_bdoc = ("/-- `Θ` is a global flow of `Y` (row 86's existence theorem for a bounded, globally Lipschitz\n"
            "field: `tc2_exists_isGlobalFlow`). -/\n")
text = replace_once(text, old_bdoc, new_bdoc, "isGlobalFlow_Theta docstring")

# (c) contDiff_Theta from boundedness
old_c = (
    "/-- `Θ` is jointly `C^∞` — **smooth dependence** (row 86, `ContactMotions.contDiff_uncurry`). -/\n"
    "theorem contDiff_Theta (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) :\n"
    "    ContDiff ℝ ∞ (uncurry (Theta T ρ)) :=\n"
    "  ContactMotions.contDiff_uncurry (contDiff_Yfield hT hρ) (hasCompactSupport_Yfield hρ)\n"
    "    (isGlobalFlow_Theta hT hρ)\n")
new_c = (
    "/-- `Θ` is jointly `C^∞` — **smooth dependence** (row 86's `ContactMotions.contDiff_uncurry`,\n"
    "localised to bounded fields by `tc9_contDiff_uncurry_of_bounded`; `Y` is bounded, `tc2_exists_bound`). -/\n"
    "theorem contDiff_Theta (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) :\n"
    "    ContDiff ℝ ∞ (uncurry (Theta T ρ)) := by\n"
    "  obtain ⟨L, hL⟩ := tc2_exists_bound hT hρ\n"
    "  exact tc9_contDiff_uncurry_of_bounded (contDiff_Yfield hT hρ) hL (isGlobalFlow_Theta hT hρ)\n")
text = replace_once(text, old_c, new_c, "contDiff_Theta body")

# (d) move `section tc9_localization … end tc9_localization` up, in front of isGlobalFlow_Theta
lines = text.split("\n")
i0 = lines.index("section tc9_localization")
i1 = lines.index("end tc9_localization")
assert lines[i0 - 1] == "" and lines[i1 + 1] == ""
block = lines[i0:i1 + 2]            # section … end, plus the blank line after it
del lines[i0:i1 + 2]
j = next(i for i, l in enumerate(lines) if l.startswith("/-- `Θ` is a global flow of `Y`"))
lines[j:j] = block
text = "\n".join(lines)
assert text.count("section tc9_localization") == 1
print(f"pass 2: C2 removed, isGlobalFlow_Theta/contDiff_Theta re-proved, tc9_localization ({len(block)} lines) moved to line {j+1}")

n_sorry = sum(1 for l in text.split("\n") if l.strip() == "sorry")
print("pass 2: remaining `sorry` lines:", n_sorry)

# (e) if sorry-free, rewrite the module docstring so the word does not occur; drop #print/#eval
if n_sorry == 0:
    old_hdr_start = text.index("/-! # SM fd:transverse-neighborhood")
    old_hdr_end = text.index("-/\n", old_hdr_start) + 3
    new_hdr = """/-! # SM fd:transverse-neighborhood — the transverse neighbourhood theorem (row 84), assembled

Assembled 2026-09-14 (work/drafts/fd/, `TN_assemble.py`) from `TN_Skeleton.lean` and the unit files
`TN_U_{A,B,C,D,E,F}.lean`.  Source: reference/SM/sm-3-statesum.tex:2395-2409 (statement), 2410-2559
(proof).  Route: `FD_84_87_FEASIBILITY_v2.md` §1; leaf plan: `TN_PLAN.md`; assembly record:
`TN_ASSEMBLY_REPORT.md`.

Layout.  §1–§6 (from `namespace SM` to `TransverseNeighborhoodData`) are **byte-identical** to
`TransverseNeighborhood.lean` lines 67-238 (the statement).  §7 is the proof: definitions, the Moser
rational identities of `MoserIdentityCheck.lean` transported to the concrete chart, the former leaf
lemmas (all proved) grouped in units A–F with their helpers (prefixes `ta_`, `tb_`, `tc*_`, `td_`,
`te_`, `tf_`), and the row theorem `SM.fd_transverse_neighborhood : TransverseNeighborhoodData`.
`#print axioms SM.fd_transverse_neighborhood` gives `[propext, Classical.choice, Quot.sound]`.

Units (dependencies): A chart `F` (none) · B forms and Moser field (none) · C the time-dependent
flow (B defs) · D the model neighbourhood `H` (A, B, C) · E Legendrian `L`, annulus, pushoff,
transverse isotopy (statement notions only) · F ambient isotopy `Ψ` (statement notions only).
Row theorem: D + E + F.

One deviation from the skeleton: its leaf C2 (`hasCompactSupport_Yfield`) was false as stated and
is replaced by the bounded/Lipschitz route (see the note in Unit C and `TN_U_C_REPORT.md` §2).

Check: `cd work/lean && lake env lean ../drafts/fd/TN_Assembled.lean`. -/
"""
    text = text[:old_hdr_start] + new_hdr + text[old_hdr_end:]
    kept = []
    dropped = 0
    for l in text.split("\n"):
        if re.match(r"^\s*#(print|eval|check)\b", l):
            dropped += 1; continue
        kept.append(l)
    text = "\n".join(kept)
    print(f"module docstring rewritten; dropped {dropped} #print/#eval/#check lines")

open(OUT, "w").write(text)
final_lines = text.split("\n")
print(f"wrote {OUT}: {len(final_lines)} lines")
print("word `sorry` occurrences (any form):", sum(l.lower().count("sorry") for l in final_lines))
for k, l in enumerate(final_lines, start=1):
    if "sorry" in l.lower():
        print(f"   line {k}: {l.strip()[:100]}")
