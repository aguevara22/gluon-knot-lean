#!/usr/bin/env python3
"""Assemble (A) work/drafts/frontrows/FrontRows_W3b_Delta.lean (certificate rows lane, last delta: the type-II move leaf,
rows 78 ng:front-II and 83 ng:local-front-bound, certificate_laws and word_bound) from W3_U6.lean + Skeleton_W2.lean, and
(B) work/drafts/frontrows/NgBound_Final.lean from NgBound_Statement.lean per NGBOUND_PLAN.md "Recipe B".  Rerunnable; every
source range is anchored (first/last line text asserted) so it fails loudly on a different input; byte-identity of every
copied range is asserted after assembly.  Also writes the axiom probe copies /tmp/w3b/W3b_ax.lean, /tmp/w3b/NgBound_ax.lean
and the olean source copy /tmp/w3b/src/SM/FrontRowsW3b.lean.  Writes nothing under work/lean."""
import os, sys, json
ROOT = "/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912"
FR = f"{ROOT}/work/drafts/frontrows"
SKEL = f"{FR}/Skeleton_W2.lean"
U6F = f"{FR}/W3_U6.lean"
DELTA3 = f"{FR}/FrontRows_W3_Delta.lean"
PORTED3 = f"{ROOT}/work/lean/SM/FrontRowsW3.lean"
NGS = f"{FR}/NgBound_Statement.lean"
OUT = f"{FR}/FrontRows_W3b_Delta.lean"
OUTB = f"{FR}/NgBound_Final.lean"
TMP = "/tmp/w3b"
os.makedirs(f"{TMP}/src/SM", exist_ok=True); os.makedirs(f"{TMP}/lib/SM", exist_ok=True)

S = open(SKEL, encoding="utf-8").read().split("\n")
U6 = open(U6F, encoding="utf-8").read().split("\n")
D3 = open(DELTA3, encoding="utf-8").read().split("\n")
P3 = open(PORTED3, encoding="utf-8").read().split("\n")
N = open(NGS, encoding="utf-8").read().split("\n")
assert len(S) == 14892 and S[-1] == "", len(S)      # 14,891 lines + trailing newline
assert len(U6) == 29217 and U6[-1] == "", len(U6)   # 29,216
assert len(D3) == 13267 and D3[-1] == "", len(D3)   # 13,266
assert len(P3) == 13268 and P3[-1] == "", len(P3)   # 13,267 = header line + delta
assert len(N) == 123 and N[-1] == "", len(N)        # 122

def s(i): return S[i - 1]
def u6(i): return U6[i - 1]
def n(i): return N[i - 1]
def rng(L, a, b): return L[a - 1:b]   # inclusive 1-based

def anchor(desc, cond):
    if not cond:
        sys.exit(f"ANCHOR FAILED: {desc}")

# ---- the ported module is the W3 delta plus one header line; the delta's U6 block is W3_U6's prefix of the block ----
anchor("ported FrontRowsW3 = one comment line + FrontRows_W3_Delta", P3[0].startswith("-- Ported 17:10Z 2026-09-14") and P3[1:] == D3)
anchor("W3_U6 11103-22207 == delta 2070-13174 (the ported part of the U6 block)", rng(U6, 11103, 22207) == rng(D3, 2070, 13174))
anchor("delta 13175-13178 is the old block footer end / blank / end U6 / blank", rng(D3, 13175, 13178) == ["end", "", "end U6", ""])
anchor("W3_U6 prefix 1-11102 == skeleton", U6[:11102] == S[:11102])
anchor("U6 block header 11110-11114", u6(11110) == "namespace U6" and u6(11111) == "" and u6(11112) == "open SM.FrontRealize SM.FrontWord.Letter Equiv U2 U4"
       and u6(11113) == "" and u6(11114) == "noncomputable section")
anchor("U6 22207-22209: end TypeIIbPassage / blank / H3 heading (the new part starts)", u6(22207) == "end TypeIIbPassage" and u6(22208) == ""
       and u6(22209) == "/-! #### H3. The type-II variant (b): the moved diagram (the cusp arc is lifted above the through-strand) -/")
anchor("U6 25412 J heading, 25416 typeII_move_proof", u6(25412) == "/-! #### J. The type-II leaf: the four variants -/"
       and u6(25416) == "theorem typeII_move_proof {W W' : OWord} (h : IsTypeII W.letters W'.letters) :")
anchor("U6 new block footer 25423-25427: blank / end / blank / end U6 / blank", rng(U6, 25423, 25427) == ["", "end", "", "end U6", ""])
anchor("typeII_move docstring 25428-25433 == skeleton 11103-11108", rng(U6, 25428, 25433) == rng(S, 11103, 11108) and u6(25428).startswith("/-- LEAF (ng:front-II, sm-3:1979-1984"))
anchor("typeII_move statement 25434-25435 == skeleton 11109-11110", rng(U6, 25434, 25435) == rng(S, 11109, 11110) and u6(25434).startswith("theorem typeII_move "))
anchor("typeII_move body 25436 = skeleton 11111 with := U6.typeII_move_proof h", u6(25436).rsplit(":=", 1)[0] == s(11111).rsplit(":=", 1)[0]
       and u6(25436).endswith(":= U6.typeII_move_proof h") and s(11111).endswith(":= sorry") and u6(25437) == "")
anchor("U6 25438 is typeI_move's docstring (ported already)", u6(25438).startswith("/-- LEAF (ng:front-I, sm-3:1955-1963"))
# ---- skeleton anchors ----
anchor("skeleton 42-45 preamble", s(42) == "namespace SM" and s(44) == "open SM.FrontWord SM.Link" and s(45) == "open scoped ContDiff")
anchor("P_typeII 14625-14630", s(14625) == "/-- ng:front-II: `Δd = 0` (`P_reidemeister_II` to the vertex-moved diagram, then its record). -/"
       and s(14626) == "theorem P_typeII {W W' : OWord} (h : IsTypeII W.letters W'.letters) :"
       and s(14629) == "  exact (P_reidemeister_II hR).symm.trans (presentations _ _ hrec)" and s(14630) == "")
anchor("end FrontRows 14735 / open FrontRows 14737", s(14735) == "end FrontRows" and s(14737) == "open FrontRows")
anchor("ng_front_II 14765-14773", s(14765) == "/-- **ng:front-II** (row 78), assembled. -/" and s(14766) == "theorem ng_front_II : NgFrontIIClauses where"
       and s(14772) == "    rw [(typeII_counts h).1, (typeII_counts h).2, P_typeII h]" and s(14773) == "")
anchor("row-83 block 14842-14877: namespace FrontRows .. end FrontRows / blank", s(14842) == "namespace FrontRows" and s(14843) == ""
       and s(14844) == "/-! ## Row 83: the word bound, then the smooth front -/" and s(14850) == "theorem certificate_laws :"
       and s(14873) == "theorem word_bound : ∀ W : OWord, 0 ≤ (realize W).defect :=" and s(14874) == "  ng_finite_word_bound _ _ certificate_laws"
       and s(14875) == "" and s(14876) == "end FrontRows" and s(14877) == "")
anchor("ng_local_front_bound 14878-14891", s(14878).startswith("/-- **ng:local-front-bound** (row 83), assembled") and s(14881) == "theorem ng_local_front_bound : NgLocalFrontBoundClauses where"
       and s(14889) == "    exact h0" and s(14890) == "" and s(14891) == "end SM")
# the copied unit ranges contain no forbidden token
for name, L, a, b in [("U6 new part", U6, 22209, 25437), ("skeleton P_typeII", S, 14625, 14630), ("skeleton ng_front_II", S, 14765, 14773), ("skeleton row 83", S, 14842, 14891)]:
    for i in range(a, b + 1):
        l = L[i - 1]
        anchor(f"{name} line {i} has no sorry", "sorry" not in l.lower())
        anchor(f"{name} line {i} has no #print/#eval/#check/set_option", not any(k in l for k in ("#print", "#eval", "#check", "set_option")))

HEADER = """/-! # Front certificate rows — last delta: the type-II move leaf, rows 78 and 83, `certificate_laws`, `word_bound`

Certificate rows lane, last delta (decision D-FR1: the lane is ported incrementally as fully proved modules): the
type-II move leaf, rows 78 ng:front-II and 83 ng:local-front-bound, `certificate_laws` and `word_bound`.  This module
imports `SM.FrontRowsW3` (which imports `SM.FrontRowsW2S` and `SM.FrontRowsW2`: rows 76 ng:commutation, 77 ng:front-I,
79 ng:front-III, 80 ng:deletions, 81 ng:circle, 82 ng:cusp-skein, the five row-statement structures, the infrastructure
blocks U1-U8 and the leaves `represent`, `typeIII_site`, `typeI_move`, `crossedCusp_move`) and adds, in this order:
* **the continuation of the U6 infrastructure block** (`SM.FrontRows.U6`, re-opened with the block's header `open`
  and `noncomputable section`): sections H3-H5 — the type-II variant (b) (`l_{m+1} σ_m σ_{m+1} ↦ l_m`): the moved
  diagram, its specification and the remaining specification fields, `U6.typeII_b`; sections I1-I5 — the type-II
  variant (d) (`σ_{m+1} σ_m r_{m+1} ↦ r_m`): the word level, the block passage, the moved diagram, the specification,
  `U6.typeII_d`; section J — the dispatch `U6.typeII_move_proof` over the four variants of `IsTypeII` (`typeII_a`,
  `typeII_c` are in `SM.FrontRowsW3`).  Verbatim from `W3_U6.lean` L22209-25423 (W3_U6_REPORT.md), whose prefix
  L11103-22207 is the block already ported in `SM.FrontRowsW3`.  The continuation declares two further global tactic
  macros, `bII_pair` and `dII_pair` (the nine of the ported block, `cc_mem` … `cII_pair`, are imported, not re-declared).
* **the leaf `SM.FrontRows.typeII_move`** (ng:front-II: the two standard realizations of a type-II pair are related by
  an oriented Reidemeister-II site through a vertex-moved diagram carrying the named record of `realize W'`): docstring
  and statement verbatim from `Skeleton_W2.lean` L11103-11111, body `U6.typeII_move_proof h` (`W3_U6.lean` L25428-25436).
* **the polynomial consumer** `SM.FrontRows.P_typeII` (`Δd = 0` through `P_reidemeister_II` and `presentations`),
  verbatim from `Skeleton_W2.lean` L14625-14629.
* **row 78**: `SM.ng_front_II : NgFrontIIClauses`, verbatim from `Skeleton_W2.lean` L14765-14772, assembled from the
  count leaf `typeII_counts` (`SM.FrontRowsW2`) and `P_typeII`.
* **`SM.FrontRows.certificate_laws`** (the seven laws of the descent `Moves.Laws` for the moves of `SM.ng_finite_word`
  with the geometric `s`, `B` of the realization and the syntactic base: rows 76(1), 77, 78, 79 for `pres_B`; rows 80,
  81(1) for `del_B`; row 82 for `skein_B`; `base_defect_nonneg` for `base_B`) and **`SM.FrontRows.word_bound`** (`B ≥ 0`
  on every closed oriented word's realization, consuming the accepted literature interface `SM.ng_finite_word` through
  `ng_finite_word_bound`), verbatim from `Skeleton_W2.lean` L14842-14876.
* **row 83**: `SM.ng_local_front_bound : NgLocalFrontBoundClauses` (the representation clause of ng:commutation carries
  `D`, `w` and the rounding's record to a word, `presentations` carries `P`, the word bound gives `B ≥ 0`), verbatim
  from `Skeleton_W2.lean` L14878-14889.

Every declaration in this module is fully proved: the axioms of `SM.FrontRows.typeII_move` and `U6.typeII_move_proof`
are `[propext, Classical.choice, Quot.sound]`; those of `SM.ng_front_II`, `SM.FrontRows.P_typeII` and
`SM.FrontRows.certificate_laws` are `[propext, Classical.choice, Quot.sound, SM.lp_lm]` (`lp_lm` is the accepted
literature interface reached through `P`); those of `SM.FrontRows.word_bound` and `SM.ng_local_front_bound` are
`[propext, Classical.choice, Quot.sound, SM.lp_lm, SM.ng_finite_word]`.  Nothing declared in the three ported modules
is re-declared here.  Provenance and line map: `work/drafts/frontrows/W3B_DELTA_REPORT.md`.

Checked with `cd work/lean && lake env lean`. -/"""

out = []
out += ["import SM.FrontRowsW3", ""]
out += HEADER.split("\n")
out += ["", "namespace SM", "", "open SM.FrontWord SM.Link", "open scoped ContDiff", ""]
out += ["namespace FrontRows", "", "section Leaves", ""]
out += ["/-! ### U6 infrastructure, continued — the type-II variants (b) and (d) and the dispatch (verbatim from `W3_U6.lean`",
        "L22209-25423; the block's header L11110-11114 is re-opened, its first part L11103-22207 is in `SM.FrontRowsW3`) -/", ""]
u6h_a = len(out) + 1
out += rng(U6, 11110, 11114)    # namespace U6 / blank / open ... / blank / noncomputable section
u6h_b = len(out)
out += [""]
u6_a = len(out) + 1
out += rng(U6, 22209, 25423)    # the new part of the U6 block (H3-H5, I1-I5, J), ends with a blank line
u6_b = len(out)
u6f_a = len(out) + 1
out += rng(U6, 25424, 25427)    # end / blank / end U6 / blank
u6f_b = len(out)
leaf_a = len(out) + 1
out += rng(U6, 25428, 25437)    # typeII_move: docstring, theorem, proved body, blank
leaf_b = len(out)
out += ["end Leaves", ""]
out += ["/-! ## Glue: the polynomial consumer (verbatim from `Skeleton_W2.lean` L14625-14630) -/", ""]
pII_a = len(out) + 1
out += rng(S, 14625, 14630)     # P_typeII + blank
pII_b = len(out)
out += ["end FrontRows", "", "open FrontRows", ""]
out += ["/-! ## Assembly of row 78 (verbatim from `Skeleton_W2.lean` L14765-14773) -/", ""]
rII_a = len(out) + 1
out += rng(S, 14765, 14773)     # ng_front_II + blank
rII_b = len(out)
out += ["/-! ## Row 83: `certificate_laws`, `word_bound` and `ng_local_front_bound` (verbatim from `Skeleton_W2.lean` L14842-14891) -/", ""]
r83_a = len(out) + 1
out += rng(S, 14842, 14891)     # namespace FrontRows .. end FrontRows, blank, row 83 docstring + theorem, blank, end SM
r83_b = len(out)
text = "\n".join(out) + "\n"
open(OUT, "w", encoding="utf-8").write(text)
open(f"{TMP}/src/SM/FrontRowsW3b.lean", "w", encoding="utf-8").write(text)
lines = text.split("\n")
nA = text.count("\n")
print(f"wrote {OUT}: {nA} lines (copy for the olean build: {TMP}/src/SM/FrontRowsW3b.lean)")

# ---- verification: byte identity of every copied range ----
def eq(desc, a, b, src, sa, sb):
    got = lines[a - 1:b]; want = rng(src, sa, sb)
    assert got == want, f"NOT byte-identical: {desc} (module {a}-{b} vs source {sa}-{sb})"
eq("U6 block header", u6h_a, u6h_b, U6, 11110, 11114)
eq("U6 new part", u6_a, u6_b, U6, 22209, 25423)
eq("U6 block footer", u6f_a, u6f_b, U6, 25424, 25427)
eq("typeII_move", leaf_a, leaf_b, U6, 25428, 25437)
eq("P_typeII", pII_a, pII_b, S, 14625, 14630)
eq("ng_front_II", rII_a, rII_b, S, 14765, 14773)
eq("row 83 block", r83_a, r83_b, S, 14842, 14891)
# the leaf's docstring + statement == skeleton (body differs only after the last :=)
assert lines[leaf_a - 1:leaf_a + 7] == rng(S, 11103, 11110) and lines[leaf_a + 7].rsplit(":=", 1)[0] == s(11111).rsplit(":=", 1)[0]
bad = [(i, l) for i, l in enumerate(lines, 1) if "sorry" in l.lower()]
bad2 = [(i, l) for i, l in enumerate(lines, 1) if any(k in l for k in ("#print", "#eval", "#check", "set_option"))]
assert not bad, bad[:5]
assert not bad2, bad2[:5]
assert lines[-2] == "end SM" and lines[-1] == ""
print("  (A) byte-identity checks OK; sorry (case-insensitive) = 0; #print/#eval/#check/set_option = 0")

def find(prefix, a, b):
    for i in range(a, b + 1):
        if lines[i - 1].startswith(prefix): return i
    raise KeyError(prefix)
MA = {
 "typeII_move_proof": find("theorem typeII_move_proof", u6_a, u6_b),
 "typeII_b": find("theorem typeII_b", u6_a, u6_b),
 "typeII_d": find("theorem typeII_d", u6_a, u6_b),
 "typeII_move": find("theorem typeII_move ", leaf_a, leaf_b),
 "P_typeII": find("theorem P_typeII", pII_a, pII_b),
 "ng_front_II": find("theorem ng_front_II", rII_a, rII_b),
 "certificate_laws": find("theorem certificate_laws", r83_a, r83_b),
 "word_bound": find("theorem word_bound", r83_a, r83_b),
 "ng_local_front_bound": find("theorem ng_local_front_bound", r83_a, r83_b),
 "macro bII_pair": find('macro "bII_pair"', u6_a, u6_b),
 "macro dII_pair": find('macro "dII_pair"', u6_a, u6_b),
}
hdr_n = len(HEADER.split("\n"))
print(f"  header L3-{2 + hdr_n}; namespace SM L{4 + hdr_n}; namespace FrontRows L{9 + hdr_n}, section Leaves L{11 + hdr_n}")
print(f"  U6 block header L{u6h_a}-{u6h_b} (W3_U6 11110-11114); new part L{u6_a}-{u6_b} (W3_U6 22209-25423, offset {u6_a - 22209:+d}); footer L{u6f_a}-{u6f_b} (W3_U6 25424-25427)")
print(f"  typeII_move docstring L{leaf_a}, theorem L{MA['typeII_move']}-{leaf_b - 1} (W3_U6 25428-25437 / skeleton 11103-11111); end Leaves L{leaf_b + 1}")
print(f"  P_typeII L{MA['P_typeII']} (doc {pII_a}; skeleton 14625-14630); end FrontRows L{pII_b + 1}, open FrontRows L{pII_b + 3}")
print(f"  ng_front_II L{MA['ng_front_II']} (doc {rII_a}; skeleton 14765-14773)")
print(f"  row-83 block L{r83_a}-{r83_b} (skeleton 14842-14891): certificate_laws L{MA['certificate_laws']}, word_bound L{MA['word_bound']}, ng_local_front_bound L{MA['ng_local_front_bound']}; end SM L{nA}")
print("  new-part landmarks: " + ", ".join(f"{k} L{v}" for k, v in MA.items() if k in ("typeII_b", "typeII_d", "typeII_move_proof", "macro bII_pair", "macro dII_pair")))

probe = text + "\n".join([
    "#print axioms SM.ng_front_II",
    "#print axioms SM.ng_local_front_bound",
    "#print axioms SM.FrontRows.typeII_move",
    "#print axioms SM.FrontRows.certificate_laws",
    "#print axioms SM.FrontRows.word_bound",
    "#print axioms SM.FrontRows.P_typeII",
    "#print axioms SM.FrontRows.U6.typeII_move_proof",
    "#print axioms SM.FrontRows.U6.typeII_b",
    "#print axioms SM.FrontRows.U6.typeII_d",
]) + "\n"
open(f"{TMP}/W3b_ax.lean", "w", encoding="utf-8").write(probe)
print(f"  probe: {TMP}/W3b_ax.lean")

# ======================= (B) NgBound_Final.lean per NGBOUND_PLAN.md Recipe B =======================
anchor("NgBound_Statement 1 import", n(1) == "import SM.FrontRowsW2")
anchor("NgBound_Statement 32-35 preamble", n(32) == "namespace SM" and n(33) == "" and n(34) == "open SM.FrontWord SM.Link" and n(35) == "open scoped ContDiff" and n(36) == "")
anchor("NgBound_Statement 37-42 the re-declared structure (dropped)", n(37).startswith("/-! ## Row 83's statement") and n(39) == "structure NgLocalFrontBoundClauses : Prop where"
       and n(41) == "    F.writhe - (F.downCount : ℤ) ≤ -degAZ (P S) - 1" and n(42) == "")
anchor("NgBound_Statement 43 degAZ section heading", n(43).startswith('/-! ## "max deg_a P_{S(F)}" is `degAZ (P S)`'))
anchor("NgBound_Statement 49 degAZ_P_isMaxDegA / 55 dOf_eq_degAZ / 57 row 93 heading", n(49).startswith("theorem degAZ_P_isMaxDegA") and n(55).startswith("theorem SmoothFront.dOf_eq_degAZ")
       and n(57) == "/-! ## Row 93: fd:ng-bound (sm-3:3379-3390), one field per assertion of display fd:ng-input -/")
anchor("NgBound_Statement 68 NgBoundClauses / 80 fd_ng_bound_of / 89, 95 cross-checks / 98-99", n(68) == "structure NgBoundClauses : Prop where"
       and n(80) == "theorem fd_ng_bound_of (h83 : NgLocalFrontBoundClauses) : NgBoundClauses where"
       and n(89).startswith("theorem NgBoundClauses.defect_nonneg") and n(95) == "theorem NgBoundClauses.of_defect_nonneg"
       and n(98) == "  ng_input := fun F S hS => (F.defect_nonneg_iff_slNg S).1 (h F S hS)" and n(99) == "")
anchor("NgBound_Statement 100-107 sanity examples", n(100).startswith("/-! ## Sanity checks") and n(102).startswith("example (h83") and n(104).startswith("example (h83")
       and n(106) == "  (fd_ng_bound_of h83).ng_input F S hS" and n(107) == "")
anchor("NgBound_Statement 108-111 #check/#print (dropped)", n(108).startswith("#check") and n(111).startswith("#print axioms") and n(112) == "")
anchor("NgBound_Statement 113-122 DraftOnly (dropped)", n(113).startswith("/-! ## Draft-only") and n(116) == "section DraftOnly" and n(120) == "end DraftOnly" and n(122) == "end SM")
for i in range(43, 108):
    anchor(f"NgBound_Statement line {i} has no sorry / #-command", "sorry" not in n(i).lower() and not any(k in n(i) for k in ("#print", "#eval", "#check", "set_option")))

HEADER_B = """/-! # fd:ng-bound (row 93) — the individual-front bound in Ng's self-linking form

Front certificate rows lane, row 93 sub-lane (plan `work/drafts/frontrows/NGBOUND_PLAN.md`, Recipe B; draft
`NgBound_Statement.lean`, whose declarations are kept verbatim).  Lemma fd:ng-bound (sm-3:3379-3390) is Theorem
ng:local-front-bound (row 83, sm-3:2305-2313) "restated in Ng's self-linking form".  Its only mathematical input is row 83
(DEPENDENCIES.json: lp:core, ng:front-domain, ng:local-front-bound, ng:smoothing-record).  This module imports
`SM.FrontRowsW3b` (the last delta of the lane, which proves row 83 `SM.ng_local_front_bound : NgLocalFrontBoundClauses`;
the statement `SM.NgLocalFrontBoundClauses` is declared in `SM.FrontRowsW3`, so it is NOT re-declared here) and contains

* the accepted `SM.SmoothFront.slNg F : ℤ := F.writhe - F.downCount` (FrontSmooth.lean:731-732, docstring "the quantity
  bounded in ng:local-front-bound / fd:ng-bound (`sl_Ng`)"), REUSED, not re-declared; `slNg_def` is `rfl`.
* `SM.degAZ_P_isMaxDegA` — the printed proof's first sentence: "Theorem lp:core gives P_{S(F)} ≠ 0, ... so
  deg_a P_{S(F)} ... is the largest a exponent with nonzero coefficient, max deg_a P_{S(F)}".  Proved from the
  accepted `P_ne_zero` (lp:core) and `degAZ_spec`; it certifies that `degAZ (P S)` is the printed `max deg_a`
  (the `0`-at-`0` convention of `degAZ` is never exercised on a diagram polynomial).  `SM.SmoothFront.dOf_eq_degAZ`
  identifies `d(F)` of display ng:defect with it (`rfl`).
* `SM.NgBoundClauses` — the row bundle, one field per assertion of the printed display fd:ng-input.
* `SM.fd_ng_bound_of (h83 : NgLocalFrontBoundClauses) : NgBoundClauses` — the row theorem conditional on row 83; pure
  algebra (`slNg` unfolds to `w − D`; the inequality is row 83's clause verbatim); the cross-checks
  `NgBoundClauses.defect_nonneg` / `of_defect_nonneg` with the accepted defect (`defect_nonneg_iff_slNg`).
* **`SM.fd_ng_bound : NgBoundClauses := fd_ng_bound_of ng_local_front_bound`** — row 93, unconditional.

Axioms of `SM.fd_ng_bound`: `[propext, Classical.choice, Quot.sound, SM.lp_lm, SM.ng_finite_word]` — exactly those of
row 83 (`lp_lm` reached through `P`, `ng_finite_word` the accepted literature interface consumed by `word_bound`);
`fd_ng_bound_of`, `degAZ_P_isMaxDegA` and the bundle `NgBoundClauses` depend on `[propext, Classical.choice,
Quot.sound, SM.lp_lm]` (`lp_lm` enters through the accepted `P` in the statements; no other axiom).  Fidelity readings
FR-NB-1..FR-NB-7 in NGBOUND_PLAN.md; they cite FR-1 (polygonal reading of `S(F)`), FR-8/FR-10 (row 83 on the smooth
class via `represent`), FR-16 (`d = degAZ (P S)`).  Checked with `cd work/lean && lake env lean`. -/"""

outB = ["import SM.FrontRowsW3b", ""]
outB += HEADER_B.split("\n")
outB += [""]
outB += rng(N, 32, 36)          # namespace SM / blank / open .. / open scoped / blank
kept_a = len(outB) + 1
outB += rng(N, 43, 107)         # degAZ section .. NgBoundClauses .. fd_ng_bound_of .. cross-checks .. sanity examples + blank
kept_b = len(outB)
outB += ["/-! ## Row 93, unconditional: row 83 is proved in `SM.FrontRowsW3b` -/", ""]
outB += ["/-- **fd:ng-bound** (row 93, sm-3:3379-3390), unconditional: `fd_ng_bound_of` applied to row 83 `ng_local_front_bound`. -/"]
fd_a = len(outB) + 1
outB += ["theorem fd_ng_bound : NgBoundClauses := fd_ng_bound_of ng_local_front_bound", ""]
outB += ["end SM"]
textB = "\n".join(outB) + "\n"
open(OUTB, "w", encoding="utf-8").write(textB)
linesB = textB.split("\n")
nB = textB.count("\n")
print(f"wrote {OUTB}: {nB} lines")
assert linesB[kept_a - 1:kept_b] == rng(N, 43, 107), "NOT byte-identical: NgBound kept range"
assert linesB[kept_a - 1 - 5:kept_a - 1] == rng(N, 32, 36)
badB = [(i, l) for i, l in enumerate(linesB, 1) if "sorry" in l.lower() or any(k in l for k in ("#print", "#eval", "#check", "set_option"))]
assert not badB, badB
assert not any(l.startswith("structure NgLocalFrontBoundClauses") for l in linesB)
def findB(prefix):
    for i, l in enumerate(linesB, 1):
        if l.startswith(prefix): return i
    raise KeyError(prefix)
MB = {"degAZ_P_isMaxDegA": findB("theorem degAZ_P_isMaxDegA"), "dOf_eq_degAZ": findB("theorem SmoothFront.dOf_eq_degAZ"),
      "NgBoundClauses": findB("structure NgBoundClauses"), "fd_ng_bound_of": findB("theorem fd_ng_bound_of"),
      "defect_nonneg": findB("theorem NgBoundClauses.defect_nonneg"), "of_defect_nonneg": findB("theorem NgBoundClauses.of_defect_nonneg"),
      "fd_ng_bound": findB("theorem fd_ng_bound :")}
print(f"  (B) byte-identity OK (NgBound_Statement 32-36, 43-107); sorry = 0; #-commands = 0; NgLocalFrontBoundClauses not re-declared")
print("  (B) map: " + ", ".join(f"{k} L{v}" for k, v in MB.items()) + f"; kept range L{kept_a}-{kept_b}; end SM L{nB}")
probeB = textB + "\n".join(["#print axioms SM.fd_ng_bound", "#print axioms SM.fd_ng_bound_of", "#print axioms SM.degAZ_P_isMaxDegA", "#print axioms SM.NgBoundClauses"]) + "\n"
open(f"{TMP}/NgBound_ax.lean", "w", encoding="utf-8").write(probeB)
# concatenation fallback: (A) + (B) body in one file (B's import and header dropped, its `namespace SM` merged)
concat = text + "\n-- ==== NgBound_Final.lean body (concatenation check) ====\n" + "\n".join(linesB[len(HEADER_B.split(chr(10))) + 3:]) + "\n" + \
    "\n".join(["#print axioms SM.fd_ng_bound", "#print axioms SM.fd_ng_bound_of"]) + "\n"
open(f"{TMP}/Concat_ax.lean", "w", encoding="utf-8").write(concat)
json.dump({"A": {"lines": nA, "map": MA, "ranges": {"u6h": [u6h_a, u6h_b], "u6": [u6_a, u6_b], "u6f": [u6f_a, u6f_b], "leaf": [leaf_a, leaf_b],
                 "pII": [pII_a, pII_b], "rII": [rII_a, rII_b], "r83": [r83_a, r83_b]}},
           "B": {"lines": nB, "map": MB, "kept": [kept_a, kept_b]}}, open(f"{TMP}/linemap.json", "w"), indent=1)
print(f"  probes: {TMP}/NgBound_ax.lean, {TMP}/Concat_ax.lean; line map {TMP}/linemap.json")
