#!/usr/bin/env python3
"""Assemble work/drafts/frontrows/FrontRows_W3_Delta.lean (certificate rows lane, wave-3 delta: the front-move leaves
typeIII_site, typeI_move, crossedCusp_move and rows 77 ng:front-I, 79 ng:front-III, 80 ng:deletions; the five
row-statement structures) from W3_U5.lean + W3_U6.lean + Skeleton_W2.lean.  Rerunnable; every source range is anchored
(first/last line text asserted) so it fails loudly on a different input; byte-identity of every copied range is
asserted after assembly.  Also writes the axiom probe copy /tmp/w3delta/W3_ax.lean.  Writes nothing under work/lean."""
import os, sys
ROOT = "/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912"
FR = f"{ROOT}/work/drafts/frontrows"
SKEL = f"{FR}/Skeleton_W2.lean"
U5F = f"{FR}/W3_U5.lean"
U6F = f"{FR}/W3_U6.lean"
OUT = f"{FR}/FrontRows_W3_Delta.lean"
TMP = "/tmp/w3delta"
PROBE = f"{TMP}/W3_ax.lean"
os.makedirs(TMP, exist_ok=True)

S = open(SKEL, encoding="utf-8").read().split("\n")
U5 = open(U5F, encoding="utf-8").read().split("\n")
U6 = open(U6F, encoding="utf-8").read().split("\n")
assert len(S) == 14892 and S[-1] == "", len(S)      # 14,891 lines + trailing newline
assert len(U5) == 16856 and U5[-1] == "", len(U5)   # 16,855
assert len(U6) == 26001 and U6[-1] == "", len(U6)   # 26,000

def s(i): return S[i - 1]
def u5(i): return U5[i - 1]
def u6(i): return U6[i - 1]
def rng(L, a, b): return L[a - 1:b]   # inclusive 1-based

def anchor(desc, cond):
    if not cond:
        sys.exit(f"ANCHOR FAILED: {desc}")

# ---- the two unit files are the skeleton plus exactly the reported hunks ----
# W3_U5: 11092a11093,13042 ; 11101c13051,13065
anchor("U5 prefix == skeleton 1-11092", U5[:11092] == S[:11092])
anchor("U5 13043-13050 == skeleton 11093-11100 (typeIII_site docstring + statement line 1)", rng(U5, 13043, 13050) == rng(S, 11093, 11100))
anchor("U5 13066.. == skeleton 11102..", U5[13065:] == S[11101:])
anchor("skeleton 11101 is the typeIII_site sorry line", s(11101) == "    ∃ U : Set Plane, Nonempty (RIIIData U (realize W).diagram (realize W').diagram) := sorry")
anchor("U5 13051 is the same statement line with := by", u5(13051) == "    ∃ U : Set Plane, Nonempty (RIIIData U (realize W).diagram (realize W').diagram) := by")
anchor("U5 block header 11093", u5(11093) == "/-! ### U5 infrastructure -/" and u5(11094) == "" and u5(11095) == "namespace U5")
anchor("U5 block footer 13039-13042", u5(13039) == "end" and u5(13040) == "" and u5(13041) == "end U5" and u5(13042) == "")
anchor("typeIII_site docstring 13043", u5(13043).startswith("/-- LEAF (ng:front-III, sm-3:1995-2003"))
anchor("theorem typeIII_site 13050", u5(13050) == "theorem typeIII_site {W W' : OWord} (h : IsTypeIII W.letters W'.letters) :")
anchor("typeIII_site body last line 13065 / blank 13066", u5(13065) == "    convert this using 3 <;> simp only [hW, hW']" and u5(13066) == "")
# W3_U6: 11102a11103,22211 ; 11119c22228 ; 11128c22237
anchor("U6 prefix == skeleton 1-11102", U6[:11102] == S[:11102])
anchor("U6 22212-22227 == skeleton 11103-11118", rng(U6, 22212, 22227) == rng(S, 11103, 11118))
anchor("U6 22229-22236 == skeleton 11120-11127", rng(U6, 22229, 22236) == rng(S, 11120, 11127))
anchor("U6 22238.. == skeleton 11129..", U6[22237:] == S[11128:])
anchor("skeleton 11119 / 11128 are the sorry lines", s(11119).endswith(":= sorry") and s(11128).endswith(":= sorry"))
anchor("U6 22228 typeI_move body", u6(22228) == "      Nonempty (RecordIso D.record (realize W').diagram.record) := U6.typeI_move_proof h")
anchor("U6 22237 crossedCusp_move body", u6(22237) == "      Nonempty (RecordIso D.record (realize W').diagram.record) := U6.crossedCusp_move_proof h")
anchor("U6 block header 11103", u6(11103) == "/-! ### U6 infrastructure -/" and u6(11110) == "namespace U6"
       and u6(11112) == "open SM.FrontRealize SM.FrontWord.Letter Equiv U2 U4" and u6(11114) == "noncomputable section")
anchor("U6 block footer 22208-22211", u6(22208) == "end" and u6(22209) == "" and u6(22210) == "end U6" and u6(22211) == "")
anchor("typeII_move 22212-22221 (omitted)", u6(22212).startswith("/-- LEAF (ng:front-II, sm-3:1979-1984") and u6(22218).startswith("theorem typeII_move")
       and u6(22220).endswith(":= sorry") and u6(22221) == "")
anchor("typeI_move 22222-22229", u6(22222).startswith("/-- LEAF (ng:front-I, sm-3:1955-1963") and u6(22226).startswith("theorem typeI_move") and u6(22229) == "")
anchor("crossedCusp_move 22230-22238", u6(22230).startswith("/-- LEAF (ng:deletions, sm-3:2027-2033") and u6(22235).startswith("theorem crossedCusp_move") and u6(22238) == "")
anchor("skeleton 11130 is the L-PL heading", s(11130).startswith("/-! ### L-PL (unit U7)"))
# ---- skeleton anchors ----
anchor("skeleton 42-45 preamble", s(42) == "namespace SM" and s(44) == "open SM.FrontWord SM.Link" and s(45) == "open scoped ContDiff")
anchor("NgFrontIClauses 74", s(74) == "structure NgFrontIClauses : Prop where" and s(73) == "" and s(76) == "")
anchor("NgFrontIIClauses 77", s(77) == "structure NgFrontIIClauses : Prop where" and s(84) == "")
anchor("NgFrontIIIClauses 85", s(85) == "structure NgFrontIIIClauses : Prop where" and s(92) == "")
anchor("NgDeletionsClauses 93", s(93) == "structure NgDeletionsClauses : Prop where" and s(102) == "" and s(103).startswith("structure NgCircleClauses"))
anchor("NgLocalFrontBoundClauses 119", s(119) == "structure NgLocalFrontBoundClauses : Prop where" and s(118) == "" and s(122) == "" and s(123).startswith("/-! ### Nonemptiness helpers"))
anchor("namespace FrontRows 146 / section Leaves 150", s(146) == "namespace FrontRows" and s(150) == "section Leaves")
anchor("end U4 11083 / L-geo docstring 11085-11092", s(11083) == "end U4" and s(11085).startswith("/-! ### L-geo (units U5, U6 on the geometry core U4)") and s(11091).endswith("-/") and s(11092) == "")
anchor("end Leaves 14575", s(14575) == "end Leaves")
anchor("P_typeIII 14619-14624", s(14619) == "/-- ng:front-III: `Δd = 0` (`P_reidemeister_III` on the site). -/" and s(14620).startswith("theorem P_typeIII")
       and s(14623) == "  exact P_reidemeister_III ⟨U, Or.inl hU⟩" and s(14624) == "")
anchor("P_typeII 14625-14630 (omitted)", s(14626).startswith("theorem P_typeII") and s(14630) == "")
anchor("P_typeI 14631-14636", s(14631) == "/-- ng:front-I: `Δd = 0` (`P_reidemeister_I`, then the record). -/" and s(14632).startswith("theorem P_typeI")
       and s(14635) == "  exact (P_reidemeister_I hR).symm.trans (presentations _ _ hrec)" and s(14636) == "")
anchor("P_crossedCusp 14637-14642", s(14637) == "/-- ng:deletions, crossed cusp: `Δd = 0`. -/" and s(14638).startswith("theorem P_crossedCusp")
       and s(14641) == "  exact (P_reidemeister_I hR).symm.trans (presentations _ _ hrec)" and s(14642) == "" and s(14643) == "")
anchor("end FrontRows 14735 / open FrontRows 14737", s(14735) == "end FrontRows" and s(14737) == "open FrontRows")
anchor("ng_front_I 14757-14764", s(14757).startswith("/-- **ng:front-I** (row 77), assembled") and s(14758) == "theorem ng_front_I : NgFrontIClauses where"
       and s(14763) == "    push_cast; ring" and s(14764) == "")
anchor("ng_front_II 14765-14773 (omitted)", s(14766) == "theorem ng_front_II : NgFrontIIClauses where" and s(14773) == "")
anchor("ng_front_III 14774-14782", s(14774) == "/-- **ng:front-III** (row 79), assembled. -/" and s(14775) == "theorem ng_front_III : NgFrontIIIClauses where"
       and s(14781) == "    rw [(typeIII_counts h).1, (typeIII_counts h).2, P_typeIII h]" and s(14782) == "")
anchor("ng_deletions 14783-14804", s(14783).startswith("/-- **ng:deletions** (row 80), assembled") and s(14785) == "theorem ng_deletions : NgDeletionsClauses where"
       and s(14803) == "    rcases hD with hD | hD <;> omega" and s(14804) == "" and s(14805).startswith("/-- **ng:circle** (row 81)"))
anchor("end SM 14891", s(14891) == "end SM")
# the copied unit ranges contain no forbidden token
for name, L, a, b in [("U5 block+leaf", U5, 11093, 13066), ("U6 block", U6, 11103, 22211), ("U6 leaves", U6, 22222, 22238)]:
    for i in range(a, b + 1):
        l = L[i - 1]
        anchor(f"{name} line {i} has no sorry", "sorry" not in l.lower())
        anchor(f"{name} line {i} has no #print/#eval/#check/set_option", not any(k in l for k in ("#print", "#eval", "#check", "set_option")))

HEADER = """/-! # Front certificate rows — wave-3 delta: the front-move leaves and rows 77, 79, 80

Certificate rows lane, wave-3 delta (decision D-FR1: the lane is ported incrementally as fully proved modules).
This module imports `SM.FrontRowsW2S` (which imports `SM.FrontRowsW2`: rows 81 ng:circle and 82 ng:cusp-skein with
the shared infrastructure U1-U4, U7, U8D, U8R; then the U8R sweep block, the leaf `represent` and row 76
ng:commutation) and adds, in this order:
* **the five row-statement structures** `SM.NgFrontIClauses`, `SM.NgFrontIIClauses`, `SM.NgFrontIIIClauses`,
  `SM.NgDeletionsClauses`, `SM.NgLocalFrontBoundClauses`, verbatim from `Skeleton_W2.lean` L74-102 and L119-122
  (= `Statements_FINAL.lean`).  All five are declared here, so that the last delta (rows 78 and 83) declares none.
* **the U5 infrastructure block** (`SM.FrontRows.U5`: the band disc, the block hypothesis `Blk`, the chains, the
  crossings, the arc cover, the visits, the two-word comparison `Pair`, the general site `Pair.site_of` and the two
  patterns `site₁₂`/`site₂₁`) and **the leaf `SM.FrontRows.typeIII_site`** (ng:front-III: the two standard
  realizations of a type-III pair form an `RIIIData` site in the band disc), verbatim from `W3_U5.lean`
  (W3_U5_REPORT.md).
* **the U6 infrastructure block** (`SM.FrontRows.U6`: the generic slot-level assembly of `RIData`/`RIIData` on a
  vertex-moved slot diagram, the crossed-cusp and type-I geometries with their proofs `crossedCusp_move_proof`,
  `typeI_move_proof`, and the type-II helpers for the variants (a), (c) and the word level of (b)) and **the leaves
  `SM.FrontRows.typeI_move`** (ng:front-I: a kink removed by `RI` through a vertex-moved diagram carrying the named
  record of `realize W'`) and **`SM.FrontRows.crossedCusp_move`** (ng:deletions, crossed cusp: the same through the
  arms' exchange), verbatim from `W3_U6.lean` (W3_U6_REPORT.md).  The block also declares nine global tactic macros
  (`cc_mem`, `ccr_mem`, `tI_mem`, `tI_pair`, `tU_pair`, `tIIL_mem`, `tIIR_mem`, `aII_pair`, `cII_pair`), which importers see.
* **the polynomial consumers** `SM.FrontRows.P_typeIII`, `P_typeI`, `P_crossedCusp` (`Δd = 0` through
  `P_reidemeister_III/I` and `presentations`), verbatim from `Skeleton_W2.lean` L14619-14623, L14631-14641.
* **rows 77, 79, 80**: `SM.ng_front_I : NgFrontIClauses`, `SM.ng_front_III : NgFrontIIIClauses`,
  `SM.ng_deletions : NgDeletionsClauses`, verbatim from `Skeleton_W2.lean` L14757-14764, L14774-14804, assembled
  from the count leaves `typeI_counts`, `typeIII_counts`, `zigzag_counts`, `crossedCusp_counts`, the polynomial
  leaf `P_zigzag` and the nonemptiness helpers (all in `SM.FrontRowsW2`) and the three consumers above.

Every declaration in this module is fully proved: the axioms of `SM.ng_front_I`, `SM.ng_front_III`,
`SM.ng_deletions` are `[propext, Classical.choice, Quot.sound, SM.lp_lm]` (`lp_lm` is the accepted literature
interface reached through `P`); those of `SM.FrontRows.typeIII_site`, `typeI_move`, `crossedCusp_move` are
`[propext, Classical.choice, Quot.sound]`.  Provenance and line map: `work/drafts/frontrows/W3_DELTA_REPORT.md`.

NOT in this module — the last delta (`import SM.FrontRowsW3`) adds exactly these and declares nothing else: the
leaf `SM.FrontRows.typeII_move` (`Skeleton_W2.lean` L11103-11112; its variants (b) and (d) are being proved in a
follow-up unit, whose helpers `U6.typeII_b`, `U6.typeII_d`, `U6.typeII_move_proof` go there too), its consumer
`P_typeII` (L14625-14629), row 78 `ng_front_II` (L14765-14772), `certificate_laws` and `word_bound`
(L14842-14877), and row 83 `ng_local_front_bound` (L14878-14889).

Checked with `cd work/lean && lake env lean`. -/"""

NOTE_II = ["/-! The leaf `typeII_move` (`Skeleton_W2.lean` L11103-11112; ng:front-II, row 78) is not in this module: its",
           "variants (b) and (d) are being proved in a follow-up unit; it goes into the last delta with `P_typeII`. -/",
           ""]

out = []
out += ["import SM.FrontRowsW2S", ""]
out += HEADER.split("\n")
out += ["", "namespace SM", "", "open SM.FrontWord SM.Link", "open scoped ContDiff", ""]
out += ["/-! ## Statements of rows 77, 78, 79, 80 and 83 (verbatim from `Skeleton_W2.lean` L74-102 and L119-122 = `Statements_FINAL.lean`) -/", ""]
structs_a = len(out) + 1
out += rng(S, 74, 102)          # NgFrontIClauses .. NgDeletionsClauses, each followed by a blank line
structs_b = len(out)
out += rng(S, 119, 122)         # NgLocalFrontBoundClauses + blank
structs_c = len(out)
out += ["namespace FrontRows", "", "section Leaves", ""]
lgeo_a = len(out) + 1
out += rng(S, 11085, 11092)     # the L-geo section docstring + blank
u5_a = len(out) + 1
out += rng(U5, 11093, 13042)    # the U5 block
u5_b = len(out)
site_a = len(out) + 1
out += rng(U5, 13043, 13066)    # typeIII_site: docstring, theorem, proved body, blank
site_b = len(out)
u6_a = len(out) + 1
out += rng(U6, 11103, 22211)    # the U6 block
u6_b = len(out)
note_a = len(out) + 1
out += NOTE_II
typeI_a = len(out) + 1
out += rng(U6, 22222, 22229)    # typeI_move: docstring, theorem, proved body, blank
typeI_b = len(out)
cc_a = len(out) + 1
out += rng(U6, 22230, 22238)    # crossedCusp_move: docstring, theorem, proved body, blank
cc_b = len(out)
out += ["end Leaves", ""]
out += ["/-! ## Glue: the polynomial consumers (verbatim from `Skeleton_W2.lean` L14619-14624, L14631-14642) -/", ""]
pIII_a = len(out) + 1
out += rng(S, 14619, 14624)     # P_typeIII + blank
pI_a = len(out) + 1
out += rng(S, 14631, 14636)     # P_typeI + blank
pcc_a = len(out) + 1
out += rng(S, 14637, 14642)     # P_crossedCusp + blank
pcc_b = len(out)
out += ["end FrontRows", "", "open FrontRows", ""]
out += ["/-! ## Assembly of rows 77, 79 and 80 (verbatim from `Skeleton_W2.lean` L14757-14764, L14774-14804) -/", ""]
rI_a = len(out) + 1
out += rng(S, 14757, 14764)     # ng_front_I + blank
rIII_a = len(out) + 1
out += rng(S, 14774, 14782)     # ng_front_III + blank
rD_a = len(out) + 1
out += rng(S, 14783, 14804)     # ng_deletions + blank
rD_b = len(out)
out += ["end SM"]
text = "\n".join(out) + "\n"
open(OUT, "w", encoding="utf-8").write(text)
lines = text.split("\n")
n = text.count("\n")
print(f"wrote {OUT}: {n} lines")

# ---- verification: byte identity of every copied range ----
def eq(desc, a, b, src, sa, sb):
    got = lines[a - 1:b]; want = rng(src, sa, sb)
    assert got == want, f"NOT byte-identical: {desc} (delta {a}-{b} vs source {sa}-{sb})"
eq("structures 1-4", structs_a, structs_b, S, 74, 102)
eq("structure 5", structs_b + 1, structs_c, S, 119, 122)
eq("L-geo docstring", lgeo_a, lgeo_a + 7, S, 11085, 11092)
eq("U5 block", u5_a, u5_b, U5, 11093, 13042)
eq("typeIII_site", site_a, site_b, U5, 13043, 13066)
eq("U6 block", u6_a, u6_b, U6, 11103, 22211)
eq("typeI_move", typeI_a, typeI_b, U6, 22222, 22229)
eq("crossedCusp_move", cc_a, cc_b, U6, 22230, 22238)
eq("P_typeIII", pIII_a, pIII_a + 5, S, 14619, 14624)
eq("P_typeI", pI_a, pI_a + 5, S, 14631, 14636)
eq("P_crossedCusp", pcc_a, pcc_b, S, 14637, 14642)
eq("ng_front_I", rI_a, rI_a + 7, S, 14757, 14764)
eq("ng_front_III", rIII_a, rIII_a + 8, S, 14774, 14782)
eq("ng_deletions", rD_a, rD_b, S, 14783, 14804)
# statement lines of the three leaves == skeleton statement lines (with `:= sorry` -> `:= by` / `:= U6....`)
assert lines[site_a + 7 - 1] == s(11100) and lines[site_a + 8 - 1].rsplit(":=", 1)[0] == s(11101).rsplit(":=", 1)[0]
assert lines[typeI_a + 4 - 1:typeI_a + 6 - 1] == rng(S, 11117, 11118) and lines[typeI_a + 6 - 1].rsplit(":=", 1)[0] == s(11119).rsplit(":=", 1)[0]
assert lines[cc_a + 5 - 1:cc_a + 7 - 1] == rng(S, 11126, 11127) and lines[cc_a + 7 - 1].rsplit(":=", 1)[0] == s(11128).rsplit(":=", 1)[0]
bad = [(i, l) for i, l in enumerate(lines, 1) if "sorry" in l.lower()]
bad2 = [(i, l) for i, l in enumerate(lines, 1) if any(k in l for k in ("#print", "#eval", "#check", "set_option"))]
assert not bad, bad[:5]
assert not bad2, bad2[:5]
print("  byte-identity checks OK; sorry (case-insensitive) = 0; #print/#eval/#check/set_option = 0")

# ---- line map ----
def find(prefix, a, b):
    for i in range(a, b + 1):
        if lines[i - 1].startswith(prefix): return i
    raise KeyError(prefix)
M = {
 "NgFrontIClauses": find("structure NgFrontIClauses", structs_a, structs_c),
 "NgFrontIIClauses": find("structure NgFrontIIClauses", structs_a, structs_c),
 "NgFrontIIIClauses": find("structure NgFrontIIIClauses", structs_a, structs_c),
 "NgDeletionsClauses": find("structure NgDeletionsClauses", structs_a, structs_c),
 "NgLocalFrontBoundClauses": find("structure NgLocalFrontBoundClauses", structs_a, structs_c),
 "typeIII_site": find("theorem typeIII_site", site_a, site_b),
 "typeI_move": find("theorem typeI_move", typeI_a, typeI_b),
 "crossedCusp_move": find("theorem crossedCusp_move", cc_a, cc_b),
 "P_typeIII": find("theorem P_typeIII", pIII_a, pIII_a + 5),
 "P_typeI": find("theorem P_typeI", pI_a, pI_a + 5),
 "P_crossedCusp": find("theorem P_crossedCusp", pcc_a, pcc_b),
 "ng_front_I": find("theorem ng_front_I", rI_a, rI_a + 7),
 "ng_front_III": find("theorem ng_front_III", rIII_a, rIII_a + 8),
 "ng_deletions": find("theorem ng_deletions", rD_a, rD_b),
}
print(f"  header L3-{2 + len(HEADER.split(chr(10)))}; preamble to L{structs_a - 3}")
print(f"  structures: delta L{structs_a}-{structs_c} (skeleton 74-102, 119-122): " + ", ".join(f"{k} L{v}" for k, v in M.items() if k.startswith("Ng")))
print(f"  namespace FrontRows L{structs_c + 1}, section Leaves L{structs_c + 3}; L-geo docstring L{lgeo_a}-{lgeo_a + 7}")
print(f"  U5 block: delta L{u5_a}-{u5_b} (W3_U5 11093-13042, offset {u5_a - 11093:+d}); typeIII_site docstring L{site_a}, theorem L{M['typeIII_site']}-{site_b - 1} (W3_U5 13043-13066)")
print(f"  U6 block: delta L{u6_a}-{u6_b} (W3_U6 11103-22211, offset {u6_a - 11103:+d}); typeII_move note L{note_a}-{note_a + 1}")
print(f"  typeI_move docstring L{typeI_a}, theorem L{M['typeI_move']}-{typeI_b - 1} (W3_U6 22222-22229); crossedCusp_move docstring L{cc_a}, theorem L{M['crossedCusp_move']}-{cc_b - 1} (W3_U6 22230-22238)")
print(f"  end Leaves L{cc_b + 1}; P_typeIII L{M['P_typeIII']}, P_typeI L{M['P_typeI']}, P_crossedCusp L{M['P_crossedCusp']}; end FrontRows L{pcc_b + 1}, open FrontRows L{pcc_b + 3}")
print(f"  ng_front_I L{M['ng_front_I']} (doc {rI_a}), ng_front_III L{M['ng_front_III']} (doc {rIII_a}), ng_deletions L{M['ng_deletions']} (doc {rD_a}-{rD_a + 1}); end SM L{n}")
import json
json.dump({"lines": n, "map": M, "ranges": {"structs": [structs_a, structs_c], "lgeo": [lgeo_a, lgeo_a + 7], "u5": [u5_a, u5_b], "site": [site_a, site_b],
           "u6": [u6_a, u6_b], "note": [note_a, note_a + 2], "typeI": [typeI_a, typeI_b], "cc": [cc_a, cc_b], "pIII": [pIII_a, pIII_a + 5], "pI": [pI_a, pI_a + 5],
           "pcc": [pcc_a, pcc_b], "rI": [rI_a, rI_a + 7], "rIII": [rIII_a, rIII_a + 8], "rD": [rD_a, rD_b]}}, open(f"{TMP}/linemap.json", "w"), indent=1)

# ---- axiom probe copy ----
probe = text + "\n".join([
    "#print axioms SM.ng_front_I",
    "#print axioms SM.ng_front_III",
    "#print axioms SM.ng_deletions",
    "#print axioms SM.FrontRows.typeIII_site",
    "#print axioms SM.FrontRows.typeI_move",
    "#print axioms SM.FrontRows.crossedCusp_move",
    "#print axioms SM.FrontRows.P_typeIII",
    "#print axioms SM.FrontRows.P_typeI",
    "#print axioms SM.FrontRows.P_crossedCusp",
    "#print axioms SM.FrontRows.U5.Pair.site_of",
    "#print axioms SM.FrontRows.U6.typeI_move_proof",
    "#print axioms SM.FrontRows.U6.crossedCusp_move_proof",
    "#print axioms SM.NgFrontIClauses",
    "#print axioms SM.NgFrontIIClauses",
    "#print axioms SM.NgFrontIIIClauses",
    "#print axioms SM.NgDeletionsClauses",
    "#print axioms SM.NgLocalFrontBoundClauses",
]) + "\n"
open(PROBE, "w", encoding="utf-8").write(probe)
print(f"  probe: {PROBE}")
