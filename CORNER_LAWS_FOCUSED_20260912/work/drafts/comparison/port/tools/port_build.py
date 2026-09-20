#!/usr/bin/env python3
"""port_build.py — build the port-ready comparison-lane modules from work/drafts/comparison/Comparison_Assembled.lean.

Every module is a concatenation of VERBATIM line ranges of the assembled file (1-indexed, inclusive) and a few NEW
lines (header, imports, module docstring, the `open` line where reduced, the row-122 one-liner).  Each range boundary
is guarded by an assertion on the expected text, so an off-by-one cannot pass silently.  Output:
work/drafts/comparison/port/SM/*.lean and a JSON manifest (stdout).
Usage: python3 port_build.py [--time HH:MM]     (default header time placeholder <HH:MM>)"""
import argparse, json, pathlib

HERE = pathlib.Path(__file__).resolve().parent
PORT = HERE.parent
LANE = PORT.parent
SRC = LANE / "Comparison_Assembled.lean"
OUT = PORT / "SM"
OUT.mkdir(parents=True, exist_ok=True)

ap = argparse.ArgumentParser()
ap.add_argument("--time", default="<HH:MM>")
T = ap.parse_args().time

lines = SRC.read_text(encoding="utf-8").split("\n")
assert lines[-1] == "", "assembled file must end with a newline"
lines = lines[:-1]
assert len(lines) == 1052, len(lines)

def L(i):
    return lines[i - 1]

GUARDS = {
    1: "import SM.Uniqueness", 14: "import SM.CBProducts", 16: "/-! # Comparison_Assembled — comparison lane: rows 122 prop:anchor-values, 127 thm:comparison,",
    45: "the tail's copy is to be replaced by §4's (PLAN_FINAL.md §6). -/", 47: "namespace SM",
    49: "open WallGerm SoftDuplication Carrier", 51: "/-! ## §0 Interfaces of the corner lane — VERBATIM copies (TO BE UNIFIED) -/",
    53: "section CornerInterfaces", 60: "structure CS7Data : Prop where", 72: "structure CSoftData : Prop where",
    82: "theorem cvl_embedded_of_no_crossings (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)",
    106: "theorem corner_values_i (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)", 129: "end CornerInterfaces", 130: "",
    131: "/-! ## §1 The descent of `C` to the polygon space (library; helpers prefixed `cp_`).", 137: "section Descent",
    140: "theorem cp_cornerStateSum_compat (hn : 3 ≤ n) (P Q : GenericTuple n)", 161: "end Descent",
    186: "  exact (prop_C_chamber.constant n hn P' Q' hQ).symm", 187: "",
    188: "/-! ## §2 Row 122 prop:anchor-values (sm-5:461-476) — proposed name `SM.prop_anchor_values` -/",
    195: "structure AnchorValuesHypotheses (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) : Prop where",
    220: "structure AnchorValuesData : Prop where", 404: "theorem anchor_values_of (hs : CSoftData) : AnchorValuesData where",
    439: "    cornerPolygon_projection' A.parent_card] at h", 440: "",
    441: "/-! ## §3 Row 127 thm:comparison (sm-6:299-311) — FIXED name `SM.thm_comparison` -/", 445: "def TrianglesC : Prop :=",
    538: "theorem trianglesC : TrianglesC := by", 616: "theorem uniquenessHypotheses_C_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData) :",
    652: "theorem thm_comparison_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData) :",
    677: "    exact thm_comparison_of hR h7 hs n hn P.val P.property", 678: "",
    679: "/-! ## §4 Row 128 cor:C-inherits (sm-6:313-372) — FIXED name `SM.cor_C_inherits` -/", 684: "def CuspLawC : Prop :=",
    699: "def ReversalLawC : Prop :=", 712: "structure CInheritsData : Prop where", 768: "  triangles : TrianglesC", 769: "",
    770: "/-! ### The cusp law — the ONE open leaf of the lane.  Prefix `cu_`. -/", 771: "",
    772: "/-! #### Helpers of unit U-CM-CUSPGEN (prefix `cu_`): the fused-edge containments (PLAN_FINAL.md §3.4",
    779: "theorem cu_fused_interior_true {n : ℕ} [NeZero n] {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}",
    871: "def cu_lift {n : ℕ} [NeZero n] (j k : ZMod (n + 1)) (i : ZMod n) : ZMod (n + 1) :=",
    908: "/-- LEAF (unit U-CM-CUSPGEN; sm-6:335-359): at a simple cusp wall whose deletion `Q = P(0) ∖ j`",
    916: "theorem cusp_deletion_generic {n : ℕ} [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1))",
    936: "  simp only [hce, Finset.notMem_empty] at hm", 937: "",
    938: "/-- The cusp law for `C` from `C = A` (thm:comparison) and thm:A-S4 via cor:A-lawful", 940: "theorem cu_cuspLawC_of",
    963: "theorem cor_C_inherits_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData) : CInheritsData := by",
    997: "    exact A_lawful.reversal_law n hn P hP", 998: "",
    999: "/-! ## §5 The row theorems (UNCONDITIONAL statements; `sorry` until rows 110 thm:C-S7 and 112 thm:C-soft",
    1003: "/-- Row 122 prop:anchor-values (proposed name).  Body once row 112 lands: `anchor_values_of thm_C_soft`. -/",
    1004: "theorem prop_anchor_values : AnchorValuesData := by", 1005: "  sorry",
    1009: "theorem thm_comparison (hR : hyp_R) :", 1016: "theorem cor_C_inherits (hR : hyp_R) : CInheritsData := by", 1017: "  sorry",
    1019: "/-! ## §6 Consumer and equivalence shape checks (all PROVED) -/",
    1050: "  fun n _ hn P hP => hinh.root_values n hn P hP 0", 1051: "", 1052: "end SM",
}
for i, t in GUARDS.items():
    assert L(i) == t, f"guard failed at assembled line {i}:\n  expected {t!r}\n  found    {L(i)!r}"

OPEN_FULL = L(49)
assert OPEN_FULL == "open WallGerm SoftDuplication Carrier"
HDR = "-- Ported {T}Z 2026-09-15 from work/drafts/comparison/Comparison_Assembled.lean lines {ranges} ({what}) by the pod executor; {how}"

def build(name, ranges, what, how, imports, doc, open_line, tail=None, ranges_label=None):
    """ranges: list of (a, b) inclusive assembled ranges, emitted in order with one blank line between them;
    ranges_label overrides the header's range text (the row module quotes its source lines but copies no range)."""
    out = [HDR.format(T=T, ranges=ranges_label or ", ".join(f"{a}-{b}" if a != b else f"{a}" for a, b in ranges), what=what, how=how)]
    out += imports + [""] + doc + ["", L(47), ""] + ([open_line, ""] if open_line else [])
    spans = []
    for k, (a, b) in enumerate(ranges):
        if k > 0:
            out.append("")
        s = len(out) + 1
        out += lines[a - 1:b]
        spans.append({"assembled": [a, b], "output": [s, len(out)]})
    if tail:
        out += ([] if out[-1] == "" else [""]) + tail
    out += ["", L(1052), ""]
    p = OUT / f"{name}.lean"
    p.write_text("\n".join(out), encoding="utf-8")
    return {"module": f"SM.{name}", "file": str(p.relative_to(LANE.parent.parent.parent)), "lines": len(out) - 1, "spans": spans}

manifest = []

manifest.append(build(
    "CornerPolygon", [(131, 186)],
    "comparison lane §1, library: the descent of `C` to the polygon space — `cp_cornerStateSum_compat`, `cornerPolygonSum`, "
    "`cornerPolygonSum_projection`, `cp_cornerStateSum_congr`, `cornerPolygon`, `cornerPolygon_projection`, "
    "`cornerPolygon_projection'`, `cornerPolygon_chamber`",
    "body verbatim except this header, the import block (`import SM.CChamber` alone replaces the draft's 14 imports; compile-verified "
    "sufficient), the module docstring (new) and the draft's file-level line 49 `open WallGerm SoftDuplication Carrier` reduced to "
    "`open WallGerm Carrier` (the namespace `SoftDuplication` is not in this module's import closure; nothing in §1 uses it).  "
    "The wrappers `namespace SM` (line 47) / `end SM` (line 1052) are repeated.",
    ["import SM.CChamber"],
    ["/-! # The descent of `C` to the polygon space — comparison lane §1 (library material)",
     "",
     "Source: work/drafts/comparison/Comparison_Assembled.lean §1 (ASSEMBLY_REPORT.md §7 port plan; PLAN_FINAL.md §4 unit",
     "U-CM-CPOLY, FR-CM-5).  def:C defines `C` on labelled generic tuples; sm-5/sm-6 compare it with thm:uniqueness's",
     "`F : ∀ n [NeZero n], GenericPolygon n → ℤ`.  `cornerPolygon` is the `Quotient.lift` of `cornerStateSum` along def:C's",
     "cyclic quotient (the accepted `cornerStateSum_genericShift`, SM/CChamber.lean), `0` below arity 3; `cornerPolygon_chamber`",
     "is prop:C-chamber on the quotient.  Consumers: SM/AnchorValues.lean (row 122), SM/Comparison.lean (row 127),",
     "SM/CInherits.lean (row 128). -/"],
    "open WallGerm Carrier"))

manifest.append(build(
    "AnchorValues", [(188, 439)],
    "comparison lane §2, row 122 prop:anchor-values as library material: `AnchorValuesHypotheses`, "
    "`UniquenessHypotheses.toAnchorValuesHypotheses`, `AnchorValuesData`, the `av_*` helpers, `cornerPolygon_soft_of`, "
    "`cornerPolygon_anchorValuesHypotheses_of`, `anchor_values_of (hs : CSoftData)` and the companions `AnchorValuesData.C_zero/.C_loop/.C_loopZero`",
    "body verbatim except this header, the import block (SM.CornerPolygon for §1, SM.Uniqueness, and SM.CornerChainStatements whose "
    "accepted `CSoftData` replaces the draft's DELETED §0 copy, lines 71-77 — byte-identical declaration block, tools/port_copy_diff.py) "
    "and the module docstring (new).  The wrappers `namespace SM` / `open WallGerm SoftDuplication Carrier` / `end SM` (lines 47, 49, 1052) "
    "are repeated verbatim.",
    ["import SM.CornerPolygon", "import SM.Uniqueness", "import SM.CornerChainStatements"],
    ["/-! # Row 122 prop:anchor-values (sm-5:461-476; proof 477-505) — the statement and the abstract argument",
     "",
     "Source: work/drafts/comparison/Comparison_Assembled.lean §2 (PLAN_FINAL.md §4 unit U-CM-AV; FR-CM-1..5).  `AnchorValuesData`",
     "is prop:anchor-values as printed, one field per clause; `anchor_values_of (hs : CSoftData) : AnchorValuesData` proves it",
     "modulo thm:C-soft (D-F11/D-F14 pattern: every clause but `C_hypotheses.soft` is unconditional).  The row theorem",
     "`SM.prop_anchor_values : AnchorValuesData := anchor_values_of thm_C_soft` is declared in SM/AnchorValuesRow.lean from the",
     "accepted `SM.thm_C_soft` (SM/CSoft.lean).  `CSoftData` is the corner lane's accepted bundle (SM/CornerChainStatements.lean §5). -/"],
    OPEN_FULL))

# row 122 module: statement line of assembled 1004 (signature verbatim, ` by` + `sorry` replaced by the prescribed one-liner)
sig = L(1004)
assert sig.endswith(" := by")
row122 = ["/-- **Row 122 prop:anchor-values** (sm-5:461-476; proposed name `SM.prop_anchor_values`): `AnchorValuesData`",
          "(SM/AnchorValues.lean §2) from thm:C-soft (`SM.thm_C_soft`, SM/CSoft.lean) through `anchor_values_of` — the body the",
          "frozen docstring prescribed for the moment row 112 lands. -/",
          sig[: -len(" by")] + " anchor_values_of thm_C_soft"]
manifest.append(build(
    "AnchorValuesRow", [],
    "comparison lane §5, row 122 prop:anchor-values: the row theorem `SM.prop_anchor_values : AnchorValuesData` (proposed name), body "
    "`anchor_values_of thm_C_soft` as the frozen docstring (line 1003) prescribes once row 112 lands — it has, SM/CSoft.lean",
    "statement line 1004 verbatim (the trailing ` by` of the draft's placeholder body dropped); the docstring rewritten for the accepted "
    "state; import block and module docstring new (pattern of SM/CSoft.lean); wrappers `namespace SM` / `end SM` repeated.",
    ["import SM.AnchorValues", "import SM.CSoft"],
    ["/-! # Row 122 prop:anchor-values (sm-5:461-476) — proposed name `SM.prop_anchor_values` -/"],
    None, tail=row122, ranges_label="1003-1005"))

manifest.append(build(
    "CuspDeletionGeneric", [(772, 936)],
    "comparison lane §4, unit U-CM-CUSPGEN: the `cu_*` helpers `cu_fused_interior_true/false`, `cu_deletionIndex_adjacent/_remote/_two_prev`, "
    "`cu_remote_prev/_deleted`, `cu_lift`, `cu_lift_remote`, `cu_lift_interior` and the leaf `cusp_deletion_generic` (PROVED, frozen statement)",
    "body verbatim except this header, the import block (SM.CuspDefinition, SM.DeletionIndices, SM.DeletedTuple, SM.GenericTopology, "
    "SM.ZeroTriples — compile-verified sufficient), the module docstring (new), the draft's file-level line 49 `open WallGerm "
    "SoftDuplication Carrier` reduced to `open WallGerm` (the namespaces `SoftDuplication`, `Carrier` are not in this module's import "
    "closure; nothing here uses them) and the DROPPED section-comment line 770 (`### The cusp law — the ONE open leaf of the lane. …`, "
    "stale: the leaf is proved).  Wrappers `namespace SM` / `end SM` repeated.",
    ["import SM.CuspDefinition", "import SM.DeletionIndices", "import SM.DeletedTuple", "import SM.GenericTopology", "import SM.ZeroTriples"],
    ["/-! # Genericity of the cusp deletion (sm-6:335-359) — comparison lane unit U-CM-CUSPGEN (library material)",
     "",
     "Source: work/drafts/comparison/Comparison_Assembled.lean §4 (U_CUSPGEN_REPORT.md; PLAN_FINAL.md §3.4).  At a simple cusp wall",
     "`w : WallGerm (n + 1)` whose deletion `Q = P(0) ∖ j` satisfies (G1), `Q` is generic (`cusp_deletion_generic`): the fused edge",
     "`[A, B]` lies in the longer of `E_{j−1}(0)`, `E_j(0)` (`w.cusp_cases`), three pairwise remote edges of `Q` with a common",
     "relative-interior point lift injectively (`cu_lift`) to three pairwise remote edges of the centre with a common point, contrary",
     "to `concurrences = ∅`.  Pure accepted geometry; no dependence on the C rows.  Consumer: `cu_cuspLawC_of` (SM/CInherits.lean). -/"],
    "open WallGerm"))

manifest.append(build(
    "Comparison", [(441, 677)],
    "comparison lane §3, row 127 thm:comparison as library material: `TrianglesC` (this lane owns the CV/R tail's Prop, PLAN_FINAL.md §6), "
    "the `tri_*` helpers and `trianglesC` (UNCONDITIONAL), the `cs3_*` bridge, `uniquenessHypotheses_C_of`, `thm_comparison_of (hR) (h7) (hs)` "
    "and the companions `thm_comparison_root_of`, `thm_comparison_polygon_of`",
    "body verbatim except this header, the import block (SM.AnchorValues for §1-§2, SM.CornerChainUnits whose accepted `corner_values_i` "
    "replaces the draft's DELETED §0 copies of `cvl_embedded_of_no_crossings` / `corner_values_i`, lines 78-127, byte-identical declaration "
    "blocks, tools/port_copy_diff.py; SM.CS3, SM.CSilent, SM.HypR; `CS7Data` resolves to the accepted SM/CornerChainStatements.lean "
    "declaration, replacing the deleted copy at lines 59-69) and the module docstring (new).  Wrappers `namespace SM` / "
    "`open WallGerm SoftDuplication Carrier` / `end SM` repeated verbatim.  The row theorem `SM.thm_comparison (hR : hyp_R)` is NOT "
    "declared here: it needs `SM.thm_C_S7` (row 110), see port/PORT_REPORT.md §5.",
    ["import SM.AnchorValues", "import SM.CornerChainUnits", "import SM.CS3", "import SM.CSilent", "import SM.HypR"],
    ["/-! # Row 127 thm:comparison (sm-6:299-303; proof 304-311) — the conditional theorem and its ingredients",
     "",
     "Source: work/drafts/comparison/Comparison_Assembled.lean §3 (PLAN_FINAL.md §4 units U-CM-TRI, U-CM-CS3, U-CM-CMP; FR-CM-6,",
     "FR-CM-7, FR-CM-10..12).  `thm_comparison_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData)` is \"Assume Hypothesis R.  Then",
     "C(P) = A(P) for every generic polygon P\" modulo rows 110 thm:C-S7 and 112 thm:C-soft (D-F11/D-F14 pattern): the accepted",
     "`SM.uniqueness` (SM/Uniqueness.lean) at `cornerPolygon` with (a) prop:C-chamber + prop:C-silent, (b) thm:C-S3 through the",
     "`cs3_*` bridge, (c) `h7`, (d) `hR`, (e) `hs`, (f) the UNCONDITIONAL `trianglesC` from the accepted `corner_values_i`",
     "(SM/CornerChainUnits.lean §3).  The row theorem `SM.thm_comparison (hR : hyp_R)` (FIXED name) is declared when `SM.thm_C_S7`",
     "exists, as `thm_comparison_of hR thm_C_S7 thm_C_soft`. -/"],
    OPEN_FULL))

manifest.append(build(
    "CInherits", [(679, 768), (938, 997), (1019, 1050)],
    "comparison lane §4 and §6, row 128 cor:C-inherits as library material: `CuspLawC`, `ReversalLawC`, `CInheritsData` (this lane owns the "
    "row-128 bundle and the CV/R tail's three Props, PLAN_FINAL.md §6), `cu_cuspLawC_of`, `cor_C_inherits_of (hR) (h7) (hs)`, and the six §6 "
    "consumer / equivalence `example`s",
    "body verbatim except this header, the import block (SM.Comparison, SM.CuspDeletionGeneric) and the module docstring (new); the three "
    "ranges are the draft's §4 minus the unit block 770-936 (now SM/CuspDeletionGeneric.lean) and §6, each verbatim.  Wrappers "
    "`namespace SM` / `open WallGerm SoftDuplication Carrier` / `end SM` repeated verbatim.  The row theorem `SM.cor_C_inherits (hR : hyp_R)` "
    "is NOT declared here: it needs `SM.thm_C_S7` (row 110), see port/PORT_REPORT.md §5.",
    ["import SM.Comparison", "import SM.CuspDeletionGeneric"],
    ["/-! # Row 128 cor:C-inherits (sm-6:313-319; proof 320-372) — the bundle, the conditional theorem, the shape checks",
     "",
     "Source: work/drafts/comparison/Comparison_Assembled.lean §4, §6 (PLAN_FINAL.md §4 unit U-CM-INH; FR-CM-8, FR-CM-9, FR-CM-13..17).",
     "`CInheritsData` is the accepted `ALawfulData` field for field with `cornerStateSum` for `amplitude`, plus `root_values`;",
     "`CuspLawC`, `ReversalLawC` (here) and `TrianglesC` (SM/Comparison.lean) are the Props the CV/R tail's row 184 reads",
     "(`corner_laws_and_soft_of`: `hinh.cusp_law`, `hinh.reversal_law`, `hinh.triangles`).  `cor_C_inherits_of (hR : hyp_R)",
     "(h7 : CS7Data) (hs : CSoftData) : CInheritsData` is proved from `thm_comparison_of`, the accepted `A_lawful` and the",
     "genericity checks (lem:children, lem:soft-generic, `cusp_deletion_generic`).  The row theorem `SM.cor_C_inherits (hR : hyp_R)`",
     "(FIXED name) is declared when `SM.thm_C_S7` exists, as `cor_C_inherits_of hR thm_C_S7 thm_C_soft`. -/"],
    OPEN_FULL))

print(json.dumps(manifest, indent=1, ensure_ascii=False))
