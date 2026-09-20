#!/usr/bin/env python3
"""port_build.py — build the port-ready corner-chain modules from work/drafts/corner/Wave2a_Assembled.lean.

Every module is a concatenation of VERBATIM line ranges of the assembled file (1-indexed, inclusive) and a few
NEW lines (header, imports, module docstrings, the three one-line row bodies).  Each range boundary is
guarded by an assertion on the expected text, so an off-by-one cannot pass silently.  Output:
work/drafts/corner/port/SM/*.lean and a JSON manifest (stdout) with, per module, the source ranges and the
output line span each range landed on.

Usage: python3 port_build.py [--time HH:MM]     (default time placeholder <HH:MM>)
"""
import argparse, json, pathlib, sys

HERE = pathlib.Path(__file__).resolve().parent
PORT = HERE.parent
CORNER = PORT.parent
SRC = CORNER / "Wave2a_Assembled.lean"
OUT = PORT / "SM"

ap = argparse.ArgumentParser()
ap.add_argument("--time", default="<HH:MM>")
args = ap.parse_args()
T = args.time

lines = SRC.read_text(encoding="utf-8").split("\n")
assert lines[-1] == "", "assembled file must end with a newline"
lines = lines[:-1]
assert len(lines) == 12233, len(lines)

def L(i):
    """1-indexed line."""
    return lines[i - 1]

# ---- boundary guards (assembled numbering) ---------------------------------------------------------------
GUARDS = {
    1: "import SM.CBProducts", 17: "import SM.VertexSides", 18: "", 19: "/-! # Statements_FINAL — the corner chain after thm:floor: rows 103 cb:singleton, 105 lem:corner-values,",
    43: "(rows 103, 110); `z_parity` is never used (FR-CC-10). -/", 44: "", 45: "namespace SM", 47: "open Link Carrier",
    49: "attribute [local instance] Classical.propDecidable", 51: "noncomputable section", 52: "",
    53: "/-! ## §0 The row-100 interface (VERBATIM from work/drafts/floor/Statements_FINAL.lean §7) and the bridge",
    54: "from the signed form the proof routes produce. -/", 55: "", 56: "section Floor", 58: "variable {n : ℕ} [NeZero n]", 59: "",
    60: "/-- \"either all turns are left, or exactly one turn is right\" on the corner polygon `Q` (turns =",
    62: "def AllLeftOrOneRight {m : ℕ} (Q : LabelledTuple m) : Prop :=",
    79: "structure FloorTheoremData : Prop where",
    91: "    InSupportM 1 (cornerHomfly hn hP S q hS) ∧ 0 ≤ mindegZZ (cornerHomfly hn hP S q hS)", 92: "",
    93: "/-! ### The bridge (judge's addition, PROVED).  The proof routes of rows 103 and 110 produce turn",
    151: "end Floor", 156: "section Algebra", 180: "end Algebra", 181: "",
    182: "/-! ## §2 Row 103 cb:singleton (sm-3:4697-4702; proof 4703-4759) -/", 184: "section Singleton",
    186: "variable {n : ℕ} [NeZero n]", 187: "", 195: "structure CbSingletonData : Prop where",
    201: "      cornerCoefficient hn hP S A hS = 0", 202: "",
    203: "/-! ### Leaves of row 103 (frozen; units U103-A … U103-E of PLAN_FINAL.md §4). Prefix `sg_`. -/",
    1315: "end Singleton", 1316: "", 1317: "/-! ## §3 Row 105 lem:corner-values (sm-3:4801-4809; proof 4810-4820) -/",
    1319: "section CornerValues", 1321: "variable {n : ℕ} [NeZero n]", 1322: "",
    1331: "structure CornerValuesData : Prop where", 1341: "      cornerCoefficient hn hP S q hS = 0", 1342: "",
    1343: "/-! ### Row 105 (i) — UNCONDITIONAL, PROVED (grafted from Sketch_A; no floor, no leaf).  Prefix `cvl_`. -/",
    1396: "", 1397: "/-- Companion: (i)'s rotation clause for def:C's integer `r_Q` (`carrierRotationInt_cast`). -/",
    1398: "theorem CornerValuesData.embedded_rotationInt (hD : CornerValuesData) (hn : 3 ≤ n)",
    1405: "  exact_mod_cast h'", 1406: "",
    1407: "/-- **Row 105 from row 103** ((ii) is cb:singleton at `(Q, y)`; (i) needs no floor). -/",
    1413: "theorem corner_values_of_floor (hF : FloorTheoremData) : CornerValuesData :=", 1415: "",
    1416: "end CornerValues", 1417: "",
    1418: "/-! ## §4 Row 110 thm:C-S7 (sm-4:267-274; proof 275-908) — fixed target name `SM.thm_C_S7` -/",
    1420: "section VertexEdge", 1422: "variable {n : ℕ} [NeZero n]", 1423: "",
    1436: "structure CS7Data : Prop where", 1473: "  rw [g.contactSign_eq_at M a tm]", 1474: "",
    1475: "/-! ### Leaves of row 110 (units U110-A … U110-K of PLAN_FINAL.md §4). Prefix `s7_`.",
    5720: "", 5721: "/-- The sliding branch (sm-4:300-406): relocation bijection `φ(x₋) = x₊`, the support bijection",
    5724: "theorem s7_sliding_law_at (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) (h : g.SlidingAt M a)",
    5732: "  sorry", 5733: "",
    5734: "/-! ### Unit U110-H (helper unit, prefix `s7h_`; PLAN_FINAL §3.3 (3), §4): the two-component row of",
    6879: "end S7IRotationLedger", 6880: "",
    6881: "/-- The bigon branch (sm-4:407-874): two-newborn sector `B = (1−ε)J` (contact triangle: a crossing-free",
    6889: "theorem s7_bigon_law_at (hF : FloorTheoremData) (hsing : CbSingletonData) (hn : 3 ≤ n)",
    6898: "  sorry", 6899: "",
    6900: "/-! Two pure-algebra leaves of the bigon branch, stated now on the accepted ring (units U110-G / U110-J). -/",
    7071: "  refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩ <;> simp only <;> omega", 7072: "",
    7073: "/-- **Row 110, conditional on thm:floor AND cb:singleton** (the printed dependency list of",
    7077: "theorem thm_C_S7_of (hF : FloorTheoremData) (hsing : CbSingletonData) : CS7Data := by",
    7102: "theorem thm_C_S7_of_floor (hF : FloorTheoremData) : CS7Data :=", 7104: "",
    7105: "end VertexEdge", 7106: "",
    7107: "/-! ## §5 Row 112 thm:C-soft (sm-4:984-991; proof 992-1147) — fixed target name `SM.thm_C_soft` -/",
    7109: "section Soft", 7111: "open SoftDuplication", 7113: "variable {n : ℕ} [NeZero n]", 7114: "",
    7123: "structure CSoftData : Prop where", 7158: "  exact_mod_cast h2", 7159: "",
    7160: "/-! ### Leaves of row 112 (the three printed sectors; units U112-A … U112-D). Prefix `sft_`. -/",
    12198: "end Soft", 12199: "",
    12200: "/-! ## §6 The row theorems (UNCONDITIONAL statements; `sorry` until row 100 lands).  Once the floor lane's",
    12204: "/-- Row 103 cb:singleton (proposed name).  Body once row 100 lands: `cb_singleton_of_floor thm_floor`. -/",
    12205: "theorem cb_singleton : CbSingletonData := by", 12210: "theorem corner_values : CornerValuesData := by",
    12215: "theorem thm_C_S7 : CS7Data := by", 12220: "theorem thm_C_soft : CSoftData := by",
    12228: "example (hF : FloorTheoremData) : CS7Data ∧ CSoftData ∧ CbSingletonData ∧ CornerValuesData :=",
    12230: "", 12231: "end", 12232: "", 12233: "end SM",
}
bad = [(k, v, L(k)) for k, v in GUARDS.items() if L(k) != v]
if bad:
    for k, v, got in bad:
        print(f"GUARD FAIL line {k}: expected {v!r}, got {got!r}", file=sys.stderr)
    sys.exit(2)

# ---- new text -------------------------------------------------------------------------------------------
HDR_STMTS = (
    f"-- Ported {T}Z 2026-09-15 from work/drafts/corner/Wave2a_Assembled.lean lines 1-59, 93-202, 1315-1342, "
    "1397-1406, 1416-1474, 7105-7159, 12198-12199, 12231-12233 (corner chain lane, STATEMENTS of rows 103 cb:singleton, "
    "105 lem:corner-values, 110 thm:C-S7, 112 thm:C-soft: §0 the signed-form bridge to the accepted floor interface, "
    "§1 the shared algebra, the row bundles CbSingletonData, CornerValuesData (+ embedded_rotationInt), CS7Data "
    "(+ bigon, sliding, contactSign_literal), CSoftData (+ exists_generic, doubled), each inside its frozen "
    "section/variable wrapper) by the pod executor; body verbatim except this header, the added `import SM.CarrierFloor`, "
    "the module docstring (lines 19-43 reworded: draft-state sentences dropped, the §0 paragraph now describes the "
    "import), the §0 heading (lines 53-54 reworded), the DELETED lines 60-92 (the byte-identical copies of "
    "`AllLeftOrOneRight`, `CarrierUniformOrOneDissent`, `FloorTheoremData` — accepted in SM/CarrierFloor.lean:377-408), "
    "and the section closers `end Singleton` / `end CornerValues` / `end VertexEdge` / `end Soft` (lines 1315, 1416, "
    "7105, 12198) repeated here around the bundles whose unit sections live in SM/CornerChainUnits.lean."
)
HDR_UNITS = (
    f"-- Ported {T}Z 2026-09-15 from work/drafts/corner/Wave2a_Assembled.lean lines 44-52, 182-187, 203-1322, "
    "1343-1396, 1407-1423, 1475-5720, 5734-6880, 6900-7072, 7105-7114, 7160-12199, 12231-12233 (corner chain lane, "
    "UNITS: §2 the leaves of row 103 with the sgb_/sgc_/sgd_/sge_ helper blocks and cb_singleton_of_floor; §3 row 105 "
    "clause (i) cvl_/corner_values_i and corner_values_of_singleton/_of_floor; §4 the helper blocks s7a_ … s7i_, s7g_ of "
    "row 110 and its two closed algebra leaves s7_universal_extraction, s7_corner_product; §5 the leaves of row 112 with "
    "the sfta_/sftc_/sftb_/sftd_ helper blocks and thm_C_soft_of_cornerValues/_of_floor) by the pod executor; body "
    "verbatim except this header, the import block (`import SM.CornerChainStatements` replaces the 17 frozen imports, "
    "which it carries), the module docstring (new), and the OMITTED lines: 1-43 and 53-181 (imports, docstring, §0, §1 "
    "— in SM/CornerChainStatements.lean), 188-202, 1323-1342, 1397-1406, 1424-1474, 7115-7159 (the row bundles and "
    "companions — in SM/CornerChainStatements.lean), 5721-5733 s7_sliding_law_at, 6881-6899 s7_bigon_law_at, "
    "7073-7104 thm_C_S7_of / thm_C_S7_of_floor (row 110 open — NOT ported, stay in the draft), 12200-12230 (the §6 row "
    "theorems — SM/CBSingleton.lean, SM/CornerValues.lean, SM/CSoft.lean — and the §7 example, reduced in SM/CSoft.lean)."
)

DOC_STMTS = """/-! # The corner chain after thm:floor — STATEMENTS of rows 103 cb:singleton, 105 lem:corner-values,
110 thm:C-S7, 112 thm:C-soft (judge's decision, 2026-09-15)

Companion of work/drafts/corner/PLAN_FINAL.md (winner: DESIGN_B's skeleton, with DESIGN_A's grafts).  Frozen
text: work/drafts/corner/Statements_FINAL.lean; assembled with the proved units of waves 1-2a in
work/drafts/corner/Wave2a_Assembled.lean (WAVE2A_ASSEMBLY_REPORT.md; its §7 is the port plan).

This module holds the statements only: §0 the bridge from the signed turn pattern to the floor's hypothesis,
§1 the shared algebra, and the four row bundles `CbSingletonData`, `CornerValuesData`, `CS7Data`, `CSoftData`
with their companions.  The units (helper blocks, proved leaves) and the row-level assemblies
`cb_singleton_of_floor`, `corner_values_of_singleton`, `corner_values_of_floor`, `thm_C_soft_of_cornerValues`,
`thm_C_soft_of_floor`, together with row 105 clause (i) (`corner_values_i`, UNCONDITIONAL — grafted from Sketch_A),
are in SM/CornerChainUnits.lean; the row theorems `SM.cb_singleton`, `SM.corner_values`, `SM.thm_C_soft` are
declared in SM/CBSingleton.lean, SM/CornerValues.lean, SM/CSoft.lean from `SM.thm_floor` (row 100).  Row 110
(`CS7Data`, fixed target name `SM.thm_C_S7`) is STATED here but not yet proved: its two branch leaves and the
assemblies `thm_C_S7_of` / `thm_C_S7_of_floor` stay in the draft until they close.

Sources (frame SM15): reference/SM/sm-3-statesum.tex 4697-4702 (103; proof 4703-4759), 4801-4809 (105;
proof 4810-4820); reference/SM/sm-4-knotlaws.tex 267-274 (110; proof 275-908), 984-991 (112; proof
992-1147).  Dependencies (tools/claims.py): 103 ← thm:floor; 105 ← cb:singleton; 110 ← cb:singleton,
thm:floor; 112 ← lem:corner-values.  Fixed target names (work/lean/axiom-policy.json): `SM.thm_C_S7`,
`SM.thm_C_soft`.  Proposed: `SM.cb_singleton : CbSingletonData`, `SM.corner_values : CornerValuesData`.

§0 imports the accepted interface SM/CarrierFloor.lean §7 (`AllLeftOrOneRight`, `CarrierUniformOrOneDissent`
in the literal reversal form, `FloorTheoremData` with the ℤ ∧ ℝ display — the draft's byte-identical copies
are deleted, the names resolve to the accepted ones) and adds the signed-form bridge.  Only `a_floor`'s first
conjunct is consumed (rows 103, 110); `z_parity` is never used (FR-CC-10). -/"""

HDR0_STMTS = """/-! ## §0 The row-100 interface (the accepted SM/CarrierFloor.lean §7: `AllLeftOrOneRight`,
`CarrierUniformOrOneDissent`, `FloorTheoremData`) and the bridge from the signed form the proof routes produce. -/"""

DOC_UNITS = """/-! # The corner chain after thm:floor — UNITS: helper blocks, proved leaves and row-level assemblies of
rows 103 cb:singleton, 105 lem:corner-values, 112 thm:C-soft, and the closed helper corpus of row 110 thm:C-S7

Statements: SM/CornerChainStatements.lean.  Source: work/drafts/corner/Wave2a_Assembled.lean (the frozen
Statements_FINAL.lean with the units of waves 1-2a; WAVE2A_ASSEMBLY_REPORT.md), kept in the frozen order (§5
uses `sge_` from §2).  Contents: §2 the leaves of row 103 (`sg_`; helpers `sgb_`, `sgc_`, `sgd_`, `sge_`) and
the assembly `cb_singleton_of_floor`; §3 row 105 clause (i) (`cvl_`, `corner_values_i`, unconditional) and
`corner_values_of_singleton` / `corner_values_of_floor`; §4 the helper blocks of row 110 (`s7a_`, `s7b_`, `s7c_`,
`s7d_`, `s7h_`, `s7i_`, `s7g_`) and its two closed algebra leaves `s7_universal_extraction`, `s7_corner_product` —
the two branch leaves `s7_sliding_law_at`, `s7_bigon_law_at` and the assemblies `thm_C_S7_of`, `thm_C_S7_of_floor`
are NOT in this module (still open in the draft; row 110 is unmapped); §5 the leaves of row 112 (`sft_`; helpers
`sfta_`, `sftc_`, `sftb_`, `sftd_`) and `thm_C_soft_of_cornerValues` / `thm_C_soft_of_floor`.  Every declaration is
proved.  The row theorems `SM.cb_singleton`, `SM.corner_values`, `SM.thm_C_soft` are declared in SM/CBSingleton.lean,
SM/CornerValues.lean, SM/CSoft.lean. -/"""

# ---- module recipes: list of ("R", a, b) verbatim ranges or ("N", text) new text ---------------------------
STMTS = [
    ("N", HDR_STMTS), ("R", 1, 17), ("N", "import SM.CarrierFloor"), ("R", 18, 18), ("N", DOC_STMTS),
    ("R", 44, 52), ("N", HDR0_STMTS), ("R", 55, 59),
    ("R", 93, 202), ("R", 1315, 1342), ("R", 1397, 1406), ("R", 1416, 1474), ("R", 7105, 7159),
    ("R", 12198, 12199), ("R", 12231, 12233),
]
UNITS = [
    ("N", HDR_UNITS), ("N", "import SM.CornerChainStatements"), ("N", ""), ("N", DOC_UNITS),
    ("R", 44, 52), ("R", 182, 187), ("R", 203, 1322), ("R", 1343, 1396), ("R", 1407, 1423),
    ("R", 1475, 5720), ("R", 5734, 6880), ("R", 6900, 7072), ("R", 7105, 7114), ("R", 7160, 12199),
    ("R", 12231, 12233),
]

def row_module(hdr_lines, doc, docstring, stmt_line_no, body, extra_imports=(), tail=""):
    hdr = (f"-- Ported {T}Z 2026-09-15 from work/drafts/corner/Wave2a_Assembled.lean lines {hdr_lines} ") + doc
    imports = ["import SM.CornerChainUnits", "import SM.CarrierFloorRows"] + list(extra_imports)
    stmt = L(stmt_line_no)
    assert stmt.endswith(" := by")
    stmt = stmt[: -len(" by")]
    parts = [hdr] + imports + [""] + docstring.split("\n") + ["", "namespace SM", ""]
    parts += ROWDOC[stmt_line_no].split("\n") + [stmt + " " + body]
    if tail:
        parts += [""] + tail.split("\n")
    parts += ["", "end SM"]
    return parts

ROWDOC = {
    12205: """/-- **Row 103 cb:singleton** (sm-3:4697-4702; proof 4703-4759; proposed name): `CbSingletonData`
(SM/CornerChainStatements.lean §2) from thm:floor (`SM.thm_floor`, SM/CarrierFloorRows.lean) through the
conditional assembly `cb_singleton_of_floor` (SM/CornerChainUnits.lean §2). -/""",
    12210: """/-- **Row 105 lem:corner-values** (sm-3:4801-4809; proof 4810-4820; proposed name): `CornerValuesData`
(SM/CornerChainStatements.lean §3) from thm:floor through `corner_values_of_floor` (SM/CornerChainUnits.lean §3;
clause (i) is the unconditional `corner_values_i`, clause (ii) is cb:singleton at `(Q, y)`). -/""",
    12220: """/-- **Theorem thm:C-soft** (sm-4:984-991; proof 992-1147; FIXED target name, axiom-policy.json): `CSoftData`
(SM/CornerChainStatements.lean §5) from thm:floor through `thm_C_soft_of_floor` (SM/CornerChainUnits.lean §5:
row 112 ← lem:corner-values ← cb:singleton ← thm:floor). -/""",
}

CB = row_module(
    "12204-12206",
    "(corner chain lane, row 103 cb:singleton: the row theorem `SM.cb_singleton : CbSingletonData`, body "
    "`cb_singleton_of_floor thm_floor` as the frozen docstring prescribes once row 100 lands — it has, "
    "SM/CarrierFloorRows.lean) by the pod executor; statement line verbatim (the trailing ` by` of the draft's "
    "placeholder body dropped); the docstring rewritten for the accepted state; import block and module docstring new "
    "(pattern of SM/CarrierFloorRows.lean).",
    "/-! # Row 103 cb:singleton (sm-3:4697-4702) -/", 12205, "cb_singleton_of_floor thm_floor")
CV = row_module(
    "12208-12211",
    "(corner chain lane, row 105 lem:corner-values: the row theorem `SM.corner_values : CornerValuesData`, body "
    "`corner_values_of_floor thm_floor` as the frozen docstring prescribes once row 100 lands — it has, "
    "SM/CarrierFloorRows.lean) by the pod executor; statement line verbatim (the trailing ` by` of the draft's "
    "placeholder body dropped); the docstring rewritten for the accepted state; import block and module docstring new "
    "(pattern of SM/CarrierFloorRows.lean).",
    "/-! # Row 105 lem:corner-values (sm-3:4801-4809) -/", 12210, "corner_values_of_floor thm_floor")
CS = row_module(
    "12218-12221 and 12223-12229",
    "(corner chain lane, row 112 thm:C-soft: the row theorem `SM.thm_C_soft : CSoftData` (FIXED target name), body "
    "`thm_C_soft_of_floor thm_floor` as the frozen docstring prescribes once row 100 lands — it has, "
    "SM/CarrierFloorRows.lean; and the §7 consumer shape check) by the pod executor; statement line verbatim (the "
    "trailing ` by` of the draft's placeholder body dropped); the docstring rewritten for the accepted state; the §7 "
    "`example` REDUCED to the three ported rows `⟨cb_singleton, corner_values, thm_C_soft⟩` (the draft's "
    "`thm_C_S7_of_floor hF` conjunct dropped with row 110, its docstring kept verbatim); import block (plus "
    "SM.CBSingleton, SM.CornerValues for the example) and module docstring new (pattern of SM/CarrierFloorRows.lean).",
    "/-! # Row 112 thm:C-soft (sm-4:984-991) — fixed target name `SM.thm_C_soft` -/", 12220,
    "thm_C_soft_of_floor thm_floor", extra_imports=("import SM.CBSingleton", "import SM.CornerValues"),
    tail="\n".join(lines[12223 - 1:12227]) + "\nexample : CbSingletonData ∧ CornerValuesData ∧ CSoftData :=\n  ⟨cb_singleton, corner_values, thm_C_soft⟩")

def build(recipe):
    out, manifest = [], []
    for item in recipe:
        start = len(out) + 1
        if item[0] == "R":
            _, a, b = item
            out.extend(lines[a - 1:b])
            manifest.append({"src": [a, b], "out": [start, len(out)]})
        else:
            txt = item[1]
            out.extend(txt.split("\n"))
            manifest.append({"src": "NEW", "out": [start, len(out)], "preview": txt.split("\n")[0][:90]})
    return out, manifest

OUT.mkdir(parents=True, exist_ok=True)
summary = {}
for name, recipe in [("CornerChainStatements", STMTS), ("CornerChainUnits", UNITS)]:
    out, man = build(recipe)
    (OUT / f"{name}.lean").write_text("\n".join(out) + "\n", encoding="utf-8")
    summary[name] = {"lines": len(out), "manifest": man}
for name, parts in [("CBSingleton", CB), ("CornerValues", CV), ("CSoft", CS)]:
    (OUT / f"{name}.lean").write_text("\n".join(parts) + "\n", encoding="utf-8")
    summary[name] = {"lines": len(parts), "manifest": "new module; statement line verbatim from the assembled file"}

# coverage accounting: which assembled lines landed where (verbatim), which were omitted
placed = {}
for name, recipe in [("CornerChainStatements", STMTS), ("CornerChainUnits", UNITS)]:
    for item in recipe:
        if item[0] == "R":
            for k in range(item[1], item[2] + 1):
                placed.setdefault(k, []).append(name)
omitted = [k for k in range(1, 12234) if k not in placed]
def spans(ks):
    res, s, p = [], None, None
    for k in ks:
        if s is None:
            s = p = k
        elif k == p + 1:
            p = k
        else:
            res.append((s, p)); s = p = k
    if s is not None:
        res.append((s, p))
    return res
summary["omitted_spans"] = spans(omitted)
summary["placed_twice"] = spans(sorted(k for k, v in placed.items() if len(v) > 1))
print(json.dumps(summary, indent=1, ensure_ascii=False))
