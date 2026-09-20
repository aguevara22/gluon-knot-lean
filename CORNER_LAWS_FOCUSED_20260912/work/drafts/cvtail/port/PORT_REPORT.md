# PORT REPORT — CV/R tail lane, wave-1 port-ready modules

Porter, 2026-09-15 ≈ 18:05 UTC / 2:05pm ET.  Source: `work/drafts/cvtail/Wave1_Assembled.lean` (4386 lines, md5
`c196cbf67217716e47101ffda2cea974`, compiles; WAVE1_ASSEMBLY_REPORT.md).  Nothing written under `work/lean`.
Output: four modules under `work/drafts/cvtail/port/`, laid out as they are to land:

| module (port path → work/lean path) | Wave1 lines | lines | md5 | compile | `sorry`/`#print`/`#eval` |
|---|---|---|---|---|---|
| `port/CV/CarrierFloor.lean` → `CV/CarrierFloor.lean` (row 155) | 231-700 (+1765, 1767) | 487 | `7edc0a526f649abf292081f836933e0d` | 0 errors, 0 warnings, 11 s | 0 / 0 / 0 |
| `port/CV/SingletonDi.lean` → `CV/SingletonDi.lean` (row 165) | 241-247, 702-1763 (+1765, 1767) | 1080 | `abe1ac36efb8c8f04e83c6387d0e4d78` | 0 errors, 0 warnings, 29 s | 0 / 0 / 0 |
| `port/RProof/RALedgers.lean` → `RProof/RALedgers.lean` (library, no row) | 1772-2536, 2622-3470, 3485-4191, 4206-4218, 4228, 4232, 4239-4244, 4246 | 2372 | `4fd213432fc11a731830fe28c33705bf` | 0 errors, 0 warnings, 32 s | 0 / 0 / 0 |
| `port/RProof/ExtremePairZero.lean` → `RProof/ExtremePairZero.lean` (row 175) | 1772, 1774, 1795, 2552-2621, 4228 | 89 | `40d720dd9df2c061b713f58248111c71` | 0 errors, 0 warnings, 29 s | 0 / 0 / 0 |

Import graph among the new modules: `CV.CarrierFloor` ← `CV.SingletonDi`, `CV.CarrierFloor` ← `RProof.RALedgers`,
{`RProof.RALedgers`, `CV.SingletonDi`} ← `RProof.ExtremePairZero`.  Every declaration of the four modules is proved
(no `sorryAx` anywhere, §4).  Every port line that is not a verbatim Wave1 line is listed in §6 (header, imports, two new
module docstrings, one new declaration); 226 of the 227 declaration statements are byte-identical to Wave1 (the 227th is
the new `CV.carrierSlotFloor`).  Scratch (session scratchpad `…/scratchpad/port/`): `assemble_port.py` (the slicer — the
modules ARE its output), `byteid.py`, `clash.py`, `deviation.py`, `compile_*.log`, `axioms.log`, `porttree/` (compile
copies + probes), `olean/` (the scratch object tree).

## 1. Byte-identity of the deleted §0 copies (Wave1 lines 74-193) against the accepted floor module

Method (`byteid.py`): each declaration of Wave1 §0.1 (keyword line to the next blank line) against the declaration of
the same name in `work/lean/SM/CarrierFloor.lean` (lines 104-370), comments/docstrings stripped, then raw.

| §0 copy (Wave1 line) | accepted (SM/CarrierFloor.lean line) | verdict |
|---|---|---|
| `structure CarrierFloorRData` (84) | 109 | IDENTICAL code; accepted has per-field docstrings, copy has none |
| `def Round` (94) | 135 | IDENTICAL, raw |
| `def junctionTemplate` (98) | 144 | IDENTICAL, raw |
| `structure CarrierFloorAData` (101) | 148 | IDENTICAL code; field docstrings only in the accepted |
| `def AllPosOrOneNeg` (125) | 225 | IDENTICAL, raw |
| `def UniformOrOneDissent` (129) | 231 | IDENTICAL, raw |
| `def PolygonDiagram.reverse` (132) | 236 | IDENTICAL, raw |
| `def tangencySet` (135) | 241 | IDENTICAL, raw |
| `def CrossesPositively` (139) | 248 | IDENTICAL, raw |
| `def TangencyCount` (143) | 255 | IDENTICAL, raw |
| `def BClaim` (148) | 266 | IDENTICAL, raw |
| `structure CarrierFloorBData` (154) | 279 | IDENTICAL, raw |
| `structure CarrierFloorCHyp` (159) | 291 | IDENTICAL code; field docstrings only in the accepted |
| `def zZeroPart` (168) | 328 | IDENTICAL, raw |
| `theorem coeffAt_zZeroPart_zero` (171) | 331 | IDENTICAL, raw (statement and proof) |
| `structure CarrierFloorCData` (174) | 339 | IDENTICAL code; field docstrings only in the accepted |
| `structure CarrierFloorData` (180) | 363 | IDENTICAL, raw |
| `theorem cf_thm_carrierfloor : CarrierFloorData` (188, `by sorry`) | `SM/CarrierFloorRows.lean:10`, `:= cf_thm_carrierfloor_of_bound transverseFrontBound` | statement IDENTICAL; body: placeholder replaced by the accepted proof |

**Verdict: every deleted copy is byte-identical to the accepted declaration** (the only differences are the accepted
file's `/-- … -/` field docstrings, absent from the copies — no binder, name, type or proof differs).  The surrounding
`namespace SM / open Link / open scoped ContDiff / noncomputable section / open Classical` frame is the accepted file's
too.  Nothing to stop on.  Also deleted, NOT copies: §0.2's corner-lane `CS7Data`, `CSoftData` and the placeholders
`thm_C_S7`, `thm_C_soft` (rows 110/112, not yet ported — not needed by rows 155/165/175 or the ledgers), and §5's
`cor_C_inherits` placeholder with `CInheritsData` (§7 below).  The port modules import `SM.CarrierFloorRows` (which
imports `SM.CarrierFloor`) instead.

## 2. Module contents

### 2.1 `CV/CarrierFloor.lean` — row 155 CV:thm:carrierfloor
Imports: `SM.CarrierFloorRows`, `CV.Rounding`, `CV.Curl`, `CV.UniformRot`, `CV.GroupedKnot`, `CV.Axioms` (Wave1's CV
imports minus `CV.ChamberInvRow` (only `cvt_chamberInvII` needs it), `CV.FullTwist`/`CV.HomflyRows` (RA units);
`CV.Curl`/`CV.Axioms` inherited from Wave1, possibly redundant).  Body = Wave1 231-700 verbatim: the §1 heading,
`namespace CV`, `open SM SM.Link SM.Carrier SM.GeoCarrier`, `open scoped ContDiff`, `noncomputable section`,
`open Classical`; `AllPosOrOneNegCV`, `UniformOrOneDissentCV`, `uniformOrOneDissentCV_iff_sm`; `CarrierFloorRData`,
`Rnd`, `CarrierFloorAData`, `BClaimCV`, `CarrierFloorBData`, `CarrierFloorCHyp`, `CarrierFloorCHyp.toSM`,
`CarrierFloorCData`, `cvt_homfly_ne_zero`, `CarrierFloorCData.floor_z0`, `CarrierFloorDData`, `CarrierFloorData`;
§1.1 `cvt_one_le_rotAbs_of_alt`, `cvt_mindegAZ_one`, `carrierfloor_D`; §1.2 `carrierfloor_R_of_sm`,
`carrierfloor_A_of_sm`, `rotAbs_intCast_real`, `carrierfloor_B_of_sm`, `carrierfloor_C_of_sm`, `carrierfloor_of_sm`,
**`carrierfloor`**; §1.3 `CarrierSlotFloor`, `cvt_groupedPoly_ne_zero`, `cvt_groupedPoly_inSupportM`,
`CarrierSlotFloor.coeff_zero`, `cvtS_carrierPolygon_turn_ne`, `cvtS_carrierFloorCHyp`, `cvtS_carrierR_real`,
`carrier_slot_floor_of_C`; then the NEW `carrierSlotFloor` (§6), `end`, `end CV`.  34 declarations.

### 2.2 `CV/SingletonDi.lean` — row 165 CV:singleton_D_i
Imports: `CV.CarrierFloor`, `CV.PieceHomflyTransport` (`homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`),
`SM.ZeroRotationSeed` (`principalAngle_swap`) — the last two reached Wave1 through `CV.ChamberInvRow` and the §5 SM
imports; without them two `unknown identifier` errors.  Body = Wave1 241-247 (the same namespace/section opening) +
702-1763 verbatim: `SingletonPieceOn`, `SingletonDiData`, `cvt_omega1_eq_zero_of_gap`, `SingletonDiData.of_degree_gap`,
`SingletonSplitData`, `singleton_D_i_of`; `section Cvt165sPattern` (6 helpers); `section Cvt165s` with
`attribute [local instance high] Classical.propDecidable`, `cvt165s_insert_eq` and the nine sub-sections (Graph, Pieces,
Owner, Products, Homfly, SplitAlgebra, Rot, DaughterPattern, SplitRot — 65 helpers); the leaf `cvt_singleton_split`;
**`singleton_D_i`**; `end`, `end CV`.  79 declarations.  **Instance situation** (checked with `#synth` on the compiled
module): the module does not import `RProof`, so `DecidableEq (Crossing P)` resolves to
`fun a b => Classical.propDecidable (a = b)` (with `RProof.X1Rows` imported it is `RProof.instDecidableEqCrossing`).
Hence `insert c S` in `SingletonSplitData` is now elaborated with the library's classical instance (Wave1: the RProof
instance — same text, different term), `cvt165s_insert_eq c S` is an identity `insert c S = insert c S` and the
`rw` in the leaf is a trivial rewrite; the `attribute [local instance high]` section is now redundant.  Both kept
verbatim as instructed.  No downstream module consumes `SingletonSplitData`; `SingletonDiData` contains no `insert`.

### 2.3 `RProof/RALedgers.lean` — library material (no row)
Imports: `RProof.X1Rows`, `RProof.X1Rows2`, `RProof.GenericTransport`, `CV.ChamberInvRow`, `CV.FullTwist`,
`CV.HomflyRows`, `CV.CarrierFloor`, `Bridge.SmR`.  Body verbatim: `namespace RProof`, `open SM SM.GeoCarrier`,
`RowShape`, `rowShape_170/172/173`, `variable {n : ℕ} [NeZero n]` (1772-1795); U-174 (1797-2536: `section GSC` …
`gsc_ledger`, `gsc_generic_selected_of_moves`; 33 decls); U-176 (2622-3470: `section EST` … `est_ledger`,
`est_extreme_transport_of`, `est_switch_writhe`, `end EST`; 38 decls); U-177 (3485-4191: `section ESC` …
`esc_ledger`, `end ESC`; 31 decls); `cvt_chamberInvII`, `cv_R_of_rows` (4206-4218); `end RProof`;
`namespace Bridge`, `sm_R_of_rows` (4239-4244), `end Bridge`.  109 declarations.  NOT ported (still unproved or
depending on an unproved row): `generic_selected` (2538-2550), `extreme_transport` (3472-3483), `extreme_selected`
(4193-4204), `cv_R` (4220-4226), `Bridge.sm_R` (4234-4237).  `cv_R_of_rows` and `sm_R_of_rows` take the four rows as
hypotheses and are included, PROVED.

### 2.4 `RProof/ExtremePairZero.lean` — row 175 R:extreme_pair_zero
Imports: `RProof.RALedgers` (for `RowShape`), `CV.SingletonDi`.  Body verbatim: `namespace RProof`,
`open SM SM.GeoCarrier`, `variable {n : ℕ} [NeZero n]` (1772/1774/1795), then 2552-2621: `cvt_exists_owner`,
`cvt175_exists_third`, `cvt_pair_row_zero_of_singleton`, `extreme_pair_zero_of_singleton`, **`extreme_pair_zero`**;
`end RProof`.  5 declarations.

## 3. The row theorems (exact text; statements byte-identical to Wave1)

Row 155 (Wave1 576; `CV/CarrierFloor.lean`):
```lean
theorem carrierfloor : CarrierFloorData := carrierfloor_of_sm SM.cf_thm_carrierfloor
```
(`SM.cf_thm_carrierfloor : SM.CarrierFloorData` from `SM/CarrierFloorRows.lean`; the composition is the one §1 and §5
intend — `carrierfloor_of_sm` bridges (R)(A)(B)(C) and supplies the proved (D).)  Also, NEW (the floor argument of
rows 165/174/176/177; field name `clauseC : SM.CarrierFloorData → SM.CarrierFloorCData` verified):
```lean
theorem carrierSlotFloor : CarrierSlotFloor := carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC
```
Row 165 (Wave1 1762-1763; `CV/SingletonDi.lean`), body kept verbatim:
```lean
theorem singleton_D_i : SingletonDiData :=
  singleton_D_i_of cvt_singleton_split (carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC)
```
(`singleton_D_i_of (hsplit : SingletonSplitData) (hfloor : CarrierSlotFloor)`, this order; the task's form
`singleton_D_i_of cvt_singleton_split CV.carrierSlotFloor` is the same term and typechecks — probed with an `example`.)
Row 175 (Wave1 2612-2621; `RProof/ExtremePairZero.lean`), under `variable {n : ℕ} [NeZero n]`:
```lean
theorem extreme_pair_zero (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremePairZeroData hn E e f g δ :=
  extreme_pair_zero_of_singleton CV.singleton_D_i n hn E e f g h3 h4e h4f h4g hE
```
(`RowShape @ExtremePairZeroData` form; `#check` confirms the elaborated signature matches the sibling rows.)

## 4. Axioms (`#print axioms` on the scratch importer `porttree/Axioms.lean`; `axioms.log`)

| declaration(s) | axioms |
|---|---|
| **`CV.carrierfloor`, `CV.singleton_D_i`, `RProof.extreme_pair_zero`**, `CV.carrierSlotFloor` | `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact` |
| `SM.cf_thm_carrierfloor` (accepted; for attribution) | the same nine — the three beyond Wave1's set (`lit_homfly_descent`, `ng_finite_word`, `src_contact`) enter through the floor row's row-94 discharge, as PREREVIEW FR-R-178-2 predicted |
| `CV.carrierfloor_of_sm`, `CV.carrier_slot_floor_of_C`, `CV.CarrierSlotFloor.coeff_zero`, `CV.cvt_singleton_split`, `CV.singleton_D_i_of`, `RProof.rowShape_170`, `RProof.rowShape_173`, `RProof.gsc_ledger`, `RProof.gsc_generic_selected_of_moves`, `RProof.est_ledger`, `RProof.est_extreme_transport_of`, `RProof.esc_ledger`, `RProof.esc_couple`, `RProof.cvt_chamberInvII`, `RProof.cv_R_of_rows`, `Bridge.sm_R_of_rows` | `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` |
| `CV.carrierfloor_D`, `RProof.cvt_pair_row_zero_of_singleton`, `RProof.extreme_pair_zero_of_singleton`, `RProof.rowShape_172` | `propext, Classical.choice, Quot.sound, SM.lit_homfly` |
| `RProof.gsc_wallData_of_endpoint` | `propext, Classical.choice, Quot.sound` |

No `sorryAx` in any declaration of the four modules; every axiom is in `work/lean/axiom-policy.json` (`standard` +
`literature`).  The library declarations keep exactly the sets WAVE1_ASSEMBLY_REPORT.md §4 recorded.

## 5. Clash scan (`clash.py`)

227 declarations in the four modules (34 + 79 + 109 + 5), no duplicate `(namespace, name)` among them.
`grep -rnwE` of all 227 bare names over `work/lean/{SM,CV,RProof,Bridge}/**/*.lean`: 82 lines mention 9 names.
Namespace-aware classification of the hits:
* **same-namespace declaration clashes: 0**;
* different-namespace declarations with the same bare name: 6 — `SM.CarrierFloorData / RData / AData / BData / CHyp /
  CData` (SM/CarrierFloor.lean) vs the CV bundles of the same names — the F6 design (the CV clause bundles mirror
  SM's); they coexist as they did in Wave1 (§1 is written inside `namespace CV` with `open SM`, and compiles);
* the remaining hits are prose/docstring mentions (`carrierfloor` 37, `CarrierFloorCHyp` 15, …, `extreme_pair_zero`
  4 and `singleton_D_i` 2 in RProof/X1Rows.lean's docstrings).
`work/lean/lean-declarations.json`: of the 227 full names only `RProof.extreme_pair_zero` occurs — as the registry's
own PENDING target entry (`module: ""`), not an existing declaration.  Pending entries the executor fills at port:
`CV:thm:carrierfloor` (declaration and module empty → `CV.carrierfloor`, `CV.CarrierFloor`), `CV:singleton_D_i`
(→ `CV.singleton_D_i`, `CV.SingletonDi`), `R:extreme_pair_zero` (→ module `RProof.ExtremePairZero`).

## 6. Deviations from verbatim (complete: every non-blank port line absent from Wave1, `deviation.py`)

| module | deviation | justification |
|---|---|---|
| all four | line 1: the `-- Ported <HH:MM>Z 2026-09-15 …` header (template; the executor fills the time and may trim) | executor format |
| all four | the import block | §0 replaced by `SM.CarrierFloorRows`; per-module minimal imports (each missing import produced a compile error, see §2) |
| `CV/CarrierFloor` | `end` / `end CV` moved up from Wave1 1765/1767 (verbatim lines) | the module ends after §1 |
| `CV/CarrierFloor` | NEW lines 480-482: docstring + `theorem carrierSlotFloor : CarrierSlotFloor := carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC` | requested by the port task; the only statement not in Wave1 |
| `CV/SingletonDi` | Wave1 241-247 (namespace/section opening) and 1765/1767 repeated around the §2 block | §2 lived inside §1's namespace/section in Wave1 |
| `RProof/RALedgers` | new module docstring (lines 11-20); Wave1's §3 heading 1769-1770 and §4 heading 4230 omitted | those headings name the row theorems, which are not in this module |
| `RProof/RALedgers` | omitted Wave1 2538-2550, 3472-3483, 4193-4204, 4220-4226, 4234-4237 (rows 174/176/177/178/183) | still `sorry` / depend on it — per the task |
| `RProof/ExtremePairZero` | new module docstring (lines 5-9); `namespace RProof` / `open SM SM.GeoCarrier` / `variable {n : ℕ} [NeZero n]` / `end RProof` repeated (verbatim Wave1 lines) | module frame |

No declaration statement, docstring or proof of Wave1 was reworded (no forbidden string occurred in the ported ranges;
the only `sorry` hits were in my own draft header, reworded before the check).  Prose that says "declared and mapped
only when row 99 lands" (docstrings of `carrierfloor`, `singleton_D_i`) is now historical; left verbatim.

## 7. §5 (row 184 SM:corner_laws_and_soft) — what is portable now, what must wait (NOT ported, report only)

| declaration (Wave1 line) | depends on | verdict |
|---|---|---|
| `def CuspLawC` (4268) | accepted SM (`WallGerm`, `CuspAt`, `G1`, `CuspCase`, `cornerStateSum`, `deleteVertex`) | portable now as library, but OWNED by the comparison lane (byte-identical copy in comparison/Statements_FINAL.lean §4 → their `SM/CInherits.lean`); port ONCE, from there |
| `def ReversalLawC` (4282) | accepted `generic_reversal`, `cornerStateSum` | same: portable now, comparison lane owns it |
| `def TrianglesC` (4292) | accepted `star_generic_law`, `cornerStateSum` | same: portable now, comparison lane owns it |
| `def CyclicLawC` (4287) | accepted `genericShift`, `cornerStateSum` (discharged by `cornerStateSum_genericShift`) | portable now; "stays the tail's own" (comparison PLAN_FINAL §6.3) — could go with row 184's module or a small `SM/CornerLawsC.lean` |
| `structure CInheritsData` (4301) | `CS7Data`, `CSoftData` (corner §0 copies), `hyp_R`, the three Props | MUST WAIT: comparison PLAN_FINAL §6.1 REPLACES it (adds `root_values`; retypes `vertex_edge_law`, `triple_law`, `soft_theorem`); it lands as the comparison lane's `SM/CInherits.lean` |
| `theorem cor_C_inherits` (4331, placeholder) | row 128 | MUST WAIT (comparison lane's row) |
| `structure CornerLawsAndSoftData` (4337) | `CChamberData`, `CSilentData`, `CS3Data`, `CS5Data`, `hyp_R` (accepted) + `CS7Data`, `CSoftData` (corner lane's bundles — §0 copies here) + the four Props | MUST WAIT for the corner lane's port of rows 110/112 (its field types are the corner module's structures; porting the copies would duplicate them) |
| `theorem corner_laws_and_soft_of` (4367) | the above + `hinh.cusp_law / reversal_law / triangles` (types unchanged by the comparison edits, their §6.3) | MUST WAIT for both the corner (110/112) and comparison (128) ports; its body needs no change |
| `theorem corner_laws_and_soft` (4383) | `Bridge.sm_R` (rows 174/176/177 open), `thm_C_S7`, `thm_C_soft`, `cor_C_inherits` | MUST WAIT (the final target) |

Recommendation: port nothing of §5 now; when the corner and comparison modules land, `CyclicLawC`,
`CornerLawsAndSoftData`, `corner_laws_and_soft_of` port together as `SM/CornerLawsAndSoft.lean` importing
`SM.CInherits` (comparison) and the corner rows module, with `corner_laws_and_soft` added once `Bridge.sm_R` exists.

## 8. Notes and decisions for the executor

1. **`RowShape` placement.** It is in `RProof/RALedgers.lean` (with `rowShape_170/172/173`), so the row-175 module
   imports `RProof.RALedgers` (2372 lines; import-only cost).  Alternative if a lighter row 175 is preferred: move
   `RowShape` + `rowShape_170/172/173` (Wave1 1776-1793) into `RProof/ExtremePairZero.lean` and let `RALedgers`
   import it — a pure relocation, no text change.  PLAN_FINAL §6 (U-178) had `RowShape` going with `cv_R`.
2. **`CV.carrierSlotFloor`** (new, requested).  Differs from the Prop `CV.CarrierSlotFloor` only by case; the
   closing lines of rows 174/176/177 in WAVE1_ASSEMBLY_REPORT.md §7.1 can use it in place of
   `carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC`.  Drop it if a new name is unwanted (nothing here uses it).
3. **Row 165's body** is Wave1's verbatim term; `singleton_D_i_of cvt_singleton_split CV.carrierSlotFloor` is
   interchangeable (§3).
4. **DecidableEq** (§2.2): the CV modules do not import `RProof`; the classical instance now governs `insert c S`
   in `SingletonSplitData`; the section attribute and `cvt165s_insert_eq` are kept verbatim though redundant.  Any
   future `RProof` consumer of `SingletonSplitData` (none today) would meet the classical instance — the library's
   convention, so this removes rather than creates a mismatch.
5. **Compile recipe used** (true module semantics without touching `work/lean`): copy the port files into a scratch
   tree `T/{CV,RProof}/`, symlink every file of `work/lean/.lake/build/lib/lean/{CV,RProof}/` into `O/{CV,RProof}/`,
   then from `work/lean`: `lake env sh -c 'LEAN_PATH="O:$LEAN_PATH" lean --root=T -o O/CV/CarrierFloor.olean
   T/CV/CarrierFloor.lean'` and likewise in dependency order (`lean -o` refuses inputs outside a root, and Lean
   resolves all `CV.*` modules in the first `LEAN_PATH` entry that has a `CV/` directory — hence the symlinks).  After
   the executor copies the files to `work/lean/CV/…`, `RProof/…`, the ordinary `lake build` suffices (globs `CV.+`,
   `RProof.+`).
6. `lean-declarations.json` entries to fill: `CV:thm:carrierfloor`, `CV:singleton_D_i`, `R:extreme_pair_zero` (§5).
7. Header time placeholder `<HH:MM>Z` in line 1 of each module.
