# PLAN FINAL — CV/R tail (rows 155, 165, 174–178, 183, 184): judge's decision, fixed statements, routes, units

Judge, 2026-09-15 (≈15:40Z / 11:40am ET), from `work/drafts/cvtail/DESIGN_A.md` + `Sketch_A.lean`
(Architect A, fidelity-first) and `DESIGN_B.md` + `Sketch_B.lean` (Architect B, feasibility/assembly).
Both sketches typecheck (`lake env lean`, exit 0; A: 2 `sorry`, B: 14 `sorry`, all proof leaves or
fixed-name placeholders).  Inputs re-read by the judge: d3_floor.tex 736–830, 990–1012;
d6_vertexedge.tex 1155–1170, 2640–2700, 2860–2950; EXECUTION.json, R_ASSEMBLY_SPEC.md, TARGETS.md,
PROOF_PLAN.md, OPEN_WORK.md, BRIDGE.md §3, lean/axiom-policy.json; the four RA files of rows 174–177;
RProof/{X1Rows,X1Rows2,Cores,GenericTransport}.lean, Bridge/SmR.lean, SM/HypR.lean, SM/ALawful.lean,
CV/{X1,Rounding,Rotation,RotationSmooth,Setup,UniformRot,Carriers,CarriersLemma,GroupedKnot,Axioms}.lean,
SM/{LinkLaurentRing,PolynomialBlock,GeoPositiveLift,GeoCornerPolygon}.lean; and — decisive, because both
designs were written before they existed — the sibling lanes' FINAL statements
`work/drafts/floor/Statements_FINAL.lean` (+ PLAN_FINAL.md, 14:47–14:55Z),
`work/drafts/corner/Statements_FINAL.lean` (15:17Z), `work/drafts/contact/Statements_FINAL.lean`, and the
AUTHOR_NOTES entries D-GAP2, D-GAP2-2b, row-91 acceptance (14:25Z), the floor/contact panel decisions
(14:58Z, 15:03Z).

Deliverables: this file and `work/drafts/cvtail/Statements_FINAL.lean` (992 lines;
`cd work/lean && lake env lean ../drafts/cvtail/Statements_FINAL.lean` → 0 errors, exactly 10 `sorry`:
4 sibling-lane placeholders, 3 leaves of this lane, the 3 fixed-name RA rows 174/176/177; `#print axioms`
of every proved assembly = standard + `SM.lit_homfly` (+ `SM.lp_lm`, `SM.lp_lm_uniqueness` where `P = homfly`
is used)).  Nothing written under work/lean.

## 0. Verdict: **B wins** (fidelity 8 / feasibility 8 / reuse 8.5 = 24.5 vs A 7 / 6 / 8 = 21), with A's grafts

| aspect | A | B | decision |
|---|---|---|---|
| SM row-99 interface assumed | gap2 memo shapes (4-field (A), record-of-`L` (B), 5-field `CarrierFloorCHyp`, `floor_support`) | floor lane's Sketch_A shapes = the floor lane's FINAL up to two grafted names | **B**; the FINAL copies the floor lane's Statements_FINAL §2–§6 verbatim (`tangencySet`, `CrossesPositively` included) |
| clause (B) | record of `L` itself, positive crossing in all four alternatives | normalised-orientation disjunction, reversal branch on SM objects | **B**: A's (B) is FALSE for an all-negative `L` (every junction lift decreases, the tangent crosses `u` in the negative sense; `R ≥ 1` so tangencies exist) — the floor judge's FR-FL-B1; A's `carrierfloor_B_of_sm` is a proof from a false SM bundle |
| clause (C) hypothesis class | CV vocabulary: `Diagrammatic L` parameter + 5 fields | SM's `CarrierFloorCHyp (polyComp L hreg) X` reused | **A, grafted**: `CV.CarrierFloorCHyp L hreg X` with a `diagrammatic : Diagrammatic L` field (the CV text says the double-point list "repeats the shared-image clause of def:diagrammatic"); bridge `toSM` PROVED (`single_generic_of_diagrammatic`, `regular_iff_sm`, `principalTurn_eq_sm` is `rfl`) |
| clause (C) `f_D` | support form only | floor lane's `zZeroPart` form | **B** (F6: the CV clause is the SM clause; FR-FL-C3) + A's support form as the PROVED corollary `floor_z0` |
| clause (C) conclusion | ℤ, `rotAbs` | ℤ, `rotAbs` | equal |
| clause (D) | includes the "so that" as a conclusion conjunct; literal `1 − w − R ≤ 0` | `slot ≤ 0`, no commentary conjunct | **B's fields, A's literal display** (`1 - groupedWrithe - carrierR ≤ 0`); the "so that" is commentary on the hypothesis (FR-CV-155-7) |
| clause (R) polygon field | `rot (reversal L) hL' = -rot L hL` with both regularity proofs | `rot (reversal L) (regular_reversal' hL) = -rot L hL` | **floor-final shape grafted**: the diagram-carrying field (`X.Γ = single (polyComp L hL) → X.reverse.Γ = single (polyComp L hL).reverse ∧ rot … = −rot …`) with A's two proofs; PROVED from SM's field + `rot_reversal` |
| 155 bridges | (R)(A)(B)(C) all PROVED (against the stale/false memo) | (R) PROVED, (A)(B)(C) `sorry` with hints | **judge**: all four PROVED against the floor lane's FINAL shapes (`rest_is_L` is the accepted `CV.rounding.a`) |
| consumer interface of (C)+(D) | none — 165 reads `CarrierFloorCData` directly and would need `Diagrammatic (geoCornerPolygon …)` (not library material) | `CarrierSlotFloor` (support form) from SM's (C) | **B, strengthened**: `CarrierSlotFloor := slot ≤ mindegAZ groupedPoly` (the printed eq:floor in def:X1's symbols); support form = PROVED corollary `coeff_zero` (needs `groupedPoly ≠ 0`, PROVED) |
| 165 statement | two-field bundle (`degree_gap`, `factor_zero` = the printed "so") | one `Prop` with `SingletonPieceOn` | **A's bundle with B's `SingletonPieceOn`** |
| 165 route | geo-layer split + cor:groupedknot (B) + knot parity + (C)/(D) per loop, one 1.4k unit | `SingletonSplitData` interface + `cvt_coeff_zero_mul_floor` (z⁰ rows multiply) + `CarrierSlotFloor`; "shared with the corner lane" | **B's interface, judge's algebra**: `mindegAZ_mul` on the two nonzero factors (the corner lane's FR-CC-3 route) — `singleton_D_i_of` PROVED, no algebra leaf.  The corner lane's split (`sg_daughters_*`) is on SM's `Component`/`IsDecomposition` — NOT consumable here (A's FR-CV-165-3 was right); U-SPLIT is this lane's |
| 175 | bare leaf | PRE fields assembled, `wind = 0` branch, `cvt_exists_owner` leaf (stated WITHOUT `S ∈ Ind`) | **B**, judge's repair: `cvt_exists_owner` takes `hS` and is PROVED (`pieceOwner`, `mem_piecesOn_iff`); the remaining leaf is the `pair_row_zero` field given `ParityData` |
| 174/176/177 | "not this lane", ~1000 lines each | consumption lists per row, 3–8k lines each, move-interface-first mitigation | **B** (the G11 precedent — one RIII site, 11k lines — makes A's estimate an order of magnitude low) |
| 178/183 | `RowShape` + `cv_R_of_rows` PROVED | expanded shape + fixed names declared, `cv_R`, `sm_R` PROVED | **A's `RowShape`** (compact) + **B's fixed-name declarations** |
| 184 shape | flat 11 fields following TARGETS' coverage list, own Props for the pending rows | 8 fields nesting `CS7Data`, `CInheritsData`, `CSoftData` (chamber/silent/flat/vertex-edge/triple/soft appear twice) | **A's flat list**, with the corner lane's FINAL `CS7Data`/`CSoftData` as the field types (both designs had `∃`-genericity; the corner final has `∀ h₁ h₂` / `∀ hQ`), B's `CInheritsData` as the proposed row-128 bundle, A's `cyclic` discharged now |
| axiom disclosure | — | `SM.lit_homfly_descent` enters via 155 (C) (D-GAP2-2b) | **B** (recorded, §3 FR-R-178-2) |
| sketch evidence | 666 lines, 2 `sorry`; assemblies proved | 710 lines, 14 `sorry`; more of the consumer side proved | both adequate; B's skeleton is the port-ready one |

Reasons in one paragraph.  A read the texts more carefully (its FR list is the better one and is kept
almost verbatim) but built on a stale interface whose (B) is false and did not see that its 165 route
needs `Diagrammatic` of a carrier's corner polygon, which the library does not have; it also scoped the
three RA rows out with estimates that ignore the lane's own precedent.  B built on the shapes that
became the floor lane's ruling, factored the one corollary every consumer reads, and assembled 165, 175,
178, 183, 184 so that the remaining work is exactly three geometric leaves and three RA rows; its
mistakes (the shared-split assumption, `cvt_exists_owner` without `hS`, the `∃`-genericity shapes of
CS7/CSoft) are repaired below.

## 1. Chosen statements (Statements_FINAL.lean; exact text there)

### Row 155 — `CV.carrierfloor : CV.CarrierFloorData` (§1; five clause bundles)
* `CV.CarrierFloorRData` (6 fields): `homfly_reverse`, `knot_reverse`, `sign_reverse`, `writhe_reverse`,
  `rot_reverse_polygon` (diagram with shadow `single (polyComp L hL)`; reversed shadow; `rot (reversal L) hL' = -rot L hL`),
  `rot_reverse_curve` (`rotCurve γ.reverse = -rotCurve γ`).
* `CV.CarrierFloorAData` (6 fields = floor final at `polyComp L hreg`, `D.toPolygonDiagram hL`, `Rnd := roundingRecord`):
  `one_record` (`Rnd … = SM.Round …`), `one_curve`, `one_diagram`, `junction_determined`, `length_determined`, `rest_is_L`
  (the accepted `CV.rounding.a` shape).
* `CV.CarrierFloorBData.tangencies`: `UniformOrOneDissentCV L → (AllPosOrOneNegCV L ∧ BClaimCV hL hreg hturn D) ∨
  (AllPosOrOneNegCV (reversal L) ∧ SM.BClaim (polyComp L hreg).reverse (D.toPolygonDiagram hL).reverse)`,
  `BClaimCV` = `∃ u ε₁, |u| = 1, 0 < ε₁ ≤ clearance L hreg, ∀ ε ∈ (0, ε₁), TangencyCount (Rnd …) (±u) (rotAbs L hreg)`.
* `CV.CarrierFloorCHyp L hreg X` (6 fields + `hreg`): `shadow`, `positive`, `diagrammatic`, `turn_ne`, `turn_lt_pi`,
  `alternative`; `toSM` PROVED.  `CV.CarrierFloorCData`: `floor : 1 - X.writhe - rotAbs ≤ mindegAZ (homfly X)`,
  `floor_zZero` (on `SM.zZeroPart (homfly X) ≠ 0`); corollary `floor_z0` (support form) PROVED.
* `CV.CarrierFloorDData.floor_D`: `piecesOn = ∅ → turns ≠ 0 → UniformOrOneDissentCV (geoCornerPolygon …) →
  1 ≤ carrierR ∧ mindegAZ groupedPoly = 0 ∧ 1 - groupedWrithe - carrierR ≤ 0` — PROVED (`carrierfloor_D`).
* Bridges `carrierfloor_R/A/B/C_of_sm`, `carrierfloor_of_sm : SM.CarrierFloorData → CV.CarrierFloorData` — all PROVED.
  Row: `CV.carrierfloor := carrierfloor_of_sm SM.cf_thm_carrierfloor` (declared and mapped only when row 99 lands).
* Library corollary `CV.CarrierSlotFloor : Prop` (= `∀ hn hG hS q, UniformOrOneDissentCV (geoCornerPolygon …) →
  slot ≤ mindegAZ groupedPoly`), `CarrierSlotFloor.coeff_zero` PROVED, `carrier_slot_floor_of_C : SM.CarrierFloorCData →
  CarrierSlotFloor` LEAF (U-SLOT).

### Row 165 — `CV.singleton_D_i : CV.SingletonDiData` (§2)
`SingletonPieceOn hP S q c` (`mem_U`, `labels = {c}`, `owner : pieceOf c ∈ piecesOn q`); bundle fields `degree_gap`
(`∀ d, coeffAt d 0 groupedPoly ≠ 0 → slot + 2 ≤ d`) and `factor_zero` (`Omega1 = 0`); `of_degree_gap` PROVED;
`SingletonSplitData` (interface of U-SPLIT); `singleton_D_i_of : SingletonSplitData → CarrierSlotFloor → SingletonDiData`
PROVED; row `singleton_D_i := singleton_D_i_of cvt_singleton_split (carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC)`.

### Rows 174–178 (§3) — FIXED names, FIXED statements
`RProof.generic_selected / extreme_pair_zero / extreme_transport / extreme_selected` in the accepted row shape
`∀ (hn) (E) (e f g) h3 h4e h4f h4g, E.IsSimpleRIII … → ∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ <Bundle> hn E e f g δ` with the accepted
bundles of RProof/X1Rows.lean (`GenericSelectedData` :1434, `ExtremePairZeroData` :1483, `ExtremeTransportData` :1628,
`ExtremeSelectedData` :1757); `RowShape` abbreviates the shape; `rowShape_170/172/173` the accepted rows;
`cv_R_of_rows` PROVED; `RProof.cv_R : CV.hyp_R := cv_R_of_rows …` (declared).  Row 175 is PROVED modulo the leaf
`cvt_pair_row_zero_of_singleton` (`extreme_pair_zero := extreme_pair_zero_of_singleton CV.singleton_D_i …`).

### Row 183 (§4) — `Bridge.sm_R : SM.hyp_R := SM.sm_R_of_cv_R RProof.cv_R` (declared; `sm_R_of_rows` PROVED).

### Row 184 (§5) — `SM.corner_laws_and_soft : SM.CornerLawsAndSoftData`
Flat structure, one field per item of TARGETS' "Required coverage": `chamber : CChamberData`, `silent : CSilentData`,
`flat : CS3Data`, `vertex_edge : CS7Data` (corner FINAL), `triple : hyp_R`, `cusp : CuspLawC`, `empty_cusp : CS5Data`,
`soft : CSoftData` (corner FINAL), `reversal : ReversalLawC`, `cyclic : CyclicLawC`, `triangles : TrianglesC`.
`CInheritsData` = proposed row-128 bundle (ALawfulData with `cornerStateSum`, minus `root_independent` and the
"every induced root" sub-clause; `vertex_edge_law : CS7Data`, `triple_law : hyp_R`, `soft_theorem : CSoftData`,
`cusp_law : CuspLawC`, `reversal_law : ReversalLawC`, `triangles : TrianglesC`).
`corner_laws_and_soft_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData) (hinh : CInheritsData)` PROVED
(`prop_C_chamber`, `prop_C_silent`, `thm_C_S3`, `thm_C_S5`, `cornerStateSum_genericShift`);
row `:= corner_laws_and_soft_of Bridge.sm_R thm_C_S7 thm_C_soft (cor_C_inherits Bridge.sm_R)`.

## 2. Model decisions (judge's)

D-CVT-1 (interfaces are the sibling lanes' FINAL text).  §0 of Statements_FINAL is a verbatim copy of the floor lane's
`CarrierFloor{R,A,B}Data`, `CarrierFloorCHyp`, `CarrierFloorCData`, `CarrierFloorData` and their vocabulary, and of the
corner lane's `CS7Data`, `CSoftData`; the placeholders `SM.cf_thm_carrierfloor`, `SM.thm_C_S7`, `SM.thm_C_soft`,
`SM.cor_C_inherits` are deleted when those modules land.  If the floor lane's port renames anything, only §0 and the
cast layer of `carrierfloor_*_of_sm` move; the CV statements do not.
D-CVT-2 (the consumers read SM's (C), not CV's).  `carrier_slot_floor_of_C` consumes `SM.CarrierFloorCData` because the
diagram it applies (C) to is `carrierDiagram` (cor:groupedknot (B)), whose hypotheses arrive as the genericity of
its own shadow, not as `Diagrammatic (geoCornerPolygon …)` (not library material).  Content-equal by F6
(`carrierfloor_C_of_sm`); the CV row 155 is accepted as a row in its own right (the CV:lem:rounding pattern).
D-CVT-3 (165's algebra).  `mindegAZ_mul` on the two nonzero factors (`cvt_groupedPoly_ne_zero`) replaces the printed
z⁰-row bookkeeping (knot parity + `zRow 0` multiplicativity); `cvt_groupedPoly_inSupportM` is kept for the RA units.
D-CVT-4 (`CarrierSlotFloor` is the full floor).  Stated as `slot ≤ mindegAZ groupedPoly` (eq:floor in def:X1 symbols);
the support form the RA texts quote ("no exponent below d_A occurs in f_A") is `coeff_zero`.
D-CVT-5 (184 presentation).  Flat, TARGETS-ordered; the pending rows' identities enter as their lanes' bundles or
as `ALawfulData`-shaped Props; `cyclic` is discharged by the accepted def:C (`cornerStateSum_genericShift`).
D-CVT-6 (fixed-name rows are declared in the FINAL with `sorry`).  Rows 174/176/177 are units of this lane; the file
exercises the exact final shapes of `cv_R`, `sm_R`, `corner_laws_and_soft`.  In work/lean they appear only when
their bodies are complete (no `sorry` rule).

## 3. Fidelity risks — the executor writes these into AUTHOR_NOTES BEFORE the rows are stated

**FR-CV-155-1 (F6 bridge).**  (R)(A)(B)(C) are stated on CV's printed binders (`L : LabelledTuple n`, `hL : Diagrammatic L`,
`hreg : Regular L`, `hturn`, `D : OverUnder (polyComp L hreg)`) and PROVED from the floor lane's SM row-99 bundles by
`carrierfloor_*_of_sm`; the SM shapes are the floor lane's FINAL (D-FL-1).  The two texts differ only in the scoping
sentences "Here rot is as in Definition def:rot", (R)'s knot phrasing, (B)'s "diagrammatic closed polygon", (C)'s
"no generic parent polygon is assumed" commentary.
**FR-CV-155-2 ((R) on knots).**  "Let K be an oriented knot … P_{−K} = P_K": `homfly X.reverse = homfly X` on a
one-component `X` AND `LinkEquiv X X' → homfly X'.reverse = homfly X` ("knot" = `LinkEquiv` class, D2); `P_K` is
CV:def:homfly's `homfly` (`P_eq_homfly`).  The row states the knot case as printed; the library lemma is unconditional
(floor FR-FL-R1).
**FR-CV-155-3 ((R) rotation).**  "rotation number of the underlying plane curve negated": a polygon field carrying the
diagram (shadow `single (polyComp L hL)`, reversed shadow, `CV.rot` negated — the accepted `rot_reversal`) and a
C¹ field (`rotCurve γ.reverse = -rotCurve γ`; `rotCurve` is `γ.rot` by `abbrev`).  Nothing asserts that the reversal of a
CARRIED smooth diagram is carried (no consumer; floor FR-FL-R3).
**FR-CV-155-4 ((A)).**  "one curve and one diagram at those data" = the record IS the named construction (`Rnd … =
SM.Round …`, `rfl`; uniqueness of the FIXED construction, "not uniqueness among all possible smoothings"); the junction
"determined by ε, by the two incident unit directions and by the transition profile" is stated PARAMETRICALLY
(`junction_determined`, stronger than the image form, floor FR-FL-A1; the image form is the floor lane's corollary
`junction_local`); "the arc length ℓ is then determined by the endpoint condition" = `length_determined`; "the rest of
the curve is L itself" = the accepted `CV.rounding.a` (set form ∪ parametric straight parts).
**FR-CV-155-5 ((B), normalised orientation).**  The claim is made for the polygon in the normalised orientation:
for `L` itself when `AllPosOrOneNegCV L`, for `−L` carrying `−D` otherwise (`SM.BClaim (polyComp L hreg).reverse
(D.toPolygonDiagram hL).reverse`).  The literal "record of `L` itself" reading (gap2 memo, Sketch_A) is FALSE for an
all-negative `L` (the tangent crosses `u` in the negative sense).  The reversal branch is on SM's objects because
`OverUnder.reverse` / `Diagrammatic (reversal L)` are not library material; consumers read (C)+(D) only.
"exactly R points" = `Set.ncard` of the FINITE tangency set of the fundamental period (`TangencyCount`); `R = rotAbs L
hreg : ℕ` (CV:def:rot), cast to ℝ; "crosses in the positive sense" = `CrossesPositively` (positive derivative of the
junction lift `θ j`); `ε₁ ≤ ε₀(L)` added so the record exists (floor FR-FL-B2/B3/B4).  (B)'s "exactly one is negative"
omits "and every other is positive" (rem:curlauthor tightened (C) only); with all turns nonzero the two read the same.
**FR-CV-155-6 ((C)).**  Hypotheses one item per printed clause on CV's vocabulary: `shadow`, `positive`, `hreg`
(parameter, "all principal turns existing"), `turn_ne`, `turn_lt_pi`, `diagrammatic : Diagrammatic L` (the double-point /
corner list IS CV:def:diagrammatic, as (C) says), `alternative`; `toSM` shows the class is SM's seven-field class at
`polyComp L hreg`.  Conclusion in ℤ: `1 - X.writhe - (rotAbs L hreg : ℤ) ≤ mindegAZ (homfly X)` (SM's is real with
`|rotationNumber|`; `rotAbs_intCast_real`); `homfly X ≠ 0` (lp:core) so `mindegAZ` is def:adeg's `mindeg_a`; the `f_D`
sentence is the floor lane's `floor_zZero` (`zZeroPart`, FR-FL-C3), the support form the corollary `floor_z0`.
**FR-CV-155-7 ((D)).**  "carrying no residual piece" = `piecesOn … = ∅`; "so that P_{S,L} = 1 and w_{S,L} = 0 by
def:X1's empty conventions" is commentary (the accepted `X1_definition.empty_conventions`), NOT a conclusion; "all its
principal turns are nonzero" on the carrier's CORNER POLYGON `geoCornerPolygon` (CV:def:wind / def:rot; `carrierR` is
`rotAbs` of it), printed but not consumed (uniformrot needs only the sign pattern; kept, unused); the alternative in the
literal reversal form; conclusion `1 ≤ carrierR ∧ mindegAZ groupedPoly = 0 ∧ 1 - groupedWrithe - carrierR ≤ 0` (ℕ / ℤ).
**FR-CV-155-8 (row bundle, D-F11).**  `CV.carrierfloor : CarrierFloorData` is declared and mapped only when all five
clauses are theorems: (D) now, (R)(A)(B) when the floor lane's clause theorems are ported (they are PROVED there
modulo their own leaves), (C) when row 99 (C) lands (← fd:contact row 94 ← row 91, accepted).  Partial acceptance is
not a row.
**FR-CV-155-9 (the consumer corollary).**  `CarrierSlotFloor` is library material, not a row: (C)+(D) in def:X1's symbols
for every uniform / one-dissent carrier of a CV-generic polygon; it consumes SM's (C) (D-CVT-2).
**FR-CV-165-1 (`f_A`, the degree gap).**  `f_A = [z⁰] P_{S,A}` (def:markeddata); "min deg_a f_A ≥ slot + 2" in support form
`∀ d, coeffAt d 0 groupedPoly ≠ 0 → slot + 2 ≤ d` (vacuous when `f_A = 0`, where `Ω₁ = 0` holds anyway); "so the factor
Ω₁(S,A) is zero" the second field (PROVED from the first).  PROOF_PLAN step 5: "requires only the stated degree gap and
zero conclusion" — nothing of (D)(ii)–(v) is stated.
**FR-CV-165-2 (singleton piece carried by A).**  `SingletonPieceOn`: `c ∈ U(S)`, `pieceLabels (pieceOf c) = {c}`, `pieceOf c
∈ piecesOn q` (def:X1's "assigned to L by lem:carriers (iv)") — the shape the accepted
`ExtremePairZeroData.third_singleton_piece` produces; "uniform carrier" = CV:def:wind's `CarrierUniform`.
**FR-CV-165-3 (dependency column).**  claims.py lists cb:singleton (row 103) as a dependency of 165; the corner lane's
row 103 and its split leaves (`sg_daughters_products/rotation`) are on SM's `Component hn hP S` / `IsDecomposition`
(`hP : SM.Generic P`); `CV.Generic` is larger (`CV.generic_of_sm`), so nothing of row 103 is consumable on 165's domain.
Row 103 is the TEMPLATE; the split is this lane's U-SPLIT on the geo layer (`GeoComponent`, `piecesOn`, `groupedPoly`).
**FR-CV-165-4 (algebra route).**  The printed proof multiplies z⁰ rows via knot parity; the Lean route adds the FULL
floors of the two nonzero factors (`mindegAZ_mul`) and reads the coefficient below the sum (the corner lane's FR-CC-3).
Proof-route difference only; `cvt_groupedPoly_inSupportM` records knot parity for the RA units.
**FR-R-174..177 (frozen).**  The bundles are accepted text (statement panel 06:35Z; readings rlane2/NOTES_FINAL.md
§6–§13): fixed labels `a = x_ef, b = x_eg, c = x_fg` with canonical + relabelled branches; sides named by local graphs;
`hn` explicit; `T_ν(J) = rowTerm` (absent rows `0`).  Row 175's `pair_row_zero` is the only field of 174–177 whose proof
does not need 155 (C): it needs 165 (its presuppositions are the accepted `PRE_175_*`).
**FR-R-178-1.**  `RProof.cv_R : CV.hyp_R` (R6 all-parameters form); the assembly IS the accepted
`hyp_R_of_near_of_chamberinv (A2_cvRNear_of_rows …) (chamberinv_ii …)`; R_ASSEMBLY_SPEC "Finally sum the proved
identities (4) over the same finite outside-support set in (3) … giving exactly CV ax:R"; the domain is `E.IsSimpleRIII`
(CV:def:event, "its entire printed simple/transversal forced-bundle domain", OPEN_WORK 4).
**FR-R-178-2 (axiom footprint).**  `RProof.cv_R`, `Bridge.sm_R`, `SM.corner_laws_and_soft` will depend on
`SM.lit_homfly_descent` (through 155 (C) ← fd:contact ← row 91), authorised as lit:homfly's second declaration
(D-GAP2-2b); disclose in FINAL_REVIEW against TARGETS' "five listed literature interfaces".
**FR-B-183.**  `Bridge.sm_R : SM.hyp_R := SM.sm_R_of_cv_R RProof.cv_R` — BRIDGE.md §3 (19)–(21) verbatim (B1–B3 make the
germ a simple transversal RIII event, ax:R gives (20), B4 (17)/(18) gives (21)); the library theorem's conclusion IS
`SM.hyp_R` (all-side-parameters form, equivalent to the chamber form by prop:C-chamber, `hyp_R_iff_base`); no new
mathematics.
**FR-F-184-1 (shape).**  TARGETS: "the conjunction of these actual C identities, with their printed quantifiers, signs and
domains … not … a freely supplied lawful function … must not retain an R assumption": a flat `structure : Prop` whose
fields are the ACCEPTED bundles, the corner lane's FINAL `CS7Data`/`CSoftData`, the proved Prop `hyp_R`, and
`ALawfulData`-shaped Props for cor:C-inherits' identities; the row is the instantiation at `Bridge.sm_R`, `thm_C_S7`,
`thm_C_soft`, `cor_C_inherits Bridge.sm_R` — R discharged, no parameter; hyp:R's policy mode `explicit_parameter` is
honoured by `cor_C_inherits (hR : hyp_R)`.
**FR-F-184-2 (genericity of children).**  `C` is defined on generic polygons only, so `C(λ₁), C(λ₂)`, `C(P_ε)` carry
genericity proofs: UNIVERSALLY quantified in the corner lane's FINAL (`∀ h₁ h₂`, `∀ hQ`; proof-irrelevant Props), the
deletion's genericity at a simple cusp wall EXISTENTIAL (`CuspLawC`, the domain check sm-6:335–359), `P̄` by the
accepted `generic_reversal`.  Both designs had `∃`-genericity for CS7/CSoft; corrected.
**FR-F-184-3 (coverage ↔ fields).**  chamber constancy `chamber`; silent E/C `silent`; flat `flat`; vertex–edge both bigon
branches + sliding `vertex_edge` (`VertexEdgeAt` is bigon ∨ sliding, `vertexEdge_bigon_or_sliding`); triple `triple :
hyp_R`; full cusp on the (G1) domain incl. threaded `cusp` (no emptiness hypothesis); empty-cusp zero retained
`empty_cusp`; soft in every sector incl. zero-selector `soft` (every `SoftAdmissible q`); reversal / cyclic / triangles
inherited with cor:A-lawful `reversal`, `cyclic` (= def:C's `cornerStateSum_genericShift`), `triangles`.  Root
independence has no C analogue and is not a field.  The cusp law's `κ` clause follows `ALawfulData.cusp_law` (`κ = ±1`,
the rotation jump).
**FR-F-184-4 (cor:C-inherits' shape).**  No comparison-lane design exists yet; `CInheritsData` is this lane's proposal
(B's), TO BE UNIFIED: if the comparison lane fixes another shape, the field TYPES `cusp`, `reversal`, `triangles` (and
the `hinh` parameter) change, `corner_laws_and_soft_of` does not.

## 4. Proof routes, row by row (accepted lemmas by file:line; all grep-verified 2026-09-15)

**155 (R)(A)(B)(C) — PROVED in the FINAL** (`carrierfloor_R/A/B/C_of_sm`).  (R): `P_eq_homfly` (SM/PolynomialBlock.lean:667),
`rot_reversal` (CV/Rotation.lean:416).  (A): `roundingRecord` (CV/Rounding.lean:245, `roundingRecord_eq` :251 is `rfl`),
`roundingAdmissible` (:235), `polyComp_P` (:118, `rfl`), `principalTurn_eq_sm` (CV/Setup.lean:201, `rfl`), `CV.rounding.a`
(CV/Rounding.lean:406).  (B): `rotAbs_cast` (CV/Rotation.lean:149), `rot_eq_rotationNumber` (:374), `Int.cast_abs`.
(C): `toSM` = `single_generic_of_diagrammatic` (CV/Rounding.lean:127), `regular_iff_sm` (CV/Setup.lean:248);
`mindegAZ_spec` (SM/LinkLaurentRing.lean:513), `P_ne_zero` (SM/PolynomialBlock.lean:793) for `floor_z0`.
**155 (D) — PROVED** (`carrierfloor_D`): `groupedPoly_of_piecesOn_eq_empty` / `groupedWrithe_of_piecesOn_eq_empty`
(CV/X1.lean:111/115), `carrierPolygon_cvRegular` (:91), `carrierR` (:99), `uniformrot.pos_ge_one/one_dissent`
(CV/UniformRot.lean:271–306), `regular_reversal'`, `rot_reversal` (CV/Rotation.lean:412/416), `mindegAZ_eq_of_spec`
(SM/LinkLaurentRing.lean:630), `coeffAt_one` (:306).
**`CarrierSlotFloor` (U-SLOT, leaf `carrier_slot_floor_of_C`).**  Piece-free: `carrierfloor_D.floor_D` (needs the corner
polygon's turns nonzero: `geoCornerPolygon_turn_ne_zero` SM/GeoCornerPolygon.lean:580 through `CarrierGeometry.ofCV hG`
/ `WeakGeneric`).  With pieces: `groupedknot hn hG hS q` (CV/GroupedKnot.lean:883) fields `knot_diagram` (:853),
`grouped_polynomial` (:857), `grouped_writhe` (:861), `underlying_curve`, `no_triple_points` (:870), `retain_all`
(positivity, `geoPositiveLift_isPositive` SM/GeoPositiveLift.lean:548); shadow `geoPositiveLift_Γ` (:536) =
`geoCarrierShadow` (:97, `abbrev` = `Shadow.single (geoCarrierPolyComp …)`); `|turn| < π` by `principalAngle_bounds`
(SM/RegularPairs.lean:56); the alternative by `principalTurn_eq_sm` (`Iff.rfl`); SM's `CarrierFloorCHyp.of_diagram`
pattern (floor Statements_FINAL :292); then `hC.floor` + `rot_eq_rotationNumber`, `rotAbs_cast`, `carrierR_cast`
(CV/X1.lean:120), `exact_mod_cast`.  Risk: the `PolyComp` equality `geoCarrierPolyComp … = polyComp (geoCornerPolygon …) _`
(proof-irrelevant fields; `PolyComp.ext` or `rfl`) and the `ofCV` vs `ofDiagrammatic` binders (Prop, irrelevant).
**165 — assembly PROVED** (`singleton_D_i_of`): `mindegAZ_mul` (SM/LinkLaurentRing.lean:757), `mindegAZ_spec` (:513),
`cvt_groupedPoly_ne_zero` (groupedknot + `P_ne_zero`), `slot` (CV/X1.lean:103) unfolded, `omega`.
**U-SPLIT (leaf `cvt_singleton_split`)** — the printed chain d6:2890–2935 on the geo layer, six sub-leaves (A's decomposition):
(a) `insert c S ∈ Ind` (`CV.mem_Ind_iff`, `c ∈ U` ⇒ nonadjacent to `S`), `U(S') = U(S) ∖ {c}`, pieces of `S'` = pieces of `S`
minus `{c}` (pure graph on `residualGraph`, `pieceLabels` CV/Carriers.lean:703; ~250 lines); (b) the split of the carrier `q`
into `Λ₁, Λ₂ : GeoComponent (insert c S)` and every other carrier unchanged (CV:lem:carriers (i)–(iv) at `S'`,
CV/CarriersLemma.lean; the geo carrier insert/smoothing layer `CarrierInheritedInsert`/`CarrierSmoothing`/
`GeoCarrierOrder`; ~400–800); (c) `groupedPoly`/`groupedWrithe` factorisation: `piecesOn q = piecesOn q₁ ∪ piecesOn q₂ ∪ {pieceOf c}`
with the same `pieceHomfly` (labels literal), `pieceHomfly (pieceOf c) = 1` (lc:single-crossing, accepted) and
`pieceWrithe = 1` (~300); (d) rotation additivity: CV:lem:turnlift (ii) (CV/TurnLift.lean) with the two smoothing corners'
opposite turns (`principalAngle` of `det(u,v)`, `det(v,u)`, (G5)); `uniformrot` (i)/(ii) ⇒ `σ rot(Λᵢ) ≥ 1` ⇒
`carrierR q = carrierR q₁ + carrierR q₂` (~250); (e) the sign pattern: one loop uniform, the other one-dissent, in the
literal reversal form (`principalTurn_reversal` SM/RotationReversal.lean:49; ~150).  Estimated 1500–2500 lines.
**175 (U-175, leaf `cvt_pair_row_zero_of_singleton`)**: `rowTerm_of_mem_Ind` (RProof/X1Rows.lean:168) at
`PRE_175_pair_present_on_empty` (:1548); `wind = ∏ weight` (CV/Carriers.lean:440), `Finset.prod_ne_zero_iff`,
`weight_ne_zero_iff` (:468) ⇒ every carrier uniform; the third crossing `z ∉ J` (`triangleCrossings_card`
RProof/Cores.lean:1245, `J.card = 2`); `PRE_175_third_singleton_piece hPar` (X1Rows.lean:1566); owner `cvt_exists_owner`
(PROVED: `pieceOwner` CV/CarriersLemma.lean:319, `mem_piecesOn_iff` :338); `h165.factor_zero`; `Finset.prod_eq_zero`,
`mul_zero`.  Assembly `extreme_pair_zero_of_singleton` PROVED (`parity` RProof/Cores.lean:1819 for `δ`).
**174 / 176 / 177 (U-174/176/177)**: the RA ledgers on `Omega1 / carrierR / groupedPoly`, consuming rows 168 (`exterior`,
X1Rows2.lean:1966, `EXT_exteriorFactor_eq_base`), 171 (`fibre_partition`), 172 (`generic_selector` X1Rows.lean:1309),
173 (`generic_transport` GenericTransport.lean:11157: `GT_Wall`/`GT_Relabel`, `G11_Config`), CV:lem:fulltwist
(CV/FullTwist.lean), CV:lem:homflyrows (ii)/(iii) (CV/HomflyRows.lean), CV:selector_A, `cvt_groupedPoly_inSupportM`,
turnlift (ii), uniformrot, cor:groupedknot, `CarrierSlotFloor.coeff_zero` at the outer carriers (GSC §4 "no exponent
below d_A occurs in f_A"; EST (16); ESC (19)); and the MOVES: an RII deletion of the switched empty pair (174), an RII
port relation (176), a matched switch + RIII through the wall + RII after one smoothing (177) — the predicates
`RI/RIIData/RII/RIIIData/RIII` exist (SM/LinkMoves.lean:590–700); their realisation on the grouped contact diagrams is
G10/G11-scale work (the accepted G11: one RIII site, ~11k lines).  Mitigation (D-F11): each unit first states its move
as an interface Prop, proves the RA ledger from it, then attacks the move; the interface Props are never mapped.
**178 — PROVED** (`cv_R_of_rows`): `A2_cvRNear_of_rows` (X1Rows.lean:2876), `hyp_R_of_near_of_chamberinv` (:2940),
`availability_zero_one` (X1Rows2.lean:3619), `generic_selector`, `generic_transport`, `CV.chamberinv_ii`
(CV/ChamberInvRow.lean:78).
**183 — PROVED** (`sm_R_of_rows`): `SM.sm_R_of_cv_R` (Bridge/SmR.lean:52–60), itself `hyp_R_of_cv_hyp_R` + `Bridge.B4.pointwise`.
**184 — PROVED** (`corner_laws_and_soft_of`): `prop_C_chamber`, `prop_C_silent`, `thm_C_S3`, `thm_C_S5`,
`cornerStateSum_genericShift` (SM/CChamber.lean); field shapes `ALawfulData` (SM/ALawful.lean:44–135), corner FINAL
`CS7Data`/`CSoftData`.

## 5. Interface hypotheses (explicit, never mapped) and what is provable now

Interfaces: `SM.CarrierFloorData` and its clause bundles (floor lane; consumed by `carrierfloor_of_sm`,
`carrier_slot_floor_of_C`); `CS7Data`, `CSoftData` (corner lane; row 184's field types); `CInheritsData` (proposed for
the comparison lane's row 128); `SingletonSplitData` (this lane's U-SPLIT); `CarrierSlotFloor` (this lane's U-SLOT);
`CV.SingletonDiData` (for 175); the four `RowShape` rows (for 178/183); `SM.hyp_R` (for 184).

Provable NOW, unconditionally (all inputs accepted) — DONE in the FINAL: 155 (D); the four F6 bridges (R)(A)(B)(C) as
conditional theorems; `CarrierFloorCHyp.toSM`; `floor_z0`; `CarrierSlotFloor.coeff_zero`; `cvt_groupedPoly_ne_zero`;
`cvt_groupedPoly_inSupportM`; `cvt_exists_owner`; `cvt_chamberInvII`; 165's `of_degree_gap` and `singleton_D_i_of`;
175's assembly from `PRE_175_*`; 178's `cv_R_of_rows`; 183's `sm_R_of_rows`; 184's `corner_laws_and_soft_of`.
Provable now as conditionals / leaves with accepted inputs only: `carrier_slot_floor_of_C` (U-SLOT),
`cvt_pair_row_zero_of_singleton` (U-175), `cvt_singleton_split` (U-SPLIT — needs NO floor input; can start today).
Row closures today: NONE.  155 waits on row 99 (C) ← row 94; 165 on 155 (C) [i.e. row 99 (C)] + U-SPLIT; 175 on 165;
174/176/177 on row 99 (C) + their moves; 178/183 on 174–177; 184 on 183 + rows 110, 112, 128.

## 6. Unit decomposition (byte-identical skeleton copies of Statements_FINAL.lean; statements frozen; helpers prefixed)

| unit | prefix | content / leaves | inputs | est. lines | est. hours | start |
|---|---|---|---|---|---|---|
| U-155 | `cvt155_` | port-ready `CV/CarrierFloor.lean` = §1 (no leaf; statement review, then port when the floor lane's module names are final) | floor FINAL | 450 | 1 | after floor port |
| U-SLOT | `cvtS_` | `carrier_slot_floor_of_C` | groupedknot, GeoPositiveLift, GeoCornerPolygon, UniformRot, LinkLaurentRing; SM (C) as hypothesis | 350 | 2–3 | NOW |
| U-SPLIT | `cvt165s_` | `cvt_singleton_split : SingletonSplitData` in five sub-leaves (a)–(e) of §4 | CV rows 136, 138, 139, 142, 144, 145, 146, 153, 158; lc:single-crossing; geo carrier insert/smoothing layer | 1500–2500 | 6–10 | NOW |
| U-175 | `cvt175_` | `cvt_pair_row_zero_of_singleton` | `PRE_175_*`, `weight_ne_zero_iff`, `triangleCrossings_card`, 165's statement | 120 | 1 | NOW |
| U-174 | `gsc_` | `RProof.generic_selected` (move interface Prop → RA ledger → RII deletion) | §4; `CarrierSlotFloor` as hypothesis until row 99 (C) | 3000–5000 | 6–10 | ledger NOW |
| U-176 | `est_` | `RProof.extreme_transport` (RII port relation) | §4 | 3000–5000 | 6–10 | ledger NOW |
| U-177 | `esc_` | `RProof.extreme_selected` (matched switch + RIII through the wall + RII; 3-component lowest z-row) | §4; G11 toolkit | 5000–8000 | 8–14 | ledger NOW |
| U-178 | — | port `RowShape`, `cv_R_of_rows`, `cv_R` as `RProof/CvR.lean` | 174–177 | 60 | 0.3 | after 174–177 |
| U-183 | — | `Bridge/Theorem.lean`: `Bridge.sm_R` | 178 | 10 | 0.1 | after 178 |
| U-184 | — | `SM/CornerLaws.lean`: §5 statement + `corner_laws_and_soft` | 183; rows 110, 112 (corner), 128 (comparison) | 150 | 0.5 | after those |

Total ≈ 13 600–21 600 lines (point estimate 17 000), dominated by U-174/176/177; ≈ 30–50 agent-hours; ≈ 12–20 h wall
clock with U-174/176/177 in parallel after U-SLOT.  Order: U-SLOT ∥ U-SPLIT ∥ U-175 now; the three RA units start on
their ledgers now (their proofs never read (C) directly — only `CarrierSlotFloor`); U-155 when the floor lane ports;
U-178/183/184 are ports.  Reviews: one statement review per row module (155 with FR-CV-155-*; 165 with FR-CV-165-*;
184 with FR-F-184-*; the fixed-name rows 174–178/183 have accepted or dictated statements — review the instantiation).

## 7. Blocking risks (ranked)

1. **Row 99 (C) ← row 94 fd:contact (contact lane)** — the only unconditional blocker of rows 155, 165, 175 and of the
   floor steps of 174/176/177; the bridges and corollaries here are ready and cost nothing more.
2. **Rows 174/176/177 need Reidemeister-move realisations on the grouped contact diagrams** (G10 RII deletion/port;
   for 177 a matched switch + RIII through the wall): G11-scale (11k lines per site); the dominant cost of the whole
   package; only mitigation is the interface-Prop-first pattern so that the ledgers are proved and reviewed early.
3. **U-SPLIT is this lane's, not shared** (FR-CV-165-3): the carrier split under `insert c S` on `GeoComponent` and the
   piece transfer; 1.5–2.5k lines of geo-layer work; independent of the floor lane, so it should start now.
4. **Row 184's `CInheritsData` / `CuspLawC` shapes** must match the comparison lane's cor:C-inherits (no design yet);
   field types change, the assembly does not.
5. **Axiom footprint** of `RProof.cv_R` / `Bridge.sm_R` / `SM.corner_laws_and_soft` includes `SM.lit_homfly_descent`
   (D-GAP2-2b): disclose in FINAL_REVIEW.
6. **Row 155 (B)'s reversal branch on SM objects** (FR-CV-155-5): statement-review risk only.
7. **U-SLOT hypothesis assembly**: `geoCarrierPolyComp` vs `polyComp (geoCornerPolygon …)`, `ofCV` vs `ofDiagrammatic`
   binders; bounded (Prop / proof-irrelevant structure fields).
