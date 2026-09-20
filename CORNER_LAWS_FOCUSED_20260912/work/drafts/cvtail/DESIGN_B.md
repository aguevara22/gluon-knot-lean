# CV/R tail — design B (proof feasibility and assembly), 2026-09-15

Lane: every pending row that is not an SM row — 155 CV:thm:carrierfloor, 165 CV:singleton_D_i,
174-178 R:generic_selected / extreme_pair_zero / extreme_transport / extreme_selected / cv_theorem,
183 Bridge:theorem, 184 SM:corner_laws_and_soft.  Sketch: `work/drafts/cvtail/Sketch_B.lean`
(710 lines; `cd work/lean && lake env lean ../drafts/cvtail/Sketch_B.lean` exit 0 at 14:47Z / 10:47am ET; every
`sorry` is a proof leaf, no statement carries one).  Written by a Claude Code architect subagent
(claude-fable-5-1) of the pod executor after reading EXECUTION.json, TARGETS.md, R_ASSEMBLY_SPEC.md,
PROOF_PLAN.md, OPEN_WORK.md, BRIDGE.md §3, the four RA files of rows 174-177, d3_floor.tex 736-1012,
d6_vertexedge.tex 2682-2947, sm-6-comparison.tex 299-372, AUTHOR_NOTES (R-lane panel 06:35Z, D-GAP2,
D-GAP2-2b, row 91 acceptance 14:25Z), work/drafts/rlane2/Statements_FINAL.lean + NOTES_FINAL.md,
work/drafts/gap2/Gap2Statements.lean §7-§9, work/drafts/floor/Sketch_A.lean, work/drafts/contact/DESIGN_A.md,
and the accepted modules RProof/{Cores,X1Rows,X1Rows2,GenericTransport}.lean, Bridge/{B4,SmR}.lean,
CV/{X1,Rounding,UniformRot,Curl,GroupedKnot,ChamberInvRow,Axioms,Carriers}.lean, SM/{HypR,ALawful,
CChamber,CSilent,CS3,CS5,CornerStateSum,LinkLaurentRing,Rotation*}.lean.

## 0. The assembly picture (what is already in the library)

The library already contains, ACCEPTED or as reviewed library material, everything above the four open
R rows:

* `RProof/X1Rows.lean` fixes the STATEMENTS of rows 174-178 as bundles: `GenericSelectedData` (L1434),
  `ExtremePairZeroData` (L1483), `ExtremeTransportData` (L1628), `ExtremeSelectedData` (L1757),
  `CvTheoremData`/`CvRNear`/`ChamberInvII` (L1835-1880); their X₁-free presupposition fields are PROVED
  (`PRE_175_*`, `PRE_176_*`, `PRE_177_*`); the whole fibre assembly is PROVED: `A2_fibre_identities`
  (L2688), `A2_cvTheoremData_of_rows` (L2825), `A2_cvRNear_of_rows` (L2876, takes the seven row theorems
  170, 172-177 in their fixed shapes), `hyp_R_of_near_of_chamberinv : CvRNear → ChamberInvII → CV.hyp_R`
  (L2940).  The accepted row theorems have one common header shape
  (`exterior` X1Rows2:1966, `availability_zero_one` X1Rows2:3619, `generic_selector` X1Rows:1309,
  `generic_transport` GenericTransport:11157): `∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ <Bundle> hn E e f g δ`.
* prop:chamberinv (ii) is accepted: `CV.chamberinv_ii` (CV/ChamberInvRow.lean:78) — so `ChamberInvII`
  is a one-liner (`RProof.cvt_chamberInvII` in the sketch, PROVED).
* `SM.sm_R_of_cv_R : CV.hyp_R → SM.hyp_R` (Bridge/SmR.lean:60, PROVED from B1-B4 and `SM.hyp_R`).
* The four accepted C rows `SM.prop_C_chamber : CChamberData`, `SM.prop_C_silent : CSilentData`,
  `SM.thm_C_S3 : CS3Data`, `SM.thm_C_S5 : CS5Data`, and `SM.A_lawful : ALawfulData` (the shape every
  C identity of cor:C-inherits copies).

Consequence (verified in the sketch): **row 178 is a PROVED conditional theorem now**
(`RProof.cv_R_of_rows`, axioms standard + `SM.lit_homfly`), **row 183 is one line**, and **row 184's
assembly is PROVED now** (`SM.corner_laws_and_soft_of`) given the three pending SM bundles.  The whole
remaining proof burden of this lane is rows 174, 176, 177 (each a several-thousand-line RA argument) and
the geometric split behind 165; row 155 (R)(A)(B)(C) is a bridge port of SM row 99 and 155 (D) is done.

## 1. Fidelity risks, recorded BEFORE the statements

**Row 155.** FR-CV-1: (R)(A)(B)(C) are SM row 99's clauses (floor lane's `SM.CarrierFloor{R,A,B,C}Data`,
copied verbatim into the sketch §0 from work/drafts/floor/Sketch_A.lean, TO BE UNIFIED) read on CV's
printed binders through the accepted polygon bridge of CV/Rounding.lean §1 (`polyComp L hreg`,
`OverUnder`, `toPolygonDiagram`, `roundingRecord`, `clearance`) — the F6 rule under which CV:lem:rounding
and CV:lem:curl were accepted; CV's `rot` is `CV.rot` (= `rotationNumber` by `rot_eq_rotationNumber`),
the curve `rot` is `rotCurve` (= `ClosedC1Curve.rot`, `rfl`), and `P_D` is CV:def:homfly's `homfly`
(= `P` by `P_eq_homfly`).  FR-CV-2: (A) "one curve and one diagram at those data" is rendered as the
identity of the record with the named construction (`Rnd … = SM.Round …`, i.e. `roundedWitness`):
uniqueness of the FIXED construction's record, exactly as the printed clause says ("not uniqueness among
all possible smoothings", d3:765-766).  FR-CV-3: (B) the normalised branch is on CV's binders
(`BClaimCV`, `R = rotAbs L hreg`, `ε₁ ≤ clearance L hreg`); the reversal branch is stated on SM's objects
(`(polyComp L hreg).reverse`, `PolygonDiagram.reverse`) because `OverUnder.reverse`/`Diagrammatic
(reversal L)` are not library material — to be unified with the floor lane's FR-FL-B1 ("perform the
allowed normalization once": the claim is made for the normalised polygon; for `−L` the tangencies are
crossed positively only after reversal).  FR-CV-4: (C) is stated in ℤ (`(1 − w) − rotAbs ≤ mindegAZ
(homfly X)`) where SM's is in ℝ with `|rotationNumber|`; equivalent by the casts `rotAbs_cast_real`;
the `f_D` clause uses the floor lane's `zZeroPart`.  FR-CV-5: (D) "R(L) ≥ 1 and min deg_a P_{S,L} = 0 ≥
1 − w_{S,L} − R(L)" is `1 ≤ carrierR ∧ mindegAZ groupedPoly = 0 ∧ slot ≤ 0` on def:X1's own objects
(`slot = 1 − groupedWrithe − carrierR`), the hypothesis "after reversing … uniform or one-dissent" the
four-way disjunction `UniformOrOneDissentCV` (reversal negates every principal turn,
`principalTurn_reversal`); "carrying no residual piece" is `piecesOn … = ∅` (empty conventions
`groupedPoly_of_piecesOn_eq_empty`, `groupedWrithe_of_piecesOn_eq_empty`).

**Row 165.** FR-CV-6: `f_A = [z⁰]P_{S,A}` and "min deg_a f_A ≥ (1 − w − R) + 2" are rendered in SUPPORT
form, `∀ d, coeffAt d 0 (groupedPoly) ≠ 0 → slot + 2 ≤ d` (vacuous when `f_A = 0`, where `Ω₁ = 0` holds
anyway); "so the factor Ω₁(S,A) … is zero" is the separate conjunct `Omega1 = 0`.  "A a uniform carrier" =
`CV.CarrierUniform` (def:wind); "{c} a singleton residual piece of S carried by A" = `SingletonPieceOn`
(`c ∈ U(S)`, `pieceLabels (pieceOf c) = {c}`, `pieceOf c ∈ piecesOn q`, lem:carriers (iv)).  FR-CV-7: the
CV clause is STRONGER than SM cb:singleton (`c(A) = 0`) by the "+2" gap, which PROOF_PLAN step 5 requires
("requires only the stated degree gap and zero conclusion"); the proof therefore consumes cb:singleton's
SPLITTING MACHINERY (interface `SingletonSplitData`, §2.3) and not its conclusion.

**Rows 174-178.** FR-R-1: no new reading — the statements are the fixed bundles of RProof/X1Rows.lean
(statement panel 06:35Z, readings in work/drafts/rlane2/NOTES_FINAL.md §6-§9), headers byte-identical to
work/drafts/rlane2/Statements_FINAL.lean L722-1002.  FR-R-2: `cv_R : CV.hyp_R` is CV:ax:R's R6
all-parameters form; its proof is the punctured form + prop:chamberinv (ii) (R6 "cv_R = cv_R_near +
chamberinv(ii)").

**Row 183.** FR-B-1: `Bridge.sm_R : SM.hyp_R := SM.sm_R_of_cv_R RProof.cv_R` — BRIDGE.md §3 (19)-(21)
verbatim ("The imported RA theorem applies … This is exactly its quoted hyp:R"); the library theorem's
conclusion IS `SM.hyp_R`, so the row is an application, not a restatement (EXECUTION.json names the row
"Bridge:theorem" with fixed declaration `Bridge.sm_R`; the axiom policy fixes no type — `SM.hyp_R` is the
type every note since 15:15Z records).  Module: `Bridge/Theorem.lean` importing `Bridge.SmR`, `RProof.CvR`.

**Row 184.** FR-FIN-1: TARGETS.md "Define its conclusion as the conjunction of these actual C identities,
with their printed quantifiers, signs and domains" → `CornerLawsAndSoftData` with fields the ACCEPTED
bundles `CChamberData`, `CSilentData`, `CS3Data`, `CS5Data` (statement hashes untouched), the accepted
Prop `hyp_R` (TARGETS "Triple-wall invariance at every source simple triple wall, after proving R"), and
the three pending SM bundles `CS7Data`, `CInheritsData`, `CSoftData`; nesting bundles rather than
flattening their fields is presentation only — every field is an identity of `cornerStateSum`.
FR-FIN-2: no R parameter remains (`triple := Bridge.sm_R`); no "freely supplied lawful function"; the
empty-cusp zero is retained as `CS5Data`.  FR-FIN-3: `CInheritsData` = `ALawfulData` with
`cornerStateSum` for `amplitude`, minus `root_independent` (A-specific, no C analogue) and minus the
A-specific "every induced root" sub-clause of the cusp law; the deletion's genericity at a simple cusp
wall is an EXISTENTIAL field (printed proof sm-6:335-359 proves it from (G1) alone) and the printed
domain "the deletion satisfies (G1)" is kept as hypothesis; `vertex_edge_law`, `triple_law`,
`soft_theorem` of `CInheritsData` are the row bundles `CS7Data`, `hyp_R`, `CSoftData` themselves.
FR-FIN-4: `CS7Data`/`CSoftData` mirror `ALawfulData.vertex_edge_law`/`soft_theorem` with C and existential
genericity of the halves / of `P_ε` (lem:children (ii), lem:soft-generic) — TO BE UNIFIED with lane
corner (110, 112) and the comparison rows (127, 128).  FR-FIN-5: the axiom footprint of
`SM.corner_laws_and_soft` will contain `SM.lit_homfly_descent` (through 155 (C) ← fd:contact ← row 91):
authorised as lit:homfly's second declaration (D-GAP2-2b); TARGETS' "five listed literature interfaces"
is met in the author's reading, to be stated in FINAL_REVIEW.

## 2. Statements and proof routes, row by row

### 2.1 Row 155 CV:thm:carrierfloor — `CV.carrierfloor : CarrierFloorDataCV` (sketch §1)

Statement: `CarrierFloorDataCV` = `clauseR : CarrierFloorRDataCV` (6 fields = SM (R) with `homfly`,
`rot_reversal`, `rotCurve`), `clauseA : CarrierFloorADataCV` (6 fields = SM (A) at `polyComp L hreg`,
`D.toPolygonDiagram hL`, `Rnd := roundingRecord`), `clauseB : CarrierFloorBDataCV` (FR-CV-3),
`clauseC : CarrierFloorCDataCV` (`floor`, `floor_zZero` at `polyComp L hreg`, `homfly`, `rotAbs`),
`clauseD : CarrierFloorDData`.

Route.  (D) **PROVED in the sketch** (`CV.carrierfloor_D`; axioms standard + `SM.lit_homfly` through
`groupedPoly`): `cvt_one_le_rotAbs_of_alt` from `CV.uniformrot.pos_ge_one/one_dissent` (CV/UniformRot.lean:300)
and `rot_reversal` (CV/Rotation.lean:416); `mindegAZ 1 = 0` by `mindegAZ_eq_of_spec` + `coeffAt_one`;
`slot ≤ 0` by `omega`.  (R): `cvt_R_of_sm` PROVED from the SM bundle (`P_eq_homfly`, `rot_reversal`).
(A)(B)(C): leaves `cvt_A_of_sm`, `cvt_B_of_sm`, `cvt_C_of_sm` — instantiate the SM clause at
`C := polyComp L hreg`, `D := D.toPolygonDiagram hL`, `h := roundingAdmissible …` (`roundingRecord_eq` is
`rfl`, CV/Rounding.lean:251), rewrite `polyComp_P`, `rot_eq_rotationNumber`, `rotAbs_cast_real`
(CV/RotationSmooth.lean:71), `P_eq_homfly`, and the equivalence `UniformOrOneDissentCV L ↔
SM.UniformOrOneDissent (polyComp L hreg)` by `principalTurn_eq_sm` (CV/Setup.lean:201).  The bundle
theorem `carrierfloor_of_sm : SM.CarrierFloorData → CarrierFloorDataCV` is library material (D-F11/D-F14
pattern) until the floor lane's `SM.cf_thm_carrierfloor` lands; then `CV.carrierfloor :=
carrierfloor_of_sm SM.cf_thm_carrierfloor` is the row.  Consumed SM bundle clauses: all four of row 99.

### 2.2 The consumer corollary `CV.CarrierSlotFloor` (library; sketch §1.3) — the ONE interface rows
165, 174, 176, 177 read from row 155

"For every carrier `L` of a CV-generic `P` at `S ∈ Ind(G_P)` that is uniform or one-dissent, no
`a`-exponent below `slot = 1 − w_{S,L} − R(L)` occurs in `f_L = [z⁰]P_{S,L}`":
`∀ d, coeffAt d 0 (groupedPoly hn hG hS q) ≠ 0 → slot hn hG hS q ≤ d`.  This is exactly what the four
RA texts invoke ("Hence no exponent below d_A occurs in f_A", GSC §4; EST (16); ESC (19); d6:2939).
Route (`carrier_slot_floor_of_C : SM.CarrierFloorCData → CarrierSlotFloor`, leaf): piece-free carrier —
clause (D) (`groupedPoly = 1`: `d = 0 ≥ slot`); carrier with pieces — `CV.groupedknot hn hG hS q`
(CV/GroupedKnot.lean:883) fields `knot_diagram`, `retain_all` (positivity), `grouped_polynomial`
(`homfly carrierDiagram = groupedPoly`), `grouped_writhe`, `no_triple_points`; the shadow of
`carrierDiagram` is `Shadow.single (geoCarrierPolyComp …)` (`geoPositiveLift_Γ`,
SM/GeoPositiveLift.lean:536, an `abbrev`); turns nonzero `geoCornerPolygon_turn_ne_zero`
(SM/GeoCornerPolygon.lean:580, via `CarrierGeometry.ofCV hG`); `|turn| < π` by `principalAngle_bounds`;
the alternative by `principalTurn_eq_sm`; then (C) `floor` + `mindegAZ_spec` (SM/LinkLaurentRing.lean:513)
+ `rot_eq_rotationNumber`, `rotAbs_cast`.  ~350 lines; PROVABLE NOW as a conditional theorem (only the
SM (C) bundle is an interface; every other input is accepted).

### 2.3 Row 165 CV:singleton_D_i — `CV.SingletonDiStatement` (sketch §2)

Statement (FR-CV-6): `∀ hn hG hS q, CarrierUniform q → ∀ c, SingletonPieceOn hG.cg S q c →
(∀ d, coeffAt d 0 (groupedPoly q) ≠ 0 → slot q + 2 ≤ d) ∧ Omega1 q = 0`.

Route (the printed proof d6:2890-2947, in three steps): (i) `SingletonSplitData` (interface to lane
corner, FR-CV-7): `insert c S ∈ Ind`; carriers `q₁ q₂` of `S' = S ∪ {c}` with `groupedPoly q =
groupedPoly q₁ * groupedPoly q₂` ("the pieces are literally the same objects", 2895-2899, + `P_{{c}} = 1`
lc:single-crossing), `groupedWrithe q = w₁ + w₂ + 1`, `carrierR q = R₁ + R₂` (turnlift (ii) +
uniformrot signs, 2916-2934), one loop uniform and the other one-dissent (`UniformOrOneDissentCV` for
both); (ii) knot parity: `cvt_groupedPoly_inSupportM` PROVED (`groupedknot.grouped_polynomial` +
`CV.ax_homfly.knot_parity`, CV/Axioms.lean:202; `InSupportM.one` when piece-free) and the leaf
`cvt_coeff_zero_mul_floor` (`zRow_zero_mul_of_inSupportM_one`, CV/Axioms.lean:154: the `z⁰` rows
multiply, so the `a`-floors add; ~60 lines); (iii) `CarrierSlotFloor` on `q₁, q₂` at `S'`.
`singleton_D_i_of : SingletonSplitData → CarrierSlotFloor → SingletonDiStatement` is PROVED in the
sketch (arithmetic `slot q + 2 = slot q₁ + slot q₂` by `linarith`/`omega`; `Omega1 = coeffAt slot 0` is
below the floor).  Consumes from cb:singleton's lane: only the split (the SM cb:singleton row itself
proves `c(A) = 0` from the same split through cb:products/thm:floor; ONE shared split unit serves both,
see §3).

### 2.4 Rows 174-177 — fixed headers (sketch §3), consumption

Common inputs (accepted): `localization` (164), `parity` (167), `exterior` (168: the exterior factor
`C_Q` never divided; `EXT_exteriorFactor_eq_base`), `fibre_partition` (171), `generic_table` (172t),
`generic_selector` (172), `generic_transport` (173: the wall transport `GT_Wall`/`GT_Relabel`, the corner
list carried literally, `GT_rotationNumber_tcp`; and G11's `G11_Config` for an RIII site),
CV:lem:fulltwist (159, `CV.fulltwist : FullTwistData`), CV:lem:homflyrows (157), CV:cor:groupedknot
(158), CV:selector_A (164), CV:lem:uniformrot (153), CV:lem:turnlift (ii) (145), ax:homfly knot parity,
and from this lane `CarrierSlotFloor` (§2.2).  Row-specific: 174 GSC — ledger (4)-(8) on the `b/ac`
couple, the full-twist triple `(D_L, D_H, D_0)` (§3 (9)-(11)), extraction (12)-(13) needs the floor on
the two `A`, `B` carriers (uniform after reversal); an RII deletion of the switched empty pair (G10).
176 EST — three singleton rows, two successive smoothings `q, r`, ledger (12)-(15), floor on the two
clean outer carriers (exactly one-dissent by selector_A), extraction (16); an RII port relation (G10).
177 ESC — matched switch + RIII (G11-type configuration) + RII after one smoothing, the three-component
lowest `z`-row (homflyrows (ii)/(iii)), floor on the three outer carriers, live/dead selector branches
(14)-(20).  175 — PROVED modulo one leaf from row 165 (`extreme_pair_zero_of_singleton`): the three
presupposition fields are the accepted `PRE_175_*`; `pair_row_zero`: `rowTerm = wind * ∏ Ω₁`; `wind = 0`
or every carrier uniform (`weight_ne_zero_iff`, CV/Carriers.lean:468); `{z}` a singleton piece
(`PRE_175_third_singleton_piece`), its owner `q` (leaf `cvt_exists_owner`, lem:carriers (iv)),
`singleton_D_i` gives `Omega1 q = 0`, `Finset.prod_eq_zero`.

### 2.5 Row 178 — `RProof.cv_R : CV.hyp_R` (sketch §3, PROVED as `cv_R_of_rows`)

`cv_R := hyp_R_of_near_of_chamberinv (A2_cvRNear_of_rows availability_zero_one generic_selector
generic_transport generic_selected extreme_pair_zero extreme_transport extreme_selected)
cvt_chamberInvII` — spec: R_ASSEMBLY_SPEC (3)-(4) "sum the proved identities (4) over the same finite
outside-support set in (3) … giving exactly CV ax:R"; OPEN_WORK item 4 "on its entire printed
simple/transversal forced-bundle domain" = the binder of `CV.hyp_R`.  Axioms of `cv_R_of_rows`:
standard + `SM.lit_homfly` (+ `lp_lm`, `lp_lm_uniqueness` through the cores).  Module: `RProof/CvR.lean`.

### 2.6 Row 183 — `Bridge.sm_R : SM.hyp_R := SM.sm_R_of_cv_R RProof.cv_R` (sketch §4).  FR-B-1.

### 2.7 Row 184 — `SM.corner_laws_and_soft : CornerLawsAndSoftData` (sketch §5)

Statement: the eight fields of §1 FR-FIN-1.  Proof (PROVED in the sketch as
`corner_laws_and_soft_of : CS7Data → CSoftData → (hyp_R → CInheritsData) → CornerLawsAndSoftData`):
`prop_C_chamber`, `prop_C_silent`, `thm_C_S3`, `thm_C_S7`, `Bridge.sm_R`, `cor_C_inherits Bridge.sm_R`,
`thm_C_S5`, `thm_C_soft`.  Module `SM/CornerLaws.lean`; `cor_C_inherits : hyp_R → CInheritsData` is the
comparison rows' theorem with hyp:R as explicit parameter (axiom-policy mode `explicit_parameter`),
instantiated here at the proved `Bridge.sm_R` — "the final assembly instantiates that conditional
theorem with the separately proved R result" (TARGETS.md).

## 3. Provable now / blocked, and the unit decomposition

Provable NOW, unconditionally (all inputs accepted): 155 (D) [done]; the 178 assembly `cv_R_of_rows`
[done]; `cvt_chamberInvII` [done]; `cvt_groupedPoly_inSupportM` [done]; `cvt_coeff_zero_mul_floor` (U-165-ALG);
`cvt_exists_owner` and the rest of `extreme_pair_zero_of_singleton` (U-175, conditional on 165's
statement only); 155 (R) [done modulo the SM (R) bundle, itself provable now per the floor lane].
Provable now as library-material conditionals (D-F11/D-F14; never mapped until the interface row lands):
`carrierfloor_of_sm` (U-155), `carrier_slot_floor_of_C` (U-SLOT), `singleton_D_i_of` [done],
`corner_laws_and_soft_of` [done].  Blocked on other lanes: 155 (A)(B)(C) mapping ← row 99 (floor lane ←
94 contact lane ← 91 accepted); 165 ← `SingletonSplitData` (shared with cb:singleton, corner lane) +
`CarrierSlotFloor` ← 99 (C); 174/176/177 ← `CarrierSlotFloor`; 175 ← 165; 178 ← 174-177; 183 ← 178;
184 ← 183, 110, 112, 128.

Units (byte-identical skeleton copies of Sketch_B.lean; statements frozen; leaves `sorry`; each unit
proves ONLY its prefixed leaves and returns the file):

| unit | leaves (prefix) | inputs | est. lines | est. hours |
|---|---|---|---|---|
| U-155 | `cvt_A_of_sm`, `cvt_B_of_sm`, `cvt_C_of_sm` (`cvt155_`) | floor lane bundle shapes (interface) | 250 | 1.5 |
| U-SLOT | `carrier_slot_floor_of_C` (`cvtS_`) | groupedknot, GeoPositiveLift, UniformRot, LinkLaurentRing | 350 | 2-3 |
| U-165-ALG | `cvt_coeff_zero_mul_floor` (`cvt165a_`) | CV/Axioms `zRow_zero_mul_of_inSupportM_one` | 60 | 0.5 |
| U-165-SPLIT | `SingletonSplitData` (`cvt165s_`; SHARED with corner lane's cb:singleton split) | CarriersLemma (iv), GeoCarrierInsert/Smoothing layer, turnlift (ii), uniformrot, lc:single-crossing | 1500-2500 | 5-8 |
| U-175 | `cvt_exists_owner` + the `pair_row_zero` leaf (`cvt175_`) | PRE_175_*, weight_ne_zero_iff, 165's statement | 120 | 1 |
| U-174 | `generic_selected` (`gsc_`) | §2.4; G10 RII deletion | 3000-5000 | 6-10 |
| U-176 | `extreme_transport` (`est_`) | §2.4; G10 RII port | 3000-5000 | 6-10 |
| U-177 | `extreme_selected` (`esc_`) | §2.4; G11-type RIII + G10 RII, 3-component lowest row | 5000-8000 | 8-14 |
| U-178 | port `cv_R_of_rows`, `cv_R` (RProof/CvR.lean) | 174-177 | 60 | 0.3 |
| U-183 | `Bridge.sm_R` (Bridge/Theorem.lean) | 178 | 10 | 0.1 |
| U-184 | statement module SM/CornerLaws.lean + `corner_laws_and_soft` | 110, 112, 128 bundles from their lanes | 120 | 0.5 |

Total remaining for this lane ≈ 13 000-21 000 lines (dominated by 174/176/177; the G11 precedent —
one RIII site — took 11 000 lines and ~3 h of wall clock with the lane machinery), ≈ 30-50 agent-hours,
≈ 12-20 h wall clock with U-174/176/177 in parallel after U-SLOT.  Order: U-SLOT ∥ U-165-ALG ∥ U-175
now; U-165-SPLIT jointly with the corner lane now; U-174/176/177 start on the `CarrierSlotFloor`
interface now (their proofs never read (C) directly); U-155 when the floor lane's bundle names are
final; U-178/183/184 are ports.

## 4. Riskiest steps

1. **U-177 (then U-174, U-176): the actual Reidemeister moves.**  ESC §2 needs a matched crossing switch
   followed by an RIII "through the wall" of the grouped contact diagrams and an RII after one smoothing,
   with record isomorphisms between the two sides' diagrams; GSC/EST need an RII deletion/port of an empty
   oppositely-signed pair (G10).  The accepted G11 shows this is feasible (`G11_Config`, `gu5_Side`,
   `G11_Params` in RProof/GenericTransport.lean) but at 5-11k lines per move; the move PREDICATES exist (`RI`, `RIIData`/`RII`, `RIIIData`/`RIII`,
   SM/LinkMoves.lean:590-700) — what is missing is the geometric realisation of the RA's specific moves
   on the grouped contact diagrams (as G11 did for one RIII site).  Mitigation: state each
   move as an explicit interface Prop first (D-F11 pattern), prove the RA ledger from it, then attack the
   move.
2. **U-165-SPLIT (shared with cb:singleton): rotation additivity across the smoothing site** —
   `rot(A) = rot(Λ₁) + rot(Λ₂)` via turnlift (ii) with the two new corners' turns `det(u,v)`, `det(v,u)`
   opposite (d6:2916-2925), and `carrierR q = R₁ + R₂` by the sign argument (uniformrot (i)/(ii) after
   reversal); the carriers-lemma (iv) transfer of every other piece to exactly one daughter.  Geometric,
   no move, but touches the geo carrier insert/smoothing layer (`CarrierInheritedInsert`,
   `CarrierSmoothing`, `GeoCarrierOrder`).
3. **Row 155 (B) reversal branch unification** (FR-CV-3): if the floor lane changes the normalisation
   reading, `CarrierFloorBDataCV` follows; the CV consumers (§2.2) read only (C)+(D), so this is a
   statement-review risk, not an assembly risk.
4. **`carrier_slot_floor_of_C` hypothesis assembly** (U-SLOT): `CarrierGeometry.ofDiagrammatic
   (hG.diagrammatic hn)` versus `CarrierGeometry.ofCV hG` binders in `carrierDiagram` and
   `geoCornerPolygon_turn_ne_zero` (WeakGeneric) — proof-irrelevant `Prop` structures, but the abbrev
   unfolding of `geoCarrierShadow` must match `CarrierFloorCHyp.shadow` by `rfl`/`geoPositiveLift_Γ`.
5. **Statement review of 184** (FR-FIN-1/3/4): the reviewers may prefer flattened fields or ask for the
   A-specific clauses; both are shape changes with the same one-line proof.
6. **Axiom footprint** (FR-FIN-5): `SM.lit_homfly_descent` enters through 155 (C); disclose in
   FINAL_REVIEW as the author's second declaration of lit:homfly.

## 5. Summary of the statements (for the report)

155 `CV.carrierfloor : CarrierFloorDataCV` — (R)(A)(B)(C) = SM row 99 through the polygon bridge on CV's
binders, (D) on def:X1's objects, `1 ≤ carrierR ∧ mindegAZ groupedPoly = 0 ∧ slot ≤ 0`.
165 `CV.singleton_D_i : SingletonDiStatement` — uniform carrier `q`, singleton piece `{c}` on `q`:
`(∀ d, coeffAt d 0 (groupedPoly q) ≠ 0 → slot q + 2 ≤ d) ∧ Omega1 q = 0`.
174-177 `RProof.generic_selected / extreme_pair_zero / extreme_transport / extreme_selected` — the
fixed `∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ <Bundle> hn E e f g δ` headers of RProof/X1Rows.lean's bundles.
178 `RProof.cv_R : CV.hyp_R`.  183 `Bridge.sm_R : SM.hyp_R`.  184 `SM.corner_laws_and_soft :
CornerLawsAndSoftData` = `CChamberData ∧ CSilentData ∧ CS3Data ∧ CS7Data ∧ hyp_R ∧ CInheritsData ∧
CS5Data ∧ CSoftData` as a structure.
