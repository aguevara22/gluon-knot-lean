# PREREVIEW — CV/R tail statements (rows 155 CV:thm:carrierfloor, 165 CV:singleton_D_i, 178 R:cv_theorem, 183 Bridge:theorem, 184 SM:corner_laws_and_soft)

Independent Lean 4 auditor, 2026-09-15 16:56 UTC / 12:56pm ET. Object: the FROZEN statements
`work/drafts/cvtail/Statements_FINAL.lean` (992 lines) with `PLAN_FINAL.md` §1–§3 (FR-CV-155-1..9, FR-CV-165-1..4,
FR-R-*, FR-B-183, FR-F-184-1..4) and §6 (units). This is the pre-review of non-vacuity / fidelity red flags /
triviality / truth of the six leaves of this lane, NOT the formal fidelity review.

Sources read: d3_floor.tex 736–807 (the theorem), 808–1012 (its printed proof); d6_vertexedge.tex 2660–2700
((D)(i) in context), 2860–2950 (the printed proof of (D)(i)), 1157–1200 (def:markeddata); d1_setup.tex 487–520
(def:wind, def:pieces), 908–935 (def:X1, prop:chamberinv); d10_axioms.tex 1–40 (ax:R); BRIDGE.md §1 (quoted
hyp:R / ax:R), §3 (19)–(21); sm-6-comparison.tex 105–125 (cor:A-lawful), 313–360 (cor:C-inherits + proof);
sm-4-knotlaws.tex 984–992 (thm:C-soft), lem:soft-generic; EXECUTION.json, R_ASSEMBLY_SPEC.md, TARGETS.md,
OPEN_WORK.md, lean/axiom-policy.json, AUTHOR_NOTES D-GAP2 / D-GAP2-2b / D-FL-1; the floor lane's
PLAN_FINAL §5 (FR-FL-*), the corner lane's PLAN_FINAL §5 (FR-CC-*) and PREREVIEW.md.
Accepted Lean read: SM/HypR (hyp_R), Bridge/SmR (sm_R_of_cv_R, hyp_R_of_cv_hyp_R), RProof/X1Rows (CV.hyp_R,
ExtremePairZeroData, GenericSelectedData, ExtremeTransportData, ExtremeSelectedData, PRE_175_*, CvRNear,
ChamberInvII, A2_cvRNear_of_rows, hyp_R_of_near_of_chamberinv), CV/Events (Ind, U, IsSimpleRIII), CV/Carriers
(pieceOf, pieceLabels, piecesOn, weight, CarrierUniform), CV/CarriersLemma (pieceOwner, mem_piecesOn_iff),
CV/X1 (groupedPoly, groupedWrithe, carrierR, slot, Omega1, X1DefinitionData), CV/Rounding (polyComp, OverUnder,
toPolygonDiagram, clearance, roundingAdmissible, roundingRecord, CVRoundingData), CV/Rotation (rot, rotAbs,
rot_reversal, rot_eq_rotationNumber), CV/RotationSmooth (rotCurve), CV/UniformRot, CV/ChamberInvRow
(chamberinv_ii), CV/Setup (Generic, Diagrammatic, Regular, regular_iff_sm, generic_of_sm), SM/Rounding
(RoundingWitness, Admissible, clearance), SM/LinkDiagram (reverse, componentCount), SM/LinkMoves (LinkEquiv),
SM/TurnLift (ClosedC1Curve.reverse), SM/ALawful (ALawfulData, whole), SM/CChamber, CSilent, CS3, CS5 (the four
accepted bundles + cornerStateSum_genericShift), SM/NamedWallPredicates, CuspDefinition, CuspSideCrossings,
ContactIndices, DeletedTuple, SoftInsertionTuple, SoftAmplitudeSectors, StarGenericLaw, StarPolygons,
GenericReversal, CyclicChambers, Chirotope, RegularLocus, RegularPairs (principalAngle_sign), LinkLaurentRing
(coeffAt, mindegAZ, mindegAZ_spec, mindegAZ_mul), FlatCarriersDefs (GeoComponent, geoCornerPolygon);
work/drafts/floor/Statements_FINAL.lean 110–342 and work/drafts/corner/Statements_FINAL.lean (CS7Data, CSoftData).

Checks run (`source /workspace/envs/lean/env.sh; cd work/lean`; nothing written under work/lean):
- `lake env lean ../drafts/cvtail/Statements_FINAL.lean`: 0 errors, exactly 10 `sorry` warnings at lines 160,
  194, 198, 937 (the 4 sibling-lane placeholders `cf_thm_carrierfloor`, `thm_C_S7`, `thm_C_soft`,
  `cor_C_inherits`), 600, 693, 738 (this lane's leaves `carrier_slot_floor_of_C`, `cvt_singleton_split`,
  `cvt_pair_row_zero_of_singleton`) and 757, 790, 803 (the fixed-name RA rows 174, 176, 177). 19 s.
- Verbatim check of §0: after stripping comments, every one of the 17 floor-lane declarations copied into §0.1
  (`CarrierFloorRData/AData/BData/CHyp/CData/Data`, `Round`, `junctionTemplate`, `AllPosOrOneNeg`,
  `UniformOrOneDissent`, `PolygonDiagram.reverse`, `tangencySet`, `CrossesPositively`, `TangencyCount`, `BClaim`,
  `zZeroPart`, `coeffAt_zZeroPart_zero`) is byte-identical to work/drafts/floor/Statements_FINAL.lean; the floor
  file additionally has `junction_local`, `floor_support`, `CarrierFloorCHyp.of_diagram`, `coeffAt_zZeroPart_of_ne`
  (not copied, not needed). `CS7Data` and `CSoftData` are byte-identical to the corner lane's FINAL.
- `lake env lean ../drafts/cvtail/PREREVIEW_probes.lean` (= Statements_FINAL + the probes of §6): 0 errors; the
  only `sorry` besides the file's ten is my own unfinished P5b (not load-bearing). Auditor original:
  `/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/Probe1.lean`.
- `#print axioms`: `carrierfloor_D`, `SingletonDiData.of_degree_gap`, `corner_laws_and_soft_of` →
  [propext, Classical.choice, Quot.sound, lit_homfly]; `CarrierFloorCHyp.toSM` → standard only;
  `carrierfloor_of_sm`, `floor_z0`, `CarrierSlotFloor.coeff_zero`, `singleton_D_i_of`, `cvt_groupedPoly_ne_zero`,
  `cvt_groupedPoly_inSupportM`, `cv_R_of_rows`, `sm_R_of_rows` → standard + lit_homfly + lp_lm + lp_lm_uniqueness;
  the row terms `corner_laws_and_soft`, `Bridge.sm_R`, `RProof.cv_R`, `extreme_pair_zero_of_singleton` add
  `sorryAx` (from the leaves/placeholders only). No `lit_homfly_descent` yet (it enters through row 99 (C) ←
  row 94, exactly as FR-R-178-2 predicts). Matches PLAN_FINAL's header claim.
- Fixed names against lean/axiom-policy.json `targets`: `Bridge.sm_R` (Bridge:theorem), `RProof.cv_R`
  (R:cv_theorem), `RProof.generic_selected / extreme_pair_zero / extreme_transport / extreme_selected`,
  `SM.corner_laws_and_soft`, `SM.cor_C_inherits`, `SM.thm_C_S7`, `SM.thm_C_soft`, `CV.hyp_R` (CV:ax:R) — all
  present with those exact names and the policy's `hyp:R` mode `explicit_parameter` honoured
  (`cor_C_inherits (_hR : hyp_R)`; the final row has no parameter).

## 0. Verdict

**SATISFIABLE / NON-VACUOUS, no blocking issue.** No provably contradictory hypothesis combination in
`CV.CarrierFloorData`, `CV.SingletonDiData`, `CV.SingletonSplitData`, `CV.CarrierSlotFloor` or
`SM.CornerLawsAndSoftData`. Joint satisfiability reduces to the truth of two refereed source theorems: the
carrier floor (C) (d3 thm:carrierfloor, a Bennequin/front bound on positive diagrams) and Hypothesis R itself
(`SM.CornerLawsAndSoftData.triple : hyp_R` and `cusp : CuspLawC` are true iff R is; R is the campaign's claim,
to be proved by rows 174–178). Every hypothesis set has an explicit witness (§2). Fidelity: every printed clause of
155 (R)(A)(B)(C)(D) and of 165 has a field; every field without a printed counterpart is one of the documented
readings FR-CV-155-1..9 / FR-CV-165-1..4 or library material; `CornerLawsAndSoftData` covers every item of
TARGETS' "Required coverage" list with one field each, plus the three inherited identities TARGETS says to use
(reversal / cyclic / triangles) — no TARGETS identity lacks a field, no field is unlicensed; `Bridge.sm_R : SM.hyp_R`
is the consequent of BRIDGE.md's displayed theorem (19)–(21) at the proved antecedent. Triviality: none that makes a
row true; two harmless tautological fields are noted (§4). Truth probes: all six leaves TRUE (§5); none DOUBTFUL.
Non-blocking notes: 11 (§7), the most useful being the δ-restricted `flat : CS3Data` field vs cor:A-lawful's
all-parameters flat law (equivalent by chamber constancy; record it) and the port hazards of §0's redeclarations.

## 1. Compile, axioms, interface copies — see "Checks run" above. Nothing to add: PLAN_FINAL's header (992
lines, 0 errors, exactly 10 `sorry`, axiom footprint) is accurate as of this reading.

## 2. Non-vacuity / satisfiability (Q1)

| structure / hypothesis set | witness | how checked |
|---|---|---|
| (A)(B) binders: `hL : Diagrammatic L`, `hreg`, `hturn`, `D : OverUnder (polyComp L hreg)`, `0 < ε < clearance L hreg` | `SM.star 1` (the counterclockwise triangle) with the empty over/under assignment | `Diagrammatic`: no self-intersections, no vertex on a non-incident edge (3-gon); `Regular`/turns `2π/3 ≠ 0` via `star_generic_law`; `clearance_pos hL hreg` gives a nonempty ε-range; `OverUnder` on the crossing-free shadow is the empty function. Structural; not built in Lean (no library `Diagrammatic (star 1)` proof; the accepted CV:lem:rounding row shares the binder set verbatim). |
| (B) `UniformOrOneDissentCV L` and the two conclusion branches | `star 1` (all turns positive → left branch); `starNeg 1 = reversal (star 1)` (all negative → right branch) | `principalTurn_reversal` negates every turn (with an index shift `2 − i`, irrelevant to "all positive / exactly one negative"). Both branches inhabited; they are disjoint for `n ≥ 3` (forced by `Regular.three_le`), so the disjunction is a case split, not a choice. |
| (C) `CarrierFloorCHyp L hreg X` (shadow, positive, diagrammatic, turn_ne, turn_lt_pi, alternative) | `star 1` with `X` the crossing-free positive diagram | `positive` vacuous; turns `2π/3 ∈ (0, π)`; conclusion `1 − 0 − 1 ≤ mindegAZ (homfly X)`: `rotAbs = 1` (`rotationNumber (star 1) = 1`, `rot_eq_rotationNumber`), `homfly X = 1` for the crossing-free circle (`lit_homfly` normalisation) so `0 ≤ mindegAZ 1 = 0` — consistent and tight. Independent sanity on the positive trefoil polygon (w = 3, R = 2): `1 − 3 − 2 = −4 ≤ 2 = min deg_a P` in the paper's skein normalisation — consistent. |
| (D) `piecesOn = ∅`, turns nonzero, alternative | `star 1`, `S = ∅`, the unique carrier | Lean (§6 P4/P5): `CV.Generic (star 1)` via `generic_of_sm`; `∅ ∈ CV.Ind`. (D) is PROVED in the file (`carrierfloor_D`), so it is satisfiable outright; the hypothesis set is inhabited by this witness (the triangle has no crossings, so the carrier is piece-free; `1 ≤ carrierR` reads `1 ≤ 1`). |
| `CarrierSlotFloor`'s hypothesis (`UniformOrOneDissentCV (geoCornerPolygon …)`) | same | inhabited as above; conclusion `slot = 1 − 0 − 1 = 0 ≤ mindegAZ 1 = 0` — consistent, tight. Lean (§6 P6): (D) implies the `CarrierSlotFloor` inequality on every piece-free carrier (7 lines). |
| 165 hypotheses (`CarrierUniform q`, `SingletonPieceOn q c`) | the corner lane's limaçon octagon `(1,−2),(8,0),(7,8),(−1,8),(0,2),(3,0),(3,5),(0,4)`, `S = ∅`, `c` its unique crossing | numeric (the corner PREREVIEW's exact-rational check, re-used): all 8 turns left (uniform), exactly one crossing, no triple point; `c ∈ U(∅)`, its piece is `{c}`, assigned to the unique carrier. Conclusion: `groupedPoly = P_{{c}} = 1` (one-crossing unknot diagram), `slot = 1 − 1 − 2 = −2`; `coeffAt d 0 1 ≠ 0` iff `d = 0`, and `−2 + 2 = 0 ≤ 0` — the degree gap is TIGHT on this witness (a real consistency check, not slack); `Omega1 = coeffAt (−2) 0 1 = 0` ✓. |
| `SingletonSplitData`'s ledger on that witness | same, `S' = {c}` | daughters Λ₁ (4 corners, all left, rot 1), Λ₂ (6 corners, one right, rot 1): `1 = 1·1`, `w: 1 = 0 + 0 + 1`, `R: 2 = 1 + 1`, Λ₁ uniform, Λ₂ one-dissent ✓. Also: `SingletonSplitData` forces `carrierR q ≥ 2` for any uniform carrier with a self-crossing (both daughters have `R ≥ 1` by uniformrot) — consistent with the classical fact that a locally convex closed curve of turning number 1 is simple. |
| `CornerLawsAndSoftData` | field by field | `chamber/silent/flat/empty_cusp` are accepted theorems; `cyclic` is PROVED; `vertex_edge : CS7Data`, `soft : CSoftData` were found non-vacuous by the corner PREREVIEW (bowTie sectors, `vertex_halves_children`); `triangles : TrianglesC` — Lean (§6 P1): the two projections are `Generic (SM.star 1)` and `Generic (starNeg 1)` in that order, so the field reads `C(K₁) = −1 ∧ C(K₋₁) = 1`; by def:C on a crossing-free triangle `C = (−1)^{ℓ} · c(Q)` with `ℓ = 3`, `c(Q) = 1` (uniform embedded carrier, lem:corner-values (i)) → `−1`; clockwise `ℓ = 0` → `+1` ✓ and `ReversalLawC` at `n = 3` gives `(−1)^3 · (−1) = 1` ✓. `cusp : CuspLawC`: hypothesis `CuspAt j ∧ G1 (deleteVertex …)` is inhabited by every simple cusp germ whose deletion is (G1)-generic (threaded or empty; sm-6:335–359 then proves (G2)); `triple : hyp_R`: no `TripleAt` germ is constructed in the library (as for `VertexEdgeAt`, `CuspAt`), so vacuity cannot be excluded in Lean — the same status as the accepted `ALawfulData.triple_law`; mathematically a simple triple wall exists. |

No contradictory combination found. The two fields whose truth is NOT a refereed source theorem but the campaign's
claim are `triple : hyp_R` and (through `C = A`, thm:comparison under R) `cusp`, `reversal`, `triangles`: they hold
iff Hypothesis R holds. This is by design (TARGETS: "The source calls R a hypothesis. This deliverable must prove
it").

## 3. Fidelity (Q2)

### 3.1 Row 155, clause by clause (d3:736–807 ↔ `CV.CarrierFloorData`)

| printed | field | note |
|---|---|---|
| (R) "Let K be an oriented knot and −K … Then P_{−K} = P_K" | `homfly_reverse` (`componentCount = 1`), `knot_reverse` (`LinkEquiv X X' → homfly X'.reverse = homfly X`) | FR-CV-155-2; `homfly` = CV:def:homfly (`P_eq_homfly`); "knot" = `LinkEquiv` class (D2) |
| "the same crossing signs" / "the same writhe" | `sign_reverse` / `writhe_reverse` | definitional in SM (`reverse_sign`) |
| "rotation number of the underlying plane curve negated" | `rot_reverse_polygon` (shadow `single (polyComp L hL)` → reversed shadow ∧ `rot (reversal L) hL' = −rot L hL`), `rot_reverse_curve` (`rotCurve γ.reverse = −rotCurve γ`) | FR-CV-155-3; the extra binder `hL' : Regular (reversal L)` is derivable (`regular_reversal'`) — harmless |
| (A) "Let L and D satisfy the hypotheses of lem:rounding" | binders `hL hreg hturn D`, `0 < ε < clearance L hreg` | the accepted CV:lem:rounding's binder set |
| "returns one curve and one diagram at those data" | `one_record` (`Rnd … = SM.Round …`), `one_curve`, `one_diagram` | `one_record` is `rfl` (see §4) |
| "the junction … determined by ε, by the two incident unit directions and by the transition profile, fixed once and for all" | `junction_determined` (parametric, `SM.junctionTemplate` = `juncArc` with the fixed `Real.smoothTransition`) | FR-CV-155-4 / FR-FL-A1 (stronger than the image form) |
| "the arc length ℓ is then determined by the endpoint condition" | `length_determined` | |
| "the rest of the curve is L itself" | `rest_is_L` (set form ∪ straight parts; = accepted `CV.rounding.a`) | |
| (B) hypotheses ("diagrammatic closed polygon … turns exist and are nonzero, carrying D, after reversing … uniform or one-dissent; R = |rot(L)|") | `hL hreg hturn D`, `UniformOrOneDissentCV L`, `rotAbs L hreg` | |
| (B) conclusion ("u ∈ S¹, ε₁ > 0, ∀ ε ∈ (0, ε₁): L_ε of Round(L,D,ε) has exactly R tangencies at u and at −u, each crossing positively") | `BClaimCV` (`euclideanLength u = 1`, `0 < ε₁ ≤ clearance`, `TangencyCount (Rnd …) (±u) (rotAbs L hreg)`), asserted for the normalised orientation: `(AllPosOrOneNegCV L ∧ BClaimCV) ∨ (AllPosOrOneNegCV (reversal L) ∧ SM.BClaim (polyComp L hreg).reverse (D.toPolygonDiagram hL).reverse)` | FR-CV-155-5 / FR-FL-B1..B4. `ε₁ ≤ ε₀(L)` is added (the printed proof takes `ε₁ = ε₀(L)`; without it the record does not exist) — a strengthening of the witness, the only sensible reading. The reversed branch is stated on SM objects because `OverUnder.reverse` is not library material; content-equal by `toPolygonDiagram`. The literal "Round(L,D,ε) for L itself" reading is FALSE for an all-negative L (negative crossing sense), so the disjunction is the faithful rendering; I concur with FR-FL-B1. Statement-review flag only; no consumer reads (B). |
| (C) "oriented knot diagram, all crossings positive, writhe w, underlying curve a closed polygon L, turns existing, nonzero, |·| < π, finitely many double points, all transversal, no triple points, none a corner, no corner on a non-incident edge; R = |rot|; after reversing … uniform or one-dissent" | `CarrierFloorCHyp L hreg X`: `shadow` (one component, hence "knot"), `positive`, `hreg` (parameter), `turn_ne`, `turn_lt_pi`, `diagrammatic : Diagrammatic L`, `alternative`; `X.writhe`, `rotAbs L hreg` | FR-CV-155-6. `Diagrammatic` (CV/Setup 1382) is item-for-item the printed double-point list (finite; exactly two preimages = no triple point; transverse; none a corner; no vertex on a non-incident edge) — as the source itself says ("repeats the shared-image clause of def:diagrammatic"). `toSM` PROVED (standard axioms only). |
| (C) "min deg_a P_D ≥ 1 − w − R" / "the same bound for f_D = [z⁰]P_D whenever f_D ≠ 0" | `floor : 1 − X.writhe − (rotAbs : ℤ) ≤ mindegAZ (homfly X)` / `floor_zZero` on `SM.zZeroPart (homfly X) ≠ 0` | ℤ form; `homfly X ≠ 0` (lp:core) makes `mindegAZ` def:adeg's `mindeg_a`; support corollary `floor_z0` PROVED |
| (D) "P generic, S ∈ Ind, L a carrier carrying no residual piece, so that P_{S,L} = 1 and w_{S,L} = 0 …, turns nonzero, after reversing … uniform or one-dissent. Then R(L) ≥ 1 and min deg_a P_{S,L} = 0 ≥ 1 − w_{S,L} − R(L)" | `floor_D`: `piecesOn = ∅ → (∀ j, principalTurn (geoCornerPolygon …) j ≠ 0) → UniformOrOneDissentCV (geoCornerPolygon …) → 1 ≤ carrierR ∧ mindegAZ groupedPoly = 0 ∧ 1 − groupedWrithe − carrierR ≤ 0` | FR-CV-155-7. The "so that" is commentary (the accepted `X1_definition.empty_conventions`); the conclusion nevertheless states `mindegAZ groupedPoly = 0`, so nothing printed is lost. PROVED (`carrierfloor_D`, uniformrot (i)/(ii) + `rot_reversal`). |

Every printed clause has a field. Fields without a printed sentence: `Rnd` (the printed "Write Round(L,D,ε)"),
`BClaimCV` (the (B) claim), `CarrierFloorCHyp.toSM`, `cvt_homfly_ne_zero`, `floor_z0`, `rotAbs_intCast_real`, the
four `carrierfloor_*_of_sm` bridges, `carrierfloor_of_sm`, `CarrierSlotFloor` (+ `coeff_zero`,
`cvt_groupedPoly_ne_zero`, `cvt_groupedPoly_inSupportM`) — all library material declared as such (FR-CV-155-1, -8,
-9; PLAN §1, §5), none a field of the row bundle `CarrierFloorData`, whose five fields are exactly the five printed
clauses. The dependency column of claims.py lists `CV:ax:slbound` for 155; the FINAL derives (C) from SM row 99
(← fd:contact, the same source of the sl bound), consistent with OPEN_WORK ("The front and HOMFLY bounds can use
the selected SM developments"); rows 161 (VERIFIED) / 162 (implemented) show that route is live.

### 3.2 Row 165 (d6:2682–2687 ↔ `CV.SingletonDiData`)

| printed | field | note |
|---|---|---|
| "Let S ∈ Ind(G_P)" (P generic, def:X1's standing binder) | `hn`, `hG : Generic P`, `hS` | `hn : 3 ≤ n` is def:polygon's standing `n ≥ 3` — harmless |
| "let A be a uniform carrier of S" | `q : GeoComponent`, `CarrierUniform hG.crossingGeometry S q` | def:wind's "all corners turn the same way" (`turn : SignType` on `geoCornerPolygon`) |
| "let {c} be a singleton residual piece of S carried by A" | `SingletonPieceOn hP S q c` = `mem_U : c ∈ U S`, `labels : pieceLabels (pieceOf c) = {c}`, `owner : pieceOf c ∈ piecesOn q` | FR-CV-165-2; exactly the shape `PRE_175_third_singleton_piece` + `cvt_exists_owner` produce |
| "Then min deg_a f_A ≥ (1 − w_{S,A} − R(A)) + 2" | `degree_gap : ∀ d, coeffAt d 0 (groupedPoly) ≠ 0 → slot + 2 ≤ d` | FR-CV-165-1 (support form; vacuous when `f_A = 0`, exactly the printed proof's "if either row vanishes then f_A = 0 and the claim is trivial") |
| "so the factor Ω₁(S,A) of def:X1 is zero" | `factor_zero : Omega1 = 0` | PROVED from the first (`cvt_omega1_eq_zero_of_gap`) |

Every printed clause has a field; no field lacks a counterpart. `SingletonSplitData` is the U-SPLIT interface
(FR-CV-165-3/4), not a row field. One reading to record (non-blocking, §7.5): clause (D)(i) sits inside
thm:s7universal under §6's standing convention (a vertex–edge event), but its wording and its printed proof
(d6:2890–2947) are general; the Lean row is the general-P form, hence at least as strong as any contextual reading.

### 3.3 Row 184 ↔ TARGETS "Exact final target"

TARGETS: "the conjunction of these actual C identities, with their printed quantifiers, signs and domains … not …
a freely supplied lawful function … must not retain an R assumption or assume the desired laws". Checked:

| TARGETS "Required coverage" | field | licence / note |
|---|---|---|
| Chamber constancy | `chamber : CChamberData` | accepted prop:C-chamber (polygon-space chambers) |
| silent-wall invariance | `silent : CSilentData` | accepted prop:C-silent (E) and (C) |
| The flat deletion law | `flat : CS3Data` | accepted thm:C-S3 — δ-restricted side parameters (§7.1) |
| Both bigon branches and the sliding branch of the vertex–edge law, with the stated sign and the actual two child polygons | `vertex_edge : CS7Data` | `VertexEdgeAt` = bigon ∨ sliding (`vertexEdge_bigon_or_sliding`), sign `contactSign`, halves `firstHalf/secondHalf` (def:deletion-halves); corner lane FINAL |
| Triple-wall invariance at every source simple triple wall, after proving R | `triple : hyp_R` | a CONCLUSION field, discharged by `Bridge.sm_R` — no R assumption retained |
| The full cusp jump on the source domain (the deletion satisfies G1), including threaded cusps | `cusp : CuspLawC` | hypotheses `CuspAt j`, `G1 (deleteVertex …)`, no emptiness; asserts the deletion generic (sm-6's domain check), `κ = ±1` the rotation jump, `C(loop) − C(no) = −κ C(del)` at all side parameters — the `ALawfulData.cusp_law` shape minus the A-only "every induced root" clause |
| retain the direct empty-cusp zero result | `empty_cusp : CS5Data` | accepted thm:C-S5 |
| The soft theorem in every sector, including zero-selector sectors | `soft : CSoftData` | every `SoftAdmissible P j q` (the three determinant conditions of def:soft), `∀ ε ∈ (0, ε₁)`, `∀ hQ`; the ℚ identity with `softAmplitudeMultiplier = (χ₋+χ₊)/2`; the corner PREREVIEW instantiated all three sectors |
| "Use the normalizations and reversal/cyclic identities inherited with cor:A-lawful as stated there" | `reversal : ReversalLawC` (`C(P̄) = (−1)^n C(P)`), `cyclic : CyclicLawC` (def:C's cyclic quotient; PROVED), `triangles : TrianglesC` (`C(K₁) = −1 ∧ C(K₋₁) = 1`) | licensed by this TARGETS sentence and by cor:C-inherits' "every identity of cor:A-lawful"; root independence has no C analogue (correctly absent) |

No identity TARGETS names lacks a field; no field is unlicensed. The theorem is about `cornerStateSum` throughout
(no lawful-function parameter); `corner_laws_and_soft : CornerLawsAndSoftData` has no parameters; the only R in the
term is the proved `Bridge.sm_R`. `CInheritsData` (row 128 proposal) is `ALawfulData` with `cornerStateSum`,
minus `root_independent` and the induced-root clause — TO BE UNIFIED with the comparison lane (FR-F-184-4); the
assembly `corner_laws_and_soft_of` reads only its `cusp_law`, `reversal_law`, `triangles`.

### 3.4 Rows 178 / 183 (EXECUTION.json, R_ASSEMBLY_SPEC.md, BRIDGE.md)

- 178: `RProof.cv_R : CV.hyp_R` — the fixed name/type of axiom-policy ("R:cv_theorem", "CV:ax:R" → `CV.hyp_R`);
  `CV.hyp_R` (X1Rows.lean:124) is ax:R (d10:18–24) on the forced bundle `IsSimpleRIII` (zero set exactly
  `{G3, G4, G4, G4}`, `e < f < g` pairwise remote, concurrent at an interior point, transversal), in the R6
  all-parameters form (`X1` at every positive and every negative parameter; equal to the chamber form by
  prop:chamberinv (ii)). `cv_R_of_rows` is the finite summation of R_ASSEMBLY_SPEC (3)–(4) (accepted
  `A2_cvRNear_of_rows` over the accepted rows 170/172/173 and the four open rows) plus R6
  (`hyp_R_of_near_of_chamberinv` with the accepted `CV.chamberinv_ii`) — PROVED, axioms standard + lit_homfly +
  lp_lm(+uniqueness). OPEN_WORK's "free of R assumptions, CV thm:main, lawful-quantity axioms and SM R-dependent
  comparison/inherited laws": the dependency graph of `cv_R` here is rows 167–177 + CV rows 136–158 + SM row 99 (C)
  (← 94 ← 91); none of the forbidden inputs appears.
- 183: BRIDGE.md §3 displays "RA theorem in the quoted CV ax:R form ⟹ ∀ P ∈ E^T_SM11, C(P₊) = C(P₋)" (19), proved
  via B1–B3 (the germ is a simple transversal RIII event), ax:R (20), B4 (21). The accepted library theorem
  `SM.sm_R_of_cv_R : CV.hyp_R → SM.hyp_R` (Bridge/SmR.lean:60) IS that implication with `SM.hyp_R` = the quoted
  hyp:R ("At every simple triple wall, C(P₊) = C(P₋)", sm-4:1149–1151) in the accepted all-parameters rendering
  (`TripleAt e f k → ∀ tp tm, C(side true tp) = C(side false tm)`; chamber form by prop:C-chamber). `Bridge.sm_R :
  SM.hyp_R := SM.sm_R_of_cv_R RProof.cv_R` is exactly its consequent at the proved antecedent — the fixed name and
  type of axiom-policy ("Bridge:theorem" → `Bridge.sm_R`) and EXECUTION.json's target; `sm_R_of_rows` keeps the
  implication form from the four open rows. Exact; no new mathematics (FR-B-183 confirmed).

## 4. Triviality (Q3)

Nothing makes a row trivially true. Two tautological fields, both inherent and documented:
- `CV.CarrierFloorAData.one_record` is `rfl` (`Rnd` is an `abbrev` for `roundingRecord = SM.Round …`), and SM's
  `one_record : Round C D ε h = Round C D ε h'` is proof irrelevance. This is what the source asserts ("uniqueness
  of the fixed construction's record, not uniqueness among all possible smoothings", d3:830–833; FR-FL-A2); the
  content of (A) lives in `one_curve`, `one_diagram`, `junction_determined`, `length_determined`, `rest_is_L`.
- `CV.CarrierFloorRData.rot_reverse_polygon`'s first conjunct (`X.reverse.Γ = Shadow.single C.reverse`) is
  definitional; the second (`rot_reversal`) is the content.
Not trivial: `degree_gap` (tight on the octagon witness, §2), `factor_zero`, `CarrierSlotFloor` (its whole content
on piece-free carriers is `R ≥ 1`, i.e. uniformrot), `floor_D` (same), `TrianglesC` (a computation), `CuspLawC`
(asserts genericity of the deletion AND the jump), `hyp_R` (the campaign). `cyclic` being discharged by the accepted
`cornerStateSum_genericShift` is by design (TARGETS: "as stated there"). `CInheritsData.triple_law : hyp_R` is
trivially provable under the row-128 parameter `_hR : hyp_R` — redundant, harmless (it is cor:A-lawful's triple
law listed for completeness).

## 5. Truth probes of the six leaves (Q4)

| leaf | verdict | reason |
|---|---|---|
| `carrier_slot_floor_of_C : SM.CarrierFloorCData → CarrierSlotFloor` (U-SLOT) | **TRUE** | Piece-free carrier: (D) (PROVED; Lean §6 P6 derives the inequality). Carrier with pieces: cor:groupedknot (B) (accepted `groupedknot`) gives a positive knot diagram on the carrier's corner polygon with `homfly = groupedPoly`, `writhe = groupedWrithe`; its hypotheses for SM (C): shadow generic from the diagram's own `generic` field, turns nonzero (`geoCornerPolygon_turn_ne_zero` + `principalAngle_sign`), `|turn| < π` (regular pairs exclude antiparallel edges; the two strands at a smoothing corner have `det ≠ 0`), alternative by `Iff.rfl`. The carrier polygon has ≥ 3 corners automatically (`carrierPolygon_cvRegular`). Exactly d6:2936–2939's sentence. Risk is Lean plumbing (`geoCarrierPolyComp` vs `polyComp`), not truth. |
| `cvt_singleton_split : SingletonSplitData` (U-SPLIT) | **TRUE** | d6:2890–2935: `c` residual ⇒ `S ∪ {c}` independent; `{c}` isolated in `G_P[U(S)]` ⇒ the other pieces are literally the same label sets; the oriented smoothing at `c` splits `A` into two carriers (independence ⇒ every smoothing splits, so the two arcs at `c` lie on different carriers); lem:carriers (iv) for `S'` puts each former piece of `A` on `Λ₁` or `Λ₂`; `P_{{c}} = 1` (RI), `w({c}) = 1`; turnlift (ii) with the two new corners' turns `±principalAngle(u,v)` gives `rot A = rot Λ₁ + rot Λ₂`; all old corners have `A`'s sign `σ`, so one daughter is uniform and the other one-dissent; uniformrot ⇒ `σ rot Λᵢ ≥ 1` ⇒ `R(A) = R(Λ₁) + R(Λ₂)`; the reversal form of the alternative covers `σ = −1`. Verified numerically on the octagon (§2). Lean needs a label-set transport of `pieceHomfly` across `Piece hP S` / `Piece hP (insert c S)`. |
| `cvt_pair_row_zero_of_singleton` (U-175) | **TRUE** | `rowTerm (Q ∪ J) = wind · ∏ Ω₁` on the independent support (`pair_present_on_empty`); `wind ≠ 0 ⇒` every carrier uniform (def:wind, `weight_ne_zero_iff`); the third crossing `z ∉ J` has the singleton piece `{z}` (accepted `PRE_175_third_singleton_piece`), its owner (`cvt_exists_owner`) is uniform, so `singleton_D_i.factor_zero` kills its `Ω₁` and the product vanishes. A 120-line assembly, as PLAN says. |
| `RProof.generic_selected` (U-174, GSC) | **TRUE** (per the printed RA proof; statement accepted by the 06:35Z panel) | The complementary-couple identity `T_E(b) = T_P(b) + T_P(ac)` in the canonical and relabelled branches is the RA-frame argument consumed unchanged by the accepted assembly `A2_cvRNear_of_rows`; its inputs (rows 168/171/172/173, fulltwist, homflyrows (ii), knot parity, turnlift, uniformrot, groupedknot, `CarrierSlotFloor`) are all accepted or proved here modulo row 99 (C). Not re-derived line by line in this pre-review; the risk PLAN §7.2 names (RII deletion realisation) is cost, not truth. |
| `RProof.extreme_transport` (U-176, EST) | **TRUE** (same basis) | `T_H(j) = T_L(j)` for the three singletons; presuppositions `singleton_rows_present`, `graphs_complementary` (R-LOC-2 clause 4, accepted core), `sign_branch` (`extreme_iff_alternating`, accepted) already PROVED in X1Rows; the transport field rests on the RA proof + `CarrierSlotFloor`. |
| `RProof.extreme_selected` (U-177, ESC) | **TRUE** (same basis) | `T_H(∅) − T_L(∅) = T_L(xyz)`; `full_present_on_empty` / `full_absent_on_complete` PROVED (`PRE_177_*`); the couple field is the RA proof's matched switch + RIII + RII chain; the largest unit (5–8k lines) but no truth flag found. |

Doubtful leaves: none. (The three RA rows were not re-derived here; their statements are frozen accepted text and
their consumers are the accepted assembly, so a false row would make CV ax:R — the campaign's declared input —
false; I found no indication of that.)

## 6. Probes (work/drafts/cvtail/PREREVIEW_probes.lean = Statements_FINAL + this section; 0 errors)

- P1 `#check (star_generic_law le_rfl).1.2.2.2.1 : Generic (SM.star 1)`, `.1.2.2.2.2.1 : Generic (starNeg 1)`;
  `#print SM.TrianglesC` shows `cornerStateSum _ (proof on star 1) = −1 ∧ cornerStateSum _ (proof on starNeg 1) = 1`.
- P2 `#print axioms` of the 16 assemblies listed under "Checks run".
- P3 the fixed row types: `Bridge.sm_R : hyp_R`, `RProof.cv_R : CV.hyp_R`, `corner_laws_and_soft :
  CornerLawsAndSoftData`, `cor_C_inherits : hyp_R → CInheritsData`.
- P4 `example : CV.Generic (SM.star 1) := CV.generic_of_sm (by norm_num) …` — closes.
- P5 `example : (∅ : Finset (Crossing (star 1))) ∈ CV.Ind …` — closes (`mem_Ind`, `simp`).
- P6 `example (hD : CV.CarrierFloorDData) … (h : piecesOn … = ∅) … : slot ≤ mindegAZ groupedPoly` — closes in 3
  lines from `hD.floor_D` (the piece-free half of U-SLOT is already available from (D)).
- P7 `hyp_R` unfolds to the `ALawfulData.triple_law` shape with `cornerStateSum` — `Iff.rfl`-level.
- Name checks: `geoCornerPolygon_turn_ne_zero` (on `WeakGeneric`), `uniform_iff_same_way_of_ne_zero`,
  `principalTurn_eq_sm`, `principalTurn_reversal` (`= −principalTurn P (2 − i)`), `regular_reversal'`,
  `uniformrot.pos_ge_one`, `uniformrot.one_dissent`, `X1_definition`, `WallGerm.EmptyCusp`, `WallGerm.contactSign`,
  `SoftDuplication.softAmplitudeMultiplier`, `SoftAdmissible`, `Bridge.B4.pointwise`, `sm_R_of_cv_R` — all resolve
  with the expected types.

## 7. Non-blocking notes (for the statement reviews / AUTHOR_NOTES)

1. **`flat : CS3Data` is the accepted δ-restricted form.** cor:A-lawful's flat law (`ALawfulData.flat_law`,
   and `CInheritsData.flat_law`) holds at ALL nonzero side parameters; `CS3Data.flat_law` only for `tR, tL < δ`.
   Equivalent by chamber constancy on each side (`cornerStateSum_side_const`, used in thm_C_S3's own proof), and
   the row thm:C-S3 was accepted in that form, so TARGETS' "domains of cor:A-lawful" (the class of walls) is met;
   but "with their printed quantifiers" invites a one-line FR-F-184 note, or the all-parameters companion
   `flat_law_all : ∀ sRight sLeft …` proved from `thm_C_S3` + `cornerStateSum_side_const` (≈ 15 lines).
2. **Port hazards of §0.** (a) §0.1 redeclares `SM.CarrierFloorRData/…/Data`, `SM.Round`, …, and §0.2
   `SM.CS7Data`, `SM.CSoftData`, plus the four placeholders — must be deleted at port (as the header says) or the
   modules clash. (b) `CV.CarrierFloorRData/AData/BData/CHyp/CData/Data` reuse SM's names inside `namespace CV`
   with `open SM`; it resolves here, but downstream files opening both namespaces will hit ambiguity — consider
   `CV.CarrierFloor.RData` or a `CV`-prefixed spelling, or document the rule "never `open SM CV` together".
3. **(A) `one_record` is `rfl`** (§4) — record in FR-CV-155-4 that the field is definitional by construction
   (it already says "`rfl`"), so the reviewer does not read it as an empty promise.
4. **(C) is stated on `X : Diagram` + `shadow`, (A)(B) on `D : OverUnder`.** Two vocabularies in one row; content
   equal (`PolygonDiagram.ofDiagram` / `toPolygonDiagram`). A sentence in FR-CV-155-6 explaining why (C) needs
   `Diagram` (`homfly` is defined on `Diagram`) would pre-empt a reviewer question.
5. **165 general-P reading** (§3.2): note in FR-CV-165 that (D)(i) is rendered for every CV-generic `P`, not only
   for the chamber polygons of §6's standing convention — stronger, and what the printed proof proves.
6. **(D)'s `∀ j, principalTurn … ≠ 0` is unused and automatic** for carriers of CV-generic polygons
   (`geoCornerPolygon_turn_ne_zero` + `principalAngle_sign`); kept as printed (FR-CV-155-7 says so) — fine.
7. **Axiom footprint disclosure** (FR-R-178-2): `RProof.cv_R`, `Bridge.sm_R`, `SM.corner_laws_and_soft` will carry
   `SM.lit_homfly_descent` (author-authorised second declaration of lit:homfly, D-GAP2) and `SM.src_contact`
   (through row 94); TARGETS' "five listed literature interfaces" sentence needs the D-GAP2 paragraph in
   FINAL_REVIEW. Not yet visible in `#print axioms` (the (C) placeholder is `sorry`).
8. **`CInheritsData` is a proposal** (FR-F-184-4); `triple_law : hyp_R` is redundant under `_hR`; the comparison
   lane may drop `reversal_law`/`triangles`, in which case `CornerLawsAndSoftData.reversal/triangles` need their
   own route (C = A on generic polygons, thm:comparison, + `ALawfulData`) — same mathematics, different plumbing.
9. **U-SPLIT plumbing**: `groupedPoly hS q = groupedPoly hS' q₁ * groupedPoly hS' q₂` needs `pieceHomfly` to
   depend on `H` only through `pieceLabels` (transport across `Piece hP S` vs `Piece hP (insert c S)`); check that
   `pieceDiagram`/`pieceCurve` are label-set functions before starting (a) of §4.
10. **(B)'s reversed branch on SM objects** (FR-CV-155-5): a statement-review flag only; I concur with the reading
    and with the floor lane's FR-FL-B1 (the literal claim is false for all-negative `L`).
11. **claims.py dependency column** for 155 lists `CV:ax:slbound` (row 162, implemented) rather than `cf:thm-
    carrierfloor`; the FINAL's route (SM row 99 through the F6 bridge) should be named in the row's AUTHOR_NOTES
    entry so the checker's dependency reading and the actual proof agree.

## 8. What can close now (unchanged from PLAN §5)

Unconditionally: 155 (D), `toSM`, `floor_z0`, `coeff_zero`, `of_degree_gap`, `singleton_D_i_of`,
`extreme_pair_zero_of_singleton` (modulo U-175), `cv_R_of_rows`, `sm_R_of_rows`, `corner_laws_and_soft_of` — all
already PROVED in the file. Startable now with accepted inputs only: U-SPLIT, U-175, U-SLOT (conditional on SM (C)).
Row closures today: none (155/165/175 wait on row 99 (C) ← 94; 174/176/177 on their moves; 178/183/184 on those).
