# PLAN_A — def:flat-carriers / cor:flat-carriers, statement design (tag A: transport)

Written 2026-09-13 by a Claude Code statement-architect subagent. Companion file:
`work/drafts/flatcarriers/Statement_A.lean` (725 lines; `lake env lean` clean except the two
`sorry` warnings of `flat_carriers_definition` and `flat_carriers`). Frame SM15. Sources read
verbatim: sm-3-statesum.tex:788-804 (def), 805-835 (cor), 836-913 (proof);
sm-1-polygons.tex:778-826 (lem:flat-sides). Accepted Lean form of the hypotheses:
`SM.flat_sides : … → FlatSidesData hn g j hz hb hc` (SM/FlatSides.lean:17-46, 50-...).

## 0. Summary of the design

* Four configurations, all derived from one `g : WallGerm (n + 1)` (`n ≥ 3`, printed `N = n+1 ≥ 4`),
  one side parameter `t : g.SideParameter`, the flat vertex `j`:
  right side / left side `(g.sideTuple b t).val`, `b : Bool` (which `b` is "right" is decided by
  the turn at `j`: `IsRightSide : turn … j = -1`, `IsLeftSide : turn … j = 1`);
  centre `g.center = P(0)` (not generic, `CrossingGeometry` only); deletion
  `deleteVertex g.center j = Q` (generic `n`-gon).
* The common cyclic Gauss word of lem:flat-sides (ii) is realised by the *equality of crossing
  supports* `CommonSupports g t : ∀ b s, IsCrossing g.center s ↔ IsCrossing (side b) s` (this is
  the `hs` inside `GeometricRecordsAgree` of `FlatSidesData`), hence by the canonical bijections
  `crossingTransport (hs b)`, `visitTransport (hs b)` (SM/CrossingTransport.lean:12,18) and the
  new `markTransport (hs b) : Mark g.center ≃ Mark (side b)`. The common word of (iii) is realised
  by `fusionCrossingEquiv`/`fusionVisitEquiv` (SM/FusionCrossings.lean:91, FusionVisits.lean:39),
  extended to marks by `deletionMark`.
* `S : Finset (Crossing g.center)` is fixed at the centre, independent in the centre's geometric
  interlacement graph (`GeometricInterlaces (flatCentreGeometry …)`), and read on the sides as
  `sideSupport = S.map (crossingTransport (hs b))`, on the deletion as
  `deletionSupport = S.map fusionCrossingEquiv`.
* Side carriers and deletion carriers are the ACCEPTED objects, unchanged:
  `Component`, `owner`, `componentMarkList`, `componentPlaneCycle`, `ccpCornerList/Mark/Count/Polygon`,
  `carrierCrossings` (SM/CarrierSmoothing.lean:122,128; CarrierClosedTrace.lean:54,61;
  CarrierCornerPolygon.lean:317-357; CarrierCrossings.lean:56).
* Centre carriers are obtained by TRANSPORT from a side: the centre carrier "of `q`" (a side
  carrier) is the closed polygonal cycle through the *centre* points of the marks of `q`
  (`centreMarkPoint = geometricMarkPoint (flatCentreGeometry …) ∘ (markTransport (hs b)).symm`),
  in the inherited order: `centrePlaneCycle`, with corner polygon `centreCornerPolygon` (centre
  points of `ccpCornerMark`), and retained crossings `centreCarrierCrossings`. Two def-row
  fields certify that this is what "the same words" define at the centre: `centre_successor`
  (the side's `ρ`, read at centre positions, is the centre circle's own cyclic successor: no
  centre mark strictly between a mark and its successor) and `centre_reconnection` (the selected
  swap is the swap of the centre's own selected visits); `centre_side_independent` certifies the
  family does not depend on the side used.
* Carrier correspondences are honest functions: `carrierMap T q := owner (T (Quotient.out q))`,
  instantiated as `sideToSide br (!br)` and `sideToDeletion b`; cor (i) asserts they are
  bijections with `carrierMap T (owner a) = owner (T a)` (for `a ≠ Sum.inl j` in the deletion case).
* Selector: `cornerSelector Q = if ∀ i, turn Q i = -1 then 1 else if ∀ i, turn Q i = 1 then (-1)^k
  else 0` (right turn = `turn = -1`, left = `1`, `k` = corner count), `carrierSelector = cornerSelector
  ∘ ccpCornerPolygon`.

## 1. Reading of the printed text and the Lean rendering, sentence by sentence

### def:flat-carriers (sm-3:788-804) → `structure FlatCarriersDefinitionData … : Prop` (Statement_A.lean:293-421)

| printed sentence | field(s) | rendering |
|---|---|---|
| "Under the hypotheses of Lemma lem:flat-sides" | parameters `hn g hz hb hc`; theorem gives `∃ δ, … ∀ t < δ, ∃ hs : CommonSupports g t` | the same `hn g j hz hb hc` as `flat_sides`; the sign change `hsc` is NOT needed to *define* the carriers and is omitted from `flat_carriers_definition` (weaker hypothesis = stronger row; see §4) |
| "identify the crossing visits of the two sides, of the centre P(0) and of the deletion P(0)∖j through the common cyclic Gauss word of that lemma's clauses (ii) and (iii)" | `common_gauss_word` | (a) `(geometricGaussList h0).map (visitTransport (hs b)) = gaussList hn1 hPb` for both sides: the identification IS the common Gauss list (cut at label 0); (b) `(geometricGaussWord h0).map fusionCrossingEquiv = gaussWord hn hQ` (cyclic word; the deletion's cut moves, so only the cycle is equal — as printed, "cyclic Gauss word"); (c),(d) both identifications commute with the pairing `visitTwin` |
| "and fix an independent set S in their common interlacement graph" | `common_interlacement`, `independent_supports` | the four interlacement graphs correspond under the identifications (`GeometricInterlaces h0 x y ↔ Interlaces hn1 hPb (T x) (T y)`, and with `fusionCrossingEquiv`), so the fixed centre-independent `S` is a decomposition (`IsDecomposition = ∈ independentSupports`) on each side and on the deletion |
| "In each of these four configurations mark the traversal circle at every original vertex and every crossing visit, exchange the two outgoing successors at the two visits of every selected crossing — the reconnection of def:smoothing with conv:selected-visits — and trace the resulting oriented closed cycles by the inherited straight subsegments." | sides: `side_smoothing : ∀ b, SmoothingData hn1 hPb (sideSupport …)`; deletion: `deletion_smoothing : SmoothingData hn hQ (deletionSupport …)`; centre: `centre_marks`, `centre_successor`, `centre_reconnection`, `centre_traced` | `SmoothingData` (SM/SmoothingDefinition.lean:40-138) is the accepted def:smoothing packet: marks, `ρ_S = ρ ∘ selectedMarkPerm`, cycles, traced curve, straight subsegments. At the centre: marks = centre vertices at `(i,0)` and centre visits at their own centre parameter, pairwise distinct positions (`centre_marks`); the successor is the centre circle's own (`centre_successor`: `¬ traversalBetween (pos a) (pos u) (pos (ρ a))` for all `u`); the exchange is the centre's own selected swap (`centre_reconnection`); the traced cycle is the cycle of centre points in inherited order and each piece from a mark to its `ρ_S`-successor is a straight subsegment of the centre's edge of the outgoing slot (`centre_traced`) |
| "These oriented closed polygonal cycles are the carriers of S in that configuration." | `carriers_are_cycles` | `owner a = owner a' ↔ ρ_S.SameCycle a a'` on sides and deletion (`owner_eq_iff`); the centre family is indexed by the side's cycles by construction |
| "On the two generic sides they are the carriers of Definition def:smoothing;" | `side_carriers_smoothing` | `componentPlaneCycle = map markPoint componentMarkList` — the side family *is* the accepted one (rfl) |
| "at the centre and on the deletion the same words define them, no genericity being assumed." | `centre_not_generic`, `centre_positions_geometric`, `centre_side_independent` (+ `deletion_smoothing`) | `¬ Generic g.center` (`g.center_not_generic`); the centre positions are the centre's own crossing parameters (rfl); the centre family is independent of the side used (traced cycles and corner cycles agree under `sideToSide`) |

### cor:flat-carriers (sm-3:805-835) → `structure FlatCarriersData … (br : Bool) : Prop` (Statement_A.lean:437-708)

Parameters as above plus `br` = the right side; fields `right_side : IsRightSide g j br t`,
`left_side : IsLeftSide g j (!br) t`.

| clause | field | exact rendering |
|---|---|---|
| (i) "The carriers correspond under their named traversal arcs." | `correspond_sides`, `correspond_deletion` | `Bijective (sideToSide br (!br))` and `sideToSide (owner_r a) = owner_l (sideMarkTransport a)` for every mark `a`; `∀ b, Bijective (sideToDeletion b)` and `sideToDeletion (owner_b a) = owner_Q (sideToDeletionMark a)` for every mark `a ≠ Sum.inl j`. Side ↔ its centre copy is the identity of `SideCarrier` by construction. |
| (i) "Exactly one contains μ_j." | `unique_mu` | on each side `P(t) j ∈ componentPlaneCycle q ↔ q = muCarrier` and at the centre `μ_j ∈ centrePlaneCycle q ↔ q = muCarrier` (`muCarrier = owner (Sum.inl j)`) — the plane point `μ_j` lies on exactly one carrier |
| (i) "The central copy of that carrier differs from its deletion copy only by the positive-flat subdivision at μ_j;" | `central_deletion_subdivision` | for both sides: the centre mark cycle of `muCarrier` with the mark `Sum.inl j` removed equals (as `Cycle Plane`) the deletion copy's `componentPlaneCycle`; the same for the corner cycles (`ccpCornerList` mapped to points); and `StrictBetween (centre point of ρ_S⁻¹ (Sum.inl j)) μ_j (centre point of ρ_S (Sum.inl j))` — the two incident segments at `μ_j` are positive multiples of the fused direction (eq. flatpr:fusion) |
| (i) "every other central carrier is unchanged by deletion." | `others_unchanged` | `q ≠ muCarrier → centrePlaneCycle q = componentPlaneCycle_Q (sideToDeletion q)` and corner cycles equal |
| (i) "Every carrier has nonzero segments" | `nonzero_segments` | all four configurations, at both levels: every inherited subsegment (mark → `ρ_S`-successor) has distinct endpoints; every corner-polygon edge `≠ 0` |
| (i) "and no antiparallel corner;" | `no_antiparallel` | `¬ ∃ r < 0, edge Q k = r • edge Q (k-1)` for the corner polygons of sides, centre copies, deletion |
| (i) "except for that one central zero turn, all corner turns are nonzero." | `turns_nonzero` | sides/deletion: `turn (ccpCornerPolygon q) k ≠ 0`; centre: `turn (centreCornerPolygon q) k = 0 ↔ ccpCornerMark q k = Sum.inl j` (exactly one zero turn, at `μ_j`) |
| (ii) "Corresponding carriers have the same retained self-crossing visits, pairing, signs and positive over/under bits." | `same_crossings` | retained crossings correspond right ↔ left (`crossingTransport`), side ↔ deletion (`fusionCrossingEquiv ∘ crossingTransport⁻¹`), centre copy ↔ side (`centreCarrierCrossings`); both visits (twins) of a retained crossing lie on the corresponding carriers; for every crossing pair `{i,k}`: `crossingSign` equal in the four configurations (`crossingSign Q (fusionIndex j i) (fusionIndex j k)` for the deletion) and the positive over/under bits `0 < det(d_i, d_k)` agree |
| (ii) "They have the same signed rotation and hence the same absolute rotation." (round 4: covers the centre copy) | `same_rotation` | `rotationNumber (ccpCornerPolygon_l (sideToSide q)) = rotationNumber (ccpCornerPolygon_r q)`; for both sides `rotationNumber (ccpCornerPolygon_Q (sideToDeletion q)) = rotationNumber (ccpCornerPolygon_b q)` and `rotationNumber (centreCornerPolygon q) = rotationNumber (ccpCornerPolygon_b q)`; the same three with `|·|` |
| (ii) "Every corresponding corner away from μ_j has the same turn sign on both sides and in the deletion." | `same_turn_signs` | a corner is a corner mark `ccpCornerMark q k`; for `ccpCornerMark q k ≠ Sum.inl j` there is a corner `k'` of the corresponding carrier with `ccpCornerMark _ k' = T (ccpCornerMark q k)` and equal `turn` (right → left, and side → deletion) |
| (broadening, flagged) | `centre_turn_signs` | the centre copy has the same turn as its side at every corner `≠ Sum.inl j` (the printed proof's "all surviving corner signs … agree among the configurations", sm-3:875-876; not a printed sentence of (ii)) |
| (ii) "The extra corner at μ_j is right on the right side and left on the left side." | `extra_corner_mu` | `Sum.inl j` is a corner mark of `muCarrier br`; at it `turn = -1` on the right side `br` and `turn = 1` on the left side `!br` |
| (iii) "Define a carrier's selector to be 1 if all its turns are right, (−1)^c if all its c turns are left, and 0 if its turns are mixed." | `selector_def` + definitions `cornerSelector`, `carrierSelector` | the three defining clauses of `cornerSelector` and `carrierSelector = cornerSelector ∘ ccpCornerPolygon` (`c = ccpCornerCount`) |
| (iii) `W_right − W_left = W_del` for the carrier through μ_j | `selector_identity` | `carrierSelector_r (muCarrier br) - carrierSelector_l (muCarrier (!br)) = carrierSelector_Q (sideToDeletion br (muCarrier br))` |
| (iii) "All other corresponding carrier selectors agree." | `selector_others` | `q ≠ muCarrier br → carrierSelector_l (sideToSide q) = carrierSelector_r q ∧ carrierSelector_Q (sideToDeletion q) = carrierSelector_r q` |
| closing sentences ("geometric and combinatorial carrier data … no assignment of a state-sum value at the flat centre") | none | non-definitional; no field |

The theorem `flat_carriers` (Statement_A.lean:710-723): under the full hypotheses of lem:flat-sides
(`hn g hz hb hc hsc`), `∃ δ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t < δ, ∃ hs : CommonSupports g t,
(∀ b, IsRightSide ∨ IsLeftSide) ∧ ∀ S independent, ∀ br, IsRightSide g j br t → FlatCarriersData …`.
`flat_carriers_definition` (:423-435) has the same shape without `hsc` and the side clause.

## 2. Indexing decisions and conventions

* **Right/left.** lem:flat-sides names the sides by the sign of `τ_j(t) = sgn det(d_{j-1}, d_j)`,
  which changes sign at 0 (`hsc : g.SignChanges (fun P => (turn P j : ℝ))`, GermSignChange.lean:10:
  `turn (sideTuple true t) j * turn (sideTuple false t) j < 0`). `turn = 1` is a left turn
  (def:chirotope, UniformDefinition.lean header), so the *right* side is the side with `turn … j = -1`.
  The germ's `Bool` (`true` = positive parameter) is NOT the right/left label; the structure takes
  `br` with `right_side : IsRightSide g j br t` and uses `!br` for the left side. `flat_carriers`
  quantifies over `br` with hypothesis `IsRightSide g j br t`; `left_side` is derived (turn product
  `< 0` plus `SignType` case analysis, verified in scratch).
* **Where `S` lives.** At the centre (`Finset (Crossing g.center)`), because both sides and the
  deletion are compared to the centre in `FlatSidesData` (`GeometricRecordsAgree` centre ↔ side,
  `FlatFusionData` centre ↔ deletion). Independence is stated with `GeometricInterlaces
  (flatCentreGeometry …)` (SM/GeometricInterlacement.lean:16), which is definitionally `Interlaces`
  on a generic polygon (`geometricInterlaces_iff_generic : … ↔ … := Iff.rfl`, :38).
* **Where carriers live.** Side carriers: `SideCarrier hn g t hs b S = Component (flat_hn1 hn)
  (g.sideTuple b t).property (sideSupport g t hs b S)`; deletion: `DeletionCarrier`. Centre carriers
  are indexed by `SideCarrier … b S` for either `b`; `centre_side_independent` shows the two
  indexings give the same centre cycles under `sideToSide`. The correspondence side ↔ centre copy
  is therefore the identity — this is exactly the printed proof's "the successor permutation
  before smoothing [is identified]; exchanging the same selected successors … gives the same
  cycles".
* **`hs` as a parameter.** `CommonSupports g t` is a `Prop`; the definitions need it (to form
  `visitTransport`). The theorems produce it existentially (`∃ hs`), which is the strong form.
* **`hn1 = flat_hn1 hn : 3 ≤ n + 1`** everywhere the accepted `Generic`-parametrized machinery is
  used on the `(n+1)`-gons; `hn : 3 ≤ n` for the deletion (`n`-gon).

## 3. The definitions (Statement_A.lean line, rationale)

1. `markTransport` (:73) — `Equiv.sumCongr (Equiv.refl _) (visitTransport hs)`; the mark identification through the common crossing set.
2. `geometricMarkPosition` (:81) — `markPosition` without genericity (uses `geometricVisitPosition`, SM/GeometricVisits.lean:12, which needs only `CrossingGeometry`); on a generic polygon definitionally `markPosition` (as `geometricVisitPosition_eq_generic` is `rfl`).
3. `geometricMarkPoint` (:87), 4. `markPoint` (:91) — plane points of marks.
5. `carrierMap` (:97) — `owner (T (Quotient.out q))`; the induced carrier map (real function; cor (i) proves it is the bijection). Verified in scratch: `carrierMap T (owner a) = owner (T a)` reduces to `SameCycle` transport under `T` plus `Quotient.out_eq`.
6. `cornerSelector` (:105), 7. `carrierSelector` (:109).
8. `flat_hn1` (:117), 9. `flatCentreGeometry` (:123) = `flat_crossingGeometry` (SM/FlatCrossingGeometry.lean:12), 10. `flatDeletionGeneric` (:131) = `generic_deleteVertex` (SM/DeletionGeneric.lean:31) — proof-valued abbreviations (theorems).
11. `CommonSupports` (:140). 12. `IsRightSide` (:145), 13. `IsLeftSide` (:150).
14. `sideSupport` (:155), 15. `deletionSupport` (:160), 16. `SideCarrier` (:168), 17. `DeletionCarrier` (:173), 18. `muCarrier` (:180).
19. `centreMarkPosition` (:189), 20. `centreMarkPoint` (:197), 21. `centreSegment` (:205), 22. `centrePlaneCycle` (:217), 23. `centreCornerPolygon` (:227), 24. `centreCarrierCrossings` (:238) — the centre configuration by transport.
25. `sideMarkTransport` (:247), 26. `deletionMark` (:256), 27. `sideToDeletionMark` (:264) — mark identifications; 28. `sideToSide` (:273), 29. `sideToDeletion` (:280) — carrier correspondences.

Structures: `FlatCarriersDefinitionData` (:293, 14 fields), `FlatCarriersData` (:437, 19 fields).
Theorems: `flat_carriers_definition` (:423), `flat_carriers` (:710), both `sorry`.

## 4. Fidelity discussion: STRONGER / WEAKER than printed

Faithful renderings of "the same words define them" at the centre: the printed definition says
"mark the traversal circle at every original vertex and every crossing visit [at the centre],
exchange the two outgoing successors at the two visits of every selected crossing, and trace …".
The transport design does not re-run the sorting at the centre; instead it takes the side's marked
circle and successor and *proves* (fields `centre_marks`, `centre_successor`, `centre_reconnection`,
`centre_traced`) that, read at the centre's own positions (which exist without genericity by
lem:flat-sides (ii)), they are the centre's own marks, cyclic successor, selected swap and straight
subsegments. Since the cyclic successor of a finite set of distinct points on a circle is
characterised by "no point strictly between a point and its successor", `centre_successor`
determines `ρ` intrinsically; hence the transported carriers coincide with what the same words
define. This is the printed proof's own argument (sm-3:837-840) and makes the correspondence
side ↔ centre copy of cor (i) definitional (not a weakening: the printed clause (i) still has
content for right ↔ left and side ↔ deletion, and the def row certifies the identification).

* **Weaker hypotheses (stronger rows):** `flat_carriers_definition` omits `hsc` (the sign change
  is irrelevant to defining carriers). Both theorems produce `∃ hs` (the common supports) rather
  than assuming it.
* **Stronger than printed (flagged in docstrings):**
  - `nonzero_segments` is stated at both the mark level (each inherited subsegment) and the corner
    level (each corner-polygon edge), in all four configurations; the printed sentence is about
    "segments" of a carrier, and the printed proof (sm-3:849-851) argues at the mark level.
  - `centre_turn_signs` (turn agreement of the centre copy away from `μ_j`) is a separate flagged
    field; it is the proof's sentence sm-3:875-876, not a sentence of clause (ii).
  - `same_crossings` states sign/over-under agreement for *all* crossing pairs `{i,k}` of the
    common crossing set, not only for retained self-crossings; this is what lem:flat-sides (ii),(iii)
    give and what the printed sentence needs.
  - `common_gauss_word` states the centre ↔ side identification at the level of the Gauss *list*
    (cut at label 0), which is what `GeometricRecordsAgree` gives; for the deletion only the
    cyclic word (cut moves).
  - `central_deletion_subdivision`/`others_unchanged` compare the *mark* cycles and the *corner*
    cycles as `Cycle Plane` (rotation-invariant), the exact meaning of "differs only by the
    subdivision at μ_j" / "unchanged".
* **Weaker/other than printed:**
  - "the carriers correspond under their named traversal arcs": the arcs are represented by their
    marks (the arc from `ρ_S⁻¹ a` to `a` is named by `a`, conv:selected-visits); correspondence is the
    compatibility `carrierMap T (owner a) = owner (T a)`. For the deletion the arc of `μ_j` has no
    counterpart, so compatibility is asserted for `a ≠ Sum.inl j` only (as the printed "differs only
    by the subdivision at μ_j" requires).
  - The deletion's `deletionMark (Sum.inl j)` is a junk value (`Sum.inl (-1)`); every clause using
    the map excludes `Sum.inl j`.
  - `unique_mu` reads "contains μ_j" as membership of the plane point `μ_j` in the traced cycle
    (as a `Cycle Plane`); it does not additionally say the mark `Sum.inl j` is the only mark at that
    point (that is the proof).
  - Rotation is `rotationNumber` on the corner polygons (def:uniform's `carrierRotation`
    unfolds to it, SM/UniformDefinition.lean:43); for the centre copy `centreCornerPolygon`.
  - Absolute rotation is `|rotationNumber …|` on ℝ.

## 5. Reuse list (accepted library; file:line)

Hypotheses/flat geometry: `FlatSidesData`, `flat_sides` SM/FlatSides.lean:17-46,50; `FlatFusionData`,
`flat_fusion_data` SM/FlatFusionData.lean:13-53,55; `GeometricRecordsAgree` SM/GeometricRecords.lean:61-67
(`geometricGaussList_transport` :33, `geometricGaussWord_transport` :49); `CrossingParameterOrderAgrees`
SM/GeometricTransport.lean:10; `geometric_visitKey_lt_transport` :33; `flat_crossingGeometry`
SM/FlatCrossingGeometry.lean:12; `flat_germ_crossingGeometry` SM/FlatLocal.lean:39; `generic_deleteVertex`
SM/DeletionGeneric.lean:31; `WallGerm`, `center`, `sideTuple` SM/WallGerm.lean:13,27,47; `SignChanges`
SM/GermSignChange.lean:10; `deleteVertex` SM/DeletedTuple.lean:13; `deletionIndex` SM/DeletionIndices.lean:11;
`fusionIndex` SM/FusionIndices.lean:10 (`fusionIndex_deletionIndex` :15); `fusionCrossingEquiv`
SM/FusionCrossings.lean:91; `fusionVisitEquiv`, `fusionVisit_edge`, `fusionVisit_pairing` SM/FusionVisits.lean:39,54,60;
`crossingSign_fusion`, `positive_over_fusion`, `det_fusion` SM/FusionSigns.lean:19,28,10; `geometricGaussList_fusion_rotation`,
`geometricGaussWord_fusion` SM/FusionGaussWord.lean:33,58; `geometric_interlaces_fusion` SM/FusionInterlacement.lean:24;
`fusionVisitKey_compression` SM/FusionKey.lean:72; `sorted_map_monotone_cut_rotation` SM/SortedCompressedCut.lean:8.

Crossings/visits: `IsCrossing`, `Crossing`, `crossingPoint`, `crossingSign` SM/Crossings.lean:12,15,41,80;
`Visit`, `visitParameter`, `visitPosition` SM/GaussVisits.lean:17,45,48; `crossingTransport`, `visitTransport`
SM/CrossingTransport.lean:12,18; `CrossingGeometry`, `crossingPoint_injective_of_geometry` SM/CrossingGeometry.lean:11,79;
`crossingPoint_ne_vertex_of_geometry` SM/CrossingVertexExclusion.lean:29; `geometricVisitPosition`, `geometricGaussList`,
`geometricGaussWord`, `geometricVisitPosition_eq_generic`, `geometricGaussList_eq_generic` SM/GeometricVisits.lean:12,49,56,60,68;
`GeometricInterlaces`, `geometricInterlaces_iff_generic` SM/GeometricInterlacement.lean:16,38; `Interlaces` SM/Interlacement.lean:16;
`independentSupports`, `mem_independentSupports_iff` SM/InterlaceSupports.lean:33,46; `IsDecomposition`
SM/DecompositionDefinition.lean:15; `gaussList`, `gaussWord` SM/GaussWord.lean:20,88; `traversalEvaluation`, `traversalKey`,
`traversalBetween` SM/Traversal.lean:14,16,73; `continuousAt_edgeParameter_of_geometry` SM/GeometricParameters.lean:58.

Carriers: `Mark`, `markPosition`, `markList` SM/CarrierMarks.lean:32,36,84; `markSuccessor`, `nextMark_no_mark_between`
SM/CarrierSuccessor.lean:66,100; `selectedMarkPerm`, `smoothingSuccessor`, `Component`, `owner`, `owner_eq_iff`,
`owner_surjective` SM/CarrierSmoothing.lean:33,76,122,128,133,153; `visitTwin`, `visitTwin_unique`, `selectedVisitTwin`
SM/CarrierVisitTwin.lean:34,60,80; `componentMarkList`, `componentPlaneCycle`, `componentMarkList_data`,
`componentMarkList_getElem_successor`, `componentTraceEdge_data` SM/CarrierClosedTrace.lean:54,61,67,85,116;
`IsTrueCorner`, `componentCornerCycle` SM/CarrierTrueCorners.lean:41,84; `ccpOutSlot`, `ccpInEdge`, `ccpCornerList`,
`ccpCornerCount`, `ccpCornerMark`, `ccpCornerPolygon`, `ccpCornerMark_exists`, `ccpCornerPolygon_edge`(:498),
`ccpCornerPolygon_turn_det`, `ccp_corner_directions_det_ne_zero`, `ccpCornerPolygon_turn_ne_zero`,
`ccpCornerPolygon_turn_eq_sign`, `ccpCornerPolygon_turn_vertex`, `ccpCornerPolygon_turn_smoothing`,
`ccpCornerPolygon_edge_ne_zero`, `ccpCornerPolygon_not_antiparallel`, `ccpCornerPolygon_regular`,
`ccpCornerCount_ge_three`, `carriers_clause_ii` SM/CarrierCornerPolygon.lean:39,45,317,341,350,357,392,498,536,550,579,588,598,609,659,668,679,691,822;
`carrierCrossings`, `mem_carrierCrossings` SM/CarrierCrossings.lean:56,66; `smoothingSegment` (+`_length_pos`)
SM/CarrierAffineSegments.lean:69; `SmoothingData`, `smoothing_data` SM/SmoothingDefinition.lean:40,150;
`CarriersLemmaData`, `carriers_lemma` SM/CarriersLemma.lean:43,125; `independent_successor_components`
SM/CarrierComponentCount.lean:112; `sameCycle_congr_of_eqOn_bijOn` SM/CarrierAmbientTransport.lean:54.

Rotation/turns: `turn`, `turn_det`, `chi` SM/Chirotope.lean:13,87,10; `Regular`, `principalTurn`, `regular_iff_edges`
SM/RegularLocus.lean:12,15,18; `rotationNumber`, `rotationNumber_integer`, `rotationNumber_shift` SM/RotationNumber.lean:10,45,53;
`continuousAt_principalAngle`, `rotationNumber_family_constant`, `rotationNumber_path_constant` SM/RotationContinuity.lean:18,45,58;
`rotationNumber_locally_constant` SM/RegularPerturbation.lean:46; `principalAngle_smul` SM/AngleScaling.lean:12;
`StrictBetween`, `strictBetween_fusion` SM/StrictBetween.lean:9,19; `carrierRotation`, `CarrierUniform` SM/UniformDefinition.lean:43,28.

## 6. Proof-effort estimate per field (lines of Lean, including shared infrastructure once)

Shared infrastructure (new lemmas, §7): mark-order transport centre ↔ side and `ρ`/`ρ_S`
equivariance (~130), `componentMarkList` transport (~80), mark-list fusion rotation and skip-`j`
equivariance (~200), `centreCornerPolygon_edge` (~80), rotation continuity in `t` (~250),
`rotationNumber_deleteVertex_flat` (~60). ≈ 800.

Def row (≈ 380 incl. its share): `common_gauss_word` 20 (parts verified in scratch);
`common_interlacement` 6 (verified); `independent_supports` 25; `side_smoothing`/`deletion_smoothing` 4;
`centre_marks` 36 (evaluations verified); `centre_successor` 90 (uses the order transport);
`centre_reconnection` 15 (part 1 `rfl`, verified; part 2 uses the pairing lemma, verified);
`centre_traced` 60 (part 1 `rfl`); `carriers_are_cycles` 2; `side_carriers_smoothing` 0 (`rfl`);
`centre_not_generic` 1; `centre_positions_geometric` 0 (`rfl`); `centre_side_independent` 120.

Cor row (≈ 1300 beyond infrastructure): `right_side`/`left_side` 10 (verified pattern);
`correspond_sides` 60; `correspond_deletion` 280 (bijection of marks away from `j`, skip-`j`
equivariance, `SameCycle` transport, `carrierMap` bijectivity); `unique_mu` 80; `central_deletion_subdivision`
190 (mark cycle 80, corner cycle 50, `StrictBetween` 60); `others_unchanged` 70; `nonzero_segments` 140
(centre corner edges need `centreCornerPolygon_edge`); `no_antiparallel` 50; `turns_nonzero` 40;
`same_crossings` 120 (sign parts verified as one-liners); `same_rotation` 390 (centre = deletion 140 via
the flat-vertex deletion lemma + corner-list rotation; side = centre 250 via continuity in `t`);
`same_turn_signs` 100; `centre_turn_signs` 40; `extra_corner_mu` 10; `selector_def` 12 (verified);
`selector_identity` 80; `selector_others` 50.

**Total estimate: ≈ 2200 lines** (range 1800–2800).

## 7. Riskiest points and the auxiliary statements that are missing

1. **Rotation equality side ↔ centre copy (`same_rotation`, parts 2b/4b) — highest risk.** The
   printed proof is a limit argument in `t`. Intended auxiliary:
   `theorem flat_carrier_rotation_side_eq_centre : ∃ δ, 0 < δ ∧ ∀ t, t.val < δ → ∀ hs b S q,
   rotationNumber (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q)
   = rotationNumber (centreCornerPolygon hn g hz hb hc t hs b S q)`. Route: the corner marks of `q`
   are combinatorially constant in `t` (all sides share supports and visit order with the centre,
   `FlatSidesData`), so `s ↦ (corner polygon at parameter s)` is a family
   `F : Set.Ioo (-δ) δ → LabelledTuple k` continuous at `0` (vertices by `g.continuous_curve`,
   crossing points by `continuousAt_edgeParameter_of_geometry` at the centre) with `F 0 =
   centreCornerPolygon q` Regular (fields `nonzero_segments`, `no_antiparallel`); then
   `rotationNumber_locally_constant` (RegularPerturbation.lean:46) gives `∀ᶠ Q in 𝓝 (F 0), rot Q =
   rot (F 0)` and continuity at `0` gives the `δ`. Uniformity of `δ` over finitely many `S` and
   carriers: `Filter.eventually_all` over the finite index sets. Indexing carriers uniformly across
   `t` requires transporting `SideCarrier … t` along `t` through the centre marks (same machinery
   as `sideToSide`). Alternative: `rotationNumber_family_constant` on the connected side interval
   plus a limit at `0`; same ingredients.
2. **Deletion mark order = centre order with `j` skipped (`correspond_deletion`,
   `central_deletion_subdivision`, `others_unchanged`).** Missing:
   `theorem markList_fusion_rotation : (((markList hn1 hPb).filter (· ≠ Sum.inl j)).map
   (sideToDeletionMark …)).IsRotated (markList hn hQ)` — the mark analogue of
   `geometricGaussList_fusion_rotation` (FusionGaussWord.lean:33), which handles visits only; vertices
   must be added to the compressed-key argument (`fusionKey`, `sorted_map_monotone_cut_rotation`).
   Then `theorem smoothingSuccessor_deletion : ∀ a ≠ Sum.inl j, (ρ_S a ≠ Sum.inl j →
   T (ρ_S a) = ρ'_S' (T a)) ∧ (ρ_S a = Sum.inl j → T (ρ_S (Sum.inl j)) = ρ'_S' (T a))` with
   `T = sideToDeletionMark`, and a `SameCycle`-with-one-skipped-point transport (no Mathlib lemma;
   ~60 lines by induction on `zpow` or via `sameCycle_congr_of_eqOn_bijOn`, CarrierAmbientTransport.lean:54).
3. **Mark order transport centre ↔ side (`centre_successor`, `centre_side_independent`,
   `correspond_sides`).** Missing: `theorem centreMarkKey_lt_iff : traversalKey (centreMarkPosition a)
   < traversalKey (centreMarkPosition a') ↔ markKey hn1 hPb.1 a < markKey hn1 hPb.1 a'` (from
   `traversalKey_lt_iff` + `geometric_visitKey_lt_transport` + `CrossingParameterOrderAgrees` from
   `FlatSidesData`; vertex-vs-visit comparisons are by edge index and `0 < parameter`), then
   `markSuccessor` equivariance between the two sides and `componentMarkList` transport
   (`(componentMarkList_r q).map T = componentMarkList_l (sideToSide q)`, mirroring
   `geometricGaussList_transport`, GeometricRecords.lean:33-47).
4. **Centre corner-polygon edges (`nonzero_segments`, `no_antiparallel`, `turns_nonzero`,
   `centre_turn_signs`).** Missing: `theorem centreCornerPolygon_edge : ∃ c : ℝ, 0 < c ∧
   edge (centreCornerPolygon … q) k = c • edge g.center (ccpOutSlot hn1 hPb St (ccpCornerMark … q k)).1`
   — the centre analogue of `ccpCornerPolygon_edge` (:498); the block structure is the side's
   (`ccp_block_compression` :159), only the centre parameters enter. Then turns at the centre are
   `sign det(d_in, d_out)` of centre directions: zero iff at `μ_j` (`FlatSidesData.4`), transverse at
   selected visits (`CrossingGeometry`), and equal to the side's sign by `chi` constancy
   (`FlatSidesData`: `chi (g.curve t) a b c = chi g.center a b c` off `turnSupport j`) and
   `GeometricRecordsAgree.2.2.2.2` (crossing signs).
5. **Centre = deletion rotation (`same_rotation` 2a).** Missing:
   `theorem rotationNumber_deleteVertex_flat {m} [NeZero m] (Q : LabelledTuple (m+1)) (k) (hreg : Regular Q)
   (hk : StrictBetween (Q (k-1)) (Q k) (Q (k+1))) : rotationNumber (deleteVertex Q k) = rotationNumber Q`
   (principal turn at `k` is `0`; the neighbours' principal angles are unchanged by
   `principalAngle_smul`, AngleScaling.lean:12, since `d_{k-1}, d_k` are positive multiples of the
   fused edge), plus the identification `∃ a, ccpCornerPolygon_Q (sideToDeletion q) = shift a
   (deleteVertex (centreCornerPolygon q) k_j)` from the corner-list rotation (item 2) and
   `rotationNumber_shift`.
6. **`unique_mu`** needs injectivity of vertices and "no crossing at a vertex" in each
   configuration: all in `FlatSidesData` (centre: `.1`; every `t` on the radius: `∀ c k, crossingPoint c
   ≠ g.curve t k`) and `g1_vertices_injective` on the sides. Low risk.
7. **Selector table (`selector_identity`).** Needs `ccpCornerCount (muCarrier (!br)) = ccpCornerCount
   (muCarrier br) = ccpCornerCount (sideToDeletion (muCarrier br)) + 1` (from the corner-list
   correspondences) and the turn bijections; then the printed 3-row table (`pow_succ`). Medium.

Points NOT at risk (verified in `/tmp/ScratchA.lean`, compiled against the draft): `centre_reconnection.1`,
`centre_traced.1`, `side_carriers_smoothing`, `centre_positions_geometric`, `selector_def.2` are `rfl`;
`centre_marks` evaluations, `carriers_are_cycles` (`owner_eq_iff`), `same_crossings.3`
(`Finset.mem_map_equiv`), `selector_def.1`, the pairing commutations for both identifications
(`visitTwin_unique`), the right/left derivation from the turn product, and the extraction of
`common_gauss_word.1`, `common_interlacement.1/.2`, `common_gauss_word.2` and the sign clauses from
`GeometricRecordsAgree` / `geometricGaussWord_fusion` / `geometric_interlaces_fusion` /
`crossingSign_fusion` all typecheck (definitional equalities `geometricGaussList = gaussList`,
`GeometricInterlaces = Interlaces` on generic polygons, proof-irrelevance of `hs`).

## 8. Compile status

`cd work/lean && lake env lean ../drafts/flatcarriers/Statement_A.lean` → only
`declaration uses 'sorry'` at :423 (`flat_carriers_definition`) and :710 (`flat_carriers`).
