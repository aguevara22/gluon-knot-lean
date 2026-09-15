# PLAN B — prop:C-chamber (chamber constancy of the corner state sum)

Target: `SM.C_chamber : CChamberData` of `work/drafts/CChamber_statement.lean` (fixed statement).
Skeleton: `work/drafts/cchamber/Skeleton_B.lean` — typechecks with `lake env lean` (53 declarations
carry `sorry`, no errors; `#print axioms SM.C_chamber` = propext, sorryAx, Classical.choice,
Quot.sound, SM.lit_homfly). `SM.C_chamber` is PROVED from the chain; every `sorry` is inside the chain.

Source: reference/SM/sm-4-knotlaws.tex:36-99. Emphasis of tag B: parametrize along a `Path` in
`GenericTuple n` and prove each ingredient of `C` is constant along the parameter (integer-valued
continuous / clopen arguments), then descend cyclically.

## 0. The route in one paragraph

`C(P) = (−1)^{ℓ(P)} Σ_{S uniform decomposition} (−1)^{|S|} ∏_{q carrier of S} c(q)` where every object
(`independentSupports`, `Component hn hP S`, `carrierCrossingCount`, `ccpCornerPolygon`, `positiveLift`)
is built from the *marked traversal* `Mark P = ZMod n ⊕ Visit P` sorted by `markKey`
(`markList`), its cyclic successor `markSuccessor` and the visit twin `visitTwin`. We introduce a
**mark transport** `Carrier.MarkTransport hn hP hQ`: a triple of bijections (vertices `vert`, crossings
`cross`, visits `visit`) with `visit_fst`, commuting with `visitTwin` (`twin_eq`), carrying the sorted
mark list of `P` to a *rotation* of that of `Q` (`markList_rotated`), preserving `Interlaces`
(`interlaces_iff`), vertex turns (`turn_eq`) and the smoothing-corner signs `sgn det(d_i,d_j)`
(`sign_eq`). From these nine fields the whole Carrier lane transports *generically* (section 1):
`markSuccessor`, `smoothingSuccessor`, `Component` (an `Equiv`), `owner`, `carrierCrossings`, `m_Q`,
`IsDecomposition`, `IsTrueCorner`, `ccpCornerList` (up to rotation), `ccpCornerCount`,
`ccpCornerPolygon` (= a recast + cyclic shift of the "transported corner polygon" read at `Q`'s
geometry), turn signs, `CarrierUniform`, `UniformDecomposition`, the index set `uniformDecompositions`,
`leftTurns`, and finally `cornerStateSum` **provided the corner coefficients agree** (`cornerStateSum_transport`).
The coefficient `c(q) = coeffAt (1 − m_Q − |r_Q|) 0 (homfly (positiveLift q))` agrees once `m_Q` (generic),
`r_Q` and `homfly` agree; these two are the only instance-specific inputs.

Two instances:
* **Path** `pathTransport hn γ s t : MarkTransport hn (γ s).2 (γ t).2` for `γ : Path P Q` in
  `GenericTuple n`. The nine fields come from accepted `SM.chambers`/`ChamberPaths` (constant chirotope
  ⇒ turns; constant crossing set ⇒ `crossingTransport`/`visitTransport`; constant same-edge parameter
  order ⇒ `CrossingParameterOrderAgrees` ⇒ the mark order is *literally* carried (`markList_transport`)
  and interlacement is carried by accepted `geometric_interlaces_transport`) plus one new continuity
  lemma for `crossingSign`. Then: the transported corner polygon `Φ t` is continuous in `t` (vertices
  move continuously, crossing points by Cramer) and regular for every `t` (it is a recast of the
  accepted regular `ccpCornerPolygon` at `γ t`), so `r_Q` is constant (`rotationNumber_family_constant`,
  lem:rot(ii)); and `Φ` is a `DeformData` between the positive lifts (generic at each time by
  `carrierShadow_generic` at `γ t`; the crossing pairs are constant by a clopen argument; positivity
  persists by sign continuity), so `homfly` agrees by `homfly_planar` (accepted lit:homfly) — this
  replaces the printed rp:record-polynomial/lp:core route.
* **Shift** `shiftTransport hn hP a : MarkTransport hn hP ((generic_shift a P).mpr hP)` for the cyclic
  relabelling `shift a P`. Fields from accepted `crossingShiftEquiv`, `visitShiftEquiv`, `interlaces_shift`,
  `turn_shift`, `crossingSign_shift`, and a rotation lemma for `markList` (template
  `gaussList_shift_rotation`). Points do not move, so the transported corner polygon *is* `ccpCornerPolygon`;
  `r_Q` agrees by `rotationNumber_shift`; the positive lifts differ by a cyclic re-indexing of the one
  component, a `Reparam` (`φ := traversalShift r`), so `homfly` agrees by `homfly_planar`.

Descent: `polygonProjection Q ∈ chamber (polygonProjection P)` ⇒ (accepted
`projection_labelledChamber_eq_chamber`) `∃ Q' ∈ labelledChamber P, polygonProjection Q' = polygonProjection Q`
⇒ (`projection_eq_iff`) `Q = genericShift a Q'`; `labelledChamber P` is path connected
(`labelledChambers_open_pathConnected`) so there is `γ : Path P Q'`; hence
`C(P) = C(Q') = C(genericShift a Q') = C(Q)`. This is the "descent" of the printed proof done with the
accepted saturated-clopen lemma instead of a locally-constant-function argument on the quotient; no
path lifting through the quotient is used.

## 1. Lemma list (exact statements are in the skeleton; here: name — statement gist — sketch — est. lines)

Notation: `τ : MarkTransport hn hP hQ`, `T := τ.toMark = Equiv.sumCongr τ.vert τ.visit`,
`S' := τ.support S = S.map τ.cross.toEmbedding`, `q' := τ.component S q`.

### 0. Recast helpers (`SM.recastTuple {k k'} (hk : k' = k) (f : LabelledTuple k) : LabelledTuple k'`, `fun j => f (Equiv.cast (congrArg ZMod hk) j)`) — all by `subst hk`
| # | lemma | statement | sketch | lines |
|---|---|---|---|---|
| 0.1 | `rotationNumber_recastTuple` | `rotationNumber (recastTuple hk f) = rotationNumber f` | `subst hk; rfl` (`Equiv.cast rfl` reduces) | 3 |
| 0.2 | `regular_recastTuple` | `Regular (recastTuple hk f) ↔ Regular f` | subst; rfl | 3 |
| 0.3 | `turn_recastTuple` | `turn (recastTuple hk f) j = turn f (Equiv.cast _ j)` | subst; rfl | 3 |
| 0.4 | `forall_turn_recastTuple` | `(∀ j, turn (recastTuple hk f) j = τ) ↔ ∀ j, turn f j = τ` | subst; rfl | 3 |
| 0.5 | `polyComp_recastTuple` | `PolyComp.mk k' h' (recastTuple hk f) = PolyComp.mk k h f` | subst; rfl | 3 |

### 1. Generic transport (namespace `Carrier.MarkTransport`)
| # | lemma | statement | sketch | lines |
|---|---|---|---|---|
| 1.1 | `markSuccessor_transport` | `markSuccessor hn hQ (T m) = T (markSuccessor hn hP m)` | `markList_rotated : (markList hQ) ~r (markList hP).map T`. `nextMark = List.next (markList)`; `List.isRotated_next_eq` (Mathlib Data/List/Cycle.lean:385) replaces `markList hQ` by `(markList hP).map T`; then a `List.next_map` for injective maps: prove via `List.next_getElem` (:282) + `List.getElem_map` on both sides, writing `m = (markList hP)[i]` (`List.mem_iff_getElem`, `mem_markList`), cf. `markSuccessor_getElem` (CarrierSuccessor.lean:100). | 35 |
| 1.2 | `selectedMarkPerm_transport` | `selectedMarkPerm S' (T m) = T (selectedMarkPerm S m)` | cases m; vertex: rfl (CarrierSmoothing.lean:41); visit: `selectedVisitTwin` unfolds by `v.1 ∈ S` (CarrierVisitTwin.lean:80-90), `mem_support` + `visit_fst` (`(visit v).1 = cross v.1`), `twin_eq`. | 15 |
| 1.3 | `smoothingSuccessor_transport` | `smoothingSuccessor hn hQ S' (T m) = T (smoothingSuccessor hn hP S m)` | unfold (CarrierSmoothing.lean:84: `(selectedMarkPerm S).trans (markSuccessor)`); 1.2 then 1.1. | 8 |
| 1.4 | `sameCycle_transport` | `(ρ_{S'}).SameCycle (T a) (T b) ↔ (ρ_S).SameCycle a b` | 1.3 gives `ρ_{S'} = T * ρ_S * T⁻¹` (ext); `Equiv.Perm.sameCycle_conj` (Mathlib GroupTheory/Perm/Cycle/Basic.lean:96) + `Equiv.symm_apply_apply`. | 20 |
| 1.5 | `component` (def) | `Component hn hP S ≃ Component hn hQ S'` | `Quotient.congr T (fun a b => (1.4).symm)` (Logic/Equiv/Defs.lean:884); `component_owner` is `rfl` (`Quotient.congr_mk`). Already written. | 0 |
| 1.6 | `carrierCrossings_transport` | `carrierCrossings hn hQ S' q' = (carrierCrossings hn hP S q).map τ.cross.toEmbedding` | `ext x`; write `x = τ.cross x₀` (surjective); `mem_carrierCrossings` (CarrierCrossings.lean:66: `x ∉ S ∧ ∀ v, v.1 = x → owner (Sum.inr v) = q`); visits of `cross x₀` are `visit w` (surjective, `visit_fst`); `component_owner`; `component` injective; `mem_support`. | 30 |
| 1.7 | `carrierCrossingCount_transport` | `carrierCrossingCount hn hQ S' q' = carrierCrossingCount hn hP S q` | 1.6 + `Finset.card_map` (`carrierCrossingCount_eq_card`, CarrierCrossings.lean:113). | 5 |
| 1.8 | `isDecomposition_transport` | `IsDecomposition hn hQ S' ↔ IsDecomposition hn hP S` | `mem_independentSupports_iff` (InterlaceSupports.lean:37); mimic `independentSupports_shift` (:112) with `interlaces_iff`, `mem_support`, `cross.injective/surjective`. | 25 |
| 1.9 | `isTrueCorner_transport` | `IsTrueCorner S' (T m) ↔ IsTrueCorner S m` | cases m (CarrierTrueCorners.lean:44); visit case `mem_support` + `visit_fst`. | 10 |
| 1.10 | `componentMarkList_transport` | `(componentMarkList hn hQ S' q') ~r (componentMarkList hn hP S q).map T` | `componentMarkList = markList.filter (owner = q)` (CarrierClosedTrace.lean:59). Filter of a rotation: `l.rotate k = drop ++ take`, `List.filter_append`, `List.isRotated_append` (Rotate.lean:432); `List.filter_map` moves the filter through `map T`; predicates agree by `component_owner` + `component` injectivity. | 30 |
| 1.11 | `ccpCornerList_transport` | `(ccpCornerList hn hQ S' q') ~r (ccpCornerList hn hP S q).map T` | `ccpCornerList = componentMarkList.filter IsTrueCorner` (CarrierCornerPolygon.lean:317); `List.IsRotated.filter`-style argument as in 1.10 with 1.9. | 15 |
| 1.12 | `ccpCornerCount_transport` | `ccpCornerCount hn hQ S' q' = ccpCornerCount hn hP S q` | `IsRotated.perm.length_eq`, `List.length_map` (CarrierCornerPolygon.lean:341). | 5 |
| 1.13 | `exists_ccpCornerMark_transport` | `∃ r, ∀ j, ccpCornerMark hn hQ S' q' (Equiv.cast _ j) = T (ccpCornerMark hn hP S q (j + r))` | 1.11 gives `m` with `(ccpCornerList hQ).rotate m = (ccpCornerList hP).map T` (or the other direction; `List.IsRotated` is `∃ m, l.rotate m = l'`); `ccpCornerMark j = list[j.val]` (:350); `List.getElem_rotate`, `List.getElem_map`; `r := -(m : ZMod k)`, `(Equiv.cast _ j).val = j.val` (subst lemma), `ZMod.val_add`/`Nat.add_mod`. | 40 |
| 1.14 | `exists_ccpCornerPolygon_transport` | `∃ r, ccpCornerPolygon hn hQ S' q' = recastTuple (1.12) (shift r (transportedCornerPolygon τ S q))` | funext j'; `ccpCornerPolygon_apply` (:361); write `j' = Equiv.cast _ j`; 1.13; unfold `recastTuple`, `shift`, `transportedCornerPolygon`. | 20 |
| 1.15 | `ccpCornerPolygon_transport_of_markList_eq` | if `markList hn hQ = (markList hn hP).map T` then `ccpCornerPolygon hn hQ S' q' = recastTuple (1.12) (transportedCornerPolygon τ S q)` | same as 1.10-1.14 with literal equalities (`List.filter_map`), `r = 0`. | 25 |
| 1.16 | `exists_turn_ccpCornerPolygon_transport` | `hS → ∃ r, ∀ j, turn (ccp hQ S' q') (Equiv.cast _ j) = turn (ccp hP S q) (j + r)` | take `r` of 1.13; case on `ccpCornerMark hP S q (j+r)`: vertex `i` → `ccpCornerPolygon_turn_vertex` (CarrierCornerPolygon.lean:598) on both sides (mark of `Q` is `Sum.inl (vert i)`), `turn_eq`; visit `v` (`v.1 ∈ S` by `ccpCornerMark_isTrueCorner`) → `ccpCornerPolygon_turn_smoothing` (:609) on both sides (mark of `Q` is `Sum.inr (visit v)`, `(visit v).1 ∈ S'`), `twin_eq`, `sign_eq`. `hS'` from 1.8. | 45 |
| 1.17 | `carrierUniform_transport` | `hS → (CarrierUniform hn hQ S' q' ↔ CarrierUniform hn hP S q)` | `CarrierUniform = ∃ τ ≠ 0, ∀ j, turn = τ` (UniformDefinition.lean:28); 1.16 with the bijections `j ↦ Equiv.cast _ j` and `j ↦ j + r` (`Equiv.addRight`). | 25 |
| 1.18 | `uniformDecomposition_transport` | `hS → (UniformDecomposition hn hQ S' ↔ UniformDecomposition hn hP S)` | `∀ q'` ↔ `∀ q` via `component` surjective; 1.17. | 15 |
| 1.19 | `mem_uniformDecompositions_transport` | `S' ∈ uniformDecompositions hn hQ ↔ S ∈ uniformDecompositions hn hP` | `mem_uniformDecompositions` (CornerStateSum.lean:140); 1.8 and 1.18 (1.18 needs `hS`; split on `IsDecomposition hn hP S`). | 15 |
| 1.20 | `leftTurns_transport` | `leftTurns Q = leftTurns P` | `leftTurns = #{i | turn = 1}` (Chirotope.lean:15); `Finset.card_bij` with `vert` and `turn_eq`, as `leftTurns_shift` (Chirotope.lean:107). | 15 |
| 1.21 | `cornerSlot_transport` | `carrierRotation agree → cornerSlot hn hQ S' q' = cornerSlot hn hP S q` | unfold `cornerSlot`, `carrierRotationInt` (CornerStateSum.lean:61,82); 1.7; rewrite `hrot`. | 10 |
| 1.22 | `cornerCoefficient_transport` | `hS → hrot → hH → cornerCoefficient hn hQ S' q' hS' = cornerCoefficient hn hP S q hS` | unfold `cornerCoefficient`/`cornerCoefficientWith` (:103-112); 1.21; `hH`. | 15 |
| 1.23 | `cornerProduct_transport` | `(∀ q, c(q') = c(q)) → cornerProduct hn hQ S' hS' = cornerProduct hn hP S hS` | `Fintype.prod_equiv (τ.component S)` (or `Equiv.prod_comp`) with `hcoef`. | 15 |
| 1.24 | `cornerStateSum_transport` | `(∀ S hS q, c(q') = c(q)) → cornerStateSum hn hQ = cornerStateSum hn hP` | `cornerStateSum` (:166): `(−1)^ℓ * Σ_{S ∈ uD.attach} (−1)^{|S|} * cornerProduct`. 1.20 for the prefactor. Turn the dependent sum into `Σ_{S ∈ uD} g S` with a total `g` (dite), exactly as in `cornerStateSum_eq_sum_independentSupports` (:174-210); then `uniformDecompositions hn hQ = (uniformDecompositions hn hP).map (Finset.mapEmbedding τ.cross.toEmbedding).toEmbedding` from 1.19 + `support_surjective`; `Finset.sum_map` (Mathlib BigOperators/Group/Finset/Defs.lean:396); termwise `support_card` and 1.23. | 60 |

Subtotal section 1: ≈ 500 lines.

### 2. Path instance (section `PathTransport`; `hn : 3 ≤ n`, `γ : Path P Q`, `P Q : GenericTuple n`)
| # | lemma | statement | sketch | lines |
|---|---|---|---|---|
| 2.1 | `markKey_lt_transport` | `hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s`, `ho : CrossingParameterOrderAgrees P Q` ⇒ `markKey hn hQ.1 (Sum.map id (visitTransport hs) a) < markKey hn hQ.1 (… b) ↔ markKey hn hP.1 a < markKey hn hP.1 b` | cases a, b. vertex/vertex: `markKey_vertex` (CarrierMarks.lean:77) both sides `i.val`. vertex/visit and visit/vertex: `markKey_visit` (:81) = `visitKey = traversalKey (visitPosition)`, `traversalKey_lt_iff` (Traversal.lean:45): key of visit is `edge.val + p` with `p ∈ (0,1)` (`visitPosition_interior`, GaussVisits.lean:68), edge preserved (`visitTransport_edge`, CrossingTransport.lean:27): `i.val < e.val + p ↔ i.val ≤ e.val` and `e.val + p < i.val ↔ e.val < i.val` (integers; `Nat.cast` arithmetic, `linarith`). visit/visit: `geometric_visitKey_lt_transport` (GeometricTransport.lean:33) with `generic_crossingGeometry` (CrossingGeometry.lean:24) and `geometricVisitKey_eq_generic` (GeometricVisits.lean:62, `rfl`). | 50 |
| 2.2 | `markList_transport` | same hyps ⇒ `markList hn hQ = (markList hn hP).map (Sum.map id (visitTransport hs))` | copy `geometricGaussList_transport` (GeometricRecords.lean:36-50): `List.perm_ext_iff_of_nodup` (nodup: `markList_nodup` :100, injective map), membership `mem_markList` (:106), then `List.Perm.eq_of_pairwise` with `markList_sorted` (:112), `markKey_injective` (:84) and 2.1 (`≤` version via `not_lt`). | 25 |
| 2.3 | `visitTransport_twin` | `visitTransport hs (visitTwin v) = visitTwin (visitTransport hs v)` | `visitTwin_unique` (CarrierVisitTwin.lean:60): same crossing (`visitTransport_crossing`, `visitTwin_crossing`), distinct (`visitTwin_ne` + injectivity). | 12 |
| 2.4 | `generic_family_crossingSign_constant` | `hF : Continuous F`, `IsCrossing (F s).val {i,j}` ⇒ `crossingSign (F s).val i j = crossingSign (F t).val i j` | `crossingSign = sign (det (edge i) (edge j))` (Crossings.lean:82); crossing persists at all `r` (`generic_family_crossing_constant`, ChamberPaths.lean:13); `det ≠ 0` at every `r` (`crossing_edgeParameter_det_ne_zero`, Chambers.lean:123); `continuous_edge` (GenericTopology.lean:15), `continuousAt_det` (ContinuousGeometry.lean:13), `continuousAt_sign_of_ne_zero`; `PreconnectedSpace.constant` as in `continuous_generic_chi`/`generic_family_chi_constant`. Alternative: `crossingSign P i j = chi P i (i+1) (j+1)` at a crossing (sign algebra) then `generic_family_chi_constant`. | 20 |
| 2.5 | `generic_family_crossingParameterOrderAgrees` | `CrossingParameterOrderAgrees (F s).val (F t).val` | unfold (GeometricTransport.lean:10); `generic_family_crossingOrder_constant hn hF s i j k hij hik t s` (ChamberPaths.lean:35). | 10 |
| 2.6 | `pathTransport.sign_eq` (field) | `crossingSign (γ t) (visit v).2 (visit (twin v)).2 = crossingSign (γ s) v.2 (twin v).2` | `visitTransport_edge` (rfl), 2.3, 2.4 with `hij : IsCrossing (γ s) {v.2.val, (visitTwin v).2.val}` from `visit_crossing_val_eq_pair` (CarrierCrossings.lean:216) / `crossing_support_partner`. | 8 |
| 2.7 | `pathTransport_toMark_self` | `(pathTransport hn γ s s).toMark m = m` | cases m; `crossingTransport = Equiv.subtypeEquivRight` so `Subtype.ext rfl`; `Sigma.ext`. | 10 |
| 2.8 | `continuous_path_crossingPoint` | `Continuous fun t => crossingPoint (crossingTransport (path_crossing_iff hn γ 0 t) c)` | `crossing_support_partner` gives `c.val = {i, j}`; `crossingPoint = edgePoint P i (crossingParameter …)` (`crossingParameter_spec`, Crossings.lean:74) and `crossingParameter_eq_of_support_pair` (CrossingTransport.lean:40) `= edgeParameter (γ t) i j`; `generic_family_edgeParameter_continuous` (ChamberPaths.lean:24); `edgePoint` continuous in (P, t) (`continuous_vertex`, `continuous_edge`, `Continuous.smul`). | 35 |
| 2.9 | `continuous_transportedCornerPolygon` | `Continuous fun t => (pathTransport hn γ 0 t).transportedCornerPolygon S q j` | unfold; the corner mark `ccpCornerMark (γ 0) S q j` is fixed; cases: `Sum.inl i` → value `(γ t).val i` (`markPosition_evaluation_vertex`, CarrierMarks.lean:52), continuous (`continuous_vertex ∘ continuous_subtype_val ∘ γ.continuous`); `Sum.inr v` → value `crossingPoint (crossingTransport _ v.1)` (`markPosition_evaluation_visit` :58, `visitTransport_crossing`), 2.8. | 25 |
| 2.10 | `transportedCornerPolygon_zero` | `(pathTransport hn γ 0 0).transportedCornerPolygon S q = ccpCornerPolygon hn (γ 0).2 S q` | funext; `ccpCornerPolygon_apply`; 2.7. | 10 |
| 2.11 | `regular_transportedCornerPolygon` | `hS → Regular ((pathTransport hn γ 0 t).transportedCornerPolygon S q)` | `ccpCornerPolygon_regular` (CarrierCornerPolygon.lean:679) at `(γ t)` for `S'`, `q'` (`hS'` by 1.8); rewrite with `ccpCornerPolygon_pathTransport` (skeleton, from 1.15 + 2.2) and 0.2. | 15 |
| 2.12 | `carrierRotation_path` | `hS → carrierRotation hn (γ 1).2 S'₁ q'₁ = carrierRotation hn (γ 0).2 S q` | `carrierRotation = rotationNumber ∘ ccpCornerPolygon` (UniformDefinition.lean:43); `ccpCornerPolygon_pathTransport` at `t=1` and 0.1 reduce to `rotationNumber (Φ 1) = rotationNumber (Φ 0)` with `Φ t := transportedCornerPolygon (pathTransport 0 t)`; `rotationNumber_family_constant` (RotationContinuity.lean:50) with `continuous_pi` from 2.9 and 2.11; 2.10 for `Φ 0`. | 30 |
| 2.13 | `carrierShadow_pathTransport` | `carrierShadow hn (γ t).2 S' q' hS' = (carrierShadow hn (γ 0).2 S q hS).withVertices (fun _ => Φ t)` | both are `Shadow.single ⟨_, _, _⟩` (LinkPositiveLift.lean:211-222, LinkMoves.lean:224 `withVertices`); `congr`/`Shadow.ext`-style on `comp`: `funext i`; `ccpCornerPolygon_pathTransport` + 0.5 (`polyComp_recastTuple`). | 30 |
| 2.14 | `deform_positiveLift_path` | `hS → Deform (positiveLift (γ 0) S q hS) (positiveLift (γ 1) S'₁ q'₁ hS'₁)` | `D := positiveLift (γ 0) …`, `V t := fun _ => Φ t`. `h0 : V 0 = D.Γ.vertices` by 2.10. `hgen t` by 2.13 ▸ `carrierShadow_generic` (LinkPositiveLift.lean:580). `hcross t x` by Link lemma 2c.1 (times `t`, `0`) and `h0`+`withVertices_vertices` (LinkMoves.lean:228). `Deform.of_family` (2c.2) gives `Deform D (D.deform (V 1) …)`; `D.deform (V 1) … = positiveLift (γ 1) …` by `eq_positiveLift_of_isPositive` (LinkPositiveLift.lean:633) with `deform_Γ` (LinkMoves.lean:440) + 2.13 and positivity from 2c.3 (`positiveLift_isPositive` :618 for `hpos`). Continuity `hV` from 2.9 (`Fin 1` index). | 50 |
| 2.15 | `homfly_positiveLift_path`, `cornerCoefficient_path`, `cornerStateSum_path_constant` | glue, already written | `homfly_planar` (LinkInterfaces.lean:382), `PlanarIsotopic.of_deform` (LinkMoves.lean:522), 1.22, 1.24, `Path.source/target`. | 0 |

Subtotal section 2: ≈ 330 lines.

### 2c. Link-layer lemmas (namespace `SM.Link`)
| # | lemma | statement | sketch | lines |
|---|---|---|---|---|
| 2c.1 | `Shadow.isCrossing_constant_of_generic_family` | `hV : ∀ i j, Continuous (fun t => V t i j)`, `hgen : ∀ t, (Γ.withVertices (V t)).Generic` ⇒ `(Γ.withVertices (V s)).IsCrossing x ↔ (Γ.withVertices (V t)).IsCrossing x` | `A := {t | IsCrossing_t x}` is clopen in `unitInterval` (connected ⇒ `isClopen_iff`, Mathlib Topology/Connected/Clopen.lean:114: `A = ∅ ∨ A = univ`). `IsCrossing x ↔ ∃ s u, x = {s,u} ∧ ¬Adjacent ∧ (seg s ∩ seg u).Nonempty` (LinkDiagram.lean:246); adjacency is label-only. **Closed**: `{t | (seg_t s ∩ seg_t u).Nonempty}` is the `Prod.fst` image of the closed set `{(t,α,β) ∈ I×I×I | tail_t s + α dir_t s = tail_t u + β dir_t u}` (`isClosedMap_fst_of_compactSpace`, `isClosed_eq`, `fun_prop`), template `isClosed_closedTripleMeet` (GenericTopology.lean:87). **Open**: at `t₀ ∈ A`, `Generic.crossingPoint_mem_interior` (LinkDiagram.lean:456) gives parameters in `(0,1)`, `Generic.transverse` gives `det ≠ 0`; `transverse_intersection_persists` (ContinuousGeometry.lean:50) gives `∀ᶠ t, ∃ s r ∈ (0,1), a t + s•u t = b t + r•v t` ⇒ segments meet ⇒ `t ∈ A`. | 110 |
| 2c.2 | `Deform.of_family` | same hyps + `h0 : V 0 = D.Γ.vertices` ⇒ `Deform D (D.deform (V 1) (hgen 1) (hcross 1))` | `DeformData` (LinkMoves.lean:462) with `γ t := V (Set.projIcc 0 1 zero_le_one t)`; `continuous`: `(hV i j).comp continuous_projIcc` restricted (`Continuous.continuousOn`); `start`: `Set.projIcc_left` + `h0`; `generic`/`crossings`: `hgen`/`hcross`; `stop`: `Set.projIcc_right` then `congr`/`simp` (proof arguments are Props). | 30 |
| 2c.3 | `Diagram.isPositive_deform_of_family` | … + `hpos : ∀ x, D.IsPositive x` ⇒ `(D.deform (V 1) _ _).IsPositive x` | `IsPositive x ↔ 0 < det (dir over) (dir under)` (LinkDiagram.lean:547); `deform_overStrand` (LinkMoves.lean:443): over strand is `D.overStrand x₀` for `x₀ := ⟨x.val, _⟩ : D.Γ.Crossing`, under likewise (`other` is label-only, `Diagram.underStrand` LinkDiagram.lean:505). `f t := det (dir_t (over x₀)) (dir_t (under x₀))` continuous (`hV`, `continuousAt_det`), nonzero for every `t` (`hcross t` makes `x.val` a crossing of `withVertices (V t)`, `(hgen t).transverse`, `not_adjacent_over_under`), so `sign ∘ f` constant on `unitInterval` (`PreconnectedSpace.constant` / `IsPreconnected.constant`), positive at `0` (`h0`, `hpos x₀`). | 45 |
| 2c.4 | `positiveDiagram_single_recast` | `(single ⟨k', h', recastTuple hk X⟩).positiveDiagram hΓ = (single ⟨k, h, X⟩).positiveDiagram hΓ'` | `subst hk; rfl` (proof-irrelevance of `hΓ`). | 8 |
| 2c.5 | `reparam_positiveDiagram_single_shift` | `Reparam ((single C).positiveDiagram hΓ) ((single ⟨C.k, C.hk, shift r C.P⟩).positiveDiagram hΓ')` | `ReparamData` (LinkMoves.lean:370): `e := Equiv.refl (Fin 1)`; `φ _ := ⟨traversalShift r, traversalShift (−r), …⟩` (Traversal.lean: `traversalShift a p = (p.1 − a, p.2)`); `between` by `traversalBetween_shift` (TraversalRelabel/GaussDefinition clause); `eval_eq` by `traversalEvaluation_shift` (Traversal.lean, `single`'s `eval` unfolds to `traversalEvaluation C.P`); `over_map`/`over_surj`: a crossing `x = {⟨0,a⟩,⟨0,b⟩}` of `single C` corresponds to `x' = {⟨0,a−r⟩,⟨0,b−r⟩}` of the shifted shadow (`edgeSegment_shift`, Polygon.lean:80; `single_seg` LinkDiagram.lean:1630; adjacency `remote_add`-style); its over strand is the label with `det(edge a, edge b) > 0` (`positiveDiagram_det_pos`, LinkPositiveLift.lean:105) and `edge_shift` (Polygon.lean:68) preserves the determinant, so over ↦ over; `visitPt` (LinkDiagram.lean:1435) parameters agree by uniqueness of the common point (`Generic.common_point_unique` :414) and `edgePoint_injective` (Crossings.lean:90) with `regular` edges ≠ 0. | 130 |

Subtotal section 2c: ≈ 325 lines.

### 3. Shift instance (section `ShiftTransport`; `hQ := (generic_shift a P).mpr hP`)
| # | lemma | statement | sketch | lines |
|---|---|---|---|---|
| 3.1 | `visitShift_twin` | `visitShiftEquiv a P (visitTwin v) = visitTwin (visitShiftEquiv a P v)` | as 2.3 with `visitShift_crossing` (VisitRelabel.lean:24). | 12 |
| 3.2 | `markList_shift_rotated` | `(markList hn hQ) ~r (markList hn hP).map (Sum.map (Equiv.addRight (−a)) (visitShiftEquiv a P))` | copy `gaussList_shift_perm`/`gaussList_shift_rotation` (GaussRelabel.lean:11-40) with `sorted_map_cut_rotation` (SortedCut.lean:9): keys `markKey`, cut at `N = n`, `a.val`; `markKey_vertex` gives `(i − a).val = if i.val < a.val then i.val − a.val + n else i.val − a.val` (`ZMod.val_sub`/`ZMod.val_add`), visits by `visitKey_shift` (VisitRelabel.lean:30) + `markKey_visit`; injectivity `markKey_injective`; sortedness `markList_sorted`; bounds `traversalKey_nonneg/lt_size`. | 45 |
| 3.3 | `shiftTransport.turn_eq` (field) | `turn (shift a P) (i + −a) = turn P i` | `turn_shift` (Chirotope.lean:103) + `sub_add_cancel`. | 5 |
| 3.4 | `shiftTransport.sign_eq` (field) | `crossingSign (shift a P) (v.2 − a) ((twin v).2 − a) = crossingSign P v.2 (twin v).2` | `visitShiftEquiv_apply`, `visitShift` (GaussVisits.lean ~84: second component `v.2.val − a`), 3.1, `crossingSign_shift` (CrossingEquiv.lean:79). | 10 |
| 3.5 | `transportedCornerPolygon_shift` | `(shiftTransport hn hP a).transportedCornerPolygon S q = ccpCornerPolygon hn hP S q` | funext; `ccpCornerPolygon_apply`; cases on the corner mark: vertex → `markPosition_evaluation_vertex`, `shift` def (`(shift a P)(i − a) = P i`); visit → `markPosition_evaluation_visit` + `crossingPoint_shift` (CrossingEquiv.lean:57) (or `visitPosition_shift` GaussVisits.lean + `traversalEvaluation_shift`). | 20 |
| 3.6 | `carrierRotation_shift` | `carrierRotation hn hQ S' q' = carrierRotation hn hP S q` | 1.14 (r), 0.1, `rotationNumber_shift` (RotationNumber.lean:55), 3.5. | 20 |
| 3.7 | `reparam_positiveLift_shift` | `hS → Reparam (positiveLift hn hP S q hS) (positiveLift hn hQ S' q' hS')` | `positiveLift = (carrierShadow …).positiveDiagram _` (LinkPositiveLift.lean:596), `carrierShadow = single ⟨ccpCornerCount, _, ccpCornerPolygon⟩`; rewrite the `Q`-side polygon by 1.14 + 3.5 as `recastTuple hk (shift r X)`, then 2c.4 (recast) and 2c.5 (shift) — the genericity proofs are transported along the rewrites (`▸`/`Eq.mpr` on Props; use `Shadow.Generic` of the rewritten shadow via `hΓ ▸`). | 30 |
| 3.8 | `homfly_positiveLift_shift`, `cornerCoefficient_shift`, `cornerStateSum_shift` | glue, already written | `homfly_planar`, `PlanarIsotopic.of_reparam` (LinkMoves.lean:519), 1.22, 1.24. | 0 |

Subtotal section 3: ≈ 140 lines.

### 4. Descent (already fully written in the skeleton, no sorry)
`cornerStateSum_genericShift` (:= 3.8), `cornerStateSum_eq_of_mem_labelledChamber`
(`labelledChambers_open_pathConnected` Chambers.lean:48, `IsPathConnected.joinedIn`, `mem_connectedComponent`,
`JoinedIn.joined`, 2.15), `C_chamber` (`projection_labelledChamber_eq_chamber` CyclicChambers.lean:91,
`projection_eq_iff` :37).

**Total estimate: ≈ 1330 lines of new proof (plus the ≈ 600-line skeleton already compiling).**
Counts: 51 sorried theorems + 2 defs with 3 sorried fields = 53 declarations to discharge.

## 2. Dependency order (prove in this order)

0.1–0.5 → 1.1 → 1.2 → 1.3 → 1.4 → (1.5 def) → 1.6 → 1.7 → 1.8 → 1.9 → 1.10 → 1.11 → 1.12 → 1.13 → 1.14 →
1.15 → 1.16 → 1.17 → 1.18 → 1.19 → 1.20 → 1.21 → 1.22 → 1.23 → 1.24 (generic layer complete)
→ 2.1 → 2.2 → 2.3 → 2.4 → 2.5 → 2.6 (pathTransport complete) → 2.7 → 2.8 → 2.9 → 2.10 → 2.11 → 2.12
→ 2c.1 → 2c.2 → 2c.3 → 2.13 → 2.14 (path instance complete; `cornerStateSum_path_constant` closes)
→ 3.1 → 3.2 → 3.3 → 3.4 (shiftTransport complete) → 3.5 → 3.6 → 2c.4 → 2c.5 → 3.7 (shift instance complete;
`cornerStateSum_shift` closes) → `C_chamber` (already proved).
Sections 2 and 3 are independent of each other and can be proved in parallel by two provers once
section 1 is done; 2c.1–2c.3 and 2c.4–2c.5 are independent Link-layer sub-projects (they use nothing of
the Carrier lane) and can start immediately.

## 3. Reuse list (file:line, all under work/lean/SM unless noted)

Accepted topology/chambers: Chambers.lean:14 `GenericTuple`, :21 `polygonProjection`, :24 `labelledChamber`,
:28 `chamber`, :48 `labelledChambers_open_pathConnected`, :56 `continuous_generic_chi`, :73 `crossing_iff_of_chi_eq`,
:86 `edgeParameter`, :109 `crossingParameter_eq_edgeParameter`, :123 `crossing_edgeParameter_det_ne_zero`;
ChamberPaths.lean:9 `generic_family_chi_constant`, :13 `generic_family_crossing_constant`,
:24 `generic_family_edgeParameter_continuous`, :35 `generic_family_crossingOrder_constant`, :73 `chambers`;
CyclicChambers.lean:13 `genericShift`, :37 `projection_eq_iff`, :91 `projection_labelledChamber_eq_chamber`.
State sum: CornerStateSum.lean:61 `carrierRotationInt`, :82 `cornerSlot`, :96 `cornerHomfly`, :103 `cornerCoefficientWith`,
:110 `cornerCoefficient`, :136 `uniformDecompositions`, :140 `mem_uniformDecompositions`, :158 `cornerProduct`,
:166 `cornerStateSum`, :174-210 `cornerStateSum_eq_sum_independentSupports` (dependent-sum technique).
Carrier lane: CarrierMarks.lean:34 `Mark`, :38 `markPosition`, :52/:58 `markPosition_evaluation_vertex/visit`,
:74 `markKey`, :77 `markKey_vertex`, :81 `markKey_visit`, :84 `markKey_injective`, :94 `markList`, :100 `markList_nodup`,
:106 `mem_markList`, :112 `markList_sorted`; CarrierSuccessor.lean:50 `nextMark`, :84 `markSuccessor`,
:100 `markSuccessor_getElem`; CarrierSmoothing.lean:36 `selectedMarkPerm`, :84 `smoothingSuccessor`,
:126 `Component`, :131 `owner`, :135 `owner_eq_iff`, :156 `owner_surjective`; CarrierVisitTwin.lean:34 `visitTwin`,
:41 `visitTwin_ne`, :60 `visitTwin_unique`, :80-90 `selectedVisitTwin(_of_mem/_of_not_mem)`;
CarrierTrueCorners.lean:44 `IsTrueCorner`; CarrierClosedTrace.lean:59 `componentMarkList`, :73 `componentMarkList_data`;
CarrierCornerPolygon.lean:317 `ccpCornerList`, :341 `ccpCornerCount`, :350 `ccpCornerMark`, :357 `ccpCornerPolygon`,
:361 `ccpCornerPolygon_apply`, :375 `ccpCornerMark_isTrueCorner`, :598 `ccpCornerPolygon_turn_vertex`,
:609 `ccpCornerPolygon_turn_smoothing`, :579 `ccpCornerPolygon_turn_ne_zero`, :679 `ccpCornerPolygon_regular`,
:691 `ccpCornerCount_ge_three`; CarrierCrossings.lean:56 `carrierCrossings`, :62 `carrierCrossingCount`,
:66 `mem_carrierCrossings`, :113 `carrierCrossingCount_eq_card`, :216 `visit_crossing_val_eq_pair`;
UniformDefinition.lean:28 `CarrierUniform`, :38 `UniformDecomposition`, :43 `carrierRotation`;
DecompositionDefinition.lean:15 `IsDecomposition`; InterlaceSupports.lean:27 `independentSupports`,
:37 `mem_independentSupports_iff`, :112 `independentSupports_shift` (template); InterlaceRelabel.lean:31 `interlaces_shift`.
Geometric transport (flat-wall machinery reused as is): CrossingTransport.lean:12 `crossingTransport`,
:18 `visitTransport`, :24 `visitTransport_crossing`, :27 `visitTransport_edge`, :30 `crossing_support_partner`,
:40 `crossingParameter_eq_of_support_pair`; GeometricTransport.lean:10 `CrossingParameterOrderAgrees`,
:33 `geometric_visitKey_lt_transport`; GeometricRecords.lean:36 `geometricGaussList_transport` (template for 2.2);
GeometricInterlacement.lean:36 `geometricInterlaces_iff_generic`, :69 `geometric_interlaces_transport`;
GeometricVisits.lean:62 `geometricVisitKey_eq_generic`; CrossingGeometry.lean:24 `generic_crossingGeometry`.
Cyclic relabelling: Polygon.lean:22 `shift`, :68 `edge_shift`, :72 `edgePoint_shift`, :80 `edgeSegment_shift`;
Generic.lean:44 `generic_shift`; CrossingEquiv.lean:41 `crossingShiftEquiv`, :57 `crossingPoint_shift`, :79 `crossingSign_shift`;
VisitRelabel.lean:18 `visitShiftEquiv`, :24 `visitShift_crossing`, :30 `visitKey_shift`; GaussRelabel.lean:11-47
`gaussList_shift_perm/rotation`, `gaussCycle_shift` (templates for 3.2); SortedCut.lean:9 `sorted_map_cut_rotation`;
Traversal.lean `traversalShift`, `traversalEvaluation_shift`, :45 `traversalKey_lt_iff`; GaussDefinition.lean
clause `traversalBetween_shift`; Chirotope.lean:103 `turn_shift`, :107 `leftTurns_shift` (template for 1.20);
RegularLocus.lean:60 `regular_shift`; RotationNumber.lean:55 `rotationNumber_shift`.
Rotation/continuity: RotationContinuity.lean:44 `continuous_rotationNumber_family`, :50 `rotationNumber_family_constant`;
ContinuousGeometry.lean:13 `continuousAt_det`, :21 `continuousAt_cramerFirst`, :50 `transverse_intersection_persists`;
GenericTopology.lean:12 `continuous_vertex`, :15 `continuous_edge`, :87 `isClosed_closedTripleMeet` (template).
Link layer: LinkDiagram.lean:61 `PolyComp`, :83 `Shadow`, :246 `IsCrossing`, :394 `Generic`, :414 `Generic.common_point_unique`,
:456 `Generic.crossingPoint_mem_interior`, :505 `underStrand`, :547 `IsPositive`, :1413 `crossingParam`, :1435 `visitPt`,
:1588 `single`, :1594 `singleStrandEquiv`, :1630 `single_seg`, :1636 `single_dir`; LinkMoves.lean:217 `Vertices`,
:224 `withVertices`, :228 `withVertices_vertices`, :370 `ReparamData`, :428 `Diagram.deform`, :440 `deform_Γ`,
:443 `deform_overStrand`, :462 `DeformData`, :516 `PlanarIsotopic`, :519/:522 `of_reparam/of_deform`;
LinkPositiveLift.lean:93 `positiveDiagram`, :105 `positiveDiagram_det_pos`, :128 `eq_positiveDiagram_of_isPositive`,
:160 `single_generic_of`, :211 `carrierPolyComp`, :218 `carrierShadow`, :580 `carrierShadow_generic`, :596 `positiveLift`,
:618 `positiveLift_isPositive`, :633 `eq_positiveLift_of_isPositive`; LinkInterfaces.lean:382 `homfly_planar`.
Mathlib: `List.isRotated_next_eq` (Data/List/Cycle.lean:385), `List.next_getElem` (:282), `List.isRotated_append`
(Data/List/Rotate.lean:432), `List.Perm.eq_of_pairwise`, `List.perm_ext_iff_of_nodup`, `Equiv.Perm.sameCycle_conj`
(GroupTheory/Perm/Cycle/Basic.lean:96), `Quotient.congr`/`congr_mk` (Logic/Equiv/Defs.lean:884/891),
`isClopen_iff` (Topology/Connected/Clopen.lean:114), `IsPreconnected.constant_of_mapsTo` (TotallyDisconnected.lean:340),
`Set.projIcc` + `projIcc_left/right` (Order/Interval/Set/ProjIcc.lean:48/79/83), `continuous_projIcc`
(Topology/Order/ProjIcc.lean:33), `isClosedMap_fst_of_compactSpace`, `Finset.sum_map` (BigOperators/Group/Finset/Defs.lean:396),
`Fintype.prod_equiv`, `Finset.sum_attach`, `Equiv.cast_apply` (Logic/Equiv/Defs.lean:282).

## 4. The three riskiest steps and fallbacks

**R1 — 2c.1 `Shadow.isCrossing_constant_of_generic_family` (Deform's "same crossing pairs" clause; ≈110 lines).**
Risk: the openness half needs the Cramer/persistence bookkeeping at the level of `Link.Shadow` strands
(`seg`, `tail`, `dir` of `withVertices`), and the closedness half a compactness projection. Fallbacks:
(a) reduce openness to the existing `transverse_intersection_persists` (ContinuousGeometry.lean:50), which is
almost literally the needed local statement (it yields interior parameters and a common point); only the
translation `IsCrossing ↔ segments meet` remains. (b) Combinatorial route: identify the crossings of the carrier
shadow at time `t` with `carrierCrossings (γ t) S' q'` (accepted `carrierCrossingEquiv`, LinkPositiveLift.lean:799) and
their strand pairs with the block indices of the two visits (`mark_block` :676, `carrierCrossing_edges` :722),
which are transported by the MarkTransport (blocks are `ρ_S`-segments between true corners, 1.3 + 1.9); this is
≈200 lines of dependent bookkeeping but needs no topology. (c) Last resort: replace `Deform` by an `EqvGen` chain of
small deformations — no gain; (b) is the real fallback.

**R2 — 2c.5 `reparam_positiveDiagram_single_shift` (cyclic re-indexing is a `Reparam`; ≈130 lines).**
Risk: the `over_map`/`over_surj` clauses require matching `visitPt` parameters (defined by `Classical.choose`)
across the two diagrams and showing the positive over strand is carried to the positive over strand. Fallbacks:
(a) build a `StrandMap` (LinkDiagram.lean:752; `f = id`, `sgn = 1`, `toFun ⟨0,a⟩ := ⟨0, a − r⟩`) and prove once that a
*bijective* StrandMap with `f = id` induces a `ReparamData` (its `crossingEquiv` :895, `crossingPoint_mapCrossing` :846,
`pullback_isPositive_iff` :948 do the over-strand matching); this also gives the shifted positive diagram as a
`pullback` of the original by `eq_positiveDiagram_of_isPositive`. (b) Avoid 1.13's rotation altogether for the shift
instance by choosing, in 3.2, the mark list cut so that `r = 0` — impossible in general (the sorted list is cut at
label 0), so (a) is the fallback; (c) if `Reparam` proves intractable, `cornerStateSum_shift` can alternatively be
attacked by showing `C` is invariant under a *path* from `P` to a suitable representative — not available in general
(labelled chambers over one chamber are permuted by σ, `sigma_permutes_labelledChambers`), so (a) it is.

**R3 — 1.13/1.16 corner-index bookkeeping (`Equiv.cast` between `ZMod` of equal but not definitionally equal sizes
plus the rotation offset `r`; ≈85 lines) and 1.24 (dependent sum over `attach`; ≈60 lines).**
Fallbacks: (a) for the *shift* instance, uniformity needs no corner marks at all: by 1.14 + 3.5 the shifted corner
polygon is `recastTuple hk (shift r (ccpCornerPolygon P q))`, so `CarrierUniform` transports by
`forall_turn_recastTuple` (0.4) and `turn_shift` — prove `carrierUniform_transport` for `shiftTransport` this way if
1.16 stalls; (b) for the *path* instance, turn signs are constant along `t` because
`turn (Φ t) j = sign det(edge (Φ t)(j−1), edge (Φ t) j)` is continuous and never zero (`ccpCornerPolygon_turn_ne_zero`
transported through 0.3 and `ccpCornerPolygon_pathTransport`), a copy of 2.4 — this bypasses 1.16 entirely for paths;
(c) state 1.13 with an auxiliary lemma quantified over an arbitrary `k` and `f : ZMod k → Mark P` so that `subst`
is available, or with `HEq`; (d) for 1.24, convert to the `if`-form `cornerStateSum_eq_sum_independentSupports`
(CornerStateSum.lean:174) and reindex `independentSupports` instead (same technique, one less filter).

Secondary risks: 2.1 (ZMod.val/real arithmetic for vertex-vs-visit key comparisons; template `traversalKey_lt_iff`),
3.2 (`sorted_map_cut_rotation` hypotheses; template GaussRelabel.lean), 2.13 (shadow equality across `PolyComp.mk`
with a recast; use `polyComp_recastTuple` and `Shadow.mk.injEq`).
