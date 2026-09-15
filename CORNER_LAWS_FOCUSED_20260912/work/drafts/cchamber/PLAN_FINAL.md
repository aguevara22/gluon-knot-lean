# PLAN FINAL — prop:C-chamber (chamber constancy of the corner state sum)

Target: `SM.C_chamber : CChamberData` of `work/drafts/CChamber_statement.lean` (fixed statement,
copied verbatim at the end of the skeleton). Source: reference/SM/sm-4-knotlaws.tex:36-99.
Skeleton: `work/drafts/cchamber/Skeleton_FINAL.lean` — typechecks with `lake env lean` (only
`declaration uses 'sorry'` warnings, **50** sorried declarations); `#print axioms SM.C_chamber` =
`propext, sorryAx, Classical.choice, Quot.sound, SM.lit_homfly`. `SM.C_chamber` is PROVED from the
chain; every `sorry` is inside the chain.

## 0. Judgement of the two plans

| | (a) correctness vs. fixed statement | (b) provability (library + Mathlib) | (c) minimality | total |
|---|---|---|---|---|
| **A** (`MarkEquiv`, `TupleAgree`, cycle-level transport, `IsLocallyConstant` descent) | 9 | 7 | 6 | 22 |
| **B** (`MarkTransport`, `recastTuple`, list-level transport, accepted-lemma descent) | 9 | 7 | 7 | **23** |

Both are mathematically sound against `CChamberData`: neither adds a hypothesis, both prove the
labelled-path constancy and the cyclic invariance separately and descend, and both handle the
dependent type `LabelledTuple (ccpCornerCount …)` across polygons soundly (A: ℕ-indexed
`TupleAgree` + `subst`; B: `recastTuple` along `k' = k` with every invariant by `subst hk; rfl`).
Both correctly route `homfly` through `PlanarIsotopic = EqvGen (Reparam ∨ Deform)`
(`homfly_planar`, lit:homfly) in place of the printed rp:record-polynomial/lp:core step.

Why B wins, and what is grafted from A:

1. **Descent.** B uses the accepted `projection_labelledChamber_eq_chamber` + `projection_eq_iff`
   (CyclicChambers.lean) — exactly the printed "saturated open set" argument — and the descent is
   already *closed* in the skeleton (0 sorries). A re-proves it through `IsLocallyConstant` on the
   quotient (3 sorries, ~45 lines). — B kept.
2. **Path instance.** B's mark list is carried *literally* along a path
   (`ccpCornerPolygon_transport_of_markList_eq`, no rotation), and its Link-layer lemmas
   `Deform.of_family` / `Diagram.isPositive_deform_of_family` are clean generic statements. A must
   invoke the shift `Reparam` even in the path case (its corner polygon agrees only up to `∃ m`) and
   needs `single_generic_shift` (45 lines) for that. — B kept.
3. **Crossing-pair constancy along the path (B's risk R1).** B proves a 110-line from-scratch clopen
   argument on `Shadow` (compactness projection + Cramer persistence). A instead lands on the
   accepted `crossing_support_persists_of_geometry` (GeometricCrossingStability.lean:35), which
   already gives two-sided local constancy of the crossing set of any `LabelledTuple k` with
   `CrossingGeometry`, at the cost of one lemma `crossingGeometry_of_single_generic` (~40 lines).
   — **Grafted from A** (`crossingGeometry_of_single_generic`, `isCrossing_transportedCornerPolygon_path`);
   B's `Shadow.isCrossing_constant_of_generic_family` is dropped; `Deform.of_family` takes `hcross`
   as a hypothesis, so nothing else changes.
4. **Turn signs / uniformity (B's risk R3, first half).** B carried `sign_eq` as a structure field and
   transported turn signs corner by corner through `ccpCornerPolygon_turn_vertex/_smoothing` with an
   `Equiv.cast` + rotation offset (lemma 1.16, 45 lines) plus a per-instance crossing-sign lemma.
   A's route — the turn of the transported corner polygon is `sign ∘ det` of consecutive edges,
   continuous and nonzero along the path, hence constant; in the shift instance the transported
   polygon *is* `ccpCornerPolygon`, so uniformity is `Iff.rfl` — is shorter and removes the field.
   — **Grafted from A**: `sign_eq` dropped; generic `carrierUniform_iff_transported` reads uniformity
   on `transportedCornerPolygon`; `turn_transportedCornerPolygon_path` (path) and
   `uniform_transportedCornerPolygon_shift` (shift, closed in the skeleton). `turn_eq` is kept (cheap
   per instance) so `leftTurns_transport` stays generic.
5. **Twin.** B's `twin_eq` field is derivable from `visit_fst` (A's `ev_twin`); made a generic lemma,
   deleting two per-instance lemmas.
6. **Reparam for the cyclic shift** (A risk 1 = B risk R2): same in both; B's statement
   `reparam_positiveDiagram_single_shift C r hΓ hΓ'` with *both* genericity proofs as hypotheses is kept
   (it avoids `single_generic_shift`); the proof follows A's primary route (StrandMap pullback with
   `f = id`, `sgn = 1`, `pullback_isPositive_iff`, then `ReparamData` with `φ = traversalShiftEquiv r`).

Net: 50 sorries (B had 53, A 61), estimated **≈ 1,250 lines** of proof on top of the 620-line skeleton.

## 1. The route in one paragraph

`C(P) = (−1)^{ℓ(P)} Σ_{S uniform decomposition} (−1)^{|S|} ∏_{q carrier of S} c(q)`; every object is
built from the marked traversal `Mark P = ZMod n ⊕ Visit P` sorted by `markKey` (`markList`), the
cyclic successor `markSuccessor` and the twin `visitTwin`. A **mark transport**
`Carrier.MarkTransport hn hP hQ` (fields `vert`, `cross`, `visit`, `visit_fst`, `markList_rotated`,
`interlaces_iff`, `turn_eq`) transports, generically (Section 1 of the skeleton): `visitTwin`,
`markSuccessor`, `smoothingSuccessor`, `Component` (an `Equiv`), `owner`, `carrierCrossings`, `m_Q`,
`IsDecomposition`, `IsTrueCorner`, `componentMarkList`/`ccpCornerList` (up to rotation),
`ccpCornerCount`, `ccpCornerPolygon` (= recast of a cyclic shift of the **transported corner polygon**
`Φ := transportedCornerPolygon τ S q : LabelledTuple (ccpCornerCount hn hP S q)`, the corners of the old
carrier evaluated in `Q`), uniformity (⇔ uniformity of `Φ`), `leftTurns`, and — given per-carrier
agreement of uniformity of `Φ`, of `carrierRotation` and of `homfly (positiveLift …)` —
`cornerStateSum` (`cornerStateSum_transport`). Two instances: **path** `pathTransport hn γ 0 t`
(`γ : Path P Q` in `GenericTuple n`; fields from accepted `SM.chambers` ingredients and
`geometric_interlaces_transport`; the mark list is carried literally, `Φ t` is continuous, regular,
with constant rotation (`rotationNumber_family_constant`), constant turn signs, constant crossing pairs
(`crossing_support_persists_of_geometry`), and the positive lifts at `0`/`1` are a `Deform`); **shift**
`shiftTransport hn hP a` (fields from `crossingShiftEquiv`, `visitShiftEquiv`, `interlaces_shift`,
`turn_shift`, `sorted_map_cut_rotation`; `Φ = ccpCornerPolygon`, rotation by `rotationNumber_shift`,
positive lifts a `Reparam`). **Descent** (closed): `chamber (⟦P⟧) = ⟦labelledChamber P⟧`, path
connectivity of labelled chambers.

## 2. Ordered lemma list with exact statements (skeleton line numbers)

Notation: `τ : MarkTransport hn hP hQ`, `T := τ.toMark = Equiv.sumCongr τ.vert τ.visit`
(`toMark_inl`, `toMark_inr` rfl), `S' := τ.support S = S.map τ.cross.toEmbedding` (`mem_support`,
`support_card`, `support_surjective` proved), `q' := τ.component S q` (`component_owner` rfl),
`Φ := τ.transportedCornerPolygon S q := fun j => traversalEvaluation Q (markPosition hn hQ.1 (T (ccpCornerMark hn hP S q j)))`,
`hk := τ.ccpCornerCount_transport S q : ccpCornerCount hn hQ S' q' = ccpCornerCount hn hP S q`.

### Part 0 — recast (unit U1b) [~15 lines]
`recastTuple {k k'} (hk : k' = k) (f : LabelledTuple k) : LabelledTuple k' := fun j => f (Equiv.cast (congrArg ZMod hk) j)`.
- L63 `rotationNumber_recastTuple [NeZero k] [NeZero k'] (hk) (f) : rotationNumber (recastTuple hk f) = rotationNumber f` — `subst hk; rfl` (`NeZero` is a Prop, instances agree). (3)
- L67 `regular_recastTuple (hk) (f) : Regular (recastTuple hk f) ↔ Regular f` — `subst hk; rfl`. (3)
- L71 `turn_recastTuple (hk) (f) (j : ZMod k') : turn (recastTuple hk f) j = turn f (Equiv.cast (congrArg ZMod hk) j)` — `subst hk; rfl`. (3)
- L75 `forall_turn_recastTuple (hk) (f) (σ) : (∀ j, turn (recastTuple hk f) j = σ) ↔ ∀ j, turn f j = σ` — `subst hk; rfl`. (3)
- L80 `polyComp_recastTuple (hk) (h : 3 ≤ k) (h' : 3 ≤ k') (f) : PolyComp.mk k' h' (recastTuple hk f) = PolyComp.mk k h f` — `subst hk; rfl`. (3)

### Part 1a — successor, carriers, crossings, decompositions, true corners (unit U1a) [~165 lines]
- L144 `twin_eq (v) : τ.visit (visitTwin v) = visitTwin (τ.visit v)` — `visitTwin_unique (τ.visit v) (τ.visit (visitTwin v))`: crossings agree by `visit_fst` twice + `visitTwin_crossing`; distinct by `τ.visit.injective` + `visitTwin_ne`. (12)
- L149 `markSuccessor_transport (m) : markSuccessor hn hQ (T m) = T (markSuccessor hn hP m)` — `markSuccessor_apply`, `nextMark_eq_list_next`; `List.isRotated_next_eq τ.markList_rotated (markList_nodup hn hQ) (mem_markList _ _)` replaces `markList hQ` by `(markList hP).map T`; write `m = (markList hP)[i]` (`List.mem_iff_getElem`), `List.getElem_map`, a helper `next_congr (h : x = y) hx hy : l.next x hx = l.next y hy := by subst h; rfl`, `List.next_getElem` on `(markList hP).map T` (nodup: `(markList_nodup hn hP).map T.injective`, `List.length_map`) and `markSuccessor_getElem` on `markList hP`. (35)
- L153 `selectedMarkPerm_transport (S) (m) : selectedMarkPerm S' (T m) = T (selectedMarkPerm S m)` — `cases m`; `inl`: rfl; `inr v`: `selectedMarkPerm_visit`, unfold `selectedVisitTwin`, `by_cases hv : v.1 ∈ S`, `(τ.visit v).1 ∈ S' ↔ v.1 ∈ S` by `visit_fst` + `mem_support`, `if_pos/if_neg`, `twin_eq`. (15)
- L157 `smoothingSuccessor_transport (S) (m) : smoothingSuccessor hn hQ S' (T m) = T (smoothingSuccessor hn hP S m)` — `smoothingSuccessor = (selectedMarkPerm S).trans (markSuccessor hn hP)` (CarrierSmoothing.lean), `Equiv.trans_apply`, the two previous lemmas. (8)
- L162 `sameCycle_transport (S) (a b) : (smoothingSuccessor hn hQ S').SameCycle (T a) (T b) ↔ (smoothingSuccessor hn hP S).SameCycle a b` — `have : smoothingSuccessor hn hQ S' = T * smoothingSuccessor hn hP S * T⁻¹` (`Equiv.ext`, `Equiv.Perm.mul_apply`, `smoothingSuccessor_transport`, `Equiv.apply_symm_apply`); `Equiv.Perm.sameCycle_conj` (GroupTheory/Perm/Cycle/Basic.lean:96) then `Equiv.Perm.inv_apply_self`. (20)
- def `component S : Component hn hP S ≃ Component hn hQ S' := Quotient.congr T (fun a b => (sameCycle_transport S a b).symm)` (compiles).
- L177 `carrierCrossings_transport (S) (q) : carrierCrossings hn hQ S' q' = (carrierCrossings hn hP S q).map τ.cross.toEmbedding` — `Finset.ext x'`; `obtain ⟨x, rfl⟩ := τ.cross.surjective x'`; `Finset.mem_map' `, `mem_carrierCrossings` both sides; `x ∉ S ↔ τ.cross x ∉ S'` (`mem_support`); visits of `τ.cross x` are `τ.visit v` for the visits `v` of `x` (`τ.visit.surjective`, `visit_fst`, `τ.cross.injective`); `owner hQ S' (Sum.inr (τ.visit v)) = q' ↔ owner hP S (Sum.inr v) = q` by `toMark_inr`, `component_owner`, `(τ.component S).injective.eq_iff`. (30)
- L182 `carrierCrossingCount_transport (S) (q) : carrierCrossingCount hn hQ S' q' = carrierCrossingCount hn hP S q` — `carrierCrossingCount_eq_card`, previous, `Finset.card_map`. (5)
- L187 `isDecomposition_transport (S) : IsDecomposition hn hQ S' ↔ IsDecomposition hn hP S` — `IsDecomposition` unfolds to `∈ independentSupports`; `mem_independentSupports_iff` both sides; copy `independentSupports_shift` (InterlaceSupports.lean) with `interlaces_iff`, `mem_support`, `τ.cross.injective/surjective`. (25)
- L191 `isTrueCorner_transport (S) (m) : IsTrueCorner S' (T m) ↔ IsTrueCorner S m` — `cases m`; `inl`: both `True`; `inr v`: `isTrueCorner_visit`, `visit_fst`, `mem_support`. (10)

### Part 1b — corner list and corner polygon (unit U1b) [~170 lines]
- L199 `componentMarkList_transport (S) (q) : (componentMarkList hn hQ S' q').IsRotated ((componentMarkList hn hP S q).map T)` — `componentMarkList = (markList).filter (fun m => decide (owner m = q))` (CarrierClosedTrace.lean:59); `τ.markList_rotated.filter _` (`List.IsRotated.filter`, SM/CycleFiltering.lean:52); `List.filter_map` (core); `List.filter_congr`: `decide (owner hQ S' (T m) = q') = decide (owner hP S m = q)` by `component_owner`, `(τ.component S).injective.eq_iff`, `decide_eq_decide` (pattern `geoComponentMarkList_eq_generic`, FlatCarriersDefs.lean:688). (30)
- L204 `ccpCornerList_transport (S) (q) : (ccpCornerList hn hQ S' q').IsRotated ((ccpCornerList hn hP S q).map T)` — `ccpCornerList = componentMarkList.filter (decide ∘ IsTrueCorner S)` (CarrierCornerPolygon.lean:317); previous `.filter _`, `List.filter_map`, `List.filter_congr` with `isTrueCorner_transport`. (15)
- L209 `ccpCornerCount_transport (S) (q) : ccpCornerCount hn hQ S' q' = ccpCornerCount hn hP S q` — `(ccpCornerList_transport S q).perm.length_eq`, `List.length_map`. (5)
- L214 `exists_ccpCornerMark_transport (S) (q) : ∃ r : ZMod (ccpCornerCount hn hP S q), ∀ j, ccpCornerMark hn hQ S' q' (Equiv.cast (congrArg ZMod hk.symm) j) = T (ccpCornerMark hn hP S q (j + r))` — take the rotation in the direction `((ccpCornerList hP S q).map T).rotate m = ccpCornerList hQ S' q'` (`(ccpCornerList_transport S q).symm`, `List.IsRotated` is `∃ m, l.rotate m = l'`), `r := (m : ZMod k)`; `ccpCornerMark j = list[j.val]` (:350); a helper `(Equiv.cast (congrArg ZMod h) j).val = j.val` (by `subst h; rfl`); `List.getElem_rotate` (`(l.rotate m)[i] = l[(i + m) % l.length]`), `List.getElem_map`, `ZMod.val_add`, `ZMod.val_natCast`, `Nat.add_mod`. (40)
- def `transportedCornerPolygon S q` (compiles).
- L229 `exists_ccpCornerPolygon_transport (S) (q) : ∃ r, ccpCornerPolygon hn hQ S' q' = recastTuple hk (shift r Φ)` — `obtain ⟨r, hr⟩` from the previous; `refine ⟨r, funext fun j' => ?_⟩`; write `j' = Equiv.cast (congrArg ZMod hk.symm) (Equiv.cast (congrArg ZMod hk) j')` (`Equiv.cast_symm`, `Equiv.apply_symm_apply`); `ccpCornerPolygon_apply`, `hr`, unfold `recastTuple`, `shift`, `transportedCornerPolygon`. (20)
- L236 `ccpCornerPolygon_transport_of_markList_eq (h : markList hn hQ = (markList hn hP).map T) (S) (q) : ccpCornerPolygon hn hQ S' q' = recastTuple hk Φ` — the literal chain: `componentMarkList hQ S' q' = (componentMarkList hP S q).map T` (`h`, `List.filter_map`, `filter_congr`), then `ccpCornerList`, then `ccpCornerMark hQ S' q' (cast j) = T (ccpCornerMark hP S q j)` (`List.getElem_map`, val-of-cast helper), then `funext`. (25)

### Part 1d/1e — uniformity, index set, prefactor, assembly (unit U2) [~200 lines]
- L249 `carrierUniform_iff_transported (S) (q) : CarrierUniform hn hQ S' q' ↔ ∃ σ : SignType, σ ≠ 0 ∧ ∀ j, turn Φ j = σ` — `CarrierUniform` unfolds (UniformDefinition.lean:28); `obtain ⟨r, hr⟩ := exists_ccpCornerPolygon_transport`; `rw [hr]`; `exists_congr`, `and_congr_right`; `forall_turn_recastTuple`; `turn_shift` (`turn (shift r Φ) j = turn Φ (j + r)`); reindex by `(Equiv.addRight r).forall_congr_left`. (25)
- L254 `uniformDecomposition_transport {S} (huni : ∀ q, (∃ σ ≠ 0, ∀ j, turn Φ j = σ) ↔ CarrierUniform hn hP S q) : UniformDecomposition hn hQ S' ↔ UniformDecomposition hn hP S` — `UniformDecomposition = ∀ q, CarrierUniform`; `(τ.component S).forall_congr_left` (or `.surjective`); previous + `huni`. (15)
- L261 `mem_uniformDecompositions_transport (huni : ∀ S, IsDecomposition hn hP S → ∀ q, …) (S) : S' ∈ uniformDecompositions hn hQ ↔ S ∈ uniformDecompositions hn hP` — `mem_uniformDecompositions` both sides; `isDecomposition_transport`; `by_cases hS : IsDecomposition hn hP S`; `and_congr` with `uniformDecomposition_transport (huni S hS)`. (15)
- L269 `leftTurns_transport : leftTurns Q = leftTurns P` — `leftTurns = (univ.filter (turn · = 1)).card` (Chirotope.lean:16); `Finset.card_equiv τ.vert` (or `card_bij` as in `leftTurns_shift`), `Finset.mem_filter`, `turn_eq`. (15)
- L274 `cornerSlot_transport {S} (q) (hrot : carrierRotation hn hQ S' q' = carrierRotation hn hP S q) : cornerSlot hn hQ S' q' = cornerSlot hn hP S q` — unfold `cornerSlot`, `carrierRotationInt`; `carrierCrossingCount_transport`; `hrot`. (10)
- L279 `cornerCoefficient_transport {S} (hS) (q) (hrot) (hH : homfly (positiveLift hn hQ S' q' hS') = homfly (positiveLift hn hP S q hS)) : cornerCoefficient hn hQ S' q' hS' = cornerCoefficient hn hP S q hS` (`hS' := (isDecomposition_transport S).mpr hS`) — `cornerCoefficient_eq_coeffAt`, `cornerHomfly`, `cornerSlot_transport`, `hH`. (15)
- L288 `cornerProduct_transport {S} (hS) (hcoef : ∀ q, cornerCoefficient hn hQ S' q' hS' = cornerCoefficient hn hP S q hS) : cornerProduct hn hQ S' hS' = cornerProduct hn hP S hS` — `cornerProduct = ∏ q, cornerCoefficient`; `Fintype.prod_equiv (τ.component S)` (or `Equiv.prod_comp`) with `hcoef`. (15)
- L298 `cornerStateSum_transport (huni) (hcoef : ∀ S hS q, cornerCoefficient hn hQ S' q' hS' = cornerCoefficient hn hP S q hS) : cornerStateSum hn hQ = cornerStateSum hn hP` — the `dite` device of `cornerStateSum_eq_sum_independentSupports` (CornerStateSum.lean:174-210): `g S := if h : S ∈ uniformDecompositions hn hP then (-1)^S.card * cornerProduct hn hP S (isDecomposition_of_mem_uniformDecompositions hn hP h) else 0`, `g'` likewise on `Q`; rewrite both attached sums as `∑ S ∈ uD, g S` (`Finset.sum_congr`, `dite_eq_left`, `Finset.sum_attach`); `uniformDecompositions hn hQ = (uniformDecompositions hn hP).map (Finset.mapEmbedding τ.cross.toEmbedding).toEmbedding` (`Finset.ext`, `Finset.mem_map`, `Finset.mapEmbedding_apply`, `support_surjective`, `mem_uniformDecompositions_transport huni`); `Finset.sum_map`; termwise `g' S' = g S` by `mem_uniformDecompositions_transport`, `support_card`, `cornerProduct_transport hS (hcoef S hS)` (the decomposition proofs are Props); prefactor by `leftTurns_transport`. (60)

### Part 2c — Link layer (units U4, U5) [~285 lines]
Proved in the skeleton: `positiveDiagram_congr (h : Γ = Γ') hΓ hΓ' : Γ.positiveDiagram hΓ = Γ'.positiveDiagram hΓ'` and `single_isCrossing_iff_of_forall (hk) (h : ∀ s, IsCrossing X s ↔ IsCrossing Y s) (x) : (single ⟨k,hk,X⟩).IsCrossing x ↔ (single ⟨k,hk,Y⟩).IsCrossing x`.
- L332 (U4) `crossingGeometry_of_single_generic (hk : 3 ≤ k) (h : (Shadow.single ⟨k, hk, T⟩).Generic) : CrossingGeometry T` — `CrossingGeometry T = (∀ i, edge T i ≠ 0) ∧ (∀ i j, remote i j → ∀ x ∈ seg i, x ∈ seg j → x ∈ interior i ∧ x ∈ interior j ∧ det ≠ 0) ∧ G2 T` (CrossingGeometry.lean:11). Edges: `(regular_iff_edges T).mp (h.regular 0) i`. For remote `i j` and `x`: `det ≠ 0` from `h.transverse ⟨0,i⟩ ⟨0,j⟩` (`single_adjacent_iff`: `remote = ¬adjacent`; `single_seg`, `single_dir`); interiority: `x = edgePoint T i s`, `s ∈ [0,1]`; `s = 0` gives `x = T i = tail ⟨0,i⟩ ∈ seg ⟨0,j⟩`, contradicting `h.tail_off ⟨0,i⟩ ⟨0,j⟩` (`single_incidentTail_iff`: `¬incident i j` since `j ≠ i - 1`, `j ≠ i` from `remote`, defs Polygon.lean:60-66); `s = 1` gives `x = T (i+1) = tail ⟨0,i+1⟩`, `¬incident (i+1) j` (`j ≠ i`, `j ≠ i+1`); symmetric for `j`. `G2` from `h.no_triple` via `single_interior` (as in `single_generic_of_generic`, reversed). (40)
- L338 (U4) `Deform.of_family (D) {V : unitInterval → D.Γ.Vertices} (hV : ∀ i j, Continuous fun t => V t i j) (hgen : ∀ t, (D.Γ.withVertices (V t)).Generic) (hcross : ∀ t x, (D.Γ.withVertices (V t)).IsCrossing x ↔ D.Γ.IsCrossing x) (h0 : V 0 = D.Γ.vertices) : Deform D (D.deform (V 1) (hgen 1) (hcross 1))` — `DeformData` (LinkMoves.lean:462) with `γ t := V (Set.projIcc 0 1 zero_le_one t)`; `continuous`: `((hV i j).comp continuous_projIcc).continuousOn`; `start`: `Set.projIcc_left` (`= (0 : unitInterval)` by `Subtype.ext rfl`) + `h0`; `generic`, `crossings`: `hgen`, `hcross`; `stop`: `Set.projIcc_right` and a helper `deform_congr (h : V = W) : D.deform V hg hc = D.deform W (h ▸ hg) (h ▸ hc) := by subst h; rfl`. (30)
- L349 (U4) `Diagram.isPositive_deform_of_family (D) {V} (hV) (hgen) (hcross) (h0) (hpos : ∀ x, D.IsPositive x) (x : (D.deform (V 1) _ _).Γ.Crossing) : (D.deform (V 1) _ _).IsPositive x` — `x₀ : D.Γ.Crossing := ⟨x.val, (hcross 1 x.val).mp x.2⟩`; `deform_overStrand`: over strand is `D.overStrand x₀`; under strand is `D.underStrand x₀` (`Γ'.eq_other_of_mem_of_ne` with `D.under_mem x₀`, `D.under_ne_over x₀`; strands and `Adjacent` are label-only, `withVertices_Strand` rfl); `f t := det (edge (V t (over).1) (over).2) (edge (V t (under).1) (under).2)` continuous (`hV`, `continuousAt_det`); nonzero at every `t`: `(hgen t).transverse _ _ (D.not_adjacent_over_under x₀) (Γ_t.seg_inter_other_nonempty ⟨x.val, (hcross t _).mpr x₀.2⟩ _)`; `sign ∘ f` continuous (`continuousAt_sign_of_ne_zero`), `PreconnectedSpace.constant` on `unitInterval`; at `0`, `h0` and `hpos x₀`; `sign_eq_one_iff`. (45)
- L360 (U5) `positiveDiagram_single_recast (hk : k' = k) (h) (h') (X) (hΓ) (hΓ') : (single ⟨k', h', recastTuple hk X⟩).positiveDiagram hΓ = (single ⟨k, h, X⟩).positiveDiagram hΓ'` — `subst hk; rfl`. (8)
- L372 (U5) `reparam_positiveDiagram_single_shift (C : PolyComp) (r : ZMod C.k) (hΓ : (single C).Generic) (hΓ' : (single ⟨C.k, C.hk, shift r C.P⟩).Generic) : Reparam ((single C).positiveDiagram hΓ) ((single ⟨C.k, C.hk, shift r C.P⟩).positiveDiagram hΓ')` — (1) `sm : StrandMap (single C') (single C)` (`C' := ⟨C.k, C.hk, shift r C.P⟩`; the strand types coincide) with `toFun ⟨i, a⟩ := ⟨i, a + r⟩`, `f := id`, `vert := toFun`, `sgn := 1`; fields: `inj` (add cancel), `seg_eq`/`interior_eq` (`edgeSegment_shift`, `edgeInterior_shift`, `Set.image_id`), `tail_eq` (rfl: `shift r P a = P (a + r)`), `adjacent_iff`/`incidentTail_iff` (`single_adjacent_iff`, `single_incidentTail_iff`, `adjacent`/`incident` are translation invariant: `add_sub_add_right_eq_sub`, `add_left_inj`), `det_eq` (`edge_shift`, `one_mul`). (2) `D := (single C).positiveDiagram hΓ`; `D.pullback sm (fun _ => hΓ'.regular 0)` is a diagram on `single C'`, positive by `pullback_isPositive_iff` (sgn = 1) + `positiveDiagram_isPositive`, hence `= (single C').positiveDiagram hΓ'` by `eq_positiveDiagram_of_isPositive`. (3) `ReparamData D (D.pullback sm _)`: `e := Equiv.refl _`, `φ _ := traversalShiftEquiv r` (TraversalRelabel.lean:10; `p ↦ (p.1 - r, p.2)`), `between` := `(traversalBetween_shift r _ _ _).mpr`, `eval_eq` := `traversalEvaluation_shift` (Traversal.lean:89), `over_map x`: `x' := (sm.crossingEquiv hsurj).symm x` (`mapCrossing_surjective`, `hsurj` by `⟨i, a - r⟩`), `toFun_pullback_overStrand` gives `(pullback).overStrand x' = ⟨0, a - r⟩` where `a := (D.overStrand x).2`; the parameters agree: `crossingParam_spec` on both sides, `crossingPoint_mapCrossing` (`f = id`), `edgePoint_shift`, `edgePoint_injective ((regular_iff_edges _).mp (hΓ.regular 0) a).1`; `over_surj x'`: `x := sm.mapCrossing x'`, same computation (factor a lemma `pullback_visitPt_overVisit`). Then `⟨r⟩ ▸` the diagram equality of (2). Template: `ReparamData.reverse` (LinkMoves.lean:2385), `reverse_visitPt`. (130)

### Part 2 — path instance (unit U3) [~380 lines]
`γ : Path P Q`, `P Q : GenericTuple n`; `pathTransport hn γ s t : MarkTransport hn (γ s).2 (γ t).2` (def compiles: `vert := Equiv.refl`, `cross := crossingTransport (path_crossing_iff …)`, `visit := visitTransport _`, `markList_rotated` from `markList_transport`, `interlaces_iff` from `geometric_interlaces_transport`, `turn_eq` from `generic_family_chi_constant`); `Φ t := (pathTransport hn γ 0 t).transportedCornerPolygon S q`; `S'_t, q'_t, hS'_t` its support/component/decomposition proof; `ccpCornerPolygon_pathTransport t S q : ccpCornerPolygon hn (γ t).2 S'_t q'_t = recastTuple hk (Φ t)` (proved from `ccpCornerPolygon_transport_of_markList_eq`).
- L391 `markKey_lt_transport (hn) (hP) (hQ) (hs) (ho : CrossingParameterOrderAgrees P Q) (a b) : markKey hn hQ.1 (Sum.map id (visitTransport hs) a) < markKey hn hQ.1 (… b) ↔ markKey hn hP.1 a < markKey hn hP.1 b` — `cases a <;> cases b`. vertex/vertex: `markKey_vertex`, `Iff.rfl`. vertex/visit: `markKey_vertex`, `markKey_visit`, `visitKey = traversalKey (visitPosition)`, `traversalKey_lt_iff` (Traversal.lean:35): `(i, 0) < (e, p) ↔ i.val < e.val ∨ i = e ∧ 0 < p`, and `0 < p` on both sides (`visitPosition_interior`, edge kept by `visitTransport_edge`); visit/vertex symmetric (`p < 0` false both sides). visit/visit: `geometric_visitKey_lt_transport (generic_crossingGeometry hn hP) (generic_crossingGeometry hn hQ) hs ho v w` with `geometricVisitKey_eq_generic` (GeometricVisits.lean:63, rfl). (50)
- L400 `markList_transport (hn) (hP) (hQ) (hs) (ho) : markList hn hQ = (markList hn hP).map (Sum.map id (visitTransport hs))` — `List.Perm.eq_of_pairwise` (pattern `geoMarkList_eq_generic`, FlatCarriersDefs.lean:644): antisymmetry `markKey_injective hn hQ`; sortedness of the mapped list from `markList_sorted hn hP`, `List.pairwise_map`, `markKey_lt_transport` (`≤` via `not_lt`); `markList_sorted hn hQ`; perm by `List.perm_ext_iff_of_nodup` (`markList_nodup`, `.map` injective), `mem_markList`, surjectivity of the map. (25)
- L408 `generic_family_crossingParameterOrderAgrees (hn) {F : α → GenericTuple n} (hF) (s t) : CrossingParameterOrderAgrees (F s).val (F t).val` — unfold (GeometricTransport.lean:10); `intro i j k hij hik; exact generic_family_crossingOrder_constant hn hF s i j k hij hik t s`. (10)
- L441 `pathTransport_toMark_self (s) (m : Mark (γ s).val) : (pathTransport hn γ s s).toMark m = m` — `cases m`; `inl`: rfl; `inr v`: `rfl` (`crossingTransport` is `Equiv.subtypeEquivRight`, proof-irrelevant + structure eta) or `Sigma.ext (Subtype.ext rfl) (HEq.refl _)`. (10)
- L454 `continuous_path_crossingPoint (c : Crossing (γ 0).val) : Continuous fun t => crossingPoint (crossingTransport (path_crossing_iff hn γ 0 t) c)` — pick `i ∈ c.val` (`crossing_visits_exist`/`c.2`), `crossing_support_partner c i hi : ∃ j, i ≠ j ∧ c.val = {i, j}`; `crossingPoint (cT c) = edgePoint (γ t) i (crossingParameter (cT c) i _)` (`crossingParameter_spec`), `crossingParameter_eq_of_support_pair hn (γ t).2.1 (cT c) i j hi hcj` (support of `cT c` is `c.val`, `crossingTransport_support`) `= edgeParameter (γ t).val i j`; so the function is `t ↦ (γ t).val i + edgeParameter (γ t).val i j • edge (γ t).val i` (`funext`); `continuous_vertex`, `continuous_edge` composed with `continuous_subtype_val.comp γ.continuous`, `generic_family_edgeParameter_continuous hn γ.continuous i j (fun t => (path_crossing_iff hn γ 0 t _).mp (hcj ▸ c.2))`, `Continuous.add`, `Continuous.smul`. (35)
- L458 `continuous_transportedCornerPolygon (S) (q) (j) : Continuous fun t => Φ t j` — unfold; the mark `ccpCornerMark hn (γ 0).2 S q j` is fixed; `cases h : ccpCornerMark …`; `inl i`: `toMark_inl`, `Equiv.refl_apply`, `markPosition_evaluation_vertex`: `t ↦ (γ t).val i`, `(continuous_apply i).comp (continuous_subtype_val.comp γ.continuous)`; `inr v`: `toMark_inr`, `markPosition_evaluation_visit`, `visitTransport_crossing`: `continuous_path_crossingPoint v.1`. (25)
- L463 `transportedCornerPolygon_zero (S) (q) : Φ 0 = ccpCornerPolygon hn (γ 0).2 S q` — `funext j`; unfold; `pathTransport_toMark_self`; `ccpCornerPolygon_apply`. (10)
- L477 `regular_transportedCornerPolygon (hS) (q) (t) : Regular (Φ t)` — `ccpCornerPolygon_regular hn (γ t).2 hS'_t q'_t`, `ccpCornerPolygon_pathTransport`, `regular_recastTuple`. (10)
- L483 `carrierRotation_path (hS) (q) : carrierRotation hn (γ 1).2 S'_1 q'_1 = carrierRotation hn (γ 0).2 S q` — `carrierRotation = rotationNumber ∘ ccpCornerPolygon`; `ccpCornerPolygon_pathTransport 1`, `rotationNumber_recastTuple`; `rotationNumber_family_constant (f := Φ) (continuous_pi (continuous_transportedCornerPolygon hn γ S q)) (regular_transportedCornerPolygon hn γ hS q) 1 0` (RotationContinuity.lean:50; `unitInterval` is a `PreconnectedSpace`); `transportedCornerPolygon_zero`. (20)
- L493 `turn_transportedCornerPolygon_path (hS) (q) (t) (j) : turn (Φ t) j = turn (ccpCornerPolygon hn (γ 0).2 S q) j` — `turn_det` both sides; `f t := det (edge (Φ t) (j - 1)) (edge (Φ t) j)` continuous (`continuous_transportedCornerPolygon`, `edge` is a difference of coordinates, `continuousAt_det`); nonzero at every `t`: `ccpCornerPolygon_turn_ne_zero hn (γ t).2 hS'_t q'_t (Equiv.cast (congrArg ZMod hk.symm) j)` through `ccpCornerPolygon_pathTransport`, `turn_recastTuple`, `Equiv.cast_symm`/`Equiv.apply_symm_apply`, `turn_det`, `sign_ne_zero`; `continuousAt_sign_of_ne_zero`, `PreconnectedSpace.constant` (pattern `generic_family_crossingOrder_constant`, ChamberPaths.lean:35); `transportedCornerPolygon_zero` at `0`. (40)
- (proved) `uniform_transportedCornerPolygon_path (hS) (q) (t) : (∃ σ ≠ 0, ∀ j, turn (Φ t) j = σ) ↔ CarrierUniform hn (γ 0).2 S q`.
- L512 `isCrossing_transportedCornerPolygon_path (hS) (q) (t) (s) : IsCrossing (Φ t) s ↔ IsCrossing (Φ 0) s` — `hΦ : Continuous Φ := continuous_pi …`; for each `t₀`, `hgen t₀ : (single ⟨k, hk₃, Φ t₀⟩).Generic` from `carrierShadow_pathTransport hn γ t₀ hS q ▸ carrierShadow_generic hn (γ t₀).2 …` (`(single C).withVertices (fun _ => X) = single ⟨C.k, C.hk, X⟩` is rfl); `crossing_support_persists_of_geometry (crossingGeometry_of_single_generic _ (hgen t₀)) : ∀ᶠ R in 𝓝 (Φ t₀), ∀ s, IsCrossing R s ↔ IsCrossing (Φ t₀) s`; `hΦ.continuousAt.eventually`; so `g t := {s | IsCrossing (Φ t) s}` satisfies `IsLocallyConstant.iff_eventually_eq` (Topology/LocallyConstant/Basic.lean:77, `Set.ext`); `IsLocallyConstant.apply_eq_of_preconnectedSpace hg t 0`; `Set.ext_iff`. (35)
- L523 `carrierShadow_pathTransport (t) (hS) (q) : carrierShadow hn (γ t).2 S'_t q'_t hS'_t = (carrierShadow hn (γ 0).2 S q hS).withVertices (fun _ => Φ t)` — both sides are `Shadow.single ⟨_, _, _⟩` (`carrierShadow`, `carrierPolyComp` are abbrevs; RHS is `single ⟨k, hk₃, Φ t⟩` by rfl); `show Shadow.single (PolyComp.mk _ _ (ccpCornerPolygon …)) = Shadow.single (PolyComp.mk _ _ (Φ t))`; `rw [ccpCornerPolygon_pathTransport, polyComp_recastTuple]`. (30)
- L532 `deform_positiveLift_path (hS) (q) : Deform (positiveLift hn (γ 0).2 S q hS) (positiveLift hn (γ 1).2 S'_1 q'_1 hS'_1)` — `D := positiveLift hn (γ 0).2 S q hS`, `V t := fun _ => Φ t`; `hV i j := continuous_transportedCornerPolygon hn γ S q j`; `hgen t := carrierShadow_pathTransport hn γ t hS q ▸ carrierShadow_generic …`; `hcross t x := single_isCrossing_iff_of_forall _ (fun s => (isCrossing_transportedCornerPolygon_path hn γ hS q t s).trans (by rw [transportedCornerPolygon_zero])) x`; `h0 := funext fun _ => transportedCornerPolygon_zero hn γ S q`; `hd := Deform.of_family D hV hgen hcross h0`; `heq : D.deform (V 1) _ _ = positiveLift hn (γ 1).2 S'_1 q'_1 hS'_1 := eq_positiveLift_of_isPositive hn (γ 1).2 _ _ hS'_1 _ (by rw [deform_Γ, ← carrierShadow_pathTransport hn γ 1 hS q]) (Diagram.isPositive_deform_of_family D hV hgen hcross h0 (positiveLift_isPositive hn (γ 0).2 S q hS))`; `heq ▸ hd`. (50)
- (proved) `homfly_positiveLift_path`, `cornerCoefficient_path`, `cornerStateSum_path_constant (γ) : cornerStateSum hn P.2 = cornerStateSum hn Q.2`.

### Part 3 — shift instance (unit U5) [~110 lines]
`hQ := (generic_shift a P).mpr hP`; `shiftTransport hn hP a : MarkTransport hn hP hQ` (def compiles: `vert := Equiv.addRight (-a)`, `cross := crossingShiftEquiv a P`, `visit := visitShiftEquiv a P`, `interlaces_iff := interlaces_shift hn hP a`, `turn_eq` proved by `turn_shift`).
- L579 `markList_shift_rotated : (markList hn hQ).IsRotated ((markList hn hP).map (Sum.map (Equiv.addRight (-a)) (visitShiftEquiv a P)))` — `(sorted_map_cut_rotation (markList hn hP) (markList hn hQ) f (markKey hn hP.1) (markKey hn hQ.1) n a.val …).symm` (SortedCut.lean:9; template `gaussList_shift_rotation`, GaussRelabel.lean:27): injectivity `markKey_injective`; sortedness `markList_sorted`; perm by `List.perm_ext_iff_of_nodup` + `mem_markList` + bijectivity of `f = Equiv.sumCongr _ _`; bounds `traversalKey_nonneg`/`traversalKey_lt_size` (markKey = traversalKey ∘ markPosition); key law: vertex `i`: `markPosition hQ.1 (inl (i + -a)) = traversalShift a (markPosition hP.1 (inl i))` (rfl up to `sub_eq_add_neg`), `traversalKey_shift`; visit `v`: `markKey_visit`, `visitKey_shift hn hP.1 a v` (`visitShiftEquiv_apply`). (45)
- L597 `transportedCornerPolygon_shift (S) (q) : (shiftTransport hn hP a).transportedCornerPolygon S q = ccpCornerPolygon hn hP S q` — `funext j`; `ccpCornerPolygon_apply`; `cases h : ccpCornerMark hn hP S q j`; `inl i`: `toMark_inl`, `markPosition_evaluation_vertex` both sides, `shift a P (i + -a) = P i` (`neg_add_cancel_right`); `inr v`: `toMark_inr`, `markPosition_evaluation_visit` both sides, `visitShiftEquiv_apply`, `visitShift_crossing`, `crossingPoint_shift hn hP.1 a v.1`. (20)
- (proved) `uniform_transportedCornerPolygon_shift`.
- L608 `carrierRotation_shift (S) (q) : carrierRotation hn hQ S' q' = carrierRotation hn hP S q` — unfold; `obtain ⟨r, hr⟩ := exists_ccpCornerPolygon_transport`; `rw [hr, rotationNumber_recastTuple, rotationNumber_shift, transportedCornerPolygon_shift]`. (15)
- L613 `reparam_positiveLift_shift (hS) (q) : Reparam (positiveLift hn hP S q hS) (positiveLift hn hQ S' q' hS')` — `obtain ⟨r, hr⟩ := exists_ccpCornerPolygon_transport`, `rw [transportedCornerPolygon_shift] at hr`; `hsh : carrierShadow hn hQ S' q' hS' = Shadow.single ⟨_, ccpCornerCount_ge_three hn hP hS q, shift r (ccpCornerPolygon hn hP S q)⟩ := congrArg Shadow.single (by rw [show carrierPolyComp … = PolyComp.mk _ _ (ccpCornerPolygon hn hQ S' q') from rfl, hr, polyComp_recastTuple])`; `positiveLift = positiveDiagram (carrierShadow …) _` (rfl); `rw [positiveDiagram_congr hsh _ (hsh ▸ carrierShadow_generic …)]`; `exact reparam_positiveDiagram_single_shift (carrierPolyComp hn hP S q hS) r _ _`. (30)
- (proved) `homfly_positiveLift_shift`, `cornerCoefficient_shift`, `cornerStateSum_shift`.

### Part 4 — descent (closed in the skeleton)
`cornerStateSum_genericShift`, `cornerStateSum_eq_of_mem_labelledChamber`
(`labelledChambers_open_pathConnected`, `IsPathConnected.joinedIn`, `mem_connectedComponent`, `JoinedIn.joined`,
`cornerStateSum_path_constant`), `C_chamber` (`projection_labelledChamber_eq_chamber hn P`, `projection_eq_iff`).

## 3. Partition into six independent prover units

Every unit works in `work/drafts/cchamber/Skeleton_FINAL.lean` (copy it to `work/drafts/cchamber/Unit_<name>.lean` and
discharge only the listed sorries; keep every other declaration exactly as stated — the other units are
proving them). Each unit may assume, as black boxes, the *statements* of every other declaration in the
skeleton (in particular all of Section 1 and the two `def`s `component`, `transportedCornerPolygon`) plus
the accepted library under `work/lean/SM` and Mathlib. No unit may change a statement; if one is found
unprovable as stated, report it (with the counter-argument) instead.

| unit | sorries to discharge (skeleton lines) | may additionally assume | est. lines |
|---|---|---|---|
| **U1a** generic transport: twin, successor, carriers, crossings, decompositions, true corners | 144 `twin_eq`, 149 `markSuccessor_transport`, 153 `selectedMarkPerm_transport`, 157 `smoothingSuccessor_transport`, 162 `sameCycle_transport`, 177 `carrierCrossings_transport`, 182 `carrierCrossingCount_transport`, 187 `isDecomposition_transport`, 191 `isTrueCorner_transport` | library only | 165 |
| **U1b** recast lemmas + corner list / corner polygon transport | 63 `rotationNumber_recastTuple`, 67 `regular_recastTuple`, 71 `turn_recastTuple`, 75 `forall_turn_recastTuple`, 80 `polyComp_recastTuple`, 199 `componentMarkList_transport`, 204 `ccpCornerList_transport`, 209 `ccpCornerCount_transport`, 214 `exists_ccpCornerMark_transport`, 229 `exists_ccpCornerPolygon_transport`, 236 `ccpCornerPolygon_transport_of_markList_eq` | U1a statements (`component_owner` is rfl, `isTrueCorner_transport`) | 185 |
| **U2** uniformity, index set, prefactor, assembly | 249 `carrierUniform_iff_transported`, 254 `uniformDecomposition_transport`, 261 `mem_uniformDecompositions_transport`, 269 `leftTurns_transport`, 274 `cornerSlot_transport`, 279 `cornerCoefficient_transport`, 288 `cornerProduct_transport`, 298 `cornerStateSum_transport` | U1a, U1b statements | 200 |
| **U3** path instance | 391 `markKey_lt_transport`, 400 `markList_transport`, 408 `generic_family_crossingParameterOrderAgrees`, 441 `pathTransport_toMark_self`, 454 `continuous_path_crossingPoint`, 458 `continuous_transportedCornerPolygon`, 463 `transportedCornerPolygon_zero`, 477 `regular_transportedCornerPolygon`, 483 `carrierRotation_path`, 493 `turn_transportedCornerPolygon_path`, 512 `isCrossing_transportedCornerPolygon_path`, 523 `carrierShadow_pathTransport`, 532 `deform_positiveLift_path` | U1a, U1b, U4 statements | 380 |
| **U4** Link layer: geometry of a generic one-component shadow, deformation from a family, positivity persistence | 332 `crossingGeometry_of_single_generic`, 338 `Deform.of_family`, 349 `Diagram.isPositive_deform_of_family` | library only | 130 |
| **U5** Link layer: recast/reparam + shift instance | 360 `positiveDiagram_single_recast`, 372 `reparam_positiveDiagram_single_shift`, 579 `markList_shift_rotated`, 597 `transportedCornerPolygon_shift`, 608 `carrierRotation_shift`, 613 `reparam_positiveLift_shift` | U1a, U1b statements | 250 |

Order of integration: U1a → U1b → U2 (generic layer closes), U4 → U3 (`cornerStateSum_path_constant`
closes), U5 (`cornerStateSum_shift` closes), then `C_chamber` is sorry-free. Units U1a, U1b, U4, U5 can
start immediately in parallel; U2 and U3 can start immediately too (they only use statements).

## 4. Reuse list (file:line, all accepted unless marked)

Chambers / paths: Chambers.lean `GenericTuple` :14, `polygonProjection` :21, `labelledChamber` :24,
`chamber` :28, `labelledChambers_open_pathConnected` :48, `edgeParameter` :86,
`crossingParameter_eq_edgeParameter` :109, `crossing_edgeParameter_det_ne_zero` :123;
ChamberPaths.lean `generic_family_chi_constant` :9, `generic_family_crossing_constant` :13,
`generic_family_edgeParameter_continuous` :24, `generic_family_crossingOrder_constant` :35;
CyclicChambers.lean `genericShift` :13, `projection_eq_iff` :37, `projection_labelledChamber_eq_chamber` :91.
State sum: CornerStateSum.lean `carrierRotationInt`, `cornerSlot`, `cornerHomfly`, `cornerCoefficient`,
`cornerCoefficient_eq_coeffAt`, `uniformDecompositions`, `mem_uniformDecompositions`,
`isDecomposition_of_mem_uniformDecompositions`, `cornerProduct`, `cornerStateSum`,
`cornerStateSum_eq_sum_independentSupports` (dependent-sum technique).
Carrier lane: CarrierMarks.lean `Mark`, `markPosition`, `markPosition_evaluation_vertex/visit`, `markKey`,
`markKey_vertex`, `markKey_visit`, `markKey_injective`, `markList`, `markList_nodup`, `mem_markList`,
`markList_sorted`; CarrierSuccessor.lean `nextMark_eq_list_next`, `markSuccessor_apply`, `markSuccessor_getElem`;
CarrierVisitTwin.lean `visitTwin_crossing`, `visitTwin_ne`, `visitTwin_unique`, `selectedVisitTwin(_of_mem/_of_not_mem)`;
CarrierSmoothing.lean `selectedMarkPerm_vertex/_visit`, `smoothingSuccessor`, `Component`, `owner`, `owner_eq_iff`,
`owner_surjective`; CarrierTrueCorners.lean `IsTrueCorner`, `isTrueCorner_visit`; CarrierClosedTrace.lean
`componentMarkList` :59; CarrierCornerPolygon.lean `ccpCornerList` :317, `ccpCornerCount` :341, `ccpCornerMark` :350,
`ccpCornerPolygon` :357, `ccpCornerPolygon_apply` :361, `ccpCornerPolygon_turn_ne_zero` :579, `ccpCornerPolygon_regular` :679,
`ccpCornerCount_ge_three` :691; CarrierCrossings.lean `carrierCrossings` :56, `mem_carrierCrossings` :66,
`carrierCrossingCount_eq_card` :113, `visit_crossing_val_eq_pair` :216; UniformDefinition.lean `CarrierUniform` :28,
`UniformDecomposition` :38, `carrierRotation` :43; DecompositionDefinition.lean `IsDecomposition`;
InterlaceSupports.lean `mem_independentSupports_iff` :37, `independentSupports_shift` :112 (template);
InterlaceRelabel.lean `interlaces_shift` :31; SM/CycleFiltering.lean `List.IsRotated.filter` :52, `Cycle.filter_map` :87.
Geometric transport: CrossingTransport.lean `crossingTransport`, `crossingTransport_support`, `visitTransport`,
`visitTransport_crossing`, `visitTransport_edge`, `crossing_support_partner`, `crossingParameter_eq_of_support_pair`;
GeometricTransport.lean `CrossingParameterOrderAgrees` :10, `geometric_visitKey_lt_transport` :33;
GeometricInterlacement.lean `geometric_interlaces_transport` :69; GeometricVisits.lean `geometricVisitKey_eq_generic` :63;
CrossingGeometry.lean `CrossingGeometry` :11, `generic_crossingGeometry` :24;
GeometricCrossingStability.lean `crossing_support_persists_of_geometry` :35; FlatCarriersDefs.lean
`geoMarkList_eq_generic` :644, `geoComponentMarkList_eq_generic` :688, `list_next_congr` (patterns).
Relabelling: Polygon.lean `shift` :22, `edge_shift` :73, `edgePoint_shift` :77, `edgeSegment_shift` :81, `adjacent` :63,
`incident` :60; Generic.lean `edgeInterior_shift` :21, `generic_shift` :45; CrossingEquiv.lean `crossingShiftEquiv`,
`crossingPoint_shift`, `remote_add`; VisitRelabel.lean `visitShiftEquiv_apply`, `visitShift_crossing`, `visitKey_shift`;
GaussVisits.lean `visitPosition_interior`, `visitPosition_evaluation`, `visitPosition_shift`; GaussRelabel.lean
`gaussList_shift_rotation` (template); SortedCut.lean `sorted_map_cut_rotation` :9; Traversal.lean `traversalKey_lt_iff` :35,
`traversalShift` :69, `traversalEvaluation_shift` :71; TraversalRelabel.lean `traversalShiftEquiv` :10, `traversalKey_nonneg`,
`traversalKey_lt_size`, `traversalKey_shift` :126, `traversalBetween_shift` :138; Chirotope.lean `turn_det` :87,
`turn_shift` :103, `leftTurns_shift` :107 (template); RegularLocus.lean `Regular` :12, `regular_iff_edges` :18,
`regular_shift` :61; RotationNumber.lean `rotationNumber_shift` :53; RotationContinuity.lean
`rotationNumber_family_constant` :50; GenericTopology.lean `continuous_vertex` :12, `continuous_edge` :15;
ContinuousGeometry.lean `continuousAt_det` :13.
Link layer: LinkDiagram.lean `PolyComp` :61, `Shadow` :83, `Adjacent` :142, `IncidentTail` :147, `IsCrossing` :246,
`other`/`eq_other_of_mem_of_ne` :315-340, `Generic` :394, `Generic.common_point_unique` :414, `underStrand` :505,
`not_adjacent_over_under` :531, `seg_inter_other_nonempty` :355, `IsPositive` :547, `StrandMap` :752, `mapCrossing` :815,
`other_mapCrossing` :837, `crossingPoint_mapCrossing` :846, `mapCrossing_surjective` :879, `crossingEquiv` :895,
`Diagram.pullback` :910, `toFun_pullback_overStrand` :922, `pullback_isPositive_iff` :948, `crossingParam` :1413,
`crossingParam_spec` :1416, `visitPt` :1435, `single` :1589, `singleStrandEquiv` :1594, `single_adjacent_iff` :1614,
`single_incidentTail_iff` :1622, `single_seg` :1630, `single_interior` :1633, `single_dir` :1636, `single_isCrossing_iff` :1641;
LinkMoves.lean `Vertices` :217, `vertices` :220, `withVertices` :224, `withVertices_Strand`, `ReparamData` :370, `Reparam` :387,
`Diagram.deform` :429, `deform_Γ` :440, `deform_overStrand` :443, `DeformData` :462, `Deform` :478, `PlanarIsotopic.of_reparam/of_deform`
:519/:522, `ReparamData.reverse` :2385 (template); LinkPositiveLift.lean `positiveDiagram` :93, `positiveDiagram_det_pos` :105,
`positiveDiagram_isPositive` :111, `eq_positiveDiagram_of_isPositive` :128, `single_generic_of` :160, `carrierPolyComp` :211,
`carrierShadow` :218, `carrierShadow_generic` :580, `positiveLift` :596, `positiveLift_isPositive` :618,
`eq_positiveLift_of_isPositive` :633; LinkInterfaces.lean `homfly` :131, `homfly_planar` :382.
Mathlib: `List.isRotated_next_eq` (Data/List/Cycle.lean:385), `List.next_getElem` (:282), `List.getElem_rotate`
(Data/List/Rotate.lean:218), `List.IsRotated.perm/.map/.symm`, `List.filter_map`, `List.filter_congr`,
`List.Perm.eq_of_pairwise`, `List.perm_ext_iff_of_nodup`, `List.pairwise_map`, `Equiv.Perm.sameCycle_conj`
(GroupTheory/Perm/Cycle/Basic.lean:96), `Quotient.congr`, `Equiv.cast_symm`, `Equiv.forall_congr_left`,
`Finset.mem_map'`, `Finset.card_map`, `Finset.sum_map`, `Finset.sum_attach`, `Finset.mapEmbedding`, `Finset.card_equiv`,
`Fintype.prod_equiv`/`Equiv.prod_comp`, `ZMod.val_add`, `ZMod.val_natCast`, `Set.projIcc_left/right`, `continuous_projIcc`,
`continuous_pi`, `continuousAt_sign_of_ne_zero`, `PreconnectedSpace.constant`, `IsLocallyConstant.iff_eventually_eq`
(Topology/LocallyConstant/Basic.lean:77), `IsLocallyConstant.apply_eq_of_preconnectedSpace`, `sign_eq_one_iff`.

## 5. Remaining risks and fallbacks

**R1 — `reparam_positiveDiagram_single_shift` (U5, ~130 lines).** The `over_map`/`over_surj` clauses of
`ReparamData` need the `Classical.choose`d `crossingParam` of the pulled-back diagram to equal that of the
original: pinned down by `crossingParam_spec` on both sides, `crossingPoint_mapCrossing` (`f = id`),
`edgePoint_shift` and `edgePoint_injective` on a nonzero edge. Fallback: build the `ReparamData` directly
between the two positive diagrams (B's original sketch: the over strand of the shifted crossing is the
positive one because `edge_shift` preserves the determinants, `positiveDiagram_det_pos` + `det_swap`), which
avoids the `StrandMap` bookkeeping but re-proves crossing correspondence by hand. Last resort: leave this
single lemma as the flagged remaining `sorry`; everything else (labelled-chamber constancy and the
descent) is independent of it.

**R2 — index bookkeeping in `exists_ccpCornerMark_transport` (U1b, ~40 lines).** `Equiv.cast` between
`ZMod` of propositionally equal sizes plus the rotation offset. Fallbacks: prove the val-of-cast helper by
`subst`; if `List.getElem_rotate` arithmetic resists, state the lemma with `r : ℕ` and `(j.val + r) % k`
first and convert; for the *path* instance nothing of this is needed (`ccpCornerPolygon_transport_of_markList_eq`
is literal), and for the *shift* instance only `exists_ccpCornerPolygon_transport` (through
`carrierRotation_shift`, `reparam_positiveLift_shift`, `carrierUniform_iff_transported`) is used.

**R3 — `cornerStateSum_transport` (U2, ~60 lines).** The dependent `attach` sum. Fallback: convert both
sides to the `if`-form `cornerStateSum_eq_sum_independentSupports` and reindex `independentSupports`
(`isDecomposition_transport`) instead of `uniformDecompositions`.

**R4 — `deform_positiveLift_path` / `Deform.of_family` `stop` clause (U3/U4).** Equalities of `Diagram`s whose
shadows are propositionally but not definitionally equal: always go through `eq_positiveLift_of_isPositive`
/ `eq_positiveDiagram_of_isPositive` (which `subst` the shadow equality) and the helper `deform_congr`;
never `rw` inside `Diagram.deform`'s proof arguments.

Secondary: `markKey_lt_transport` vertex/visit cases (real arithmetic with `ZMod.val`; `traversalKey_lt_iff`
does the work); `markList_shift_rotated` hypotheses of `sorted_map_cut_rotation` (template
`gaussList_shift_rotation`); `isCrossing_transportedCornerPolygon_path` needs `Generic` of
`single ⟨k, hk, Φ t⟩` *before* the `Deform` is built — it comes from `carrierShadow_pathTransport` (U3, no
circularity: that lemma only uses `ccpCornerPolygon_pathTransport` and `polyComp_recastTuple`).

## §5 addendum (executor, 2026-09-13 ~23:02Z) — misstated chain lemma found by U2

`leftTurns_transport` as written in Skeleton_FINAL.lean does not mention `τ`, so by Lean's variable-inclusion rule
it is a universal claim over arbitrary P Q and is FALSE (machine-checked counterexample
`leftTurns_transport_false_as_stated` in U2.lean). ASSEMBLY RULE: prefix the skeleton statement with `include τ in`
(intended content), or use U2's proved `leftTurns_eq_of_transport : leftTurns Q = leftTurns P` (taking τ) — U2's
`cornerStateSum_transport` already uses the latter. Drop the misstated version from the assembled module.
