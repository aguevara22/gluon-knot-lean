import SM.GeoCarrierOrder

/-! Ported 2026-09-14 from work/drafts/cvdom/U2a/GeoCarrierCrossings.lean (CV-DOM unit U2a: retained crossings m_Q of the geo carriers, neighbour separation, geoSupportNeighbors/Unselected (= CV.N / CV.U by rfl); tier 0; REPORT.md in the same directory). Library module, no row. Only this header added. -/

/-! # SM/GeoCarrierCrossings.lean — the crossings of a carrier, `N(S)`, `U(S)` (CV-DOM unit U2a)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor, for the CV-DOM decision
(work/drafts/cvdom/DECISION_FINAL.md §0, §3 rulings R1–R5, §5 unit U2a). Draft home
work/drafts/cvdom/U2a/; intended home work/lean/SM/GeoCarrierCrossings.lean.

Port onto the accepted geometric carrier layer `SM.GeoCarrier` (SM/FlatCarriersDefs.lean, def:flat-carriers:
`geoMarkPosition`, `geoMarkSuccessor`, `geoSmoothingSuccessor`, `GeoComponent`, `geoOwner`, `geoSmoothingSegment`,
`geoCarrierCrossings`, `GeoIndependent`, all on `hP : CrossingGeometry P`) of
* work/lean/SM/CarrierCrossings.lean §1 (the crossings of a carrier and `m_Q`), §5 (corner statements for a
  carrier), §6 (unselected crossings interlacing no element of `S`) — §2/§4 are the accepted FlatCarriers.lean
  §3 (`geoMarkSuccessor_symm_visit_edge`, …, `geo_vertex_incoming_direction`; only their `_mem_edgeSegment`
  companions are ported here), §3 is hypothesis-free and shared (`visitTwin_snd_ne`, `visitTwin_edge_ne`,
  `visit_crossing_val_eq_pair`, `SM.Carrier`);
* work/lean/SM/CarrierNeighborSeparation.lean (a crossing interlacing a selected crossing has its visits on
  different carriers);
* SM/InterlaceSupports.lean:49–75 (`supportNeighbors` = `N(S)`, `supportUnselected` = `U(S)`), as
  `geoSupportNeighbors`, `geoSupportUnselected` (§0), the CV-free twins of the accepted `CV.N`, `CV.U`
  (CV/Events.lean:171–177; same `Finset.univ.filter` / `Finset.univ \ (S ∪ N)` bodies), so that this SM
  module imports no `CV.*` (U0's convention). `CV.mem_N_iff` / `CV.mem_U_iff` (CV/CarrierBridges.lean) and
  `mem_geoSupportNeighbors` / `mem_geoSupportUnselected_iff` here have the same right-hand sides.

Transformer: work/drafts/cvdom/port_lane.py + work/drafts/cvdom/U2a/port_u2a.py (rename dictionary, binder
rules, the hand edits listed in REPORT.md). Proofs are the source proofs verbatim modulo the renaming
`X hn hP → geoX hP`, `markPosition hn hP.1 → geoMarkPosition hP`, `visitPosition hn hP.1 →
geometricVisitPosition hP`, `Interlaces hn hP → GeometricInterlaces hP`, `S ∈ independentSupports hn hP →
GeoIndependent hP S`. Every declaration is tier 0 (`CrossingGeometry P`); `hn : 3 ≤ n` is kept exactly where
the accepted FlatCarriers §3 lemmas take it (`geoMarkSuccessor_position_cases hn`) and on the §5 targets, whose
shape DECISION_FINAL.md §5 fixes (ruling R5; there it is unused).

U2a targets (§5) in this file: `geo_neighbor_visits_separated`, `geo_nonneighbor_visits_together`,
`mem_geoCarrierCrossings`, `geoCarrierCrossings_subset_U`, `geoCarrierCrossings_disjoint`,
`geoCarrierCrossingCount`; the noncrossing target `geo_noncrossing` is in SM/GeoCarrierNoncrossing.lean. -/

namespace SM.GeoCarrier
open Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-! ## 0. `N(S)` and `U(S)` on the geometric record domain (port of `InterlaceSupports` :49–75) -/

/-- `N(S)`, def:interlace: the crossings interlacing some element of `S` (the accepted `CV.N`, word for
word, CV-free). -/
def geoSupportNeighbors {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) : Finset (Crossing P) :=
  Finset.univ.filter fun y => ∃ x ∈ S, GeometricInterlaces hP y x

theorem mem_geoSupportNeighbors {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (y : Crossing P) :
    y ∈ geoSupportNeighbors hP S ↔ ∃ x ∈ S, GeometricInterlaces hP y x := by
  simp only [geoSupportNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]

/-- `U(S)`, def:interlace: the crossings neither in `S` nor interlacing an element of `S` (the accepted
`CV.U`, word for word, CV-free). -/
def geoSupportUnselected {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) : Finset (Crossing P) :=
  Finset.univ \ (S ∪ geoSupportNeighbors hP S)

theorem geoSupportUnselected_eq {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) :
    geoSupportUnselected hP S = Finset.univ \ (S ∪ geoSupportNeighbors hP S) := rfl

theorem mem_geoSupportUnselected {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (y : Crossing P) :
    y ∈ geoSupportUnselected hP S ↔ y ∉ S ∧ y ∉ geoSupportNeighbors hP S := by
  simp only [geoSupportUnselected, Finset.mem_sdiff, Finset.mem_univ,
    Finset.mem_union, not_or, true_and]

/-- `U(S)` membership unfolded (the right-hand side of the accepted `CV.mem_U_iff`). -/
theorem mem_geoSupportUnselected_iff {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (y : Crossing P) :
    y ∈ geoSupportUnselected hP S ↔ y ∉ S ∧ ∀ x ∈ S, ¬ GeometricInterlaces hP y x := by
  rw [mem_geoSupportUnselected, mem_geoSupportNeighbors]
  simp only [not_exists, not_and]

/-! ## 1. The crossings of a carrier and `m_Q` -/

-- [port] `geoCarrierCrossings` -> accepted `geoCarrierCrossings` (SM/FlatCarriers*.lean); not re-declared

/-- `m_Q`, the number of crossings of the carrier `Q`. -/
def geoCarrierCrossingCount {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) : ℕ :=
  (geoCarrierCrossings hP S q).card

theorem mem_geoCarrierCrossings {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (x : Crossing P) :
    x ∈ geoCarrierCrossings hP S q ↔
      x ∉ S ∧ ∀ v : Visit P, v.1 = x → geoOwner hP S (Sum.inr v) = q := by
  simp only [geoCarrierCrossings, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The same membership, quantified over the two-element visit fibre of `x`. -/
theorem mem_geoCarrierCrossings_iff_fiber {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (x : Crossing P) :
    x ∈ geoCarrierCrossings hP S q ↔
      x ∉ S ∧ ∀ i : {k // k ∈ x.val}, geoOwner hP S (Sum.inr ⟨x, i⟩) = q := by
  rw [mem_geoCarrierCrossings]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun i => h ⟨x, i⟩ rfl⟩
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    rintro ⟨c, i⟩ hc
    change c = x at hc
    subst hc
    exact h i

/-- A selected crossing is a crossing of no carrier. -/
theorem geo_selected_not_mem_carrierCrossings {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S)
    {x : Crossing P} (hx : x ∈ S) : x ∉ geoCarrierCrossings hP S q :=
  fun h => ((mem_geoCarrierCrossings hP S q x).mp h).1 hx

/-- Every crossing of a carrier is unselected. -/
theorem geoCarrierCrossings_subset_compl {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    geoCarrierCrossings hP S q ⊆ Finset.univ \ S := by
  intro x hx
  rw [Finset.mem_sdiff]
  exact ⟨Finset.mem_univ x, ((mem_geoCarrierCrossings hP S q x).mp hx).1⟩

/-- A crossing is a crossing of at most one carrier: its visits have one owner. -/
theorem geoCarrierCrossings_disjoint {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) {q r : GeoComponent hP S} (hqr : q ≠ r) :
    Disjoint (geoCarrierCrossings hP S q) (geoCarrierCrossings hP S r) := by
  rw [Finset.disjoint_left]
  intro x hxq hxr
  obtain ⟨i, _, _⟩ := crossing_visits_exist x
  have h1 := ((mem_geoCarrierCrossings_iff_fiber hP S q x).mp hxq).2 i
  have h2 := ((mem_geoCarrierCrossings_iff_fiber hP S r x).mp hxr).2 i
  exact hqr (h1.symm.trans h2)

theorem geoCarrierCrossingCount_eq_card {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    geoCarrierCrossingCount hP S q = (geoCarrierCrossings hP S q).card := rfl

/-- `∑_Q m_Q` counts the crossings of all carriers, each once (the sets are disjoint). -/
theorem sum_geoCarrierCrossingCount {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) :
    ∑ q : GeoComponent hP S, geoCarrierCrossingCount hP S q =
      ((Finset.univ : Finset (GeoComponent hP S)).biUnion (geoCarrierCrossings hP S)).card := by
  rw [Finset.card_biUnion]
  · rfl
  · intro q _ r _ hqr
    exact geoCarrierCrossings_disjoint hP S hqr

/-! ## 2. Edges of incoming segments -/

-- [port] `geoMarkSuccessor_symm_visit_edge` -> accepted `geoMarkSuccessor_symm_visit_edge` (SM/FlatCarriers*.lean); not re-declared

-- [port] `geoMarkSuccessor_symm_vertex_edge` -> accepted `geoMarkSuccessor_symm_vertex_edge` (SM/FlatCarriers*.lean); not re-declared

-- [port] `geoSmoothingSegment_positive_direction_of_succ` -> accepted `geoSmoothingSegment_positive_direction_of_succ` (SM/FlatCarriers*.lean); not re-declared

-- [port] `geoSmoothingSegment_incoming_positive_direction` -> accepted `geoSmoothingSegment_incoming_positive_direction` (SM/FlatCarriers*.lean); not re-declared

/-- The incoming segment at `a` lies on the original edge carrying the `ρ`-predecessor. -/
theorem geoSmoothingSegment_incoming_mem_edgeSegment {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    geoSmoothingSegment hP S ((geoSmoothingSuccessor hP S).symm a) u ∈
      edgeSegment P (geoMarkPosition hP ((geoMarkSuccessor hP).symm a)).1 := by
  have hsel : selectedMarkPerm S ((geoSmoothingSuccessor hP S).symm a) =
      (geoMarkSuccessor hP).symm a := by
    rw [Equiv.eq_symm_apply]
    exact (geoSmoothingSuccessor hP S).apply_symm_apply a
  have h := geoSmoothingSegment_mem_edgeSegment hP S
    ((geoSmoothingSuccessor hP S).symm a) u hu0 hu1
  rwa [hsel] at h

/-! ## 3. The two edges of a crossing visit -/

-- [shared] `visitTwin_snd_ne` is hypothesis-free and already in scope (SM.Carrier); not re-declared

-- [shared] `visitTwin_edge_ne` is hypothesis-free and already in scope (SM.Carrier); not re-declared

-- [shared] `visit_crossing_val_eq_pair` is hypothesis-free and already in scope (SM.Carrier); not re-declared

/-! ## 4. Directions at the corners -/

-- [port] `geo_visit_incoming_direction` -> accepted `geo_visit_incoming_direction` (SM/FlatCarriers*.lean); not re-declared

theorem geo_visit_incoming_mem_edgeSegment (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    geoSmoothingSegment hP S ((geoSmoothingSuccessor hP S).symm (Sum.inr v)) u ∈
      edgeSegment P v.2.val := by
  have h := geoSmoothingSegment_incoming_mem_edgeSegment hP S (Sum.inr v) hu0 hu1
  rwa [geoMarkSuccessor_symm_visit_edge hn hP v] at h

-- [port] `geo_selected_visit_outgoing_direction` -> accepted `geo_selected_visit_outgoing_direction` (SM/FlatCarriers*.lean); not re-declared

theorem geo_selected_visit_outgoing_mem_edgeSegment {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    geoSmoothingSegment hP S (Sum.inr v) u ∈ edgeSegment P (visitTwin v).2.val := by
  have h := geoSmoothingSegment_mem_edgeSegment hP S (Sum.inr v) u hu0 hu1
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_mem S v hv] at h
  exact h

-- [port] `geo_unselected_visit_outgoing_direction` -> accepted `geo_unselected_visit_outgoing_direction` (SM/FlatCarriers*.lean); not re-declared

-- [port] `geo_vertex_outgoing_direction` -> accepted `geo_vertex_outgoing_direction` (SM/FlatCarriers*.lean); not re-declared

theorem geo_vertex_outgoing_mem_edgeSegment {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (i : ZMod n) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    geoSmoothingSegment hP S (Sum.inl i) u ∈ edgeSegment P i := by
  have h := geoSmoothingSegment_mem_edgeSegment hP S (Sum.inl i) u hu0 hu1
  rwa [selectedMarkPerm_vertex] at h

-- [port] `geo_vertex_incoming_direction` -> accepted `geo_vertex_incoming_direction` (SM/FlatCarriers*.lean); not re-declared

theorem geo_vertex_incoming_mem_edgeSegment (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (i : ZMod n) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    geoSmoothingSegment hP S ((geoSmoothingSuccessor hP S).symm (Sum.inl i)) u ∈
      edgeSegment P (i - 1) := by
  have h := geoSmoothingSegment_incoming_mem_edgeSegment hP S (Sum.inl i) hu0 hu1
  rwa [geoMarkSuccessor_symm_vertex_edge hn hP i] at h

/-! ## 5. Corner statements for a carrier `Q` -/

/-- `def:smoothing`, smoothing corners: let `v` be a selected visit (`v.1 ∈ S`) owned by
the carrier `Q = q`. Then `v.1` is the crossing of the edges `E_{v.2}` and
`E_{(visitTwin v).2}` (distinct edges); the incoming segment of `Q` at this corner (from
`ρ_S⁻¹ v` to `v`, both owned by `Q`) lies on `E_{v.2}` and its direction is a positive
multiple of `ℓ_{v.2}`; the outgoing segment of `Q` (from `v` to `ρ_S v = ρ(visitTwin v)`,
both owned by `Q`) lies on `E_{(visitTwin v).2}` and its direction is a positive multiple of
`ℓ_{(visitTwin v).2}`. So `Q` "arrives along one of `ℓ_i, ℓ_j` and leaves along the other". -/
theorem geo_smoothing_corner_directions (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (v : Visit P) (hv : v.1 ∈ S)
    (hq : geoOwner hP S (Sum.inr v) = q) :
    (v.1.val = {v.2.val, (visitTwin v).2.val} ∧ v.2.val ≠ (visitTwin v).2.val) ∧
    (geoOwner hP S ((geoSmoothingSuccessor hP S).symm (Sum.inr v)) = q ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        geoSmoothingSegment hP S ((geoSmoothingSuccessor hP S).symm (Sum.inr v)) u ∈
          edgeSegment P v.2.val) ∧
      ∃ c : ℝ, 0 < c ∧
        traversalEvaluation P (geoMarkPosition hP (Sum.inr v)) -
          traversalEvaluation P
            (geoMarkPosition hP ((geoSmoothingSuccessor hP S).symm (Sum.inr v))) =
          c • edge P v.2.val) ∧
    (geoSmoothingSuccessor hP S (Sum.inr v) = geoMarkSuccessor hP (Sum.inr (visitTwin v)) ∧
      geoOwner hP S (geoSmoothingSuccessor hP S (Sum.inr v)) = q ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        geoSmoothingSegment hP S (Sum.inr v) u ∈ edgeSegment P (visitTwin v).2.val) ∧
      ∃ c : ℝ, 0 < c ∧
        traversalEvaluation P
            (geoMarkPosition hP (geoSmoothingSuccessor hP S (Sum.inr v))) -
          traversalEvaluation P (geoMarkPosition hP (Sum.inr v)) =
          c • edge P (visitTwin v).2.val) := by
  refine ⟨⟨visit_crossing_val_eq_pair v, (visitTwin_edge_ne v).symm⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [geoOwner_predecessor]
    exact hq
  · intro u hu0 hu1
    exact geo_visit_incoming_mem_edgeSegment hn hP S v hu0 hu1
  · exact geo_visit_incoming_direction hn hP S v
  · exact geoSmoothingSuccessor_visit_of_mem hP S v hv
  · rw [geoOwner_successor]
    exact hq
  · intro u hu0 hu1
    exact geo_selected_visit_outgoing_mem_edgeSegment hP S v hv hu0 hu1
  · exact geo_selected_visit_outgoing_direction hn hP S v hv

/-- `def:smoothing`, original vertices: let the original vertex mark `i` be owned by the
carrier `Q = q`. Its incoming segment (from `ρ_S⁻¹ i`, owned by `Q`) lies on `E_{i-1}` with
direction a positive multiple of `ℓ_{i-1}`, and its outgoing segment (to `ρ_S i = ρ i`,
owned by `Q`) lies on `E_i` with direction a positive multiple of `ℓ_i`. -/
theorem geo_vertex_corner_directions (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (i : ZMod n)
    (hq : geoOwner hP S (Sum.inl i) = q) :
    (geoOwner hP S ((geoSmoothingSuccessor hP S).symm (Sum.inl i)) = q ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        geoSmoothingSegment hP S ((geoSmoothingSuccessor hP S).symm (Sum.inl i)) u ∈
          edgeSegment P (i - 1)) ∧
      ∃ c : ℝ, 0 < c ∧
        P i - traversalEvaluation P
            (geoMarkPosition hP ((geoSmoothingSuccessor hP S).symm (Sum.inl i))) =
          c • edge P (i - 1)) ∧
    (geoSmoothingSuccessor hP S (Sum.inl i) = geoMarkSuccessor hP (Sum.inl i) ∧
      geoOwner hP S (geoSmoothingSuccessor hP S (Sum.inl i)) = q ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        geoSmoothingSegment hP S (Sum.inl i) u ∈ edgeSegment P i) ∧
      ∃ c : ℝ, 0 < c ∧
        traversalEvaluation P
            (geoMarkPosition hP (geoSmoothingSuccessor hP S (Sum.inl i))) - P i =
          c • edge P i) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [geoOwner_predecessor]
    exact hq
  · intro u hu0 hu1
    exact geo_vertex_incoming_mem_edgeSegment hn hP S i hu0 hu1
  · exact geo_vertex_incoming_direction hn hP S i
  · exact geoSmoothingSuccessor_vertex hP S i
  · rw [geoOwner_successor]
    exact hq
  · intro u hu0 hu1
    exact geo_vertex_outgoing_mem_edgeSegment hP S i hu0 hu1
  · exact geo_vertex_outgoing_direction hn hP S i

/-! ## 6. Unselected crossings interlacing no element of `S` -/

/-- Adjoining to an independent `S` an unselected crossing that interlaces no element of
`S` (an element of `U(S)`) keeps it independent. -/
theorem geoIndependent_insert_unselected {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x : Crossing P} (hx : x ∈ geoSupportUnselected hP S) :
    GeoIndependent hP (insert x S) := by
  rw [mem_geoSupportUnselected] at hx
  obtain ⟨_, hxN⟩ := hx
  rw [mem_geoSupportNeighbors] at hxN
  intro a ha b hb hab hI
  rw [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact hab rfl
    · exact hxN ⟨b, hb, hI⟩
  · rcases hb with rfl | hb
    · exact hxN ⟨a, ha, geometricInterlaces_symm hP hI⟩
    · exact hS a ha b hb hab hI

/-- `lem:carriers` (iii), second half, in twin form: for `S` independent and `x ∈ U(S)`,
a visit of `x` and its twin have the same owner. -/
theorem geo_unselected_nonneighbor_visit_owner_eq_twin {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x : Crossing P} (hx : x ∈ geoSupportUnselected hP S) (v : Visit P) (hv : v.1 = x) :
    geoOwner hP S (Sum.inr v) = geoOwner hP S (Sum.inr (visitTwin v)) := by
  have hins := geoIndependent_insert_unselected hP hS hx
  have hxS : x ∉ S := ((mem_geoSupportUnselected hP S x).mp hx).1
  refine geoIndependent_remaining_pair_owners hP hins S (Finset.subset_insert x S) v ?_ ?_
  · rw [hv]
    exact Finset.mem_insert_self x S
  · rw [hv]
    exact hxS

/-- `lem:carriers` (iii): "an unselected crossing interlacing no element of `S` has both
visits on one carrier". -/
theorem geo_unselected_nonneighbor_both_visits_one_carrier {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x : Crossing P} (hx : x ∈ geoSupportUnselected hP S) (v w : Visit P)
    (hv : v.1 = x) (hw : w.1 = x) :
    geoOwner hP S (Sum.inr v) = geoOwner hP S (Sum.inr w) := by
  rcases visit_eq_or_twin v w (hw.trans hv.symm) with rfl | rfl
  · rfl
  · exact geo_unselected_nonneighbor_visit_owner_eq_twin hP hS hx v hv

/-- An element of `U(S)` is a crossing of the carrier owning either of its visits. -/
theorem geo_unselected_nonneighbor_mem_carrierCrossings {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x : Crossing P} (hx : x ∈ geoSupportUnselected hP S) (v : Visit P) (hv : v.1 = x) :
    x ∈ geoCarrierCrossings hP S (geoOwner hP S (Sum.inr v)) := by
  rw [mem_geoCarrierCrossings]
  refine ⟨((mem_geoSupportUnselected hP S x).mp hx).1, ?_⟩
  intro w hw
  exact geo_unselected_nonneighbor_both_visits_one_carrier hP hS hx w v hw hv

/-- An element of `U(S)` is a crossing of exactly one carrier. -/
theorem geo_unselected_nonneighbor_exists_unique_carrier {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x : Crossing P} (hx : x ∈ geoSupportUnselected hP S) :
    ∃! q : GeoComponent hP S, x ∈ geoCarrierCrossings hP S q := by
  obtain ⟨i, _, _⟩ := crossing_visits_exist x
  refine ⟨geoOwner hP S (Sum.inr ⟨x, i⟩),
    geo_unselected_nonneighbor_mem_carrierCrossings hP hS hx ⟨x, i⟩ rfl, ?_⟩
  intro q hq
  exact (((mem_geoCarrierCrossings hP S q x).mp hq).2 ⟨x, i⟩ rfl).symm

/-- Every element of `U(S)` is a crossing of some carrier. -/
theorem geoSupportUnselected_subset_biUnion_geoCarrierCrossings {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    geoSupportUnselected hP S ⊆
      (Finset.univ : Finset (GeoComponent hP S)).biUnion (geoCarrierCrossings hP S) := by
  intro x hx
  rw [Finset.mem_biUnion]
  obtain ⟨q, hq, _⟩ := geo_unselected_nonneighbor_exists_unique_carrier hP hS hx
  exact ⟨q, Finset.mem_univ q, hq⟩


/-! ## 7. Neighbours of an independent support have separated visits (port of
`CarrierNeighborSeparation`) -/

/-- Interlacing puts the two visits of the other crossing in *different* open arcs of the
original marked circle cut at the two visits of `v`: one in the forward arc `A` and one
in the backward arc `B` of any rotated presentation `v :: (A ++ twin v :: B)`. This is the
converse direction of `independent_twin_same_slice`. -/
theorem geo_interlaces_twin_different_slices {P : LabelledTuple n} (hP : CrossingGeometry P)
    (v w : Visit P) (hint : GeometricInterlaces hP v.1 w.1)
    (k : ℕ) (A B : List (Mark P))
    (hrot : (geoMarkList hP).rotate k = Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)) :
    (Sum.inr w ∈ A ∧ Sum.inr (visitTwin w) ∈ B) ∨
      (Sum.inr w ∈ B ∧ Sum.inr (visitTwin w) ∈ A) := by
  have hvw : v.1 ≠ w.1 := hint.1
  -- the arc statuses of the two visits of `w` differ
  have hdiff : ¬ (traversalBetween (geometricVisitPosition hP v) (geometricVisitPosition hP w)
          (geometricVisitPosition hP (visitTwin v)) ↔
        traversalBetween (geometricVisitPosition hP v)
          (geometricVisitPosition hP (visitTwin w)) (geometricVisitPosition hP (visitTwin v))) :=
    fun h => (geo_not_interlaces_iff_twin_same_arc hP v w hvw).mpr h hint
  -- every visit of `w` is in one of the two open arcs
  have hmem : ∀ u : Visit P, u.1 = w.1 → (Sum.inr u : Mark P) ∈ A ∨ (Sum.inr u : Mark P) ∈ B := by
    intro u hu
    have h1 : (Sum.inr u : Mark P) ∈ (geoMarkList hP).rotate k :=
      List.mem_rotate.mpr (mem_geoMarkList hP _)
    rw [hrot] at h1
    rcases List.mem_cons.mp h1 with he | h1
    · have h2 : u.1 = v.1 := congrArg Sigma.fst (Sum.inr.inj he)
      exact (hvw (h2.symm.trans hu)).elim
    · rcases List.mem_append.mp h1 with hA | hB
      · exact Or.inl hA
      · rcases List.mem_cons.mp hB with he | hB
        · have h2 : u.1 = (visitTwin v).1 := congrArg Sigma.fst (Sum.inr.inj he)
          rw [visitTwin_crossing] at h2
          exact (hvw (h2.symm.trans hu)).elim
        · exact Or.inr hB
  have hAiff : ∀ m : Mark P, m ∈ A ↔
      traversalBetween (geoMarkPosition hP (Sum.inr v)) (geoMarkPosition hP m)
        (geoMarkPosition hP (Sum.inr (visitTwin v))) :=
    geoMarkList_rotate_left_iff hP k _ _ A B hrot
  by_cases hw : (Sum.inr w : Mark P) ∈ A
  · have hb1 : traversalBetween (geometricVisitPosition hP v) (geometricVisitPosition hP w)
        (geometricVisitPosition hP (visitTwin v)) := (hAiff _).mp hw
    have hnt : (Sum.inr (visitTwin w) : Mark P) ∉ A := by
      intro ht
      have hb2 : traversalBetween (geometricVisitPosition hP v)
          (geometricVisitPosition hP (visitTwin w)) (geometricVisitPosition hP (visitTwin v)) :=
        (hAiff _).mp ht
      exact hdiff ⟨fun _ => hb2, fun _ => hb1⟩
    rcases hmem (visitTwin w) (visitTwin_crossing w) with h | h
    · exact (hnt h).elim
    · exact Or.inl ⟨hw, h⟩
  · have hnb1 : ¬ traversalBetween (geometricVisitPosition hP v) (geometricVisitPosition hP w)
        (geometricVisitPosition hP (visitTwin v)) := fun h => hw ((hAiff _).mpr h)
    have ht : (Sum.inr (visitTwin w) : Mark P) ∈ A := by
      by_contra ht
      have hnb2 : ¬ traversalBetween (geometricVisitPosition hP v)
          (geometricVisitPosition hP (visitTwin w)) (geometricVisitPosition hP (visitTwin v)) :=
        fun h => ht ((hAiff _).mpr h)
      exact hdiff ⟨fun h => (hnb1 h).elim, fun h => (hnb2 h).elim⟩
    rcases hmem w rfl with h | h
    · exact (hw h).elim
    · exact Or.inr ⟨h, ht⟩

/-- **Arc separation at a single switch.** Let the current successor `ρ_T` inherit the
marked order, let `u` be a fresh selected visit whose twin lies on the same current cycle,
and let `w` be a visit of a crossing interlacing `u.1` whose two visits both lie on that
cycle. Then the switch at `u.1` puts the two visits of `w` on different cycles of
`ρ_{insert u.1 T}`. -/
theorem geo_interlacing_pair_owners_ne_insert {P : LabelledTuple n} (hP : CrossingGeometry P)
    (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T)
    (u : Visit P) (hu : u.1 ∉ T)
    (hc : geoOwner hP T (Sum.inr u) = geoOwner hP T (Sum.inr (visitTwin u)))
    (w : Visit P) (hint : GeometricInterlaces hP u.1 w.1)
    (hw : geoOwner hP T (Sum.inr w) = geoOwner hP T (Sum.inr u))
    (hwt : geoOwner hP T (Sum.inr (visitTwin w)) = geoOwner hP T (Sum.inr u)) :
    geoOwner hP (insert u.1 T) (Sum.inr w) ≠
      geoOwner hP (insert u.1 T) (Sum.inr (visitTwin w)) := by
  obtain ⟨k, A, B, hrot, hNL, hNR, hd, hleft, hright, hactL, hactR⟩ :=
    geoSmoothingSuccessor_insert_child_data hP T hI u hu hc
  -- the two children are different
  have hne : geoOwner hP (insert u.1 T) (Sum.inr u) ≠
      geoOwner hP (insert u.1 T) (Sum.inr (visitTwin u)) := by
    intro he
    have hbL := (hleft (Sum.inr (visitTwin u))).mp he.symm
    exact hd hbL List.mem_cons_self
  have hfilA : ∀ m : Mark P, m ∈ A → geoOwner hP T m = geoOwner hP T (Sum.inr u) →
      m ∈ A.filter (fun m => decide (geoOwner hP T m = geoOwner hP T (Sum.inr u))) :=
    fun m hm ho => List.mem_filter.mpr ⟨hm, decide_eq_true ho⟩
  have hfilB : ∀ m : Mark P, m ∈ B → geoOwner hP T m = geoOwner hP T (Sum.inr u) →
      m ∈ B.filter (fun m => decide (geoOwner hP T m = geoOwner hP T (Sum.inr u))) :=
    fun m hm ho => List.mem_filter.mpr ⟨hm, decide_eq_true ho⟩
  rcases geo_interlaces_twin_different_slices hP u w hint k A B hrot with ⟨hwA, htB⟩ | ⟨hwB, htA⟩
  · have h1 : geoOwner hP (insert u.1 T) (Sum.inr w) =
        geoOwner hP (insert u.1 T) (Sum.inr (visitTwin u)) :=
      (hright (Sum.inr w)).mpr (List.mem_cons_of_mem _ (hfilA _ hwA hw))
    have h2 : geoOwner hP (insert u.1 T) (Sum.inr (visitTwin w)) =
        geoOwner hP (insert u.1 T) (Sum.inr u) :=
      (hleft (Sum.inr (visitTwin w))).mpr (List.mem_cons_of_mem _ (hfilB _ htB hwt))
    rw [h1, h2]
    exact hne.symm
  · have h1 : geoOwner hP (insert u.1 T) (Sum.inr w) =
        geoOwner hP (insert u.1 T) (Sum.inr u) :=
      (hleft (Sum.inr w)).mpr (List.mem_cons_of_mem _ (hfilB _ hwB hw))
    have h2 : geoOwner hP (insert u.1 T) (Sum.inr (visitTwin w)) =
        geoOwner hP (insert u.1 T) (Sum.inr (visitTwin u)) :=
      (hright (Sum.inr (visitTwin w))).mpr (List.mem_cons_of_mem _ (hfilA _ htA hwt))
    rw [h1, h2]
    exact hne

/-- "Process `s` first": for `s ∈ S` interlacing the crossing of `v`, after switching `s`
and then any subset `T ⊆ S \ {s}` of the remaining selected crossings, the two visits of
`v.1` have different owners. Induction on `T`; each later insertion only splits
(`geoOwner_insert_ne_of_ne`, whose same-cycle premise is `geoIndependent_remaining_pair_owners`). -/
theorem geo_interlacing_visit_owners_ne_insert_partial {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {s : Crossing P} (hsS : s ∈ S) (v : Visit P) (hint : GeometricInterlaces hP v.1 s)
    (T : Finset (Crossing P)) (hT : T ⊆ S.erase s) :
    geoOwner hP (insert s T) (Sum.inr v) ≠
      geoOwner hP (insert s T) (Sum.inr (visitTwin v)) := by
  revert hT
  induction T using Finset.induction_on with
  | empty =>
    intro _
    obtain ⟨i, _, _⟩ := crossing_visits_exist s
    let u : Visit P := ⟨s, i⟩
    have hu : u.1 ∉ (∅ : Finset (Crossing P)) := Finset.notMem_empty _
    have hsub := geoComponent_empty_subsingleton hP
    have hint' : GeometricInterlaces hP u.1 v.1 := geometricInterlaces_symm hP hint
    exact geo_interlacing_pair_owners_ne_insert hP ∅ (geoInheritsMarkOrder_empty hP) u hu
      (hsub.elim _ _) v hint' (hsub.elim _ _) (hsub.elim _ _)
  | @insert c T hcT ih =>
    intro hT
    have hT' : T ⊆ S.erase s := fun z hz => hT (Finset.mem_insert_of_mem hz)
    have hcE : c ∈ S.erase s := hT (Finset.mem_insert_self c T)
    have hcs : c ≠ s := (Finset.mem_erase.mp hcE).1
    have hcS : c ∈ S := (Finset.mem_erase.mp hcE).2
    have ih' := ih hT'
    have hcU : c ∉ insert s T := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hcs h
      · exact hcT h
    have hUS : insert s T ⊆ S :=
      Finset.insert_subset hsS (hT'.trans (Finset.erase_subset _ _))
    obtain ⟨i, _, _⟩ := crossing_visits_exist c
    let w : Visit P := ⟨c, i⟩
    have hpend : geoOwner hP (insert s T) (Sum.inr w) =
        geoOwner hP (insert s T) (Sum.inr (visitTwin w)) :=
      geoIndependent_remaining_pair_owners hP hS (insert s T) hUS w hcS hcU
    have hres : geoOwner hP (insert c (insert s T)) (Sum.inr v) ≠
        geoOwner hP (insert c (insert s T)) (Sum.inr (visitTwin v)) :=
      geoOwner_insert_ne_of_ne hP (insert s T) w hcU
        ((geoOwner_eq_iff hP _ _ _).mp hpend) ih'
    rw [Finset.insert_comm c s T] at hres
    exact hres

/-- **lem:carriers (iii), first ownership assertion / def:smoothing, last sentence.**
A crossing `x ∈ N(S)` of an independent support `S` has its two visits `v`, `visitTwin v`
on different carriers of `S`. -/
theorem geo_neighbor_visit_owners_ne {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x : Crossing P} (hx : x ∈ geoSupportNeighbors hP S) (v : Visit P) (hv : v.1 = x) :
    geoOwner hP S (Sum.inr v) ≠ geoOwner hP S (Sum.inr (visitTwin v)) := by
  obtain ⟨s, hsS, hint⟩ := (mem_geoSupportNeighbors hP S x).mp hx
  have hint' : GeometricInterlaces hP v.1 s := by
    rw [hv]
    exact hint
  have h := geo_interlacing_visit_owners_ne_insert_partial hP hS hsS v hint'
    (S.erase s) (Finset.Subset.refl _)
  rw [Finset.insert_erase hsS] at h
  exact h

/-- The same statement phrased with the interlacing witness: an unselected crossing
interlacing some element of `S` has its visits on different carriers. -/
theorem geo_interlacing_visit_owners_ne {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {s : Crossing P} (hsS : s ∈ S) (v : Visit P) (hint : GeometricInterlaces hP v.1 s) :
    geoOwner hP S (Sum.inr v) ≠ geoOwner hP S (Sum.inr (visitTwin v)) :=
  geo_neighbor_visit_owners_ne hP hS
    ((mem_geoSupportNeighbors hP S v.1).mpr ⟨s, hsS, hint⟩) v rfl

/-- A neighbour of an independent support is unselected (`N(S) ∩ S = ∅`), since the
interlacement graph is loopless and `S` is independent. -/
theorem geo_neighbor_not_mem {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x : Crossing P} (hx : x ∈ geoSupportNeighbors hP S) : x ∉ S := by
  intro hxS
  obtain ⟨s, hsS, hint⟩ := (mem_geoSupportNeighbors hP S x).mp hx
  exact hS x hxS s hsS hint.1 hint

/-- def:smoothing: "The crossings of `Q` are the crossings `x ∈ X(P) \ S` both of whose
visits lie on `Q`." Here `Q` is the carrier `q : GeoComponent hP S`, and a visit lies on
`Q` when its owner (incoming-visit convention) is `q`. -/
def GeoIsCrossingOf {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (x : Crossing P) : Prop :=
  x ∉ S ∧ ∀ v : Visit P, v.1 = x → geoOwner hP S (Sum.inr v) = q

/-- No carrier owns both visits of a crossing in `N(S)`. -/
theorem geo_neighbor_no_common_owner {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x : Crossing P} (hx : x ∈ geoSupportNeighbors hP S) (v : Visit P) (hv : v.1 = x)
    (q : GeoComponent hP S) :
    ¬ (geoOwner hP S (Sum.inr v) = q ∧ geoOwner hP S (Sum.inr (visitTwin v)) = q) :=
  fun h => geo_neighbor_visit_owners_ne hP hS hx v hv (h.1.trans h.2.symm)

/-- **def:smoothing, last sentence, second half.** A crossing in `N(S)` is a crossing of
no subpolygon. -/
theorem geo_neighbor_not_isCrossingOf {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x : Crossing P} (hx : x ∈ geoSupportNeighbors hP S) (q : GeoComponent hP S) :
    ¬ GeoIsCrossingOf hP S q x := by
  rintro ⟨_, hall⟩
  obtain ⟨i, _, _⟩ := crossing_visits_exist x
  let v : Visit P := ⟨x, i⟩
  exact geo_neighbor_no_common_owner hP hS hx v rfl q
    ⟨hall v rfl, hall (visitTwin v) (visitTwin_crossing v)⟩

/-! ## 8. The crossings of a carrier and `U(S)` -/

/-- A crossing of a carrier is a neighbour of no selected crossing: `m_Q ⊆ U(S)` (its two visits share
the owner `q`, which `geo_neighbor_visit_owners_ne` forbids for a neighbour). -/
theorem geoCarrierCrossings_subset_U {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S) :
    geoCarrierCrossings hP S q ⊆ geoSupportUnselected hP S := by
  intro x hx
  obtain ⟨hxS, hall⟩ := (mem_geoCarrierCrossings hP S q x).mp hx
  rw [mem_geoSupportUnselected]
  refine ⟨hxS, fun hxN => ?_⟩
  obtain ⟨i, _, _⟩ := crossing_visits_exist x
  exact geo_neighbor_visit_owners_ne hP hS hxN ⟨x, i⟩ rfl
    ((hall ⟨x, i⟩ rfl).trans (hall (visitTwin ⟨x, i⟩) (visitTwin_crossing _)).symm)

/-- `x` is a crossing of `q` iff `x ∈ U(S)` and `q` owns one (hence both) of its visits. -/
theorem mem_geoCarrierCrossings_iff_U {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S) (x : Crossing P) :
    x ∈ geoCarrierCrossings hP S q ↔
      x ∈ geoSupportUnselected hP S ∧ ∃ v : Visit P, v.1 = x ∧ geoOwner hP S (Sum.inr v) = q := by
  constructor
  · intro hx
    refine ⟨geoCarrierCrossings_subset_U hP hS q hx, ?_⟩
    obtain ⟨i, _, _⟩ := crossing_visits_exist x
    exact ⟨⟨x, i⟩, rfl, ((mem_geoCarrierCrossings hP S q x).mp hx).2 ⟨x, i⟩ rfl⟩
  · rintro ⟨hxU, v, hv, hq⟩
    rw [← hq]
    exact geo_unselected_nonneighbor_mem_carrierCrossings hP hS hxU v hv

/-- `U(S)` is the (disjoint, `geoCarrierCrossings_disjoint`) union of the crossing sets of the carriers. -/
theorem geoSupportUnselected_eq_biUnion_geoCarrierCrossings {P : LabelledTuple n}
    (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    geoSupportUnselected hP S =
      (Finset.univ : Finset (GeoComponent hP S)).biUnion (geoCarrierCrossings hP S) := by
  apply Finset.Subset.antisymm (geoSupportUnselected_subset_biUnion_geoCarrierCrossings hP hS)
  intro x hx
  obtain ⟨q, _, hq⟩ := Finset.mem_biUnion.mp hx
  exact geoCarrierCrossings_subset_U hP hS q hq

/-- `∑_Q m_Q = |U(S)|`: the retained crossings of the carriers are exactly `U(S)`, each counted once. -/
theorem sum_geoCarrierCrossingCount_eq_card_U {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    ∑ q : GeoComponent hP S, geoCarrierCrossingCount hP S q = (geoSupportUnselected hP S).card := by
  rw [sum_geoCarrierCrossingCount, geoSupportUnselected_eq_biUnion_geoCarrierCrossings hP hS]

/-- `GeoIsCrossingOf` (the predicate form of def:smoothing's sentence) is membership in the accepted
`geoCarrierCrossings`. -/
theorem geoIsCrossingOf_iff_mem {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (x : Crossing P) :
    GeoIsCrossingOf hP S q x ↔ x ∈ geoCarrierCrossings hP S q :=
  (mem_geoCarrierCrossings hP S q x).symm

/-- **def:smoothing, last sentence, second half**, on the accepted set: a crossing in `N(S)` is a crossing of
no carrier. -/
theorem geo_neighbor_not_mem_geoCarrierCrossings {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x : Crossing P} (hx : x ∈ geoSupportNeighbors hP S) (q : GeoComponent hP S) :
    x ∉ geoCarrierCrossings hP S q :=
  fun h => geo_neighbor_not_isCrossingOf hP hS hx q ((geoIsCrossingOf_iff_mem hP S q x).mpr h)

/-! ## 9. The U2a targets (DECISION_FINAL.md §5) -/

set_option linter.unusedVariables false in
/-- **lem:carriers (iii), first half** — `CarriersLemmaData.neighbor_visits_separated` on the geo lane: a
crossing in `N(S)` has its two visits on different carriers. `hn` is unused (§5 shape; ruling R5). -/
theorem geo_neighbor_visits_separated (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    ∀ x ∈ geoSupportNeighbors hP S, ∀ v : Visit P, v.1 = x →
      geoOwner hP S (Sum.inr v) ≠ geoOwner hP S (Sum.inr (visitTwin v)) :=
  fun x hx v hv => geo_neighbor_visit_owners_ne hP hS hx v hv

set_option linter.unusedVariables false in
/-- The same with the interlacing witness in place of `N(S)` membership (the second form §5 allows; it is
the right-hand side of `CV.mem_N_iff`). -/
theorem geo_neighbor_visits_separated' (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    ∀ x : Crossing P, (∃ y ∈ S, GeometricInterlaces hP x y) → ∀ v : Visit P, v.1 = x →
      geoOwner hP S (Sum.inr v) ≠ geoOwner hP S (Sum.inr (visitTwin v)) :=
  fun x hx v hv => geo_neighbor_visit_owners_ne hP hS ((mem_geoSupportNeighbors hP S x).mpr hx) v hv

set_option linter.unusedVariables false in
/-- **lem:carriers (iii), second half** — `CarriersLemmaData.nonneighbor_visits_together` on the geo lane: a
crossing in `U(S)` has both visits on one carrier. `hn` is unused (§5 shape; ruling R5). -/
theorem geo_nonneighbor_visits_together (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    ∀ x ∈ geoSupportUnselected hP S, ∀ v w : Visit P, v.1 = x → w.1 = x →
      geoOwner hP S (Sum.inr v) = geoOwner hP S (Sum.inr w) :=
  fun x hx v w hv hw => geo_unselected_nonneighbor_both_visits_one_carrier hP hS hx v w hv hw

set_option linter.unusedVariables false in
/-- The same with `U(S)` membership unfolded (the right-hand side of `CV.mem_U_iff`). -/
theorem geo_nonneighbor_visits_together' (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    ∀ x : Crossing P, x ∉ S → (∀ y ∈ S, ¬ GeometricInterlaces hP x y) → ∀ v w : Visit P,
      v.1 = x → w.1 = x → geoOwner hP S (Sum.inr v) = geoOwner hP S (Sum.inr w) :=
  fun x hxS hxN v w hv hw => geo_unselected_nonneighbor_both_visits_one_carrier hP hS
    ((mem_geoSupportUnselected_iff hP S x).mpr ⟨hxS, hxN⟩) v w hv hw

end
end SM.GeoCarrier
