import SM.FlatCarriersDefs

/-! # U3 — Corner geometry at the centre; turns (def:flat-carriers / cor:flat-carriers)

Prover unit U3 of work/drafts/flatcarriers/PLAN_FINAL.md §5, written 2026-09-13. Source rows:
def:flat-carriers / cor:flat-carriers (reference/SM/sm-3-statesum.tex:788-905), under the
hypotheses of lem:flat-sides (sm-1-polygons.tex:778-826, accepted `SM.flat_sides`). Definitions and
bundles: the library module `SM.FlatCarriersDefs`.

Contents.
1. The successor gap `¬ traversalBetween (pos a) (pos u) (pos (ρ a))` is proved INTRINSICALLY on the
   geometric record domain (`geoNextMark_no_mark_between`), so no field of `GeoCarrierSpec` is needed
   for it.
2. Port of the direction lemmas of `SM/CarrierCrossings.lean:130-300` (and their supports in
   `CarrierMarkedSegments`, `CarrierSegmentGeometry`) from `Generic P` to `CrossingGeometry P`:
   `geoMarkSuccessor_position_cases`, `geoSmoothingSegment_positive_direction`, the incoming /
   outgoing directions at vertices and visits (`geo_vertex_incoming_direction`, …).
3. Block compression at the centre (`geo_block_compression`, without the union-of-segments clause),
   the corner chain from the inherited order (`geo_corner_chain`, from the `traced_successor` field
   of `GeoCarrierSpec` — U2's interface), and `geoCornerPolygon_edge` (each corner-polygon edge is a
   positive multiple of the centre edge direction of the outgoing slot), `geoCornerPolygon_turn_eq_sign`.
4. The flat centre: `nonzero_segments`, `no_antiparallel`, `turns_nonzero` (`turn = 0 ↔ corner mark
   = inl j`), `StrictBetween` and the fused multiples at `μ_j`.
5. Sides and deletion (generic): the same clauses through `geoComponentEquivGeneric` and the accepted
   `carriers_clause_ii` machinery (`CarrierCornerPolygon.lean`), transported along the list equality
   `geoComponentCornerList_eq_generic` by `generic_corner_props`.
6. Turn signs: `same_turn_signs`, `centre_turn_signs`, `extra_corner`.

Assumed interface (explicit hypotheses, never `sorry`): U2's `GeoCarrierSpec (flatCentreCG …) S`
(only `traced_successor` is used), U1's `independent_supports` output in the form
`IsDecomposition … (transportSupport (hs b) S)` / `IsDecomposition … (deletionSupport … S)`, and the
side facts of lem:flat-sides read at the side parameter (chi agreement off `turnSupport j`, crossing
sign agreement), which `flat_sides_side_facts` below extracts from `FlatSidesData`. -/

namespace SM

open Carrier

namespace GeoCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-! ## 1. The successor gap, intrinsically -/

/-- No mark lies strictly in the oriented cyclic gap between a mark and its `ρ`-successor
(port of `nextMark_no_mark_between`; sorted-list argument, no genericity). -/
theorem geoNextMark_no_mark_between (hP : CrossingGeometry P) {a b : Mark P}
    (hnext : geoNextMark hP a = b) (u : Mark P) :
    ¬ traversalBetween (geoMarkPosition hP a) (geoMarkPosition hP u) (geoMarkPosition hP b) := by
  classical
  let d : DecidableEq (Mark P) := inferInstance
  let _ := geoMarkLinearOrder hP
  rw [geoNextMark_eq_list_next] at hnext
  have hnext' : @List.next (Mark P) d (Finset.univ : Finset (Mark P)).sort a
      ((Finset.mem_sort _).mpr (Finset.mem_univ a)) = b := hnext
  have hd : d = (fun a b : Mark P => LinearOrder.toDecidableEq a b) := Subsingleton.elim _ _
  rw [hd] at hnext'
  exact sorted_next_no_cyclic_between (Finset.univ : Finset (Mark P))
    (Finset.mem_univ a) (Finset.mem_univ b) hnext' u (Finset.mem_univ u)

theorem geoMarkSuccessor_no_mark_between (hP : CrossingGeometry P) (a u : Mark P) :
    ¬ traversalBetween (geoMarkPosition hP a) (geoMarkPosition hP u)
      (geoMarkPosition hP (geoMarkSuccessor hP a)) :=
  geoNextMark_no_mark_between hP rfl u

/-- `ρ` has no fixed mark: its single cycle contains the distinct vertices `0` and `1`. -/
theorem geoMarkSuccessor_ne_self (hn : 3 ≤ n) (hP : CrossingGeometry P) (a : Mark P) :
    geoMarkSuccessor hP a ≠ a := by
  have : Fact (1 < n) := ⟨by omega⟩
  intro ha
  have h0 := (geoMarkSuccessor_sameCycle hP a (Sum.inl (0 : ZMod n))).eq_of_left ha
  have h1 := (geoMarkSuccessor_sameCycle hP a (Sum.inl (1 : ZMod n))).eq_of_left ha
  have h01 : (0 : ZMod n) = 1 := Sum.inl.inj (h0.symm.trans h1)
  have hz : (0 : ℕ) = 1 := by
    simpa only [ZMod.val_zero, ZMod.val_one] using congrArg ZMod.val h01
  omega

/-! ## 2. Position cases and subsegment data (port of `CarrierMarkedSegments`) -/

/-- Consecutive marks lie in increasing parameter order on one edge, or the successor is the next
vertex (port of `markSuccessor_position_cases`). -/
theorem geoMarkSuccessor_position_cases (hn : 3 ≤ n) (hP : CrossingGeometry P) (a : Mark P) :
    ((geoMarkPosition hP (geoMarkSuccessor hP a)).1 = (geoMarkPosition hP a).1 ∧
      (geoMarkPosition hP a).2.val < (geoMarkPosition hP (geoMarkSuccessor hP a)).2.val) ∨
      geoMarkSuccessor hP a = Sum.inl ((geoMarkPosition hP a).1 + 1) := by
  have : Fact (1 < n) := ⟨by omega⟩
  let p := geoMarkPosition hP a
  let r := geoMarkPosition hP (geoMarkSuccessor hP a)
  let i := p.1
  let r' := traversalShift i r
  let z : Set.Ico (0 : ℝ) 1 := ⟨0, le_rfl, zero_lt_one⟩
  have hp : traversalShift i p = ((0 : ZMod n), p.2) := by
    simp [traversalShift, i]
  have hv : traversalShift i (geoMarkPosition hP (Sum.inl (i + 1))) = ((1 : ZMod n), z) := by
    apply Prod.ext
    · change (i + 1) - i = 1
      abel
    · apply Subtype.ext
      rfl
  have hgap : ¬ traversalBetween ((0 : ZMod n), p.2) ((1 : ZMod n), z) r' := by
    intro h
    have hshift : traversalBetween (traversalShift i p)
        (traversalShift i (geoMarkPosition hP (Sum.inl (i + 1)))) (traversalShift i r) := by
      simpa only [hp, hv] using h
    exact (geoMarkSuccessor_no_mark_between hP a (Sum.inl (i + 1)))
      ((traversalBetween_shift i p (geoMarkPosition hP (Sum.inl (i + 1))) r).mp hshift)
  have hk0 : traversalKey ((0 : ZMod n), p.2) = p.2.val := by
    simp [traversalKey]
  have hk1 : traversalKey ((1 : ZMod n), z) = 1 := by
    simp [traversalKey, z, ZMod.val_one]
  have hne : traversalKey r' ≠ p.2.val := by
    intro he
    have hkey : traversalKey (traversalShift i r) = traversalKey (traversalShift i p) := by
      rw [hp, hk0]
      exact he
    have hrp : r = p := (traversalShiftEquiv i).injective (traversalKey_injective hkey)
    exact (geoMarkSuccessor_ne_self hn hP a) (geoMarkPosition_injective hP hrp)
  have hlt : p.2.val < traversalKey r' := by
    by_contra h
    have hle := le_of_not_gt h
    have hstrict := lt_of_le_of_ne hle hne
    apply hgap
    exact Or.inr (Or.inr ⟨by simpa only [hk0] using hstrict,
      by simpa only [hk0, hk1] using p.2.property.2⟩)
  have hle : traversalKey r' ≤ 1 := by
    by_contra h
    have hstrict : 1 < traversalKey r' := lt_of_not_ge h
    apply hgap
    exact Or.inl ⟨by simpa only [hk0, hk1] using p.2.property.2, by simpa only [hk1] using hstrict⟩
  have hval : r'.1.val ≤ 1 := by
    have hp0 := r'.2.property.1
    have hval' : (r'.1.val : ℝ) ≤ 1 := by
      dsimp only [traversalKey] at hle
      linarith
    exact_mod_cast hval'
  have hcases : r'.1.val = 0 ∨ r'.1.val = 1 := by omega
  rcases hcases with hzero | hone
  · have hr0 : r'.1 = 0 := ZMod.val_injective n (by simpa only [ZMod.val_zero] using hzero)
    have hri : r.1 = p.1 := by
      have he : r.1 - i = 0 := hr0
      exact sub_eq_zero.mp he
    have hk : traversalKey r' = r.2.val := by
      change (r'.1.val : ℝ) + r.2.val = r.2.val
      rw [hr0, ZMod.val_zero, Nat.cast_zero, zero_add]
    exact Or.inl ⟨hri, by simpa only [hk] using hlt⟩
  · have hr1 : r'.1 = 1 := ZMod.val_injective n (hone.trans (ZMod.val_one n).symm)
    have hrt : r.2.val = 0 := by
      have hp0 : 0 ≤ r.2.val := r.2.property.1
      have hk : traversalKey r' = 1 + r.2.val := by
        change (r'.1.val : ℝ) + r.2.val = 1 + r.2.val
        rw [hr1, ZMod.val_one, Nat.cast_one]
      rw [hk] at hle
      linarith
    have hri : r.1 = i + 1 := by
      have he : r.1 - i = 1 := hr1
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp he)
    right
    apply geoMarkPosition_injective hP
    change r = geoMarkPosition hP (Sum.inl (i + 1))
    apply Prod.ext
    · exact hri
    · apply Subtype.ext
      exact hrt

/-- The `ρ`-successor lies a positive parameter distance ahead on the starting edge, up to and
including parameter one (port of `markSuccessor_subsegment_data`). -/
theorem geoMarkSuccessor_subsegment_data (hn : 3 ≤ n) (hP : CrossingGeometry P) (a : Mark P) :
    ∃ t : ℝ, (geoMarkPosition hP a).2.val < t ∧ t ≤ 1 ∧
      traversalEvaluation P (geoMarkPosition hP (geoMarkSuccessor hP a)) =
        edgePoint P (geoMarkPosition hP a).1 t := by
  rcases geoMarkSuccessor_position_cases hn hP a with ⟨hi, ht⟩ | hv
  · refine ⟨(geoMarkPosition hP (geoMarkSuccessor hP a)).2.val, ht,
      (geoMarkPosition hP (geoMarkSuccessor hP a)).2.property.2.le, ?_⟩
    unfold traversalEvaluation
    rw [hi]
  · refine ⟨1, (geoMarkPosition hP a).2.property.2, le_rfl, ?_⟩
    rw [hv, geoMarkPosition_evaluation_vertex]
    exact (edgePoint_one P (geoMarkPosition hP a).1).symm

/-- Both visits of a crossing evaluate to the crossing point, so the selected exchange keeps the
plane point (port of `selectedMarkPerm_evaluation`). -/
theorem geoSelectedMarkPerm_evaluation (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (a : Mark P) :
    traversalEvaluation P (geoMarkPosition hP (selectedMarkPerm S a)) =
      traversalEvaluation P (geoMarkPosition hP a) := by
  cases a with
  | inl i => rfl
  | inr v =>
    rw [selectedMarkPerm_visit, geoMarkPosition_evaluation_visit,
      geoMarkPosition_evaluation_visit, selectedVisitTwin_crossing]

/-- The outgoing segment of `a` is a positive piece of the edge of its outgoing slot (port of
`smoothingSegment_subsegment_data`). -/
theorem geoSmoothingSegment_subsegment_data (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    let p := geoMarkPosition hP (selectedMarkPerm S a)
    ∃ t : ℝ, p.2.val < t ∧ t ≤ 1 ∧
      traversalEvaluation P (geoMarkPosition hP a) = edgePoint P p.1 p.2.val ∧
      traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) =
        edgePoint P p.1 t ∧
      ∀ u : ℝ, geoSmoothingSegment hP S a u = edgePoint P p.1 (p.2.val + u * (t - p.2.val)) := by
  dsimp only
  obtain ⟨t, hst, ht1, he⟩ := geoMarkSuccessor_subsegment_data hn hP (selectedMarkPerm S a)
  have hstart : traversalEvaluation P (geoMarkPosition hP a) =
      edgePoint P (geoMarkPosition hP (selectedMarkPerm S a)).1
        (geoMarkPosition hP (selectedMarkPerm S a)).2.val :=
    (geoSelectedMarkPerm_evaluation hP S a).symm
  have hend : traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) =
      edgePoint P (geoMarkPosition hP (selectedMarkPerm S a)).1 t := he
  refine ⟨t, hst, ht1, hstart, hend, ?_⟩
  intro u
  unfold geoSmoothingSegment
  rw [hstart, hend, edgePoint_affine]

/-- The displacement from a mark to its `ρ_S`-successor is a positive multiple of the edge of its
outgoing slot (port of `smoothingSegment_positive_direction`). -/
theorem geoSmoothingSegment_positive_direction (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) -
        traversalEvaluation P (geoMarkPosition hP a) =
        c • edge P (geoMarkPosition hP (selectedMarkPerm S a)).1 := by
  obtain ⟨t, hst, _, hstart, hend, _⟩ := geoSmoothingSegment_subsegment_data hn hP S a
  refine ⟨t - (geoMarkPosition hP (selectedMarkPerm S a)).2.val, sub_pos.mpr hst, ?_⟩
  rw [hstart, hend, edgePoint_sub_edgePoint]

theorem geoSmoothingSegment_displacement_ne_zero (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) -
      traversalEvaluation P (geoMarkPosition hP a) ≠ 0 := by
  obtain ⟨c, hc, he⟩ := geoSmoothingSegment_positive_direction hn hP S a
  rw [he]
  exact smul_ne_zero (ne_of_gt hc) (hP.1 _)

theorem geoSmoothingSuccessor_ne_self (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) : geoSmoothingSuccessor hP S a ≠ a := by
  intro he
  have hne := geoSmoothingSegment_displacement_ne_zero hn hP S a
  rw [he, sub_self] at hne
  exact hne rfl

/-! ## 3. Edges of incoming segments (port of `CarrierCrossings` §2, §4) -/

/-- The mark before a crossing visit lies on the visit's own edge. -/
theorem geoMarkSuccessor_symm_visit_edge (hn : 3 ≤ n) (hP : CrossingGeometry P) (v : Visit P) :
    (geoMarkPosition hP ((geoMarkSuccessor hP).symm (Sum.inr v))).1 = v.2.val := by
  have hb : geoMarkSuccessor hP ((geoMarkSuccessor hP).symm (Sum.inr v)) = Sum.inr v :=
    (geoMarkSuccessor hP).apply_symm_apply (Sum.inr v)
  rcases geoMarkSuccessor_position_cases hn hP ((geoMarkSuccessor hP).symm (Sum.inr v)) with
    ⟨hi, _⟩ | hv
  · rw [hb] at hi
    exact hi.symm
  · rw [hb] at hv
    exact (Sum.inr_ne_inl hv).elim

/-- The mark before the vertex `i` lies on the edge `i - 1`. -/
theorem geoMarkSuccessor_symm_vertex_edge (hn : 3 ≤ n) (hP : CrossingGeometry P) (i : ZMod n) :
    (geoMarkPosition hP ((geoMarkSuccessor hP).symm (Sum.inl i))).1 = i - 1 := by
  have hb : geoMarkSuccessor hP ((geoMarkSuccessor hP).symm (Sum.inl i)) = Sum.inl i :=
    (geoMarkSuccessor hP).apply_symm_apply (Sum.inl i)
  rcases geoMarkSuccessor_position_cases hn hP ((geoMarkSuccessor hP).symm (Sum.inl i)) with
    ⟨_, ht⟩ | hv
  · rw [hb] at ht
    have h0 : (0 : ℝ) ≤ (geoMarkPosition hP ((geoMarkSuccessor hP).symm (Sum.inl i))).2.val :=
      (geoMarkPosition hP ((geoMarkSuccessor hP).symm (Sum.inl i))).2.property.1
    have hz : (geoMarkPosition hP (Sum.inl i)).2.val = 0 := rfl
    rw [hz] at ht
    exact absurd ht (not_lt.mpr h0)
  · rw [hb] at hv
    have he := Sum.inl.inj hv
    exact eq_sub_iff_add_eq.mpr he.symm

/-- The incoming displacement at `a` is a positive multiple of the edge of its `ρ`-predecessor. -/
theorem geoSmoothingSegment_positive_direction_of_succ (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) {a b : Mark P} (hba : geoSmoothingSuccessor hP S b = a) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hP a) - traversalEvaluation P (geoMarkPosition hP b) =
        c • edge P (geoMarkPosition hP ((geoMarkSuccessor hP).symm a)).1 := by
  have hsel : selectedMarkPerm S b = (geoMarkSuccessor hP).symm a := by
    rw [Equiv.eq_symm_apply]
    exact hba
  obtain ⟨c, hc, he⟩ := geoSmoothingSegment_positive_direction hn hP S b
  rw [hba, hsel] at he
  exact ⟨c, hc, he⟩

theorem geoSmoothingSegment_incoming_positive_direction (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hP a) -
        traversalEvaluation P (geoMarkPosition hP ((geoSmoothingSuccessor hP S).symm a)) =
        c • edge P (geoMarkPosition hP ((geoMarkSuccessor hP).symm a)).1 :=
  geoSmoothingSegment_positive_direction_of_succ hn hP S
    ((geoSmoothingSuccessor hP S).apply_symm_apply a)

/-- Incoming direction at a visit: a positive multiple of the visited edge. -/
theorem geo_visit_incoming_direction (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hP (Sum.inr v)) -
        traversalEvaluation P (geoMarkPosition hP ((geoSmoothingSuccessor hP S).symm (Sum.inr v))) =
        c • edge P v.2.val := by
  obtain ⟨c, hc, he⟩ := geoSmoothingSegment_incoming_positive_direction hn hP S (Sum.inr v)
  rw [geoMarkSuccessor_symm_visit_edge hn hP v] at he
  exact ⟨c, hc, he⟩

/-- Outgoing direction at a selected visit: a positive multiple of the twin's edge. -/
theorem geo_selected_visit_outgoing_direction (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S (Sum.inr v))) -
        traversalEvaluation P (geoMarkPosition hP (Sum.inr v)) =
        c • edge P (visitTwin v).2.val := by
  obtain ⟨c, hc, he⟩ := geoSmoothingSegment_positive_direction hn hP S (Sum.inr v)
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_mem S v hv] at he
  exact ⟨c, hc, he⟩

/-- Outgoing direction at an unselected visit: along its own edge. -/
theorem geo_unselected_visit_outgoing_direction (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S (Sum.inr v))) -
        traversalEvaluation P (geoMarkPosition hP (Sum.inr v)) =
        c • edge P v.2.val := by
  obtain ⟨c, hc, he⟩ := geoSmoothingSegment_positive_direction hn hP S (Sum.inr v)
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_not_mem S v hv] at he
  exact ⟨c, hc, he⟩

/-- Outgoing direction at the vertex `i`: a positive multiple of `edge P i`. -/
theorem geo_vertex_outgoing_direction (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (i : ZMod n) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S (Sum.inl i))) - P i =
        c • edge P i := by
  obtain ⟨c, hc, he⟩ := geoSmoothingSegment_positive_direction hn hP S (Sum.inl i)
  rw [selectedMarkPerm_vertex, geoMarkPosition_evaluation_vertex] at he
  exact ⟨c, hc, he⟩

/-- Incoming direction at the vertex `i`: a positive multiple of `edge P (i - 1)`. -/
theorem geo_vertex_incoming_direction (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (i : ZMod n) :
    ∃ c : ℝ, 0 < c ∧
      P i - traversalEvaluation P (geoMarkPosition hP ((geoSmoothingSuccessor hP S).symm (Sum.inl i))) =
        c • edge P (i - 1) := by
  obtain ⟨c, hc, he⟩ := geoSmoothingSegment_incoming_positive_direction hn hP S (Sum.inl i)
  rw [geoMarkSuccessor_symm_vertex_edge hn hP i, geoMarkPosition_evaluation_vertex] at he
  exact ⟨c, hc, he⟩


/-! ## 4. Outgoing slot, incoming edge, block compression (port of `CarrierCornerPolygon` §0-2) -/

/-- The original traversal position of the outgoing slot of `a`: `a` itself if unselected, its twin
if selected. -/
def geoOutSlot (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) :
    TraversalPoint n :=
  geoMarkPosition hP (selectedMarkPerm S a)

/-- The original edge carrying the incoming segment at `b` (the edge of its `ρ`-predecessor). -/
def geoInEdge (hP : CrossingGeometry P) (b : Mark P) : ZMod n :=
  (geoMarkPosition hP ((geoMarkSuccessor hP).symm b)).1

omit [NeZero n] in
theorem geometricVisitPosition_edge (hP : CrossingGeometry P) (v : Visit P) :
    (geometricVisitPosition hP v).1 = v.2.val := rfl

omit [NeZero n] in
theorem geometricVisitPosition_parameter (hP : CrossingGeometry P) (v : Visit P) :
    (geometricVisitPosition hP v).2.val = visitParameter v := rfl

omit [NeZero n] in
theorem geoOutSlot_vertex (hP : CrossingGeometry P) (S : Finset (Crossing P)) (i : ZMod n) :
    (geoOutSlot hP S (Sum.inl i)).1 = i := rfl

theorem geoOutSlot_selected (hP : CrossingGeometry P) (S : Finset (Crossing P)) (v : Visit P)
    (hv : v.1 ∈ S) : (geoOutSlot hP S (Sum.inr v)).1 = (visitTwin v).2.val := by
  unfold geoOutSlot
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_mem S v hv]
  rfl

theorem geoOutSlot_unselected (hP : CrossingGeometry P) (S : Finset (Crossing P)) (v : Visit P)
    (hv : v.1 ∉ S) : geoOutSlot hP S (Sum.inr v) = geometricVisitPosition hP v := by
  unfold geoOutSlot
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_not_mem S v hv]
  rfl

theorem geoInEdge_vertex (hn : 3 ≤ n) (hP : CrossingGeometry P) (i : ZMod n) :
    geoInEdge hP (Sum.inl i) = i - 1 :=
  geoMarkSuccessor_symm_vertex_edge hn hP i

theorem geoInEdge_visit (hn : 3 ≤ n) (hP : CrossingGeometry P) (v : Visit P) :
    geoInEdge hP (Sum.inr v) = v.2.val :=
  geoMarkSuccessor_symm_visit_edge hn hP v

/-- If `ρ_S x = b`, the outgoing edge of `x` is the incoming edge of `b`. -/
theorem geoOutSlot_eq_of_succ (hP : CrossingGeometry P) (S : Finset (Crossing P)) {x b : Mark P}
    (hxb : geoSmoothingSuccessor hP S x = b) : (geoOutSlot hP S x).1 = geoInEdge hP b := by
  unfold geoOutSlot geoInEdge
  have hsel : selectedMarkPerm S x = (geoMarkSuccessor hP).symm b := by
    rw [Equiv.eq_symm_apply]
    exact hxb
  rw [hsel]

theorem geo_evaluation_eq_outSlot (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) :
    traversalEvaluation P (geoMarkPosition hP a) =
      edgePoint P (geoOutSlot hP S a).1 (geoOutSlot hP S a).2.val :=
  (geoSelectedMarkPerm_evaluation hP S a).symm

theorem geo_subsegment_data (hn : 3 ≤ n) (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (a : Mark P) :
    ∃ t : ℝ, (geoOutSlot hP S a).2.val < t ∧ t ≤ 1 ∧
      traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) =
        edgePoint P (geoOutSlot hP S a).1 t := by
  obtain ⟨t, hst, ht1, _, hend, _⟩ := geoSmoothingSegment_subsegment_data hn hP S a
  exact ⟨t, hst, ht1, hend⟩

/-- An incoming segment ending at a crossing visit starts earlier on that visit's own edge. -/
theorem geo_incoming_visit_position (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (x : Mark P) (v : Visit P)
    (hx : geoSmoothingSuccessor hP S x = Sum.inr v) :
    (geoOutSlot hP S x).1 = v.2.val ∧ (geoOutSlot hP S x).2.val < visitParameter v := by
  unfold geoOutSlot
  have he : geoMarkSuccessor hP (selectedMarkPerm S x) = Sum.inr v := hx
  rcases geoMarkSuccessor_position_cases hn hP (selectedMarkPerm S x) with ⟨hi, ht⟩ | hv
  · constructor
    · simpa only [he, geoMarkPosition_visit, geometricVisitPosition_edge] using hi.symm
    · simpa only [he, geoMarkPosition_visit, geometricVisitPosition_parameter] using ht
  · have hbad := he.symm.trans hv
    cases hbad

/-- **Block compression at the centre** (port of `ccp_block_compression`, without the
union-of-segments clause): the marks `ρ_S a, …, ρ_S^{m-1} a` being unselected visits, all outgoing
slots of the block lie on the edge `e` of the outgoing slot of `a`, and `ρ_S^m a` is the point of a
parameter `t > s` on `e`. -/
theorem geo_block_compression (hn : 3 ≤ n) (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (a : Mark P) (m : ℕ) (hm : 1 ≤ m)
    (hmid : ∀ r, 1 ≤ r → r < m → ¬ IsTrueCorner S ((geoSmoothingSuccessor hP S ^ r) a)) :
    (∀ r < m, (geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ r) a)).1 = (geoOutSlot hP S a).1) ∧
    ∃ t : ℝ, (geoOutSlot hP S a).2.val < t ∧ t ≤ 1 ∧
      traversalEvaluation P (geoMarkPosition hP ((geoSmoothingSuccessor hP S ^ m) a)) =
        edgePoint P (geoOutSlot hP S a).1 t := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      obtain ⟨t, hst, ht1, hend⟩ := geo_subsegment_data hn hP S a
      refine ⟨?_, t, hst, ht1, ?_⟩
      · intro r hr
        have hr0 : r = 0 := by omega
        subst hr0
        rw [pow_zero, Equiv.Perm.one_apply]
      · rw [zero_add, pow_one]
        exact hend
    · have hmid' : ∀ r, 1 ≤ r → r < m → ¬ IsTrueCorner S ((geoSmoothingSuccessor hP S ^ r) a) :=
        fun r h1 h2 => hmid r h1 (by omega)
      obtain ⟨hedges, t, hst, ht1, hend⟩ := ih hmpos hmid'
      have hedge : edge P (geoOutSlot hP S a).1 ≠ 0 := hP.1 _
      obtain ⟨v, hxv, hvS⟩ := ccp_not_trueCorner S (hmid m hmpos (Nat.lt_succ_self m))
      have hprev : geoSmoothingSuccessor hP S ((geoSmoothingSuccessor hP S ^ (m - 1)) a) =
          (geoSmoothingSuccessor hP S ^ m) a := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ']
        congr 2
        omega
      have hin := geo_incoming_visit_position hn hP S _ v (hprev.trans hxv)
      have hedge_prev : (geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ (m - 1)) a)).1 =
          (geoOutSlot hP S a).1 :=
        hedges (m - 1) (by omega)
      have hev : v.2.val = (geoOutSlot hP S a).1 := hin.1.symm.trans hedge_prev
      have hslot : geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ m) a) =
          geometricVisitPosition hP v := by
        rw [hxv]
        exact geoOutSlot_unselected hP S v hvS
      have hxeval : traversalEvaluation P (geoMarkPosition hP ((geoSmoothingSuccessor hP S ^ m) a)) =
          edgePoint P (geoOutSlot hP S a).1 (visitParameter v) := by
        rw [hxv, geoMarkPosition_visit]
        change edgePoint P v.2.val (visitParameter v) = _
        rw [hev]
      have htv : t = visitParameter v := edgePoint_injective hedge (hend.symm.trans hxeval)
      obtain ⟨t', hst', ht1', hend'⟩ := geo_subsegment_data hn hP S ((geoSmoothingSuccessor hP S ^ m) a)
      have hslot1 : (geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ m) a)).1 = (geoOutSlot hP S a).1 := by
        rw [hslot]
        exact hev
      have hslot2 : (geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ m) a)).2.val = t := by
        rw [hslot, htv]
        rfl
      rw [hslot2] at hst'
      rw [hslot1] at hend'
      refine ⟨?_, t', lt_trans hst hst', ht1', ?_⟩
      · intro r hr
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr' | hr'
        · exact hedges r hr'
        · rw [hr']
          exact hslot1
      · rw [pow_succ', Equiv.Perm.mul_apply]
        exact hend'

/-! ## 5. The corner chain from the inherited order (U2's `traced_successor`) -/

/-- The inherited-order field of `GeoCarrierSpec` at one carrier `q`: consecutive entries of
`geoComponentMarkList hP S q` are `ρ_S`-successors (cyclically). -/
abbrev TracedSuccessor (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    Prop :=
  ∀ i : Fin (geoComponentMarkList hP S q).length,
    geoSmoothingSuccessor hP S ((geoComponentMarkList hP S q)[i.val]'i.isLt) =
      (geoComponentMarkList hP S q)[(i.val + 1) % (geoComponentMarkList hP S q).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt))

theorem tracedSuccessor_of_spec (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (hspec : GeoCarrierSpec hP S) (q : GeoComponent hP S) : TracedSuccessor hP S q :=
  hspec.traced_successor q

theorem geoCornerMark_mem (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    geoOwner hP S (geoCornerMark hP S q k) = q ∧ IsTrueCorner S (geoCornerMark hP S q k) :=
  (mem_geoComponentCornerList hP S q _).mp (List.getElem_mem (ZMod.val_lt k))

theorem geoCornerMark_mem_cornerList (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    geoCornerMark hP S q k ∈ geoComponentCornerList hP S q :=
  List.getElem_mem (ZMod.val_lt k)

/-- The corner after `c_k` is the next corner of the corner list, cyclically (port of
`ccpCornerMark_add_one`). -/
theorem geoCornerMark_add_one (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    geoCornerMark hP S q (k + 1) =
      (geoComponentCornerList hP S q).next (geoCornerMark hP S q k)
        (geoCornerMark_mem_cornerList hP S q k) := by
  unfold geoCornerMark
  rw [List.next_getElem _ (geoComponentCornerList_nodup hP S q) k.val (ZMod.val_lt k)]
  have hval : (k + 1).val = (k.val + 1) % (geoComponentCornerList hP S q).length := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    rfl
  simp only [hval]

/-- **Corner-to-corner chain at the centre.** From a true corner `a` of `q`, the next corner of the
corner list is reached in `m ≥ 1` steps of `ρ_S`, every intermediate mark not being a true corner.
Derived from the inherited order (`TracedSuccessor`) and the list lemma `firstCornerBlock`. -/
theorem geo_corner_chain (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S)
    (htr : TracedSuccessor hP S q) (a : Mark P) (ha : geoOwner hP S a = q) (hac : IsTrueCorner S a) :
    ∃ m : ℕ, 1 ≤ m ∧
      (geoSmoothingSuccessor hP S ^ m) a =
        (geoComponentCornerList hP S q).next a ((mem_geoComponentCornerList hP S q a).mpr ⟨ha, hac⟩) ∧
      ∀ r, 1 ≤ r → r < m → ¬ IsTrueCorner S ((geoSmoothingSuccessor hP S ^ r) a) := by
  set L := geoComponentMarkList hP S q with hLdef
  have hNL : L.Nodup := geoComponentMarkList_nodup hP S q
  have haL : a ∈ L := (mem_geoComponentMarkList hP S q a).mpr ha
  obtain ⟨A, R, hAR⟩ := List.mem_iff_append.mp haL
  have hrot : L.rotate A.length = a :: (R ++ A) := by
    rw [hAR, List.rotate_append_length_eq, List.cons_append]
  have hN : (a :: (R ++ A)).Nodup := by
    rw [← hrot]
    exact List.nodup_rotate.mpr hNL
  have hk : A.length ≤ L.length := by
    rw [hAR]
    simp
  let p : Mark P → Bool := fun m => decide (IsTrueCorner S m)
  have hpa : p a = true := by simp only [p, hac, decide_true]
  obtain ⟨M, b, B, hsplit, hM, hb, hnext, hprefix, _, _⟩ := firstCornerBlock p a (R ++ A) hN hpa
  have heqOn : Set.EqOn (a :: (R ++ A)).formPerm (geoSmoothingSuccessor hP S)
      {m | m ∈ a :: (R ++ A)} := by
    intro m hm
    have hmL : m ∈ L := by
      have hm' : m ∈ L.rotate A.length := by
        rw [hrot]
        exact hm
      exact List.mem_rotate.mp hm'
    obtain ⟨i, hi, hmi⟩ := List.getElem_of_mem hmL
    change (a :: (R ++ A)).formPerm m = geoSmoothingSuccessor hP S m
    rw [← hrot, List.formPerm_rotate L hNL, ← hmi, List.formPerm_apply_getElem L hNL i hi]
    exact (htr ⟨i, hi⟩).symm
  have hpow : ∀ i (hi : i < M.length + 2),
      (geoSmoothingSuccessor hP S ^ i) a = (a :: (M ++ [b]))[i]'(by simp; omega) := by
    intro i hi
    have hlen := hprefix.length_le
    simp at hlen
    rw [ccp_pow_apply_closed_list _ a (R ++ A) hN heqOn i (by simp only [List.length_append]; omega)]
    exact (hprefix.getElem (by simp; omega)).symm
  have hrotF : (L.filter p) ~r ((a :: (R ++ A)).filter p) := by
    rw [← hrot, List.rotate_eq_drop_append_take hk, List.filter_append]
    conv_lhs => rw [← List.take_append_drop A.length L, List.filter_append]
    exact List.isRotated_append
  have haK : a ∈ geoComponentCornerList hP S q :=
    (mem_geoComponentCornerList hP S q a).mpr ⟨ha, hac⟩
  have hnextK : (geoComponentCornerList hP S q).next a haK = b := by
    rw [← hnext]
    exact List.isRotated_next_eq hrotF (hNL.filter p) haK
  refine ⟨M.length + 1, by omega, ?_, ?_⟩
  · rw [hnextK, hpow (M.length + 1) (by omega)]
    simp
  · intro r hr1 hrm
    rw [hpow r (by omega)]
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hr' : r' < M.length := by omega
    rw [List.getElem_cons_succ, List.getElem_append_left hr']
    intro hc
    have hMx := hM _ (List.getElem_mem hr')
    simp only [p, hc, decide_true] at hMx
    exact Bool.true_eq_false.mp hMx

/-! ## 6. Edges and turns of the corner polygon at the centre -/

/-- **Compressed block between consecutive corners at the centre**: `c_{k+1}` is reached from `c_k`
in `m ≥ 1` steps through non-corners, the edge `c_{k+1} - c_k` of the corner polygon is a positive
multiple of the direction of the edge `e` of the outgoing slot of `c_k`, and `e` is the incoming
edge at `c_{k+1}`. -/
theorem geoCornerPolygon_edge_data (hn : 3 ≤ n) (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (htr : TracedSuccessor hP S q) (k : ZMod (geoCornerCount hP S q)) :
    ∃ m : ℕ, 1 ≤ m ∧
      (geoSmoothingSuccessor hP S ^ m) (geoCornerMark hP S q k) = geoCornerMark hP S q (k + 1) ∧
      (∀ r, 1 ≤ r → r < m →
        ¬ IsTrueCorner S ((geoSmoothingSuccessor hP S ^ r) (geoCornerMark hP S q k))) ∧
      (∃ c : ℝ, 0 < c ∧ edge (geoCornerPolygon hP S q) k =
        c • edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1) ∧
      (geoOutSlot hP S (geoCornerMark hP S q k)).1 = geoInEdge hP (geoCornerMark hP S q (k + 1)) := by
  obtain ⟨m, hm, hchain, hmid⟩ := geo_corner_chain hP S q htr _ (geoCornerMark_mem hP S q k).1
    (geoCornerMark_mem hP S q k).2
  rw [← geoCornerMark_add_one hP S q k] at hchain
  obtain ⟨hedges, t, hst, ht1, hend⟩ := geo_block_compression hn hP S _ m hm hmid
  have hstart : geoCornerPolygon hP S q k =
      edgePoint P (geoOutSlot hP S (geoCornerMark hP S q k)).1
        (geoOutSlot hP S (geoCornerMark hP S q k)).2.val :=
    geo_evaluation_eq_outSlot hP S _
  have hend' : geoCornerPolygon hP S q (k + 1) =
      edgePoint P (geoOutSlot hP S (geoCornerMark hP S q k)).1 t := by
    show traversalEvaluation P (geoMarkPosition hP (geoCornerMark hP S q (k + 1))) = _
    rw [← hchain]
    exact hend
  refine ⟨m, hm, hchain, hmid, ⟨t - (geoOutSlot hP S (geoCornerMark hP S q k)).2.val,
    sub_pos.mpr hst, ?_⟩, ?_⟩
  · show geoCornerPolygon hP S q (k + 1) - geoCornerPolygon hP S q k = _
    rw [hstart, hend', edgePoint_sub_edgePoint]
  · have hprev : geoSmoothingSuccessor hP S
        ((geoSmoothingSuccessor hP S ^ (m - 1)) (geoCornerMark hP S q k)) =
        geoCornerMark hP S q (k + 1) := by
      rw [← hchain, ← Equiv.Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    rw [← geoOutSlot_eq_of_succ hP S hprev]
    exact (hedges (m - 1) (by omega)).symm

/-- **`geoCornerPolygon_edge_centre`**: each edge of the corner polygon is a positive multiple of the
direction of the original edge of the outgoing slot of its starting corner. -/
theorem geoCornerPolygon_edge (hn : 3 ≤ n) (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (htr : TracedSuccessor hP S q) (k : ZMod (geoCornerCount hP S q)) :
    ∃ c : ℝ, 0 < c ∧ edge (geoCornerPolygon hP S q) k =
      c • edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1 := by
  obtain ⟨_, _, _, _, hc, _⟩ := geoCornerPolygon_edge_data hn hP S q htr k
  exact hc

theorem geoCornerPolygon_outEdge_eq_inEdge (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (htr : TracedSuccessor hP S q)
    (k : ZMod (geoCornerCount hP S q)) :
    (geoOutSlot hP S (geoCornerMark hP S q k)).1 = geoInEdge hP (geoCornerMark hP S q (k + 1)) := by
  obtain ⟨_, _, _, _, _, he⟩ := geoCornerPolygon_edge_data hn hP S q htr k
  exact he

/-- The incoming corner-polygon edge at `c_k` is a positive multiple of the original edge carrying
the incoming segment at `c_k`. -/
theorem geoCornerPolygon_edge_pred (hn : 3 ≤ n) (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (htr : TracedSuccessor hP S q) (k : ZMod (geoCornerCount hP S q)) :
    ∃ c : ℝ, 0 < c ∧ edge (geoCornerPolygon hP S q) (k - 1) =
      c • edge P (geoInEdge hP (geoCornerMark hP S q k)) := by
  obtain ⟨c, hc, he⟩ := geoCornerPolygon_edge hn hP S q htr (k - 1)
  refine ⟨c, hc, ?_⟩
  rw [he, geoCornerPolygon_outEdge_eq_inEdge hn hP S q htr (k - 1), sub_add_cancel]

theorem geoCornerPolygon_turn_det (hn : 3 ≤ n) (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (htr : TracedSuccessor hP S q) (k : ZMod (geoCornerCount hP S q)) :
    ∃ c : ℝ, 0 < c ∧
      det (edge (geoCornerPolygon hP S q) (k - 1)) (edge (geoCornerPolygon hP S q) k) =
        c * det (edge P (geoInEdge hP (geoCornerMark hP S q k)))
          (edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1) := by
  obtain ⟨c₁, hc₁, he₁⟩ := geoCornerPolygon_edge_pred hn hP S q htr k
  obtain ⟨c₂, hc₂, he₂⟩ := geoCornerPolygon_edge hn hP S q htr k
  refine ⟨c₁ * c₂, mul_pos hc₁ hc₂, ?_⟩
  rw [he₁, he₂, ccp_det_smul_smul]

/-- **`turn = sign det(in, out)`** at every corner of a centre carrier. -/
theorem geoCornerPolygon_turn_eq_sign (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (htr : TracedSuccessor hP S q)
    (k : ZMod (geoCornerCount hP S q)) :
    turn (geoCornerPolygon hP S q) k =
      SignType.sign (det (edge P (geoInEdge hP (geoCornerMark hP S q k)))
        (edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1)) := by
  obtain ⟨c, hc, he⟩ := geoCornerPolygon_turn_det hn hP S q htr k
  rw [turn_det, he, sign_mul, sign_pos hc, one_mul]

/-- Every corner-polygon edge of a centre carrier is nonzero. -/
theorem geoCornerPolygon_edge_ne_zero (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (htr : TracedSuccessor hP S q)
    (k : ZMod (geoCornerCount hP S q)) : edge (geoCornerPolygon hP S q) k ≠ 0 := by
  obtain ⟨c, hc, he⟩ := geoCornerPolygon_edge hn hP S q htr k
  rw [he]
  exact smul_ne_zero hc.ne' (hP.1 _)

/-- Where the original in/out determinant is nonzero the corner is not antiparallel. -/
theorem geoCornerPolygon_not_antiparallel_of_det (hn : 3 ≤ n) (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (htr : TracedSuccessor hP S q)
    (k : ZMod (geoCornerCount hP S q))
    (hdet : det (edge P (geoInEdge hP (geoCornerMark hP S q k)))
      (edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1) ≠ 0) :
    ¬ ∃ r : ℝ, r < 0 ∧
      edge (geoCornerPolygon hP S q) k = r • edge (geoCornerPolygon hP S q) (k - 1) := by
  rintro ⟨r, _, hr⟩
  obtain ⟨c, hc, he⟩ := geoCornerPolygon_turn_det hn hP S q htr k
  apply mul_ne_zero hc.ne' hdet
  rw [← he, hr]
  exact det_smul_self _ r


/-! ## 7. Generic configurations: transfer along `geoComponentCornerList_eq_generic` -/

/-- The closed polygon read at the entries of a nonempty list (`geoCornerPolygon` and
`ccpCornerPolygon` are both of this form, definitionally). -/
abbrev polyOfList {α : Type*} (L : List α) [NeZero L.length] (pos : α → Plane) :
    LabelledTuple L.length :=
  fun k => pos (L[k.val]'(ZMod.val_lt k))

/-- The accepted clause (ii) facts (`CarrierCornerPolygon.lean`), stated for any list equal to the
accepted corner list and any position map equal to the accepted one, so that they transport along a
propositional equality of lists (the index types `ZMod L.length` are identified by `subst`). -/
theorem generic_corner_props (hn : 3 ≤ n) (hP : Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) (q' : Component hn hP S) (L : List (Mark P))
    (hL : L = ccpCornerList hn hP S q') [hNZ : NeZero L.length] (pos : Mark P → Plane)
    (hpos : pos = fun a => traversalEvaluation P (markPosition hn hP.1 a)) (k : ZMod L.length) :
    edge (polyOfList L pos) k ≠ 0 ∧
    (¬ ∃ r : ℝ, r < 0 ∧ edge (polyOfList L pos) k = r • edge (polyOfList L pos) (k - 1)) ∧
    turn (polyOfList L pos) k ≠ 0 ∧
    turn (polyOfList L pos) k =
      SignType.sign (det (edge P (ccpInEdge hn hP (L[k.val]'(ZMod.val_lt k))))
        (edge P (ccpOutSlot hn hP S (L[k.val]'(ZMod.val_lt k))).1)) := by
  subst hpos
  subst hL
  exact ⟨ccpCornerPolygon_edge_ne_zero hn hP hS q' k, ccpCornerPolygon_not_antiparallel hn hP hS q' k,
    ccpCornerPolygon_turn_ne_zero hn hP hS q' k, ccpCornerPolygon_turn_eq_sign hn hP hS q' k⟩

/-- **Generic configurations (sides, deletion).** On a generic polygon with `S` independent, every
`geoCornerPolygon` has nonzero edges, no antiparallel corner, nonzero turns, and
`turn = sign det(in, out)` in the accepted in/out-edge bookkeeping. -/
theorem generic_geoCornerPolygon_props (hn : 3 ≤ n) (hP : Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) (q : GeoComponent (generic_crossingGeometry hn hP) S)
    (k : ZMod (geoCornerCount (generic_crossingGeometry hn hP) S q)) :
    edge (geoCornerPolygon (generic_crossingGeometry hn hP) S q) k ≠ 0 ∧
    (¬ ∃ r : ℝ, r < 0 ∧ edge (geoCornerPolygon (generic_crossingGeometry hn hP) S q) k =
      r • edge (geoCornerPolygon (generic_crossingGeometry hn hP) S q) (k - 1)) ∧
    turn (geoCornerPolygon (generic_crossingGeometry hn hP) S q) k ≠ 0 ∧
    turn (geoCornerPolygon (generic_crossingGeometry hn hP) S q) k =
      SignType.sign (det (edge P (ccpInEdge hn hP (geoCornerMark (generic_crossingGeometry hn hP) S q k)))
        (edge P (ccpOutSlot hn hP S (geoCornerMark (generic_crossingGeometry hn hP) S q k)).1)) := by
  have h := @generic_corner_props n _ P hn hP S hS (geoComponentEquivGeneric hn hP S q)
    (geoComponentCornerList (generic_crossingGeometry hn hP) S q)
    (geoComponentCornerList_eq_generic hn hP S q) (geoCornerCount_neZero _ S q)
    (fun a => traversalEvaluation P (geoMarkPosition (generic_crossingGeometry hn hP) a))
    (by funext a; rw [geoMarkPosition_eq_generic hn hP]) k
  exact h

/-- On a generic polygon, `geoCornerTurn` at a true corner `a` is `sign det(in, out)`. -/
theorem generic_geoCornerTurn (hn : 3 ≤ n) (hP : Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) {a : Mark P} (ha : IsTrueCorner S a) :
    geoCornerTurn (generic_crossingGeometry hn hP) S a =
      SignType.sign (det (edge P (ccpInEdge hn hP a)) (edge P (ccpOutSlot hn hP S a).1)) := by
  unfold geoCornerTurn
  have h := (generic_geoCornerPolygon_props hn hP hS (geoOwner _ S a) (geoCornerIndex _ S a)).2.2.2
  rw [geoCornerMark_geoCornerIndex _ S ha] at h
  exact h

theorem generic_geoCornerTurn_vertex (hn : 3 ≤ n) (hP : Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) (i : ZMod n) :
    geoCornerTurn (generic_crossingGeometry hn hP) S (Sum.inl i) = turn P i := by
  rw [generic_geoCornerTurn hn hP hS (isTrueCorner_vertex S i), ccpInEdge_vertex, ccpOutSlot_vertex,
    turn_det]

theorem generic_geoCornerTurn_visit (hn : 3 ≤ n) (hP : Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ independentSupports hn hP) (v : Visit P) (hv : v.1 ∈ S) :
    geoCornerTurn (generic_crossingGeometry hn hP) S (Sum.inr v) =
      crossingSign P v.2.val (visitTwin v).2.val := by
  rw [generic_geoCornerTurn hn hP hS ((isTrueCorner_visit S v).mpr hv), ccpInEdge_visit,
    ccpOutSlot_selected hn hP S v hv]
  rfl

/-! ## 8. Small helpers -/

omit [NeZero n] in
/-- Two positive multiples of one nonzero vector in sequence: the middle point is strictly between. -/
theorem strictBetween_of_positive_multiples {a x b w : Plane} (hw : w ≠ 0) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hxa : x - a = α • w) (hbx : b - x = β • w) : StrictBetween a x b := by
  have hba : b - a = (α + β) • w := by
    rw [add_smul, ← hxa, ← hbx]
    abel
  have hsum : α + β ≠ 0 := by linarith
  refine ⟨?_, α / (α + β), div_pos hα (by linarith), ?_, ?_⟩
  · intro hab
    rw [hab, sub_self] at hba
    exact smul_ne_zero hsum hw hba.symm
  · rw [div_lt_one (by linarith)]
    linarith
  · rw [hba, smul_smul, div_mul_cancel₀ _ hsum, ← hxa]
    abel

omit [NeZero n] in
theorem turn_eq_crossingSign (Q : LabelledTuple n) (i : ZMod n) :
    turn Q i = crossingSign Q (i - 1) i := by
  rw [turn_det]
  rfl

/-- The fused-edge index of `k - 1` is the fused-edge index of `k` minus one, for `k ≠ j`. -/
theorem fusionIndex_sub_one {j k : ZMod (n + 1)} (hk : k ≠ j) :
    fusionIndex j (k - 1) = fusionIndex j k - 1 := by
  obtain ⟨ι, rfl⟩ := deletionIndex_exhaust j hk
  rw [fusionIndex_deletionIndex]
  by_cases hι : ι = 0
  · subst hι
    rw [deletionIndex_zero, add_sub_cancel_right, fusionIndex_deleted]
    ring
  · have hι' : ι - 1 ≠ -1 := by
      intro h
      apply hι
      linear_combination h
    have hnext := deletionIndex_next j hι'
    rw [sub_add_cancel] at hnext
    have h2 : deletionIndex j ι - 1 = deletionIndex j (ι - 1) := by
      rw [hnext]
      ring
    rw [h2, fusionIndex_deletionIndex]

omit [NeZero n] in
/-- The identification of visits with the same crossing supports commutes with the pairing. -/
theorem visitTransport_visitTwin {Q : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (v : Visit P) : visitTransport hs (visitTwin v) = visitTwin (visitTransport hs v) := by
  apply visitTwin_unique
  · rw [visitTransport_crossing, visitTransport_crossing, visitTwin_crossing]
  · intro h
    exact visitTwin_ne v ((visitTransport hs).injective h)

/-- The fused-edge identification of visits commutes with the pairing. -/
theorem fusionVisitEquiv_visitTwin {j : ZMod (n + 1)} (hn : 3 ≤ n) {Q : LabelledTuple (n + 1)}
    (hz : pointZeroTriples Q = {turnSupport j}) (hb : StrictBetween (Q (j - 1)) (Q j) (Q (j + 1)))
    (hc : concurrenceTriples Q = ∅) (v : Visit Q) :
    fusionVisitEquiv hn hz hb hc (visitTwin v) = visitTwin (fusionVisitEquiv hn hz hb hc v) := by
  apply visitTwin_unique
  · rw [fusionVisit_crossing, fusionVisit_crossing, visitTwin_crossing]
  · intro h
    exact visitTwin_ne v ((fusionVisitEquiv hn hz hb hc).injective h)

omit [NeZero n] in
theorem mem_transportSupport_iff {Q : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (S : Finset (Crossing P)) (x : Crossing P) :
    crossingTransport hs x ∈ transportSupport hs S ↔ x ∈ S :=
  Finset.mem_map' (crossingTransport hs).toEmbedding

theorem mem_deletionSupport_iff (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center)) (x : Crossing g.center) :
    fusionCrossingEquiv hn hz hb hc x ∈ deletionSupport hn g j hz hb hc S ↔ x ∈ S :=
  Finset.mem_map' (fusionCrossingEquiv hn hz hb hc).toEmbedding

end
end GeoCarrier

/-! ## 9. The flat centre -/

section FlatCentre

open GeoCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Original in/out determinant at a true corner of the centre: nonzero away from `μ_j` (vertex:
`τ_i ≠ 0` for `i ≠ j`, lem:flat-sides (i); selected visit: transversality of the crossing), zero at
`μ_j` (`τ_j = 0`). -/
theorem flat_centre_corner_det (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center)) (a : Mark g.center)
    (hac : IsTrueCorner S a) :
    (a ≠ Sum.inl j →
      det (edge g.center (geoInEdge (flatCentreCG hn g j hz hb hc) a))
        (edge g.center (geoOutSlot (flatCentreCG hn g j hz hb hc) S a).1) ≠ 0) ∧
    (a = Sum.inl j →
      det (edge g.center (geoInEdge (flatCentreCG hn g j hz hb hc) a))
        (edge g.center (geoOutSlot (flatCentreCG hn g j hz hb hc) S a).1) = 0) := by
  have hturn : ∀ i, turn g.center i = 0 ↔ i = j :=
    (flat_center_geometry (by omega) hz hb).2.2.2.1
  cases a with
  | inl i =>
    rw [geoInEdge_vertex (flat_hn1 hn), geoOutSlot_vertex]
    constructor
    · intro hij
      have hi : i ≠ j := fun h => hij (congrArg Sum.inl h)
      have hne : turn g.center i ≠ 0 := fun h => hi ((hturn i).mp h)
      rw [turn_det] at hne
      exact sign_ne_zero.mp hne
    · intro hij
      have hi : i = j := Sum.inl.inj hij
      have h0 : turn g.center i = 0 := (hturn i).mpr hi
      rw [turn_det] at h0
      exact sign_eq_zero_iff.mp h0
  | inr v =>
    have hv : v.1 ∈ S := hac
    rw [geoInEdge_visit (flat_hn1 hn), geoOutSlot_selected _ S v hv]
    refine ⟨fun _ => ?_, fun h => (Sum.inr_ne_inl h).elim⟩
    have hcr : IsCrossing g.center {v.2.val, (visitTwin v).2.val} := by
      rw [← visit_crossing_val_eq_pair v]
      exact v.1.property
    exact crossing_det_ne_zero_of_geometry (flatCentreCG hn g j hz hb hc) hcr

omit [NeZero n] in
/-- **cor (i) at the centre, `turns_nonzero`:** a corner turn of a centre carrier vanishes exactly
at the corner `μ_j`. -/
theorem flat_centre_turn_zero_iff (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center))
    (hspec : GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (k : ZMod (geoCornerCount (flatCentreCG hn g j hz hb hc) S q)) :
    turn (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k = 0 ↔
      geoCornerMark (flatCentreCG hn g j hz hb hc) S q k = Sum.inl j := by
  rw [geoCornerPolygon_turn_eq_sign (flat_hn1 hn) _ S q (hspec.traced_successor q) k,
    sign_eq_zero_iff]
  have hd := flat_centre_corner_det hn g j hz hb hc S _ (geoCornerMark_mem _ S q k).2
  constructor
  · intro h0
    by_contra hne
    exact hd.1 hne h0
  · exact hd.2

omit [NeZero n] in
/-- **cor (i) at the centre, `nonzero_segments` (corner edges).** -/
theorem flat_centre_edge_ne_zero (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center))
    (hspec : GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (k : ZMod (geoCornerCount (flatCentreCG hn g j hz hb hc) S q)) :
    edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k ≠ 0 :=
  geoCornerPolygon_edge_ne_zero (flat_hn1 hn) _ S q (hspec.traced_successor q) k

omit [NeZero n] in
/-- **cor (i) at the centre, `nonzero_segments` (inherited subsegments).** -/
theorem flat_centre_segment_ne (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center)) (a : Mark g.center) :
    traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a)) ≠
      traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) a) :=
  sub_ne_zero.mp (geoSmoothingSegment_displacement_ne_zero (flat_hn1 hn) _ S a)

omit [NeZero n] in
/-- **cor (i) at the centre, `no_antiparallel`:** away from `μ_j` the in/out determinant is nonzero;
at `μ_j` the two consecutive corner edges are positive multiples of `edge C (j-1)` and
`edge C j = r • edge C (j-1)`, `r > 0`, hence positive multiples of each other. -/
theorem flat_centre_not_antiparallel (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center))
    (hspec : GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (k : ZMod (geoCornerCount (flatCentreCG hn g j hz hb hc) S q)) :
    ¬ ∃ r : ℝ, r < 0 ∧
      edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k =
        r • edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) (k - 1) := by
  have htr := hspec.traced_successor q
  have hd := flat_centre_corner_det hn g j hz hb hc S _ (geoCornerMark_mem _ S q k).2
  by_cases hk : geoCornerMark (flatCentreCG hn g j hz hb hc) S q k = Sum.inl j
  · rintro ⟨ρ, hρ, he⟩
    obtain ⟨c₁, hc₁, he₁⟩ := geoCornerPolygon_edge_pred (flat_hn1 hn) _ S q htr k
    obtain ⟨c₂, hc₂, he₂⟩ := geoCornerPolygon_edge (flat_hn1 hn) _ S q htr k
    rw [hk, geoInEdge_vertex (flat_hn1 hn)] at he₁
    rw [hk, geoOutSlot_vertex] at he₂
    obtain ⟨r, hr, hrj⟩ := (flat_center_geometry (by omega) hz hb).2.2.2.2.1
    have hne : edge g.center (j - 1) ≠ 0 := (flat_center_geometry (by omega) hz hb).2.1 _
    rw [he₁, he₂, hrj, smul_smul, smul_smul] at he
    have hcoef : c₂ * r = ρ * c₁ := smul_left_injective ℝ hne he
    have h1 : 0 < c₂ * r := mul_pos hc₂ hr
    have h2 : ρ * c₁ < 0 := mul_neg_of_neg_of_pos hρ hc₁
    linarith
  · exact geoCornerPolygon_not_antiparallel_of_det (flat_hn1 hn) _ S q htr k (hd.1 hk)

/-- **cor (i) at the centre, the geometric conjuncts of `central_vs_deletion_through_mu_j`:** `μ_j`
lies strictly between its carrier neighbours, both incident displacements being positive multiples
of the fused direction `edge D (-1) = μ_{j+1} - μ_{j-1}` (eq. flatpr:fusion). -/
theorem flat_centre_mu_j_between (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center)) :
    StrictBetween
      (traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        ((geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j))))
      (g.center j)
      (traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)))) ∧
    (∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      g.center j - traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        ((geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j))) =
        r • edge (deleteVertex g.center j) (-1) ∧
      traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j))) - g.center j =
        s • edge (deleteVertex g.center j) (-1)) := by
  obtain ⟨r, hr0, hr1, hprev, hnext, _⟩ := (flat_fusion_data hn hz hb hc).2.1
  obtain ⟨c, hc0, hin⟩ := geo_vertex_incoming_direction (flat_hn1 hn) (flatCentreCG hn g j hz hb hc) S j
  obtain ⟨c', hc'0, hout⟩ := geo_vertex_outgoing_direction (flat_hn1 hn) (flatCentreCG hn g j hz hb hc) S j
  rw [hprev, smul_smul] at hin
  rw [hnext, smul_smul] at hout
  have hw : edge (deleteVertex g.center j) (-1) ≠ 0 := (flatDeletionCG hn g j hz hb hc).1 _
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  exact ⟨strictBetween_of_positive_multiples hw (mul_pos hc0 hr0) (mul_pos hc'0 h1r) hin hout,
    c * r, c' * (1 - r), mul_pos hc0 hr0, mul_pos hc'0 h1r, hin, hout⟩

end
end FlatCentre

/-! ## 10. Turn signs across the four configurations -/

section FlatTurnSigns

open GeoCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

/-- The two side facts of lem:flat-sides used by U3, read at one side `b` of the side parameter
`t`: chi agrees with the centre off `turnSupport j` (clause (i)), and crossing signs agree with the
centre at every centre crossing (clause (ii), `GeometricRecordsAgree`). -/
def SideFacts (g : WallGerm (n + 1)) (j : ZMod (n + 1)) (b : Bool) (t : g.SideParameter) : Prop :=
  (∀ a b' c : ZMod (n + 1), a ≠ b' → b' ≠ c → a ≠ c →
    ({a, b', c} : Finset (ZMod (n + 1))) ≠ turnSupport j →
    chi (g.sideTuple b t).val a b' c = chi g.center a b' c) ∧
  (∀ i k : ZMod (n + 1), IsCrossing g.center {i, k} →
    crossingSign (g.sideTuple b t).val i k = crossingSign g.center i k)

/-- `SideFacts` hold on both sides for every side parameter below lem:flat-sides' radius
(extraction from the accepted `FlatSidesData`). -/
theorem flat_sides_side_facts (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (hF : FlatSidesData hn g j hz hb hc) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧
      ∀ t : g.SideParameter, t.val < δ → ∀ b : Bool, SideFacts g j b t := by
  obtain ⟨_, _, _, _, _, _, δ, hδ, hδr, _, hloc⟩ := hF
  refine ⟨δ, hδ, hδr, ?_⟩
  intro t ht b
  have habs : |(g.sideTime b t).val| < δ := by
    cases b <;> simp only [WallGerm.sideTime, Bool.false_eq_true, ↓reduceIte, abs_neg,
      abs_of_pos t.property.1] <;> exact ht
  obtain ⟨hchi, _, _, _, _, hrec, _⟩ := hloc (g.sideTime b t) habs
  obtain ⟨_, _, _, _, hsign⟩ := hrec
  exact ⟨fun a b' c h1 h2 h3 h4 => (hchi a b' c h1 h2 h3 h4).1, hsign⟩

omit [NeZero n] in
/-- Away from `j`, the vertex turn on a side is the centre's (`chi` agreement off `turnSupport j`,
`turnSupport` injective for `n + 1 ≥ 4`). -/
theorem side_turn_eq_centre (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1)) (b : Bool)
    (t : g.SideParameter) (hsf : SideFacts g j b t) (i : ZMod (n + 1)) (hi : i ≠ j) :
    turn (g.sideTuple b t).val i = turn g.center i := by
  have : Fact (1 < n + 1) := ⟨by omega⟩
  have hts : turnSupport i ≠ turnSupport j := fun h => hi (turnSupport_injective (by omega) h)
  exact hsf.1 (i - 1) i (i + 1) (prev_ne_self i) (next_ne_self i).symm (prev_ne_next (by omega) i) hts

/-- Away from `j`, the vertex turn on the deletion at the fused index is the centre's
(`crossingSign_fusion` for all index pairs, and `fusionIndex_sub_one`). -/
theorem deletion_turn_eq_centre (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (i : ZMod (n + 1)) (hi : i ≠ j) :
    turn (deleteVertex g.center j) (fusionIndex j i) = turn g.center i := by
  have hcs := (flat_fusion_data hn hz hb hc).2.2.2.2.2.2.2.2.2.1
  rw [turn_eq_crossingSign, turn_eq_crossingSign, ← fusionIndex_sub_one hi]
  exact hcs _ _

omit [NeZero n] in
/-- The turn of a centre carrier at an original vertex `i` is `τ_i` of the centre. -/
theorem flat_centre_geoCornerTurn_vertex (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center))
    (hspec : GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S) (i : ZMod (n + 1)) :
    geoCornerTurn (flatCentreCG hn g j hz hb hc) S (Sum.inl i) = turn g.center i := by
  unfold geoCornerTurn
  rw [geoCornerPolygon_turn_eq_sign (flat_hn1 hn) _ S _ (hspec.traced_successor _),
    geoCornerMark_geoCornerIndex _ S (isTrueCorner_vertex S i), geoInEdge_vertex (flat_hn1 hn),
    geoOutSlot_vertex, turn_det]

omit [NeZero n] in
/-- The turn of a centre carrier at a selected visit `v` is `sgn det(d_{v.2}, d_{twin.2})`. -/
theorem flat_centre_geoCornerTurn_visit (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center))
    (hspec : GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S) (v : Visit g.center) (hv : v.1 ∈ S) :
    geoCornerTurn (flatCentreCG hn g j hz hb hc) S (Sum.inr v) =
      crossingSign g.center v.2.val (visitTwin v).2.val := by
  unfold geoCornerTurn
  rw [geoCornerPolygon_turn_eq_sign (flat_hn1 hn) _ S _ (hspec.traced_successor _),
    geoCornerMark_geoCornerIndex _ S ((isTrueCorner_visit S v).mpr hv), geoInEdge_visit (flat_hn1 hn),
    geoOutSlot_selected _ S v hv]
  rfl

/-- **cor (ii) `same_turn_signs`.** -/
theorem flat_same_turn_signs (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center)) (hsf : ∀ b : Bool, SideFacts g j b t)
    (hST : ∀ b : Bool, IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S))
    (hSD : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)) :
    ∀ a : Mark g.center, a ≠ Sum.inl j → IsTrueCorner S a → ∀ b : Bool,
      geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
        geoCornerTurn (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (delMark hn g j hz hb hc a) := by
  intro a ha hac b
  cases a with
  | inl i =>
    have hi : i ≠ j := fun h => ha (congrArg Sum.inl h)
    change geoCornerTurn _ _ (Sum.inl i) = geoCornerTurn _ _ (Sum.inl (fusionIndex j i))
    rw [generic_geoCornerTurn_vertex (flat_hn1 hn) _ (hST b), generic_geoCornerTurn_vertex hn _ hSD,
      side_turn_eq_centre hn g j b t (hsf b) i hi, deletion_turn_eq_centre hn g j hz hb hc i hi]
  | inr v =>
    have hv : v.1 ∈ S := hac
    have hcs := (flat_fusion_data hn hz hb hc).2.2.2.2.2.2.2.2.2.1
    have hcr : IsCrossing g.center {v.2.val, (visitTwin v).2.val} := by
      rw [← visit_crossing_val_eq_pair v]
      exact v.1.property
    change geoCornerTurn _ _ (Sum.inr (visitTransport (hs b) v)) =
      geoCornerTurn _ _ (Sum.inr (fusionVisitEquiv hn hz hb hc v))
    have hvT : (visitTransport (hs b) v).1 ∈ transportSupport (hs b) S :=
      (mem_transportSupport_iff (hs b) S v.1).mpr hv
    have hvD : (fusionVisitEquiv hn hz hb hc v).1 ∈ deletionSupport hn g j hz hb hc S :=
      (mem_deletionSupport_iff hn g j hz hb hc S v.1).mpr hv
    rw [generic_geoCornerTurn_visit (flat_hn1 hn) _ (hST b) _ hvT,
      generic_geoCornerTurn_visit hn _ hSD _ hvD, ← visitTransport_visitTwin,
      ← fusionVisitEquiv_visitTwin hn hz hb hc v, visitTransport_edge, visitTransport_edge,
      fusionVisit_edge hn hz hb hc v, fusionVisit_edge hn hz hb hc (visitTwin v),
      (hsf b).2 _ _ hcr, hcs]

/-- **cor (ii), flagged broadening `centre_turn_signs`.** -/
theorem flat_centre_turn_signs (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center))
    (hspec : GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S)
    (hSD : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)) :
    ∀ a : Mark g.center, a ≠ Sum.inl j → IsTrueCorner S a →
      geoCornerTurn (flatCentreCG hn g j hz hb hc) S a =
        geoCornerTurn (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (delMark hn g j hz hb hc a) := by
  intro a ha hac
  cases a with
  | inl i =>
    have hi : i ≠ j := fun h => ha (congrArg Sum.inl h)
    change _ = geoCornerTurn _ _ (Sum.inl (fusionIndex j i))
    rw [flat_centre_geoCornerTurn_vertex hn g j hz hb hc S hspec i,
      generic_geoCornerTurn_vertex hn _ hSD, deletion_turn_eq_centre hn g j hz hb hc i hi]
  | inr v =>
    have hv : v.1 ∈ S := hac
    have hcs := (flat_fusion_data hn hz hb hc).2.2.2.2.2.2.2.2.2.1
    change _ = geoCornerTurn _ _ (Sum.inr (fusionVisitEquiv hn hz hb hc v))
    have hvD : (fusionVisitEquiv hn hz hb hc v).1 ∈ deletionSupport hn g j hz hb hc S :=
      (mem_deletionSupport_iff hn g j hz hb hc S v.1).mpr hv
    rw [flat_centre_geoCornerTurn_visit hn g j hz hb hc S hspec v hv,
      generic_geoCornerTurn_visit hn _ hSD _ hvD, ← fusionVisitEquiv_visitTwin hn hz hb hc v,
      fusionVisit_edge hn hz hb hc v, fusionVisit_edge hn hz hb hc (visitTwin v), hcs]

omit [NeZero n] in
/-- **cor (ii) `extra_corner`.** -/
theorem flat_extra_corner (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (t : g.SideParameter) (hs : CommonSupports g t) (S : Finset (Crossing g.center))
    (hST : ∀ b : Bool, IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)) :
    ∀ b : Bool,
      geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) =
        turn (g.sideTuple b t).val j ∧
      (IsRightSide g j b t →
        geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) = -1) ∧
      (IsLeftSide g j b t →
        geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) = 1) := by
  intro b
  have h := generic_geoCornerTurn_vertex (flat_hn1 hn) (g.sideTuple b t).property (hST b) j
  exact ⟨h, fun hr => h.trans hr, fun hl => h.trans hl⟩

end
end FlatTurnSigns

/-! ## 11. The U3 bundle: the six cor fields and the two geometric conjuncts, verbatim -/

section U3Bundle

open GeoCarrier

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

/-- The fields of `FlatCarriersData` owned by U3, with the statements copied verbatim from
`SM/FlatCarriersDefs.lean` (`nonzero_segments`, `no_antiparallel`, `turns_nonzero`,
`same_turn_signs`, `centre_turn_signs`, `extra_corner`), plus the two geometric conjuncts of
`central_vs_deletion_through_mu_j` (`mu_j_between`, `mu_j_fused_multiples`). -/
structure FlatCarriersU3Data (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center)) : Prop where
  nonzero_segments :
    (∀ a : Mark g.center,
      traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a)) ≠
      traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) a)) ∧
    (∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (k : ZMod (geoCornerCount _ S q)),
      edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k ≠ 0) ∧
    (∀ b : Mark (deleteVertex g.center j),
      traversalEvaluation (deleteVertex g.center j) (geoMarkPosition (flatDeletionCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)) ≠
      traversalEvaluation (deleteVertex g.center j) (geoMarkPosition (flatDeletionCG hn g j hz hb hc) b)) ∧
    (∀ (q : GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S))
      (k : ZMod (geoCornerCount _ _ q)),
      edge (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) q) k
        ≠ 0) ∧
    (∀ b : Bool,
      (∀ a : Mark (g.sideTuple b t).val,
        traversalEvaluation (g.sideTuple b t).val (geoMarkPosition (flatSideCG hn g b t)
          (geoSmoothingSuccessor (flatSideCG hn g b t) (transportSupport (hs b) S) a)) ≠
        traversalEvaluation (g.sideTuple b t).val (geoMarkPosition (flatSideCG hn g b t) a)) ∧
      ∀ (q : GeoComponent (flatSideCG hn g b t) (transportSupport (hs b) S))
        (k : ZMod (geoCornerCount _ _ q)),
        edge (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S) q) k ≠ 0)
  no_antiparallel :
    (∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (k : ZMod (geoCornerCount _ S q)),
      ¬ ∃ r : ℝ, r < 0 ∧
        edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k =
          r • edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) (k - 1)) ∧
    (∀ (q : GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S))
      (k : ZMod (geoCornerCount _ _ q)),
      ¬ ∃ r : ℝ, r < 0 ∧
        edge (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) q) k =
          r • edge (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
            (deletionSupport hn g j hz hb hc S) q) (k - 1)) ∧
    (∀ (b : Bool) (q : GeoComponent (flatSideCG hn g b t) (transportSupport (hs b) S))
      (k : ZMod (geoCornerCount _ _ q)),
      ¬ ∃ r : ℝ, r < 0 ∧
        edge (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S) q) k =
          r • edge (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S) q) (k - 1))
  turns_nonzero :
    (∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (k : ZMod (geoCornerCount _ S q)),
      turn (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k = 0 ↔
        geoCornerMark (flatCentreCG hn g j hz hb hc) S q k = Sum.inl j) ∧
    (∀ (q : GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S))
      (k : ZMod (geoCornerCount _ _ q)),
      turn (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) q) k
        ≠ 0) ∧
    (∀ (b : Bool) (q : GeoComponent (flatSideCG hn g b t) (transportSupport (hs b) S))
      (k : ZMod (geoCornerCount _ _ q)),
      turn (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S) q) k ≠ 0)
  same_turn_signs : ∀ a : Mark g.center, a ≠ Sum.inl j → IsTrueCorner S a → ∀ b : Bool,
    geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
      geoCornerTurn (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (delMark hn g j hz hb hc a)
  centre_turn_signs : ∀ a : Mark g.center, a ≠ Sum.inl j → IsTrueCorner S a →
    geoCornerTurn (flatCentreCG hn g j hz hb hc) S a =
      geoCornerTurn (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (delMark hn g j hz hb hc a)
  extra_corner : ∀ b : Bool,
    geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) =
      turn (g.sideTuple b t).val j ∧
    (IsRightSide g j b t →
      geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) = -1) ∧
    (IsLeftSide g j b t →
      geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) = 1)
  mu_j_between :
    StrictBetween
      (traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        ((geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j))))
      (g.center j)
      (traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j))))
  mu_j_fused_multiples :
    ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      g.center j - traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        ((geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j))) =
        r • edge (deleteVertex g.center j) (-1) ∧
      traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j))) - g.center j =
        s • edge (deleteVertex g.center j) (-1)

/-- **U3, assembled.** Hypotheses beyond lem:flat-sides' domain: U2's `GeoCarrierSpec` at the centre
(only `traced_successor` is used), U1's `independent_supports` output on both sides and on the
deletion, and the side facts of lem:flat-sides at `t` (`flat_sides_side_facts`). -/
theorem flat_carriers_U3 (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center))
    (hspec : GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S)
    (hsf : ∀ b : Bool, SideFacts g j b t)
    (hST : ∀ b : Bool, IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S))
    (hSD : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)) :
    FlatCarriersU3Data hn g j hz hb hc t hs S where
  nonzero_segments := by
    refine ⟨flat_centre_segment_ne hn g j hz hb hc S,
      flat_centre_edge_ne_zero hn g j hz hb hc S hspec, ?_, ?_, ?_⟩
    · intro b
      exact sub_ne_zero.mp (geoSmoothingSegment_displacement_ne_zero hn _ _ b)
    · intro q k
      exact (generic_geoCornerPolygon_props hn (generic_deleteVertex hn hz hb hc) hSD q k).1
    · intro b
      refine ⟨fun a => sub_ne_zero.mp (geoSmoothingSegment_displacement_ne_zero (flat_hn1 hn) _ _ a),
        fun q k => ?_⟩
      exact (generic_geoCornerPolygon_props (flat_hn1 hn) (g.sideTuple b t).property (hST b) q k).1
  no_antiparallel := by
    refine ⟨flat_centre_not_antiparallel hn g j hz hb hc S hspec, ?_, ?_⟩
    · intro q k
      exact (generic_geoCornerPolygon_props hn (generic_deleteVertex hn hz hb hc) hSD q k).2.1
    · intro b q k
      exact (generic_geoCornerPolygon_props (flat_hn1 hn) (g.sideTuple b t).property (hST b) q k).2.1
  turns_nonzero := by
    refine ⟨flat_centre_turn_zero_iff hn g j hz hb hc S hspec, ?_, ?_⟩
    · intro q k
      exact (generic_geoCornerPolygon_props hn (generic_deleteVertex hn hz hb hc) hSD q k).2.2.1
    · intro b q k
      exact (generic_geoCornerPolygon_props (flat_hn1 hn) (g.sideTuple b t).property (hST b) q k).2.2.1
  same_turn_signs := flat_same_turn_signs hn g j hz hb hc t hs S hsf hST hSD
  centre_turn_signs := flat_centre_turn_signs hn g j hz hb hc S hspec hSD
  extra_corner := flat_extra_corner hn g j t hs S hST
  mu_j_between := (flat_centre_mu_j_between hn g j hz hb hc S).1
  mu_j_fused_multiples := (flat_centre_mu_j_between hn g j hz hb hc S).2

end U3Bundle

end SM
