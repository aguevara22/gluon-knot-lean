import OpenCurrentTurnAlgebra
import OpenFirstEdgeCurrentTail

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.OpenCurrentTurnProjector
open OpenFirstEdgeGeometry ShortEdgeSignStability

/-- The source short-first b and M identities on the actual geometric approach,
with one radius for every suffix and with nonzero determinants throughout. -/
theorem exists_short_first_currents (q : ℕ → PlanarPoint ℝ) (N : ℕ)
    (hcore : CoreHGeneric q N) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1 ∧ ∀ ε : ℝ, 0<ε → ε<δ →
      CoreHGeneric (approach q ε) N ∧
      ∀ j : ℕ, 1<j → j≤N →
        ordinaryCurrent (fun _ _ _ => -1) (polygonSignArray (approach q ε)) 0 j=
          ((1+polygonSignArray q 0 1 2)/2) *
            ordinaryCurrent (fun _ _ _ => -1) (polygonSignArray q) 1 j ∧
        OpenMarkedCurrent.entry (polygonSignArray (approach q ε)) 0 j=
          (((1+polygonSignArray q 0 1 2)/2)-1) *
            OpenMarkedCurrent.entry (polygonSignArray q) 1 j := by
  obtain ⟨δf,hδf,hδf1,hfar⟩ := exists_uniform_far_signs q N hcore
  obtain ⟨δg,hδg,hδg1,hgen⟩ := exists_approach_coreHGeneric q N hcore
  refine ⟨min δf δg,lt_min hδf hδg,(min_le_left _ _).trans hδf1,?_⟩
  intro ε hε hεδ
  have hεf : ε<δf := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεg : ε<δg := lt_of_lt_of_le hεδ (min_le_right _ _)
  refine ⟨hgen ε hε hεg,?_⟩
  intro j hj hjN
  have hf : ∀ k t, 0+1<k → k<t → t≤N →
      polygonSignArray (approach q ε) 0 k t=polygonSignArray (approach q ε) (0+1) k t := by
    intro k t hk hkt htN
    exact (hfar ε hε hεf k t hk hkt htN).1
  have hb := OpenCurrentShortFirst.ordinaryCurrent_short_first
    (polygonSignArray (approach q ε)) 0 N hf j hj hjN
  have hM := OpenCurrentShortFirst.entry_short_first
    (polygonSignArray (approach q ε)) 0 N hf j hj hjN
  norm_num only [Nat.zero_add] at hb hM
  rw [polygonSignArray_turn q hε,ordinaryCurrent_tail q ε _ (by omega) hj] at hb
  rw [polygonSignArray_turn q hε,openMarkedCurrent_tail q ε (by omega) hj] at hM
  exact ⟨hb,hM⟩

/-- Cartesian left/right normalization, with no sign-stability assumption
remaining in the theorem. The first point approaches on the actual incoming edge. -/
theorem exists_cartesian_turn_projector (q : ℕ → PlanarPoint ℝ) (N : ℕ)
    (hcore : CoreHGeneric q N) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1 ∧ ∀ ε : ℝ, 0<ε → ε<δ →
      CoreHGeneric (approach q ε) N ∧
      ∀ j : ℕ, 1<j → j≤N →
        (0<planarDet (polygonChord q 0 1) (polygonChord q 1 2) →
          OpenMarkedCurrent.entry (polygonSignArray (approach q ε)) 0 j=
            -OpenMarkedCurrent.entry (polygonSignArray q) 1 j) ∧
        (planarDet (polygonChord q 0 1) (polygonChord q 1 2)<0 →
          OpenMarkedCurrent.entry (polygonSignArray (approach q ε)) 0 j=0) := by
  obtain ⟨δ,hδ,hδ1,hgood⟩ := exists_short_first_currents q N hcore
  refine ⟨δ,hδ,hδ1,?_⟩
  intro ε hε hεδ
  have hg := hgood ε hε hεδ
  refine ⟨hg.1,?_⟩
  intro j hj hjN
  have hM := (hg.2 j hj hjN).2
  constructor
  · intro hleft
    have hneg : polygonHDet q 0 1 2<0 := by
      rw [polygonHDet_eq_neg_turn]
      exact neg_neg_of_pos hleft
    have hsign : polygonSignArray q 0 1 2=-1 := by
      simp [polygonSignArray,scalarSignValue,ne_of_lt hneg,hneg]
    rw [hsign] at hM
    norm_num at hM
    exact hM
  · intro hright
    have hpos : 0<polygonHDet q 0 1 2 := by
      rw [polygonHDet_eq_neg_turn]
      exact neg_pos.mpr hright
    have hsign : polygonSignArray q 0 1 2=1 := by
      simp [polygonSignArray,scalarSignValue,ne_of_gt hpos,not_lt_of_ge hpos.le]
    rw [hsign] at hM
    norm_num at hM
    exact hM

/-- The separate one-edge case is the unit current, including its unary term. -/
theorem one_edge_currents (q : ℕ → PlanarPoint ℝ) :
    ordinaryCurrent (fun _ _ _ => -1) (polygonSignArray q) 0 1=1 ∧
      OpenMarkedCurrent.entry (polygonSignArray q) 0 1=1 := by
  exact ⟨ordinaryCurrent_adjacent _ _ 0,OpenMarkedCurrent.entry_adjacent_eq_one _ 0⟩

end DirectGLSSW.OpenCurrentTurnProjector
#check @DirectGLSSW.OpenCurrentTurnProjector.exists_short_first_currents
#check @DirectGLSSW.OpenCurrentTurnProjector.exists_cartesian_turn_projector
#check @DirectGLSSW.OpenCurrentTurnProjector.one_edge_currents



