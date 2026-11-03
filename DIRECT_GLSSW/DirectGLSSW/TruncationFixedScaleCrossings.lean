import DirectGLSSW.TruncationAmplitudeCrossings
import DirectGLSSW.TruncationFixedScale

namespace DirectGLSSW.TruncationFixedScaleCrossings
open DirectGLSSW.TruncationDirection
open DirectGLSSW.TruncationEdgeLift

theorem exists_fixedScale_leftCorner_truncation_amplitude_crossings
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hturn : 0 < planarDet (q a - q p) (q (cyclicSuccessor a) - q a))
    (scale : ℝ) (hscale : 0 < scale)
    (havoid : ∀ x : Fin n, x ≠ a →
      planarDet
        (scale • (q (cyclicSuccessor a) - q a) - (q p - q a))
        (q x - q a) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ε < 1 ∧ ε * scale < 1 ∧
          ∃ ht : CyclicGeneric (truncateCyclicCorner q a p scale ε),
            polygonAmplitude (truncateCyclicCorner q a p scale ε) ht =
              -polygonAmplitude q hq ∧
              ∃ E : PolygonCrossing q ≃
                PolygonCrossing (truncateCyclicCorner q a p scale ε),
                (∀ c : PolygonCrossing q,
                  (E c).val = (edgeLift a c.val.1, edgeLift a c.val.2)) ∧
                (∀ c : PolygonCrossing q,
                  crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
                    crossingPoint q c) := by
  obtain ⟨δA, hδA, hA⟩ :=
    TruncationFixedScale.exists_fixedScale_leftCorner_truncation_amplitude
      hRI q hq a p hp hturn scale hscale havoid
  obtain ⟨ρ, hρ, hclear, hfree⟩ :=
    exists_combined_vertex_clearance_radius hq.size_ge_three q hq.g1 a
  obtain ⟨δB, hδB, hB⟩ := exists_shortening_points_small_radius
    (q a) (q p) (q (cyclicSuccessor a)) scale ρ hscale hρ
  refine ⟨min δA δB, lt_min hδA hδB, ?_⟩
  intro ε hε hεδ
  have hεδA : ε < δA := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεδB : ε < δB := lt_of_lt_of_le hεδ (min_le_right _ _)
  obtain ⟨hε1, hεscale1, ht, hamp⟩ := hA ε hε hεδA
  obtain ⟨_, _, hinB, hinC⟩ := hB ε hε hεδB
  have hεscale : 0 < ε * scale := mul_pos hε hscale
  let E := polygonCrossing_truncationEquiv hq.size_ge_three q a p hp scale ε ρ
    hε hε1 hεscale hεscale1 ht.g1 hclear hfree hinB hinC
  have hleft (c : PolygonCrossing q) : (E c).val.1 = edgeLift a c.val.1 :=
    polygonCrossing_truncationEquiv_left_label hq.size_ge_three q a p hp scale ε ρ
      hε hε1 hεscale hεscale1 ht.g1 hclear hfree hinB hinC c
  have hright (c : PolygonCrossing q) : (E c).val.2 = edgeLift a c.val.2 :=
    polygonCrossing_truncationEquiv_right_label hq.size_ge_three q a p hp scale ε ρ
      hε hε1 hεscale hεscale1 ht.g1 hclear hfree hinB hinC c
  refine ⟨hε1, hεscale1, ht, hamp, E, ?_, ?_⟩
  · intro c
    exact Prod.ext (hleft c) (hright c)
  · intro c
    have hout : ρ ≤ dist (crossingPoint q c) (q a) := by
      apply le_of_not_gt
      intro hin
      exact hfree _ hin (isCrossingPoint_crossingPoint q c)
    have hl : edgeInterior (truncateCyclicCorner q a p scale ε)
        (E c).val.1 (crossingPoint q c) := by
      rw [hleft c]
      exact edgeInterior_transfer_from_old_outside_vertex_ball
        (by have := hq.size_ge_three; omega)
        q a p c.val.1 hp scale ε ρ hε hε1 hεscale hεscale1 hinB hinC
        (crossingPoint q c) hout (crossingPoint_mem_left q c)
    have hr : edgeInterior (truncateCyclicCorner q a p scale ε)
        (E c).val.2 (crossingPoint q c) := by
      rw [hright c]
      exact edgeInterior_transfer_from_old_outside_vertex_ball
        (by have := hq.size_ge_three; omega)
        q a p c.val.2 hp scale ε ρ hε hε1 hεscale hεscale1 hinB hinC
        (crossingPoint q c) hout (crossingPoint_mem_right q c)
    exact (crossingPoint_eq_of_mem ht.size_ge_three
      (truncateCyclicCorner q a p scale ε) ht.g1 (E c) (crossingPoint q c) hl hr).symm

end DirectGLSSW.TruncationFixedScaleCrossings
