import DirectGLSSW.HOMFLY.PLDiagrams

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.SupportingGeometry

private theorem det_offset_sub (u a b p : PlanarPoint ℝ) :
    planarDet u (a-b) = planarDet u (a-p) - planarDet u (b-p) := by
  simp only [planarDet, Prod.fst_sub, Prod.snd_sub]
  ring

private theorem det_right_smul (u a : PlanarPoint ℝ) (t : ℝ) :
    planarDet u (t • a) = t * planarDet u a := by
  simp only [planarDet, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

private theorem det_kernel_collinear (u v w : PlanarPoint ℝ) (hu : u ≠ 0)
    (hv : planarDet u v = 0) (hw : planarDet u w = 0) : planarDet v w = 0 := by
  by_cases hx : u.1 = 0
  · have hy : u.2 ≠ 0 := by
      intro hy
      exact hu (Prod.ext hx hy)
    have hvx : v.1 = 0 := by
      have h : u.2 * v.1 = 0 := by simpa [planarDet, hx] using hv
      exact (mul_eq_zero.mp h).resolve_left hy
    have hwx : w.1 = 0 := by
      have h : u.2 * w.1 = 0 := by simpa [planarDet, hx] using hw
      exact (mul_eq_zero.mp h).resolve_left hy
    simp [planarDet, hvx, hwx]
  · have h : u.1 * planarDet v w = 0 := by
      calc
        _ = v.1 * planarDet u w - w.1 * planarDet u v := by
          simp only [planarDet]
          ring
        _ = 0 := by rw [hv, hw]; ring
    exact (mul_eq_zero.mp h).resolve_left hx

/-- A transverse drawing crossing cannot lie on a line supporting all vertices. -/
theorem crossing_strictly_inside_halfplane (D : PLLinkDiagram)
    (p u : PlanarPoint ℝ) (hu : u ≠ 0)
    (hhalf : ∀ v, 0 ≤ planarDet u (D.vertexPoint v-p))
    (c : Fin D.nCrossing) :
    0 < planarDet u (D.vertexPoint (D.crossingVertex c)-p) := by
  by_contra hn
  have hz : planarDet u (D.vertexPoint (D.crossingVertex c)-p) = 0 :=
    le_antisymm (le_of_not_gt hn) (hhalf _)
  have hb (i : Fin 2) :
      planarDet u (D.vertexPoint (D.crossingVertex c) -
        D.vertexPoint (D.arcSource (D.incoming c i))) = 0 := by
    obtain ⟨t, ht, he⟩ := D.through_tangents_positive_collinear c i
    have hnonneg : 0 ≤ planarDet u
        (D.vertexPoint (D.crossingVertex c) -
          D.vertexPoint (D.arcSource (D.incoming c i))) := by
      rw [he, det_right_smul, det_offset_sub u _ _ p, hz, sub_zero]
      exact mul_nonneg ht.le (hhalf _)
    have hnonpos : planarDet u
        (D.vertexPoint (D.crossingVertex c) -
          D.vertexPoint (D.arcSource (D.incoming c i))) ≤ 0 := by
      rw [det_offset_sub u _ _ p, hz, zero_sub]
      exact neg_nonpos.mpr (hhalf _)
    exact le_antisymm hnonpos hnonneg
  apply D.crossing_transverse c
  exact det_kernel_collinear u _ _ hu (hb 0) (hb 1)

/-- Both endpoints of an arc on a supporting line avoid every crossing vertex. -/
theorem supporting_arc_endpoints_not_crossing (D : PLLinkDiagram)
    (p u : PlanarPoint ℝ) (hu : u ≠ 0)
    (hhalf : ∀ v, 0 ≤ planarDet u (D.vertexPoint v-p))
    (e : Fin D.nArc)
    (hs : planarDet u (D.vertexPoint (D.arcSource e)-p) = 0)
    (ht : planarDet u (D.vertexPoint (D.arcTarget e)-p) = 0)
    (c : Fin D.nCrossing) :
    D.arcSource e ≠ D.crossingVertex c ∧ D.arcTarget e ≠ D.crossingVertex c := by
  have hc := crossing_strictly_inside_halfplane D p u hu hhalf c
  constructor
  · intro he
    apply (ne_of_gt hc)
    simpa only [he] using hs
  · intro he
    apply (ne_of_gt hc)
    simpa only [he] using ht

/-- The actual directed supporting base arc has no incoming or outgoing crossing port. -/
theorem supporting_base_arc_nonincident (D : PLLinkDiagram) (e : Fin D.nArc)
    (hhalf : ∀ v, 0 ≤ planarDet
      (D.vertexPoint (D.arcTarget e)-D.vertexPoint (D.arcSource e))
      (D.vertexPoint v-D.vertexPoint (D.arcSource e)))
    (c : Fin D.nCrossing) (i : Fin 2) :
    e ≠ D.incoming c i ∧ e ≠ D.outgoing c i := by
  have hu : D.vertexPoint (D.arcTarget e)-D.vertexPoint (D.arcSource e) ≠ 0 := by
    intro he
    exact D.arc_endpoints_distinct e
      (D.vertexPoint_injective (sub_eq_zero.mp he).symm)
  have hs : planarDet
      (D.vertexPoint (D.arcTarget e)-D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcSource e)-D.vertexPoint (D.arcSource e)) = 0 := by
    simp [planarDet]
  have ht : planarDet
      (D.vertexPoint (D.arcTarget e)-D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcTarget e)-D.vertexPoint (D.arcSource e)) = 0 := by
    simp [planarDet, mul_comm]
  obtain ⟨hsrc,htgt⟩ := supporting_arc_endpoints_not_crossing D
    (D.vertexPoint (D.arcSource e))
    (D.vertexPoint (D.arcTarget e)-D.vertexPoint (D.arcSource e)) hu hhalf e hs ht c
  constructor
  · intro he
    apply htgt
    simpa only [he] using D.incoming_target c i
  · intro he
    apply hsrc
    simpa only [he] using D.outgoing_source c i

end DirectGLSSW.HOMFLY.SupportingGeometry



