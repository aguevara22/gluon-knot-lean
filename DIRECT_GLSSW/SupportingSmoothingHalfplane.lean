import DirectGLSSW.HOMFLY.HOMFYSmoothingDiagram
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.SupportingGeometry

/-- Closed affine segments preserve the concrete oriented half-plane. -/
theorem affinePoint_halfplane (p u a b : PlanarPoint ℝ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : 0 ≤ planarDet u (a-p)) (hb : 0 ≤ planarDet u (b-p)) :
    0 ≤ planarDet u (DirectGLSSW.affinePoint a b t-p) := by
  have he : planarDet u (DirectGLSSW.affinePoint a b t-p) =
      (1-t)*planarDet u (a-p) + t*planarDet u (b-p) := by
    simp only [planarDet, DirectGLSSW.affinePoint, Prod.fst_sub, Prod.snd_sub]
    ring
  rw [he]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) ha) (mul_nonneg ht0 hb)

/-- Every vertex of the actual corrected smoothing stays in the old half-plane. -/
theorem smoothCrossing_vertices_halfplane (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (p u : PlanarPoint ℝ)
    (hhalf : ∀ v, 0 ≤ planarDet u (D.vertexPoint v-p)) :
    ∀ v, 0 ≤ planarDet u ((smoothCrossing D c).vertexPoint v-p) := by
  intro v
  change 0 ≤ planarDet u (smoothVertexPoint D c v-p)
  unfold smoothVertexPoint
  rcases smoothVertexPointGeometryCode_cutpoint_or_old D c
      ((smoothVertexEquiv D c).symm v) with ⟨k, hk⟩ | ⟨w, hw, hwc⟩
  · rw [hk]
    have hεr : smoothEpsilon D c < crossingCutoffRadius D c :=
      lt_of_lt_of_le (smoothEpsilon_lt_radius D c) (smoothRadius_le_cutoff D c)
    obtain ⟨t, ht0, ht1, he⟩ := smoothCutLabel_interior D c
      (smoothEpsilon D c) (smoothEpsilon_pos D c) hεr k
    rw [he]
    exact affinePoint_halfplane p u _ _ t ht0.le ht1.le (hhalf _) (hhalf _)
  · rw [hw]
    simpa only [smoothVertexPointGeometryCode, if_neg hwc] using hhalf w

end DirectGLSSW.HOMFLY.SupportingGeometry


