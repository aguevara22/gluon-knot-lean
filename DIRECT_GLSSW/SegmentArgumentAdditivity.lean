import RetainedSecantTriangleBalance
import EdgeCancellation

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Exact conversion of a literal complex segment to its real-coordinate segment. -/
theorem equivRealProd_mem_segment_of_mem {a b c : ℂ}
    (hb : b ∈ segment ℝ a c) :
    Complex.equivRealProd b ∈ segment ℝ
      (Complex.equivRealProd a) (Complex.equivRealProd c) := by
  obtain ⟨u,v,hu,hv,hs,hp⟩ := hb
  refine ⟨u,v,hu,hv,hs,?_⟩
  simpa [Complex.equivRealProd_apply, Complex.smul_re, Complex.smul_im,
    Complex.add_re, Complex.add_im, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    using congrArg Complex.equivRealProd hp

/-- Subdividing a zero-free affine chord preserves its principal-argument
increment. No common supporting half-plane of the whole polygon is assumed. -/
theorem segment_arg_additive (a b c : ℂ)
    (hb : b ∈ segment ℝ a c) (havoid : (0 : ℂ) ∉ segment ℝ a c) :
    Complex.arg (c/a) = Complex.arg (b/a) + Complex.arg (c/b) := by
  have hbP := equivRealProd_mem_segment_of_mem hb
  have hvertices :
      ({Complex.equivRealProd a, Complex.equivRealProd b,
        Complex.equivRealProd c} : Set (PlanarPoint ℝ)) ⊆
      segment ℝ (Complex.equivRealProd a) (Complex.equivRealProd c) := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact left_mem_segment ℝ _ _
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hbP
    have hx' := Set.mem_singleton_iff.mp hx
    subst x
    exact right_mem_segment ℝ _ _
  have hout : (0 : PlanarPoint ℝ) ∉ convexHull ℝ
      {Complex.equivRealProd a, Complex.equivRealProd b,
        Complex.equivRealProd c} := by
    intro hz
    have hseg := convexHull_min hvertices (convex_segment _ _) hz
    obtain ⟨u,v,hu,hv,hs,hp⟩ := hseg
    apply havoid
    refine ⟨u,v,hu,hv,hs,?_⟩
    apply Complex.equivRealProd.injective
    simpa [Complex.equivRealProd_apply, Complex.smul_re, Complex.smul_im,
      Complex.add_re, Complex.add_im, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
      using hp
  have htriangle := triangle_angle_zero_of_origin_outside a b c hout
  rw [segment_arg_reverse a c havoid] at htriangle
  linarith

end DirectGLSSW.HOMFLY.PrincipalTurning

