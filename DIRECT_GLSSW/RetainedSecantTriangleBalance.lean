import RetainedSecantTriangles

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

theorem origin_triangle_of_segment (a b c : ℂ) (hz : (0 : ℂ) ∈ segment ℝ a b) :
    (0 : PlanarPoint ℝ) ∈ convexHull ℝ
      {Complex.equivRealProd a,Complex.equivRealProd b,Complex.equivRealProd c} := by
  obtain ⟨α,β,hα,hβ,hs,hp⟩ := hz
  have hpoint : α • Complex.equivRealProd a + β • Complex.equivRealProd b +
      (0 : ℝ) • Complex.equivRealProd c = 0 := by
    simpa [Complex.equivRealProd_apply,Complex.add_re,Complex.add_im,
      Complex.smul_re,Complex.smul_im,Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul]
      using congrArg Complex.equivRealProd hp
  have hc := triangle_mem_of_barycentric (Complex.equivRealProd a) (Complex.equivRealProd b)
    (Complex.equivRealProd c) α β 0 hα hβ (le_refl _) (by linarith)
  rw [hpoint] at hc
  exact hc

theorem triangle_angle_zero_of_origin_outside (a b c : ℂ)
    (hh : (0 : PlanarPoint ℝ) ∉ convexHull ℝ
      {Complex.equivRealProd a,Complex.equivRealProd b,Complex.equivRealProd c}) :
    Complex.arg (b/a)+Complex.arg (c/b)+Complex.arg (a/c)=0 := by
  have hab : (0 : ℂ) ∉ segment ℝ a b := fun h => hh (origin_triangle_of_segment a b c h)
  have hbc : (0 : ℂ) ∉ segment ℝ b c := by
    intro h
    apply hh
    have h' := origin_triangle_of_segment b c a h
    have he : ({Complex.equivRealProd b,Complex.equivRealProd c,Complex.equivRealProd a} :
        Set (PlanarPoint ℝ)) = {Complex.equivRealProd a,Complex.equivRealProd b,Complex.equivRealProd c} := by
      ext x
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    rwa [he] at h'
  have hca : (0 : ℂ) ∉ segment ℝ c a := by
    intro h
    apply hh
    have h' := origin_triangle_of_segment c a b h
    have he : ({Complex.equivRealProd c,Complex.equivRealProd a,Complex.equivRealProd b} :
        Set (PlanarPoint ℝ)) = {Complex.equivRealProd a,Complex.equivRealProd b,Complex.equivRealProd c} := by
      ext x
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    rwa [he] at h'
  rw [triangle_origin_angle_balance a b c hab hbc hca,if_neg hh]

/-- Literal oriented triangle sum for any three actual parameter vertices
of a retained mesh rectangle. Degenerate image triangles are included. -/
theorem retainedSecantTriangle_angle_zero {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b u v s1 s2 s3 t1 t2 t3 : ℝ)
    (hr : ((a,b),(u,v)) ∈ secantRetainedRectangles T C)
    (hs1 : s1 ∈ Set.Icc a b) (hs2 : s2 ∈ Set.Icc a b) (hs3 : s3 ∈ Set.Icc a b)
    (ht1 : t1 ∈ Set.Icc u v) (ht2 : t2 ∈ Set.Icc u v) (ht3 : t3 ∈ Set.Icc u v) :
    Complex.arg (basedUniformSecant T C s2 t2 / basedUniformSecant T C s1 t1)+
      Complex.arg (basedUniformSecant T C s3 t3 / basedUniformSecant T C s2 t2)+
      Complex.arg (basedUniformSecant T C s1 t1 / basedUniformSecant T C s3 t3)=0 := by
  exact triangle_angle_zero_of_origin_outside _ _ _
    (retainedSecantTriangle_origin_excluded T C a b u v s1 s2 s3 t1 t2 t3 hr hs1 hs2 hs3 ht1 ht2 ht3)

end DirectGLSSW.HOMFLY.PrincipalTurning



