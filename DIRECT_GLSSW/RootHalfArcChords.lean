import OuterChordIncrements

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open Equiv

theorem basedUniformSecant_initial_half_arc {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/2)) :
    basedUniformSecant T C 0 t=(t : ℂ)*arcVector D (T.baseArc C).val := by
  let e := (T.baseArc C).val
  have h0 : basedUniformPLCurve T C 0 =
      affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) (1/2) := by
    have h := uniformPLCurve_arc_cell D e 0 (1/2) (by constructor <;> norm_num)
    simpa only [basedUniformPLCurve,Int.cast_zero,zero_add,zpow_zero,Perm.one_apply] using h
  have htt : basedUniformPLCurve T C t =
      affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) (t+1/2) := by
    have h := uniformPLCurve_arc_cell D e 0 (t+1/2) (by constructor <;> linarith [ht.1,ht.2])
    simpa only [basedUniformPLCurve,Int.cast_zero,zero_add,zpow_zero,Perm.one_apply] using h
  apply Complex.equivRealProd.injective
  simp only [basedUniformSecant,Equiv.apply_symm_apply]
  rw [h0,htt]
  apply Prod.ext <;> simp [Complex.equivRealProd_apply,arcVector,affinePoint] <;> ring

theorem basedUniformSecant_return_half_arc {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (t : ℝ)
    (ht : t ∈ Set.Icc ((componentArcLength D (T.baseArc C).val : ℝ)-1/2)
      (componentArcLength D (T.baseArc C).val : ℝ)) :
    basedUniformSecant T C 0 t=
      ((t-(componentArcLength D (T.baseArc C).val : ℝ) : ℝ) : ℂ)*arcVector D (T.baseArc C).val := by
  let e := (T.baseArc C).val
  let m : ℝ := componentArcLength D e
  have h0 : basedUniformPLCurve T C 0 =
      affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) (1/2) := by
    have h := uniformPLCurve_arc_cell D e 0 (1/2) (by constructor <;> norm_num)
    simpa only [basedUniformPLCurve,Int.cast_zero,zero_add,zpow_zero,Perm.one_apply] using h
  have htt : basedUniformPLCurve T C t =
      affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) (t-m+1/2) := by
    have hp := basedUniformPLCurve_periodic T C (t-m)
    change basedUniformPLCurve T C ((t-m)+m)=basedUniformPLCurve T C (t-m) at hp
    rw [sub_add_cancel] at hp
    rw [hp]
    have h := uniformPLCurve_arc_cell D e 0 (t-m+1/2) (by constructor <;> linarith [ht.1,ht.2])
    simpa only [basedUniformPLCurve,Int.cast_zero,zero_add,zpow_zero,Perm.one_apply] using h
  apply Complex.equivRealProd.injective
  simp only [basedUniformSecant,Equiv.apply_symm_apply]
  rw [h0,htt]
  apply Prod.ext <;> simp [Complex.equivRealProd_apply,arcVector,affinePoint] <;> ring

theorem basedUniformSecant_initial_relative_arg {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/2)) :
    Complex.arg (basedUniformSecant T C 0 t/arcVector D (T.baseArc C).val)=0 := by
  rw [basedUniformSecant_initial_half_arc T C t ht]
  have hv := arcVector_ne_zero D (T.baseArc C).val
  have hdiv : ((t : ℂ)*arcVector D (T.baseArc C).val)/arcVector D (T.baseArc C).val=(t : ℂ) := by
    simpa only [one_mul,div_one] using mul_div_mul_right (t : ℂ) (1 : ℂ) hv
  rw [hdiv]
  exact Complex.arg_ofReal_of_nonneg ht.1

theorem basedUniformSecant_return_relative_arg {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (t : ℝ)
    (ht : t ∈ Set.Ico ((componentArcLength D (T.baseArc C).val : ℝ)-1/2)
      (componentArcLength D (T.baseArc C).val : ℝ)) :
    Complex.arg (basedUniformSecant T C 0 t/arcVector D (T.baseArc C).val)=Real.pi := by
  rw [basedUniformSecant_return_half_arc T C t ⟨ht.1,ht.2.le⟩]
  have hv := arcVector_ne_zero D (T.baseArc C).val
  have hdiv : ((((t-(componentArcLength D (T.baseArc C).val : ℝ) : ℝ) : ℂ)*
      arcVector D (T.baseArc C).val)/arcVector D (T.baseArc C).val)=
      ((t-(componentArcLength D (T.baseArc C).val : ℝ) : ℝ) : ℂ) := by
    simpa only [one_mul,div_one] using
      mul_div_mul_right ((t-(componentArcLength D (T.baseArc C).val : ℝ) : ℝ) : ℂ) (1 : ℂ) hv
  rw [hdiv]
  exact Complex.arg_ofReal_of_neg (by linarith [ht.2])

end DirectGLSSW.HOMFLY.PrincipalTurning




