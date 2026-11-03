import UniformPLGlobalZero

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open Equiv

theorem basedUniformSecant_base_corner {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (s t : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) (1/4))
    (ht : t ∈ Set.Icc ((componentArcLength D (T.baseArc C).val : ℝ)-1/4)
      (componentArcLength D (T.baseArc C).val)) :
    basedUniformSecant T C s t =
      ((t-(componentArcLength D (T.baseArc C).val : ℝ)-s : ℝ) : ℂ) * arcVector D (T.baseArc C).val := by
  let e := (T.baseArc C).val
  let m : ℝ := componentArcLength D e
  have hsarc : basedUniformPLCurve T C s =
      affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) (s+1/2) := by
    have hc := uniformPLCurve_arc_cell D e 0 (s+1/2) (by constructor <;> linarith [hs.1,hs.2])
    simpa only [basedUniformPLCurve,Int.cast_zero,zero_add,zpow_zero,Perm.one_apply] using hc
  have htarc : basedUniformPLCurve T C t =
      affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) (t-m+1/2) := by
    have hp := basedUniformPLCurve_periodic T C (t-m)
    change basedUniformPLCurve T C ((t-m)+m)=basedUniformPLCurve T C (t-m) at hp
    rw [sub_add_cancel] at hp
    rw [hp]
    have hc := uniformPLCurve_arc_cell D e 0 (t-m+1/2) (by constructor <;> linarith [ht.1,ht.2])
    simpa only [basedUniformPLCurve,Int.cast_zero,zero_add,zpow_zero,Perm.one_apply] using hc
  apply Complex.equivRealProd.injective
  simp only [basedUniformSecant,Equiv.apply_symm_apply]
  rw [hsarc,htarc]
  apply Prod.ext <;> simp [Complex.equivRealProd_apply,arcVector,affinePoint] <;> ring

theorem base_corner_coefficient_negative (m s t : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) (1/4)) (ht : t ∈ Set.Icc (m-1/4) m)
    (hnot : ¬(s=0 ∧ t=m)) : t-m-s < 0 := by
  classical
  by_contra hn
  apply hnot
  constructor <;> linarith [hs.1,ht.2]

/-- Every nonzero secant on the actual periodic base-corner cut has the
same negative root direction, hence any finite boundary refinement adds0. -/
theorem basedUniformSecant_base_corner_ratio_arg {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (s1 t1 s2 t2 : ℝ)
    (hs1 : s1 ∈ Set.Icc (0 : ℝ) (1/4))
    (ht1 : t1 ∈ Set.Icc ((componentArcLength D (T.baseArc C).val : ℝ)-1/4)
      (componentArcLength D (T.baseArc C).val))
    (hs2 : s2 ∈ Set.Icc (0 : ℝ) (1/4))
    (ht2 : t2 ∈ Set.Icc ((componentArcLength D (T.baseArc C).val : ℝ)-1/4)
      (componentArcLength D (T.baseArc C).val))
    (hn1 : ¬(s1=0 ∧ t1=(componentArcLength D (T.baseArc C).val : ℝ)))
    (hn2 : ¬(s2=0 ∧ t2=(componentArcLength D (T.baseArc C).val : ℝ))) :
    Complex.arg (basedUniformSecant T C s2 t2 / basedUniformSecant T C s1 t1)=0 := by
  let m : ℝ := componentArcLength D (T.baseArc C).val
  have hneg1 := base_corner_coefficient_negative m s1 t1 hs1 ht1 hn1
  have hneg2 := base_corner_coefficient_negative m s2 t2 hs2 ht2 hn2
  rw [basedUniformSecant_base_corner T C s2 t2 hs2 ht2,basedUniformSecant_base_corner T C s1 t1 hs1 ht1]
  have hv := arcVector_ne_zero D (T.baseArc C).val
  have hα1 : ((t1-m-s1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_lt hneg1)
  have hc : (((t2-m-s2 : ℝ) : ℂ)*arcVector D (T.baseArc C).val) /
      (((t1-m-s1 : ℝ) : ℂ)*arcVector D (T.baseArc C).val) =
      ((t2-m-s2 : ℝ) : ℂ)/((t1-m-s1 : ℝ) : ℂ) := by
    exact mul_div_mul_right _ _ hv
  rw [hc,← Complex.ofReal_div]
  exact Complex.arg_ofReal_of_nonneg (div_pos_of_neg_of_neg hneg2 hneg1).le

end DirectGLSSW.HOMFLY.PrincipalTurning



