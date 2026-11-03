import ActualSpatialTrace

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY HOMFLY.PrincipalTurning

theorem splitMain_first_cell (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : unitInterval) (ht : ((componentArcLength D e:ℝ)+1)*t.val ≤ 1) :
    splitMainPlanar D e t = affinePoint (D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcTarget e)) (3/4+((componentArcLength D e:ℝ)+1)*t.val/4) := by
  rw [splitMainPlanar_apply, splitTraversalTime_first _ (componentArcLength_pos D e) _ ht]
  have hlo : 0 ≤ ((componentArcLength D e:ℝ)+1)*t.val :=
    mul_nonneg (by positivity) t.property.1
  simpa using uniformPLCurve_arc_cell D e 0
    (3/4+((componentArcLength D e:ℝ)+1)*t.val/4) (by constructor <;> linarith)

theorem splitMain_last_cell (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : unitInterval) (ht : (componentArcLength D e:ℝ) ≤
      ((componentArcLength D e:ℝ)+1)*t.val) :
    splitMainPlanar D e t = affinePoint (D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcTarget e))
        ((((componentArcLength D e:ℝ)+1)*t.val-componentArcLength D e)/4) := by
  rw [splitMainPlanar_apply, splitTraversalTime_last _ (componentArcLength_pos D e) _ ht,
    add_comm, uniformPLCurve_periodic]
  have hhi : ((componentArcLength D e:ℝ)+1)*t.val ≤ (componentArcLength D e:ℝ)+1 := by
    nlinarith [t.property.2]
  simpa using uniformPLCurve_arc_cell D e 0
    ((((componentArcLength D e:ℝ)+1)*t.val-componentArcLength D e)/4)
    (by constructor <;> linarith)

theorem split_difference_first (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : unitInterval) (ht : ((componentArcLength D e:ℝ)+1)*t.val ≤ 1) :
    splitMainComplex D e t - splitBeta D e t =
      (t.val * (((componentArcLength D e:ℝ)+1)/4+1/2) : ℝ) • arcVector D e := by
  rw [splitMainComplex_apply, splitMain_first_cell D e t ht, splitBeta_apply]
  apply Complex.ext <;>
    simp [splitBaseA, splitBaseB, affinePoint, Complex.equivRealProd_symm_apply, arcVector] <;> ring

theorem split_difference_last (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : unitInterval) (ht : (componentArcLength D e:ℝ) ≤
      ((componentArcLength D e:ℝ)+1)*t.val) :
    splitMainComplex D e t - splitBeta D e t =
      (-(1-t.val) * (((componentArcLength D e:ℝ)+1)/4+1/2) : ℝ) • arcVector D e := by
  rw [splitMainComplex_apply, splitMain_last_cell D e t ht, splitBeta_apply]
  apply Complex.ext <;>
    simp [splitBaseA, splitBaseB, affinePoint, Complex.equivRealProd_symm_apply, arcVector] <;> ring

end DirectGLSSW.DescendingSpatial




