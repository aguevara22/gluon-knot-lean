import OuterCellClassification

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

theorem basedUniformSecant_period_chord {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (s : ℝ) :
    basedUniformSecant T C s (componentArcLength D (T.baseArc C).val : ℝ) =
      -basedUniformSecant T C 0 s := by
  have hp := basedUniformPLCurve_periodic T C 0
  rw [zero_add] at hp
  apply Complex.equivRealProd.injective
  simp only [basedUniformSecant,Equiv.apply_symm_apply]
  rw [hp]
  apply Prod.ext <;> simp [Complex.equivRealProd_apply]

theorem rectangleSideIncrement_top_chord {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C)
    (hs : e.2=2) (hv : e.1.val.2.2=(componentArcLength D (T.baseArc C).val : ℝ)) :
    rectangleSideIncrement e = Complex.arg
      (basedUniformSecant T C 0 e.1.val.1.1 / basedUniformSecant T C 0 e.1.val.1.2) := by
  simp only [rectangleSideIncrement,rectangleSideStart,rectangleSideFinish,hs,
    show (2 : Fin 4) ≠ 0 by decide,show (2 : Fin 4) ≠ 1 by decide,
    ite_false,ite_true]
  rw [hv,basedUniformSecant_period_chord,basedUniformSecant_period_chord]
  simp only [neg_div,div_neg,neg_neg]

theorem rectangleSideIncrement_left_chord {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C)
    (hs : e.2=3) (ha : e.1.val.1.1=0) :
    rectangleSideIncrement e = Complex.arg
      (basedUniformSecant T C 0 e.1.val.2.1 / basedUniformSecant T C 0 e.1.val.2.2) := by
  simp only [rectangleSideIncrement,rectangleSideStart,rectangleSideFinish,hs,
    show (3 : Fin 4) ≠ 0 by decide,show (3 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 2 by decide,ite_false,ha]

end
end DirectGLSSW.HOMFLY.PrincipalTurning



