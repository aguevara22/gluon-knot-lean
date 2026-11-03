import ActualAxisPartition

set_option autoImplicit false
noncomputable section
open DirectGLSSW
attribute [local instance] Classical.propDecidable

namespace DirectGLSSW.HOMFLY.PLWinding

/-- The initial quarter-to-original-knot axis fragment contributes no
exterior principal-angle increment. -/
theorem actualAxis_initial_base_fragment_zero {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    (∑ ab ∈ (PrincipalTurning.secantAxisCells T C).filter
      (fun ab => (1/4 : ℝ) ≤ ab.1 ∧ ab.2 ≤ 1/2),
      Complex.arg (PrincipalTurning.basedUniformSecant T C 0 ab.1 /
        PrincipalTurning.basedUniformSecant T C 0 ab.2)) = 0 := by
  apply Finset.sum_eq_zero
  intro ab hab
  have hb := (Finset.mem_filter.mp hab).2
  have hc : PrincipalTurning.secantAxisAdjacent T C ab.1 ab.2 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hab).1).2
  exact initial_base_secant_cell_arg_zero T C ab.1 ab.2
    (by linarith [hb.1]) hc.2.2.1.le hb.2

/-- The final original-knot-to-quarter axis fragment likewise
contributes no exterior principal-angle increment. -/
theorem actualAxis_return_base_fragment_zero {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    let m : ℝ := componentArcLength D (T.baseArc C).val
    (∑ ab ∈ (PrincipalTurning.secantAxisCells T C).filter
      (fun ab => m - 1/2 ≤ ab.1 ∧ ab.2 ≤ m - 1/4),
      Complex.arg (PrincipalTurning.basedUniformSecant T C 0 ab.1 /
        PrincipalTurning.basedUniformSecant T C 0 ab.2)) = 0 := by
  intro m
  apply Finset.sum_eq_zero
  intro ab hab
  have hb := (Finset.mem_filter.mp hab).2
  have hc : PrincipalTurning.secantAxisAdjacent T C ab.1 ab.2 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hab).1).2
  exact return_base_secant_cell_arg_zero T C ab.1 ab.2
    hb.1 hc.2.2.1.le (by dsimp [m] at *; linarith [hb.2])

end DirectGLSSW.HOMFLY.PLWinding
