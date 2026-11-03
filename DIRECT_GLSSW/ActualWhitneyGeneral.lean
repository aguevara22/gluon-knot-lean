import ActualOuterAxisSums
import ExposedWhitney

set_option autoImplicit false
noncomputable section
open DirectGLSSW
attribute [local instance] Classical.propDecidable

namespace DirectGLSSW.HOMFLY.PLWinding

/-- The actual exterior boundary equals minus two-pi times the sum of
the two actual adjacent region winding indices, at any selected base
arc. No supporting half-plane premise is needed. -/
theorem actualOuterBoundary_eq_neg_side_indices {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    let pair := actualBaseSideIndexPair T C
    (∑ e ∈ (Finset.univ : Finset (PrincipalTurning.RetainedRectangleSide T C)).filter
      PrincipalTurning.rectangleExteriorSide,
      PrincipalTurning.rectangleSideIncrement e) =
        -(2*Real.pi) * (((pair.1 + pair.2 : ℤ) : ℝ)) := by
  intro pair
  have ht := actualOuterTop_arg_sum_eq_axisInterior T C
  have hl := actualOuterLeft_arg_sum_eq_axisInterior T C
  have ha := actualAxis_whole_eq_neg_nonBaseArgSum T C
  have hp := actual_side_index_sum_eq_nonBase_midpoint T C
  rw [PrincipalTurning.actualOuterBoundary_axis_regrouping,ht,hl,ha]
  linear_combination hp

/-- General actual-component Whitney formula in the source's first-visit
determinant convention. The adjacent indices come from independent
off-trace polygon winding, and the turning number is the actual tangent
degree of the same component. -/
theorem actualComponent_whitney_general {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    let pair := actualBaseSideIndexPair T C
    (PrincipalTurning.componentTurnInteger D C : ℝ) +
      (∑ c ∈ PrincipalTurning.actualComponentSelfCrossings T C,
        if 0 < PrincipalTurning.complexDet
          (PrincipalTurning.crossingVector D c (firstVisitedBranch T c))
          (PrincipalTurning.crossingVector D c
            (otherBranch (firstVisitedBranch T c)))
        then (1 : ℝ) else -1) =
      (((pair.1 + pair.2 : ℤ) : ℝ)) := by
  intro pair
  have hb := PrincipalTurning.actualComponent_secantBoundary_formula T C
  have ho := actualOuterBoundary_eq_neg_side_indices T C
  rw [ho, PrincipalTurning.actualComponent_orbit_turn_sum,
    PrincipalTurning.componentTotalTurn_eq_integer] at hb
  apply mul_left_cancel₀
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  linear_combination hb

end DirectGLSSW.HOMFLY.PLWinding
