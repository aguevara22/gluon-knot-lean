import ExposedOuterAngle
import ActualSecantBoundaryFormula
import ActualTangentLift

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The literal actual exterior boundary of an exposed component has turn -2π. -/
theorem actualOuterBoundary_exposed_sum {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (hhalf : actualRootVertexHalfplane T C) :
    (∑ e ∈ (Finset.univ : Finset (RetainedRectangleSide T C)).filter rectangleExteriorSide,
      rectangleSideIncrement e) = -2*Real.pi := by
  rw [actualOuterBoundary_axis_regrouping,actualOuterTop_exposed_sum T C hhalf,
    actualOuterLeft_exposed_sum T C hhalf]
  ring

/-- The exact turn sum in the secant boundary formula is the actual component turn. -/
theorem actualComponent_orbit_turn_sum {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    (∑ k : Fin (componentArcLength D (T.baseArc C).val),
      turn D ((D.continuation ^ (k.val : ℤ)) (T.baseArc C).val)) =
    componentTotalTurn D C := by
  have h := orbitTurningPrimitive_component_period D (T.baseArc C).val
  rw [orbitTurningPrimitive_nat,←Fin.sum_univ_eq_sum_range] at h
  simpa only [zpow_natCast,(T.baseArc C).property] using h

/-- Exposed-basepoint Whitney identity for the actual first-visit signs and
actual component tangent degree. The only premise is the concrete finite
vertex half-plane predicate at this traversal's own directed base arc. -/
theorem actualComponent_exposed_whitney {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (hhalf : actualRootVertexHalfplane T C) :
    (componentTurnInteger D C : ℝ) +
    (∑ c ∈ actualComponentSelfCrossings T C,
      if 0<complexDet (crossingVector D c (firstVisitedBranch T c))
        (crossingVector D c (otherBranch (firstVisitedBranch T c)))
      then (1 : ℝ) else -1) = 1 := by
  have h := actualComponent_secantBoundary_formula T C
  rw [actualOuterBoundary_exposed_sum T C hhalf,actualComponent_orbit_turn_sum,
    componentTotalTurn_eq_integer] at h
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ)≠0) Real.pi_ne_zero)
  nlinarith [h]

/-- The same Whitney identity is bound directly to the period increment of
the actual continuous lift of the actual rounded nonzero tangent. -/
theorem actualComponent_exposed_tangentLift_whitney {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D)
    (hhalf : actualRootVertexHalfplane T C) (δ : RoundingFraction) :
    actualTangentLift D (T.baseArc C).val δ
      (componentArcLength D (T.baseArc C).val : ℝ) -
    actualTangentLift D (T.baseArc C).val δ 0 +
    (2*Real.pi) * (∑ c ∈ actualComponentSelfCrossings T C,
      if 0<complexDet (crossingVector D c (firstVisitedBranch T c))
        (crossingVector D c (otherBranch (firstVisitedBranch T c)))
      then (1 : ℝ) else -1) = 2*Real.pi := by
  rw [actualTangentLift_period_increment,(T.baseArc C).property,componentTotalTurn_eq_integer]
  have h := actualComponent_exposed_whitney T C hhalf
  linear_combination (2*Real.pi)*h

end
end DirectGLSSW.HOMFLY.PrincipalTurning




