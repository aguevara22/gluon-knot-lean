import ProcessedChildCrossingData
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable

/-- The stored original root survives each actual parent operation as an old arc. -/
theorem MarkedParentStep.arcOrigin_baseArc {s t : MarkedParentState}
    (step : MarkedParentStep s t) (d : Fin t.1.nCrossing) :
    step.arcOrigin (t.2.1.baseArc (componentOf t.1.continuation (t.1.incoming d 0))).val =
      some (s.2.1.baseArc (componentOf s.1.continuation
        (s.1.incoming (step.crossingOrigin d) 0))).val := by
  cases step with
  | switched S c hc hgood => rfl
  | @smoothed D T S c hc hgood R =>
    change smoothOldArcOrigin D (R.arcEquiv
      (((R.basedTraversal (parentRootSelfSmoothingTraversal D T c (S.connected _ _))).baseArc _).val)).val = _
    rw [R.basedTraversal_baseArc,R.parentRestriction_original_root]
    simp only [smoothOldArcOrigin,Equiv.symm_apply_apply]
    have he : componentOf D.continuation (D.incoming c (firstVisitedBranch T c)) =
        componentOf D.continuation (D.incoming ((MarkedParentStep.smoothed S c hc hgood R).crossingOrigin d) 0) :=
      (componentOf_eq_iff _ _ _).mpr (S.connected _ _)
    rw [he]

/-- Backward ancestry of the actual fixed root through the literal finite history. -/
theorem MarkedParentTrace.arcOrigin_baseArc {s t : MarkedParentState}
    (h : MarkedParentTrace s t) : ∀ d : Fin t.1.nCrossing,
    h.arcOrigin (t.2.1.baseArc (componentOf t.1.continuation (t.1.incoming d 0))).val =
      some (s.2.1.baseArc (componentOf s.1.continuation
        (s.1.incoming (h.crossingOrigin d) 0))).val := by
  induction h with
  | nil s => intro d; rfl
  | cons step tail ih =>
    intro d
    change (tail.arcOrigin _).bind step.arcOrigin = _
    rw [ih,Option.some_bind,step.arcOrigin_baseArc]
    rfl
end DirectGLSSW.HOMFLY
