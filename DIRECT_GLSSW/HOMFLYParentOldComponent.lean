import HOMFLYParentConnectorPosition
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- Actual continuing-component membership reflects to the original cut component. -/
theorem parentRoot_old_component (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (x : Fin D.nArc)
    (hx : componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl x)) =
      componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c)))) :
    componentOf D.continuation x =
      componentOf D.continuation (D.incoming c (firstVisitedBranch T c)) := by
  have hc : componentOf (rootCutContinuation D c (firstVisitedBranch T c)) x =
      componentOf (rootCutContinuation D c (firstVisitedBranch T c))
        (D.incoming c (firstVisitedBranch T c)) := by
    apply (smoothRootCutComponentEquiv D c (firstVisitedBranch T c)).injective
    rw [smoothRootCutComponentEquiv_old, smoothRootCutComponentEquiv_connector]
    exact hx
  exact (componentOf_eq_iff _ _ _).2
    (sameCycle_mul_swap_refines D.continuation
      (rootCut_sameCycle D c hself (firstVisitedBranch T c))
      ((componentOf_eq_iff _ _ _).1 hc))

/-- Retained incoming ports are literal old-arc images. -/
theorem parentRoot_retained_incoming (D : PLLinkDiagram) (c d : Fin D.nCrossing)
    (hd : d ≠ c) (i : Fin 2) :
    (smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨d,hd⟩) i =
      smoothArcEquiv D (Sum.inl (D.incoming d i)) := by
  change smoothArcEquiv D (Sum.inl (D.incoming
    (((smoothCrossingEquiv D c).symm (smoothCrossingEquiv D c ⟨d,hd⟩)).val) i)) = _
  rw [Equiv.symm_apply_apply]

end DirectGLSSW.HOMFLY
