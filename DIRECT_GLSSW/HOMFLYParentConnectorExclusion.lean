import HOMFLYParentConnectorPosition
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- A tagged actual parent connector cannot enter a later detached child once the later cut
is proved to occur after that tag. Producing this order from a recursive history is separate. -/
theorem parentRoot_connector_not_later_detached (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (d : Fin (smoothCrossing D c).nCrossing)
    (hdself : (smoothCrossing D c).continuation.SameCycle
      ((smoothCrossing D c).incoming d 0) ((smoothCrossing D c).incoming d 1))
    (hafter : rankBefore
      (visitRank (parentRootSelfSmoothingTraversal D T c hself)
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))))
      (visitRank (parentRootSelfSmoothingTraversal D T c hself)
        ((smoothCrossing D c).incoming d
          (firstVisitedBranch (parentRootSelfSmoothingTraversal D T c hself) d)))) :
    componentOf (smoothCrossing (smoothCrossing D c) d).continuation
      (smoothArcEquiv (smoothCrossing D c)
        (Sum.inl (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))))) ≠
      rootSelfCutComponents (smoothCrossing D c) d hdself
        (firstVisitedBranch (parentRootSelfSmoothingTraversal D T c hself) d) (Sum.inl true) :=
  before_first_visit_not_detached (smoothCrossing D c)
    (parentRootSelfSmoothingTraversal D T c hself) d hdself _ hafter

/-- Every inherited prefix tag also stays outside that later actual child. -/
theorem parentRoot_prefix_not_later_detached (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (x : Fin D.nArc)
    (hx : componentOf D.continuation x =
      componentOf D.continuation (D.incoming c (firstVisitedBranch T c)))
    (hle : visitPosition T x ≤ visitPosition T (D.incoming c (firstVisitedBranch T c)))
    (d : Fin (smoothCrossing D c).nCrossing)
    (hdself : (smoothCrossing D c).continuation.SameCycle
      ((smoothCrossing D c).incoming d 0) ((smoothCrossing D c).incoming d 1))
    (hafter : rankBefore
      (visitRank (parentRootSelfSmoothingTraversal D T c hself)
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))))
      (visitRank (parentRootSelfSmoothingTraversal D T c hself)
        ((smoothCrossing D c).incoming d
          (firstVisitedBranch (parentRootSelfSmoothingTraversal D T c hself) d)))) :
    componentOf (smoothCrossing (smoothCrossing D c) d).continuation
      (smoothArcEquiv (smoothCrossing D c) (Sum.inl (smoothArcEquiv D (Sum.inl x)))) ≠
      rootSelfCutComponents (smoothCrossing D c) d hdself
        (firstVisitedBranch (parentRootSelfSmoothingTraversal D T c hself) d) (Sum.inl true) := by
  apply before_first_visit_not_detached (smoothCrossing D c)
    (parentRootSelfSmoothingTraversal D T c hself) d hdself
  have hb := parentRoot_prefix_before_connector D T c hself x hx hle
  unfold rankBefore at *
  rcases hb with hb | ⟨he,hb⟩ <;> rcases hafter with ha | ⟨hf,ha⟩ <;> omega

end DirectGLSSW.HOMFLY
