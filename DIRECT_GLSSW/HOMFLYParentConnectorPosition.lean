import HOMFLYVisitPositionSuccessor
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- The actual new parent connector occurs immediately after the preserved first-cut visit. -/
theorem parentRoot_connector_visitPosition (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) :
    visitPosition (parentRootSelfSmoothingTraversal D T c hself)
      (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))) =
      visitPosition T (D.incoming c (firstVisitedBranch T c)) + 1 := by
  let i := firstVisitedBranch T c
  let a := D.incoming c i
  let E := smoothCrossing D c
  let U := parentRootSelfSmoothingTraversal D T c hself
  let old := smoothArcEquiv D (Sum.inl a)
  let tag := smoothArcEquiv D (Sum.inr i)
  have hstep : E.continuation old = tag := by
    rw [← smoothCode_actual_step,smoothCode_cut_step]
  have hcomp : componentOf E.continuation old = componentOf E.continuation tag := by
    rw [← hstep,componentOf_apply]
  have hroot : (U.baseArc (componentOf E.continuation old)).val =
      smoothArcEquiv D (Sum.inl (T.baseArc (componentOf D.continuation a)).val) := by
    rw [hcomp]
    exact parentRootSelfSmoothingTraversal_continuing_root D T c hself
  have hne : E.continuation old ≠ (U.baseArc (componentOf E.continuation old)).val := by
    rw [hstep,hroot]
    intro he
    have h := (smoothArcEquiv D).injective he
    cases h
  have hp := visitPosition_continuation_of_ne_root E U old hne
  rw [hstep] at hp
  have hold : visitPosition U old = visitPosition T a :=
    parentRoot_prefix_visitPosition D T c hself a rfl (le_refl _)
  exact hp.trans (congrArg (fun n:ℕ=>n+1) hold)

/-- Every inherited prefix arc precedes the new artificial-corner connector, in the actual parent. -/
theorem parentRoot_prefix_before_connector (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (x : Fin D.nArc)
    (hx : componentOf D.continuation x =
      componentOf D.continuation (D.incoming c (firstVisitedBranch T c)))
    (hle : visitPosition T x ≤ visitPosition T (D.incoming c (firstVisitedBranch T c))) :
    rankBefore
      (visitRank (parentRootSelfSmoothingTraversal D T c hself) (smoothArcEquiv D (Sum.inl x)))
      (visitRank (parentRootSelfSmoothingTraversal D T c hself)
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c)))) := by
  have hc := prefix_visit_continuing_component D T c hself x hx hle
  rw [rootSelfCutComponents_false] at hc
  unfold rankBefore visitRank
  refine Or.inr ⟨congrArg (parentRootSelfSmoothingTraversal D T c hself).componentIndex hc,?_⟩
  rw [parentRoot_prefix_visitPosition D T c hself x hx hle,parentRoot_connector_visitPosition]
  omega

end DirectGLSSW.HOMFLY
