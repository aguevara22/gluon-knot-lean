import ProcessedParentMarks
import HOMFLYRegularEndpointConsumers
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.ProcessedParentMarks
open PermutationOrbits LowestRowContract

/-- Every old regular marked endpoint is excluded from the next actual detached child. -/
theorem regular_mark_endpoints_not_detached {D : PLLinkDiagram} {T : BasedTraversal D}
    (S : ProcessedParentMarks D T) (c : Fin D.nCrossing) (hc : badAt T c)
    (x : {x : Fin D.nArc // x ∈ S.marks})
    (hs : ∀ d : Fin D.nCrossing, D.crossingVertex d ≠ D.arcSource x.val)
    (ht : ∀ d : Fin D.nCrossing, D.crossingVertex d ≠ D.arcTarget x.val) :
    (¬ ∃ a : ComponentArc (smoothCrossing D c)
        (rootSelfCutComponents D c (S.connected _ _) (firstVisitedBranch T c) (Sum.inl true)),
      (smoothCrossing D c).arcSource a.val =
        (smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inl x.val))) ∧
    (¬ ∃ a : ComponentArc (smoothCrossing D c)
        (rootSelfCutComponents D c (S.connected _ _) (firstVisitedBranch T c) (Sum.inl true)),
      (smoothCrossing D c).arcSource a.val =
        (smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inl x.val))) := by
  have hreg := smooth_old_arc_regular_endpoints D c x.val hs ht
  have hne := S.mark_not_detached c hc x
  exact ⟨regular_vertex_not_componentVertex _ _ _ hreg.1 _ (Or.inl rfl) hne,
    regular_vertex_not_componentVertex _ _ _ hreg.2 _ (Or.inr rfl) hne⟩

end DirectGLSSW.HOMFLY.ProcessedParentMarks
