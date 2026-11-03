import HOMFLYParentRootRetention

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : DecidableEq (diagramComponent D) := Classical.decEq _

/-- The old root, as an actual smoothed old arc, belongs to label false. -/
theorem firstVisited_original_root_component (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) :
    componentOf (smoothCrossing D c).continuation
      (smoothArcEquiv D (Sum.inl
        (T.baseArc (componentOf D.continuation
          (D.incoming c (firstVisitedBranch T c)))).val)) =
      rootSelfCutComponents D c hself (firstVisitedBranch T c) (Sum.inl false) := by
  have h := firstVisited_root_sameCycle_cut D T c hself
  dsimp only at h
  have hc := congrArg (smoothRootCutComponentEquiv D c (firstVisitedBranch T c))
    ((componentOf_eq_iff _ _ _).2 h)
  rw [smoothRootCutComponentEquiv_old, smoothRootCutComponentEquiv_connector] at hc
  exact hc.trans (rootSelfCutComponents_false D c hself (firstVisitedBranch T c)).symm

/-- Keep the old continuing root; only the detached component uses a connector root. -/
def parentRootSelfCutRoots (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing) :
    RootSelfCutLabels D c (firstVisitedBranch T c) → Fin (smoothCrossing D c).nArc
  | Sum.inl false => smoothArcEquiv D (Sum.inl
      (T.baseArc (componentOf D.continuation
        (D.incoming c (firstVisitedBranch T c)))).val)
  | Sum.inl true => smoothArcEquiv D (Sum.inr (otherBranch (firstVisitedBranch T c)))
  | Sum.inr C => smoothArcEquiv D (Sum.inl (T.baseArc C.val).val)

/-- Actual smoothing traversal with the original continuing root, the old
component order, and all unrelated component roots retained. -/
def parentRootSelfSmoothingTraversal (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) :
    BasedTraversal (smoothCrossing D c) :=
  basedTraversalOfComponentRoots (rootSelfCutComponents D c hself (firstVisitedBranch T c))
    (rootSelfCutOrder D T c hself (firstVisitedBranch T c)) (parentRootSelfCutRoots D T c) (by
      intro l
      cases l with
      | inl b =>
        cases b
        · exact firstVisited_original_root_component D T c hself
        · exact (rootSelfCutComponents_true D c hself (firstVisitedBranch T c)).symm
      | inr C => exact (rootSelfCutComponents_other D T c hself (firstVisitedBranch T c) C).symm)

@[simp] theorem parentRootSelfSmoothingTraversal_baseArc
    (D : PLLinkDiagram) (T : BasedTraversal D) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (l : RootSelfCutLabels D c (firstVisitedBranch T c)) :
    ((parentRootSelfSmoothingTraversal D T c hself).baseArc
      (rootSelfCutComponents D c hself (firstVisitedBranch T c) l)).val =
      parentRootSelfCutRoots D T c l := by
  apply basedTraversalOfComponentRoots_baseArc

@[simp] theorem parentRootSelfSmoothingTraversal_index
    (D : PLLinkDiagram) (T : BasedTraversal D) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (l : RootSelfCutLabels D c (firstVisitedBranch T c)) :
    (parentRootSelfSmoothingTraversal D T c hself).componentIndex
      (rootSelfCutComponents D c hself (firstVisitedBranch T c) l) =
      rootSelfCutOrder D T c hself (firstVisitedBranch T c) l := by
  apply basedTraversalOfComponentRoots_index

/-- The continuing component retains the old root as an old geometric arc. -/
theorem parentRootSelfSmoothingTraversal_continuing_root
    (D : PLLinkDiagram) (T : BasedTraversal D) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) :
    ((parentRootSelfSmoothingTraversal D T c hself).baseArc
      (componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))))).val =
      smoothArcEquiv D (Sum.inl
        (T.baseArc (componentOf D.continuation
          (D.incoming c (firstVisitedBranch T c)))).val) := by
  rw [← rootSelfCutComponents_false D c hself (firstVisitedBranch T c),
    parentRootSelfSmoothingTraversal_baseArc]
  rfl

/-- The detached component's connector root is unchanged. -/
theorem parentRootSelfSmoothingTraversal_detached_root
    (D : PLLinkDiagram) (T : BasedTraversal D) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) :
    ((parentRootSelfSmoothingTraversal D T c hself).baseArc
      (rootSelfCutComponents D c hself (firstVisitedBranch T c) (Sum.inl true))).val =
      ((rootSelfSmoothingTraversal D T c hself (firstVisitedBranch T c)).baseArc
        (rootSelfCutComponents D c hself (firstVisitedBranch T c) (Sum.inl true))).val := by
  rw [parentRootSelfSmoothingTraversal_baseArc, rootSelfSmoothingTraversal_baseArc]
  rfl

/-- Every unrelated component's original root is unchanged. -/
theorem parentRootSelfSmoothingTraversal_other_root
    (D : PLLinkDiagram) (T : BasedTraversal D) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (C : {C : diagramComponent D //
      C ≠ componentOf D.continuation (D.incoming c (firstVisitedBranch T c))}) :
    ((parentRootSelfSmoothingTraversal D T c hself).baseArc
      (rootSelfCutComponents D c hself (firstVisitedBranch T c) (Sum.inr C))).val =
      smoothArcEquiv D (Sum.inl (T.baseArc C.val).val) := by
  rw [parentRootSelfSmoothingTraversal_baseArc]
  rfl

/-- Component ordering is exactly that of the existing connector-root traversal. -/
theorem parentRootSelfSmoothingTraversal_componentIndex
    (D : PLLinkDiagram) (T : BasedTraversal D) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) :
    (parentRootSelfSmoothingTraversal D T c hself).componentIndex =
      (rootSelfSmoothingTraversal D T c hself (firstVisitedBranch T c)).componentIndex := rfl

end
end DirectGLSSW.HOMFLY
