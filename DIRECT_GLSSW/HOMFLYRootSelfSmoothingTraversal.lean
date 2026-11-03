import SplitComponentLabelsDirect
import SplitSumOrder
import HOMFLYSmoothingVisitTransport
import HOMFLYTraversalFromRoots

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : DecidableEq (diagramComponent D) := Classical.decEq _

/-- The two ports are ordered by which one is the old traversal root. -/
def rootCutContinuation (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    Perm (Fin D.nArc) :=
  D.continuation * swap (D.incoming c i) (D.incoming c (otherBranch i))

theorem rootCutContinuation_eq (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    rootCutContinuation D c i = cutContinuation D c := by
  fin_cases i <;> simp [rootCutContinuation, cutContinuation, swap_comm]

theorem rootCut_ports_distinct (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    D.incoming c i ≠ D.incoming c (otherBranch i) := by
  fin_cases i
  · exact (D.four_ports_distinct c).1
  · exact (D.four_ports_distinct c).1.symm

theorem rootCut_sameCycle (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) (i : Fin 2) :
    D.continuation.SameCycle (D.incoming c i) (D.incoming c (otherBranch i)) := by
  fin_cases i
  · exact hself
  · exact hself.symm

/-- Root-oriented cut labels transported to the actual geometric smoothing. -/
def smoothRootCutComponentEquiv (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    Component (rootCutContinuation D c i) ≃ diagramComponent (smoothCrossing D c) :=
  (componentEquivOfIntertwining (Equiv.refl (Fin D.nArc))
    (rootCutContinuation D c i) (cutContinuation D c)
    (fun x => congrArg (fun p : Perm (Fin D.nArc) => p x) (rootCutContinuation_eq D c i))).trans
    (smoothCutComponentEquiv D c)

@[simp] theorem smoothRootCutComponentEquiv_old (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (i : Fin 2) (x : Fin D.nArc) :
    smoothRootCutComponentEquiv D c i (componentOf (rootCutContinuation D c i) x) =
      componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl x)) := rfl

theorem smoothRootCutComponentEquiv_connector (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (i j : Fin 2) :
    smoothRootCutComponentEquiv D c i
      (componentOf (rootCutContinuation D c i) (D.incoming c j)) =
      componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inr j)) := by
  change smoothCutComponentEquiv D c
    (componentOf (cutContinuation D c) (D.incoming c j)) = _
  exact smoothCutComponentEquiv_connector D c j

abbrev RootSelfCutLabels (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :=
  Bool ⊕ {C : diagramComponent D // C ≠ componentOf D.continuation (D.incoming c i)}

def rootSelfCutComponents (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) (i : Fin 2) :
    RootSelfCutLabels D c i ≃ diagramComponent (smoothCrossing D c) :=
  (cutComponentSumEquiv D.continuation (D.incoming c i) (D.incoming c (otherBranch i))
    (rootCut_ports_distinct D c i) (rootCut_sameCycle D c hself i)).symm.trans
      (smoothRootCutComponentEquiv D c i)

theorem rootSelfCutComponents_false (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) (i : Fin 2) :
    rootSelfCutComponents D c hself i (Sum.inl false) =
      componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inr i)) := by
  let e := cutComponentSumEquiv D.continuation (D.incoming c i)
    (D.incoming c (otherBranch i)) (rootCut_ports_distinct D c i)
    (rootCut_sameCycle D c hself i)
  have he : e (componentOf (rootCutContinuation D c i) (D.incoming c i)) = Sum.inl false :=
    cutComponentSumEquiv_left D.continuation (D.incoming c i)
      (D.incoming c (otherBranch i)) (rootCut_ports_distinct D c i) (rootCut_sameCycle D c hself i)
  change smoothRootCutComponentEquiv D c i (e.symm (Sum.inl false)) = _
  rw [← he, Equiv.symm_apply_apply]
  exact smoothRootCutComponentEquiv_connector D c i i

theorem rootSelfCutComponents_true (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) (i : Fin 2) :
    rootSelfCutComponents D c hself i (Sum.inl true) =
      componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (otherBranch i))) := by
  let e := cutComponentSumEquiv D.continuation (D.incoming c i)
    (D.incoming c (otherBranch i)) (rootCut_ports_distinct D c i)
    (rootCut_sameCycle D c hself i)
  have he : e (componentOf (rootCutContinuation D c i) (D.incoming c (otherBranch i))) = Sum.inl true :=
    cutComponentSumEquiv_right D.continuation (D.incoming c i)
      (D.incoming c (otherBranch i)) (rootCut_ports_distinct D c i) (rootCut_sameCycle D c hself i)
  change smoothRootCutComponentEquiv D c i (e.symm (Sum.inl true)) = _
  rw [← he, Equiv.symm_apply_apply]
  exact smoothRootCutComponentEquiv_connector D c i (otherBranch i)

theorem rootSelfCutComponents_other (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) (i : Fin 2)
    (C : {C : diagramComponent D // C ≠ componentOf D.continuation (D.incoming c i)}) :
    rootSelfCutComponents D c hself i (Sum.inr C) =
      componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inl (T.baseArc C.val).val)) := by
  let e := cutComponentSumEquiv D.continuation (D.incoming c i)
    (D.incoming c (otherBranch i)) (rootCut_ports_distinct D c i)
    (rootCut_sameCycle D c hself i)
  have hc : componentOf D.continuation (T.baseArc C.val).val ≠
      componentOf D.continuation (D.incoming c i) := by
    rw [(T.baseArc C.val).property]
    exact C.property
  have he : e (componentOf (rootCutContinuation D c i) (T.baseArc C.val).val) = Sum.inr C := by
    rw [show e (componentOf (rootCutContinuation D c i) (T.baseArc C.val).val) =
      Sum.inr ⟨componentOf D.continuation (T.baseArc C.val).val, hc⟩ from
      cutComponentSumEquiv_other D.continuation (D.incoming c i)
        (D.incoming c (otherBranch i)) (T.baseArc C.val).val (rootCut_ports_distinct D c i)
        (rootCut_sameCycle D c hself i) hc]
    congr 1
    exact Subtype.ext (T.baseArc C.val).property
  change smoothRootCutComponentEquiv D c i (e.symm (Sum.inr C)) = _
  rw [← he, Equiv.symm_apply_apply]
  exact smoothRootCutComponentEquiv_old D c i (T.baseArc C.val).val

def rootSelfCutRoots (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) :
    RootSelfCutLabels D c i → Fin (smoothCrossing D c).nArc
  | Sum.inl false => smoothArcEquiv D (Sum.inr i)
  | Sum.inl true => smoothArcEquiv D (Sum.inr (otherBranch i))
  | Sum.inr C => smoothArcEquiv D (Sum.inl (T.baseArc C.val).val)

def rootSelfCutOrder (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) (i : Fin 2) :
    RootSelfCutLabels D c i ≃ Fin (diagramComponentCount (smoothCrossing D c)) :=
  (splitSumToFinMiddleFirst T.componentIndex (componentOf D.continuation (D.incoming c i))).trans
    (Equiv.cast (congrArg Fin (smooth_componentCount_self D c hself).symm))

/-- Concrete self-smoothing traversal: middle cut interval first, then tail;
connector roots on the two new components; original roots everywhere else. -/
def rootSelfSmoothingTraversal (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) (i : Fin 2) :
    BasedTraversal (smoothCrossing D c) :=
  basedTraversalOfComponentRoots (rootSelfCutComponents D c hself i)
    (rootSelfCutOrder D T c hself i) (rootSelfCutRoots D T c i) (by
      intro l
      cases l with
      | inl b =>
        cases b
        · exact (rootSelfCutComponents_false D c hself i).symm
        · exact (rootSelfCutComponents_true D c hself i).symm
      | inr C => exact (rootSelfCutComponents_other D T c hself i C).symm)

@[simp] theorem rootSelfSmoothingTraversal_baseArc (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) (i : Fin 2)
    (l : RootSelfCutLabels D c i) :
    ((rootSelfSmoothingTraversal D T c hself i).baseArc
      (rootSelfCutComponents D c hself i l)).val = rootSelfCutRoots D T c i l := by
  apply basedTraversalOfComponentRoots_baseArc

@[simp] theorem rootSelfSmoothingTraversal_index (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) (i : Fin 2)
    (l : RootSelfCutLabels D c i) :
    (rootSelfSmoothingTraversal D T c hself i).componentIndex
      (rootSelfCutComponents D c hself i l) = rootSelfCutOrder D T c hself i l := by
  apply basedTraversalOfComponentRoots_index

end
end DirectGLSSW.HOMFLY




