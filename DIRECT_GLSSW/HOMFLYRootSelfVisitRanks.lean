import HOMFLYRootSelfSmoothingTraversal
import HOMFLYSmoothPositionWrappers
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : DecidableEq (diagramComponent D) := Classical.decEq _

def rootSelfPort (i : Fin 2) (b : Bool) : Fin 2 := if b then otherBranch i else i

theorem rootSelfCutComponents_selected (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) (i : Fin 2) (b : Bool) :
    rootSelfCutComponents D c hself i (Sum.inl b) =
      componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (rootSelfPort i b))) := by
  cases b
  · exact rootSelfCutComponents_false D c hself i
  · exact rootSelfCutComponents_true D c hself i

theorem rootSelf_selected_visitRank (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (i : Fin 2) (b : Bool) (x : Fin D.nArc)
    (hc : componentOf (cutContinuation D c) x =
      componentOf (cutContinuation D c) (D.incoming c (rootSelfPort i b)))
    (hx : x ≠ D.incoming c (rootSelfPort i b)) :
    visitRank (rootSelfSmoothingTraversal D T c hself i) (smoothArcEquiv D (Sum.inl x)) =
      (rootSelfCutOrder D T c hself i (Sum.inl b),
        ((orbitEnumeration (cutContinuation D c) (D.incoming c (rootSelfPort i b))).symm
          ⟨x,hc⟩).val) := by
  let U := rootSelfSmoothingTraversal D T c hself i
  have hs : componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl x)) =
      componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (rootSelfPort i b))) := by
    exact (congrArg (smoothCutComponentEquiv D c) hc).trans
      (smoothCutComponentEquiv_connector D c (rootSelfPort i b))
  have hl : componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl x)) =
      rootSelfCutComponents D c hself i (Sum.inl b) :=
    hs.trans (rootSelfCutComponents_selected D c hself i b).symm
  have hbase : (U.baseArc (componentOf (smoothCrossing D c).continuation
      (smoothArcEquiv D (Sum.inl x)))).val = smoothArcEquiv D (Sum.inr (rootSelfPort i b)) := by
    rw [hl]
    change ((rootSelfSmoothingTraversal D T c hself i).baseArc _).val = _
    rw [rootSelfSmoothingTraversal_baseArc]
    cases b <;> rfl
  unfold visitRank
  rw [show visitPosition U (smoothArcEquiv D (Sum.inl x)) =
      ((orbitEnumeration (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (rootSelfPort i b)))).symm
          ⟨smoothArcEquiv D (Sum.inl x),hs⟩).val from
    visitPosition_eq_orbitPosition_of_baseArc U _ _ hbase hs]
  rw [smoothConnector_orbitPosition D c hself (rootSelfPort i b) x hc hx hs, hl,
    rootSelfSmoothingTraversal_index]

end
end DirectGLSSW.HOMFLY

