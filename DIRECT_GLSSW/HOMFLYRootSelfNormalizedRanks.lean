import HOMFLYRootSelfVisitRanks
import HOMFLYCutPositionWrappers
import HOMFLYCutSideComponents
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : DecidableEq (diagramComponent D) := Classical.decEq _

theorem rootSelf_middle_visitRank (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) (i : Fin 2)
    (j : Fin (Fintype.card (Fibre D.continuation (componentOf D.continuation (D.incoming c i)))))
    (hj : FiniteCycleSplit.cutSide (cutMarkIndex D.continuation (D.incoming c i)
      (D.incoming c (otherBranch i)) (rootCut_sameCycle D c hself i)) j = true)
    (hjex : j ≠ (cutMarkIndex D.continuation (D.incoming c i) (D.incoming c (otherBranch i)) (rootCut_sameCycle D c hself i))) :
    visitRank (rootSelfSmoothingTraversal D T c hself i)
      (smoothArcEquiv D (Sum.inl (orbitEnumeration D.continuation (D.incoming c i) j).val)) =
      (rootSelfCutOrder D T c hself i (Sum.inl true), j.val) := by
  have hcomp := cutMiddle_component D.continuation (D.incoming c i)
    (D.incoming c (otherBranch i)) (rootCut_ports_distinct D c i) (rootCut_sameCycle D c hself i) j hj
  have hc : componentOf (cutContinuation D c) (orbitEnumeration D.continuation (D.incoming c i) j).val =
      componentOf (cutContinuation D c) (D.incoming c (otherBranch i)) := by
    have h := hcomp
    change componentOf (rootCutContinuation D c i) _ = componentOf (rootCutContinuation D c i) _ at h
    rw [rootCutContinuation_eq] at h
    exact h
  have hx : (orbitEnumeration D.continuation (D.incoming c i) j).val ≠ D.incoming c (otherBranch i) := by
    intro he
    apply hjex
    apply (Subtype.val_injective.comp (orbitEnumeration D.continuation (D.incoming c i)).injective)
    exact he.trans (cutMarkIndex_enumerate D.continuation (D.incoming c i)
      (D.incoming c (otherBranch i)) (rootCut_sameCycle D c hself i)).symm
  have hr := rootSelf_selected_visitRank D T c hself i true
    (orbitEnumeration D.continuation (D.incoming c i) j).val hc hx
  have hp := cutMiddle_orbitPosition D.continuation (D.incoming c i)
    (D.incoming c (otherBranch i)) (rootCut_ports_distinct D c i) (rootCut_sameCycle D c hself i) j hj hjex hcomp
  exact hr.trans (congrArg (fun n => (rootSelfCutOrder D T c hself i (Sum.inl true), n))
    ((orbitPosition_perm_congr (cutContinuation D c)
      (D.continuation * swap (D.incoming c i) (D.incoming c (otherBranch i)))
      (rootCutContinuation_eq D c i).symm (D.incoming c (otherBranch i))
      (orbitEnumeration D.continuation (D.incoming c i) j).val hc hcomp).trans hp))

theorem rootSelf_tail_visitRank (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) (i : Fin 2)
    (j : Fin (Fintype.card (Fibre D.continuation (componentOf D.continuation (D.incoming c i)))))
    (hj : FiniteCycleSplit.cutSide (cutMarkIndex D.continuation (D.incoming c i)
      (D.incoming c (otherBranch i)) (rootCut_sameCycle D c hself i)) j = false)
    (hjex : j ≠ 0) :
    visitRank (rootSelfSmoothingTraversal D T c hself i)
      (smoothArcEquiv D (Sum.inl (orbitEnumeration D.continuation (D.incoming c i) j).val)) =
      (rootSelfCutOrder D T c hself i (Sum.inl false), j.val - (cutMarkIndex D.continuation (D.incoming c i)
          (D.incoming c (otherBranch i)) (rootCut_sameCycle D c hself i)).val) := by
  have hcomp := cutTail_component D.continuation (D.incoming c i)
    (D.incoming c (otherBranch i))  (rootCut_sameCycle D c hself i) j hj
  have hc : componentOf (cutContinuation D c) (orbitEnumeration D.continuation (D.incoming c i) j).val =
      componentOf (cutContinuation D c) (D.incoming c i) := by
    have h := hcomp
    change componentOf (rootCutContinuation D c i) _ = componentOf (rootCutContinuation D c i) _ at h
    rw [rootCutContinuation_eq] at h
    exact h
  have hx : (orbitEnumeration D.continuation (D.incoming c i) j).val ≠ D.incoming c i := by
    intro he
    apply hjex
    apply (Subtype.val_injective.comp (orbitEnumeration D.continuation (D.incoming c i)).injective)
    exact he.trans (orbitEnumeration_zero D.continuation (D.incoming c i)).symm
  have hr := rootSelf_selected_visitRank D T c hself i false
    (orbitEnumeration D.continuation (D.incoming c i) j).val hc hx
  have hp := cutTail_orbitPosition D.continuation (D.incoming c i)
    (D.incoming c (otherBranch i))  (rootCut_sameCycle D c hself i) j hj hjex hcomp
  exact hr.trans (congrArg (fun n => (rootSelfCutOrder D T c hself i (Sum.inl false), n))
    ((orbitPosition_perm_congr (cutContinuation D c)
      (D.continuation * swap (D.incoming c i) (D.incoming c (otherBranch i)))
      (rootCutContinuation_eq D c i).symm (D.incoming c i)
      (orbitEnumeration D.continuation (D.incoming c i) j).val hc hcomp).trans hp))

end
end DirectGLSSW.HOMFLY


