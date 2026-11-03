import HOMFLYRootSelfSmoothingTraversal
import HOMFLYSmoothPositionWrappers
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : DecidableEq (diagramComponent D) := Classical.decEq _

theorem rootSelf_unaffected_visitRank (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (i : Fin 2)
    (C : {C : diagramComponent D // C ≠ componentOf D.continuation (D.incoming c i)})
    (x : Fin D.nArc) (hc : componentOf D.continuation x = C.val) :
    visitRank (rootSelfSmoothingTraversal D T c hself i) (smoothArcEquiv D (Sum.inl x)) =
      (rootSelfCutOrder D T c hself i (Sum.inr C), visitPosition T x) := by
  let U := rootSelfSmoothingTraversal D T c hself i
  let root := (T.baseArc C.val).val
  have hr : componentOf D.continuation root = C.val := (T.baseArc C.val).property
  have ha : ¬ D.continuation.SameCycle root (D.incoming c 0) := by
    intro h
    apply C.property
    rw [← hr]
    apply (componentOf_eq_iff _ _ _).2
    fin_cases i
    · exact h
    · exact h.trans hself
  have hb : ¬ D.continuation.SameCycle root (D.incoming c 1) :=
    fun h => ha (h.trans hself.symm)
  have hxc : componentOf D.continuation x = componentOf D.continuation root := hc.trans hr.symm
  have hcut : componentOf (cutContinuation D c) x = componentOf (cutContinuation D c) root := by
    apply (componentOf_eq_iff _ _ _).2
    exact ((cutUnaffected_sameCycle D.continuation (D.incoming c 0)
      (D.incoming c 1) root x ha hb).2 ((componentOf_eq_iff _ _ _).1 hxc.symm)).symm
  have hs : componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl x)) =
      componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl root)) :=
    congrArg (smoothCutComponentEquiv D c) hcut
  have hl : componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl x)) =
      rootSelfCutComponents D c hself i (Sum.inr C) :=
    hs.trans (rootSelfCutComponents_other D T c hself i C).symm
  have hbase : (U.baseArc (componentOf (smoothCrossing D c).continuation
      (smoothArcEquiv D (Sum.inl x)))).val = smoothArcEquiv D (Sum.inl root) := by
    rw [hl]
    exact rootSelfSmoothingTraversal_baseArc D T c hself i (Sum.inr C)
  have holdbase : (T.baseArc (componentOf D.continuation x)).val = root := by rw [hc]
  have hp := visitPosition_eq_orbitPosition_of_baseArc U _ _ hbase hs
  rw [smoothUnaffected_orbitPosition D c hself root x ha hxc hs] at hp
  rw [← visitPosition_eq_orbitPosition_of_baseArc T x root holdbase hxc] at hp
  unfold visitRank
  rw [hp, hl, rootSelfSmoothingTraversal_index]

end
end DirectGLSSW.HOMFLY

