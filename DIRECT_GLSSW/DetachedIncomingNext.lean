import DetachedIncomingOrder
import ChildMarkedCycleComparison
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract MarkedCycleGaps
attribute [local instance] Classical.propDecidable
variable {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

theorem detachedOrbitEquiv_symm_step (x : Fin R.diagram.nArc) :
    (detachedOrbitEquiv t c R).symm (R.diagram.continuation x) =
      cyclicSuccessorPerm _ ((detachedOrbitEquiv t c R).symm x) := by
  apply (detachedOrbitEquiv t c R).injective
  rw [Equiv.apply_symm_apply]
  have hh := congrArg Subtype.val (orbitEnumeration_successor
    R.diagram.continuation (detachedConnector t c R) ((detachedOrbitEquiv t c R).symm x))
  change detachedOrbitEquiv t c R (cyclicSuccessorPerm _ ((detachedOrbitEquiv t c R).symm x)) =
    R.diagram.continuation (detachedOrbitEquiv t c R ((detachedOrbitEquiv t c R).symm x)) at hh
  rw [Equiv.apply_symm_apply] at hh
  exact hh.symm

/-- The actual historical incoming marks inside the exact original cut fibre. -/
def MarkedParentTrace.detachedOriginalIncomingMark (m : Fin R.diagram.nCrossing × Fin 2) :
    Fibre (cutContinuation s.1 (h.crossingOrigin c))
      (componentOf (cutContinuation s.1 (h.crossingOrigin c))
        (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)) :=
  ⟨s.1.incoming (h.detachedCrossingOrigin c R m.1) m.2,
    h.detachedIncoming_cut_component c hc R m.1 m.2⟩

theorem MarkedParentTrace.detachedOriginalIncomingMark_injective :
    Function.Injective (h.detachedOriginalIncomingMark c hc R) := by
  intro x y he
  have hv := congrArg Subtype.val he
  have hh := @incomingMark_injective s.1
    (h.detachedCrossingOrigin c R x.1,x.2)
    (h.detachedCrossingOrigin c R y.1,y.2) hv
  exact Prod.ext ((h.detachedCrossingOrigin c R).injective (congrArg Prod.fst hh))
    (congrArg (fun z : Fin s.1.nCrossing × Fin 2 => z.2) hh)

/-- Actual incoming next-mark permutation is unchanged when the fresh connector
is removed and old arcs are labelled in the exact original singleton cut. -/
theorem MarkedParentTrace.detachedIncoming_next_eq :
    next R.diagram.continuation
      (fun m : Fin R.diagram.nCrossing × Fin 2 => R.diagram.incoming m.1 m.2)
      (@incomingMark_injective R.diagram) =
    next (fibrePerm (cutContinuation s.1 (h.crossingOrigin c))
      (componentOf (cutContinuation s.1 (h.crossingOrigin c))
        (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)))
      (h.detachedOriginalIncomingMark c hc R)
      (h.detachedOriginalIncomingMark_injective c hc R) := by
  apply next_eq_of_coordinate_order _ _ (detachedOrbitEquiv t c R).symm
    (orbitEnumeration (cutContinuation s.1 (h.crossingOrigin c))
      (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)).symm
  · exact detachedOrbitEquiv_symm_step c R
  · intro x
    apply (orbitEnumeration (cutContinuation s.1 (h.crossingOrigin c))
      (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)).injective
    rw [Equiv.apply_symm_apply,orbitEnumeration_successor,Equiv.apply_symm_apply]
  · intro x y
    exact h.detachedIncoming_cut_order c hc R x.1 y.1 x.2 y.2





end DirectGLSSW.HOMFLY
