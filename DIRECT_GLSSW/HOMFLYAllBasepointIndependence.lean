import HOMFLYBasepointEvaluatorInvariance
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section
open PermutationOrbits

/-- Sum of forward distances from the current roots to the desired roots.
The target component enumeration is used solely to index this finite sum. -/
def basepointDistance {D : PLLinkDiagram} (T U : BasedTraversal D) : ℕ :=
  ∑ i : Fin (diagramComponentCount D),
    visitPosition T (U.baseArc (U.componentIndex.symm i)).val

theorem basepointDistance_advance_lt {D : PLLinkDiagram} (T U : BasedTraversal D)
    (C : diagramComponent D) (hne : (U.baseArc C).val ≠ (T.baseArc C).val) :
    basepointDistance (advanceBaseTraversal T C) U < basepointDistance T U := by
  classical
  unfold basepointDistance
  apply Finset.sum_lt_sum
  · intro i _
    let e := (U.baseArc (U.componentIndex.symm i)).val
    have he : componentOf D.continuation e = U.componentIndex.symm i :=
      (U.baseArc (U.componentIndex.symm i)).property
    by_cases hi : U.componentIndex.symm i = C
    · have hcomp : componentOf D.continuation e = C := he.trans hi
      have heval : e = (U.baseArc C).val := congrArg (fun X => (U.baseArc X).val) hi
      have hnot : e ≠ (T.baseArc C).val := heval ▸ hne
      have hp := visitPosition_advanceBase_nonroot T C e hcomp hnot
      change visitPosition (advanceBaseTraversal T C) e ≤ visitPosition T e
      omega
    · have hcomp : componentOf D.continuation e ≠ C := fun h => hi (he.symm.trans h)
      exact le_of_eq (visitPosition_advanceBase_other T C e hcomp)
  · refine ⟨U.componentIndex C, Finset.mem_univ _, ?_⟩
    have hp := visitPosition_advanceBase_nonroot T C (U.baseArc C).val
      (U.baseArc C).property hne
    have hlt : visitPosition (advanceBaseTraversal T C) (U.baseArc C).val <
        visitPosition T (U.baseArc C).val := by omega
    rw [U.componentIndex.symm_apply_apply C]
    exact hlt

/-- At a fixed crossing stage, all basepoint choices with the same component
order have the same value. Only the strict lower-crossing joint hypothesis
is used; no current-stage traversal invariance is assumed. -/
theorem descendingEvaluator_eq_of_componentIndex_eq {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    {D : PLLinkDiagram} (hD : D.nCrossing = n) (T U : BasedTraversal D)
    (horder : T.componentIndex = U.componentIndex) :
    descendingLaurentEvaluator D T = descendingLaurentEvaluator D U := by
  classical
  by_cases hb : ∀ C, (T.baseArc C).val = (U.baseArc C).val
  · exact congrArg (descendingLaurentEvaluator D) (basedTraversal_ext horder hb)
  · push_neg at hb
    obtain ⟨C, hC⟩ := hb
    have hstep := descendingEvaluator_advanceBase_eq outer D hD T C
    have hrest := descendingEvaluator_eq_of_componentIndex_eq outer hD
      (advanceBaseTraversal T C) U horder
    exact hstep.trans hrest
termination_by basepointDistance T U
decreasing_by
  exact basepointDistance_advance_lt T U C (Ne.symm hC)

end
end DirectGLSSW.HOMFLY




