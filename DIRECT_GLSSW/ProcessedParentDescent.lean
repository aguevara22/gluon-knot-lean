import ComponentRestrictionCrossingBound
import Mathlib.Order.WellFounded
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open LowestRowContract PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- The literal finite complexity used by the source descending calculation. -/
def markedParentComplexity (s : MarkedParentState) : ℕ × ℕ :=
  (s.1.nCrossing, (badCrossings s.2.1).card)

/-- Each actual parent operation strictly decreases the lexicographic complexity. -/
theorem MarkedParentStep.decreases {s t : MarkedParentState}
    (step : MarkedParentStep s t) :
    Prod.Lex (· < ·) (· < ·) (markedParentComplexity t) (markedParentComplexity s) := by
  cases step with
  | @switched D T S c hc hgood =>
    apply Prod.Lex.right
    have hmem : c ∈ badCrossings T := by
      simpa only [badCrossings, Finset.mem_filter, Finset.mem_univ, true_and] using hc
    have hdrop := badCrossings_switch_card T c hmem
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_of_eq hdrop)
  | @smoothed D T S c hc hgood R =>
    exact Prod.Lex.left _ _ (R.nCrossing_lt_before_smoothing D c _)

/-- The inverse of actual parent steps is well-founded. This permits recursion
through any supplied actual extracted parent, without an infinite parent path. -/
theorem markedParentStep_wellFounded :
    WellFounded (fun t s : MarkedParentState => Nonempty (MarkedParentStep s t)) := by
  have hw : WellFounded (Prod.Lex (· < ·) (· < ·) : (ℕ × ℕ) → (ℕ × ℕ) → Prop) :=
    Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf
  exact (InvImage.wf markedParentComplexity hw).mono
    (fun _ _ h => h.elim (fun step => step.decreases))

/-- No infinite sequence can consist entirely of the two actual parent operations. -/
theorem no_infinite_markedParentSteps (f : ℕ → MarkedParentState) :
    ¬ (∀ n, Nonempty (MarkedParentStep (f n) (f (n+1)))) := by
  intro h
  exact (WellFounded.wellFounded_iff_no_descending_seq.mp
    markedParentStep_wellFounded).false ⟨f,h⟩

end DirectGLSSW.HOMFLY
