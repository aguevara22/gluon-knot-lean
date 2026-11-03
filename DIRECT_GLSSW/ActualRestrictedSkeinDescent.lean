import ProcessedParentDescent
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open LowestRowContract PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- An actual diagram and its actual based traversal, including arbitrary roots
on a detached extracted child. -/
abbrev ActualRestrictedSkeinState := Σ D : PLLinkDiagram, BasedTraversal D

/-- Literal skein branches. Smoothing may continue into any exact extracted
component and any traversal of that component. Extraction existence is separate. -/
inductive ActualRestrictedSkeinStep :
    ActualRestrictedSkeinState → ActualRestrictedSkeinState → Type where
  | switched (D : PLLinkDiagram) (T : BasedTraversal D)
      (c : Fin D.nCrossing) (hc : badAt T c) :
      ActualRestrictedSkeinStep ⟨D,T⟩ ⟨switchCrossing D c,switchTraversal T c⟩
  | smoothed (D : PLLinkDiagram) (T : BasedTraversal D)
      (c : Fin D.nCrossing) (C : Component (smoothCrossing D c).continuation)
      (R : ComponentRestriction (smoothCrossing D c) C) (U : BasedTraversal R.diagram) :
      ActualRestrictedSkeinStep ⟨D,T⟩ ⟨R.diagram,U⟩

/-- Actual crossing count followed by actual bad-crossing count. -/
def actualRestrictedSkeinComplexity (s : ActualRestrictedSkeinState) : ℕ × ℕ :=
  (s.1.nCrossing, (badCrossings s.2).card)

/-- Either branch decreases the source's lexicographic complexity. -/
theorem ActualRestrictedSkeinStep.decreases {s t : ActualRestrictedSkeinState}
    (step : ActualRestrictedSkeinStep s t) :
    Prod.Lex (· < ·) (· < ·)
      (actualRestrictedSkeinComplexity t) (actualRestrictedSkeinComplexity s) := by
  cases step with
  | switched D T c hc =>
    apply Prod.Lex.right
    have hmem : c ∈ badCrossings T := by
      simpa only [badCrossings, Finset.mem_filter, Finset.mem_univ, true_and] using hc
    have hdrop := badCrossings_switch_card T c hmem
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_of_eq hdrop)
  | smoothed D T c C R U =>
    exact Prod.Lex.left _ _ (R.nCrossing_lt_before_smoothing D c C)

/-- Well-foundedness simultaneously covers switched parents and all actual
extracted smoothed children, independently of positive/exposed geometry. -/
theorem actualRestrictedSkeinStep_wellFounded :
    WellFounded (fun t s : ActualRestrictedSkeinState =>
      Nonempty (ActualRestrictedSkeinStep s t)) := by
  have hw : WellFounded (Prod.Lex (· < ·) (· < ·) : (ℕ × ℕ) → (ℕ × ℕ) → Prop) :=
    Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf
  exact (InvImage.wf actualRestrictedSkeinComplexity hw).mono
    (fun _ _ h => h.elim (fun step => step.decreases))

/-- No infinite branch can alternate the actual switch and any actual extracted
smoothing operations, even when each child traversal is chosen anew. -/
theorem no_infinite_actualRestrictedSkeinSteps (f : ℕ → ActualRestrictedSkeinState) :
    ¬ (∀ n, Nonempty (ActualRestrictedSkeinStep (f n) (f (n+1)))) := by
  intro h
  exact (WellFounded.wellFounded_iff_no_descending_seq.mp
    actualRestrictedSkeinStep_wellFounded).false ⟨f,h⟩

/-- Every marked parent operation is literally an instance of the all-component
skein relation; no traversal or diagram identification is assumed. -/
def MarkedParentStep.toActualRestrictedSkeinStep {s t : MarkedParentState}
    (step : MarkedParentStep s t) :
    ActualRestrictedSkeinStep ⟨s.1,s.2.1⟩ ⟨t.1,t.2.1⟩ := by
  cases step with
  | @switched D T S c hc hgood => exact .switched D T c hc
  | @smoothed D T S c hc hgood R =>
    exact .smoothed D T c _ R
      (R.basedTraversal (parentRootSelfSmoothingTraversal D T c (S.connected _ _)))

end DirectGLSSW.HOMFLY
