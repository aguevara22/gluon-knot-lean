import HOMFLYArcContractionChildTraversal
import HOMFLYRootSelfEvaluatorTerminal

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section
namespace SignedArcContraction

/-- Internal step of the joint crossing induction. The two lower-stage
premises remain explicit; this theorem does not close that induction. -/
theorem evaluator_induction_stage {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (lower : ∀ {D E : PLLinkDiagram} (R : SignedArcContraction D E),
      D.nCrossing < n → ∀ T : BasedTraversal D,
        descendingLaurentEvaluator D T =
          descendingLaurentEvaluator E (R.transportTraversal T))
    {D E : PLLinkDiagram} (R : SignedArcContraction D E)
    (hD : D.nCrossing = n) (T : BasedTraversal D) :
    descendingLaurentEvaluator D T =
      descendingLaurentEvaluator E (R.transportTraversal T) := by
  classical
  by_cases hbad : (badCrossings T).Nonempty
  · obtain ⟨c, hc⟩ := hbad
    have hcD : badAt T c := by
      simpa only [badCrossings, Finset.mem_filter, Finset.mem_univ, true_and] using hc
    have hcE : badAt (R.transportTraversal T) (R.crossingEquiv c) :=
      (R.badAt_map T c).2 hcD
    have hDE : D.nCrossing = E.nCrossing := by
      simpa only [Fintype.card_fin] using Fintype.card_congr R.crossingEquiv
    have hE : E.nCrossing = n := hDE.symm.trans hD
    have hSwitch := evaluator_induction_stage outer lower (R.switch c) hD
      (switchTraversal T c)
    rw [R.switch_transportTraversal] at hSwitch
    have hltD : (smoothCrossing D c).nCrossing < n := by
      have hdrop := smoothCrossing_crossing_count_drop D c
      omega
    have hltE : (smoothCrossing E (R.crossingEquiv c)).nCrossing < n := by
      have hdrop := smoothCrossing_crossing_count_drop E (R.crossingEquiv c)
      omega
    have hSmooth := lower (R.smooth c) hltD (smoothChildBasedTraversal D c)
    have hTraversal := outer.1
      (SignedDiagramIso.refl (smoothCrossing E (R.crossingEquiv c))) hltE
      ((R.smooth c).transportTraversal (smoothChildBasedTraversal D c))
      (smoothChildBasedTraversal E (R.crossingEquiv c))
    have hSmoothChosen := hSmooth.trans hTraversal
    have hA : pivotSwitchFactor D c = pivotSwitchFactor E (R.crossingEquiv c) := by
      simp only [pivotSwitchFactor, R.crossingSign_map c]
    have hB : pivotSmoothFactor D c = pivotSmoothFactor E (R.crossingEquiv c) := by
      simp only [pivotSmoothFactor, R.crossingSign_map c]
    rw [descendingEvaluator_eq_any_bad_pivot outer D hD T c hcD,
      descendingEvaluator_eq_any_bad_pivot outer E hE (R.transportTraversal T)
        (R.crossingEquiv c) hcE,
      descendingEvaluatorPivotBranch, descendingEvaluatorPivotBranch,
      hSwitch, hSmoothChosen, hA, hB]
  · exact R.evaluator_eq_of_descending T (Finset.not_nonempty_iff_eq_empty.mp hbad)
termination_by (badCrossings T).card
decreasing_by
  have hdrop := badCrossings_switch_card T c hc
  omega

end SignedArcContraction
end
end DirectGLSSW.HOMFLY


