import HOMFLYRootSelfEvaluatorTerminal
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits

theorem rootSelf_singleBranch_evaluator_eq {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (D : PLLinkDiagram) (hD : D.nCrossing = n)
    (T U : BasedTraversal D) (c : Fin D.nCrossing) (i : Fin 2)
    (hroot : (T.baseArc (componentOf D.continuation (D.incoming c i))).val = D.incoming c i)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (hbranches : ∀ d : Fin D.nCrossing, d ≠ c → firstVisitedBranch T d = firstVisitedBranch U d) :
    descendingLaurentEvaluator D T = descendingLaurentEvaluator D U := by
  classical
  by_cases hn : ((badCrossings T).erase c).Nonempty
  · obtain ⟨d,hd⟩ := hn
    have hdc : d ≠ c := (Finset.mem_erase.mp hd).1
    have hdMem : d ∈ badCrossings T := (Finset.mem_erase.mp hd).2
    have hdT : badAt T d := by simpa only [badCrossings, Finset.mem_filter,
      Finset.mem_univ, true_and] using hdMem
    have hdU : badAt U d := by
      change firstVisitedBranch U d ≠ D.overBranch d
      rw [← hbranches d hdc]
      exact hdT
    have hsD : (switchCrossing D d).nCrossing = n := hD
    have hsroot : ((switchTraversal T d).baseArc
      (componentOf (switchCrossing D d).continuation ((switchCrossing D d).incoming c i))).val =
        (switchCrossing D d).incoming c i := hroot
    have hsself : (switchCrossing D d).continuation.SameCycle
      ((switchCrossing D d).incoming c 0) ((switchCrossing D d).incoming c 1) := hself
    have hsbranches : ∀ e : Fin (switchCrossing D d).nCrossing, e ≠ c →
        firstVisitedBranch (switchTraversal T d) e = firstVisitedBranch (switchTraversal U d) e := by
      intro e he
      simpa using hbranches e he
    have hs := rootSelf_singleBranch_evaluator_eq outer (switchCrossing D d) hsD
      (switchTraversal T d) (switchTraversal U d) c i hsroot hsself hsbranches
    rw [descendingEvaluator_eq_any_bad_pivot outer D hD T d hdT,
      descendingEvaluator_eq_any_bad_pivot outer D hD U d hdU,
      descendingEvaluatorPivotBranch, descendingEvaluatorPivotBranch, hs]
  · have hgoodT : ∀ d : Fin D.nCrossing, d ≠ c → ¬ badAt T d := by
      intro d hdc hb
      apply hn
      refine ⟨d, Finset.mem_erase.mpr ⟨hdc, ?_⟩⟩
      simpa only [badCrossings, Finset.mem_filter, Finset.mem_univ, true_and] using hb
    have hgoodU : ∀ d : Fin D.nCrossing, d ≠ c → ¬ badAt U d := by
      intro d hdc hb
      apply hgoodT d hdc
      change firstVisitedBranch T d ≠ D.overBranch d
      rw [hbranches d hdc]
      exact hb
    obtain ⟨W,hW⟩ := smoothCrossing_exists_descending_of_baseArc D T
      (componentOf D.continuation (D.incoming c i)) c i hroot.symm hself hgoodT
    exact (evaluator_eq_unlink_of_only_self_bad outer D hD T c hself hgoodT W hW).trans
      (evaluator_eq_unlink_of_only_self_bad outer D hD U c hself hgoodU W hW).symm
termination_by ((badCrossings T).erase c).card
decreasing_by
  rw [badCrossings_switch_erase T d hdMem, Finset.erase_right_comm]
  exact Finset.card_erase_lt_of_mem hd

end DirectGLSSW.HOMFLY

