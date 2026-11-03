import HOMFLYDescendingSelfSmoothing
import UnlinkPivotIdentity
import DirectGLSSW.HOMFLY.HOMFLYInnerTransportInduction
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits

theorem descendingEvaluator_eq_any_bad_pivot {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (D : PLLinkDiagram) (hD : D.nCrossing = n) (T : BasedTraversal D)
    (c : Fin D.nCrossing) (hc : badAt T c) :
    descendingLaurentEvaluator D T = descendingEvaluatorPivotBranch D T c := by
  exact (innerBadCard_simultaneous_induction outer ((badCrossings T).card + 1)).1
    hD T c (Nat.lt_succ_self _) hc

theorem evaluator_eq_unlink_of_only_self_bad {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (D : PLLinkDiagram) (hD : D.nCrossing = n)
    (V : BasedTraversal D) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (hgood : ∀ d : Fin D.nCrossing, d ≠ c → ¬ badAt V d)
    (W : BasedTraversal (smoothCrossing D c)) (hW : badCrossings W = ∅) :
    descendingLaurentEvaluator D V = descendingUnlinkValue D := by
  classical
  by_cases hc : badAt V c
  · have hcMem : c ∈ badCrossings V := by simpa only [badCrossings, Finset.mem_filter,
      Finset.mem_univ, true_and] using hc
    have hsEmpty : badCrossings (switchTraversal V c) = ∅ := by
      rw [badCrossings_switch_erase V c hcMem]
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro d hd
      have hd' := Finset.mem_erase.mp hd
      exact hgood d hd'.1 (by simpa only [badCrossings, Finset.mem_filter,
        Finset.mem_univ, true_and] using hd'.2)
    have hs := descendingLaurentEvaluator_terminal (switchCrossing D c)
      (switchTraversal V c) (by simp only [hsEmpty, Finset.not_nonempty_empty, eq_false])
    have hlt : (smoothCrossing D c).nCrossing < n := by
      have h := smoothCrossing_crossing_count_drop D c
      omega
    have hsm := outer.1 (SignedDiagramIso.refl (smoothCrossing D c)) hlt
      (smoothChildBasedTraversal D c) W
    have hw := descendingLaurentEvaluator_terminal (smoothCrossing D c) W
      (by simp only [hW, Finset.not_nonempty_empty, eq_false])
    rw [hw] at hsm
    rw [descendingEvaluator_eq_any_bad_pivot outer D hD V c hc,
      descendingEvaluatorPivotBranch, hs, hsm]
    exact descendingUnlinkValue_self_pivot D c hself
  · have hEmpty : badCrossings V = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro d hd
      have hb : badAt V d := by simpa only [badCrossings, Finset.mem_filter,
        Finset.mem_univ, true_and] using hd
      by_cases hdc : d = c
      · exact hc (hdc ▸ hb)
      · exact hgood d hdc hb
    exact descendingLaurentEvaluator_terminal D V
      (by simp only [hEmpty, Finset.not_nonempty_empty, eq_false])

end DirectGLSSW.HOMFLY


