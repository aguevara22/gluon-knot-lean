import NormalizedEvaluatorUniqueness
import HOMFLYRegularDeletionInduction

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY.Gemini

open DirectGLSSW.HOMFLY DirectGLSSW.HOMFLY.Coefficients

noncomputable section

/-- The concrete candidate evaluator obtained by choosing an arbitrary based
traversal on each link diagram. -/
noncomputable def candidateEvaluator (D : PLLinkDiagram) (_hD : 0 < D.nArc) : HOMFLYCoeff :=
  descendingLaurentEvaluator D (chooseBasedTraversal D)

theorem positive_skein_of_pivot (Hplus Hminus Hzero : HOMFLYCoeff)
    (hpivot : Hplus = (aInvMonomial * aInvMonomial) * Hminus +
      (aInvMonomial * zMonomial) * Hzero) :
    aMonomial * Hplus - aInvMonomial * Hminus = zMonomial * Hzero := by
  have hmul : aMonomial * Hplus = aInvMonomial * Hminus + zMonomial * Hzero := by
    calc
      aMonomial * Hplus =
          aMonomial * ((aInvMonomial * aInvMonomial) * Hminus +
            (aInvMonomial * zMonomial) * Hzero) := by rw [hpivot]
      _ = (aMonomial * aInvMonomial) * (aInvMonomial * Hminus) +
          (aMonomial * aInvMonomial) * (zMonomial * Hzero) := by ring
      _ = aInvMonomial * Hminus + zMonomial * Hzero := by
        rw [aMonomial_mul_aInvMonomial, one_mul, one_mul]
  rw [hmul, add_sub_cancel_left]

theorem negative_skein_of_pivot (Hplus Hminus Hzero : HOMFLYCoeff)
    (hpivot : Hminus = (aMonomial * aMonomial) * Hplus +
      -(aMonomial * zMonomial) * Hzero) :
    aMonomial * Hplus - aInvMonomial * Hminus = zMonomial * Hzero := by
  have hinv : aInvMonomial * aMonomial = 1 := by
    rw [mul_comm, aMonomial_mul_aInvMonomial]
  have hmul : aInvMonomial * Hminus = aMonomial * Hplus - zMonomial * Hzero := by
    calc
      aInvMonomial * Hminus =
          aInvMonomial * ((aMonomial * aMonomial) * Hplus +
            -(aMonomial * zMonomial) * Hzero) := by rw [hpivot]
      _ = (aInvMonomial * aMonomial) * (aMonomial * Hplus) -
          (aInvMonomial * aMonomial) * (zMonomial * Hzero) := by ring
      _ = aMonomial * Hplus - zMonomial * Hzero := by
        rw [hinv, one_mul, one_mul]
  rw [hmul, sub_sub_cancel]

theorem candidateEvaluator_eq_traversal
    (hSkein : ∀ n : ℕ, LowerCrossingEvaluatorSkeinIH n)
    (D : PLLinkDiagram) (hD : 0 < D.nArc) (T : BasedTraversal D) :
    candidateEvaluator D hD = descendingLaurentEvaluator D T :=
  (hSkein (D.nCrossing + 1)).1 (SignedDiagramIso.refl D)
    (Nat.lt_succ_self D.nCrossing) (chooseBasedTraversal D) T

theorem candidateEvaluator_isNormalized
    (hSkein : ∀ n : ℕ, LowerCrossingEvaluatorSkeinIH n) :
    IsNormalizedDescendingSkeinEvaluator candidateEvaluator := by
  refine ⟨?_, ?_⟩
  · intro D hD T hbad
    rw [candidateEvaluator_eq_traversal hSkein D hD T]
    rw [descendingLaurentEvaluator_terminal D T (by simp [hbad])]
    simp [descendingUnlinkValue, Nat.ne_of_gt hD]
  · intro D hD c
    have hpivot := (hSkein (D.nCrossing + 1)).2 (Nat.lt_succ_self D.nCrossing)
      (chooseBasedTraversal D) c
    have hsw : descendingLaurentEvaluator (switchCrossing D c)
        (switchTraversal (chooseBasedTraversal D) c) =
        candidateEvaluator (switchCrossing D c) hD :=
      (candidateEvaluator_eq_traversal hSkein (switchCrossing D c) hD
        (switchTraversal (chooseBasedTraversal D) c)).symm
    have hsm : descendingLaurentEvaluator (smoothCrossing D c)
        (smoothChildBasedTraversal D c) =
        candidateEvaluator (smoothCrossing D c) (by change 0 < D.nArc + 2; omega) :=
      (candidateEvaluator_eq_traversal hSkein (smoothCrossing D c)
        (by change 0 < D.nArc + 2; omega) (smoothChildBasedTraversal D c)).symm
    change descendingLaurentEvaluator D (chooseBasedTraversal D) =
      pivotSwitchFactor D c *
        descendingLaurentEvaluator (switchCrossing D c)
          (switchTraversal (chooseBasedTraversal D) c) +
      pivotSmoothFactor D c *
        descendingLaurentEvaluator (smoothCrossing D c)
          (smoothChildBasedTraversal D c) at hpivot
    rw [hsw, hsm] at hpivot
    cases hs : crossingSign D c with
    | pos =>
        simp only [pivotSwitchFactor, pivotSmoothFactor, hs] at hpivot
        exact positive_skein_of_pivot
          (candidateEvaluator D hD)
          (candidateEvaluator (switchCrossing D c) hD)
          (candidateEvaluator (smoothCrossing D c) (by change 0 < D.nArc + 2; omega))
          hpivot
    | neg =>
        simp only [pivotSwitchFactor, pivotSmoothFactor, hs] at hpivot
        exact negative_skein_of_pivot
          (candidateEvaluator (switchCrossing D c) hD)
          (candidateEvaluator D hD)
          (candidateEvaluator (smoothCrossing D c) (by change 0 < D.nArc + 2; omega))
          hpivot

theorem candidateEvaluator_signedDiagramIso
    (hSkein : ∀ n : ℕ, LowerCrossingEvaluatorSkeinIH n)
    (D E : PLLinkDiagram) (hD : 0 < D.nArc) (hE : 0 < E.nArc)
    (I : SignedDiagramIso D E) :
    candidateEvaluator D hD = candidateEvaluator E hE :=
  (hSkein (D.nCrossing + 1)).1 I (Nat.lt_succ_self D.nCrossing)
    (chooseBasedTraversal D) (chooseBasedTraversal E)

theorem lowerRegularDeletion_transport_of_all_skeinIH
    (hSkein : ∀ n : ℕ, LowerCrossingEvaluatorSkeinIH n) :
    ∀ n : ℕ, ∀ {D E : PLLinkDiagram} (R : SignedRegularDeletion D E),
      D.nCrossing < n →
      ∀ T : BasedTraversal D,
        descendingLaurentEvaluator D T =
          descendingLaurentEvaluator E (R.transportTraversal T)
  | 0, _, _, _, hlt, _ => False.elim (Nat.not_lt_zero _ hlt)
  | n + 1, D, E, R, hlt, T => by
      by_cases hlt' : D.nCrossing < n
      · exact lowerRegularDeletion_transport_of_all_skeinIH hSkein n R hlt' T
      · have hEq : D.nCrossing = n := by omega
        exact R.evaluator_induction_stage (hSkein n)
          (lowerRegularDeletion_transport_of_all_skeinIH hSkein n) hEq T

theorem candidateEvaluator_signedRegularDeletion
    (hSkein : ∀ n : ℕ, LowerCrossingEvaluatorSkeinIH n)
    (D E : PLLinkDiagram) (hD : 0 < D.nArc) (hE : 0 < E.nArc)
    (R : SignedRegularDeletion D E) :
    candidateEvaluator D hD = candidateEvaluator E hE := by
  have htr := lowerRegularDeletion_transport_of_all_skeinIH hSkein (D.nCrossing + 1)
    R (Nat.lt_succ_self D.nCrossing) (chooseBasedTraversal D)
  exact htr.trans (candidateEvaluator_eq_traversal hSkein E hE
    (R.transportTraversal (chooseBasedTraversal D))).symm

theorem normalizedEvaluator_existsUnique_of_all_skeinIH
    (hSkein : ∀ n : ℕ, LowerCrossingEvaluatorSkeinIH n) :
    ∃! H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff,
      IsNormalizedDescendingSkeinEvaluator H := by
  refine ⟨candidateEvaluator, candidateEvaluator_isNormalized hSkein, ?_⟩
  intro K hK
  funext D hD
  exact normalized_descending_skein_evaluator_unique K candidateEvaluator
    hK (candidateEvaluator_isNormalized hSkein) D hD

theorem normalizedEvaluator_package_of_all_skeinIH
    (hSkein : ∀ n : ℕ, LowerCrossingEvaluatorSkeinIH n) :
    ∃ H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff,
      IsNormalizedDescendingSkeinEvaluator H ∧
      (∀ K : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff,
        IsNormalizedDescendingSkeinEvaluator K → K = H) ∧
      (∀ (D : PLLinkDiagram) (hD : 0 < D.nArc) (T : BasedTraversal D),
        H D hD = descendingLaurentEvaluator D T) ∧
      (∀ (D E : PLLinkDiagram) (hD : 0 < D.nArc) (hE : 0 < E.nArc),
        SignedDiagramIso D E → H D hD = H E hE) ∧
      (∀ (D E : PLLinkDiagram) (hD : 0 < D.nArc) (hE : 0 < E.nArc),
        SignedRegularDeletion D E → H D hD = H E hE) := by
  refine ⟨candidateEvaluator, candidateEvaluator_isNormalized hSkein, ?_, ?_, ?_, ?_⟩
  · intro K hK
    funext D hD
    exact normalized_descending_skein_evaluator_unique K candidateEvaluator
      hK (candidateEvaluator_isNormalized hSkein) D hD
  · exact candidateEvaluator_eq_traversal hSkein
  · exact candidateEvaluator_signedDiagramIso hSkein
  · exact candidateEvaluator_signedRegularDeletion hSkein

end

end DirectGLSSW.HOMFLY.Gemini



