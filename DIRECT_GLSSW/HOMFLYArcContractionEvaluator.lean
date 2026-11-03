import HOMFLYArcContractionInduction
import Gemini.Solution

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY
open Coefficients
noncomputable section
namespace SignedArcContraction

/-- The lower-stage premises are discharged by the proved normalized evaluator package. -/
private theorem lower_evaluator_transport :
    ∀ n : ℕ, ∀ {D E : PLLinkDiagram} (R : SignedArcContraction D E),
      D.nCrossing < n → ∀ T : BasedTraversal D,
        descendingLaurentEvaluator D T =
          descendingLaurentEvaluator E (R.transportTraversal T)
  | 0, _, _, _, hlt, _ => False.elim (Nat.not_lt_zero _ hlt)
  | n + 1, D, E, R, hlt, T => by
      by_cases hlt' : D.nCrossing < n
      · exact lower_evaluator_transport n R hlt' T
      · have hEq : D.nCrossing = n := by omega
        exact R.evaluator_induction_stage (Gemini.all_lowerCrossingEvaluatorSkeinIH n)
          (lower_evaluator_transport n) hEq T

/-- Actual contraction preserves the concrete evaluator for every pair of traversals. -/
theorem evaluator_eq {D E : PLLinkDiagram} (R : SignedArcContraction D E)
    (T : BasedTraversal D) (U : BasedTraversal E) :
    descendingLaurentEvaluator D T = descendingLaurentEvaluator E U := by
  have h := lower_evaluator_transport (D.nCrossing + 1) R (Nat.lt_succ_self _) T
  have hT := Gemini.candidateEvaluator_eq_traversal
    Gemini.all_lowerCrossingEvaluatorSkeinIH E R.target_nArc_pos (R.transportTraversal T)
  have hU := Gemini.candidateEvaluator_eq_traversal
    Gemini.all_lowerCrossingEvaluatorSkeinIH E R.target_nArc_pos U
  exact h.trans (hT.symm.trans hU)

/-- The accepted candidate evaluator respects the more general actual contraction. -/
theorem candidateEvaluator_eq {D E : PLLinkDiagram} (R : SignedArcContraction D E)
    (hD : 0 < D.nArc) (hE : 0 < E.nArc) :
    Gemini.candidateEvaluator D hD = Gemini.candidateEvaluator E hE := by
  exact R.evaluator_eq (chooseBasedTraversal D) (chooseBasedTraversal E)

/-- Any normalized descending signed-skein evaluator respects actual contraction.
The certificate has no evaluator equality or post-smoothing assumption. -/
theorem normalizedEvaluator_eq
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    {D E : PLLinkDiagram} (R : SignedArcContraction D E)
    (hD : 0 < D.nArc) (hE : 0 < E.nArc) : H D hD = H E hE := by
  have hG := Gemini.candidateEvaluator_isNormalized Gemini.all_lowerCrossingEvaluatorSkeinIH
  have hD' := normalized_descending_skein_evaluator_unique H Gemini.candidateEvaluator hH hG D hD
  have hE' := normalized_descending_skein_evaluator_unique H Gemini.candidateEvaluator hH hG E hE
  exact hD'.trans ((R.candidateEvaluator_eq hD hE).trans hE'.symm)

end SignedArcContraction
end
end DirectGLSSW.HOMFLY
