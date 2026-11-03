import HOMFLYTraversalFromRoots
import DirectGLSSW.HOMFLY.Coefficients

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open Coefficients
noncomputable section

def IsNormalizedDescendingSkeinEvaluator
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff) : Prop :=
  (∀ (D : PLLinkDiagram) (hD : 0 < D.nArc) (T : BasedTraversal D),
    badCrossings T = ∅ →
      H D hD = unlinkFactor ^ (diagramComponentCount D - 1)) ∧
  (∀ (D : PLLinkDiagram) (hD : 0 < D.nArc) (c : Fin D.nCrossing),
    match crossingSign D c with
    | .pos => aMonomial * H D hD -
        aInvMonomial * H (switchCrossing D c) hD =
        zMonomial * H (smoothCrossing D c) (by change 0 < D.nArc + 2; omega)
    | .neg => aMonomial * H (switchCrossing D c) hD -
        aInvMonomial * H D hD =
        zMonomial * H (smoothCrossing D c) (by change 0 < D.nArc + 2; omega))

private theorem unique_by_induction
    (H K : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    (hK : IsNormalizedDescendingSkeinEvaluator K)
    (D : PLLinkDiagram) (hD : 0 < D.nArc) (T : BasedTraversal D) :
    H D hD = K D hD := by
  classical
  by_cases hdesc : badCrossings T = ∅
  · exact (hH.1 D hD T hdesc).trans (hK.1 D hD T hdesc).symm
  · have hbad : (badCrossings T).Nonempty := Finset.nonempty_iff_ne_empty.mpr hdesc
    obtain ⟨c, hc⟩ := hbad
    have hsw := unique_by_induction H K hH hK (switchCrossing D c) hD
      (switchTraversal T c)
    have hsm := unique_by_induction H K hH hK (smoothCrossing D c)
      (by change 0 < D.nArc + 2; omega) (smoothChildBasedTraversal D c)
    have hF := hH.2 D hD c
    have hK' := hK.2 D hD c
    cases hs : crossingSign D c with
    | pos =>
        have hInv : aInvMonomial * aMonomial = 1 := by
          rw [mul_comm, aMonomial_mul_aInvMonomial]
        simp [hs] at hF hK'
        rw [hsw, hsm] at hF
        have hmul : aMonomial * H D hD = aMonomial * K D hD := by
          exact sub_left_inj.mp (hF.trans hK'.symm)
        calc
          H D hD = aInvMonomial * (aMonomial * H D hD) := by
            rw [← mul_assoc, hInv, one_mul]
          _ = aInvMonomial * (aMonomial * K D hD) := by rw [hmul]
          _ = K D hD := by
            rw [← mul_assoc, hInv, one_mul]
    | neg =>
        simp [hs] at hF hK'
        rw [hsw, hsm] at hF
        have hmul : aInvMonomial * H D hD = aInvMonomial * K D hD := by
          exact (sub_right_inj.mp (hK'.trans hF.symm)).symm
        calc
          H D hD = aMonomial * (aInvMonomial * H D hD) := by
            rw [← mul_assoc, aMonomial_mul_aInvMonomial, one_mul]
          _ = aMonomial * (aInvMonomial * K D hD) := by rw [hmul]
          _ = K D hD := by
            rw [← mul_assoc, aMonomial_mul_aInvMonomial, one_mul]
  termination_by (D.nCrossing, (badCrossings T).card)
  decreasing_by
    · simp_wf
      have hdrop := badCrossings_switch_card T c hc
      omega
    · simp_wf
      have hdrop := smoothCrossing_crossing_count_drop D c
      omega

theorem normalized_descending_skein_evaluator_unique
    (H K : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    (hK : IsNormalizedDescendingSkeinEvaluator K)
    (D : PLLinkDiagram) (hD : 0 < D.nArc) : H D hD = K D hD := by
  classical
  exact unique_by_induction H K hH hK D hD (chooseBasedTraversal D)

end
end DirectGLSSW.HOMFLY




