import BranchIsoTraversal
import BranchIsoSmoothing
import NormalizedEvaluatorUniqueness
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DirectGLSSW.HOMFLY.BranchSignedDiagramIso
open Coefficients
private theorem compare
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    (D E : PLLinkDiagram) (hD : 0 < D.nArc) (hE : 0 < E.nArc)
    (I : BranchSignedDiagramIso D E) (T : BasedTraversal D) : H D hD=H E hE := by
  classical
  by_cases hdesc : badCrossings T=∅
  · have he : badCrossings (I.transportTraversal T)=∅ := by rw [I.badCrossings_map,hdesc];simp
    exact (hH.1 D hD T hdesc).trans ((congrArg (fun n=>unlinkFactor^(n-1)) I.componentCount_eq).trans (hH.1 E hE (I.transportTraversal T) he).symm)
  · obtain ⟨c,hc⟩:=Finset.nonempty_iff_ne_empty.mpr hdesc
    have hsw:=compare H hH (switchCrossing D c) (switchCrossing E (I.crossingEquiv c)) hD hE (I.switch c) (switchTraversal T c)
    have hsm:=compare H hH (smoothCrossing D c) (smoothCrossing E (I.crossingEquiv c))
      (by change 0<D.nArc+2;omega) (by change 0<E.nArc+2;omega) (I.smooth c) (smoothChildBasedTraversal D c)
    have hd:=hH.2 D hD c
    have he:=hH.2 E hE (I.crossingEquiv c)
    rw [←I.crossingSign_map c] at he
    cases hs : crossingSign D c with
    | pos =>
      simp only [hs] at hd he
      rw [hsw,hsm] at hd
      have hm : aMonomial*H D hD=aMonomial*H E hE:=sub_left_inj.mp (hd.trans he.symm)
      have hi : aInvMonomial*aMonomial=1:=by rw [mul_comm,aMonomial_mul_aInvMonomial]
      calc
        H D hD=aInvMonomial*(aMonomial*H D hD):=by rw [←mul_assoc,hi,one_mul]
        _=aInvMonomial*(aMonomial*H E hE):=by rw [hm]
        _=H E hE:=by rw [←mul_assoc,hi,one_mul]
    | neg =>
      simp only [hs] at hd he
      rw [hsw,hsm] at hd
      have hm : aInvMonomial*H D hD=aInvMonomial*H E hE:=(sub_right_inj.mp (he.trans hd.symm)).symm
      calc
        H D hD=aMonomial*(aInvMonomial*H D hD):=by rw [←mul_assoc,aMonomial_mul_aInvMonomial,one_mul]
        _=aMonomial*(aInvMonomial*H E hE):=by rw [hm]
        _=H E hE:=by rw [←mul_assoc,aMonomial_mul_aInvMonomial,one_mul]
  termination_by (D.nCrossing,(badCrossings T).card)
  decreasing_by
  · simp_wf
    have hdrop:=badCrossings_switch_card T c hc
    omega
  · simp_wf
    have hdrop:=smoothCrossing_crossing_count_drop D c
    omega

theorem normalizedEvaluator_eq
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    {D E : PLLinkDiagram} (I : BranchSignedDiagramIso D E)
    (hD : 0 < D.nArc) (hE : 0 < E.nArc) : H D hD=H E hE :=
  compare H hH D E hD hE I (chooseBasedTraversal D)
end DirectGLSSW.HOMFLY.BranchSignedDiagramIso
