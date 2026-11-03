import HOMFLYRootSelfEvaluatorTerminal

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section
open Coefficients

/-- Smoothing removes the very crossing whose overbranch was switched.
All retained signed data agree; independently chosen geometry is irrelevant. -/
def smoothSwitchSameSignedDiagramIso (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    SignedDiagramIso (smoothCrossing (switchCrossing D c) c) (smoothCrossing D c) where
  arcEquiv := Equiv.refl _
  crossingEquiv := Equiv.refl _
  incoming_map := by
    intro x i
    exact congrFun (congrFun (smoothIncoming_switch D c c) x) i
  outgoing_map := by
    intro x i
    exact congrFun (congrFun (smoothOutgoing_switch D c c) x) i
  continuation_map := by
    intro e
    exact congrArg (fun f : Equiv.Perm (Fin (D.nArc + 2)) => f e)
      (smoothContinuation_switch D c c)
  through_map := by
    intro x
    exact congrFun (smoothThrough_switch D c c) x
  overBranch_map := by
    intro x
    change (switchCrossing D c).overBranch ((smoothCrossingEquiv (switchCrossing D c) c).symm x).val =
      D.overBranch ((smoothCrossingEquiv D c).symm x).val
    rw [smoothCrossingEquiv_switch]
    exact Function.update_of_ne ((smoothCrossingEquiv D c).symm x).property _ _
  crossingSign_map := by
    intro x
    let old := (smoothCrossingEquiv D c).symm x
    have hS : smoothCrossingEquiv (switchCrossing D c) c old = x := by
      rw [smoothCrossingEquiv_switch]
      exact (smoothCrossingEquiv D c).apply_symm_apply x
    have hD : smoothCrossingEquiv D c old = x :=
      (smoothCrossingEquiv D c).apply_symm_apply x
    have hsource := crossingSign_smoothRetained (switchCrossing D c) c old.val old.property
    have htarget := crossingSign_smoothRetained D c old.val old.property
    change crossingSign (smoothCrossing (switchCrossing D c) c)
      (smoothCrossingEquiv (switchCrossing D c) c old) =
        crossingSign (switchCrossing D c) old.val at hsource
    change crossingSign (smoothCrossing D c) (smoothCrossingEquiv D c old) =
      crossingSign D old.val at htarget
    rw [hS] at hsource
    rw [hD] at htarget
    exact hsource.trans ((crossingSign_switchCrossing_of_ne D c old.val old.property).trans htarget.symm)

theorem descendingEvaluator_switch_twice (D : PLLinkDiagram)
    (T : BasedTraversal D) (c : Fin D.nCrossing) :
    descendingLaurentEvaluator (switchCrossing (switchCrossing D c) c)
      (switchTraversal (switchTraversal T c) c) = descendingLaurentEvaluator D T := by
  let F : (Fin D.nCrossing → Fin 2) → HOMFLYCoeff := fun b =>
    descendingLaurentEvaluator {D with overBranch := b}
      ⟨T.componentIndex, T.baseArc⟩
  change F (Function.update (Function.update D.overBranch c (otherBranch (D.overBranch c))) c
    (otherBranch ((Function.update D.overBranch c (otherBranch (D.overBranch c))) c))) =
      F D.overBranch
  apply congrArg F
  funext x
  by_cases hx : x = c <;> simp [Function.update_apply, hx, otherBranch_involutive]

private theorem pivot_reverse_expansion (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (x y : HOMFLYCoeff) :
    pivotSwitchFactor D c *
        (pivotSwitchFactor (switchCrossing D c) c * x +
          pivotSmoothFactor (switchCrossing D c) c * y) +
      pivotSmoothFactor D c * y = x := by
  have hai : aInvMonomial * aMonomial = 1 := by
    rw [mul_comm, aMonomial_mul_aInvMonomial]
  rw [pivotSwitchFactor, pivotSmoothFactor, pivotSwitchFactor, pivotSmoothFactor,
    crossingSign_switchCrossing]
  cases crossingSign D c <;> simp only [Sign.reverse]
  · calc
      _ = (aMonomial * aInvMonomial) * (aMonomial * aInvMonomial) * x +
          (aMonomial * aInvMonomial - 1) * aMonomial * zMonomial * y := by ring
      _ = x := by rw [aMonomial_mul_aInvMonomial]; ring
  · calc
      _ = (aInvMonomial * aMonomial) * (aInvMonomial * aMonomial) * x +
          (1 - aInvMonomial * aMonomial) * aInvMonomial * zMonomial * y := by ring
      _ = x := by rw [hai]; ring

/-- The full fixed-stage skein equation, including good pivots, follows from
strict lower-stage invariance and skein. No current-stage traversal hypothesis
or geometric move is assumed here. -/
theorem descendingEvaluator_eq_any_pivot {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n) (D : PLLinkDiagram)
    (hD : D.nCrossing = n) (T : BasedTraversal D) (c : Fin D.nCrossing) :
    descendingLaurentEvaluator D T = descendingEvaluatorPivotBranch D T c := by
  classical
  by_cases hc : badAt T c
  · exact descendingEvaluator_eq_any_bad_pivot outer D hD T c hc
  · have hcS : badAt (switchTraversal T c) c := (badAt_switch_toggle T c).2 hc
    have hstep := descendingEvaluator_eq_any_bad_pivot outer (switchCrossing D c) hD
      (switchTraversal T c) c hcS
    have hlt : (smoothCrossing (switchCrossing D c) c).nCrossing < n := by
      have hdrop := smoothCrossing_crossing_count_drop (switchCrossing D c) c
      change D.nCrossing - 1 + 1 = D.nCrossing at hdrop
      change D.nCrossing - 1 < n
      omega
    have hsm := outer.1 (smoothSwitchSameSignedDiagramIso D c) hlt
      (smoothChildBasedTraversal (switchCrossing D c) c)
      (smoothChildBasedTraversal D c)
    rw [descendingEvaluatorPivotBranch, descendingEvaluator_switch_twice, hsm] at hstep
    rw [descendingEvaluatorPivotBranch, hstep]
    exact (pivot_reverse_expansion D c (descendingLaurentEvaluator D T)
      (descendingLaurentEvaluator (smoothCrossing D c) (smoothChildBasedTraversal D c))).symm

end
end DirectGLSSW.HOMFLY




