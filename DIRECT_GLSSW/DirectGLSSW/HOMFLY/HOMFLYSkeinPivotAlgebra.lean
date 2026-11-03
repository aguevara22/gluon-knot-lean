import DirectGLSSW.HOMFLY.HOMFLYSignedIsoTraversal
import DirectGLSSW.HOMFLY.HOMFLYSwitchSmoothDiamond
import DirectGLSSW.HOMFLY.HOMFLYDoubleSmoothingContinuation

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

open Coefficients

/-- The coefficient of the switched child in the source-convention skein
expansion at a crossing. -/
noncomputable def pivotSwitchFactor (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    HOMFLYCoeff :=
  match crossingSign D c with
  | .pos => aInvMonomial * aInvMonomial
  | .neg => aMonomial * aMonomial

/-- The coefficient of the smoothed child in the source-convention skein
expansion at a crossing. -/
noncomputable def pivotSmoothFactor (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    HOMFLYCoeff :=
  match crossingSign D c with
  | .pos => aInvMonomial * zMonomial
  | .neg => -(aMonomial * zMonomial)

theorem pivotSwitchFactor_switch_ne (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) :
    pivotSwitchFactor (switchCrossing D d) c = pivotSwitchFactor D c := by
  rw [pivotSwitchFactor, pivotSwitchFactor, crossingSign_switchCrossing_of_ne D d c hcd]

theorem pivotSmoothFactor_switch_ne (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) :
    pivotSmoothFactor (switchCrossing D d) c = pivotSmoothFactor D c := by
  rw [pivotSmoothFactor, pivotSmoothFactor, crossingSign_switchCrossing_of_ne D d c hcd]

theorem pivotSwitchFactor_smooth_ne (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) :
    pivotSwitchFactor (smoothCrossing D d)
      (smoothCrossingEquiv D d ⟨c, hcd⟩) = pivotSwitchFactor D c := by
  rw [pivotSwitchFactor, pivotSwitchFactor, crossingSign_smoothRetained D d c hcd]

theorem pivotSmoothFactor_smooth_ne (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) :
    pivotSmoothFactor (smoothCrossing D d)
      (smoothCrossingEquiv D d ⟨c, hcd⟩) = pivotSmoothFactor D c := by
  rw [pivotSmoothFactor, pivotSmoothFactor, crossingSign_smoothRetained D d c hcd]

/-- The evaluator's recursive right-hand side expressed using the source sign
factor functions. -/
noncomputable def descendingEvaluatorPivotBranch (D : PLLinkDiagram)
    (T : BasedTraversal D) (c : Fin D.nCrossing) : HOMFLYCoeff :=
  pivotSwitchFactor D c *
      descendingLaurentEvaluator (switchCrossing D c) (switchTraversal T c) +
    pivotSmoothFactor D c *
      descendingLaurentEvaluator (smoothCrossing D c) (smoothChildBasedTraversal D c)

/-- The four grandchildren in the two orders of expanding distinct pivots
have coefficients that agree after the actual retained-sign lemmas. This is
the coefficient-level diamond; child evaluator equalities are supplied only
by the lower-crossing induction in the use site. -/
theorem twoPivotExpansion_algebra (a b c d x y z w : HOMFLYCoeff) :
    a * (c * x + d * y) + b * (c * z + d * w) =
      c * (a * x + b * z) + d * (a * y + b * w) := by
  simp only [mul_add]
  ac_rfl

/-- The coefficient diamond specialized to the actual positive/negative
source-convention factors at two parent crossings. -/
theorem actualTwoPivotExpansion_algebra (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (x y z w : HOMFLYCoeff) :
    pivotSwitchFactor D c *
        (pivotSwitchFactor D d * x + pivotSmoothFactor D d * y) +
      pivotSmoothFactor D c *
        (pivotSwitchFactor D d * z + pivotSmoothFactor D d * w) =
    pivotSwitchFactor D d *
        (pivotSwitchFactor D c * x + pivotSmoothFactor D c * z) +
      pivotSmoothFactor D d *
        (pivotSwitchFactor D c * y + pivotSmoothFactor D c * w) := by
  exact twoPivotExpansion_algebra (pivotSwitchFactor D c) (pivotSmoothFactor D c)
    (pivotSwitchFactor D d) (pivotSmoothFactor D d) x y z w

/-- Two distinct crossing switches commute on the actual signed diagram data.
The identity arc/crossing labels expose the four-grandchild switch corner. -/
def switchSwitchSignedDiagramIso_commute (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) :
    SignedDiagramIso (switchCrossing (switchCrossing D c) d)
      (switchCrossing (switchCrossing D d) c) where
  arcEquiv := Equiv.refl _
  crossingEquiv := Equiv.refl _
  incoming_map := by intros; rfl
  outgoing_map := by intros; rfl
  continuation_map := by intro; rfl
  through_map := by intro; rfl
  overBranch_map := by
    intro e
    by_cases hec : e = c <;> by_cases hed : e = d <;>
      simp [switchCrossing, Function.update_apply, hec, hed, hcd, hcd.symm]
  crossingSign_map := by
    intro e
    change crossingSign (switchCrossing (switchCrossing D c) d) e =
      crossingSign (switchCrossing (switchCrossing D d) c) e
    by_cases hec : e = c <;> by_cases hed : e = d
    · exact False.elim (hcd (hec.symm.trans hed))
    · subst e
      calc
        crossingSign (switchCrossing (switchCrossing D c) d) c =
            crossingSign (switchCrossing D c) c :=
          crossingSign_switchCrossing_of_ne (switchCrossing D c) d c hcd
        _ = (crossingSign D c).reverse := crossingSign_switchCrossing D c
        _ = (crossingSign (switchCrossing D d) c).reverse :=
          congrArg Sign.reverse (crossingSign_switchCrossing_of_ne D d c hcd).symm
        _ = crossingSign (switchCrossing (switchCrossing D d) c) c :=
          (crossingSign_switchCrossing (switchCrossing D d) c).symm
    · subst e
      calc
        crossingSign (switchCrossing (switchCrossing D c) d) d =
            (crossingSign (switchCrossing D c) d).reverse :=
          crossingSign_switchCrossing (switchCrossing D c) d
        _ = (crossingSign D d).reverse :=
          congrArg Sign.reverse (crossingSign_switchCrossing_of_ne D c d hcd.symm)
        _ = crossingSign (switchCrossing D d) d :=
          (crossingSign_switchCrossing D d).symm
        _ = crossingSign (switchCrossing (switchCrossing D d) c) d :=
          (crossingSign_switchCrossing_of_ne (switchCrossing D d) c d hcd.symm).symm
    · calc
        crossingSign (switchCrossing (switchCrossing D c) d) e =
            crossingSign (switchCrossing D c) e :=
          crossingSign_switchCrossing_of_ne (switchCrossing D c) d e hed
        _ = crossingSign D e := crossingSign_switchCrossing_of_ne D c e hec
        _ = crossingSign (switchCrossing D d) e :=
          (crossingSign_switchCrossing_of_ne D d e hed).symm
        _ = crossingSign (switchCrossing (switchCrossing D d) c) e :=
          (crossingSign_switchCrossing_of_ne (switchCrossing D d) c e hec).symm

/-- Induction-step premise, scoped to diagrams with fewer crossings. The
outer proof must establish this for all traversals and signed diagram
isomorphisms; it is not an axiom or a parameter of the final invariant. -/
def LowerCrossingEvaluatorInvariant (n : ℕ) : Prop :=
  ∀ {D E : PLLinkDiagram} (_I : SignedDiagramIso D E), D.nCrossing < n →
    ∀ (T : BasedTraversal D) (U : BasedTraversal E),
      descendingLaurentEvaluator D T = descendingLaurentEvaluator E U

theorem lowerIH_switchSmooth_child_eval_eq {n : ℕ}
    (ih : LowerCrossingEvaluatorInvariant n)
    (D : PLLinkDiagram) (c d : Fin D.nCrossing) (hcd : c ≠ d)
    (hD : D.nCrossing = n)
    (T : BasedTraversal (smoothCrossing (switchCrossing D d) c))
    (U : BasedTraversal
      (switchCrossing (smoothCrossing D c)
        (smoothCrossingEquiv D c ⟨d, hcd.symm⟩))) :
    descendingLaurentEvaluator (smoothCrossing (switchCrossing D d) c) T =
      descendingLaurentEvaluator
        (switchCrossing (smoothCrossing D c)
          (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)) U := by
  have hlt : (smoothCrossing (switchCrossing D d) c).nCrossing < n := by
    have h1 := smoothCrossing_crossing_count_drop (switchCrossing D d) c
    rw [switch_crossing_count] at h1
    rw [hD] at h1
    omega
  exact ih (switchSmoothSignedDiagramIso D c d hcd) hlt T U

theorem lowerIH_doubleSmooth_child_eval_eq {n : ℕ}
    (ih : LowerCrossingEvaluatorInvariant n)
    (D : PLLinkDiagram) (c d : Fin D.nCrossing) (hcd : c ≠ d)
    (hD : D.nCrossing = n)
    (T : BasedTraversal
      (smoothCrossing (smoothCrossing D c)
        (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)))
    (U : BasedTraversal
      (smoothCrossing (smoothCrossing D d)
        (smoothCrossingEquiv D d ⟨c, hcd⟩))) :
    descendingLaurentEvaluator
        (smoothCrossing (smoothCrossing D c)
          (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)) T =
      descendingLaurentEvaluator
        (smoothCrossing (smoothCrossing D d)
          (smoothCrossingEquiv D d ⟨c, hcd⟩)) U := by
  have hlt :
      (smoothCrossing (smoothCrossing D c)
        (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)).nCrossing < n := by
    have h1 := smoothCrossing_crossing_count_drop D c
    have h2 := smoothCrossing_crossing_count_drop (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)
    omega
  exact ih (smoothTwiceSignedDiagramIso D c d hcd) hlt T U

/-- Inner induction hypothesis for a fixed crossing count and a strict
bad-crossing-cardinality bound. -/
def InnerBadCardPivotIH (n k : ℕ) : Prop :=
  ∀ {D : PLLinkDiagram} (_hD : D.nCrossing = n)
    (T : BasedTraversal D) (c : Fin D.nCrossing),
    (badCrossings T).card < k → badAt T c →
      descendingLaurentEvaluator D T = descendingEvaluatorPivotBranch D T c

theorem innerIH_switch_child_other_pivot {n k : ℕ}
    (ih : InnerBadCardPivotIH n k)
    (D : PLLinkDiagram) (c d : Fin D.nCrossing) (hcd : c ≠ d)
    (hD : D.nCrossing = n) (T : BasedTraversal D)
    (hc : badAt T c) (hd : badAt T d)
    (hk : (badCrossings T).card = k) :
    descendingLaurentEvaluator (switchCrossing D c) (switchTraversal T c) =
      descendingEvaluatorPivotBranch (switchCrossing D c) (switchTraversal T c) d := by
  have hcMem : c ∈ badCrossings T := by simp [badCrossings, hc]
  have hdChild : badAt (switchTraversal T c) d :=
    (badAt_switch_same T c d hcd.symm).2 hd
  have hcard : (badCrossings (switchTraversal T c)).card < k := by
    have hdrop := badCrossings_switch_card T c hcMem
    omega
  have hDchild : (switchCrossing D c).nCrossing = n := by
    simpa [switch_crossing_count] using hD
  exact ih hDchild (switchTraversal T c) d hcard hdChild

theorem innerIH_switch_child_other_pivot_swap {n k : ℕ}
    (ih : InnerBadCardPivotIH n k)
    (D : PLLinkDiagram) (c d : Fin D.nCrossing) (hcd : c ≠ d)
    (hD : D.nCrossing = n) (T : BasedTraversal D)
    (hc : badAt T c) (hd : badAt T d)
    (hk : (badCrossings T).card = k) :
    descendingLaurentEvaluator (switchCrossing D d) (switchTraversal T d) =
      descendingEvaluatorPivotBranch (switchCrossing D d) (switchTraversal T d) c := by
  have hdMem : d ∈ badCrossings T := by simp [badCrossings, hd]
  have hcChild : badAt (switchTraversal T d) c :=
    (badAt_switch_same T d c hcd).2 hc
  have hcard : (badCrossings (switchTraversal T d)).card < k := by
    have hdrop := badCrossings_switch_card T d hdMem
    omega
  have hDchild : (switchCrossing D d).nCrossing = n := by
    simpa [switch_crossing_count] using hD
  exact ih hDchild (switchTraversal T d) c hcard hcChild

/-- The outer induction-step package includes both evaluator transport and
the full skein equation on every lower-crossing child. It is a local strong
induction premise, not a permanent assumption on the final evaluator. -/
def LowerCrossingEvaluatorSkeinIH (n : ℕ) : Prop :=
  LowerCrossingEvaluatorInvariant n ∧
    (∀ {D : PLLinkDiagram}, D.nCrossing < n →
      ∀ (T : BasedTraversal D) (c : Fin D.nCrossing),
        descendingLaurentEvaluator D T = descendingEvaluatorPivotBranch D T c)

/-- Inner strong induction also transports the evaluator across signed
isomorphisms whenever both based traversals have smaller bad-crossing count. -/
def InnerBadCardEvaluatorIH (n k : ℕ) : Prop :=
  ∀ {D E : PLLinkDiagram} (_I : SignedDiagramIso D E)
    (_hD : D.nCrossing = n) (T : BasedTraversal D) (U : BasedTraversal E),
    (badCrossings T).card < k → (badCrossings U).card < k →
      descendingLaurentEvaluator D T = descendingLaurentEvaluator E U

theorem innerIH_doubleSwitch_eval_eq {n k : ℕ}
    (ih : InnerBadCardEvaluatorIH n k)
    (D : PLLinkDiagram) (c d : Fin D.nCrossing) (hcd : c ≠ d)
    (hD : D.nCrossing = n) (T : BasedTraversal D)
    (hc : badAt T c) (hd : badAt T d)
    (hk : (badCrossings T).card = k) :
    descendingLaurentEvaluator (switchCrossing (switchCrossing D c) d)
        (switchTraversal (switchTraversal T c) d) =
      descendingLaurentEvaluator (switchCrossing (switchCrossing D d) c)
        (switchTraversal (switchTraversal T d) c) := by
  have hcMem : c ∈ badCrossings T := by simp [badCrossings, hc]
  have hdMem : d ∈ badCrossings T := by simp [badCrossings, hd]
  have hcdChild : d ∈ badCrossings (switchTraversal T c) := by
    simpa [badCrossings] using (badAt_switch_same T c d hcd.symm).2 hd
  have hdcChild : c ∈ badCrossings (switchTraversal T d) := by
    simpa [badCrossings] using (badAt_switch_same T d c hcd).2 hc
  have hcardCD :
      (badCrossings (switchTraversal (switchTraversal T c) d)).card < k := by
    have h1 := badCrossings_switch_card T c hcMem
    have h2 := badCrossings_switch_card (switchTraversal T c) d hcdChild
    omega
  have hcardDC :
      (badCrossings (switchTraversal (switchTraversal T d) c)).card < k := by
    have h1 := badCrossings_switch_card T d hdMem
    have h2 := badCrossings_switch_card (switchTraversal T d) c hdcChild
    omega
  have hD' :
      (switchCrossing (switchCrossing D c) d).nCrossing = n := by
    simpa [switch_crossing_count] using hD
  exact ih (switchSwitchSignedDiagramIso_commute D c d hcd) hD'
    (switchTraversal (switchTraversal T c) d)
    (switchTraversal (switchTraversal T d) c) hcardCD hcardDC

/-- For one fixed based traversal, expanding at either of two distinct bad
crossings gives the same skein branch. The proof uses the actual switch and
smoothing operations; all comparisons of smoothing grandchildren use the
lower-crossing isomorphism and skein induction packages. -/
theorem innerIH_twoBadPivot_branches_eq {n k : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (inner : InnerBadCardPivotIH n k)
    (innerIso : InnerBadCardEvaluatorIH n k)
    (D : PLLinkDiagram) (c d : Fin D.nCrossing) (hcd : c ≠ d)
    (hD : D.nCrossing = n) (T : BasedTraversal D)
    (hc : badAt T c) (hd : badAt T d)
    (hk : (badCrossings T).card = k) :
    descendingEvaluatorPivotBranch D T c =
      descendingEvaluatorPivotBranch D T d := by
  let sc := smoothChildBasedTraversal D c
  let sd := smoothChildBasedTraversal D d
  let dc := smoothCrossingEquiv D c ⟨d, hcd.symm⟩
  let cd := smoothCrossingEquiv D d ⟨c, hcd⟩
  have hsc : descendingLaurentEvaluator (switchCrossing D c) (switchTraversal T c) =
      descendingEvaluatorPivotBranch (switchCrossing D c) (switchTraversal T c) d :=
    innerIH_switch_child_other_pivot inner D c d hcd hD T hc hd hk
  have hsd : descendingLaurentEvaluator (switchCrossing D d) (switchTraversal T d) =
      descendingEvaluatorPivotBranch (switchCrossing D d) (switchTraversal T d) c :=
    innerIH_switch_child_other_pivot_swap inner D c d hcd hD T hc hd hk
  have hltc : (smoothCrossing D c).nCrossing < n := by
    have hdrop := smoothCrossing_crossing_count_drop D c
    rw [hD] at hdrop
    omega
  have hltd : (smoothCrossing D d).nCrossing < n := by
    have hdrop := smoothCrossing_crossing_count_drop D d
    rw [hD] at hdrop
    omega
  have hmc := outer.2 hltc sc dc
  have hmd := outer.2 hltd sd cd
  have hss := innerIH_doubleSwitch_eval_eq innerIso D c d hcd hD T hc hd hk
  have hys := lowerIH_switchSmooth_child_eval_eq outer.1 D d c hcd.symm hD
    (smoothChildBasedTraversal (switchCrossing D c) d)
    (switchTraversal sd (smoothCrossingEquiv D d ⟨c, hcd⟩))
  have hzs := lowerIH_switchSmooth_child_eval_eq outer.1 D c d hcd hD
    (smoothChildBasedTraversal (switchCrossing D d) c)
    (switchTraversal sc (smoothCrossingEquiv D c ⟨d, hcd.symm⟩))
  have hmm := lowerIH_doubleSmooth_child_eval_eq outer.1 D c d hcd hD
    (smoothChildBasedTraversal (smoothCrossing D c) dc)
    (smoothChildBasedTraversal (smoothCrossing D d) cd)
  change pivotSwitchFactor D c *
      descendingLaurentEvaluator (switchCrossing D c) (switchTraversal T c) +
    pivotSmoothFactor D c * descendingLaurentEvaluator (smoothCrossing D c) sc =
    pivotSwitchFactor D d *
      descendingLaurentEvaluator (switchCrossing D d) (switchTraversal T d) +
    pivotSmoothFactor D d * descendingLaurentEvaluator (smoothCrossing D d) sd
  rw [hsc, hsd, hmc, hmd]
  simp only [descendingEvaluatorPivotBranch]
  rw [pivotSwitchFactor_switch_ne D d c hcd.symm,
    pivotSmoothFactor_switch_ne D d c hcd.symm,
    pivotSwitchFactor_smooth_ne D c d hcd,
    pivotSmoothFactor_smooth_ne D c d hcd,
    pivotSwitchFactor_switch_ne D c d hcd,
    pivotSmoothFactor_switch_ne D c d hcd,
    pivotSwitchFactor_smooth_ne D d c hcd.symm,
    pivotSmoothFactor_smooth_ne D d c hcd.symm]
  rw [← hss, ← hys, ← hzs, ← hmm]
  exact actualTwoPivotExpansion_algebra D c d
    (descendingLaurentEvaluator
      (switchCrossing (switchCrossing D c) d)
      (switchTraversal (switchTraversal T c) d))
    (descendingLaurentEvaluator (smoothCrossing (switchCrossing D c) d)
      (smoothChildBasedTraversal (switchCrossing D c) d))
    (descendingLaurentEvaluator (smoothCrossing (switchCrossing D d) c)
      (smoothChildBasedTraversal (switchCrossing D d) c))
    (descendingLaurentEvaluator (smoothCrossing (smoothCrossing D c) dc)
      (smoothChildBasedTraversal (smoothCrossing D c) dc))

/-- A chosen bad pivot satisfies the actual evaluator equation. This helper
makes the choice condition explicit; it does not assert that another bad
pivot has the same branch value. -/
theorem descendingEvaluator_eq_pivotBranch_of_choice (D : PLLinkDiagram)
    (T : BasedTraversal D) (hbad : (badCrossings T).Nonempty)
    (c : Fin D.nCrossing) (hc : Classical.choose hbad = c) :
    descendingLaurentEvaluator D T = descendingEvaluatorPivotBranch D T c := by
  rw [← hc]
  cases hs : crossingSign D (Classical.choose hbad)
  · rw [descendingLaurentEvaluator_step D T hbad, hs]
    simp [descendingEvaluatorPivotBranch, pivotSwitchFactor, pivotSmoothFactor, hs]
    rw [sub_eq_add_neg]
  · rw [descendingLaurentEvaluator_step D T hbad, hs]
    simp [descendingEvaluatorPivotBranch, pivotSwitchFactor, pivotSmoothFactor, hs,
      mul_assoc, neg_mul]

/-- Successor step for the fixed-traversal pivot equation. A chosen bad pivot
is the evaluator's actual recursive pivot; the two-pivot theorem transports
that equation to any other bad pivot. -/
theorem innerIH_pivot_successor {n k : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (ihPivot : InnerBadCardPivotIH n k)
    (ihIso : InnerBadCardEvaluatorIH n k) :
    InnerBadCardPivotIH n (k + 1) := by
  intro D hD T c hcard hc
  by_cases hlt : (badCrossings T).card < k
  · exact ihPivot hD T c hlt hc
  · have hk : (badCrossings T).card = k := by omega
    have hnonempty : (badCrossings T).Nonempty := by
      refine ⟨c, ?_⟩
      simpa [badCrossings] using hc
    let c0 := Classical.choose hnonempty
    have hmem : c0 ∈ badCrossings T := Classical.choose_spec hnonempty
    have hc0 : badAt T c0 := by simpa [badCrossings] using hmem
    have heval := descendingEvaluator_eq_pivotBranch_of_choice D T hnonempty c0 rfl
    have hbranch : descendingEvaluatorPivotBranch D T c0 =
        descendingEvaluatorPivotBranch D T c := by
      by_cases heq : c0 = c
      · simpa [heq]
      · exact innerIH_twoBadPivot_branches_eq outer ihPivot ihIso
          D c0 c heq hD T hc0 hc hk
    exact heval.trans hbranch

end DirectGLSSW.HOMFLY





















