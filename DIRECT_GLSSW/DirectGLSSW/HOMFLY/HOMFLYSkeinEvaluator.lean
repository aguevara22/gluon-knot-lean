import DirectGLSSW.HOMFLY.Coefficients
import DirectGLSSW.HOMFLY.BasedTraversal
import DirectGLSSW.HOMFLY.HOMFYSmoothingTraversalBridge

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

open Coefficients

/-- The source convention's value on a split `k`-component unlink. The
zero-component empty diagram is assigned the multiplicative unit separately. -/
noncomputable def descendingUnlinkValue (D : PLLinkDiagram) : HOMFLYCoeff :=
  if D.nArc = 0 then 1
  else unlinkFactor ^ (diagramComponentCount D - 1)

theorem descendingUnlinkValue_empty : descendingUnlinkValue emptyDiagram = 1 := by
  simp [descendingUnlinkValue, emptyDiagram]

theorem descendingUnlinkValue_of_nonempty_components (D : PLLinkDiagram)
    (h : 0 < diagramComponentCount D) :
    descendingUnlinkValue D = unlinkFactor ^ (diagramComponentCount D - 1) := by
  have harc : D.nArc ≠ 0 := by
    intro hz
    have hempty : IsEmpty (PermutationOrbits.Component D.continuation) := by
      refine ⟨fun C => Quotient.inductionOn C ?_⟩
      intro e
      rw [hz] at e
      exact Fin.elim0 e
    have hc : diagramComponentCount D = 0 := by
      exact Fintype.card_eq_zero_iff.mpr hempty
    omega
  simp [descendingUnlinkValue, harc]

theorem positive_skein_solve (Hplus Hminus Hzero : HOMFLYCoeff)
    (hskein : aMonomial * Hplus - aInvMonomial * Hminus = zMonomial * Hzero) :
    Hplus = aInvMonomial * aInvMonomial * Hminus +
      aInvMonomial * zMonomial * Hzero := by
  have hplus : aMonomial * Hplus = aInvMonomial * Hminus + zMonomial * Hzero := by
    calc
      aMonomial * Hplus =
          (aMonomial * Hplus - aInvMonomial * Hminus) + aInvMonomial * Hminus :=
            (sub_add_cancel _ _).symm
      _ = zMonomial * Hzero + aInvMonomial * Hminus := by rw [hskein]
      _ = aInvMonomial * Hminus + zMonomial * Hzero := add_comm _ _
  have hinv : aInvMonomial * aMonomial = 1 := by
    rw [mul_comm, aMonomial_mul_aInvMonomial]
  calc
    Hplus = (aInvMonomial * aMonomial) * Hplus := by rw [hinv, one_mul]
    _ = aInvMonomial * (aMonomial * Hplus) := by ac_rfl
    _ = aInvMonomial * (aInvMonomial * Hminus + zMonomial * Hzero) := by rw [hplus]
    _ = aInvMonomial * aInvMonomial * Hminus +
        aInvMonomial * zMonomial * Hzero := by rw [mul_add, ← mul_assoc, ← mul_assoc]

theorem negative_skein_solve (Hplus Hminus Hzero : HOMFLYCoeff)
    (hskein : aMonomial * Hplus - aInvMonomial * Hminus = zMonomial * Hzero) :
    Hminus = aMonomial * aMonomial * Hplus -
      aMonomial * zMonomial * Hzero := by
  have hminus : aInvMonomial * Hminus = aMonomial * Hplus - zMonomial * Hzero := by
    apply (eq_sub_iff_add_eq).2
    calc
      aInvMonomial * Hminus + zMonomial * Hzero =
          zMonomial * Hzero + aInvMonomial * Hminus := add_comm _ _
      _ = aMonomial * Hplus := by
        calc
          zMonomial * Hzero + aInvMonomial * Hminus =
              (aMonomial * Hplus - aInvMonomial * Hminus) +
                aInvMonomial * Hminus := by rw [hskein]
          _ = aMonomial * Hplus := sub_add_cancel _ _
  calc
    Hminus = (aMonomial * aInvMonomial) * Hminus := by rw [aMonomial_mul_aInvMonomial, one_mul]
    _ = aMonomial * (aInvMonomial * Hminus) := by ac_rfl
    _ = aMonomial * (aMonomial * Hplus - zMonomial * Hzero) := by rw [hminus]
    _ = aMonomial * (aMonomial * Hplus) - aMonomial * (zMonomial * Hzero) := by
      rw [mul_sub]
    _ = aMonomial * aMonomial * Hplus - aMonomial * zMonomial * Hzero := by
      rw [← mul_assoc, ← mul_assoc]

/-- The concrete descending skein evaluator. At a bad crossing it uses the
actual crossing switch with the inherited traversal, and the actual oriented
smoothing with a freshly chosen traversal of that child. -/
noncomputable def descendingLaurentEvaluator :
    (D : PLLinkDiagram) → (T : BasedTraversal D) → HOMFLYCoeff
  | D, T => by
      classical
      exact if hbad : (badCrossings T).Nonempty then
        let c := Classical.choose hbad
        match crossingSign D c with
        | .pos =>
            aInvMonomial * aInvMonomial *
                descendingLaurentEvaluator (switchCrossing D c) (switchTraversal T c) +
              aInvMonomial * zMonomial *
                descendingLaurentEvaluator (smoothCrossing D c) (smoothChildBasedTraversal D c)
        | .neg =>
            aMonomial * aMonomial *
                descendingLaurentEvaluator (switchCrossing D c) (switchTraversal T c) -
              aMonomial * zMonomial *
                descendingLaurentEvaluator (smoothCrossing D c) (smoothChildBasedTraversal D c)
      else descendingUnlinkValue D
termination_by D T => (D.nCrossing, (badCrossings T).card)

decreasing_by
  all_goals
    simp_wf
    apply (Prod.lex_def).2
    simp only [Prod.fst, Prod.snd, lt_self_iff_false, eq_self, true_and, false_or]
    first
    | have hdec := smoothCrossing_crossing_count_drop D (Classical.choose hbad)
      omega
    | have hc : Classical.choose hbad ∈ badCrossings T := Classical.choose_spec hbad
      have hdec := badCrossings_switch_card T (Classical.choose hbad) hc
      omega

/-- The recursive equation at its selected bad crossing, with coefficients
fixed by the source skein convention. -/
theorem descendingLaurentEvaluator_step (D : PLLinkDiagram)
    (T : BasedTraversal D) (hbad : (badCrossings T).Nonempty) :
    descendingLaurentEvaluator D T =
      match crossingSign D (Classical.choose hbad) with
      | .pos =>
          aInvMonomial * aInvMonomial *
              descendingLaurentEvaluator (switchCrossing D (Classical.choose hbad))
                (switchTraversal T (Classical.choose hbad)) +
            aInvMonomial * zMonomial *
              descendingLaurentEvaluator (smoothCrossing D (Classical.choose hbad))
                (smoothChildBasedTraversal D (Classical.choose hbad))
      | .neg =>
          aMonomial * aMonomial *
              descendingLaurentEvaluator (switchCrossing D (Classical.choose hbad))
                (switchTraversal T (Classical.choose hbad)) -
            aMonomial * zMonomial *
              descendingLaurentEvaluator (smoothCrossing D (Classical.choose hbad))
                (smoothChildBasedTraversal D (Classical.choose hbad)) := by
  classical
  rw [descendingLaurentEvaluator]
  simp only [dif_pos hbad]

/-- On a zero-component input the evaluator's terminal convention is explicit;
nonempty-link inputs retain the source unlink factor. This does not assert
basepoint/order independence or Reidemeister invariance. -/
theorem descendingLaurentEvaluator_terminal (D : PLLinkDiagram)
    (T : BasedTraversal D) (h : (badCrossings T).Nonempty = False) :
    descendingLaurentEvaluator D T = descendingUnlinkValue D := by
  classical
  simp [descendingLaurentEvaluator, h]

theorem descendingLaurentEvaluator_empty :
    descendingLaurentEvaluator emptyDiagram (chooseBasedTraversal emptyDiagram) = 1 := by
  rw [descendingLaurentEvaluator_terminal]
  · exact descendingUnlinkValue_empty
  · simp [badCrossings, emptyDiagram]

theorem descendingLaurentEvaluator_terminal_nonempty (D : PLLinkDiagram)
    (T : BasedTraversal D) (hgood : (badCrossings T).Nonempty = False)
    (hcomponents : 0 < diagramComponentCount D) :
    descendingLaurentEvaluator D T = unlinkFactor ^ (diagramComponentCount D - 1) := by
  rw [descendingLaurentEvaluator_terminal D T hgood]
  exact descendingUnlinkValue_of_nonempty_components D hcomponents











end DirectGLSSW.HOMFLY
