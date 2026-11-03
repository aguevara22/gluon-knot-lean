import PrincipalTurning
import SmoothingPositiveShortening
import DirectGLSSW.HOMFLY.HOMFYSmoothingDiagram

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open scoped BigOperators

/-- Literal code-indexed displacement of the corrected smoothing constructor. -/
theorem arcVector_smooth_code (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : SmoothArcCode D) :
    arcVector (smoothCrossing D c) (smoothArcEquiv D e) =
      ⟨(smoothVertexPointGeometryCode D c (smoothEpsilon D c)
          (smoothArcTargetGeometryCode D c e)).1 -
          (smoothVertexPointGeometryCode D c (smoothEpsilon D c)
          (smoothArcSourceCode D c e)).1,
        (smoothVertexPointGeometryCode D c (smoothEpsilon D c)
          (smoothArcTargetGeometryCode D c e)).2 -
          (smoothVertexPointGeometryCode D c (smoothEpsilon D c)
          (smoothArcSourceCode D c e)).2⟩ := by
  simp [arcVector, smoothCrossing, smoothVertexPoint, smoothArcSource, smoothArcTarget]

noncomputable def crossingVector (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) : ℂ := ⟨(strandTangent D c i).1, (strandTangent D c i).2⟩

theorem arcVector_smooth_connector (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) :
    arcVector (smoothCrossing D c) (smoothArcEquiv D (Sum.inr i)) =
      (smoothEpsilon D c : ℂ) * (crossingVector D c 0 + crossingVector D c 1) := by
  rw [arcVector_smooth_code]
  rw [smoothArcSourceGeometryCode_connector, smoothArcTargetGeometryCode_connector]
  fin_cases i <;> apply Complex.ext <;>
    simp [incomingCutPoint, outgoingCutPoint, crossingVector, otherBranch_zero,
      otherBranch_one, Complex.mul_re, Complex.mul_im] <;> ring

theorem continuation_smooth_code (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : SmoothArcCode D) :
    (smoothCrossing D c).continuation (smoothArcEquiv D e) =
      smoothArcEquiv D (smoothContinuationGeometryCode D c e) := by
  simp [smoothCrossing, smoothContinuation, Equiv.trans_apply]

theorem totalTurn_smooth_reindex (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    totalTurn (smoothCrossing D c) =
      (∑ e : Fin D.nArc, turn (smoothCrossing D c) (smoothArcEquiv D (Sum.inl e))) +
      ∑ i : Fin 2, turn (smoothCrossing D c) (smoothArcEquiv D (Sum.inr i)) := by
  unfold totalTurn
  change (∑ e : Fin (D.nArc + 2), turn (smoothCrossing D c) e) = _
  rw [← Fintype.sum_equiv (smoothArcEquiv D)
    (fun e => turn (smoothCrossing D c) (smoothArcEquiv D e))
    (fun e => turn (smoothCrossing D c) e) (fun _ => rfl)]
  exact Fintype.sum_sum_type _

theorem continuation_code_old_nonincoming (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : Fin D.nArc) (h0 : e ≠ D.incoming c 0) (h1 : e ≠ D.incoming c 1) :
    smoothContinuationGeometryCode D c (Sum.inl e) = Sum.inl (D.continuation e) := by
  have hout (j : Fin 2) : D.continuation e ≠ D.outgoing c j := by
    intro heq
    have hj : D.continuation (D.incoming c ((D.through c).symm j)) = D.outgoing c j := by
      rw [D.continuation_crossing, Equiv.apply_symm_apply]
    have hi := D.continuation.injective (heq.trans hj.symm)
    have hc : (D.through c).symm j = 0 ∨ (D.through c).symm j = 1 := by omega
    rcases hc with hc | hc
    · exact h0 (hc ▸ hi)
    · exact h1 (hc ▸ hi)
  by_cases ht : D.through c 0 = 0 <;>
    simp [smoothContinuationGeometryCode, smoothContinuationGeometryAdjust,
      smoothContinuationCodeLocal, smoothContinuationAdjustLocal, ht,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def, hout]

theorem arcVector_incoming (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    arcVector D (D.incoming c i) = crossingVector D c i := by
  simp [arcVector, crossingVector, strandTangent, D.incoming_target]

theorem crossingVector_through_scale (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) :
    crossingVector D c i = (outgoingTangentScale D c i : ℂ) *
      arcVector D (D.outgoing c (D.through c i)) := by
  apply Complex.ext
  · have h := congrArg Prod.fst (outgoingTangentScale_spec D c i)
    simpa [crossingVector, arcVector, smoothingCenter, D.outgoing_source] using h
  · have h := congrArg Prod.snd (outgoingTangentScale_spec D c i)
    simpa [crossingVector, arcVector, smoothingCenter, D.outgoing_source] using h

theorem turn_incoming_zero (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    turn D (D.incoming c i) = 0 := by
  rw [turn, D.continuation_crossing, arcVector_incoming, crossingVector_through_scale]
  have h := turn_positive_rescale (arcVector D (D.outgoing c (D.through c i)))
    (arcVector D (D.outgoing c (D.through c i))) 1 (outgoingTangentScale D c i)
    (by norm_num) (outgoingTangentScale_pos D c i)
  simpa [arcVector_ne_zero D _] using h

theorem turn_smooth_old_nonincoming (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hscale : ∀ e : Fin D.nArc, ∃ a : ℝ, 0 < a ∧
      arcVector (smoothCrossing D c) (smoothArcEquiv D (Sum.inl e)) =
        (a : ℂ) * arcVector D e)
    (e : Fin D.nArc) (h0 : e ≠ D.incoming c 0) (h1 : e ≠ D.incoming c 1) :
    turn (smoothCrossing D c) (smoothArcEquiv D (Sum.inl e)) = turn D e := by
  rw [turn, continuation_smooth_code, continuation_code_old_nonincoming D c e h0 h1]
  obtain ⟨a, ha, hva⟩ := hscale (D.continuation e)
  obtain ⟨b, hb, hvb⟩ := hscale e
  rw [hva, hvb]
  exact turn_positive_rescale _ _ a b ha hb

theorem turn_smooth_incoming (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hscale : ∀ e : Fin D.nArc, ∃ a : ℝ, 0 < a ∧
      arcVector (smoothCrossing D c) (smoothArcEquiv D (Sum.inl e)) =
        (a : ℂ) * arcVector D e) (i : Fin 2) :
    turn (smoothCrossing D c) (smoothArcEquiv D (Sum.inl (D.incoming c i))) =
      Complex.arg ((crossingVector D c 0 + crossingVector D c 1) / crossingVector D c i) := by
  have hcont : smoothContinuationGeometryCode D c (Sum.inl (D.incoming c i)) = Sum.inr i := by
    fin_cases i
    · exact smoothContinuationGeometryCode_incoming_zero D c
    · exact smoothContinuationGeometryCode_incoming_one D c
  rw [turn, continuation_smooth_code, hcont, arcVector_smooth_connector]
  obtain ⟨a, ha, hva⟩ := hscale (D.incoming c i)
  rw [hva, arcVector_incoming]
  exact turn_positive_rescale _ _ (smoothEpsilon D c) a (smoothEpsilon_pos D c) ha

theorem turn_smooth_connector (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hscale : ∀ e : Fin D.nArc, ∃ a : ℝ, 0 < a ∧
      arcVector (smoothCrossing D c) (smoothArcEquiv D (Sum.inl e)) =
        (a : ℂ) * arcVector D e) (i : Fin 2) :
    turn (smoothCrossing D c) (smoothArcEquiv D (Sum.inr i)) =
      Complex.arg (crossingVector D c (otherBranch i) /
        (crossingVector D c 0 + crossingVector D c 1)) := by
  rw [turn, continuation_smooth_code, smoothContinuationGeometryCode_connector,
    arcVector_smooth_connector]
  obtain ⟨a, ha, hva⟩ := hscale (D.outgoing c (D.through c (otherBranch i)))
  rw [hva, turn_positive_rescale _ _ a (smoothEpsilon D c) ha (smoothEpsilon_pos D c)]
  rw [crossingVector_through_scale D c (otherBranch i)]
  have h := turn_positive_rescale (crossingVector D c 0 + crossingVector D c 1)
    (arcVector D (D.outgoing c (D.through c (otherBranch i))))
    (outgoingTangentScale D c (otherBranch i)) 1
    (outgoingTangentScale_pos D c (otherBranch i)) (by norm_num)
  simpa using h.symm

private theorem sum_change_two {n : ℕ} (f g : Fin n → ℝ) (i j : Fin n)
    (hij : i ≠ j) (hi : g i = 0) (hj : g j = 0)
    (hrest : ∀ e, e ≠ i → e ≠ j → f e = g e) :
    (∑ e, f e) = (∑ e, g e) + f i + f j := by
  classical
  have hs : (∑ e, (f e - g e)) = (f i - g i) + (f j - g j) := by
    calc
      (∑ e, (f e - g e)) = ∑ e ∈ ({i, j} : Finset (Fin n)), (f e - g e) := by
        symm
        apply Finset.sum_subset (by simp)
        intro e he hn
        have hne : e ≠ i ∧ e ≠ j := by simpa using hn
        rw [hrest e hne.1 hne.2, sub_self]
      _ = (f i - g i) + (f j - g j) := by simp [hij]; ring
  rw [Finset.sum_sub_distrib, hi, hj] at hs
  linarith

/-- Intermediate composition: its vector premise will be discharged by the
actual cutoff geometry lemma; it is not a new premise of smoothing invariance. -/
theorem totalTurn_smooth_of_positive_old_vectors (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hscale : ∀ e : Fin D.nArc, ∃ a : ℝ, 0 < a ∧
      arcVector (smoothCrossing D c) (smoothArcEquiv D (Sum.inl e)) =
        (a : ℂ) * arcVector D e) :
    totalTurn (smoothCrossing D c) = totalTurn D := by
  rw [totalTurn_smooth_reindex]
  have hs := sum_change_two
    (fun e => turn (smoothCrossing D c) (smoothArcEquiv D (Sum.inl e)))
    (turn D) (D.incoming c 0) (D.incoming c 1) (D.four_ports_distinct c).1
    (turn_incoming_zero D c 0) (turn_incoming_zero D c 1)
    (fun e h0 h1 => turn_smooth_old_nonincoming D c hscale e h0 h1)
  simp only [] at hs
  rw [hs, turn_smooth_incoming D c hscale 0, turn_smooth_incoming D c hscale 1]
  simp only [Fin.sum_univ_two, turn_smooth_connector D c hscale,
    otherBranch_zero, otherBranch_one]
  have hcancel := four_smoothing_bends_cancel (crossingVector D c 0) (crossingVector D c 1)
    (D.crossing_transverse c)
  change _ = ∑ e, turn D e
  linarith

/-- Actual corrected smoothing preserves the finite total principal turn. -/
theorem totalTurn_smoothCrossing (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    totalTurn (smoothCrossing D c) = totalTurn D :=
  totalTurn_smooth_of_positive_old_vectors D c (smoothCrossing_old_arcVector_positive D c)

/-- Actual corrected smoothing preserves the uniquely constructed turning integer.
Identification with source rotation of a rounding remains a separate theorem. -/
theorem turnInteger_smoothCrossing (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    turnInteger (smoothCrossing D c) = turnInteger D := by
  apply turnInteger_unique
  rw [totalTurn_smoothCrossing]
  exact totalTurn_eq_turnInteger D

end DirectGLSSW.HOMFLY.PrincipalTurning




























