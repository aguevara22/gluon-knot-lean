import SM.Reversal
import SM.Segment

/-! The unrestricted reversal count reads original right turns. The formula
n-leftTurns requires an explicit nonzero-turn hypothesis, missing from the
literal source lem:shift(iii). This module does not accept that source row. -/

namespace SM

variable {n : ℕ} [NeZero n]

noncomputable def rightTurns (P : LabelledTuple n) : ℕ :=
  (Finset.univ.filter (fun i => turn P i = -1)).card

theorem sign_neg_eq_one (s : SignType) : -s = 1 ↔ s = -1 := by
  cases s <;> decide

theorem sign_right_iff_not_left (s : SignType) (hs : s ≠ 0) : s = -1 ↔ ¬s = 1 := by
  cases s <;> simp_all

theorem leftTurns_reversal_eq_right (P : LabelledTuple n) :
    leftTurns (reversal P) = rightTurns P := by
  classical
  unfold leftTurns rightTurns
  apply Finset.card_bij (fun i _ => 2 - i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      turn_reversal, sign_neg_eq_one] using hi
  · intro i _ j _ hij
    exact (Equiv.subLeft (2 : ZMod n)).injective hij
  · intro j hj
    refine ⟨2 - j, ?_, by simp⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      turn_reversal, sub_sub_cancel, sign_neg_eq_one] using hj

theorem leftTurns_add_rightTurns (P : LabelledTuple n) (h : ∀ i, turn P i ≠ 0) :
    leftTurns P + rightTurns P = n := by
  classical
  have hf : Finset.univ.filter (fun i : ZMod n => ¬turn P i = 1) =
      Finset.univ.filter (fun i => turn P i = -1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (sign_right_iff_not_left (turn P i) (h i)).symm
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : ZMod n => turn P i = 1)
  rw [hf] at hc
  simpa only [leftTurns, rightTurns, Finset.card_univ, ZMod.card] using hc

theorem leftTurns_reversal_of_nonzero (P : LabelledTuple n) (h : ∀ i, turn P i ≠ 0) :
    leftTurns (reversal P) = n - leftTurns P := by
  rw [leftTurns_reversal_eq_right]
  have hc := leftTurns_add_rightTurns P h
  omega

theorem leftTurns_reversal_of_generic (hn : 3 ≤ n) {P : LabelledTuple n} (h : Generic P) :
    leftTurns (reversal P) = n - leftTurns P := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  apply leftTurns_reversal_of_nonzero
  intro i
  rw [turn_det]
  exact sign_ne_zero.mpr (g1_turn_nonzero hn h.1 i)

end SM
