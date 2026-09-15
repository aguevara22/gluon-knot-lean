import SM.NarrowSector
import SM.RotationReversal

/-! Every clause of lem:uniformrot. The hard positive case is derived from
actual edge closure in NarrowSector. Cyclic shifts move the exceptional turn,
and actual traversal reversal proves both negative cases. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem principalTurn_sign {P : LabelledTuple n} (h : Regular P) (i : ZMod n) :
    SignType.sign (principalTurn P i) = turn P i := by
  rw [turn_det]
  exact principalAngle_sign (h i)

theorem principalTurn_pos_of_left {P : LabelledTuple n} (h : Regular P) {i : ZMod n}
    (hi : turn P i = 1) : 0 < principalTurn P i :=
  sign_eq_one_iff.mp ((principalTurn_sign h i).trans hi)

theorem rotationNumber_ge_one_of_pos {P : LabelledTuple n} (h : Regular P)
    (hp : 0 < rotationNumber P) : 1 ≤ rotationNumber P := by
  obtain ⟨k, hk⟩ := rotationNumber_integer h
  rw [hk] at hp ⊢
  have hkpos : (0 : ℤ) < k := by exact_mod_cast hp
  have hkone : (1 : ℤ) ≤ k := by omega
  exact_mod_cast hkone

theorem rotationNumber_ge_one_of_other_left_zero {P : LabelledTuple n} (h : Regular P)
    (hp : ∀ i : ZMod n, i ≠ 0 → turn P i = 1) : 1 ≤ rotationNumber P :=
  rotationNumber_ge_one_of_pos h (rotationNumber_pos_of_other_principalTurns_pos h
    (fun i hi => principalTurn_pos_of_left h (hp i hi)))

theorem rotationNumber_ge_one_of_other_left {P : LabelledTuple n} (h : Regular P) (a : ZMod n)
    (hp : ∀ i : ZMod n, i ≠ a → turn P i = 1) : 1 ≤ rotationNumber P := by
  have hs : Regular (shift a P) := (regular_shift a P).mpr h
  have ht : ∀ i : ZMod n, i ≠ 0 → turn (shift a P) i = 1 := by
    intro i hi
    rw [turn_shift]
    apply hp
    intro he
    apply hi
    have he' : i + a = 0 + a := by simpa only [zero_add] using he
    exact add_right_cancel he'
  simpa only [rotationNumber_shift] using rotationNumber_ge_one_of_other_left_zero hs ht

theorem rotationNumber_le_neg_one_of_other_right {P : LabelledTuple n} (h : Regular P) (a : ZMod n)
    (hp : ∀ i : ZMod n, i ≠ a → turn P i = -1) : rotationNumber P ≤ -1 := by
  have hr : Regular (reversal P) := regular_reversal_forward h
  have ht : ∀ i : ZMod n, i ≠ 2 - a → turn (reversal P) i = 1 := by
    intro i hi
    have he : 2 - i ≠ a := by
      intro heq
      apply hi
      calc
        i = 2 - (2 - i) := by ring
        _ = 2 - a := by rw [heq]
    rw [turn_reversal, hp (2 - i) he]
    simp
  have hb := rotationNumber_ge_one_of_other_left hr (2 - a) ht
  rw [rotationNumber_reversal h] at hb
  linarith

theorem uniform_rotation (hn : 3 ≤ n) (P : LabelledTuple n) (h : Regular P)
    (hτ : ∀ i : ZMod n, turn P i ≠ 0) :
    ((∀ i : ZMod n, turn P i = 1) → 1 ≤ rotationNumber P) ∧
    ((∀ i : ZMod n, turn P i = -1) → rotationNumber P ≤ -1) ∧
    ((∃ a : ZMod n, turn P a = -1 ∧ ∀ i : ZMod n, i ≠ a → turn P i = 1) →
      1 ≤ rotationNumber P) ∧
    ((∃ a : ZMod n, turn P a = 1 ∧ ∀ i : ZMod n, i ≠ a → turn P i = -1) →
      rotationNumber P ≤ -1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hp
    exact rotationNumber_ge_one_of_other_left h 0 (fun i _ => hp i)
  · intro hp
    exact rotationNumber_le_neg_one_of_other_right h 0 (fun i _ => hp i)
  · rintro ⟨a, _, hp⟩
    exact rotationNumber_ge_one_of_other_left h a hp
  · rintro ⟨a, _, hp⟩
    exact rotationNumber_le_neg_one_of_other_right h a hp

end SM
