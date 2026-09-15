import SM.ZeroRotationSeed
import SM.PositiveRotationSeed

/-! Sufficiency for all integer rotations, with the actual seed construction,
reversal, repeated subdivision and proved generic perturbation. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem exists_generic_of_admissible {r : ℤ} (ha : Admissible (n : ℤ) r) :
    ∃ P : LabelledTuple n, Generic P ∧ rotationNumber P = (r : ℝ) := by
  have hn : 3 ≤ n := by exact_mod_cast ha.1
  cases r with
  | ofNat k =>
    by_cases hk : k = 0
    · subst k
      have hne : n ≠ 3 := by
        intro he
        apply ha.2.2
        simp [he]
      simpa using exists_generic_rotation_zero (by omega : 4 ≤ n)
    · have hkp : 0 < k := Nat.pos_of_ne_zero hk
      have hbZ : 2 * (k : ℤ) < (n : ℤ) := by simpa using ha.2.1
      have hb : 2 * k < n := by exact_mod_cast hbZ
      obtain ⟨P, hP, hr⟩ := exists_generic_at_larger_size hn
        (positiveRotationSeed_regular hkp) (by omega : 2 * k + 1 ≤ n)
      refine ⟨P, hP, ?_⟩
      simpa using hr.trans (positiveRotationSeed_rotation hkp)
  | negSucc k =>
    have hab : |Int.negSucc k| = ((k + 1 : ℕ) : ℤ) := by
      rw [abs_of_neg (show Int.negSucc k < 0 by omega)]
      simp [Int.negSucc_eq]
    have hbZ : 2 * ((k + 1 : ℕ) : ℤ) < (n : ℤ) := by simpa only [hab] using ha.2.1
    have hb : 2 * (k + 1) < n := by exact_mod_cast hbZ
    have hreg := regular_reversal_forward (positiveRotationSeed_regular (Nat.succ_pos k))
    obtain ⟨P, hP, hr⟩ := exists_generic_at_larger_size hn hreg
      (by omega : 2 * (k + 1) + 1 ≤ n)
    refine ⟨P, hP, ?_⟩
    rw [hr, rotationNumber_reversal (positiveRotationSeed_regular (Nat.succ_pos k)),
      positiveRotationSeed_rotation (Nat.succ_pos k)]
    simp

theorem generic_rotation_exists_iff (hn : 3 ≤ n) (r : ℤ) :
    (∃ P : LabelledTuple n, Generic P ∧ rotationNumber P = (r : ℝ)) ↔
      Admissible (n : ℤ) r := by
  constructor
  · rintro ⟨P, hP, hr⟩
    exact generic_rotation_admissible hn hP r hr
  · exact exists_generic_of_admissible

end SM
