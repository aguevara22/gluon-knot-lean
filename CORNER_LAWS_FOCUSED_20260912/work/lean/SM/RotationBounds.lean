import SM.RotationNumber

/-! The strict absolute-value bound from the source principal-angle interval.
This is clause (v) of lem:rot; the full lemma is still tracked separately. -/

namespace SM

variable {n : ℕ}

theorem principalTurn_abs_lt_pi {P : LabelledTuple n} (h : Regular P) (i : ZMod n) :
    |principalTurn P i| < Real.pi := by
  exact abs_lt.mpr (principalAngle_bounds (h i))

theorem sum_abs_principalTurn_lt [NeZero n] {P : LabelledTuple n} (h : Regular P) :
    (∑ i : ZMod n, |principalTurn P i|) < (n : ℝ) * Real.pi := by
  have hs : (∑ i : ZMod n, |principalTurn P i|) < ∑ _i : ZMod n, Real.pi :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => principalTurn_abs_lt_pi h i)
  simpa using hs

theorem rotationNumber_strict_bound [NeZero n] {P : LabelledTuple n} (h : Regular P) :
    2 * |rotationNumber P| < (n : ℝ) := by
  have hs : |∑ i : ZMod n, principalTurn P i| < (n : ℝ) * Real.pi :=
    (Finset.abs_sum_le_sum_abs _ _).trans_lt (sum_abs_principalTurn_lt h)
  have he : 2 * |rotationNumber P| = |∑ i : ZMod n, principalTurn P i| / Real.pi := by
    rw [rotationNumber, abs_div, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    field_simp
  rw [he]
  exact (div_lt_iff₀ Real.pi_pos).mpr hs

end SM
