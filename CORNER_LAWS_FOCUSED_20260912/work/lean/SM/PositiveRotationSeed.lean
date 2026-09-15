import SM.CyclicComplexSeed

/-! The source's regular seed for every positive integer rotation, constructed
from the actual complex exponential at angle 2*pi*k/(2*k+1). -/

namespace SM

noncomputable def positiveSeedAngle (k : ℕ) : ℝ :=
  2 * Real.pi * (k : ℝ) / (2 * (k : ℝ) + 1)

noncomputable def positiveSeedRatio (k : ℕ) : ℂ :=
  Complex.exp ((positiveSeedAngle k : ℂ) * Complex.I)

theorem positiveSeedAngle_pos {k : ℕ} (hk : 0 < k) : 0 < positiveSeedAngle k := by
  unfold positiveSeedAngle
  positivity

theorem positiveSeedAngle_lt_pi (k : ℕ) : positiveSeedAngle k < Real.pi := by
  have hd : 0 < 2 * (k : ℝ) + 1 := by positivity
  rw [positiveSeedAngle, div_lt_iff₀ hd]
  nlinarith [Real.pi_pos]

theorem positiveSeedAngle_count (k : ℕ) :
    ((2 * k + 1 : ℕ) : ℝ) * positiveSeedAngle k = 2 * Real.pi * (k : ℝ) := by
  have hd : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
  unfold positiveSeedAngle
  push_cast
  field_simp

theorem positiveSeedRatio_arg {k : ℕ} (hk : 0 < k) :
    (positiveSeedRatio k).arg = positiveSeedAngle k := by
  rw [positiveSeedRatio, Complex.arg_exp_mul_I]
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  exact ⟨by linarith [positiveSeedAngle_pos hk, Real.pi_pos],
    by linarith [positiveSeedAngle_lt_pi k]⟩

theorem positiveSeedRatio_ne_zero (k : ℕ) : positiveSeedRatio k ≠ 0 :=
  Complex.exp_ne_zero _

theorem positiveSeedRatio_ne_one {k : ℕ} (hk : 0 < k) : positiveSeedRatio k ≠ 1 := by
  intro he
  have ha := positiveSeedRatio_arg hk
  rw [he, Complex.arg_one] at ha
  exact (positiveSeedAngle_pos hk).ne' ha.symm

theorem positiveSeedRatio_pow (k : ℕ) : positiveSeedRatio k ^ (2 * k + 1) = 1 := by
  unfold positiveSeedRatio
  rw [← Complex.exp_nat_mul]
  have hx : ((2 * k + 1 : ℕ) : ℂ) * ((positiveSeedAngle k : ℂ) * Complex.I) =
      (k : ℂ) * (2 * Real.pi * Complex.I) := by
    calc
      _ = ((((2 * k + 1 : ℕ) : ℝ) * positiveSeedAngle k : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      _ = (k : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [positiveSeedAngle_count]
        push_cast
        ring
  rw [hx, Complex.exp_nat_mul_two_pi_mul_I]

noncomputable def positiveRotationSeed (k : ℕ) : LabelledTuple (2 * k + 1) :=
  cyclicComplexSeed (positiveSeedRatio k)

theorem positiveRotationSeed_regular {k : ℕ} (hk : 0 < k) :
    Regular (positiveRotationSeed k) := by
  apply cyclicComplexSeed_regular (by omega) (positiveSeedRatio_pow k)
    (positiveSeedRatio_ne_zero k) (positiveSeedRatio_ne_one hk)
  rw [positiveSeedRatio_arg hk]
  exact (positiveSeedAngle_lt_pi k).ne

theorem positiveRotationSeed_rotation {k : ℕ} (hk : 0 < k) :
    rotationNumber (positiveRotationSeed k) = (k : ℝ) := by
  unfold positiveRotationSeed
  rw [cyclicComplexSeed_rotation (by omega) (positiveSeedRatio_pow k)
    (positiveSeedRatio_ne_zero k) (positiveSeedRatio_ne_one hk),
    positiveSeedRatio_arg hk, positiveSeedAngle_count]
  have hp : 2 * Real.pi ≠ 0 := by positivity
  exact mul_div_cancel_left₀ _ hp

end SM
