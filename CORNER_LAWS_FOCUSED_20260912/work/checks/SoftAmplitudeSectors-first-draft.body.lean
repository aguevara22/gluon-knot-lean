namespace SM.SoftDuplication

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The printed soft multiplier is computed in the rationals after casting both
attachment signs through the integers; no integer division is used. -/
def softAmplitudeMultiplier (P : LabelledTuple n) (j : ZMod n) (q : Plane) : ℚ :=
  ((((softAttachmentMinus P j q : SignType) : ℤ) : ℚ) +
    (((softAttachmentPlus P j q : SignType) : ℤ) : ℚ)) / 2

/-- In the source same-sign sector, both attachment signs equal the negative turn. -/
theorem softAmplitudeMultiplier_same_sign (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (hsector : softAttachmentMinus P j q = -turn P j ∧
      softAttachmentPlus P j q = -turn P j) :
    softAmplitudeMultiplier P j q = -(((turn P j : SignType) : ℤ) : ℚ) := by
  simp only [softAmplitudeMultiplier, hsector.1, hsector.2, SignType.coe_neg, Int.cast_neg]
  ring

/-- Distinct admissible attachment signs are the two opposite nonzero signs,
so their rational average is zero. Nonzeroness is derived from admissibility. -/
theorem softAmplitudeMultiplier_mixed (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (hq : SoftAdmissible P j q)
    (hsector : softAttachmentMinus P j q ≠ softAttachmentPlus P j q) :
    softAmplitudeMultiplier P j q = 0 := by
  have hn := softAttachment_signs_nonzero hq
  cases hm : softAttachmentMinus P j q <;>
    cases hp : softAttachmentPlus P j q <;>
    simp_all [softAmplitudeMultiplier]

/-- In the source loop sector, both attachment signs equal the turn. -/
theorem softAmplitudeMultiplier_loop (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (hsector : softAttachmentMinus P j q = turn P j ∧
      softAttachmentPlus P j q = turn P j) :
    softAmplitudeMultiplier P j q = (((turn P j : SignType) : ℤ) : ℚ) := by
  simp only [softAmplitudeMultiplier, hsector.1, hsector.2]
  ring

/-- Faithful rational casting gives the same-sign integer coefficient law. -/
theorem softAmplitude_integer_same_sign (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (hsector : softAttachmentMinus P j q = -turn P j ∧
      softAttachmentPlus P j q = -turn P j)
    (X Y : ℤ) (hXY : (X : ℚ) = softAmplitudeMultiplier P j q * (Y : ℚ)) :
    X = -(turn P j : ℤ) * Y := by
  rw [softAmplitudeMultiplier_same_sign P j q hsector] at hXY
  apply Int.cast_injective (α := ℚ)
  simpa only [Int.cast_mul, Int.cast_neg] using hXY

/-- The mixed sector gives a zero integer coefficient without any assumption on Y. -/
theorem softAmplitude_integer_mixed (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (hq : SoftAdmissible P j q)
    (hsector : softAttachmentMinus P j q ≠ softAttachmentPlus P j q)
    (X Y : ℤ) (hXY : (X : ℚ) = softAmplitudeMultiplier P j q * (Y : ℚ)) :
    X = 0 := by
  rw [softAmplitudeMultiplier_mixed P j q hq hsector, zero_mul] at hXY
  apply Int.cast_injective (α := ℚ)
  simpa only [Int.cast_zero] using hXY

/-- Faithful rational casting gives the loop-sector integer coefficient law. -/
theorem softAmplitude_integer_loop (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (hsector : softAttachmentMinus P j q = turn P j ∧
      softAttachmentPlus P j q = turn P j)
    (X Y : ℤ) (hXY : (X : ℚ) = softAmplitudeMultiplier P j q * (Y : ℚ)) :
    X = (turn P j : ℤ) * Y := by
  rw [softAmplitudeMultiplier_loop P j q hsector] at hXY
  apply Int.cast_injective (α := ℚ)
  simpa only [Int.cast_mul] using hXY

end
end SM.SoftDuplication
