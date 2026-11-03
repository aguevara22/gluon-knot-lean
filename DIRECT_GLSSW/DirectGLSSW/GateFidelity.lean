import DirectGLSSW.Gates

/-!
# The original Heaviside gates on nonzero sign inputs

Source: `ep:linear-gates`. The existing gate definitions are rational half-sums.
These equalities connect them to the actual step-function expressions in the
manuscript. Their arguments are products of two signs, hence never zero; the
chosen total extension of `positiveStep` at zero is not a source convention.
No assertion about geometric determinant realization is made in this module.
-/

namespace DirectGLSSW

/-- The positive-input indicator. Only nonzero sign products are used below. -/
def positiveStep (x : ℚ) : ℚ := if 0 < x then 1 else 0

/-- The manuscript's ordinary Heaviside gate equals its rational half-difference. -/
theorem ordinaryGate_heaviside (d h : Sign) :
    d.value * positiveStep (-(h.value * d.value)) = ordinaryGate d h := by
  cases d <;> cases h <;> norm_num [positiveStep, ordinaryGate, Sign.value]

/-- The manuscript's marked Heaviside gate equals its rational half-sum. -/
theorem markedGate_heaviside (d h : Sign) :
    d.value * positiveStep (h.value * d.value) = markedGate d h := by
  cases d <;> cases h <;> norm_num [positiveStep, markedGate, Sign.value]

end DirectGLSSW
