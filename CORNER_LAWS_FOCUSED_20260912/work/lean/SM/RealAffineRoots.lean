import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Exact roots and multiplicities of real affine polynomials. These lemmas
include the zero-slope cases allowed by the no-common-root determinant test. -/

namespace SM

open Polynomial

noncomputable section

def realAffinePolynomial (a b : ℝ) : ℝ[X] := C a * X + C b

@[simp] theorem realAffinePolynomial_eval (a b t : ℝ) :
    (realAffinePolynomial a b).eval t = a * t + b := by
  simp [realAffinePolynomial]

theorem realAffinePolynomial_root_iff (a b : ℝ) (ha : a ≠ 0) (t : ℝ) :
    (realAffinePolynomial a b).IsRoot t ↔ t = -b / a := by
  rw [IsRoot, realAffinePolynomial_eval, ← eq_neg_iff_add_eq_zero, eq_div_iff ha]
  rw [mul_comm a t]

theorem realAffinePolynomial_simple_root (a b : ℝ) (ha : a ≠ 0) :
    (realAffinePolynomial a b).rootMultiplicity (-b / a) = 1 := by
  have hc : a * (-b / a) = -b := by field_simp
  have he : realAffinePolynomial a b = C a * (X - C (-b / a)) := by
    rw [mul_sub, ← C_mul, hc, C_neg, sub_neg_eq_add]
    rfl
  rw [he, rootMultiplicity_mul (mul_ne_zero (by simpa using ha) (X_sub_C_ne_zero _)),
    rootMultiplicity_C, rootMultiplicity_X_sub_C_self]

theorem realAffinePolynomial_no_common_root (a b c d : ℝ) (h : a * d - b * c ≠ 0) (t : ℝ) :
    ¬ ((realAffinePolynomial a b).IsRoot t ∧ (realAffinePolynomial c d).IsRoot t) := by
  rintro ⟨hp, hq⟩
  simp only [IsRoot, realAffinePolynomial_eval] at hp hq
  apply h
  linear_combination a * hq - c * hp

end

end SM
