import SM.DeterminantPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Exact variable and degree facts for the primitive-linear proof of the
three-line determinant. No genericity or irreducibility oracle is assumed. -/

namespace SM

open MvPolynomial

variable {σ : Type*} {p q : MvPolynomial σ ℝ} {i : σ}

theorem polynomial_not_mem_add (hp : i ∉ p.vars) (hq : i ∉ q.vars) :
    i ∉ (p + q).vars := by
  classical
  intro h
  exact (Finset.mem_union.mp (vars_add_subset p q h)).elim hp hq

theorem polynomial_not_mem_mul (hp : i ∉ p.vars) (hq : i ∉ q.vars) :
    i ∉ (p * q).vars := by
  classical
  intro h
  exact (Finset.mem_union.mp (vars_mul p q h)).elim hp hq

theorem polynomial_not_mem_neg (hp : i ∉ p.vars) : i ∉ (-p).vars := by
  have he : (-p).vars = p.vars := by
    rw [show -p = C (-1) * p by simp, vars_C_mul (-1) (by norm_num)]
  rwa [he]

theorem polynomial_not_mem_sub (hp : i ∉ p.vars) (hq : i ∉ q.vars) :
    i ∉ (p - q).vars := by
  simpa only [sub_eq_add_neg] using polynomial_not_mem_add hp (polynomial_not_mem_neg hq)

theorem polynomial_degree_zero (hp : i ∉ p.vars) : p.degreeOf i = 0 := by
  simpa only [mem_vars_iff_degreeOf_ne_zero, not_not] using hp

theorem polynomial_linear_degree (hp : p ≠ 0) (hip : i ∉ p.vars) (hiq : i ∉ q.vars) :
    (p * X i + q).degreeOf i = 1 := by
  have hd : (p * X i).degreeOf i = 1 := by
    simpa only [polynomial_degree_zero hip, zero_add] using
      (degreeOf_mul_X_eq_degreeOf_add_one_iff i p).mpr hp
  have hlt : q.degreeOf i < (p * X i).degreeOf i := by
    rw [polynomial_degree_zero hiq, hd]
    exact Nat.zero_lt_one
  exact (degreeOf_add_eq_of_degreeOf_lt hlt).trans hd

theorem polynomial_linear_sub_degree (hp : p ≠ 0) (hip : i ∉ p.vars) (hiq : i ∉ q.vars) :
    (p * X i - q).degreeOf i = 1 := by
  simpa only [sub_eq_add_neg] using
    polynomial_linear_degree hp hip (polynomial_not_mem_neg hiq)

theorem polynomial_not_dvd_of_degree_lt (hq : q ≠ 0) (hdeg : q.degreeOf i < p.degreeOf i) :
    ¬ p ∣ q := by
  rintro ⟨r, hr⟩
  have hpr : p * r ≠ 0 := by rwa [← hr]
  have hp : p ≠ 0 := (mul_ne_zero_iff.mp hpr).1
  have hr0 : r ≠ 0 := (mul_ne_zero_iff.mp hpr).2
  have hd : q.degreeOf i = p.degreeOf i + r.degreeOf i := by
    rw [hr, degreeOf_mul_eq hp hr0]
  omega

theorem polynomial_isRelPrime_neg_right (h : IsRelPrime p q) : IsRelPrime p (-q) := by
  intro d hd hq
  exact h hd (by simpa only [dvd_neg] using hq)

theorem polynomial_linear_sub_irreducible (hp : p ≠ 0)
    (hip : i ∉ p.vars) (hiq : i ∉ q.vars) (hcop : IsRelPrime p q) :
    Irreducible (p * X i - q) := by
  simpa only [sub_eq_add_neg] using irreducible_mul_X_add p (-q) i hp hip
    (polynomial_not_mem_neg hiq) (polynomial_isRelPrime_neg_right hcop)

end SM
