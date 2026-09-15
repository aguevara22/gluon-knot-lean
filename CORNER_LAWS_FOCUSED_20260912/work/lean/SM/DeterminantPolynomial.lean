import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! The actual two-by-two determinant is irreducible in an arbitrary
coordinate ring containing its independent variables. Extra variables remain
in the ring throughout; no unused-variable extension is assumed. -/

namespace SM

open MvPolynomial

theorem determinantPolynomial_irreducible {σ : Type*} (a b c d : σ)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Irreducible (X a * X b - X c * X d : MvPolynomial σ ℝ) := by
  classical
  let g : MvPolynomial σ ℝ := C (-1) * (X c * X d)
  have ha : a ∉ g.vars := by
    dsimp only [g]
    rw [vars_C_mul (-1) (by norm_num)]
    intro hm
    have hh := vars_mul (X c : MvPolynomial σ ℝ) (X d) hm
    simp only [vars_X, Finset.mem_union, Finset.mem_singleton] at hh
    exact hh.elim hac had
  have hg : IsRelPrime (X b : MvPolynomial σ ℝ) g := by
    apply (X_prime (R := ℝ) (i := b)).irreducible.isRelPrime_iff_not_dvd.mpr
    simp only [g, map_neg, map_one, neg_one_mul, dvd_neg, X_dvd_mul_iff, X_dvd_X]
    exact not_or_intro hbc hbd
  have hi := irreducible_mul_X_add (X b : MvPolynomial σ ℝ) g a
    (X_ne_zero b) (by simpa only [vars_X, Finset.mem_singleton] using hab) ha hg
  simpa only [g, map_neg, map_one, neg_one_mul, ← sub_eq_add_neg, mul_comm (X b) (X a)] using hi

end SM
