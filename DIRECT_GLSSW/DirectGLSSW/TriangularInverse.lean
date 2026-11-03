import Mathlib.Algebra.GeomSum
import Mathlib.Data.Matrix.Basic
import Lean.Elab.Tactic.Omega

/-!
# Finite inverses for strict upper triangular currents

The inverse is a finite geometric series, with no analytic convergence and
no use of a field-valued matrix inverse. Source: `ep:K` and `un:M`.
-/

namespace DirectGLSSW
open scoped BigOperators

def StrictUpper {R : Type*} [Zero R] {n : ℕ} (X : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, j.val ≤ i.val → X i j = 0

theorem strictUpper_pow_entry_zero {R : Type*} [Semiring R] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) R) (hX : StrictUpper X)
    (k : ℕ) (i j : Fin n) (hij : j.val < i.val + k) : (X ^ k) i j = 0 := by
  induction k generalizing i j with
  | zero =>
      have hne : i ≠ j := by
        intro h
        subst j
        omega
      simp [Matrix.one_apply, hne]
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : l.val < i.val + k
      · rw [ih i l hl, zero_mul]
      · have hlj : j.val ≤ l.val := by omega
        rw [hX l j hlj, mul_zero]

theorem strictUpper_nilpotent {R : Type*} [Semiring R] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) R) (hX : StrictUpper X) : X ^ n = 0 := by
  apply Matrix.ext
  intro i j
  apply strictUpper_pow_entry_zero X hX n i j
  have hj := j.isLt
  omega

def finiteInverse {R : Type*} [Ring R] (X : R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range n, (-X) ^ k

theorem finiteInverse_mul {R : Type*} [Ring R] (X : R) (n : ℕ)
    (hnil : X ^ n = 0) : finiteInverse X n * (1 + X) = 1 := by
  have hneg : (-X) ^ n = 0 := by rw [neg_pow, hnil, mul_zero]
  simpa only [finiteInverse, sub_neg_eq_add, hneg, sub_zero] using
    geom_sum_mul_neg (-X) n

theorem mul_finiteInverse {R : Type*} [Ring R] (X : R) (n : ℕ)
    (hnil : X ^ n = 0) : (1 + X) * finiteInverse X n = 1 := by
  have hneg : (-X) ^ n = 0 := by rw [neg_pow, hnil, mul_zero]
  simpa only [finiteInverse, sub_neg_eq_add, hneg, sub_zero] using
    mul_neg_geom_sum (-X) n

theorem strictUpper_finiteInverse {R : Type*} [Ring R] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) R) (hX : StrictUpper X) :
    finiteInverse X n * (1 + X) = 1 ∧ (1 + X) * finiteInverse X n = 1 := by
  exact ⟨finiteInverse_mul X n (strictUpper_nilpotent X hX),
    mul_finiteInverse X n (strictUpper_nilpotent X hX)⟩

end DirectGLSSW
