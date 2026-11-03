import DirectGLSSW.TriangularInverse
import DirectGLSSW.CapAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DirectGLSSW

open scoped BigOperators

def capMatrix {n : ℕ} (P : Fin n → Fin n → ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun c d => if c.val < d.val then P c d else 0

theorem capMatrix_strictUpper {n : ℕ} (P : Fin n → Fin n → ℚ) :
    StrictUpper (capMatrix P) := by
  intro c d hdc
  simp [capMatrix, not_lt_of_ge hdc]

theorem strictUpperMulCapAssembly {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℚ)
    (hA : StrictUpper A) (hB : StrictUpper B) : StrictUpper (A * B) := by
  intro i j hji
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hki : k.val ≤ i.val
  · rw [hA i k hki, zero_mul]
  · have hjk : j.val ≤ k.val := by omega
    rw [hB k j hjk, mul_zero]

theorem capMatrixRelationOfUpperEntries
    {n : ℕ} (s : Fin n → ℚ) (P : Fin n → Fin n → ℚ)
    (hentry : ∀ c d : Fin n, c.val < d.val →
      (s c + s d) * P c d +
        2 * ∑ e ∈ Finset.univ.filter
          (fun e : Fin n => c.val < e.val ∧ e.val < d.val),
          s e * P c e * P e d = 0) :
    Matrix.diagonal s * capMatrix P + capMatrix P * Matrix.diagonal s +
      (capMatrix P * Matrix.diagonal s * capMatrix P +
       capMatrix P * Matrix.diagonal s * capMatrix P) = 0 := by
  classical
  let X := capMatrix P
  let S := Matrix.diagonal s
  have hX : StrictUpper X := capMatrix_strictUpper P
  have hSX : StrictUpper (S * X) := by
    intro i j hji
    rw [Matrix.diagonal_mul, hX i j hji, mul_zero]
  have hXS : StrictUpper (X * S) := by
    intro i j hji
    rw [Matrix.mul_diagonal, hX i j hji, zero_mul]
  have hXSX : StrictUpper (X * S * X) := strictUpperMulCapAssembly (X * S) X hXS hX
  apply Matrix.ext
  intro c d
  by_cases hcd : c.val < d.val
  · have hSXentry : (S * X) c d = s c * P c d := by
      simp [S, X, Matrix.diagonal_mul, capMatrix, hcd]
    have hXSentry : (X * S) c d = P c d * s d := by
      simp [S, X, Matrix.mul_diagonal, capMatrix, hcd]
    have hquad : (X * S * X) c d =
        ∑ e ∈ Finset.univ.filter
          (fun e : Fin n => c.val < e.val ∧ e.val < d.val),
          P c e * s e * P e d := by
      rw [Matrix.mul_apply]
      calc
        (∑ e, (X * S) c e * X e d) =
            ∑ e, (X c e * s e) * X e d := by
              apply Finset.sum_congr rfl
              intro e he
              rw [Matrix.mul_diagonal]
        _ = ∑ e, if c.val < e.val ∧ e.val < d.val then
              P c e * s e * P e d else 0 := by
              apply Finset.sum_congr rfl
              intro e he
              by_cases hce : c.val < e.val
              · by_cases hed : e.val < d.val
                · simp [X, capMatrix, hce, hed]
                · simp [X, capMatrix, hce, hed]
              · simp [X, capMatrix, hce]
        _ = ∑ e ∈ Finset.univ.filter
              (fun e : Fin n => c.val < e.val ∧ e.val < d.val),
              P c e * s e * P e d := by
              rw [Finset.sum_filter]
    have hsum :
        (∑ e ∈ Finset.univ.filter
          (fun e : Fin n => c.val < e.val ∧ e.val < d.val),
          s e * P c e * P e d) =
        ∑ e ∈ Finset.univ.filter
          (fun e : Fin n => c.val < e.val ∧ e.val < d.val),
          P c e * s e * P e d := by
      apply Finset.sum_congr rfl
      intro e he
      ring
    have h := hentry c d hcd
    change (S * X + X * S + (X * S * X + X * S * X)) c d = 0
    simp only [Matrix.add_apply]
    rw [hSXentry, hXSentry, hquad]
    calc
      s c * P c d + P c d * s d +
          (∑ e ∈ Finset.univ.filter
            (fun e : Fin n => c.val < e.val ∧ e.val < d.val),
            P c e * s e * P e d +
           ∑ e ∈ Finset.univ.filter
            (fun e : Fin n => c.val < e.val ∧ e.val < d.val),
            P c e * s e * P e d) =
          (s c + s d) * P c d + 2 *
            ∑ e ∈ Finset.univ.filter
              (fun e : Fin n => c.val < e.val ∧ e.val < d.val),
              s e * P c e * P e d := by rw [← hsum]; ring
      _ = 0 := h
  · have htotal : StrictUpper (S * X + X * S + (X * S * X + X * S * X)) := by
      intro i j hji
      simp only [Matrix.add_apply]
      rw [hSX i j hji, hXS i j hji, hXSX i j hji]
      simp
    simpa only [Matrix.add_apply] using htotal c d (le_of_not_gt hcd)

theorem capMatrixFiniteInverseIdentity
    {n : ℕ} (s : Fin n → ℚ) (P : Fin n → Fin n → ℚ)
    (hentry : ∀ c d : Fin n, c.val < d.val →
      (s c + s d) * P c d +
        2 * ∑ e ∈ Finset.univ.filter
          (fun e : Fin n => c.val < e.val ∧ e.val < d.val),
          s e * P c e * P e d = 0) :
    finiteInverse (capMatrix P) n * Matrix.diagonal s +
      Matrix.diagonal s * finiteInverse (capMatrix P) n =
      Matrix.diagonal s + Matrix.diagonal s := by
  let X := capMatrix P
  let S := Matrix.diagonal s
  have hX : StrictUpper X := capMatrix_strictUpper P
  have hcap : S * X + X * S + (X * S * X + X * S * X) = 0 := by
    exact capMatrixRelationOfUpperEntries s P hentry
  obtain ⟨hleft, hright⟩ := strictUpper_finiteInverse X hX
  exact cap_inverse_identity X S (finiteInverse X n) hcap hleft hright






end DirectGLSSW
