import DirectGLSSW.TriangularInverse
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW.CapCrossingAlgebra
open scoped BigOperators

def columnUpdate {n : ℕ} (a : Fin n → ℚ) (j : Fin n) :
    Matrix (Fin n) (Fin n) ℚ := fun i k => if k = j then a i else 0

theorem inverse_conjugation_change {R : Type*} [Ring R]
    (F₀ F₁ K₀ K₁ S T : R)
    (hF₀ : F₀ * K₀ = 1) (hK₁ : K₁ * F₁ = 1)
    (hjump : F₁ = (1 + T) * F₀)
    (hnil : T * T = 0) (hquad : T * S * T = 0) :
    K₁ * S * F₁ - K₀ * S * F₀ = K₀ * (S * T - T * S) * F₀ := by
  have hright : F₁ * (K₀ * (1 - T)) = 1 := by
    rw [hjump]
    calc
      (1 + T) * F₀ * (K₀ * (1 - T)) = (1 + T) * (F₀ * K₀) * (1 - T) := by
        noncomm_ring
      _ = (1 + T) * (1 - T) := by rw [hF₀, mul_one]
      _ = 1 - T * T := by noncomm_ring
      _ = 1 := by rw [hnil, sub_zero]
  have hK : K₁ = K₀ * (1 - T) := by
    calc
      K₁ = K₁ * 1 := (mul_one _).symm
      _ = K₁ * (F₁ * (K₀ * (1 - T))) := by rw [hright]
      _ = (K₁ * F₁) * (K₀ * (1 - T)) := (mul_assoc _ _ _).symm
      _ = K₀ * (1 - T) := by rw [hK₁, one_mul]
  have hmiddle : (1 - T) * S * (1 + T) - S = S * T - T * S := by
    calc
      _ = S * T - T * S - T * S * T := by noncomm_ring
      _ = S * T - T * S := by rw [hquad, sub_zero]
  rw [hK, hjump]
  calc
    _ = K₀ * ((1 - T) * S * (1 + T) - S) * F₀ := by noncomm_ring
    _ = K₀ * (S * T - T * S) * F₀ := by rw [hmiddle]

private theorem columnUpdate_mul {n : ℕ} (a : Fin n → ℚ) (j : Fin n)
    (F : Matrix (Fin n) (Fin n) ℚ) (i k : Fin n) :
    (columnUpdate a j * F) i k = a i * F j k := by
  simp [Matrix.mul_apply, columnUpdate, ite_mul]

private theorem mul_columnUpdate {n : ℕ} (F : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℚ) (j : Fin n) :
    F * columnUpdate a j = columnUpdate (fun i => ∑ l, F i l * a l) j := by
  ext i k
  by_cases hk : k = j <;> simp [Matrix.mul_apply, columnUpdate, hk]

private theorem columnUpdate_nilpotent {n : ℕ} (a : Fin n → ℚ) (j : Fin n)
    (ha : a j = 0) : columnUpdate a j * columnUpdate a j = 0 := by
  ext i k
  rw [columnUpdate_mul]
  simp [columnUpdate, ha]

private theorem columnUpdate_mul_diagonal {n : ℕ} (h a : Fin n → ℚ)
    (j : Fin n) (s : ℚ) (hs : h j = s) :
    columnUpdate a j * Matrix.diagonal h = s • columnUpdate a j := by
  ext i k
  rw [Matrix.mul_diagonal]
  by_cases hk : k = j
  · subst k
    simp [columnUpdate, hs, mul_comm]
  · simp [columnUpdate, hk]

private theorem diagonal_column_commutator {n : ℕ}
    (F U : Matrix (Fin n) (Fin n) ℚ) (h a : Fin n → ℚ)
    (b j : Fin n) (s : ℚ) (hs : h j = s)
    (hcolumn : ∀ i, (F * U) i b = ((h i - s) / 2) * a i) :
    Matrix.diagonal h * columnUpdate a j - columnUpdate a j * Matrix.diagonal h =
      (2 : ℚ) • (F * columnUpdate (fun i => U i b) j) := by
  rw [mul_columnUpdate F (fun i => U i b) j]
  ext i k
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hk : k = j
  · subst k
    have hc : (∑ l, F i l * U l b) = ((h i - s) / 2) * a i := by
      simpa only [Matrix.mul_apply] using hcolumn i
    simp only [columnUpdate, if_true, hs, Matrix.smul_apply, smul_eq_mul]
    rw [hc]
    ring
  · simp [columnUpdate, hk]

theorem rank_one_conjugation_jump {n : ℕ}
    (F₀ F₁ K₀ K₁ U : Matrix (Fin n) (Fin n) ℚ)
    (h a : Fin n → ℚ) (b j : Fin n) (s : ℚ)
    (hF₀ : F₀ * K₀ = 1) (hK₀ : K₀ * F₀ = 1)
    (hK₁ : K₁ * F₁ = 1)
    (hjump : F₁ = (1 + s • columnUpdate a j) * F₀)
    (hazero : a j = 0) (hs : h j = s)
    (hcolumn : ∀ i, (F₀ * U) i b = ((h i - s) / 2) * a i) :
    ∀ i k, (K₁ * Matrix.diagonal h * F₁ - K₀ * Matrix.diagonal h * F₀) i k =
      2 * s * U i b * F₀ j k := by
  let S := Matrix.diagonal h
  let N := columnUpdate a j
  let C := columnUpdate (fun i => U i b) j
  have hN : N * N = 0 := columnUpdate_nilpotent a j hazero
  have hNS : N * S = s • N := columnUpdate_mul_diagonal h a j s hs
  have hnil : (s • N) * (s • N) = 0 := by
    simp only [smul_mul_assoc, mul_smul_comm, hN, smul_zero]
  have hquad : (s • N) * S * (s • N) = 0 := by
    simp only [smul_mul_assoc, mul_smul_comm, hNS, hN, smul_zero]
  have hcomm : S * N - N * S = (2 : ℚ) • (F₀ * C) :=
    diagonal_column_commutator F₀ U h a b j s hs hcolumn
  have hdelta : K₁ * S * F₁ - K₀ * S * F₀ = (2 * s) • (C * F₀) := by
    calc
      _ = K₀ * (S * (s • N) - (s • N) * S) * F₀ :=
        inverse_conjugation_change F₀ F₁ K₀ K₁ S (s • N) hF₀ hK₁ hjump hnil hquad
      _ = K₀ * (s • ((2 : ℚ) • (F₀ * C))) * F₀ := by
        rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, hcomm]
      _ = (s * 2) • ((K₀ * F₀) * C * F₀) := by
        simp only [smul_smul, mul_smul_comm, smul_mul_assoc, mul_assoc]
      _ = (2 * s) • (C * F₀) := by rw [hK₀, one_mul, mul_comm s 2]
  intro i k
  have hi := congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => M i k) hdelta
  simpa only [S, C, Matrix.smul_apply, smul_eq_mul, columnUpdate_mul, mul_assoc] using hi










end DirectGLSSW.CapCrossingAlgebra
