import DirectGLSSW.CapActualBranches
import DirectGLSSW.CapMatrixRestriction

set_option autoImplicit false

namespace DirectGLSSW.GlobalCapAlgebra
open scoped BigOperators
open DirectGLSSW.CapActualBranches DirectGLSSW.CapMatrixRestriction

noncomputable def lineCapHeights (q : ℕ → PlanarPoint ℝ) (n : ℕ) : Fin n → ℚ :=
  fun r => scalarSignValue (q (r.val + 1)).2

noncomputable def lineCapPairing (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  let d := fun k => scalarSignValue (q k).2
  globalCapPairing (capEndpointMatrix q (q 0) d n)
    (capInternalMatrix q d n) (capTerminalMatrix q d n) (lineCapHeights q n)

private theorem upper_mul {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℚ)
    (hA : UpperTriangularBlock A) (hC : UpperTriangularBlock C) :
    UpperTriangularBlock (A * C) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hki : k.val < i.val
  · rw [hA i k hki, zero_mul]
  · rw [hC k j (by omega), mul_zero]

private theorem upper_mul_diagonal {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℚ)
    (hA : UpperTriangularBlock A) (hC : UpperTriangularBlock C) (i : Fin n) :
    (A * C) i i = A i i * C i i := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro k _ hki
    by_cases hlt : k.val < i.val
    · rw [hA i k hlt, zero_mul]
    · have hne : k.val ≠ i.val := fun h => hki (Fin.ext h)
      rw [hC k i (by omega), mul_zero]
  · simp

private theorem diagonal_upper {n : ℕ} (h : Fin n → ℚ) :
    UpperTriangularBlock (Matrix.diagonal h) := by
  intro i j hij
  have hne : i ≠ j := by intro he; subst j; omega
  simp [Matrix.diagonal, hne]

private theorem weight_strictUpper {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ)
    (hB : StrictUpper B) (h : Fin n → ℚ) :
    StrictUpper (B * Matrix.diagonal h) := by
  intro i j hji
  rw [Matrix.mul_diagonal, hB i j hji, zero_mul]

private theorem resolvent_upper {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ)
    (hB : StrictUpper B) (h : Fin n → ℚ) :
    UpperTriangularBlock (globalCapResolvent B h) := by
  intro i j hij
  unfold globalCapResolvent finiteInverse
  simp only [neg_neg, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro k _
  exact strictUpper_pow_entry_zero _ (weight_strictUpper B hB h) k i j (by omega)

private theorem resolvent_diagonal {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ)
    (hB : StrictUpper B) (h : Fin n → ℚ) (i : Fin n) :
    globalCapResolvent B h i i = 1 := by
  classical
  unfold globalCapResolvent finiteInverse
  simp only [neg_neg, Matrix.sum_apply]
  have hi : 0 < n := by have := i.isLt; omega
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    exact strictUpper_pow_entry_zero _ (weight_strictUpper B hB h) k i i (by omega)
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr hi))

private theorem endpoint_upper (q : ℕ → PlanarPoint ℝ) (d : ℕ → ℚ) (n : ℕ) :
    UpperTriangularBlock (capEndpointMatrix q (q 0) d n) := by
  intro i j hij
  exact EndpointCurrent.endpointCurrent_below d _ (by omega)

private theorem terminal_upper (q : ℕ → PlanarPoint ℝ) (d : ℕ → ℚ) (n : ℕ) :
    UpperTriangularBlock (capTerminalMatrix q d n) := by
  intro i j hij
  exact TerminalEndpoint.terminalCurrent_below d _ (by omega)

theorem lineCapPairing_below (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (a b : Fin n) (hba : b.val < a.val) : lineCapPairing q n a b = 0 := by
  let d := fun k => scalarSignValue (q k).2
  let F := capEndpointMatrix q (q 0) d n
  let B := capInternalMatrix q d n
  let G := capTerminalMatrix q d n
  let h := lineCapHeights q n
  have hF : UpperTriangularBlock F := endpoint_upper q d n
  have hG : UpperTriangularBlock G := terminal_upper q d n
  have hB : StrictUpper B := cap_internalMatrix_strictUpper q d n
  exact upper_mul _ _ (upper_mul _ _ (upper_mul _ _ hF (diagonal_upper h))
    (resolvent_upper B hB h)) hG a b hba

theorem lineCapPairing_diagonal (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (a : Fin n) : lineCapPairing q n a a = lineCapHeights q n a := by
  let d := fun k => scalarSignValue (q k).2
  let F := capEndpointMatrix q (q 0) d n
  let B := capInternalMatrix q d n
  let G := capTerminalMatrix q d n
  let h := lineCapHeights q n
  have hF : UpperTriangularBlock F := endpoint_upper q d n
  have hG : UpperTriangularBlock G := terminal_upper q d n
  have hB : StrictUpper B := cap_internalMatrix_strictUpper q d n
  have hS := diagonal_upper h
  have hR := resolvent_upper B hB h
  change (F * Matrix.diagonal h * globalCapResolvent B h * G) a a = h a
  rw [upper_mul_diagonal _ _ (upper_mul _ _ (upper_mul _ _ hF hS) hR) hG,
    upper_mul_diagonal _ _ (upper_mul _ _ hF hS) hR,
    upper_mul_diagonal _ _ hF hS,
    resolvent_diagonal B hB h a]
  have hFd : F a a = 1 := EndpointCurrent.endpointCurrent_diagonal d _ a.val
  have hGd : G a a = 1 := TerminalEndpoint.terminalCurrent_diagonal d _ a.val
  simp [hFd, hGd, Matrix.diagonal_apply_eq]














end DirectGLSSW.GlobalCapAlgebra
