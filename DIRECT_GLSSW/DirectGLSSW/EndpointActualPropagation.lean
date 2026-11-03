import DirectGLSSW.EndpointActualRecurrence
import DirectGLSSW.EndpointMatrixRecurrence

set_option autoImplicit false

namespace DirectGLSSW.EndpointCurrent
open DirectGLSSW EndpointPropagation
open scoped BigOperators

theorem endpointCurrent_eq_finiteInverse (d : ℕ → ℚ) (H : TripleArray) (n : ℕ) :
    (fun a i : Fin n => endpointCurrent d H a.val i.val) =
      finiteInverse (finiteKernel (endpointCoefficient d H) n) n := by
  apply matrix_eq_finiteInverse_of_endpoint_recurrence
  · intro a i _ hi
    exact endpointCurrent_below d H hi
  · intro a i _ hai
    exact endpointCurrent_recurrence d H hai

private theorem endpointCoefficient_congr (d : ℕ → ℚ) (H₀ H₁ : TripleArray)
    {l J : ℕ} (hl : 0 < l) (hlJ : l < J)
    (hcore : ∀ a b c, 0 < a → a < b → b < c → c ≤ J → H₁ a b c = H₀ a b c)
    (hroot : ∀ b, 0 < b → b < J → H₁ 0 b J = H₀ 0 b J) :
    endpointCoefficient d H₁ l J = endpointCoefficient d H₀ l J := by
  classical
  unfold endpointCoefficient
  rw [hroot l hl hlJ]
  congr 1
  let w₀ := fun b => (d b - H₀ 0 b J) / 2
  let w₁ := fun b => (d b - H₁ 0 b J) / 2
  let b₀ := ordinaryCurrent (fun _ b _ => d b) H₀
  let b₁ := ordinaryCurrent (fun _ b _ => d b) H₁
  change weightedCutSum w₁ b₁ l J = weightedCutSum w₀ b₀ l J
  calc
    weightedCutSum w₁ b₁ l J = weightedCutSum w₀ b₁ l J := by
      unfold weightedCutSum
      apply Finset.sum_congr rfl
      intro S hS
      apply congrArg (fun z : ℚ => z * branchProduct b₁ (cutVertices l J S))
      apply Finset.prod_congr rfl
      intro b hb
      have hbI := Finset.mem_Ioo.mp (Finset.mem_powerset.mp hS hb)
      dsimp [w₀, w₁]
      rw [hroot b (by omega) hbI.2]
    _ = weightedCutSum w₀ b₀ l J := by
      apply weightedCutSum_congr_of_branch_eq w₀ hlJ
      intro a b hla hab hbJ
      apply ordinaryCurrent_congr_interval_fixed_near _ _ _ hab
      intro x y z hax hxy hyz hzb
      exact hcore x y z (by omega) hxy hyz (by omega)

theorem endpointCurrent_single_far_event_propagation
    (d : ℕ → ℚ) (H₀ H₁ : TripleArray) (n k : ℕ) (j : Fin n)
    (hother : ∀ x y z, x < y → y < z → z ≤ n →
      (x ≠ 0 ∨ y ≠ k ∨ z ≠ j.val+1) → H₁ x y z = H₀ x y z)
    (a i : Fin n) :
    endpointCurrent d H₁ a.val i.val - endpointCurrent d H₀ a.val i.val =
      (endpointCurrent d H₁ a.val j.val - endpointCurrent d H₀ a.val j.val) *
        endpointCurrent d H₀ j.val i.val := by
  let K₀ := finiteKernel (endpointCoefficient d H₀) n
  let K₁ := finiteKernel (endpointCoefficient d H₁) n
  have hK₀ : StrictUpper K₀ := by
    intro x y hyx
    simp [K₀, finiteKernel, Nat.not_lt.mpr hyx]
  have hK₁ : StrictUpper K₁ := by
    intro x y hyx
    simp [K₁, finiteKernel, Nat.not_lt.mpr hyx]
  have hKother : ∀ x y, y ≠ j → K₁ x y = K₀ x y := by
    intro x y hy
    by_cases hxy : x.val < y.val
    · simp only [K₀, K₁, finiteKernel, if_pos hxy]
      apply endpointCoefficient_congr d H₀ H₁ (by omega) (by omega)
      · intro p q r hp hpq hqr hry
        exact hother p q r hpq hqr (by have hyN := y.isLt; omega) (Or.inl (ne_of_gt hp))
      · intro b hb hby
        have hcol : y.val + 1 ≠ j.val + 1 := by
          intro he
          exact hy (Fin.ext (by omega))
        exact hother 0 b (y.val+1) hb hby (by have hyN := y.isLt; omega)
          (Or.inr (Or.inr hcol))
    · simp [K₀, K₁, finiteKernel, hxy]
  have hF₀ := endpointCurrent_eq_finiteInverse d H₀ n
  have hF₁ := endpointCurrent_eq_finiteInverse d H₁ n
  have hp := inverse_single_column_propagation K₀ K₁ hK₀ hK₁ j hKother a i
  change (fun a i : Fin n => endpointCurrent d H₀ a.val i.val) = finiteInverse K₀ n at hF₀
  change (fun a i : Fin n => endpointCurrent d H₁ a.val i.val) = finiteInverse K₁ n at hF₁
  rw [← hF₀, ← hF₁] at hp
  exact hp





end DirectGLSSW.EndpointCurrent
