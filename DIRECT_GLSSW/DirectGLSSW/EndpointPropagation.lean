import DirectGLSSW.TriangularInverse
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false

namespace DirectGLSSW.EndpointPropagation
open DirectGLSSW
open scoped BigOperators

theorem finiteInverse_diagonal {n : ℕ} (K : Matrix (Fin n) (Fin n) ℚ)
    (hK : StrictUpper K) (j : Fin n) : finiteInverse K n j j = 1 := by
  have hneg : StrictUpper (-K) := by
    intro a b hab
    simp only [Matrix.neg_apply, hK a b hab, neg_zero]
  unfold finiteInverse
  simp only [Matrix.sum_apply]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    exact strictUpper_pow_entry_zero (-K) hneg k j j (by omega)
  · intro hzero
    have hj := j.isLt
    exact False.elim (hzero (Finset.mem_range.mpr (by omega)))

theorem inverse_single_column_propagation {n : ℕ}
    (K₀ K₁ : Matrix (Fin n) (Fin n) ℚ)
    (hK₀ : StrictUpper K₀) (hK₁ : StrictUpper K₁) (j : Fin n)
    (hother : ∀ a b, b ≠ j → K₁ a b = K₀ a b) (a i : Fin n) :
    finiteInverse K₁ n a i - finiteInverse K₀ n a i =
      (finiteInverse K₁ n a j - finiteInverse K₀ n a j) * finiteInverse K₀ n j i := by
  let F₀ := finiteInverse K₀ n
  let F₁ := finiteInverse K₁ n
  obtain ⟨hF₀, hF₀r⟩ := strictUpper_finiteInverse K₀ hK₀
  obtain ⟨hF₁, _⟩ := strictUpper_finiteInverse K₁ hK₁
  change F₀ * (1 + K₀) = 1 at hF₀
  change (1 + K₀) * F₀ = 1 at hF₀r
  change F₁ * (1 + K₁) = 1 at hF₁
  let C := F₁ * (K₀ - K₁)
  have heq : F₁ - F₀ = C * F₀ := by
    calc
      F₁ - F₀ = F₁ * ((1 + K₀) * F₀) - (F₁ * (1 + K₁)) * F₀ := by
        rw [hF₀r, hF₁, mul_one, one_mul]
      _ = C * F₀ := by dsimp [C]; noncomm_ring
  have hCzero (b : Fin n) (hb : b ≠ j) : C a b = 0 := by
    change (F₁ * (K₀ - K₁)) a b = 0
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    simp [Matrix.sub_apply, hother l b hb]
  have hentry (b : Fin n) : F₁ a b - F₀ a b = C a j * F₀ j b := by
    have he := congrFun (congrFun heq a) b
    simp only [Matrix.sub_apply, Matrix.mul_apply] at he
    rw [Finset.sum_eq_single j] at he
    · exact he
    · intro l _ hlj
      rw [hCzero l hlj, zero_mul]
    · simp
  have hdiag : F₀ j j = 1 := finiteInverse_diagonal K₀ hK₀ j
  have hsource : F₁ a j - F₀ a j = C a j := by
    simpa only [hdiag, mul_one] using hentry j
  change F₁ a i - F₀ a i = (F₁ a j - F₀ a j) * F₀ j i
  rw [hsource]
  exact hentry i




end DirectGLSSW.EndpointPropagation
