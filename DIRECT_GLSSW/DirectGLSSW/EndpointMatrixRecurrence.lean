import DirectGLSSW.EndpointPropagation
import DirectGLSSW.IntervalCurrent

set_option autoImplicit false

namespace DirectGLSSW.EndpointPropagation
open DirectGLSSW
open scoped BigOperators

def finiteKernel (C : IntervalArray) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun a i => if a.val < i.val then C (a.val+1) (i.val+1) else 0

private theorem finiteKernel_strictUpper (C : IntervalArray) (n : ℕ) :
    StrictUpper (finiteKernel C n) := by
  intro a i hi
  simp [finiteKernel, Nat.not_lt.mpr hi]

private theorem finite_sum_eq_interval_sum (F C : IntervalArray) (n : ℕ)
    (hbelow : ∀ a i, a < n → i < a → F a i = 0) (a i : Fin n) :
    (∑ r : Fin n, F a.val r.val * finiteKernel C n r i) =
      ∑ k ∈ Finset.Ioo a.val (i.val+1), F a.val (k-1) * C k (i.val+1) := by
  classical
  let s := Finset.univ.filter (fun r : Fin n => a.val ≤ r.val ∧ r.val < i.val)
  have hf : (∑ r : Fin n, F a.val r.val * finiteKernel C n r i) =
      ∑ r ∈ s, F a.val r.val * C (r.val+1) (i.val+1) := by
    dsimp [s]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases har : a.val ≤ r.val
    · by_cases hri : r.val < i.val <;> simp [finiteKernel, har, hri]
    · have hF : F a.val r.val = 0 := hbelow _ _ a.isLt (by omega)
      simp [hF, har]
  rw [hf]
  apply Finset.sum_bij (fun r _ => r.val + 1)
  · intro r hr
    have h := (Finset.mem_filter.mp hr).2
    exact Finset.mem_Ioo.mpr (by omega)
  · intro r hr t ht he
    apply Fin.ext
    omega
  · intro k hk
    have h := Finset.mem_Ioo.mp hk
    have hik := i.isLt
    let r : Fin n := ⟨k-1, by omega⟩
    refine ⟨r, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · simp
      · dsimp [r]
        omega
    · dsimp [r]
      omega
  · intro r hr
    simp

theorem matrix_eq_finiteInverse_of_endpoint_recurrence
    (F C : IntervalArray) (n : ℕ)
    (hbelow : ∀ a i, a < n → i < a → F a i = 0)
    (hrec : ∀ a i, i < n → a ≤ i →
      F a i = source a (i+1) - ∑ k ∈ Finset.Ioo a (i+1), F a (k-1) * C k (i+1)) :
    (fun a i : Fin n => F a.val i.val) = finiteInverse (finiteKernel C n) n := by
  classical
  let M : Matrix (Fin n) (Fin n) ℚ := fun a i => F a.val i.val
  let K := finiteKernel C n
  have hm : M * (1+K) = 1 := by
    rw [mul_add, mul_one]
    apply Matrix.ext
    intro a i
    change F a.val i.val + (∑ r : Fin n, F a.val r.val * finiteKernel C n r i) =
      (1 : Matrix (Fin n) (Fin n) ℚ) a i
    rw [finite_sum_eq_interval_sum F C n hbelow a i]
    by_cases hai : a.val ≤ i.val
    · have hr := hrec a.val i.val i.isLt hai
      have hs : source a.val (i.val+1) = (1 : Matrix (Fin n) (Fin n) ℚ) a i := by
        by_cases he : a = i
        · subst i
          simp [source]
        · have hv : i.val ≠ a.val := by
            intro h
            exact he (Fin.ext h.symm)
          simp [source, Matrix.one_apply, he, hv]
      rw [← hs]
      linarith
    · have hil : i.val < a.val := by omega
      have he : a ≠ i := by intro h; subst i; omega
      have hempty : Finset.Ioo a.val (i.val+1) = ∅ := by
        apply Finset.eq_empty_iff_forall_not_mem.mpr
        intro k hk
        have h := Finset.mem_Ioo.mp hk
        omega
      simp [hbelow a.val i.val a.isLt hil, hempty, Matrix.one_apply, he]
  have hK : StrictUpper K := finiteKernel_strictUpper C n
  obtain ⟨_, hright⟩ := strictUpper_finiteInverse K hK
  change M = finiteInverse K n
  calc
    M = M * ((1+K) * finiteInverse K n) := by rw [hright, mul_one]
    _ = (M * (1+K)) * finiteInverse K n := (mul_assoc _ _ _).symm
    _ = finiteInverse K n := by rw [hm, one_mul]





end DirectGLSSW.EndpointPropagation
