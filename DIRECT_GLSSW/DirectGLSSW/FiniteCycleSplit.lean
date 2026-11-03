import DirectGLSSW.OrderedEventSuccessor
import DirectGLSSW.PermutationOrbits

/-!
# Normalized finite-cycle split (staged prerequisite)

Statement transcription: STATEMENTS.md, written before this source.
Source motivation: frozen note lines 131–139. This module only classifies
one cut of the accepted modular successor. It does not prove source
nonalternation, arbitrary endpoint normalization, or geometric realization.
The full component quotient retains every singleton orbit.
-/

set_option autoImplicit false

namespace DirectGLSSW.FiniteCycleSplit

open Equiv

variable {m : ℕ} [NeZero m]

/-- The interval side consists of the labels 1 through k, including k. -/
def cutSide (k i : Fin m) : Bool := decide (0 < i.val ∧ i.val ≤ k.val)

/-- Swap the selected outgoing successors of the accepted modular cycle. -/
noncomputable def cutPerm (k : Fin m) : Perm (Fin m) :=
  DirectGLSSW.cyclicSuccessorPerm m * Equiv.swap 0 k

@[simp] theorem cutSide_zero (k : Fin m) : cutSide k 0 = false := by
  simp [cutSide]

@[simp] theorem cutSide_mark (k : Fin m) (hk : k ≠ 0) : cutSide k k = true := by
  have hkval : 0 < k.val := by
    have : k.val ≠ 0 := fun h => hk (Fin.ext h)
    omega
  simp [cutSide, hkval]

/-- The root 0 takes the old successor of k, including wrap to 0. -/
theorem cutPerm_apply_zero (k : Fin m) :
    (cutPerm k 0).val = (k.val + 1) % m := by
  simp [cutPerm, DirectGLSSW.cyclicSuccessor, DirectGLSSW.cyclicVertexIndex]

/-- The root k takes the old successor of 0. -/
theorem cutPerm_apply_mark (k : Fin m) (hk : k ≠ 0) :
    (cutPerm k k).val = 1 := by
  have htwo : 1 < m := by
    have : k.val ≠ 0 := fun h => hk (Fin.ext h)
    have := k.isLt
    omega
  simp [cutPerm, DirectGLSSW.cyclicSuccessor, DirectGLSSW.cyclicVertexIndex,
    Nat.mod_eq_of_lt htwo]

/-- Away from both selected labels the old successor is unchanged. -/
theorem cutPerm_apply_of_ne (k i : Fin m) (hi0 : i ≠ 0) (hik : i ≠ k) :
    (cutPerm k i).val = (i.val + 1) % m := by
  simp [cutPerm, Equiv.swap_apply_of_ne_of_ne hi0 hik,
    DirectGLSSW.cyclicSuccessor, DirectGLSSW.cyclicVertexIndex]

/-- One step preserves the actual interval label. -/
theorem cutSide_apply (k i : Fin m) : cutSide k (cutPerm k i) = cutSide k i := by
  unfold cutSide
  apply decide_eq_decide.mpr
  by_cases hk : k = 0
  · subst k
    simp only [Fin.val_zero]
    omega
  by_cases hi0 : i = 0
  · subst i
    rw [cutPerm_apply_zero]
    simp only [Fin.val_zero]
    by_cases hwrap : k.val + 1 < m
    · rw [Nat.mod_eq_of_lt hwrap]
      omega
    · have heq : k.val + 1 = m := by have := k.isLt; omega
      simp [heq]
  by_cases hik : i = k
  · subst i
    rw [cutPerm_apply_mark k hk]
    have : k.val ≠ 0 := fun h => hk (Fin.ext h)
    omega
  rw [cutPerm_apply_of_ne k i hi0 hik]
  have hiv : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
  have hikv : i.val ≠ k.val := fun h => hik (Fin.ext h)
  by_cases hwrap : i.val + 1 < m
  · rw [Nat.mod_eq_of_lt hwrap]
    omega
  · have heq : i.val + 1 = m := by have := i.isLt; omega
    rw [heq, Nat.mod_self]
    have := k.isLt
    omega

/-- The interval label is constant along all forward iterates. -/
theorem cutSide_pow_apply (k i : Fin m) (t : ℕ) :
    cutSide k ((cutPerm k ^ t) i) = cutSide k i := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pow_succ', Perm.mul_apply, cutSide_apply, ih]

/-- Before closure, the 0-rooted traversal follows k+1 through m-1. -/
theorem cutPerm_pow_zero_val (k : Fin m) (t : ℕ)
    (ht : 1 ≤ t) (htbound : t < m - k.val) :
    ((cutPerm k ^ t) 0).val = k.val + t := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases ht0 : t = 0
      · subst t
        simp only [Nat.zero_add, pow_one, cutPerm_apply_zero]
        apply Nat.mod_eq_of_lt
        omega
      · have hv := ih (by omega) (by omega)
        rw [pow_succ', Perm.mul_apply]
        have hi0 : (cutPerm k ^ t) 0 ≠ 0 := by
          intro he
          have hval := congrArg Fin.val he
          simp only [Fin.val_zero] at hval
          omega
        have hik : (cutPerm k ^ t) 0 ≠ k := by
          intro he
          have hval := congrArg Fin.val he
          omega
        rw [cutPerm_apply_of_ne k _ hi0 hik, hv, Nat.mod_eq_of_lt (by omega)]
        omega

/-- Before closure, the k-rooted traversal follows 1 through k-1. -/
theorem cutPerm_pow_mark_val (k : Fin m) (hk : k ≠ 0) (t : ℕ)
    (ht : 1 ≤ t) (htbound : t < k.val) :
    ((cutPerm k ^ t) k).val = t := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases ht0 : t = 0
      · subst t
        simpa using cutPerm_apply_mark k hk
      · have hv := ih (by omega) (by omega)
        rw [pow_succ', Perm.mul_apply]
        have hi0 : (cutPerm k ^ t) k ≠ 0 := by
          intro he
          have hval := congrArg Fin.val he
          simp only [Fin.val_zero] at hval
          omega
        have hik : (cutPerm k ^ t) k ≠ k := by
          intro he
          have hval := congrArg Fin.val he
          omega
        rw [cutPerm_apply_of_ne k _ hi0 hik, hv, Nat.mod_eq_of_lt (by have := k.isLt; omega)]

/-- The 0-rooted traversal closes after m-k steps, also when that side is a singleton. -/
theorem cutPerm_pow_zero_close (k : Fin m) :
    (cutPerm k ^ (m - k.val)) 0 = 0 := by
  have hlen : 0 < m - k.val := by have := k.isLt; omega
  apply Fin.ext
  simp only [Fin.val_zero]
  by_cases hsingle : m - k.val = 1
  · rw [hsingle, pow_one, cutPerm_apply_zero]
    have heq : k.val + 1 = m := by have := k.isLt; omega
    simp [heq]
  · have ht : 1 ≤ m - k.val - 1 := by omega
    have htbound : m - k.val - 1 < m - k.val := by omega
    have hv := cutPerm_pow_zero_val k (m - k.val - 1) ht htbound
    have hi0 : (cutPerm k ^ (m - k.val - 1)) 0 ≠ 0 := by
      intro he
      have hval := congrArg Fin.val he
      simp only [Fin.val_zero] at hval
      omega
    have hik : (cutPerm k ^ (m - k.val - 1)) 0 ≠ k := by
      intro he
      have hval := congrArg Fin.val he
      omega
    have hexp : m - k.val = (m - k.val - 1) + 1 := by omega
    conv_lhs => rw [hexp, pow_succ', Perm.mul_apply]
    rw [cutPerm_apply_of_ne k _ hi0 hik, hv]
    have heq : k.val + (m - k.val - 1) + 1 = m := by omega
    simp [heq]

/-- The k-rooted traversal closes after k steps, also when k=1. -/
theorem cutPerm_pow_mark_close (k : Fin m) (hk : k ≠ 0) :
    (cutPerm k ^ k.val) k = k := by
  have hkpos : 0 < k.val := by
    have : k.val ≠ 0 := fun h => hk (Fin.ext h)
    omega
  apply Fin.ext
  by_cases hsingle : k.val = 1
  · rw [hsingle, pow_one, cutPerm_apply_mark k hk]
  · have ht : 1 ≤ k.val - 1 := by omega
    have htbound : k.val - 1 < k.val := by omega
    have hv := cutPerm_pow_mark_val k hk (k.val - 1) ht htbound
    have hi0 : (cutPerm k ^ (k.val - 1)) k ≠ 0 := by
      intro he
      have hval := congrArg Fin.val he
      simp only [Fin.val_zero] at hval
      omega
    have hik : (cutPerm k ^ (k.val - 1)) k ≠ k := by
      intro he
      have hval := congrArg Fin.val he
      omega
    have hexp : k.val = (k.val - 1) + 1 := by omega
    conv_lhs => rw [hexp, pow_succ', Perm.mul_apply]
    rw [cutPerm_apply_of_ne k _ hi0 hik, hv]
    have heq : k.val - 1 + 1 = k.val := by omega
    rw [heq, Nat.mod_eq_of_lt k.isLt]

/-- Every point on the complementary side is reached before the 0-rooted closure. -/
theorem cut_zero_exists_pow (k i : Fin m) (hi : cutSide k i = false) :
    ∃ t < m - k.val, (cutPerm k ^ t) 0 = i := by
  by_cases hi0 : i = 0
  · subst i
    exact ⟨0, by have := k.isLt; omega, by simp⟩
  have hipos : 0 < i.val := by
    have : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    omega
  have hitop : k.val < i.val := by
    simp only [cutSide, decide_eq_false_iff_not] at hi
    omega
  have ht : 1 ≤ i.val - k.val := by omega
  have htbound : i.val - k.val < m - k.val := by have := i.isLt; omega
  refine ⟨i.val - k.val, htbound, ?_⟩
  apply Fin.ext
  rw [cutPerm_pow_zero_val k _ ht htbound]
  omega

/-- Every point on the interval side is reached before the k-rooted closure. -/
theorem cut_mark_exists_pow (k : Fin m) (hk : k ≠ 0) (i : Fin m)
    (hi : cutSide k i = true) :
    ∃ t < k.val, (cutPerm k ^ t) k = i := by
  have hip : 0 < i.val ∧ i.val ≤ k.val := by
    simpa only [cutSide, decide_eq_true_eq] using hi
  by_cases hik : i = k
  · subst i
    exact ⟨0, hip.1, by simp⟩
  have hiv : i.val ≠ k.val := fun h => hik (Fin.ext h)
  have htbound : i.val < k.val := by omega
  refine ⟨i.val, htbound, ?_⟩
  apply Fin.ext
  exact cutPerm_pow_mark_val k hk _ hip.1 htbound

/-- Orbit related points have the same actual interval label. -/
theorem cutSide_eq_of_sameCycle (k i j : Fin m)
    (h : (cutPerm k).SameCycle i j) : cutSide k i = cutSide k j := by
  obtain ⟨t, ht⟩ := h.exists_nat_pow_eq
  have hs := cutSide_pow_apply k i t
  rw [ht] at hs
  exact hs.symm

/-- The complete orbit of 0 is exactly the complementary side. -/
theorem cut_sameCycle_zero_iff (k i : Fin m) :
    (cutPerm k).SameCycle 0 i ↔ cutSide k i = false := by
  constructor
  · intro hi
    have h := cutSide_eq_of_sameCycle k 0 i hi
    simpa using h.symm
  · intro hi
    obtain ⟨t, _, ht⟩ := cut_zero_exists_pow k i hi
    exact ⟨(t : ℤ), by simpa only [zpow_natCast] using ht⟩

/-- The complete orbit of k is exactly the interval side. -/
theorem cut_sameCycle_mark_iff (k : Fin m) (hk : k ≠ 0) (i : Fin m) :
    (cutPerm k).SameCycle k i ↔ cutSide k i = true := by
  constructor
  · intro hi
    have h := cutSide_eq_of_sameCycle k k i hi
    simpa only [cutSide_mark k hk] using h.symm
  · intro hi
    obtain ⟨t, _, ht⟩ := cut_mark_exists_pow k hk i hi
    exact ⟨(t : ℤ), by simpa only [zpow_natCast] using ht⟩

/-- The entire SameCycle relation is equality of the two interval labels. -/
theorem cut_sameCycle_iff (k : Fin m) (hk : k ≠ 0) (i j : Fin m) :
    (cutPerm k).SameCycle i j ↔ cutSide k i = cutSide k j := by
  constructor
  · exact cutSide_eq_of_sameCycle k i j
  · intro hij
    cases hi : cutSide k i with
    | false =>
        have hj : cutSide k j = false := hij.symm.trans hi
        exact ((cut_sameCycle_zero_iff k i).2 hi).symm.trans
          ((cut_sameCycle_zero_iff k j).2 hj)
    | true =>
        have hj : cutSide k j = true := hij.symm.trans hi
        exact ((cut_sameCycle_mark_iff k hk i).2 hi).symm.trans
          ((cut_sameCycle_mark_iff k hk j).2 hj)

/-- Both labels occur at the selected roots, including singleton blocks. -/
theorem cutSide_surjective (k : Fin m) (hk : k ≠ 0) :
    Function.Surjective (cutSide k) := by
  intro b
  cases b with
  | false => exact ⟨0, cutSide_zero k⟩
  | true => exact ⟨k, cutSide_mark k hk⟩

/-- The full component quotient is equivalent to the two actual interval sides. -/
noncomputable def cutComponentEquiv (k : Fin m) (hk : k ≠ 0) :
    PermutationOrbits.Component (cutPerm k) ≃ Bool :=
  (Quotient.congrRight (cut_sameCycle_iff k hk)).trans
    (Setoid.quotientKerEquivOfSurjective (cutSide k) (cutSide_surjective k hk))

/-- The component equivalence reads the interval label of every representative. -/
@[simp] theorem cutComponentEquiv_componentOf (k : Fin m) (hk : k ≠ 0) (i : Fin m) :
    cutComponentEquiv k hk (PermutationOrbits.componentOf (cutPerm k) i) = cutSide k i := rfl

/-- The full quotient has two components; no fixed-point component is discarded. -/
theorem cut_componentCount (k : Fin m) (hk : k ≠ 0) :
    PermutationOrbits.componentCount (cutPerm k) = 2 := by
  simpa only [Fintype.card_bool] using Fintype.card_congr (cutComponentEquiv k hk)

end DirectGLSSW.FiniteCycleSplit
