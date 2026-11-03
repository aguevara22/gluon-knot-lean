import SplitSumOrder

set_option autoImplicit false

namespace DirectGLSSW.PermutationOrbits

private theorem pivot_ne_of_subtype
    {α : Type} {p : Equiv.Perm α} {n : ℕ}
    (e : Component p ≃ Fin n) (C₀ : Component p)
    (C : {C : Component p // C ≠ C₀}) : e C₀ ≠ e C.val := by
  intro h
  exact C.property (e.injective h).symm

private theorem middle_lt_unaffected_fin
    {n : ℕ} (p q : Fin n) (hpq : p ≠ q) :
    p.castSucc < p.succ.succAbove q ↔ p < q := by
  rcases lt_or_gt_of_ne hpq with hpq' | hqp
  · rw [Fin.succAbove_succ_of_lt p q hpq', Fin.castSucc_lt_succ_iff]
    exact ⟨fun _ => hpq', fun h => le_of_lt h⟩
  · rw [Fin.succAbove_succ_of_le p q (Fin.le_of_lt hqp)]
    simp only [Fin.castSucc_lt_castSucc_iff]

private theorem tail_lt_unaffected_fin
    {n : ℕ} (p q : Fin n) (hpq : p ≠ q) :
    p.succ < p.succ.succAbove q ↔ p < q := by
  rcases lt_or_gt_of_ne hpq with hpq' | hqp
  · rw [Fin.succAbove_succ_of_lt p q hpq', Fin.succ_lt_succ_iff]
  · rw [Fin.succAbove_succ_of_le p q (Fin.le_of_lt hqp)]
    have hlt : q.castSucc < p.succ :=
      Fin.castSucc_lt_succ_iff.mpr (Fin.le_of_lt hqp)
    exact ⟨fun h => False.elim ((lt_asymm hlt) h),
      fun h => False.elim ((lt_asymm hqp) h)⟩

private theorem unaffected_lt_middle_fin
    {n : ℕ} (p q : Fin n) (hpq : p ≠ q) :
    p.succ.succAbove q < p.castSucc ↔ q < p := by
  rcases lt_or_gt_of_ne hpq with hpq' | hqp
  · rw [Fin.succAbove_succ_of_lt p q hpq']
    have hlt : p.castSucc < q.succ :=
      Fin.castSucc_lt_succ_iff.mpr (le_of_lt hpq')
    exact ⟨fun h => False.elim ((lt_asymm hlt) h),
      fun h => False.elim ((lt_asymm hpq') h)⟩
  · rw [Fin.succAbove_succ_of_le p q (Fin.le_of_lt hqp)]
    simp only [Fin.castSucc_lt_castSucc_iff]

private theorem unaffected_lt_tail_fin
    {n : ℕ} (p q : Fin n) (hpq : p ≠ q) :
    p.succ.succAbove q < p.succ ↔ q < p := by
  rcases lt_or_gt_of_ne hpq with hpq' | hqp
  · rw [Fin.succAbove_succ_of_lt p q hpq']
    have hlt : p.succ < q.succ := Fin.succ_lt_succ_iff.mpr hpq'
    exact ⟨fun h => False.elim ((lt_asymm hlt) h),
      fun h => False.elim ((lt_asymm hpq') h)⟩
  · rw [Fin.succAbove_succ_of_le p q (Fin.le_of_lt hqp)]
    exact ⟨fun _ => hqp, fun _ => Fin.castSucc_lt_succ_iff.mpr (Fin.le_of_lt hqp)⟩

theorem splitSumToFinMiddleFirst_true_lt_other_iff
    {α : Type} {p : Equiv.Perm α} {n : ℕ}
    (e : Component p ≃ Fin n) (C₀ : Component p)
    (C : {C : Component p // C ≠ C₀}) :
    splitSumToFinMiddleFirst e C₀ (Sum.inl true) <
      splitSumToFinMiddleFirst e C₀ (Sum.inr C) ↔ e C₀ < e C.val := by
  rw [splitSumToFinMiddleFirst_true, splitSumToFinMiddleFirst_other]
  exact middle_lt_unaffected_fin (e C₀) (e C.val) (pivot_ne_of_subtype e C₀ C)

theorem splitSumToFinMiddleFirst_false_lt_other_iff
    {α : Type} {p : Equiv.Perm α} {n : ℕ}
    (e : Component p ≃ Fin n) (C₀ : Component p)
    (C : {C : Component p // C ≠ C₀}) :
    splitSumToFinMiddleFirst e C₀ (Sum.inl false) <
      splitSumToFinMiddleFirst e C₀ (Sum.inr C) ↔ e C₀ < e C.val := by
  rw [splitSumToFinMiddleFirst_false, splitSumToFinMiddleFirst_other]
  exact tail_lt_unaffected_fin (e C₀) (e C.val) (pivot_ne_of_subtype e C₀ C)

theorem splitSumToFinMiddleFirst_other_lt_true_iff
    {α : Type} {p : Equiv.Perm α} {n : ℕ}
    (e : Component p ≃ Fin n) (C₀ : Component p)
    (C : {C : Component p // C ≠ C₀}) :
    splitSumToFinMiddleFirst e C₀ (Sum.inr C) <
      splitSumToFinMiddleFirst e C₀ (Sum.inl true) ↔ e C.val < e C₀ := by
  rw [splitSumToFinMiddleFirst_other, splitSumToFinMiddleFirst_true]
  exact unaffected_lt_middle_fin (e C₀) (e C.val) (pivot_ne_of_subtype e C₀ C)

theorem splitSumToFinMiddleFirst_other_lt_false_iff
    {α : Type} {p : Equiv.Perm α} {n : ℕ}
    (e : Component p ≃ Fin n) (C₀ : Component p)
    (C : {C : Component p // C ≠ C₀}) :
    splitSumToFinMiddleFirst e C₀ (Sum.inr C) <
      splitSumToFinMiddleFirst e C₀ (Sum.inl false) ↔ e C.val < e C₀ := by
  rw [splitSumToFinMiddleFirst_other, splitSumToFinMiddleFirst_false]
  exact unaffected_lt_tail_fin (e C₀) (e C.val) (pivot_ne_of_subtype e C₀ C)

end DirectGLSSW.PermutationOrbits





