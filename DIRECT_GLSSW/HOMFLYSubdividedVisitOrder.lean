import SmoothingSubdividedCycles
import DirectGLSSW.PermutationInsertionWords

set_option autoImplicit false

namespace DirectGLSSW.SmoothingSubdividedCycles
open Equiv PermutationOrbits
universe u v
variable {α : Type u} {ι : Type v}
noncomputable section
attribute [local instance] Classical.propDecidable
variable (p : Perm α) (q : Perm (α ⊕ ι)) (a : ι → α)
variable (hnew : ∀ i, q (Sum.inr i) = Sum.inl (p (a i)))
variable (hcut : ∀ i, q (Sum.inl (a i)) = Sum.inr i)
variable (hold : ∀ x, (∀ i, x ≠ a i) → q (Sum.inl x) = Sum.inl (p x))
include hnew hcut hold

@[simp] theorem componentEquiv_old (x : α) :
    componentEquiv p q a hnew hcut hold (componentOf p x) =
      componentOf q (Sum.inl x) := rfl

theorem componentEquiv_new (i : ι) :
    componentEquiv p q a hnew hcut hold (componentOf p (a i)) =
      componentOf q (Sum.inr i) := by
  rw [componentEquiv_old, ← hcut, componentOf_apply]

/-- When different selected ports lie on different cut cycles, each selected
cycle acquires exactly its own connector. -/
def selectedFibreEquiv (i : ι)
    (hsep : ∀ j, j ≠ i → ¬ p.SameCycle (a i) (a j)) :
    Option (Fibre p (componentOf p (a i))) ≃
      Fibre q (componentOf q (Sum.inr i)) := by
  let e := componentEquiv p q a hnew hcut hold
  let f : Option (Fibre p (componentOf p (a i))) →
      Fibre q (componentOf q (Sum.inr i)) := fun x =>
    match x with
    | none => ⟨Sum.inr i, rfl⟩
    | some x => ⟨Sum.inl x.val, by
        rw [← componentEquiv_old p q a hnew hcut hold, x.property,
          componentEquiv_new p q a hnew hcut hold]⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    have hv := congrArg Subtype.val h
    cases x with
    | none => cases y <;> simp_all [f]
    | some x =>
      cases y with
      | none => simp_all [f]
      | some y =>
        apply congrArg some
        apply Subtype.ext
        exact Sum.inl.inj hv
  · intro y
    cases hy : y.val with
    | inl x =>
      have hx : componentOf p x = componentOf p (a i) := by
        apply e.injective
        change componentEquiv p q a hnew hcut hold _ = componentEquiv p q a hnew hcut hold _
        rw [componentEquiv_old, componentEquiv_new]
        exact hy ▸ y.property
      exact ⟨some ⟨x, hx⟩, Subtype.ext hy.symm⟩
    | inr j =>
      have hx : componentOf p (a j) = componentOf p (a i) := by
        apply e.injective
        change componentEquiv p q a hnew hcut hold _ = componentEquiv p q a hnew hcut hold _
        rw [componentEquiv_new, componentEquiv_new]
        exact hy ▸ y.property
      have hji : j = i := by
        by_contra hne
        exact hsep j hne ((componentOf_eq_iff p _ _).1 hx.symm)
      subst j
      exact ⟨none, Subtype.ext hy.symm⟩

theorem selectedFibre_card [Fintype α] [Fintype ι] (i : ι)
    (hsep : ∀ j, j ≠ i → ¬ p.SameCycle (a i) (a j)) :
    Fintype.card (Fibre q (componentOf q (Sum.inr i))) =
      Fintype.card (Fibre p (componentOf p (a i))) + 1 := by
  rw [← Fintype.card_congr (selectedFibreEquiv p q a hnew hcut hold i hsep)]
  exact Fintype.card_option

/-- Before the old cut cycle closes, starting at its new connector has the
same positive-time old visits as starting at its deleted incoming port. -/
theorem selected_pow [Fintype α] (i : ι)
    (hsep : ∀ j, j ≠ i → ¬ p.SameCycle (a i) (a j))
    (t : ℕ) (htpos : 0 < t)
    (ht : t < Fintype.card (Fibre p (componentOf p (a i)))) :
    (q ^ t) (Sum.inr i) = Sum.inl ((p ^ t) (a i)) := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases ht0 : t = 0
    · subst t
      simpa using hnew i
    · have hprev := ih (by omega) (by omega)
      have hports : ∀ j, (p ^ t) (a i) ≠ a j := by
        intro j hj
        by_cases hji : j = i
        · subst j
          exact PermutationInsertion.pow_ne_self_of_lt_fibreCard p (a i)
            (by omega) (by omega) hj
        · apply hsep j hji
          exact ⟨(t : ℤ), by simpa only [zpow_natCast] using hj⟩
      rw [pow_succ', Perm.mul_apply, hprev, hold _ hports,
        pow_succ', Perm.mul_apply]

/-- The exact retained visit-position transport for all-at-once connector
insertion, specialized only by the fact that selected ports occupy distinct
cut components. -/
theorem selected_orbitPosition [Fintype α] [Fintype ι]
    (i : ι) (hsep : ∀ j, j ≠ i → ¬ p.SameCycle (a i) (a j))
    (x : Fibre p (componentOf p (a i))) (hx : x.val ≠ a i) :
    ((orbitEnumeration q (Sum.inr i)).symm
      ⟨Sum.inl x.val, by
        rw [← componentEquiv_old p q a hnew hcut hold, x.property,
          componentEquiv_new p q a hnew hcut hold]⟩).val =
      ((orbitEnumeration p (a i)).symm x).val := by
  let t := (orbitEnumeration p (a i)).symm x
  have htbound := t.isLt
  have hpow : (p ^ t.val) (a i) = x.val := by
    have h := congrArg Subtype.val ((orbitEnumeration p (a i)).apply_symm_apply x)
    simpa only [orbitEnumeration_apply_val] using h
  have htpos : 0 < t.val := by
    by_contra h
    have ht0 : t.val = 0 := by omega
    rw [ht0, pow_zero, Perm.one_apply] at hpow
    exact hx hpow.symm
  let s : Fin (Fintype.card (Fibre q (componentOf q (Sum.inr i)))) :=
    ⟨t.val, by rw [selectedFibre_card p q a hnew hcut hold i hsep]; omega⟩
  have hiter := selected_pow p q a hnew hcut hold i hsep t.val htpos htbound
  rw [hpow] at hiter
  have he : orbitEnumeration q (Sum.inr i) s =
      ⟨Sum.inl x.val, by
        rw [← componentEquiv_old p q a hnew hcut hold, x.property,
          componentEquiv_new p q a hnew hcut hold]⟩ := by
    apply Subtype.ext
    simpa only [orbitEnumeration_apply_val] using hiter
  rw [← he, Equiv.symm_apply_apply]

/-- Cycles containing no selected port are unchanged by connector insertion. -/
def unselectedFibreEquiv (root : α)
    (hroot : ∀ j, ¬ p.SameCycle root (a j)) :
    Fibre p (componentOf p root) ≃ Fibre q (componentOf q (Sum.inl root)) := by
  let e := componentEquiv p q a hnew hcut hold
  let f : Fibre p (componentOf p root) → Fibre q (componentOf q (Sum.inl root)) :=
    fun x => ⟨Sum.inl x.val, by
      rw [← componentEquiv_old p q a hnew hcut hold, x.property, componentEquiv_old]⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    exact Sum.inl.inj (congrArg Subtype.val h)
  · intro y
    cases hy : y.val with
    | inl x =>
      have hx : componentOf p x = componentOf p root := by
        apply e.injective
        change componentEquiv p q a hnew hcut hold _ = componentEquiv p q a hnew hcut hold _
        rw [componentEquiv_old, componentEquiv_old]
        exact hy ▸ y.property
      exact ⟨⟨x, hx⟩, Subtype.ext hy.symm⟩
    | inr j =>
      have hx : componentOf p (a j) = componentOf p root := by
        apply e.injective
        change componentEquiv p q a hnew hcut hold _ = componentEquiv p q a hnew hcut hold _
        rw [componentEquiv_new, componentEquiv_old]
        exact hy ▸ y.property
      exact False.elim (hroot j ((componentOf_eq_iff p _ _).1 hx.symm))

omit hnew hcut in
theorem unselected_pow (root : α) (hroot : ∀ j, ¬ p.SameCycle root (a j))
    (t : ℕ) : (q ^ t) (Sum.inl root) = Sum.inl ((p ^ t) root) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hports : ∀ j, (p ^ t) root ≠ a j := by
      intro j hj
      apply hroot j
      exact ⟨(t : ℤ), by simpa only [zpow_natCast] using hj⟩
    rw [pow_succ', Perm.mul_apply, ih, hold _ hports, pow_succ', Perm.mul_apply]

theorem unselected_orbitPosition [Fintype α] [Fintype ι]
    (root : α) (hroot : ∀ j, ¬ p.SameCycle root (a j))
    (x : Fibre p (componentOf p root)) :
    ((orbitEnumeration q (Sum.inl root)).symm
      ⟨Sum.inl x.val, by
        rw [← componentEquiv_old p q a hnew hcut hold, x.property,
          componentEquiv_old p q a hnew hcut hold]⟩).val =
      ((orbitEnumeration p root).symm x).val := by
  let t := (orbitEnumeration p root).symm x
  have htbound := t.isLt
  have hpow : (p ^ t.val) root = x.val := by
    have h := congrArg Subtype.val ((orbitEnumeration p root).apply_symm_apply x)
    simpa only [orbitEnumeration_apply_val] using h
  have hc := Fintype.card_congr (unselectedFibreEquiv p q a hnew hcut hold root hroot)
  let s : Fin (Fintype.card (Fibre q (componentOf q (Sum.inl root)))) := Fin.cast hc t
  have hiter := unselected_pow p q a hold root hroot t.val
  rw [hpow] at hiter
  have he : orbitEnumeration q (Sum.inl root) s =
      ⟨Sum.inl x.val, by
        rw [← componentEquiv_old p q a hnew hcut hold, x.property,
          componentEquiv_old p q a hnew hcut hold]⟩ := by
    apply Subtype.ext
    simpa only [orbitEnumeration_apply_val] using hiter
  rw [← he, Equiv.symm_apply_apply]
  rfl

end
end DirectGLSSW.SmoothingSubdividedCycles











