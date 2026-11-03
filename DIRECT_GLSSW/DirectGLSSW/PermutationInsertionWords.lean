import DirectGLSSW.PermutationInsertion

set_option autoImplicit false

namespace DirectGLSSW.PermutationInsertion

open Equiv PermutationOrbits
attribute [local instance] Classical.propDecidable
universe u v
variable {α : Type u} {β : Type v}

noncomputable def insertedFibreEquiv (p : Perm α) (q : Perm β) (a : α) (b : β)
    (E : α ≃ {y : β // y ≠ b})
    (hb : q b = (E a).val)
    (hstep : ∀ x, q (E x).val = if p x = a then b else (E (p x)).val) :
    Option (Fibre p (componentOf p a)) ≃ Fibre q (componentOf q b) := by
  let f : Option (Fibre p (componentOf p a)) → Fibre q (componentOf q b) :=
    fun z => match z with
    | none => ⟨b, rfl⟩
    | some x => ⟨(E x.val).val, by
        rw [← insertedComponentEquiv_componentOf p q a b E hb hstep,
          x.property, insertedComponentEquiv_extra p q a b E hb hstep]⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    have hv := congrArg Subtype.val hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some y => exact False.elim ((E y.val).property hv.symm)
    | some x =>
        cases y with
        | none => exact False.elim ((E x.val).property hv)
        | some y =>
            apply congrArg some
            apply Subtype.ext
            exact E.injective (Subtype.ext hv)
  · intro y
    by_cases hy : y.val = b
    · exact ⟨none, Subtype.ext hy.symm⟩
    · let x := E.symm ⟨y.val, hy⟩
      have hx : (E x).val = y.val := congrArg Subtype.val (E.apply_symm_apply _)
      have hc : componentOf p x = componentOf p a := by
        apply (componentOf_eq_iff p x a).mpr
        apply Equiv.Perm.SameCycle.symm
        apply (extra_sameCycle_iff p q a b E hb hstep x).mp
        apply (componentOf_eq_iff q b _).mp
        rw [hx, y.property]
      exact ⟨some ⟨x, hc⟩, Subtype.ext hx⟩

theorem inserted_fibreCard [Fintype α] [Fintype β] (p : Perm α) (q : Perm β) (a : α) (b : β)
    (E : α ≃ {y : β // y ≠ b})
    (hb : q b = (E a).val)
    (hstep : ∀ x, q (E x).val = if p x = a then b else (E (p x)).val) :
    Fintype.card (Fibre q (componentOf q b)) =
      Fintype.card (Fibre p (componentOf p a)) + 1 := by
  rw [← Fintype.card_congr (insertedFibreEquiv p q a b E hb hstep)]
  exact Fintype.card_option

theorem pow_ne_self_of_lt_fibreCard [Fintype α] (p : Perm α) (x : α)
    {k : ℕ} (hk0 : 0 < k) (hk : k < Fintype.card (Fibre p (componentOf p x))) :
    (p ^ k) x ≠ x := by
  intro h
  have h0 : 0 < Fintype.card (Fibre p (componentOf p x)) := Fintype.card_pos
  have he : orbitEnumeration p x ⟨k, hk⟩ = orbitEnumeration p x ⟨0, h0⟩ := by
    apply Subtype.ext
    simpa only [orbitEnumeration_apply_val, pow_zero, Perm.one_apply] using h
  have hv := congrArg Fin.val ((orbitEnumeration p x).injective he)
  exact (Nat.ne_of_gt hk0) hv

theorem inserted_pow_beforeReturn [Fintype α] (p : Perm α) (q : Perm β) (a : α) (b : β)
    (E : α ≃ {y : β // y ≠ b})
    (hb : q b = (E a).val)
    (hstep : ∀ x, q (E x).val = if p x = a then b else (E (p x)).val) (k : ℕ)
    (hk : k < Fintype.card (Fibre p (componentOf p a))) :
    (q ^ (k + 1)) b = (E ((p ^ k) a)).val := by
  induction k with
  | zero => simpa using hb
  | succ k ih =>
      have hi := ih (by omega)
      have hn : p ((p ^ k) a) ≠ a := by
        simpa only [pow_succ', Perm.mul_apply] using
          pow_ne_self_of_lt_fibreCard p a (by omega) hk
      rw [pow_succ', Perm.mul_apply, hi, hstep, if_neg hn]
      rw [pow_succ', Perm.mul_apply]

theorem inserted_orbitWord [Fintype α] [Fintype β] (p : Perm α) (q : Perm β) (a : α) (b : β)
    (E : α ≃ {y : β // y ≠ b})
    (hb : q b = (E a).val)
    (hstep : ∀ x, q (E x).val = if p x = a then b else (E (p x)).val) :
    orbitWord q b = b :: (orbitWord p a).map (fun x => (E x).val) := by
  apply List.ext_getElem
  · simp only [orbitWord_length, List.length_cons, List.length_map,
      inserted_fibreCard p q a b E hb hstep]
  · intro i hi hj
    cases i with
    | zero => simp [orbitWord]
    | succ i =>
        have hi' : i < Fintype.card (Fibre p (componentOf p a)) := by
          simpa only [List.length_cons, List.length_map, orbitWord_length,
            Nat.succ_lt_succ_iff] using hj
        simpa [orbitWord, orbitEnumeration_apply_val] using
          inserted_pow_beforeReturn p q a b E hb hstep i hi'

noncomputable def unaffectedFibreEquiv (p : Perm α) (q : Perm β) (a : α) (b : β)
    (E : α ≃ {y : β // y ≠ b})
    (hb : q b = (E a).val)
    (hstep : ∀ x, q (E x).val = if p x = a then b else (E (p x)).val)
    (x : α) (hx : ¬ p.SameCycle x a) :
    Fibre p (componentOf p x) ≃ Fibre q (componentOf q (E x).val) := by
  let f : Fibre p (componentOf p x) → Fibre q (componentOf q (E x).val) :=
    fun y => ⟨(E y.val).val, by
      rw [← insertedComponentEquiv_componentOf p q a b E hb hstep,
        y.property, insertedComponentEquiv_componentOf p q a b E hb hstep]⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro y z hyz
    have hv : (E y.val).val = (E z.val).val :=
      congrArg (fun w : Fibre q (componentOf q (E x).val) => w.val) hyz
    apply Subtype.ext
    exact E.injective (Subtype.ext hv)
  · intro y
    have hy : y.val ≠ b := by
      intro he
      have hc := y.property
      rw [he] at hc
      have hp : componentOf p a = componentOf p x := by
        apply (insertedComponentEquiv p q a b E hb hstep).injective
        rw [insertedComponentEquiv_extra, insertedComponentEquiv_componentOf]
        exact hc
      exact hx ((componentOf_eq_iff p x a).mp hp.symm)
    let z := E.symm ⟨y.val, hy⟩
    have hz : (E z).val = y.val := congrArg Subtype.val (E.apply_symm_apply _)
    have hc : componentOf p z = componentOf p x := by
      apply (insertedComponentEquiv p q a b E hb hstep).injective
      rw [insertedComponentEquiv_componentOf, insertedComponentEquiv_componentOf,
        hz, y.property]
    exact ⟨⟨z, hc⟩, Subtype.ext hz⟩

theorem unaffected_fibreCard [Fintype α] [Fintype β] (p : Perm α) (q : Perm β) (a : α) (b : β)
    (E : α ≃ {y : β // y ≠ b})
    (hb : q b = (E a).val)
    (hstep : ∀ x, q (E x).val = if p x = a then b else (E (p x)).val)
    (x : α) (hx : ¬ p.SameCycle x a) :
    Fintype.card (Fibre q (componentOf q (E x).val)) =
      Fintype.card (Fibre p (componentOf p x)) :=
  (Fintype.card_congr (unaffectedFibreEquiv p q a b E hb hstep x hx)).symm

theorem unaffected_pow (p : Perm α) (q : Perm β) (a : α) (b : β)
    (E : α ≃ {y : β // y ≠ b})
    (hb : q b = (E a).val)
    (hstep : ∀ x, q (E x).val = if p x = a then b else (E (p x)).val)
    (x : α) (hx : ¬ p.SameCycle x a) (k : ℕ) :
    (q ^ k) (E x).val = (E ((p ^ k) x)).val := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hn : p ((p ^ k) x) ≠ a := by
        intro he
        apply hx
        apply (componentOf_eq_iff p x a).mp
        rw [← he, componentOf_apply, componentOf_pow_apply]
      rw [pow_succ', Perm.mul_apply, ih, hstep, if_neg hn]
      rw [pow_succ', Perm.mul_apply]

theorem unaffected_orbitWord [Fintype α] [Fintype β] (p : Perm α) (q : Perm β) (a : α) (b : β)
    (E : α ≃ {y : β // y ≠ b})
    (hb : q b = (E a).val)
    (hstep : ∀ x, q (E x).val = if p x = a then b else (E (p x)).val)
    (x : α) (hx : ¬ p.SameCycle x a) :
    orbitWord q (E x).val = (orbitWord p x).map (fun y => (E y).val) := by
  apply List.ext_getElem
  · simp only [orbitWord_length, List.length_map,
      unaffected_fibreCard p q a b E hb hstep x hx]
  · intro i hi hj
    simpa [orbitWord, orbitEnumeration_apply_val] using
      unaffected_pow p q a b E hb hstep x hx i

end DirectGLSSW.PermutationInsertion
