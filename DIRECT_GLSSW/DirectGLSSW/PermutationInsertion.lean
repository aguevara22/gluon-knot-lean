import DirectGLSSW.IndexedInvariantPartition

set_option autoImplicit false

namespace DirectGLSSW.PermutationInsertion

open Equiv PermutationOrbits
attribute [local instance] Classical.propDecidable

universe u v
variable {α : Type u} {β : Type v}

noncomputable def dropPoint (a : α) (b : β)
    (E : α ≃ {y : β // y ≠ b}) (y : β) : α :=
  if h : y = b then a else E.symm ⟨y, h⟩

theorem dropPoint_lift (a : α) (b : β)
    (E : α ≃ {y : β // y ≠ b}) (x : α) :
    dropPoint a b E (E x).val = x := by
  simp [dropPoint, (E x).property]

theorem dropPoint_extra (a : α) (b : β)
    (E : α ≃ {y : β // y ≠ b}) : dropPoint a b E b = a := by
  simp [dropPoint]

variable (p : Perm α) (q : Perm β) (a : α) (b : β)
    (E : α ≃ {y : β // y ≠ b})
    (hb : q b = (E a).val)
    (hstep : ∀ x, q (E x).val = if p x = a then b else (E (p x)).val)

include hb hstep

theorem mapped_component_step (x : α) :
    componentOf q (E (p x)).val = componentOf q (E x).val := by
  by_cases h : p x = a
  · have hs : q (E x).val = b := by simpa [h] using hstep x
    calc
      componentOf q (E (p x)).val = componentOf q (E a).val := by rw [h]
      _ = componentOf q (q b) := by rw [hb]
      _ = componentOf q b := componentOf_apply q b
      _ = componentOf q (q (E x).val) := by rw [hs]
      _ = componentOf q (E x).val := componentOf_apply q (E x).val
  · have hs : q (E x).val = (E (p x)).val := by simpa [h] using hstep x
    rw [← hs, componentOf_apply]

theorem mapped_sameCycle {x y : α} (hxy : p.SameCycle x y) :
    q.SameCycle (E x).val (E y).val := by
  apply (componentOf_eq_iff q _ _).mp
  exact IndexedInvariantPartition.index_eq_of_sameCycle p
    (fun z => componentOf q (E z).val)
    (mapped_component_step p q a b E hb hstep) hxy

theorem drop_component_step (y : β) :
    componentOf p (dropPoint a b E (q y)) =
      componentOf p (dropPoint a b E y) := by
  by_cases hy : y = b
  · subst y
    rw [hb, dropPoint_lift, dropPoint_extra]
  · let x : α := E.symm ⟨y, hy⟩
    have hx : (E x).val = y := congrArg Subtype.val (E.apply_symm_apply ⟨y, hy⟩)
    rw [← hx, hstep]
    by_cases h : p x = a
    · simp only [if_pos h, dropPoint_extra, dropPoint_lift]
      rw [← h, componentOf_apply]
    · simp only [if_neg h, dropPoint_lift]
      exact componentOf_apply p x

noncomputable def insertedComponentEquiv : Component p ≃ Component q where
  toFun := Quotient.map (fun x => (E x).val)
    (fun _ _ h => mapped_sameCycle p q a b E hb hstep h)
  invFun := Quotient.lift (fun y => componentOf p (dropPoint a b E y))
    (fun _ _ h => IndexedInvariantPartition.index_eq_of_sameCycle q
      (fun y => componentOf p (dropPoint a b E y))
      (drop_component_step p q a b E hb hstep) h)
  left_inv := by
    intro c
    refine Quotient.inductionOn c ?_
    intro x
    change componentOf p (dropPoint a b E (E x).val) = componentOf p x
    rw [dropPoint_lift]
  right_inv := by
    intro c
    refine Quotient.inductionOn c ?_
    intro y
    change componentOf q (E (dropPoint a b E y)).val = componentOf q y
    by_cases hy : y = b
    · subst y
      rw [dropPoint_extra, ← hb, componentOf_apply]
    · simp only [dropPoint, dif_neg hy]
      have hx := congrArg Subtype.val (E.apply_symm_apply ⟨y, hy⟩)
      rw [hx]

theorem insertedComponentEquiv_componentOf (x : α) :
    insertedComponentEquiv p q a b E hb hstep (componentOf p x) =
      componentOf q (E x).val := rfl

theorem insertedComponentEquiv_extra :
    insertedComponentEquiv p q a b E hb hstep (componentOf p a) =
      componentOf q b := by
  rw [insertedComponentEquiv_componentOf, ← hb, componentOf_apply]

theorem inserted_sameCycle_iff (x y : α) :
    q.SameCycle (E x).val (E y).val ↔ p.SameCycle x y := by
  rw [← componentOf_eq_iff, ← componentOf_eq_iff,
    ← insertedComponentEquiv_componentOf p q a b E hb hstep x,
    ← insertedComponentEquiv_componentOf p q a b E hb hstep y]
  exact (insertedComponentEquiv p q a b E hb hstep).injective.eq_iff

theorem extra_sameCycle_iff (x : α) :
    q.SameCycle b (E x).val ↔ p.SameCycle a x := by
  rw [← componentOf_eq_iff, ← componentOf_eq_iff,
    ← insertedComponentEquiv_extra p q a b E hb hstep,
    ← insertedComponentEquiv_componentOf p q a b E hb hstep x]
  exact (insertedComponentEquiv p q a b E hb hstep).injective.eq_iff

theorem inserted_componentCount [Fintype α] [Fintype β] :
    componentCount p = componentCount q :=
  Fintype.card_congr (insertedComponentEquiv p q a b E hb hstep)

end DirectGLSSW.PermutationInsertion
