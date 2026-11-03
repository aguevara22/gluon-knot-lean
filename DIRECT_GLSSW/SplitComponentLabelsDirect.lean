import HOMFLYCutUnaffectedOrder

set_option autoImplicit false

namespace DirectGLSSW.PermutationOrbits
open Equiv

noncomputable def cutComponentSumEquiv
    {α : Type} [Fintype α] [DecidableEq α] (p : Perm α)
    (a b : α) (hne : a ≠ b)
    (hab : p.SameCycle a b) :
    Component (p * swap a b) ≃
      Bool ⊕ {C : Component p // C ≠ componentOf p a} := by
  classical
  let q := p * swap a b
  let label : α → Bool ⊕ {C : Component p // C ≠ componentOf p a} := fun x =>
    if h : componentOf p x = componentOf p a then
      if q.SameCycle a x then Sum.inl false else Sum.inl true
    else Sum.inr ⟨componentOf p x, h⟩
  have hlabel : ∀ x y, q.SameCycle x y → label x = label y := by
    intro x y hxy
    have hp : componentOf p x = componentOf p y :=
      (componentOf_eq_iff p x y).2 (sameCycle_mul_swap_refines p hab hxy)
    have hq : q.SameCycle a x ↔ q.SameCycle a y :=
      ⟨fun h => h.trans hxy, fun h => h.trans hxy.symm⟩
    simp only [label, hp, hq]
  let f : Component q → Bool ⊕ {C : Component p // C ≠ componentOf p a} :=
    Quotient.lift label hlabel
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro X Y h
    obtain ⟨x, rfl⟩ := Quotient.exists_rep X
    obtain ⟨y, rfl⟩ := Quotient.exists_rep Y
    change label x = label y at h
    apply (componentOf_eq_iff q x y).2
    by_cases hx : componentOf p x = componentOf p a
    · by_cases hy : componentOf p y = componentOf p a
      · by_cases hax : q.SameCycle a x
        · have hay : q.SameCycle a y := by
            by_contra hnot
            simp only [label, dif_pos hx, dif_pos hy, if_pos hax, if_neg hnot, Sum.inl.injEq, Bool.false_eq_true] at h
          exact hax.symm.trans hay
        · have hay : ¬ q.SameCycle a y := by
            intro hay
            simp only [label, dif_pos hx, dif_pos hy, if_neg hax, if_pos hay, Sum.inl.injEq, Bool.true_eq_false] at h
          have hpx : p.SameCycle a x := (componentOf_eq_iff p a x).1 hx.symm
          have hpy : p.SameCycle a y := (componentOf_eq_iff p a y).1 hy.symm
          have hbx := ((sameCycle_split_iff p hne hab x).1 hpx).resolve_left hax
          have hby := ((sameCycle_split_iff p hne hab y).1 hpy).resolve_left hay
          exact hbx.symm.trans hby
      · simp only [label, dif_pos hx, dif_neg hy] at h
        split_ifs at h
    · by_cases hy : componentOf p y = componentOf p a
      · simp only [label, dif_neg hx, dif_pos hy] at h
        split_ifs at h
      · have hp : componentOf p x = componentOf p y := by
          have hh : (⟨componentOf p x, hx⟩ : {C : Component p // C ≠ componentOf p a}) = ⟨componentOf p y, hy⟩ := by
            simpa only [label, dif_neg hx, dif_neg hy, Sum.inr.injEq] using h
          exact congrArg Subtype.val hh
        have hxa : ¬ p.SameCycle x a := fun h => hx ((componentOf_eq_iff p x a).2 h)
        have hxb : ¬ p.SameCycle x b := fun h => hxa (h.trans hab.symm)
        exact (cutUnaffected_sameCycle p a b x y hxa hxb).2
          ((componentOf_eq_iff p x y).1 hp)
  · intro z
    cases z with
    | inl u =>
      cases u with
      | false =>
        refine ⟨componentOf q a, ?_⟩
        change label a = _
        simp [label, Perm.SameCycle.refl]
      | true =>
        refine ⟨componentOf q b, ?_⟩
        change label b = _
        have hp : componentOf p b = componentOf p a := ((componentOf_eq_iff p a b).2 hab).symm
        have hq : ¬ q.SameCycle a b := not_sameCycle_mul_swap_of_sameCycle p hne hab
        simp only [label, dif_pos hp, if_neg hq]
    | inr C =>
      let x := Classical.choice (fibreNonempty p C.val)
      refine ⟨componentOf q x.val, ?_⟩
      change label x.val = _
      have hx : componentOf p x.val ≠ componentOf p a := by simpa only [x.property] using C.property
      simp only [label, dif_neg hx]
      congr 1
      exact Subtype.ext x.property

@[simp] theorem cutComponentSumEquiv_left
    {α : Type} [Fintype α] [DecidableEq α] (p : Perm α)
    (a b : α) (hne : a ≠ b)
    (hab : p.SameCycle a b) :
    cutComponentSumEquiv p a b hne hab (componentOf (p * swap a b) a) = Sum.inl false := by
  classical
  change (if h : componentOf p a = componentOf p a then
    if (p * swap a b).SameCycle a a then Sum.inl false else Sum.inl true
    else Sum.inr (⟨componentOf p a, h⟩ : {C : Component p // C ≠ componentOf p a})) = _
  simp only [dif_pos rfl, if_pos (Perm.SameCycle.refl _ _), dite_true]

@[simp] theorem cutComponentSumEquiv_right
    {α : Type} [Fintype α] [DecidableEq α] (p : Perm α)
    (a b : α) (hne : a ≠ b)
    (hab : p.SameCycle a b) :
    cutComponentSumEquiv p a b hne hab (componentOf (p * swap a b) b) = Sum.inl true := by
  classical
  have hp : componentOf p b = componentOf p a := ((componentOf_eq_iff p a b).2 hab).symm
  have hq : ¬ (p * swap a b).SameCycle a b := not_sameCycle_mul_swap_of_sameCycle p hne hab
  change (if h : componentOf p b = componentOf p a then
    if (p * swap a b).SameCycle a b then Sum.inl false else Sum.inl true
    else Sum.inr (⟨componentOf p b, h⟩ : {C : Component p // C ≠ componentOf p a})) = _
  simp only [dif_pos hp, if_neg hq]

@[simp] theorem cutComponentSumEquiv_other
    {α : Type} [Fintype α] [DecidableEq α] (p : Perm α)
    (a b x : α) (hne : a ≠ b)
    (hab : p.SameCycle a b)
    (hx : componentOf p x ≠ componentOf p a) :
    cutComponentSumEquiv p a b hne hab (componentOf (p * swap a b) x) =
      Sum.inr ⟨componentOf p x, hx⟩ := by
  classical
  change (if h : componentOf p x = componentOf p a then
    if (p * swap a b).SameCycle a x then Sum.inl false else Sum.inl true
    else Sum.inr (⟨componentOf p x, h⟩ : {C : Component p // C ≠ componentOf p a})) = _
  simp only [dif_neg hx]

end DirectGLSSW.PermutationOrbits





