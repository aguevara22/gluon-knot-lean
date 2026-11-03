import DirectGLSSW.OrbitNormalization

set_option autoImplicit false

namespace DirectGLSSW.PermutationOrbits
open Equiv
universe u v
variable {α : Type u} {β : Type v}
variable [Fintype α] [Fintype β]

/-- An injective successor map transports every full orbit of its domain;
it need not cover unrelated target components. -/
theorem pow_map_of_embedding (p : Perm α) (q : Perm β)
    (e : α → β) (he : ∀ x, e (p x) = q (e x)) (n : ℕ) (x : α) :
    e ((p ^ n) x) = (q ^ n) (e x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, he, ih, pow_succ', Perm.mul_apply]

noncomputable def orbitFibreEquivOfEmbedding (p : Perm α) (q : Perm β)
    (e : α → β) (hinj : Function.Injective e)
    (he : ∀ x, e (p x) = q (e x)) (root : α) :
    Fibre p (componentOf p root) ≃ Fibre q (componentOf q (e root)) := by
  let f : Fibre p (componentOf p root) → Fibre q (componentOf q (e root)) :=
    fun x => ⟨e x.val, by
      apply (componentOf_eq_iff q _ _).2
      obtain ⟨n, hn⟩ := ((componentOf_eq_iff p _ _).1 x.property).exists_nat_pow_eq
      refine ⟨(n : ℤ), ?_⟩
      rw [zpow_natCast, ← pow_map_of_embedding p q e he, hn]⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    exact hinj (congrArg Subtype.val h)
  · intro y
    have hrel : q.SameCycle (e root) y.val :=
      (componentOf_eq_iff q _ _).1 y.property.symm
    obtain ⟨n, hn⟩ := hrel.exists_nat_pow_eq
    refine ⟨⟨(p ^ n) root, ?_⟩, ?_⟩
    · apply (componentOf_eq_iff p _ _).2
      exact (show p.SameCycle root ((p ^ n) root) from
        ⟨(n : ℤ), by simp only [zpow_natCast]⟩).symm
    · apply Subtype.ext
      exact (pow_map_of_embedding p q e he n root).trans hn

@[simp] theorem orbitFibreEquivOfEmbedding_val (p : Perm α) (q : Perm β)
    (e : α → β) (hinj : Function.Injective e)
    (he : ∀ x, e (p x) = q (e x)) (root : α)
    (x : Fibre p (componentOf p root)) :
    (orbitFibreEquivOfEmbedding p q e hinj he root x).val = e x.val := rfl

/-- Orbit-enumeration positions are unchanged under injective successor
transport, even when the target has additional components. -/
theorem orbitPosition_embedding (p : Perm α) (q : Perm β)
    (e : α → β) (hinj : Function.Injective e)
    (he : ∀ x, e (p x) = q (e x)) (root : α)
    (x : Fibre p (componentOf p root)) :
    ((orbitEnumeration q (e root)).symm
      (orbitFibreEquivOfEmbedding p q e hinj he root x)).val =
      ((orbitEnumeration p root).symm x).val := by
  let t := (orbitEnumeration p root).symm x
  let f := orbitFibreEquivOfEmbedding p q e hinj he root
  have hc := Fintype.card_congr f
  let s : Fin (Fintype.card (Fibre q (componentOf q (e root)))) := Fin.cast hc t
  have hp : (p ^ t.val) root = x.val := by
    have h := congrArg Subtype.val ((orbitEnumeration p root).apply_symm_apply x)
    simpa only [orbitEnumeration_apply_val] using h
  have hmap : orbitEnumeration q (e root) s = f x := by
    apply Subtype.ext
    rw [orbitEnumeration_apply_val, orbitFibreEquivOfEmbedding_val]
    change (q ^ t.val) (e root) = e x.val
    rw [← pow_map_of_embedding p q e he, hp]
  rw [← hmap, Equiv.symm_apply_apply]
  rfl

end DirectGLSSW.PermutationOrbits





