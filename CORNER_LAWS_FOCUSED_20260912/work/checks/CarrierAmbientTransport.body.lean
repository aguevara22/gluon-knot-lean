namespace SM.Carrier

/-- A bijectively invariant set is closed in both directions of an ambient
permutation, without any finiteness assumption. -/
theorem perm_bijOn_mem_iff {α : Type*} (f : Equiv.Perm α) (U : Set α)
    (hU : Set.BijOn f U U) (x : α) : f x ∈ U ↔ x ∈ U := by
  constructor
  · intro hx
    have hi : f⁻¹ (f x) ∈ U := hU.perm_inv.mapsTo hx
    simpa using hi
  · intro hx
    exact hU.mapsTo hx

/-- Agreement on one bijectively invariant set transports the entire orbit
of a member. The other endpoint is unrestricted; outside points are excluded
by integer-power invariance, not by an additional endpoint premise. -/
theorem sameCycle_congr_of_eqOn_bijOn {α : Type*} (f g : Equiv.Perm α) (U : Set α)
    (hU : Set.BijOn f U U) (he : Set.EqOn f g U)
    (x : α) (hx : x ∈ U) (y : α) : g.SameCycle x y ↔ f.SameCycle x y := by
  have hgU : Set.BijOn g U U := hU.congr he
  let hfM : ∀ z, f z ∈ U ↔ z ∈ U := perm_bijOn_mem_iff f U hU
  let hgM : ∀ z, g z ∈ U ↔ z ∈ U := perm_bijOn_mem_iff g U hgU
  have hs : f.subtypePerm hfM = g.subtypePerm hgM := by
    apply Equiv.ext
    intro z
    apply Subtype.ext
    exact he z.property
  constructor
  · rintro ⟨k, hk⟩
    have hy : y ∈ U := hk ▸ (hgU.perm_zpow k).mapsTo hx
    have hc : (g.subtypePerm hgM).SameCycle (⟨x, hx⟩ : U) (⟨y, hy⟩ : U) :=
      Equiv.Perm.sameCycle_subtypePerm.mpr ⟨k, hk⟩
    rw [← hs] at hc
    exact Equiv.Perm.sameCycle_subtypePerm.mp hc
  · rintro ⟨k, hk⟩
    have hy : y ∈ U := hk ▸ (hU.perm_zpow k).mapsTo hx
    have hc : (f.subtypePerm hfM).SameCycle (⟨x, hx⟩ : U) (⟨y, hy⟩ : U) :=
      Equiv.Perm.sameCycle_subtypePerm.mpr ⟨k, hk⟩
    rw [hs] at hc
    exact Equiv.Perm.sameCycle_subtypePerm.mp hc

/-- Local permutation agreement preserves a complete cycle on its marked set.
The result includes singleton cycles and requires no global permutation equality. -/
theorem isCycleOn_of_eqOn {α : Type*} (f g : Equiv.Perm α) (U : Set α)
    (hf : f.IsCycleOn U) (he : Set.EqOn f g U) : g.IsCycleOn U := by
  refine ⟨hf.1.congr he, ?_⟩
  intro x hx y hy
  exact (sameCycle_congr_of_eqOn_bijOn f g U hf.1 he x hx y).mpr (hf.2 hx hy)

variable {α : Type*} [DecidableEq α]

/-- Swapping the two displayed endpoint slots preserves local agreement with
an ambient permutation. Only membership in the literal parent list is used. -/
theorem splitList_ambient_swap_eqOn (f : Equiv.Perm α) (a b : α) (A B : List α)
    (he : Set.EqOn (a :: (A ++ b :: B)).formPerm f {x | x ∈ a :: (A ++ b :: B)}) :
    Set.EqOn ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b)
      (f * Equiv.swap a b) {x | x ∈ a :: (A ++ b :: B)} := by
  intro x hx
  change (a :: (A ++ b :: B)).formPerm (Equiv.swap a b x) = f (Equiv.swap a b x)
  apply he
  by_cases hxa : x = a
  · subst x
    simp
  · by_cases hxb : x = b
    · subst x
      simp
    · simpa only [Equiv.swap_apply_of_ne_of_ne hxa hxb] using hx

/-- The ambient switched successor has exactly the left split-list orbit,
even when the surrounding permutation has other moving components. -/
theorem splitList_ambient_left_sameCycle_iff (f : Equiv.Perm α) (a b : α) (A B : List α)
    (hN : (a :: (A ++ b :: B)).Nodup)
    (he : Set.EqOn (a :: (A ++ b :: B)).formPerm f {m | m ∈ a :: (A ++ b :: B)})
    (x : α) : (f * Equiv.swap a b).SameCycle a x ↔ x ∈ a :: B := by
  have heS := splitList_ambient_swap_eqOn f a b A B he
  have heL : Set.EqOn ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b)
      (f * Equiv.swap a b) {m | m ∈ a :: B} := by
    intro m hm
    apply heS
    rcases List.mem_cons.mp hm with rfl | hm
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a
        (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem b hm)))
  exact (sameCycle_congr_of_eqOn_bijOn _ _ {m | m ∈ a :: B}
    (splitList_left_isCycleOn a b A B hN).1 heL a List.mem_cons_self x).trans
      (splitList_left_sameCycle_iff a b A B hN x)

/-- The ambient switched successor has exactly the right split-list orbit;
its description includes a one-mark child when A is empty. -/
theorem splitList_ambient_right_sameCycle_iff (f : Equiv.Perm α) (a b : α) (A B : List α)
    (hN : (a :: (A ++ b :: B)).Nodup)
    (he : Set.EqOn (a :: (A ++ b :: B)).formPerm f {m | m ∈ a :: (A ++ b :: B)})
    (x : α) : (f * Equiv.swap a b).SameCycle b x ↔ x ∈ b :: A := by
  have heS := splitList_ambient_swap_eqOn f a b A B he
  have heR : Set.EqOn ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b)
      (f * Equiv.swap a b) {m | m ∈ b :: A} := by
    intro m hm
    apply heS
    rcases List.mem_cons.mp hm with rfl | hm
    · exact List.mem_cons_of_mem a (List.mem_append.mpr (Or.inr List.mem_cons_self))
    · exact List.mem_cons_of_mem a (List.mem_append.mpr (Or.inl hm))
  exact (sameCycle_congr_of_eqOn_bijOn _ _ {m | m ∈ b :: A}
    (splitList_right_isCycleOn a b A B hN).1 heR b List.mem_cons_self x).trans
      (splitList_right_sameCycle_iff a b A B hN x)

/-- The two incoming endpoints are separated in the actual ambient orbits,
not merely in the permutation formed by the isolated parent list. -/
theorem splitList_ambient_not_sameCycle (f : Equiv.Perm α) (a b : α) (A B : List α)
    (hN : (a :: (A ++ b :: B)).Nodup)
    (he : Set.EqOn (a :: (A ++ b :: B)).formPerm f {m | m ∈ a :: (A ++ b :: B)}) :
    ¬ (f * Equiv.swap a b).SameCycle a b := by
  intro hc
  have hb := (splitList_ambient_left_sameCycle_iff f a b A B hN he b).mp hc
  exact (splitList_child_data a b A B hN).2.2 hb List.mem_cons_self

/-- On the left child's actual members, the ambient successor follows that
child's own cyclic list. This is the pointwise form needed for inherited order. -/
theorem splitList_ambient_left_apply (f : Equiv.Perm α) (a b : α) (A B : List α)
    (hN : (a :: (A ++ b :: B)).Nodup)
    (he : Set.EqOn (a :: (A ++ b :: B)).formPerm f {m | m ∈ a :: (A ++ b :: B)})
    (x : α) (hx : x ∈ a :: B) :
    (f * Equiv.swap a b) x = (a :: B).formPerm x := by
  have hxL : x ∈ a :: (A ++ b :: B) := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a
        (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem b hx)))
  have hd := (splitList_child_data a b A B hN).2.2
  calc
    (f * Equiv.swap a b) x = ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b) x :=
      ((splitList_ambient_swap_eqOn f a b A B he) hxL).symm
    _ = (a :: B).formPerm x := by
      rw [splitList_identity a b A B hN, Equiv.Perm.mul_apply,
        List.formPerm_apply_of_notMem (fun hr => hd hx hr)]

/-- The other ambient child likewise follows its own inherited cyclic list. -/
theorem splitList_ambient_right_apply (f : Equiv.Perm α) (a b : α) (A B : List α)
    (hN : (a :: (A ++ b :: B)).Nodup)
    (he : Set.EqOn (a :: (A ++ b :: B)).formPerm f {m | m ∈ a :: (A ++ b :: B)})
    (x : α) (hx : x ∈ b :: A) :
    (f * Equiv.swap a b) x = (b :: A).formPerm x := by
  have hxL : x ∈ a :: (A ++ b :: B) := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_of_mem a (List.mem_append.mpr (Or.inr List.mem_cons_self))
    · exact List.mem_cons_of_mem a (List.mem_append.mpr (Or.inl hx))
  have hd := (splitList_child_data a b A B hN).2.2
  calc
    (f * Equiv.swap a b) x = ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b) x :=
      ((splitList_ambient_swap_eqOn f a b A B he) hxL).symm
    _ = (b :: A).formPerm x := by
      rw [splitList_identity a b A B hN,
        (formPerm_disjoint_of_disjoint (a :: B) (b :: A) hd).commute.eq,
        Equiv.Perm.mul_apply, List.formPerm_apply_of_notMem (fun hl => hd hl hx)]

end SM.Carrier
