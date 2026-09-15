import Mathlib.GroupTheory.Perm.Cycle.Basic

namespace SM.Carrier

variable {α : Type*} [DecidableEq α]

/-- Adjacent-transposition products concatenate at their shared endpoint.
No distinctness assumption is needed for this algebraic identity. -/
theorem formPerm_append_shared (L R : List α) (a : α) :
    (L ++ a :: R).formPerm = (L ++ [a]).formPerm * (a :: R).formPerm := by
  induction L with
  | nil => simp
  | cons x L ih =>
    cases L with
    | nil => rfl
    | cons y L =>
      simpa only [List.cons_append, List.formPerm_cons_cons, mul_assoc] using
        congrArg (fun q : Equiv.Perm α => Equiv.swap x y * q) ih

/-- Relabelling a list conjugates its actual adjacent-transposition product. -/
theorem formPerm_map_perm (f : Equiv.Perm α) (L : List α) :
    (L.map f).formPerm = f * L.formPerm * f⁻¹ := by
  induction L with
  | nil => simp
  | cons x L ih =>
    cases L with
    | nil => simp
    | cons y L =>
      change Equiv.swap (f x) (f y) * ((y :: L).map f).formPerm =
        f * (Equiv.swap x y * (y :: L).formPerm) * f⁻¹
      rw [ih, Equiv.swap_apply_apply]
      simp [mul_assoc]

/-- Swapping an absent alternative head changes only the head of a cycle list. -/
theorem formPerm_conj_swap_head (a b : α) (L : List α)
    (ha : a ∉ L) (hb : b ∉ L) :
    Equiv.swap a b * (a :: L).formPerm * Equiv.swap a b = (b :: L).formPerm := by
  have hm : L.map (Equiv.swap a b) = L := by
    calc
      L.map (Equiv.swap a b) = L.map id := by
        apply List.map_congr_left
        intro x hx
        exact Equiv.swap_apply_of_ne_of_ne
          (fun he => ha (he ▸ hx)) (fun he => hb (he ▸ hx))
      _ = L := by simp
  simpa only [List.map_cons, Equiv.swap_apply_left, hm, Equiv.swap_inv] using
    (formPerm_map_perm (Equiv.swap a b) (a :: L)).symm

/-- Disjoint node lists give disjoint permutation supports, including singleton lists. -/
theorem formPerm_disjoint_of_disjoint (L R : List α) (h : L.Disjoint R) :
    Equiv.Perm.Disjoint L.formPerm R.formPerm := by
  intro x
  by_cases hx : x ∈ L
  · exact Or.inr (List.formPerm_apply_of_notMem (fun hr => h hx hr))
  · exact Or.inl (List.formPerm_apply_of_notMem hx)

/-- The two source split lists are duplicate-free and have disjoint node sets.
The original list's exact Nodup hypothesis supplies every endpoint exclusion. -/
theorem splitList_child_data (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) :
    (a :: B).Nodup ∧ (b :: A).Nodup ∧ (a :: B).Disjoint (b :: A) := by
  rcases List.nodup_cons.mp h with ⟨ha, hAB⟩
  rcases List.nodup_append'.mp hAB with ⟨hA, hbB, hAd⟩
  rcases List.nodup_cons.mp hbB with ⟨hb, hB⟩
  have haA : a ∉ A := fun hx => ha (List.mem_append.mpr (Or.inl hx))
  have haB : a ∉ B := fun hx =>
    ha (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem b hx)))
  have hab : a ≠ b := by
    intro he
    apply ha
    simp [he]
  have hbA : b ∉ A := fun hx => hAd hx List.mem_cons_self
  refine ⟨List.nodup_cons.mpr ⟨haB, hB⟩, List.nodup_cons.mpr ⟨hbA, hA⟩, ?_⟩
  intro x hx hy
  rcases List.mem_cons.mp hx with rfl | hx
  · rcases List.mem_cons.mp hy with he | hy
    · exact hab he
    · exact haA hy
  · rcases List.mem_cons.mp hy with rfl | hy
    · exact hb hx
    · exact hAd hy (List.mem_cons_of_mem b hx)

/-- Switching the two outgoing slots splits the concrete old cyclic list into
exactly the source's two products. Either open arc may be empty. -/
theorem splitList_identity (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) :
    (a :: (A ++ b :: B)).formPerm * Equiv.swap a b =
      (a :: B).formPerm * (b :: A).formPerm := by
  obtain ⟨haB, hbA, hd⟩ := splitList_child_data a b A B h
  have haA : a ∉ A := fun hx => h.notMem (List.mem_append.mpr (Or.inl hx))
  have hbB : b ∉ B := h.of_cons.of_append_right.notMem
  have hshort : ((a :: A) ++ [b]).Nodup := by
    have ht : (((a :: A) ++ [b]) ++ B).Nodup := by
      simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using h
    exact ht.of_append_left
  have hrotN : (b :: a :: A).Nodup := by
    simpa only [List.append_nil] using (List.nodup_middle.mp hshort)
  have hrot : ((a :: A) ++ [b]).formPerm = (b :: a :: A).formPerm := by
    simpa only [List.rotate_cons_succ, List.rotate_zero] using
      (List.formPerm_rotate_one (b :: a :: A) hrotN)
  have hconjA := formPerm_conj_swap_head a b A haA hbA.notMem
  have hconjB : Equiv.swap a b * (b :: B).formPerm * Equiv.swap a b =
      (a :: B).formPerm := by
    simpa only [Equiv.swap_comm b a] using
      (formPerm_conj_swap_head b a B hbB haB.notMem)
  calc
    (a :: (A ++ b :: B)).formPerm * Equiv.swap a b =
        (Equiv.swap a b * (a :: A).formPerm * (b :: B).formPerm) *
          Equiv.swap a b := by
      rw [show a :: (A ++ b :: B) = (a :: A) ++ b :: B from rfl,
        formPerm_append_shared, hrot, List.formPerm_cons_cons, Equiv.swap_comm b a]
    _ = (Equiv.swap a b * (a :: A).formPerm * Equiv.swap a b) *
        (Equiv.swap a b * (b :: B).formPerm * Equiv.swap a b) := by
      simp [mul_assoc]
    _ = (b :: A).formPerm * (a :: B).formPerm := by rw [hconjA, hconjB]
    _ = (a :: B).formPerm * (b :: A).formPerm :=
      (formPerm_disjoint_of_disjoint (a :: B) (b :: A) hd).commute.eq.symm

/-- A product with a disjoint list cycle remains a cycle on the first node set.
The proof uses integer powers and includes one-node cycles. -/
theorem formPerm_mul_isCycleOn_left (L R : List α) (hL : L.Nodup)
    (hd : L.Disjoint R) :
    (L.formPerm * R.formPerm).IsCycleOn {x | x ∈ L} := by
  have hc := hL.isCycleOn_formPerm
  have hfix : ∀ x ∈ L, R.formPerm x = x := fun x hx =>
    List.formPerm_apply_of_notMem (fun hr => hd hx hr)
  have hz (x : α) (hx : x ∈ L) (k : ℤ) :
      ((L.formPerm * R.formPerm) ^ k) x = (L.formPerm ^ k) x := by
    rw [(formPerm_disjoint_of_disjoint L R hd).commute.mul_zpow,
      Equiv.Perm.mul_apply,
      Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (hfix x hx) k]
  refine ⟨hc.1.congr ?_, ?_⟩
  · intro x hx
    exact (show (L.formPerm * R.formPerm) x = L.formPerm x by
      rw [Equiv.Perm.mul_apply, hfix x hx]).symm
  · intro x hx y hy
    obtain ⟨k, hk⟩ := hc.2 hx hy
    exact ⟨k, (hz x hx k).trans hk⟩

/-- The child containing the incoming endpoint a is the complete cycle a,B. -/
theorem splitList_left_isCycleOn (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) :
    ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b).IsCycleOn
      {x | x ∈ a :: B} := by
  obtain ⟨hL, hR, hd⟩ := splitList_child_data a b A B h
  rw [splitList_identity a b A B h]
  exact formPerm_mul_isCycleOn_left (a :: B) (b :: A) hL hd

/-- The child containing the incoming endpoint b is the complete cycle b,A. -/
theorem splitList_right_isCycleOn (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) :
    ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b).IsCycleOn
      {x | x ∈ b :: A} := by
  obtain ⟨hL, hR, hd⟩ := splitList_child_data a b A B h
  rw [splitList_identity a b A B h,
    (formPerm_disjoint_of_disjoint (a :: B) (b :: A) hd).commute.eq]
  exact formPerm_mul_isCycleOn_left (b :: A) (a :: B) hR hd.symm

/-- The entire successor orbit of a is exactly its source split list. -/
theorem splitList_left_sameCycle_iff (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) (x : α) :
    ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b).SameCycle a x ↔
      x ∈ a :: B := by
  have hc := splitList_left_isCycleOn a b A B h
  constructor
  · rintro ⟨k, rfl⟩
    exact (hc.1.perm_zpow k).mapsTo List.mem_cons_self
  · intro hx
    exact hc.2 List.mem_cons_self hx

/-- The entire successor orbit of b is exactly its source split list. -/
theorem splitList_right_sameCycle_iff (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) (x : α) :
    ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b).SameCycle b x ↔
      x ∈ b :: A := by
  have hc := splitList_right_isCycleOn a b A B h
  constructor
  · rintro ⟨k, rfl⟩
    exact (hc.1.perm_zpow k).mapsTo List.mem_cons_self
  · intro hx
    exact hc.2 List.mem_cons_self hx

/-- The two incoming endpoint marks belong to different successor orbits. -/
theorem splitList_not_sameCycle (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) :
    ¬ ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b).SameCycle a b := by
  intro hc
  have hb := (splitList_left_sameCycle_iff a b A B h b).mp hc
  exact (splitList_child_data a b A B h).2.2 hb List.mem_cons_self

end SM.Carrier


namespace SM.Carrier

/-- A bijectively invariant set is closed in both directions of an ambient
permutation, without any finiteness assumption. -/
theorem perm_bijOn_mem_iff {α : Type*} (f : Equiv.Perm α) (U : Set α)
    (hU : Set.BijOn f U U) (x : α) : f x ∈ U ↔ x ∈ U := by
  constructor
  · intro hx
    have hi : f⁻¹ (f x) ∈ U := hU.perm_inv.mapsTo hx
    simpa using hi
  · exact hU.mapsTo

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


#print axioms SM.Carrier.perm_bijOn_mem_iff
#print axioms SM.Carrier.sameCycle_congr_of_eqOn_bijOn
#print axioms SM.Carrier.isCycleOn_of_eqOn
#print axioms SM.Carrier.splitList_ambient_swap_eqOn
#print axioms SM.Carrier.splitList_ambient_left_sameCycle_iff
#print axioms SM.Carrier.splitList_ambient_right_sameCycle_iff
#print axioms SM.Carrier.splitList_ambient_not_sameCycle
#print axioms SM.Carrier.splitList_ambient_left_apply
#print axioms SM.Carrier.splitList_ambient_right_apply
