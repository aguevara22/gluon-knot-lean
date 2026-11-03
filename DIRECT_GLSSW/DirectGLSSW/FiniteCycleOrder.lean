import DirectGLSSW.OrderedEventSuccessor
import DirectGLSSW.InvariantOrbitPartition

/-!
# Inherited order of the two actual daughter cycles

Source motivation: frozen note lines 131–139, with context 61–154.
Arbitrary ordered endpoints, literal interval subtypes and actual successor
restrictions. This is not the full nonalternation or geometric realization
claim. Pre-proof transcription is in the author's STATEMENTS.md.
-/

set_option autoImplicit false

namespace DirectGLSSW.FiniteCycleOrder

open Equiv
open scoped Classical

variable {m : ℕ}

/-- The literal half-open interval `(a,b]` in the parent labels. -/
def intervalSide (a b : Fin m) : Set (Fin m) := {i | a.val < i.val ∧ i.val ≤ b.val}

/-- The other daughter consists of the actual complement of `(a,b]`. -/
def complementSide (a b : Fin m) : Set (Fin m) := (intervalSide a b)ᶜ

/-- Cut the parent successor at the two specified outgoing labels. -/
noncomputable def splitPerm (a b : Fin m) : Perm (Fin m) :=
  cyclicSuccessorPerm m * swap a b

/-- Both daughter lengths are positive, even in either singleton case. -/
theorem daughterLengths_pos (a b : Fin m) (hab : a < b) :
    0 < b.val - a.val ∧ 0 < m - (b.val - a.val) := by
  have := b.isLt
  change a.val < b.val at hab
  omega

/-- At a, the new successor takes b's old outgoing step, including wrap. -/
theorem splitPerm_apply_left (a b : Fin m) :
    (splitPerm a b a).val = (b.val + 1) % m := by
  simp [splitPerm, cyclicSuccessor, cyclicVertexIndex]

/-- At b, the successor returns to the first label strictly after a. -/
theorem splitPerm_apply_right (a b : Fin m) (hab : a < b) :
    (splitPerm a b b).val = a.val + 1 := by
  have ha : a.val + 1 < m := by have := b.isLt; change a.val < b.val at hab; omega
  simp [splitPerm, cyclicSuccessor, cyclicVertexIndex, Nat.mod_eq_of_lt ha]

/-- All other labels retain their original successor. -/
theorem splitPerm_apply_of_ne (a b i : Fin m) (hia : i ≠ a) (hib : i ≠ b) :
    (splitPerm a b i).val = (i.val + 1) % m := by
  simp [splitPerm, swap_apply_of_ne_of_ne hia hib, cyclicSuccessor, cyclicVertexIndex]

/-- Membership in the actual interval is invariant under the literal cut. -/
theorem intervalSide_invariant (a b : Fin m) (hab : a < b) (i : Fin m) :
    i ∈ intervalSide a b ↔ splitPerm a b i ∈ intervalSide a b := by
  change (a.val < i.val ∧ i.val ≤ b.val) ↔
    (a.val < (splitPerm a b i).val ∧ (splitPerm a b i).val ≤ b.val)
  have hb := b.isLt
  have hi := i.isLt
  change a.val < b.val at hab
  by_cases hia : i = a
  · subst i
    rw [splitPerm_apply_left]
    by_cases hw : b.val + 1 < m
    · rw [Nat.mod_eq_of_lt hw]
      omega
    · have he : b.val + 1 = m := by omega
      rw [he, Nat.mod_self]
      omega
  by_cases hib : i = b
  · subst i
    rw [splitPerm_apply_right a b hab]
    omega
  rw [splitPerm_apply_of_ne a b i hia hib]
  have hia' : i.val ≠ a.val := fun h => hia (Fin.ext h)
  have hib' : i.val ≠ b.val := fun h => hib (Fin.ext h)
  by_cases hw : i.val + 1 < m
  · rw [Nat.mod_eq_of_lt hw]
    omega
  · have he : i.val + 1 = m := by omega
    rw [he, Nat.mod_self]
    omega

/-- The actual complementary daughter is invariant too. -/
theorem complementSide_invariant (a b : Fin m) (hab : a < b) (i : Fin m) :
    i ∈ complementSide a b ↔ splitPerm a b i ∈ complementSide a b :=
  not_congr (intervalSide_invariant a b hab i)

/-- Increasing enumeration of the actual interval daughter. -/
def intervalOrderIso (a b : Fin m) (hab : a < b) :
    Fin (b.val - a.val) ≃o intervalSide a b where
  toFun j := ⟨⟨a.val + 1 + j.val, by have := j.isLt; have := b.isLt; change a.val < b.val at hab; omega⟩,
    by change a.val < a.val + 1 + j.val ∧ a.val + 1 + j.val ≤ b.val; have := j.isLt; omega⟩
  invFun i := ⟨i.val.val - a.val - 1, by
    have hi : a.val < i.val.val ∧ i.val.val ≤ b.val := i.property
    omega⟩
  left_inv j := by apply Fin.ext; dsimp; have := j.isLt; omega
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    dsimp
    have hi : a.val < i.val.val ∧ i.val.val ≤ b.val := i.property
    omega
  map_rel_iff' := by intro i j; change a.val + 1 + i.val ≤ a.val + 1 + j.val ↔ i.val ≤ j.val; omega

/-- Increasing enumeration of the actual complementary daughter, skipping the gap. -/
def complementOrderIso (a b : Fin m) (hab : a < b) :
    Fin (m - (b.val - a.val)) ≃o complementSide a b where
  toFun j := ⟨⟨if j.val ≤ a.val then j.val else j.val + (b.val - a.val), by
    have := j.isLt
    have := b.isLt
    change a.val < b.val at hab
    split_ifs <;> omega⟩, by
      change ¬ (a.val < (if j.val ≤ a.val then j.val else j.val + (b.val - a.val)) ∧
        (if j.val ≤ a.val then j.val else j.val + (b.val - a.val)) ≤ b.val)
      change a.val < b.val at hab
      split_ifs <;> omega⟩
  invFun i := ⟨if i.val.val ≤ a.val then i.val.val else i.val.val - (b.val - a.val), by
    have hi : ¬ (a.val < i.val.val ∧ i.val.val ≤ b.val) := i.property
    have := i.val.isLt
    have := b.isLt
    change a.val < b.val at hab
    split_ifs <;> omega⟩
  left_inv j := by
    apply Fin.ext
    dsimp
    have := j.isLt
    change a.val < b.val at hab
    split_ifs <;> omega
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    dsimp
    have hi : ¬ (a.val < i.val.val ∧ i.val.val ≤ b.val) := i.property
    change a.val < b.val at hab
    split_ifs <;> omega
  map_rel_iff' := by
    intro i j
    change (if i.val ≤ a.val then i.val else i.val + (b.val - a.val)) ≤
      (if j.val ≤ a.val then j.val else j.val + (b.val - a.val)) ↔ i.val ≤ j.val
    split_ifs <;> omega

@[simp] theorem intervalOrderIso_apply_val (a b : Fin m) (hab : a < b)
    (j : Fin (b.val - a.val)) :
    (intervalOrderIso a b hab j).val.val = a.val + 1 + j.val := rfl

@[simp] theorem intervalOrderIso_symm_apply_val (a b : Fin m) (hab : a < b)
    (i : intervalSide a b) :
    ((intervalOrderIso a b hab).symm i).val = i.val.val - a.val - 1 := rfl

@[simp] theorem complementOrderIso_apply_val (a b : Fin m) (hab : a < b)
    (j : Fin (m - (b.val - a.val))) :
    (complementOrderIso a b hab j).val.val =
      if j.val ≤ a.val then j.val else j.val + (b.val - a.val) := rfl

@[simp] theorem complementOrderIso_symm_apply_val (a b : Fin m) (hab : a < b)
    (i : complementSide a b) :
    ((complementOrderIso a b hab).symm i).val =
      if i.val.val ≤ a.val then i.val.val else i.val.val - (b.val - a.val) := rfl

/-- The literal interval subtype restriction, using the proved invariant iff. -/
noncomputable def intervalPerm (a b : Fin m) (hab : a < b) :
    Perm (intervalSide a b) :=
  PermutationOrbits.restrictPerm (splitPerm a b) (intervalSide a b)
    (intervalSide_invariant a b hab)

/-- The literal complementary subtype restriction. -/
noncomputable def complementPerm (a b : Fin m) (hab : a < b) :
    Perm (complementSide a b) :=
  PermutationOrbits.restrictPerm (splitPerm a b) (complementSide a b)
    (complementSide_invariant a b hab)

@[simp] theorem intervalPerm_apply_val (a b : Fin m) (hab : a < b)
    (i : intervalSide a b) : (intervalPerm a b hab i).val = splitPerm a b i.val := rfl

@[simp] theorem complementPerm_apply_val (a b : Fin m) (hab : a < b)
    (i : complementSide a b) : (complementPerm a b hab i).val = splitPerm a b i.val := rfl

/-- On the interval, the cut is its actual increasing successor and final wrap. -/
theorem intervalPerm_eq_orderedCyclicSuccessor (a b : Fin m) (hab : a < b) :
    intervalPerm a b hab = orderedCyclicSuccessor (intervalSide a b) := by
  apply Equiv.ext
  intro i
  symm
  apply orderedCyclicSuccessor_eq_of_order_spec
  have hi : a.val < i.val.val ∧ i.val.val ≤ b.val := i.property
  have hia : i.val ≠ a := by intro he; have := congrArg Fin.val he; omega
  by_cases hib : i.val = b
  · have hv : (intervalPerm a b hab i).val.val = a.val + 1 := by
      rw [intervalPerm_apply_val, hib, splitPerm_apply_right a b hab]
    right
    constructor
    · intro z
      have hz : a.val < z.val.val ∧ z.val.val ≤ b.val := z.property
      change z.val.val ≤ i.val.val
      have := congrArg Fin.val hib
      omega
    · intro z
      have hz : a.val < z.val.val ∧ z.val.val ≤ b.val := z.property
      change (intervalPerm a b hab i).val.val ≤ z.val.val
      rw [hv]
      omega
  · have hib' : i.val.val ≠ b.val := fun h => hib (Fin.ext h)
    have hv : (intervalPerm a b hab i).val.val = i.val.val + 1 := by
      rw [intervalPerm_apply_val, splitPerm_apply_of_ne a b i.val hia hib,
        Nat.mod_eq_of_lt (by have := b.isLt; omega)]
    left
    constructor
    · change i.val.val < (intervalPerm a b hab i).val.val
      rw [hv]
      omega
    · intro z hz
      change (intervalPerm a b hab i).val.val ≤ z.val.val
      change i.val.val < z.val.val at hz
      rw [hv]
      omega

/-- On the complement, the cut walks over the gap and wraps in inherited order. -/
theorem complementPerm_eq_orderedCyclicSuccessor (a b : Fin m) (hab : a < b) :
    complementPerm a b hab = orderedCyclicSuccessor (complementSide a b) := by
  apply Equiv.ext
  intro i
  symm
  apply orderedCyclicSuccessor_eq_of_order_spec
  have hi : ¬ (a.val < i.val.val ∧ i.val.val ≤ b.val) := i.property
  have hb := b.isLt
  have hib : i.val ≠ b := by
    intro he
    have := congrArg Fin.val he
    change a.val < b.val at hab
    omega
  by_cases hia : i.val = a
  · have hv : (complementPerm a b hab i).val.val = (b.val + 1) % m := by
      rw [complementPerm_apply_val, hia, splitPerm_apply_left]
    have hia' := congrArg Fin.val hia
    by_cases hw : b.val + 1 < m
    · rw [Nat.mod_eq_of_lt hw] at hv
      left
      constructor
      · change i.val.val < (complementPerm a b hab i).val.val
        change a.val < b.val at hab
        omega
      · intro z hz
        have hz' : ¬ (a.val < z.val.val ∧ z.val.val ≤ b.val) := z.property
        change i.val.val < z.val.val at hz
        change (complementPerm a b hab i).val.val ≤ z.val.val
        omega
    · have he : b.val + 1 = m := by omega
      rw [he, Nat.mod_self] at hv
      right
      constructor
      · intro z
        have hz : ¬ (a.val < z.val.val ∧ z.val.val ≤ b.val) := z.property
        have := z.val.isLt
        change z.val.val ≤ i.val.val
        omega
      · intro z
        change (complementPerm a b hab i).val.val ≤ z.val.val
        omega
  · have hv : (complementPerm a b hab i).val.val = (i.val.val + 1) % m := by
      rw [complementPerm_apply_val, splitPerm_apply_of_ne a b i.val hia hib]
    by_cases hw : i.val.val + 1 < m
    · rw [Nat.mod_eq_of_lt hw] at hv
      left
      constructor
      · change i.val.val < (complementPerm a b hab i).val.val
        omega
      · intro z hz
        change i.val.val < z.val.val at hz
        change (complementPerm a b hab i).val.val ≤ z.val.val
        omega
    · have he : i.val.val + 1 = m := by have := i.val.isLt; omega
      rw [he, Nat.mod_self] at hv
      right
      constructor
      · intro z
        have := z.val.isLt
        change z.val.val ≤ i.val.val
        omega
      · intro z
        change (complementPerm a b hab i).val.val ≤ z.val.val
        omega

/-- The explicit increasing interval map intertwines the actual successors. -/
theorem intervalOrderIso_successor (a b : Fin m) (hab : a < b)
    (j : Fin (b.val - a.val)) :
    intervalPerm a b hab (intervalOrderIso a b hab j) =
      intervalOrderIso a b hab (cyclicSuccessorPerm (b.val - a.val) j) := by
  rw [intervalPerm_eq_orderedCyclicSuccessor,
    orderedCyclicSuccessor_naturality, orderedCyclicSuccessor_fin]
  rfl

/-- The complementary map intertwines actual successors, including gap and wrap. -/
theorem complementOrderIso_successor (a b : Fin m) (hab : a < b)
    (j : Fin (m - (b.val - a.val))) :
    complementPerm a b hab (complementOrderIso a b hab j) =
      complementOrderIso a b hab (cyclicSuccessorPerm (m - (b.val - a.val)) j) := by
  rw [complementPerm_eq_orderedCyclicSuccessor,
    orderedCyclicSuccessor_naturality, orderedCyclicSuccessor_fin]
  rfl

/-- The strict circular order induced by a strict linear order. -/
def strictCyclicBetween {α : Type*} [LT α] (x y z : α) : Prop :=
  (x < y ∧ y < z) ∨ (y < z ∧ z < x) ∨ (z < x ∧ x < y)

/-- Increasing order isomorphisms preserve and reflect the exact relation. -/
theorem strictCyclicBetween_orderIso {α β : Type*} [LinearOrder α] [LinearOrder β]
    (e : α ≃o β) (x y z : α) :
    strictCyclicBetween (e x) (e y) (e z) ↔ strictCyclicBetween x y z := by
  simp only [strictCyclicBetween, e.lt_iff_lt]

/-- Actual subtype inclusion preserves and reflects strict circular order. -/
theorem strictCyclicBetween_subtype {α : Type*} [LinearOrder α] (s : Set α)
    (x y z : s) :
    strictCyclicBetween x.val y.val z.val ↔ strictCyclicBetween x y z := Iff.rfl

/-- The interval daughter's Fin coordinates have exactly the inherited circle order. -/
theorem intervalOrderIso_strictCyclicBetween (a b : Fin m) (hab : a < b)
    (x y z : Fin (b.val - a.val)) :
    strictCyclicBetween (intervalOrderIso a b hab x).val (intervalOrderIso a b hab y).val
      (intervalOrderIso a b hab z).val ↔ strictCyclicBetween x y z :=
  strictCyclicBetween_orderIso (intervalOrderIso a b hab) x y z

/-- The complementary daughter's Fin coordinates have the inherited circle order. -/
theorem complementOrderIso_strictCyclicBetween (a b : Fin m) (hab : a < b)
    (x y z : Fin (m - (b.val - a.val))) :
    strictCyclicBetween (complementOrderIso a b hab x).val (complementOrderIso a b hab y).val
      (complementOrderIso a b hab z).val ↔ strictCyclicBetween x y z :=
  strictCyclicBetween_orderIso (complementOrderIso a b hab) x y z

/-- The full orbit relation is exactly agreement on the two literal sides. -/
theorem split_sameCycle_iff (a b : Fin m) (hab : a < b) (x y : Fin m) :
    (splitPerm a b).SameCycle x y ↔
      (x ∈ intervalSide a b ↔ y ∈ intervalSide a b) := by
  constructor
  · exact PermutationOrbits.mem_iff_of_sameCycle (splitPerm a b) (intervalSide a b)
      (intervalSide_invariant a b hab)
  · intro hxy
    by_cases hx : x ∈ intervalSide a b
    · have hy := hxy.mp hx
      have hc : (intervalPerm a b hab).SameCycle (⟨x, hx⟩ : intervalSide a b) ⟨y, hy⟩ := by
        rw [intervalPerm_eq_orderedCyclicSuccessor]
        exact (orderedCyclicSuccessor_isCycleOn (intervalSide a b)).2 (Set.mem_univ _) (Set.mem_univ _)
      exact (Perm.sameCycle_subtypePerm (h := intervalSide_invariant a b hab)).mp hc
    · have hy : y ∈ complementSide a b := fun hy => hx (hxy.mpr hy)
      have hc : (complementPerm a b hab).SameCycle (⟨x, hx⟩ : complementSide a b) ⟨y, hy⟩ := by
        rw [complementPerm_eq_orderedCyclicSuccessor]
        exact (orderedCyclicSuccessor_isCycleOn (complementSide a b)).2 (Set.mem_univ _) (Set.mem_univ _)
      exact (Perm.sameCycle_subtypePerm (h := complementSide_invariant a b hab)).mp hc

/-- The daughter containing a is exactly the complementary side, singleton allowed. -/
theorem split_sameCycle_left_iff (a b : Fin m) (hab : a < b) (i : Fin m) :
    (splitPerm a b).SameCycle a i ↔ i ∈ complementSide a b := by
  rw [split_sameCycle_iff a b hab]
  simp only [intervalSide, complementSide, Set.mem_compl_iff, Set.mem_setOf_eq, lt_self_iff_false,
    false_and, false_iff]

/-- The daughter containing b is exactly the interval side, singleton allowed. -/
theorem split_sameCycle_right_iff (a b : Fin m) (hab : a < b) (i : Fin m) :
    (splitPerm a b).SameCycle b i ↔ i ∈ intervalSide a b := by
  rw [split_sameCycle_iff a b hab]
  have hb : b ∈ intervalSide a b := ⟨hab, le_rfl⟩
  simp only [hb, true_iff]

/-- The selected endpoints lie in different actual daughter orbits. -/
theorem split_endpoints_separated (a b : Fin m) (hab : a < b) :
    ¬ (splitPerm a b).SameCycle a b := by
  rw [split_sameCycle_left_iff a b hab]
  exact fun h => h ⟨hab, le_rfl⟩

/-- With increasing endpoint labels the strict circular interval is literal. -/
theorem strictCyclicBetween_iff_of_lt {α : Type*} [LinearOrder α]
    (a b x : α) (hab : a < b) :
    strictCyclicBetween a x b ↔ a < x ∧ x < b := by
  constructor
  · intro h
    rcases h with h | h | h
    · exact h
    · exact False.elim ((lt_asymm hab) h.2)
    · exact False.elim ((lt_asymm hab) h.1)
  · exact Or.inl

/-- Away from b, strict betweenness equals the chosen half-open side label. -/
theorem strictCyclicBetween_iff_intervalSide (a b x : Fin m) (hab : a < b)
    (hxb : x ≠ b) :
    strictCyclicBetween a x b ↔ x ∈ intervalSide a b := by
  rw [strictCyclicBetween_iff_of_lt a b x hab]
  change (a.val < x.val ∧ x.val < b.val) ↔ (a.val < x.val ∧ x.val ≤ b.val)
  have hxb' : x.val ≠ b.val := fun h => hxb (Fin.ext h)
  omega

end DirectGLSSW.FiniteCycleOrder
