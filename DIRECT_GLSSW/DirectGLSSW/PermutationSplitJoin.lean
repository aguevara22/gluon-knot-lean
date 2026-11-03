import DirectGLSSW.InvariantOrbitPartition
import DirectGLSSW.FiniteCycleSplit
import DirectGLSSW.OrbitNormalization

/-!
# Arbitrary finite permutation split and join
Preproof transcription: STATEMENTS.md. Source motivation: frozen lines 131–139.
Only the permutation prerequisite; no nonalternation or geometric claim.
-/
set_option autoImplicit false
namespace DirectGLSSW.PermutationOrbits
open Equiv
universe u
variable {α : Type u}

/-- A same-orbit endpoint swap preserves each original component label. -/
theorem componentOf_mul_swap [DecidableEq α] (p : Perm α) {a b : α}
    (hab : p.SameCycle a b) (x : α) :
    componentOf p ((p * swap a b) x) = componentOf p x := by
  rw [Perm.mul_apply, componentOf_apply]
  by_cases hxa : x = a
  · subst x
    simpa using ((componentOf_eq_iff p a b).2 hab).symm
  by_cases hxb : x = b
  · subst x
    simpa using (componentOf_eq_iff p a b).2 hab
  simp [swap_apply_of_ne_of_ne hxa hxb]

/-- Every new orbit is contained in one old orbit when both endpoints were together. -/
theorem sameCycle_mul_swap_refines [Fintype α] [DecidableEq α] (p : Perm α)
    {a b x y : α} (hab : p.SameCycle a b)
    (hxy : (p * swap a b).SameCycle x y) : p.SameCycle x y := by
  obtain ⟨i, hi⟩ := hxy.exists_nat_pow_eq
  have hc : ∀ j : ℕ, componentOf p (((p * swap a b) ^ j) x) = componentOf p x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ', Perm.mul_apply, componentOf_mul_swap p hab, ih]
  exact (componentOf_eq_iff p x y).1 (by rw [← hi, hc])

/-- The actual old endpoint fibre is invariant under the swapped successor. -/
theorem swap_fibre_invariant [DecidableEq α] (p : Perm α) {a b : α}
    (hab : p.SameCycle a b) (x : α) :
    componentOf p x = componentOf p a ↔
      componentOf p ((p * swap a b) x) = componentOf p a := by
  rw [componentOf_mul_swap p hab]

/-- Swapped successor restricted to the entire actual old endpoint fibre. -/
def swapFibrePerm [DecidableEq α] (p : Perm α) (a b : α)
    (hab : p.SameCycle a b) : Perm (Fibre p (componentOf p a)) :=
  (p * swap a b).subtypePerm (swap_fibre_invariant p hab)

@[simp] theorem swapFibrePerm_apply_val [DecidableEq α] (p : Perm α) (a b : α)
    (hab : p.SameCycle a b) (x : Fibre p (componentOf p a)) :
    (swapFibrePerm p a b hab x).val = (p * swap a b) x.val := rfl

/-- On the complement of the affected old fibre, the permutations agree literally. -/
theorem restrictPerm_mul_swap_complement [DecidableEq α] (p : Perm α) (a b : α)
    (hab : p.SameCycle a b) :
    restrictPerm (p * swap a b) {x | componentOf p x = componentOf p a}ᶜ
        (fun x => not_congr (swap_fibre_invariant p hab x)) =
      restrictPerm p {x | componentOf p x = componentOf p a}ᶜ
        (fun x => by simp) := by
  ext x
  apply mul_swap_apply_of_ne p
  · intro h
    apply x.property
    change componentOf p x.val = componentOf p a
    rw [h]
  · intro h
    exact x.property (by simpa [h] using ((componentOf_eq_iff p a b).2 hab).symm)

/-- The swapped restriction of an actual old fibre has exactly the two
endpoint orbits, and its full component quotient has cardinality two. -/
theorem swapFibrePerm_split [Fintype α] [DecidableEq α] (p : Perm α) (a b : α)
    (hne : a ≠ b) (hab : p.SameCycle a b) :
    let a₀ : Fibre p (componentOf p a) := ⟨a, rfl⟩
    let b₀ : Fibre p (componentOf p a) :=
      ⟨b, ((componentOf_eq_iff p a b).2 hab).symm⟩
    ¬(swapFibrePerm p a b hab).SameCycle a₀ b₀ ∧
      (∀ x, (swapFibrePerm p a b hab).SameCycle a₀ x ∨
        (swapFibrePerm p a b hab).SameCycle b₀ x) ∧
      componentCount (swapFibrePerm p a b hab) = 2 := by
  classical
  dsimp only
  let a₀ : Fibre p (componentOf p a) := ⟨a, rfl⟩
  let b₀ : Fibre p (componentOf p a) :=
    ⟨b, ((componentOf_eq_iff p a b).2 hab).symm⟩
  let e := orbitEnumeration p a
  let k := e.symm b₀
  have he0 : e 0 = a₀ := by
    apply Subtype.ext
    exact orbitEnumeration_zero p a
  have hek : e k = b₀ := e.apply_symm_apply b₀
  have hk : k ≠ 0 := by
    intro h
    have he := hek.symm.trans ((congrArg e h).trans he0)
    exact hne (congrArg Subtype.val he).symm
  have he : ∀ i, e (FiniteCycleSplit.cutPerm k i) =
      swapFibrePerm p a b hab (e i) := by
    intro i
    change e (cyclicSuccessorPerm _ (swap 0 k i)) = _
    rw [orbitEnumeration_successor]
    apply Subtype.ext
    simp only [fibrePerm_apply_val, swapFibrePerm_apply_val, Perm.mul_apply]
    have hs := (Subtype.val_injective.comp e.injective).map_swap 0 k i
    simpa only [Function.comp_apply, show (e 0).val = a from congrArg Subtype.val he0,
      show (e k).val = b from congrArg Subtype.val hek] using congrArg p hs
  have ht := sameCycle_iff_of_intertwining e (FiniteCycleSplit.cutPerm k)
    (swapFibrePerm p a b hab) he
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h' : (FiniteCycleSplit.cutPerm k).SameCycle 0 k :=
      (ht 0 k).2 (by simpa only [he0, hek] using h)
    have hc := (FiniteCycleSplit.cut_sameCycle_zero_iff k k).1 h'
    rw [FiniteCycleSplit.cutSide_mark k hk] at hc
    contradiction
  · intro x
    cases hc : FiniteCycleSplit.cutSide k (e.symm x) with
    | false =>
        left
        have h := (ht 0 (e.symm x)).1
          ((FiniteCycleSplit.cut_sameCycle_zero_iff k (e.symm x)).2 hc)
        simpa only [he0, e.apply_symm_apply] using h
    | true =>
        right
        have h := (ht k (e.symm x)).1
          ((FiniteCycleSplit.cut_sameCycle_mark_iff k hk (e.symm x)).2 hc)
        simpa only [hek, e.apply_symm_apply] using h
  · rw [← componentCount_eq_of_intertwining e (FiniteCycleSplit.cutPerm k)
        (swapFibrePerm p a b hab) he]
    exact FiniteCycleSplit.cut_componentCount k hk

/-- Distinct endpoints in one original orbit lie in different new orbits. -/
theorem not_sameCycle_mul_swap_of_sameCycle [Fintype α] [DecidableEq α]
    (p : Perm α) {a b : α} (hne : a ≠ b) (hab : p.SameCycle a b) :
    ¬(p * swap a b).SameCycle a b := by
  intro h
  apply (swapFibrePerm_split p a b hne hab).1
  exact Perm.sameCycle_subtypePerm.mpr h

/-- The complete old endpoint orbit is exactly the union of the two new endpoint orbits. -/
theorem sameCycle_split_iff [Fintype α] [DecidableEq α] (p : Perm α)
    {a b : α} (hne : a ≠ b) (hab : p.SameCycle a b) (x : α) :
    p.SameCycle a x ↔ (p * swap a b).SameCycle a x ∨
      (p * swap a b).SameCycle b x := by
  constructor
  · intro hx
    let x₀ : Fibre p (componentOf p a) :=
      ⟨x, ((componentOf_eq_iff p a x).2 hx).symm⟩
    rcases (swapFibrePerm_split p a b hne hab).2.1 x₀ with ha | hb
    · exact Or.inl (Perm.sameCycle_subtypePerm.mp ha)
    · exact Or.inr (Perm.sameCycle_subtypePerm.mp hb)
  · rintro (ha | hb)
    · exact sameCycle_mul_swap_refines p hab ha
    · exact hab.trans (sameCycle_mul_swap_refines p hab hb)

/-- Cutting one full orbit increases the full component count by one. -/
theorem componentCount_mul_swap_of_sameCycle [Fintype α] [DecidableEq α]
    (p : Perm α) {a b : α} (hne : a ≠ b) (hab : p.SameCycle a b) :
    componentCount (p * swap a b) = componentCount p + 1 := by
  classical
  let s : Set α := {x | componentOf p x = componentOf p a}
  have hp : ∀ x, x ∈ s ↔ p x ∈ s := by intro x; simp [s]
  have hq : ∀ x, x ∈ s ↔ (p * swap a b) x ∈ s := swap_fibre_invariant p hab
  have hpcount : componentCount (restrictPerm p s hp) = 1 :=
    componentCount_eq_one (fibrePerm p (componentOf p a)) (fibrePerm_isCycleOn p _)
  have hqcount : componentCount (restrictPerm (p * swap a b) s hq) = 2 :=
    (swapFibrePerm_split p a b hne hab).2.2
  have hcomp : restrictPerm (p * swap a b) sᶜ (fun x => not_congr (hq x)) =
      restrictPerm p sᶜ (fun x => not_congr (hp x)) :=
    restrictPerm_mul_swap_complement p a b hab
  rw [componentCount_invariant_partition p s hp,
    componentCount_invariant_partition (p * swap a b) s hq, hpcount, hqcount, hcomp]
  omega

/-- Return times are exactly multiples of the actual full orbit cardinality,
including a fixed point's cardinality one. -/
theorem pow_apply_eq_self_iff_fibre_card_dvd [Fintype α] (p : Perm α) (b : α) (j : ℕ) :
    (p ^ j) b = b ↔ Fintype.card (Fibre p (componentOf p b)) ∣ j := by
  classical
  let b₀ : Fibre p (componentOf p b) := ⟨b, rfl⟩
  have hp : (fibrePerm p (componentOf p b)).IsCycleOn
      (Finset.univ : Finset (Fibre p (componentOf p b))) := by
    simpa using fibrePerm_isCycleOn p (componentOf p b)
  have hv : ((fibrePerm p (componentOf p b)) ^ j) b₀ = b₀ ↔ (p ^ j) b = b := by
    constructor
    · intro h
      simpa only [fibrePerm_pow_apply_val] using congrArg Subtype.val h
    · intro h
      apply Subtype.ext
      simpa only [fibrePerm_pow_apply_val] using h
  rw [← hv]
  simpa only [Finset.card_univ] using hp.pow_apply_eq (Finset.mem_univ b₀)

/-- After moving from a to p(b), the new traversal follows the entire old
b-orbit through its closing step; the cardinality-one case is included. -/
theorem join_traversal [Fintype α] [DecidableEq α] (p : Perm α) {a b : α}
    (hab : ¬p.SameCycle a b) (j : ℕ) (hj : 1 ≤ j)
    (hjd : j ≤ Fintype.card (Fibre p (componentOf p b))) :
    ((p * swap a b) ^ j) a = (p ^ j) b := by
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases hj0 : j = 0
      · subst j
        simp
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hjlt : j < Fintype.card (Fibre p (componentOf p b)) := by omega
      have ha : (p ^ j) b ≠ a := by
        intro h
        apply hab
        exact (show p.SameCycle b a from ⟨(j : ℤ), by simpa using h⟩).symm
      have hb : (p ^ j) b ≠ b := by
        intro h
        have hdvd := (pow_apply_eq_self_iff_fibre_card_dvd p b j).1 h
        exact (Nat.not_dvd_of_pos_of_lt hjpos hjlt) hdvd
      rw [pow_succ', Perm.mul_apply, ih (by omega) (by omega),
        mul_swap_apply_of_ne p ha hb, pow_succ', Perm.mul_apply]

/-- Distinct old orbits become one: a bounded closing traversal is the witness. -/
theorem sameCycle_mul_swap_of_not_sameCycle [Fintype α] [DecidableEq α]
    (p : Perm α) {a b : α} (hab : ¬p.SameCycle a b) :
    (p * swap a b).SameCycle a b := by
  let d := Fintype.card (Fibre p (componentOf p b))
  have hd : 1 ≤ d := Fintype.card_pos
  have hclose : (p ^ d) b = b :=
    (pow_apply_eq_self_iff_fibre_card_dvd p b d).2 dvd_rfl
  refine ⟨(d : ℤ), ?_⟩
  simpa only [zpow_natCast, join_traversal p hab d hd (le_refl d)] using hclose

/-- The joined orbit is exactly the union of both complete original endpoint orbits. -/
theorem sameCycle_join_iff [Fintype α] [DecidableEq α] (p : Perm α)
    {a b : α} (hab : ¬p.SameCycle a b) (x : α) :
    (p * swap a b).SameCycle a x ↔ p.SameCycle a x ∨ p.SameCycle b x := by
  have hne : a ≠ b := fun h => hab (h.sameCycle p)
  have hjoin := sameCycle_mul_swap_of_not_sameCycle p hab
  simpa only [mul_assoc, swap_mul_self, mul_one] using
    sameCycle_split_iff (p * swap a b) hne hjoin x

/-- Joining two old orbits decreases the full component count by one,
expressed additively so no truncated subtraction is involved. -/
theorem componentCount_mul_swap_of_not_sameCycle [Fintype α] [DecidableEq α]
    (p : Perm α) {a b : α} (hab : ¬p.SameCycle a b) :
    componentCount (p * swap a b) + 1 = componentCount p := by
  have hne : a ≠ b := fun h => hab (h.sameCycle p)
  have hjoin := sameCycle_mul_swap_of_not_sameCycle p hab
  simpa only [mul_assoc, swap_mul_self, mul_one] using
    (componentCount_mul_swap_of_sameCycle (p * swap a b) hne hjoin).symm

/-- In a join, each entire old orbit lies in one new orbit. -/
theorem sameCycle_mul_swap_coarsens [Fintype α] [DecidableEq α] (p : Perm α)
    {a b x y : α} (hab : ¬p.SameCycle a b) (hxy : p.SameCycle x y) :
    (p * swap a b).SameCycle x y := by
  have hjoin := sameCycle_mul_swap_of_not_sameCycle p hab
  apply sameCycle_mul_swap_refines (p * swap a b) hjoin
  simpa only [mul_assoc, swap_mul_self, mul_one] using hxy

/-- Any endpoint swap adds at most one full component; coincident endpoints
are allowed and then the permutation is unchanged. -/
theorem componentCount_mul_swap_le [Fintype α] [DecidableEq α]
    (p : Perm α) (a b : α) :
    componentCount (p * swap a b) ≤ componentCount p + 1 := by
  by_cases hne : a = b
  · subst b
    simp
  by_cases hab : p.SameCycle a b
  · rw [componentCount_mul_swap_of_sameCycle p hne hab]
  · have h := componentCount_mul_swap_of_not_sameCycle p hab
    omega

end DirectGLSSW.PermutationOrbits
