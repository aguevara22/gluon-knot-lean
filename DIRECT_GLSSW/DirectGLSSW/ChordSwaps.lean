import DirectGLSSW.PermutationSplitJoin
import Mathlib.Data.Finset.NoncommProd

/-! Actual products of disjoint endpoint swaps. Preproof types: STATEMENTS.md. -/
set_option autoImplicit false
namespace DirectGLSSW.ChordNonalternation
open Equiv PermutationOrbits
universe u v
variable {C : Type u} {α : Type v} [DecidableEq α]

/-- The literal endpoint transposition, with both branch labels retained. -/
def chordSwap (e : C × Bool → α) (c : C) : Perm α :=
  swap (e (c, false)) (e (c, true))

omit [DecidableEq α] in
theorem endpoints_ne (e : C × Bool → α) (he : Function.Injective e) (c : C) :
    e (c, false) ≠ e (c, true) := by
  intro h
  have := congrArg Prod.snd (he h)
  contradiction

omit [DecidableEq α] in
theorem endpoints_ne_of_ne (e : C × Bool → α) (he : Function.Injective e)
    {c d : C} (hcd : c ≠ d) (i j : Bool) : e (c,i) ≠ e (d,j) := by
  intro h
  exact hcd (congrArg Prod.fst (he h))

theorem chordSwap_disjoint (e : C × Bool → α) (he : Function.Injective e)
    {c d : C} (hcd : c ≠ d) : (chordSwap e c).Disjoint (chordSwap e d) := by
  intro x
  by_cases hc0 : x = e (c,false)
  · right
    subst x
    exact swap_apply_of_ne_of_ne (endpoints_ne_of_ne e he hcd false false)
      (endpoints_ne_of_ne e he hcd false true)
  by_cases hc1 : x = e (c,true)
  · right
    subst x
    exact swap_apply_of_ne_of_ne (endpoints_ne_of_ne e he hcd true false)
      (endpoints_ne_of_ne e he hcd true true)
  · left
    exact swap_apply_of_ne_of_ne hc0 hc1

theorem chordSwap_commute (e : C × Bool → α) (he : Function.Injective e)
    (c d : C) : Commute (chordSwap e c) (chordSwap e d) := by
  by_cases h : c = d
  · subst d
    exact Commute.refl _
  exact (chordSwap_disjoint e he h).commute

/-- Actual finite product, independent of the enumeration by proved commutation. -/
noncomputable def swapProduct (e : C × Bool → α) (he : Function.Injective e)
    (S : Finset C) : Perm α :=
  S.noncommProd (chordSwap e) (fun _ _ _ _ _ => chordSwap_commute e he _ _)

@[simp] theorem swapProduct_empty (e : C × Bool → α) (he : Function.Injective e) :
    swapProduct e he ∅ = 1 := rfl

@[simp] theorem swapProduct_singleton (e : C × Bool → α) (he : Function.Injective e) (c : C) :
    swapProduct e he {c} = chordSwap e c := Finset.noncommProd_singleton c (chordSwap e)

theorem swapProduct_insert [DecidableEq C] (e : C × Bool → α)
    (he : Function.Injective e) (S : Finset C) (c : C) (hc : c ∉ S) :
    swapProduct e he (insert c S) = chordSwap e c * swapProduct e he S :=
  Finset.noncommProd_insert_of_not_mem S c (chordSwap e) _ hc

theorem swapProduct_insert_right [DecidableEq C] (e : C × Bool → α)
    (he : Function.Injective e) (S : Finset C) (c : C) (hc : c ∉ S) :
    swapProduct e he (insert c S) = swapProduct e he S * chordSwap e c :=
  Finset.noncommProd_insert_of_not_mem' S c (chordSwap e) _ hc

theorem swapProduct_union [DecidableEq C] (e : C × Bool → α)
    (he : Function.Injective e) (S T : Finset C) (h : Disjoint S T) :
    swapProduct e he (S ∪ T) = swapProduct e he S * swapProduct e he T :=
  Finset.noncommProd_union_of_disjoint h (chordSwap e) _

theorem swapProduct_erase [DecidableEq C] (e : C × Bool → α)
    (he : Function.Injective e) (S : Finset C) (c : C) (hc : c ∈ S) :
    swapProduct e he S = chordSwap e c * swapProduct e he (S.erase c) :=
  (Finset.mul_noncommProd_erase S hc (chordSwap e) _).symm

theorem swapProduct_erase_right [DecidableEq C] (e : C × Bool → α)
    (he : Function.Injective e) (S : Finset C) (c : C) (hc : c ∈ S) :
    swapProduct e he S = swapProduct e he (S.erase c) * chordSwap e c :=
  (Finset.noncommProd_erase_mul S hc (chordSwap e) _).symm

/-- Each support swap adds at most one component of any finite base permutation. -/
theorem componentCount_mul_swapProduct_le [Fintype α] (e : C × Bool → α)
    (he : Function.Injective e) (p : Perm α) (S : Finset C) :
    componentCount (p * swapProduct e he S) ≤ componentCount p + S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert c S hc ih =>
      rw [swapProduct_insert_right e he S c hc, ← mul_assoc, Finset.card_insert_of_not_mem hc]
      have h := componentCount_mul_swap_le (p * swapProduct e he S) (e (c,false)) (e (c,true))
      change componentCount (p * swapProduct e he S * chordSwap e c) ≤ _ at h
      omega

/-- A swap whose endpoints agree in membership preserves the literal subset. -/
theorem mem_chordSwap_iff (e : C × Bool → α) (c : C) (A : Set α)
    (hc : e (c,false) ∈ A ↔ e (c,true) ∈ A) (x : α) :
    chordSwap e c x ∈ A ↔ x ∈ A := by
  by_cases h0 : x = e (c,false)
  · subst x
    simpa [chordSwap] using hc.symm
  by_cases h1 : x = e (c,true)
  · subst x
    simpa [chordSwap] using hc
  simp [chordSwap, swap_apply_of_ne_of_ne h0 h1]

/-- Literal membership is preserved by the complete concrete swap product. -/
theorem mem_swapProduct_iff (e : C × Bool → α) (he : Function.Injective e)
    (S : Finset C) (A : Set α)
    (hS : ∀ c ∈ S, e (c,false) ∈ A ↔ e (c,true) ∈ A) (x : α) :
    swapProduct e he S x ∈ A ↔ x ∈ A := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert c S hc ih =>
      rw [swapProduct_insert e he S c hc, Perm.mul_apply,
        mem_chordSwap_iff e c A (hS c (Finset.mem_insert_self _ _))]
      exact ih (fun d hd => hS d (Finset.mem_insert_of_mem hd))

/-- Every unused event label is fixed, so unused anchors are literal survivors. -/
theorem swapProduct_apply_of_avoids (e : C × Bool → α) (he : Function.Injective e)
    (S : Finset C) (x : α)
    (hx : ∀ c ∈ S, x ≠ e (c,false) ∧ x ≠ e (c,true)) : swapProduct e he S x = x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert c S hc ih =>
      rw [swapProduct_insert e he S c hc, Perm.mul_apply,
        ih (fun d hd => hx d (Finset.mem_insert_of_mem hd))]
      exact swap_apply_of_ne_of_ne (hx c (Finset.mem_insert_self _ _)).1
        (hx c (Finset.mem_insert_self _ _)).2

/-- Both endpoints of any unselected chord are fixed by the whole swap product. -/
theorem swapProduct_endpoint_of_not_mem (e : C × Bool → α) (he : Function.Injective e)
    (S : Finset C) (c : C) (hc : c ∉ S) (i : Bool) :
    swapProduct e he S (e (c,i)) = e (c,i) := by
  apply swapProduct_apply_of_avoids
  intro d hd
  have hcd : c ≠ d := fun h => hc (h ▸ hd)
  exact ⟨endpoints_ne_of_ne e he hcd i false, endpoints_ne_of_ne e he hcd i true⟩

/-- The left-swap convention also refines the actual same-component relation. -/
theorem sameCycle_swap_mul_refines [Fintype α] (p : Perm α)
    {a b x y : α} (hab : p.SameCycle a b)
    (hxy : (swap a b * p).SameCycle x y) : p.SameCycle x y := by
  obtain ⟨i, hi⟩ := hxy.exists_nat_pow_eq
  have hc : ∀ j : ℕ, componentOf p (((swap a b * p) ^ j) x) = componentOf p x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ', Perm.mul_apply]
        have hs := componentOf_mul_swap p hab (p (((swap a b * p) ^ j) x))
        simp only [Perm.mul_apply, componentOf_apply] at hs
        simpa only [Perm.mul_apply, hs] using ih
  exact (componentOf_eq_iff p x y).1 (by rw [← hi, hc])

/-- Every noduplicate list ordering realizes the same literal swap product. -/
theorem swapProduct_toFinset [DecidableEq C] (e : C × Bool → α)
    (he : Function.Injective e) (L : List C) (hL : L.Nodup) :
    swapProduct e he L.toFinset = (L.map (chordSwap e)).prod :=
  Finset.noncommProd_toFinset L (chordSwap e) _ hL

end DirectGLSSW.ChordNonalternation
