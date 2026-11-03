import DirectGLSSW.PermutationSplitJoin
import DirectGLSSW.OrderedEventSuccessor

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.PermutationOrbits
open Equiv
attribute [local instance] Classical.propDecidable
variable {α : Type*} [LinearOrder α] [Fintype α]

/-- A successor cut at a<b preserves exactly the half-open middle interval (a,b]. -/
theorem orderedCut_interval_step (a b x : α) (hab : a<b) :
    (a < (orderedCyclicSuccessor α * swap a b) x ∧
      (orderedCyclicSuccessor α * swap a b) x ≤ b) ↔ (a<x ∧ x≤b) := by
  by_cases hxa : x=a
  · subst x
    rw [mul_swap_apply_left]
    rcases orderedCyclicSuccessor_order_spec α b with ⟨hnext,_⟩ | ⟨_,hmin⟩
    · constructor
      · rintro ⟨_,h⟩;exact False.elim ((not_le_of_gt hnext) h)
      · rintro ⟨h,_⟩;exact False.elim (lt_irrefl _ h)
    · constructor
      · rintro ⟨h,_⟩;exact False.elim ((not_lt_of_ge (hmin a)) h)
      · rintro ⟨h,_⟩;exact False.elim (lt_irrefl _ h)
  by_cases hxb : x=b
  · subst x
    rw [mul_swap_apply_right]
    rcases orderedCyclicSuccessor_order_spec α a with ⟨hnext,hmin⟩ | ⟨hmax,_⟩
    · exact iff_of_true ⟨hnext,hmin b hab⟩ ⟨hab,le_rfl⟩
    · exact False.elim ((not_lt_of_ge (hmax b)) hab)
  rw [mul_swap_apply_of_ne _ hxa hxb]
  rcases orderedCyclicSuccessor_order_spec α x with ⟨hnext,hmin⟩ | ⟨hmax,hmin⟩
  · constructor
    · rintro ⟨ha,hb⟩
      have hax : a<x := by
        by_contra hn
        have hxa' : x<a := lt_of_le_of_ne (le_of_not_gt hn) hxa
        exact (not_lt_of_ge (hmin a hxa')) ha
      exact ⟨hax,(le_of_lt hnext).trans hb⟩
    · rintro ⟨ha,hb⟩
      exact ⟨ha.trans hnext,hmin b (lt_of_le_of_ne hb hxb)⟩
  · constructor
    · rintro ⟨h,_⟩;exact False.elim ((not_lt_of_ge (hmin a)) h)
    · rintro ⟨_,h⟩
      exact False.elim (hxb (le_antisymm h (hmax b)))

/-- The actual swapped successor's b-component is exactly (a,b], including b
and excluding a. No cycle-membership or interval hypothesis is supplied. -/
theorem orderedCut_sameCycle_right_iff (a b x : α) (hab : a<b) :
    (orderedCyclicSuccessor α * swap a b).SameCycle b x ↔ a<x ∧ x≤b := by
  let p := orderedCyclicSuccessor α * swap a b
  have hinv (y : α) (n : ℕ) : (a < (p ^ n) y ∧ (p ^ n) y ≤ b) ↔ (a<y ∧ y≤b) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',Perm.mul_apply]
      exact (orderedCut_interval_step a b ((p ^ n) y) hab).trans ih
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    rw [←hn]
    exact (hinv b n).mpr ⟨hab,le_rfl⟩
  · intro hx
    have hax := (orderedCyclicSuccessor_isCycleOn α).2 (Set.mem_univ a) (Set.mem_univ x)
    have habc := (orderedCyclicSuccessor_isCycleOn α).2 (Set.mem_univ a) (Set.mem_univ b)
    rcases (sameCycle_split_iff (orderedCyclicSuccessor α) (ne_of_lt hab) habc x).mp hax with ha|hb
    · obtain ⟨n,hn⟩ := ha.exists_nat_pow_eq
      have hf : a<a ∧ a≤b := (hinv a n).mp (by rw [hn];exact hx)
      exact False.elim (lt_irrefl _ hf.1)
    · exact hb
end DirectGLSSW.PermutationOrbits
