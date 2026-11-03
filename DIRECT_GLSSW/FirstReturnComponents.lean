import DirectGLSSW.OrbitNormalization

set_option autoImplicit false
namespace DirectGLSSW.FirstReturnComponents
open Equiv PermutationOrbits
noncomputable section
universe u v
variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]
variable (p : Perm α) (q : Perm β) (E : β → α) (hE : Function.Injective E)
variable (K : α → Prop) (hK : ∀ x, K (E x))
variable (hret : ∀ x, ∃ d : ℕ, 0 < d ∧ (p ^ d) (E x) = E (q x) ∧
  ∀ k : ℕ, 0 < k → k < d → ¬ K ((p ^ k) (E x)))

include hret in
theorem sameCycle_map (x y : β) (h : q.SameCycle x y) :
    p.SameCycle (E x) (E y) := by
  obtain ⟨m,hm⟩ := h.exists_nat_pow_eq
  subst y
  clear h
  induction m with
  | zero => exact Perm.SameCycle.refl p (E x)
  | succ m ih =>
    obtain ⟨d,_,hd,_⟩ := hret ((q ^ m) x)
    have hs : p.SameCycle (E ((q ^ m) x)) (E (q ((q ^ m) x))) := by
      exact ⟨(d : ℤ), by simpa only [zpow_natCast] using hd⟩
    simpa only [pow_succ',Perm.mul_apply] using ih.trans hs

include hE hK hret in
theorem sameCycle_of_pow_eq (m : ℕ) (x y : β) (hm : (p ^ m) (E x) = E y) :
    q.SameCycle x y := by
  induction m using Nat.strong_induction_on generalizing x y with
  | h m ih =>
    by_cases hm0 : m = 0
    · subst m
      have hxy : x = y := hE hm
      exact hxy.sameCycle q
    · obtain ⟨d,hd0,hd,hno⟩ := hret x
      have hdm : d ≤ m := by
        by_contra h
        have hn := hno m (by omega) (by omega)
        rw [hm] at hn
        exact hn (hK y)
      have hm' : (p ^ (m-d)) (E (q x)) = E y := by
        rw [← hd,← Perm.mul_apply,← pow_add,Nat.sub_add_cancel hdm]
        exact hm
      have hr := ih (m-d) (by omega) (q x) y hm'
      have hs : q.SameCycle x (q x) := by
        exact ⟨(1 : ℤ), by simp⟩
      exact hs.trans hr

include hE hK hret in
theorem sameCycle_iff (x y : β) :
    q.SameCycle x y ↔ p.SameCycle (E x) (E y) := by
  constructor
  · exact sameCycle_map p q E K hret x y
  · intro h
    obtain ⟨m,hm⟩ := h.exists_nat_pow_eq
    exact sameCycle_of_pow_eq p q E hE K hK hret m x y hm

def componentMap : Component q → Component p :=
  Quotient.lift (fun x => componentOf p (E x)) (fun x y h =>
    (componentOf_eq_iff p _ _).mpr (sameCycle_map p q E K hret x y h))

@[simp] theorem componentMap_componentOf (x : β) :
    componentMap p q E K hret (componentOf q x) = componentOf p (E x) := rfl

include hE hK in
theorem componentMap_injective : Function.Injective (componentMap p q E K hret) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h x =>
    induction b using Quotient.inductionOn with
    | h y =>
      intro h
      exact (componentOf_eq_iff q x y).mpr
        ((sameCycle_iff p q E hE K hK hret x y).mpr ((componentOf_eq_iff p _ _).mp h))







end
end DirectGLSSW.FirstReturnComponents
