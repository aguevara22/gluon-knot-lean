import DirectGLSSW.PermutationOrbits
import Mathlib.Data.Fintype.Sum

/-!
# Components split over an invariant subset

Generic prerequisite only. `STATEMENTS.md` was written before this proof.
Source motivation: frozen note lines 131–139, not certification of its full
smoothing paragraph. No geometric component count or swap law is asserted.
-/

set_option autoImplicit false

namespace DirectGLSSW.PermutationOrbits

open Equiv
open scoped Classical

universe u
variable {α : Type u}

/-- The actual restriction of a successor to a successor-invariant subset. -/
def restrictPerm (p : Perm α) (s : Set α) (hs : ∀ x, x ∈ s ↔ p x ∈ s) : Perm s :=
  p.subtypePerm hs

@[simp] theorem restrictPerm_apply_val (p : Perm α) (s : Set α)
    (hs : ∀ x, x ∈ s ↔ p x ∈ s) (x : s) :
    (restrictPerm p s hs x).val = p x.val := rfl

/-- A successor-invariant subset is a union of entire `SameCycle` classes. -/
theorem mem_iff_of_sameCycle (p : Perm α) (s : Set α)
    (hs : ∀ x, x ∈ s ↔ p x ∈ s) {x y : α} (hxy : p.SameCycle x y) :
    x ∈ s ↔ y ∈ s := by
  have forward : ∀ {x y : α}, p.SameCycle x y → x ∈ s → y ∈ s := by
    intro x y h hx
    obtain ⟨i, hi⟩ := h
    have hm := ((restrictPerm p s hs ^ i) (⟨x, hx⟩ : s)).property
    have hv : (((restrictPerm p s hs ^ i) (⟨x, hx⟩ : s)) : α) = (p ^ i) x := by
      simp [restrictPerm]
    rw [hv, hi] at hm
    exact hm
  exact ⟨forward hxy, forward hxy.symm⟩

/-- Include a restricted component by including its actual underlying points. -/
def restrictComponentInclusion (p : Perm α) (s : Set α)
    (hs : ∀ x, x ∈ s ↔ p x ∈ s) :
    Component (restrictPerm p s hs) → Component p :=
  Quotient.map Subtype.val fun _ _ h => Perm.sameCycle_subtypePerm.mp h

@[simp] theorem restrictComponentInclusion_componentOf (p : Perm α) (s : Set α)
    (hs : ∀ x, x ∈ s ↔ p x ∈ s) (x : s) :
    restrictComponentInclusion p s hs (componentOf (restrictPerm p s hs) x) =
      componentOf p x.val := rfl

/-- Partition the full orbit quotient by an invariant subset and its complement.
The inverse sends either restricted class to its ambient class. -/
noncomputable def invariantPartitionEquiv (p : Perm α) (s : Set α)
    (hs : ∀ x, x ∈ s ↔ p x ∈ s) :
    Component p ≃ Component (restrictPerm p s hs) ⊕
      Component (restrictPerm p sᶜ (fun x => not_congr (hs x))) := by
  classical
  let hs' : ∀ x, x ∈ sᶜ ↔ p x ∈ sᶜ := fun x => not_congr (hs x)
  let f : α → Component (restrictPerm p s hs) ⊕ Component (restrictPerm p sᶜ hs') :=
    fun x => if hx : x ∈ s then Sum.inl (componentOf _ ⟨x, hx⟩)
      else Sum.inr (componentOf _ ⟨x, hx⟩)
  have hf : ∀ x y, p.SameCycle x y → f x = f y := by
    intro x y hxy
    have hmem := mem_iff_of_sameCycle p s hs hxy
    by_cases hx : x ∈ s
    · have hy := hmem.mp hx
      simp only [f, dif_pos hx, dif_pos hy]
      apply congrArg Sum.inl
      apply (componentOf_eq_iff _ _ _).2
      exact Perm.sameCycle_subtypePerm.mpr hxy
    · have hy : y ∉ s := fun hy => hx (hmem.mpr hy)
      simp only [f, dif_neg hx, dif_neg hy]
      apply congrArg Sum.inr
      apply (componentOf_eq_iff _ _ _).2
      exact Perm.sameCycle_subtypePerm.mpr hxy
  refine
    { toFun := Quotient.lift f hf
      invFun := Sum.elim (restrictComponentInclusion p s hs)
        (restrictComponentInclusion p sᶜ hs')
      left_inv := ?_
      right_inv := ?_ }
  · intro c
    induction c using Quotient.inductionOn with | h x =>
      change Sum.elim _ _ (f x) = componentOf p x
      by_cases hx : x ∈ s <;> simp [f, hx]
  · intro c
    cases c with
    | inl c =>
      induction c using Quotient.inductionOn with | h x =>
        change f x.val = Sum.inl (componentOf _ x)
        simp [f, x.property]
    | inr c =>
      induction c using Quotient.inductionOn with | h x =>
        change f x.val = Sum.inr (componentOf _ x)
        simp [f, show x.val ∉ s from x.property]

@[simp] theorem invariantPartitionEquiv_componentOf_mem (p : Perm α) (s : Set α)
    (hs : ∀ x, x ∈ s ↔ p x ∈ s) (x : α) (hx : x ∈ s) :
    invariantPartitionEquiv p s hs (componentOf p x) =
      Sum.inl (componentOf (restrictPerm p s hs) ⟨x, hx⟩) := by
  simp [invariantPartitionEquiv, hx, componentOf]

@[simp] theorem invariantPartitionEquiv_componentOf_not_mem (p : Perm α) (s : Set α)
    (hs : ∀ x, x ∈ s ↔ p x ∈ s) (x : α) (hx : x ∉ s) :
    invariantPartitionEquiv p s hs (componentOf p x) =
      Sum.inr (componentOf (restrictPerm p sᶜ (fun x => not_congr (hs x))) ⟨x, hx⟩) := by
  simp [invariantPartitionEquiv, hx, componentOf]

@[simp] theorem invariantPartitionEquiv_symm_inl (p : Perm α) (s : Set α)
    (hs : ∀ x, x ∈ s ↔ p x ∈ s) (c : Component (restrictPerm p s hs)) :
    (invariantPartitionEquiv p s hs).symm (Sum.inl c) =
      restrictComponentInclusion p s hs c := rfl

@[simp] theorem invariantPartitionEquiv_symm_inr (p : Perm α) (s : Set α)
    (hs : ∀ x, x ∈ s ↔ p x ∈ s)
    (c : Component (restrictPerm p sᶜ (fun x => not_congr (hs x)))) :
    (invariantPartitionEquiv p s hs).symm (Sum.inr c) =
      restrictComponentInclusion p sᶜ (fun x => not_congr (hs x)) c := rfl

/-- The additive count is a consequence of the explicit component equivalence. -/
theorem componentCount_invariant_partition [Fintype α] (p : Perm α) (s : Set α)
    (hs : ∀ x, x ∈ s ↔ p x ∈ s) :
    componentCount p = componentCount (restrictPerm p s hs) +
      componentCount (restrictPerm p sᶜ (fun x => not_congr (hs x))) := by
  classical
  simpa [componentCount] using Fintype.card_congr (invariantPartitionEquiv p s hs)

end DirectGLSSW.PermutationOrbits
