import DirectGLSSW.InvariantOrbitPartition
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false

namespace DirectGLSSW.IndexedInvariantPartition

open Equiv PermutationOrbits

universe u v
variable {α : Type u} {I : Type v}

/-- The actual points carrying one value of the invariant label. -/
def indexFiber (f : α → I) (i : I) : Set α := {x | f x = i}

/-- Each label fibre is invariant because the label is preserved by `p`. -/
theorem indexFiber_invariant (p : Equiv.Perm α) (f : α → I)
    (hf : ∀ x, f (p x) = f x) (i : I) (x : α) :
    x ∈ indexFiber f i ↔ p x ∈ indexFiber f i := by
  change (f x = i) ↔ (f (p x) = i)
  rw [hf x]

/-- Every invariant-index subtype is finite when the ambient type is finite. -/
noncomputable instance indexFiberFintype [Fintype α] (f : α → I) (i : I) :
    Fintype {x : α // x ∈ indexFiber f i} := by
  classical
  unfold indexFiber
  infer_instance

/-- Restrict the actual permutation to one entire invariant label fibre. -/
def indexRestrictedPerm (p : Equiv.Perm α) (f : α → I)
    (hf : ∀ x, f (p x) = f x) (i : I) :
    Equiv.Perm {x : α // x ∈ indexFiber f i} :=
  restrictPerm p (indexFiber f i) (indexFiber_invariant p f hf i)

@[simp] theorem indexRestrictedPerm_apply_val (p : Equiv.Perm α) (f : α → I)
    (hf : ∀ x, f (p x) = f x) (i : I)
    (x : {x : α // x ∈ indexFiber f i}) :
    (indexRestrictedPerm p f hf i x).val = p x.val := rfl

/-- An ambient orbit cannot change its invariant label. -/
theorem index_eq_of_sameCycle (p : Equiv.Perm α) (f : α → I)
    (hf : ∀ x, f (p x) = f x) {x y : α} (hxy : p.SameCycle x y) :
    f x = f y := by
  let s : Set α := indexFiber f (f x)
  have hs : ∀ z, z ∈ s ↔ p z ∈ s := by
    intro z
    change (f z = f x) ↔ (f (p z) = f x)
    rw [hf z]
  have hx : x ∈ s := by simp [s, indexFiber]
  have hy : y ∈ s := (mem_iff_of_sameCycle p s hs hxy).mp hx
  simpa [s, indexFiber] using hy.symm

/-- Restriction preserves and reflects precisely the ambient SameCycle relation on a fibre. -/
theorem sameCycle_indexRestrictedPerm_iff (p : Equiv.Perm α) (f : α → I)
    (hf : ∀ x, f (p x) = f x) (i : I)
    (x y : {z : α // z ∈ indexFiber f i}) :
    (indexRestrictedPerm p f hf i).SameCycle x y ↔ p.SameCycle x.val y.val := by
  change (p.subtypePerm (indexFiber_invariant p f hf i)).SameCycle x y ↔
    p.SameCycle x.val y.val
  exact Perm.sameCycle_subtypePerm

/-- Read an ambient point as its label and its component within that actual fibre. -/
noncomputable def indexedComponentPointMap (p : Equiv.Perm α) (f : α → I)
    (hf : ∀ x, f (p x) = f x) (x : α) :
    Σ i : I, Component (indexRestrictedPerm p f hf i) :=
  ⟨f x, componentOf (indexRestrictedPerm p f hf (f x))
    ⟨x, by simp [indexFiber]⟩⟩

theorem indexedComponentPointMap_eq_fibre (p : Equiv.Perm α) (f : α → I)
    (hf : ∀ x, f (p x) = f x) (x : α) (i : I) (h : f x = i) :
    indexedComponentPointMap p f hf x =
      ⟨i, componentOf (indexRestrictedPerm p f hf i)
        ⟨x, by simpa [indexFiber] using h⟩⟩ := by
  subst i
  rfl

theorem indexedComponentPointMap_respects_sameCycle (p : Equiv.Perm α)
    (f : α → I) (hf : ∀ x, f (p x) = f x) {x y : α}
    (hxy : p.SameCycle x y) :
    indexedComponentPointMap p f hf x = indexedComponentPointMap p f hf y := by
  have hindex : f x = f y := index_eq_of_sameCycle p f hf hxy
  have hy : y ∈ indexFiber f (f x) := by
    change f y = f x
    exact hindex.symm
  have hcomponent :
      componentOf (indexRestrictedPerm p f hf (f x)) ⟨x, by simp [indexFiber]⟩ =
        componentOf (indexRestrictedPerm p f hf (f x)) ⟨y, hy⟩ := by
    apply (componentOf_eq_iff _ _ _).2
    exact (sameCycle_indexRestrictedPerm_iff p f hf (f x)
      ⟨x, by simp [indexFiber]⟩ ⟨y, hy⟩).2 hxy
  rw [indexedComponentPointMap_eq_fibre p f hf x (f x) rfl,
    indexedComponentPointMap_eq_fibre p f hf y (f x) hindex.symm]
  exact congrArg (Sigma.mk (f x)) hcomponent

/-- Decompose every ambient orbit into its unique label and restricted orbit. -/
noncomputable def indexedComponentEquiv (p : Equiv.Perm α) (f : α → I)
    (hf : ∀ x, f (p x) = f x) :
    Component p ≃ Σ i : I, Component (indexRestrictedPerm p f hf i) where
  toFun := Quotient.lift (indexedComponentPointMap p f hf)
    (fun _ _ h => indexedComponentPointMap_respects_sameCycle p f hf h)
  invFun := fun z =>
    restrictComponentInclusion p (indexFiber f z.1) (indexFiber_invariant p f hf z.1) z.2
  left_inv := by
    intro c
    induction c using Quotient.inductionOn with
    | h x =>
        change restrictComponentInclusion p (indexFiber f (f x))
          (indexFiber_invariant p f hf (f x))
          (componentOf (indexRestrictedPerm p f hf (f x))
            ⟨x, by simp [indexFiber]⟩) = componentOf p x
        exact restrictComponentInclusion_componentOf p (indexFiber f (f x))
          (indexFiber_invariant p f hf (f x)) ⟨x, by simp [indexFiber]⟩
  right_inv := by
    rintro ⟨i, c⟩
    induction c using Quotient.inductionOn with
    | h x =>
      change indexedComponentPointMap p f hf x.val =
        ⟨i, componentOf (indexRestrictedPerm p f hf i) x⟩
      rw [indexedComponentPointMap_eq_fibre p f hf x.val i x.property]

@[simp] theorem indexedComponentEquiv_componentOf (p : Equiv.Perm α)
    (f : α → I) (hf : ∀ x, f (p x) = f x) (x : α) :
    indexedComponentEquiv p f hf (componentOf p x) =
      ⟨f x, componentOf (indexRestrictedPerm p f hf (f x))
        ⟨x, by simp [indexFiber]⟩⟩ := rfl

@[simp] theorem indexedComponentEquiv_symm_componentOf (p : Equiv.Perm α)
    (f : α → I) (hf : ∀ x, f (p x) = f x) (i : I)
    (x : {x : α // x ∈ indexFiber f i}) :
    (indexedComponentEquiv p f hf).symm
      ⟨i, componentOf (indexRestrictedPerm p f hf i) x⟩ =
        componentOf p x.val := rfl

/-- The finite sum of restricted component counts follows from the explicit quotient equivalence. -/
theorem componentCount_indexedInvariantPartition [Fintype α] [Fintype I]
    (p : Equiv.Perm α) (f : α → I) (hf : ∀ x, f (p x) = f x) :
    componentCount p =
      ∑ i : I, componentCount (indexRestrictedPerm p f hf i) := by
  classical
  simpa [componentCount, Fintype.card_sigma] using
    Fintype.card_congr (indexedComponentEquiv p f hf)

end DirectGLSSW.IndexedInvariantPartition
