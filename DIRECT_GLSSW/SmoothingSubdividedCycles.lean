import DirectGLSSW.IndexedInvariantPartition
import DirectGLSSW.PermutationSplitJoin

set_option autoImplicit false
namespace DirectGLSSW.SmoothingSubdividedCycles
open PermutationOrbits
noncomputable section
universe u v
variable {α : Type u} {ι : Type v}
variable (p : Equiv.Perm α) (q : Equiv.Perm (α ⊕ ι)) (a : ι → α)
variable (hnew : ∀ i, q (Sum.inr i) = Sum.inl (p (a i)))
variable (hcut : ∀ i, q (Sum.inl (a i)) = Sum.inr i)
variable (hold : ∀ x, (∀ i, x ≠ a i) → q (Sum.inl x) = Sum.inl (p x))

def drop : α ⊕ ι → α
  | Sum.inl x => x
  | Sum.inr i => a i

include hnew hcut hold

theorem mapped_step (x : α) :
    componentOf q (Sum.inl (p x)) = componentOf q (Sum.inl x) := by
  classical
  by_cases hx : ∃ i, x = a i
  · obtain ⟨i,rfl⟩ := hx
    rw [← hnew i, componentOf_apply, ← hcut i, componentOf_apply]
  · have h := hold x (by simpa only [not_exists] using hx)
    rw [← h, componentOf_apply]

theorem drop_step (y : α ⊕ ι) :
    componentOf p (drop a (q y)) = componentOf p (drop a y) := by
  classical
  cases y with
  | inr i => rw [hnew]; exact componentOf_apply p (a i)
  | inl x =>
    by_cases hx : ∃ i, x = a i
    · obtain ⟨i,rfl⟩ := hx
      rw [hcut]; rfl
    · rw [hold x (by simpa only [not_exists] using hx)]
      exact componentOf_apply p x

/-- Inserting new successor points after selected old points preserves full
orbit components, including singleton old cycles. -/
def componentEquiv : Component p ≃ Component q where
  toFun := Quotient.map Sum.inl (fun x y h =>
    (componentOf_eq_iff q _ _).mp
      (IndexedInvariantPartition.index_eq_of_sameCycle p (fun x => componentOf q (Sum.inl x))
        (mapped_step p q a hnew hcut hold) h))
  invFun := Quotient.lift (fun y => componentOf p (drop a y))
    (fun x y h => IndexedInvariantPartition.index_eq_of_sameCycle q
      (fun y => componentOf p (drop a y)) (drop_step p q a hnew hcut hold) h)
  left_inv := by intro c; refine Quotient.inductionOn c ?_; intro x; rfl
  right_inv := by
    intro c
    refine Quotient.inductionOn c ?_
    intro y
    change componentOf q (Sum.inl (drop a y)) = componentOf q y
    cases y with
    | inl x => rfl
    | inr i =>
      change componentOf q (Sum.inl (a i)) = componentOf q (Sum.inr i)
      rw [← hcut i, componentOf_apply]

theorem componentCount_eq [Fintype α] [Fintype ι] :
    componentCount q = componentCount p :=
  (Fintype.card_congr (componentEquiv p q a hnew hcut hold)).symm






end
end DirectGLSSW.SmoothingSubdividedCycles
