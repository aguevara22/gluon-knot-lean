import HOMFLYBasepointShift
import DirectGLSSW.PermutationSplitJoin
import DirectGLSSW.IndexedInvariantPartition

set_option autoImplicit false

namespace DirectGLSSW.PermutationOrbits
open Equiv

/-- The two interval labels of a cut are an explicit Bool-valued quotient of
its selected old orbit fibre. -/
noncomputable def swapFibreComponentEquiv
    {α : Type} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) (a b : α)
    (hne : a ≠ b) (hab : p.SameCycle a b) :
    Component (swapFibrePerm p a b hab) ≃ Bool := by
  classical
  let a₀ : Fibre p (componentOf p a) := ⟨a, rfl⟩
  let b₀ : Fibre p (componentOf p a) :=
    ⟨b, ((componentOf_eq_iff p a b).2 hab).symm⟩
  let q := swapFibrePerm p a b hab
  let split := swapFibrePerm_split p a b hne hab
  let label : Component q → Bool := Quotient.lift
    (fun x => if q.SameCycle a₀ x then false else true)
    (by
      intro x y hxy
      have hrel : q.SameCycle a₀ x ↔ q.SameCycle a₀ y := by
        constructor
        · intro hx
          exact hx.trans hxy
        · intro hy
          exact hy.trans hxy.symm
      simp [hrel])
  have hinj : Function.Injective label := by
    intro x y hxy
    obtain ⟨u, rfl⟩ := Quotient.exists_rep x
    obtain ⟨v, rfl⟩ := Quotient.exists_rep y
    change (if q.SameCycle a₀ u then false else true) =
      (if q.SameCycle a₀ v then false else true) at hxy
    by_cases hu : q.SameCycle a₀ u
    · have hv : q.SameCycle a₀ v := by simpa [hu] using hxy
      apply (componentOf_eq_iff q u v).2
      exact hu.symm.trans hv
    · have hv : ¬ q.SameCycle a₀ v := by simpa [hu] using hxy
      rcases split.2.1 u with hu' | hu'
      · exact False.elim (hu hu')
      · rcases split.2.1 v with hv' | hv'
        · exact False.elim (hv hv')
        · apply (componentOf_eq_iff q u v).2
          exact hu'.symm.trans hv'
  have hsurj : Function.Surjective label := by
    intro x
    cases x
    · refine ⟨componentOf q a₀, ?_⟩
      change (if q.SameCycle a₀ a₀ then false else true) = false
      exact if_pos (Perm.SameCycle.refl q a₀)
    · refine ⟨componentOf q b₀, ?_⟩
      have hnot : ¬ q.SameCycle a₀ b₀ := split.1
      change (if q.SameCycle a₀ b₀ then false else true) = true
      exact if_neg hnot
  exact Equiv.ofBijective label ⟨hinj, hsurj⟩

@[simp] theorem swapFibreComponentEquiv_left
    {α : Type} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) (a b : α)
    (hne : a ≠ b) (hab : p.SameCycle a b) :
    swapFibreComponentEquiv p a b hne hab
      (componentOf (swapFibrePerm p a b hab)
        (⟨a, rfl⟩ : Fibre p (componentOf p a))) = false := by
  classical
  change (if (swapFibrePerm p a b hab).SameCycle _ _ then false else true) = false
  exact if_pos (Perm.SameCycle.refl _ _)

@[simp] theorem swapFibreComponentEquiv_right
    {α : Type} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) (a b : α)
    (hne : a ≠ b) (hab : p.SameCycle a b) :
    swapFibreComponentEquiv p a b hne hab
      (componentOf (swapFibrePerm p a b hab)
        (⟨b, ((componentOf_eq_iff p a b).2 hab).symm⟩ :
          Fibre p (componentOf p a))) = true := by
  classical
  have hnot := (swapFibrePerm_split p a b hne hab).1
  change (if (swapFibrePerm p a b hab).SameCycle _ _ then false else true) = true
  exact if_neg hnot

end DirectGLSSW.PermutationOrbits



namespace DirectGLSSW.PermutationOrbits

/-- The old component label is invariant under a cut of two points in one
old component. -/
theorem cut_oldComponent_invariant {α : Type} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) (a b : α) (hab : p.SameCycle a b) (x : α) :
    componentOf p ((p * Equiv.swap a b) x) = componentOf p x :=
  componentOf_mul_swap p hab x

noncomputable def cutRestrictedComponentCode
    {α : Type} [Fintype α] [DecidableEq α] (p : Equiv.Perm α)
    [DecidableEq (Component p)] (a b : α)
    (hne : a ≠ b) (hab : p.SameCycle a b) (C : Component p) :
    Component (IndexedInvariantPartition.indexRestrictedPerm
      (p * Equiv.swap a b) (componentOf p)
      (cut_oldComponent_invariant p a b hab) C) ≃
      (if C = componentOf p a then Bool else PUnit) := by
  classical
  by_cases hC : C = componentOf p a
  · subst C
    have htype : {x : α // x ∈ IndexedInvariantPartition.indexFiber
        (componentOf p) (componentOf p a)} = Fibre p (componentOf p a) := rfl
    have hperm : IndexedInvariantPartition.indexRestrictedPerm
        (p * Equiv.swap a b) (componentOf p)
        (cut_oldComponent_invariant p a b hab) (componentOf p a) =
        swapFibrePerm p a b hab := by
      cases htype
      apply Equiv.ext
      intro x
      rfl
    rw [hperm]
    exact (swapFibreComponentEquiv p a b hne hab).trans (Equiv.cast (by simp))
  · have hperm : IndexedInvariantPartition.indexRestrictedPerm
        (p * Equiv.swap a b) (componentOf p)
        (cut_oldComponent_invariant p a b hab) C = fibrePerm p C := by
      apply Equiv.ext
      intro x
      apply Subtype.ext
      have hxa : x.val ≠ a := by
        intro hh
        apply hC
        calc
          C = componentOf p x.val := x.property.symm
          _ = componentOf p a := by rw [hh]
      have hxb : x.val ≠ b := by
        intro hh
        apply hC
        calc
          C = componentOf p x.val := x.property.symm
          _ = componentOf p a := by
            rw [hh]
            exact ((componentOf_eq_iff p a b).2 hab).symm
      change (p * Equiv.swap a b) x.val = p x.val
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb]
    let q := fibrePerm p C
    have hcycle : q.IsCycleOn (Set.univ : Set (Fibre p C)) := by
      simpa [q] using fibrePerm_isCycleOn p C
    have hcard : Fintype.card (Component q) = 1 := componentCount_eq_one q hcycle
    letI : Nonempty (Component q) := ⟨componentOf q
      (Classical.choice (fibreNonempty p C))⟩
    letI : Unique (Component q) := Classical.choice
      (Fintype.card_eq_one_iff_nonempty_unique.mp hcard)
    rw [hperm]
    simpa [hC, q] using (Equiv.equivPUnit (Component q))

end DirectGLSSW.PermutationOrbits

namespace DirectGLSSW.PermutationOrbits

noncomputable def cutComponentPartitionCode
    {α : Type} [Fintype α] [DecidableEq α] (p : Equiv.Perm α)
    [DecidableEq (Component p)] (a b : α) (hne : a ≠ b)
    (hab : p.SameCycle a b) :
    Component (p * Equiv.swap a b) ≃
      Σ C : Component p, (if C = componentOf p a then Bool else PUnit) := by
  classical
  exact (IndexedInvariantPartition.indexedComponentEquiv
      (p * Equiv.swap a b) (componentOf p)
      (cut_oldComponent_invariant p a b hab)).trans
    (Equiv.sigmaCongrRight fun C => cutRestrictedComponentCode p a b hne hab C)

end DirectGLSSW.PermutationOrbits
