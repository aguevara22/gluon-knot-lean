import HOMFLYBasepointSplitComponents
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Fin.Basic

set_option autoImplicit false

namespace DirectGLSSW.PermutationOrbits

/-- Encode the two pieces of the selected component by `false` and `true`;
all other old components retain their old component label. -/
noncomputable def splitSumToOption {α : Type} {p : Equiv.Perm α} {n : ℕ}
    (e : Component p ≃ Fin n) (C₀ : Component p) :
    (Bool ⊕ {C : Component p // C ≠ C₀}) ≃ Option (Fin n) := by
  classical
  refine {
    toFun := fun x =>
      match x with
      | Sum.inl false => some (e C₀)
      | Sum.inl true => none
      | Sum.inr C => some (e C.val)
    invFun := fun x =>
      match x with
      | none => Sum.inl true
      | some i => if h : i = e C₀ then Sum.inl false
          else Sum.inr ⟨e.symm i, by
            intro hC
            apply h
            rw [← hC, Equiv.apply_symm_apply]⟩
    left_inv := by
      intro x
      cases x with
      | inl b => cases b <;> simp [Equiv.symm_apply_apply]
      | inr C =>
          have h : e C.val ≠ e C₀ := by
            intro heq
            exact C.property (e.injective heq)
          simp [h, Equiv.symm_apply_apply]
    right_inv := by
      intro x
      cases x with
      | none => rfl
      | some i =>
          by_cases h : i = e C₀
          · subst i
            simp [Equiv.symm_apply_apply]
          · have hC : e.symm i ≠ C₀ := by
              intro hc
              apply h
              calc
                i = e (e.symm i) := (Equiv.apply_symm_apply e i).symm
                _ = e C₀ := congrArg e hc
            simp [h, hC, Equiv.apply_symm_apply]
  }

/-- Insert the second selected piece immediately after the first one. -/
noncomputable def splitSumToFin {α : Type} {p : Equiv.Perm α} {n : ℕ}
    (e : Component p ≃ Fin n) (C₀ : Component p) :
    (Bool ⊕ {C : Component p // C ≠ C₀}) ≃ Fin (n + 1) := by
  let r : Fin n := e C₀
  let i : Fin (n + 1) := r.succ
  exact (splitSumToOption e C₀).trans (finSuccEquiv' i).symm

@[simp] theorem splitSumToFin_first {α : Type} {p : Equiv.Perm α} {n : ℕ}
    (e : Component p ≃ Fin n) (C₀ : Component p) :
    splitSumToFin e C₀ (Sum.inl false) = (e C₀).castSucc := by
  simp [splitSumToFin, splitSumToOption, finSuccEquiv']

@[simp] theorem splitSumToFin_second {α : Type} {p : Equiv.Perm α} {n : ℕ}
    (e : Component p ≃ Fin n) (C₀ : Component p) :
    splitSumToFin e C₀ (Sum.inl true) = (e C₀).succ := by
  simp [splitSumToFin, splitSumToOption, finSuccEquiv']


/-- Unaffected old components are inserted after the selected component's
second piece, preserving their old relative order. -/
@[simp] theorem splitSumToFin_other {α : Type} {p : Equiv.Perm α} {n : ℕ}
    (e : Component p ≃ Fin n) (C₀ : Component p)
    (C : {C : Component p // C ≠ C₀}) :
    splitSumToFin e C₀ (Sum.inr C) = (e C₀).succ.succAbove (e C.val) := by
  simp [splitSumToFin, splitSumToOption, finSuccEquiv']

/-- The inserted labels preserve strict order among unaffected components. -/
theorem splitSumToFin_other_lt_iff {α : Type} {p : Equiv.Perm α} {n : ℕ}
    (e : Component p ≃ Fin n) (C₀ : Component p)
    (C₁ C₂ : {C : Component p // C ≠ C₀}) :
    splitSumToFin e C₀ (Sum.inr C₁) < splitSumToFin e C₀ (Sum.inr C₂) ↔
      e C₁.val < e C₂.val := by
  simp only [splitSumToFin_other, Fin.succAbove_lt_succAbove_iff]

/-- Swap the selected labels so the `true` middle piece comes before the
`false` tail, while retaining the same ordering of unaffected components. -/
noncomputable def splitSumToFinMiddleFirst {α : Type} {p : Equiv.Perm α} {n : ℕ}
    (e : Component p ≃ Fin n) (C₀ : Component p) :
    (Bool ⊕ {C : Component p // C ≠ C₀}) ≃ Fin (n + 1) := by
  let swap : (Bool ⊕ {C : Component p // C ≠ C₀}) ≃
      (Bool ⊕ {C : Component p // C ≠ C₀}) := {
    toFun := fun x => match x with
      | Sum.inl false => Sum.inl true
      | Sum.inl true => Sum.inl false
      | Sum.inr C => Sum.inr C
    invFun := fun x => match x with
      | Sum.inl false => Sum.inl true
      | Sum.inl true => Sum.inl false
      | Sum.inr C => Sum.inr C
    left_inv := by intro x; cases x with
      | inl b => cases b <;> rfl
      | inr C => rfl
    right_inv := by intro x; cases x with
      | inl b => cases b <;> rfl
      | inr C => rfl
  }
  exact swap.trans (splitSumToFin e C₀)

@[simp] theorem splitSumToFinMiddleFirst_true {α : Type} {p : Equiv.Perm α} {n : ℕ}
    (e : Component p ≃ Fin n) (C₀ : Component p) :
    splitSumToFinMiddleFirst e C₀ (Sum.inl true) = (e C₀).castSucc := by
  simp [splitSumToFinMiddleFirst, splitSumToFin, splitSumToOption, finSuccEquiv']

@[simp] theorem splitSumToFinMiddleFirst_false {α : Type} {p : Equiv.Perm α} {n : ℕ}
    (e : Component p ≃ Fin n) (C₀ : Component p) :
    splitSumToFinMiddleFirst e C₀ (Sum.inl false) = (e C₀).succ := by
  simp [splitSumToFinMiddleFirst, splitSumToFin, splitSumToOption, finSuccEquiv']

@[simp] theorem splitSumToFinMiddleFirst_other {α : Type} {p : Equiv.Perm α} {n : ℕ}
    (e : Component p ≃ Fin n) (C₀ : Component p)
    (C : {C : Component p // C ≠ C₀}) :
    splitSumToFinMiddleFirst e C₀ (Sum.inr C) = (e C₀).succ.succAbove (e C.val) := by
  simp [splitSumToFinMiddleFirst, splitSumToFin, splitSumToOption, finSuccEquiv']

theorem splitSumToFinMiddleFirst_other_lt_iff {α : Type} {p : Equiv.Perm α} {n : ℕ}
    (e : Component p ≃ Fin n) (C₀ : Component p)
    (C₁ C₂ : {C : Component p // C ≠ C₀}) :
    splitSumToFinMiddleFirst e C₀ (Sum.inr C₁) <
        splitSumToFinMiddleFirst e C₀ (Sum.inr C₂) ↔
      e C₁.val < e C₂.val := by
  simp only [splitSumToFinMiddleFirst_other, Fin.succAbove_lt_succAbove_iff]


end DirectGLSSW.PermutationOrbits

#check DirectGLSSW.PermutationOrbits.splitSumToFin_other
#check DirectGLSSW.PermutationOrbits.splitSumToFin_other_lt_iff
#check DirectGLSSW.PermutationOrbits.splitSumToFinMiddleFirst
#check DirectGLSSW.PermutationOrbits.splitSumToFinMiddleFirst_true
#check DirectGLSSW.PermutationOrbits.splitSumToFinMiddleFirst_false
#check DirectGLSSW.PermutationOrbits.splitSumToFinMiddleFirst_other
#check DirectGLSSW.PermutationOrbits.splitSumToFinMiddleFirst_other_lt_iff













