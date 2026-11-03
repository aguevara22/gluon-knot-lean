import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Basic



set_option autoImplicit false

namespace DirectGLSSW.MarkedCycleGaps

universe u

variable {ι : Type u}

private theorem fin_heq_same {n : ℕ} (x y : Fin n) (h : x.val = y.val) : HEq x y :=
  heq_of_eq (Fin.ext h)

private theorem fin_heq_of_index {n m : ℕ} (h : n = m)
    (x : Fin n) (y : Fin m) (hv : x.val = y.val) : HEq x y := by
  cases h
  exact fin_heq_same x y hv

/-- Move one position forward in a finite marked gap, wrapping to the first
position of the next gap at its endpoint. -/
noncomputable def gapSuccessor (len : ι → ℕ) (hpos : ∀ m, 0 < len m)
    (next : Equiv.Perm ι) : Equiv.Perm (Σ m, Fin (len m)) := by
  let f : (Σ m, Fin (len m)) → (Σ m, Fin (len m)) := fun x =>
    if h : x.2.val + 1 < len x.1 then
      ⟨x.1, ⟨x.2.val + 1, h⟩⟩
    else
      ⟨next x.1, ⟨0, hpos (next x.1)⟩⟩
  let g : (Σ m, Fin (len m)) → (Σ m, Fin (len m)) := fun x =>
    if h : x.2.val = 0 then
      let m := next.symm x.1
      ⟨m, ⟨len m - 1, by have hm := hpos m; omega⟩⟩
    else
      ⟨x.1, ⟨x.2.val - 1, by omega⟩⟩
  have hfg : Function.LeftInverse g f := by
    intro x
    rcases x with ⟨m, ⟨k, hk⟩⟩
    change g (f ⟨m, ⟨k, hk⟩⟩) = ⟨m, ⟨k, hk⟩⟩
    by_cases h : k + 1 < len m
    · simp [f, g, h, Nat.succ_ne_zero]
    · have hlast : k + 1 = len m := by have hm := hpos m; omega
      simp only [f, dif_neg h, g, dif_pos rfl]
      apply Sigma.ext (next.symm_apply_apply m)
      have hval : len (next.symm (next m)) - 1 = k := by
        rw [next.symm_apply_apply]
        omega
      exact fin_heq_of_index (congrArg len (next.symm_apply_apply m)) _ _ hval
  have hgf : Function.RightInverse g f := by
    intro x
    rcases x with ⟨m, ⟨k, hk⟩⟩
    change f (g ⟨m, ⟨k, hk⟩⟩) = ⟨m, ⟨k, hk⟩⟩
    by_cases hzero : k = 0
    · subst k
      have hm := hpos (next.symm m)
      have hlast : ¬ (len (next.symm m) - 1 + 1 < len (next.symm m)) := by omega
      simp only [g, dif_pos rfl, f, dif_neg hlast]
      apply Sigma.ext (next.apply_symm_apply m)
      exact fin_heq_of_index (congrArg len (next.apply_symm_apply m)) _ _ rfl
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hzero
      have hposk : 0 < k := Nat.pos_of_ne_zero hzero
      have hstep : (k - 1) + 1 < len m := by omega
      simp [g, f, hzero, hstep]
      omega
  exact Equiv.ofBijective f ⟨hfg.injective, hgf.surjective⟩

@[simp]
theorem gapSuccessor_inner (len : ι → ℕ) (hpos : ∀ m, 0 < len m)
    (next : Equiv.Perm ι) (m : ι) (k : Fin (len m))
    (hk : k.val + 1 < len m) :
    gapSuccessor len hpos next ⟨m, k⟩ = ⟨m, ⟨k.val + 1, hk⟩⟩ := by
  simp [gapSuccessor, hk]

@[simp]
theorem gapSuccessor_last (len : ι → ℕ) (hpos : ∀ m, 0 < len m)
    (next : Equiv.Perm ι) (m : ι) :
    gapSuccessor len hpos next ⟨m, ⟨len m - 1, by have hm := hpos m; omega⟩⟩ =
      ⟨next m, ⟨0, hpos (next m)⟩⟩ := by
  have hm := hpos m
  have hnot : ¬ (len m - 1 + 1 < len m) := by omega
  simp [gapSuccessor, hnot]

@[simp]
theorem gapSuccessor_symm_zero (len : ι → ℕ) (hpos : ∀ m, 0 < len m)
    (next : Equiv.Perm ι) (m : ι) :
    (gapSuccessor len hpos next).symm ⟨m, ⟨0, hpos m⟩⟩ =
      ⟨next.symm m, ⟨len (next.symm m) - 1,
        by have hm := hpos (next.symm m); omega⟩⟩ := by
  apply (gapSuccessor len hpos next).injective
  rw [(gapSuccessor len hpos next).apply_symm_apply ⟨m, ⟨0, hpos m⟩⟩,
    gapSuccessor_last]
  apply Sigma.ext
  · exact (next.apply_symm_apply m).symm
  · exact fin_heq_of_index (congrArg len (next.apply_symm_apply m).symm) _ _ rfl

@[simp]
theorem gapSuccessor_symm_positive (len : ι → ℕ) (hpos : ∀ m, 0 < len m)
    (next : Equiv.Perm ι) (m : ι) (k : Fin (len m)) (hk : 0 < k.val) :
    (gapSuccessor len hpos next).symm ⟨m, k⟩ =
      ⟨m, ⟨k.val - 1, by omega⟩⟩ := by
  apply (gapSuccessor len hpos next).injective
  have hprem : 0 < k.val := hk
  have hprev : (k.val - 1) + 1 < len m := by omega
  rw [(gapSuccessor len hpos next).apply_symm_apply ⟨m,k⟩]
  rw [gapSuccessor_inner len hpos next m ⟨k.val - 1, by omega⟩ hprev]
  refine Sigma.ext rfl ?_
  exact fin_heq_same k ⟨k.val - 1 + 1, hprev⟩ (by change k.val = k.val - 1 + 1; omega)

end DirectGLSSW.MarkedCycleGaps

open DirectGLSSW.MarkedCycleGaps
#check @gapSuccessor
#check @gapSuccessor_inner
#check @gapSuccessor_last
#check @gapSuccessor_symm_zero
#check @gapSuccessor_symm_positive





