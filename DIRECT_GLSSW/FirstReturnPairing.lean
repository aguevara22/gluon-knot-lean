import DirectGLSSW.FiniteFirstReturn
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.FirstReturnOrbitWord

/-- Pairing only represented events preserves genuine first-return gaps.
This is the finite mechanism for smoothing again after deleting unselected visits. -/
theorem firstReturn_pairing
    {α β : Type*} [Fintype α] [Fintype β]
    (p : Equiv.Perm α) (q : Equiv.Perm β) (f : β → α)
    (r : Equiv.Perm α) (s : Equiv.Perm β)
    (hpair : ∀x, r (f x)=f (s x))
    (hfix : ∀y, y ∉ Set.range f → r y=y)
    (hreturn : ∀x : β, ∃d : ℕ, 0<d ∧ (p^d) (f x)= f (q x) ∧
      ∀k : ℕ, 0<k → k<d → (p^k) (f x) ∉ Set.range f) :
    ∀x : β, ∃d : ℕ, 0<d ∧ ((r*p)^d) (f x)= f ((s*q) x) ∧
      ∀k : ℕ, 0<k → k<d → ((r*p)^k) (f x) ∉ Set.range f := by
  intro x
  obtain ⟨d,hd,hreach,hno⟩ := hreturn x
  have hprefix : ∀k : ℕ, k<d → ((r*p)^k) (f x)=(p^k) (f x) := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      rw [pow_succ',Equiv.Perm.mul_apply]
      change r (p (((r*p)^k) (f x))) = _
      rw [ih (by omega)]
      have hp : p ((p^k) (f x))=(p^(k+1)) (f x) := by rw [pow_succ',Equiv.Perm.mul_apply]
      rw [hp]
      exact hfix _ (hno (k+1) (by omega) hk)
  refine ⟨d,hd,?_,fun k hk hkd => ?_⟩
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    rw [pow_succ',Equiv.Perm.mul_apply]
    change r (p (((r*p)^k) (f x))) = _
    rw [hprefix k (by omega)]
    have hp : p ((p^k) (f x))=(p^(k+1)) (f x) := by rw [pow_succ',Equiv.Perm.mul_apply]
    rw [hp,hreach,hpair]
    rfl
  · rw [hprefix k hkd]
    exact hno k hk hkd
end DirectGLSSW.FirstReturnOrbitWord
