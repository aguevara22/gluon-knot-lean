import DirectGLSSW.PermutationOrbits
import DirectGLSSW.OrderedEventSuccessor

/-!
# Actual finite orbit normalization

Statement transcription: STATEMENTS.md, written before this source.
Source motivation: frozen note lines 131–139. These are generic orbit
transport and normalization bridges, not the source smoothing theorem.
The full orbit quotient and actual orbit fibres retain singleton orbits.
-/

set_option autoImplicit false

namespace DirectGLSSW.PermutationOrbits

open Equiv

universe u v
variable {α : Type u} {β : Type v}

/-- Actual successor intertwining preserves and reflects finite orbit membership. -/
theorem sameCycle_iff_of_intertwining [Fintype α] [Fintype β]
    (e : α ≃ β) (p : Perm α) (q : Perm β)
    (he : ∀ x, e (p x) = q (e x)) (x y : α) :
    p.SameCycle x y ↔ q.SameCycle (e x) (e y) := by
  have hp : ∀ n : ℕ, ∀ z : α, e ((p ^ n) z) = (q ^ n) (e z) := by
    intro n
    induction n with
    | zero => intro z; rfl
    | succ n ih =>
        intro z
        rw [pow_succ', Perm.mul_apply, he, ih, pow_succ', Perm.mul_apply]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    simp only [zpow_natCast, ← hp, hn]
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast]
    apply e.injective
    rw [hp, hn]

/-- Transport every component using the prescribed map on its representatives. -/
def componentEquivOfIntertwining [Fintype α] [Fintype β]
    (e : α ≃ β) (p : Perm α) (q : Perm β)
    (he : ∀ x, e (p x) = q (e x)) : Component p ≃ Component q :=
  Quotient.congr e (sameCycle_iff_of_intertwining e p q he)

@[simp] theorem componentEquivOfIntertwining_componentOf [Fintype α] [Fintype β]
    (e : α ≃ β) (p : Perm α) (q : Perm β)
    (he : ∀ x, e (p x) = q (e x)) (x : α) :
    componentEquivOfIntertwining e p q he (componentOf p x) =
      componentOf q (e x) := rfl

/-- The equality of full component counts follows from the component equivalence. -/
theorem componentCount_eq_of_intertwining [Fintype α] [Fintype β]
    (e : α ≃ β) (p : Perm α) (q : Perm β)
    (he : ∀ x, e (p x) = q (e x)) : componentCount p = componentCount q :=
  Fintype.card_congr (componentEquivOfIntertwining e p q he)

/-- The actual orbit enumeration starts at its specified root. -/
@[simp] theorem orbitEnumeration_zero [Fintype α] (p : Perm α) (x : α) :
    (orbitEnumeration p x 0).val = x := by
  simp

/-- Modular successor coordinates intertwine with the actual fibre successor,
including a one-point fibre and the final wrap back to its root. -/
theorem orbitEnumeration_successor [Fintype α] (p : Perm α) (x : α)
    (i : Fin (Fintype.card (Fibre p (componentOf p x)))) :
    orbitEnumeration p x
        (DirectGLSSW.cyclicSuccessorPerm (Fintype.card (Fibre p (componentOf p x))) i) =
      fibrePerm p (componentOf p x) (orbitEnumeration p x i) := by
  classical
  let q := fibrePerm p (componentOf p x)
  let x₀ : Fibre p (componentOf p x) := ⟨x, rfl⟩
  have hq : q.IsCycleOn (Finset.univ : Finset (Fibre p (componentOf p x))) := by
    simpa using fibrePerm_isCycleOn p (componentOf p x)
  change (q ^ ((i.val + 1 + 0) % Fintype.card (Fibre p (componentOf p x)))) x₀ =
    q ((q ^ i.val) x₀)
  rw [← Perm.mul_apply, ← pow_succ']
  apply (hq.pow_apply_eq_pow_apply (Finset.mem_univ x₀)).2
  simp only [Finset.card_univ, Nat.add_zero, Nat.ModEq, Nat.mod_mod]

end DirectGLSSW.PermutationOrbits
