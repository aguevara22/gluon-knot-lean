import OrbitJoinSpectatorComponents

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PermutationOrbits
open Equiv
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*} [Fintype A] [DecidableEq A]
variable (p r : Perm A) (a b : A) (hab : ¬p.SameCycle a b) (hr : r=p*swap a b)

def joinComponentMapTo : Component p → Component r := by
  subst r
  exact joinComponentMap p a b hab

@[simp] theorem joinComponentMapTo_componentOf (x : A) :
    joinComponentMapTo p r a b hab hr (componentOf p x)=componentOf r x := by
  subst r
  rfl

theorem joinComponentMapTo_eq_joined_iff (C : Component p) :
    joinComponentMapTo p r a b hab hr C=componentOf r a ↔
      C=componentOf p a ∨ C=componentOf p b := by
  subst r
  exact joinComponentMap_eq_joined_iff p a b hab C

/-- Multiplication-only spectator product transport under an actual orbit
join; the one removed old factor multiplies the new spectator product. -/
theorem join_spectator_product (f : Component p → ℚ) (g : Component r → ℚ)
    (hweight : ∀ C, C≠componentOf p a → C≠componentOf p b →
      g (joinComponentMapTo p r a b hab hr C)=f C) :
    f (componentOf p b) * (∏ D ∈ Finset.univ.erase (componentOf r a),g D) =
      ∏ C ∈ Finset.univ.erase (componentOf p a),f C := by
  classical
  subst r
  have hba : componentOf p b≠componentOf p a :=
    fun h => hab ((componentOf_eq_iff _ _ _).mp h).symm
  have hbmem : componentOf p b∈Finset.univ.erase (componentOf p a) := by simp [hba]
  have hprod : (∏ D ∈ Finset.univ.erase (componentOf (p*swap a b) a),g D) =
      ∏ C ∈ (Finset.univ.erase (componentOf p a)).erase (componentOf p b),f C := by
    rw [Finset.prod_subtype (p:=fun D => D≠componentOf (p*swap a b) a)
      _ (fun D => by simp)]
    rw [Finset.prod_subtype (p:=fun C => C≠componentOf p a ∧ C≠componentOf p b)
      _ (fun C => by simp [and_comm])]
    symm
    apply Fintype.prod_equiv (joinSpectatorEquiv p a b hab)
    intro C
    exact (hweight C.val C.property.1 C.property.2).symm
  rw [hprod]
  exact Finset.mul_prod_erase _ _ hbmem

end DirectGLSSW.PermutationOrbits
