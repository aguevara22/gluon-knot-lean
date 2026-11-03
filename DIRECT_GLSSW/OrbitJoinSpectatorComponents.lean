import DirectGLSSW.PermutationSplitJoin
import DirectGLSSW.SpectatorDaughterWords

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PermutationOrbits
open Equiv
variable {A : Type*} [Fintype A] [DecidableEq A]
variable (p : Perm A) (a b : A) (hab : ¬p.SameCycle a b)

/-- The actual quotient map under joining two distinct complete orbits. -/
def joinComponentMap : Component p → Component (p * swap a b) :=
  Quotient.lift (componentOf (p * swap a b)) (fun _ _ h =>
    (componentOf_eq_iff _ _ _).mpr (sameCycle_mul_swap_coarsens p hab h))

@[simp] theorem joinComponentMap_componentOf (x : A) :
    joinComponentMap p a b hab (componentOf p x) = componentOf (p * swap a b) x := rfl

theorem joinComponentMap_eq_joined_iff (C : Component p) :
    joinComponentMap p a b hab C = componentOf (p * swap a b) a ↔
      C=componentOf p a ∨ C=componentOf p b := by
  induction C using Quotient.inductionOn with
  | h x =>
    change componentOf (p * swap a b) x = componentOf (p * swap a b) a ↔
      componentOf p x=componentOf p a ∨ componentOf p x=componentOf p b
    simp only [componentOf_eq_iff]
    rw [Perm.sameCycle_comm (f:=p * swap a b),sameCycle_join_iff p hab]
    constructor
    · rintro (h|h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h|h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm

theorem joinComponentMap_injective_away (C D : Component p)
    (ha : C≠componentOf p a) (hb : C≠componentOf p b)
    (he : joinComponentMap p a b hab C = joinComponentMap p a b hab D) : C=D := by
  induction C using Quotient.inductionOn with
  | h x =>
    induction D using Quotient.inductionOn with
    | h y =>
      apply (componentOf_eq_iff _ _ _).mpr
      apply (sameCycle_mul_swap_iff_of_avoids p
        (fun h => ha ((componentOf_eq_iff _ _ _).mpr h))
        (fun h => hb ((componentOf_eq_iff _ _ _).mpr h))).mp
      exact (componentOf_eq_iff _ _ _).mp he

/-- Spectator orbit quotient map, excluding exactly the two joined old
orbits and exactly the one joined new orbit. -/
def joinSpectatorMap :
    {C : Component p // C≠componentOf p a ∧ C≠componentOf p b} →
    {D : Component (p * swap a b) // D≠componentOf (p * swap a b) a} := fun C =>
  ⟨joinComponentMap p a b hab C.val,fun h =>
    ((joinComponentMap_eq_joined_iff p a b hab C.val).mp h).elim C.property.1 C.property.2⟩

theorem joinSpectatorMap_bijective : Function.Bijective (joinSpectatorMap p a b hab) := by
  constructor
  · intro C D h
    apply Subtype.ext
    exact joinComponentMap_injective_away p a b hab C.val D.val C.property.1 C.property.2
      (congrArg Subtype.val h)
  · intro D
    obtain ⟨x,hx⟩ : ∃ x, componentOf (p * swap a b) x=D.val := by
      induction D.val using Quotient.inductionOn with
      | h x => exact ⟨x,rfl⟩
    have ha : componentOf p x≠componentOf p a := by
      intro h
      apply D.property
      rw [← hx]
      exact (joinComponentMap_eq_joined_iff p a b hab (componentOf p x)).mpr (Or.inl h)
    have hb : componentOf p x≠componentOf p b := by
      intro h
      apply D.property
      rw [← hx]
      exact (joinComponentMap_eq_joined_iff p a b hab (componentOf p x)).mpr (Or.inr h)
    exact ⟨⟨componentOf p x,ha,hb⟩,Subtype.ext hx⟩

def joinSpectatorEquiv :
    {C : Component p // C≠componentOf p a ∧ C≠componentOf p b} ≃
    {D : Component (p * swap a b) // D≠componentOf (p * swap a b) a} :=
  Equiv.ofBijective (joinSpectatorMap p a b hab) (joinSpectatorMap_bijective p a b hab)

@[simp] theorem joinSpectatorEquiv_apply_val
    (C : {C : Component p // C≠componentOf p a ∧ C≠componentOf p b}) :
    (joinSpectatorEquiv p a b hab C).val = joinComponentMap p a b hab C.val := rfl

end DirectGLSSW.PermutationOrbits
