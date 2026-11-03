import HOMFLYCutNormalization
set_option autoImplicit false
namespace DirectGLSSW.PermutationOrbits
open Equiv
variable {α : Type} [Fintype α] [DecidableEq α]

theorem cutMiddle_component (p : Perm α) (a b : α) (hne : a ≠ b)
    (hab : p.SameCycle a b)
    (j : Fin (Fintype.card (Fibre p (componentOf p a))))
    (hj : FiniteCycleSplit.cutSide (cutMarkIndex p a b hab) j = true) :
    componentOf (p * swap a b) (orbitEnumeration p a j).val =
      componentOf (p * swap a b) b := by
  let k := cutMarkIndex p a b hab
  let x : Fibre (FiniteCycleSplit.cutPerm k) (componentOf (FiniteCycleSplit.cutPerm k) k) :=
    ⟨j, ((componentOf_eq_iff _ _ _).2
      ((FiniteCycleSplit.cut_sameCycle_mark_iff k (cutMarkIndex_ne_zero p a b hne hab) j).2 hj)).symm⟩
  have h := (orbitFibreEquivOfEmbedding (FiniteCycleSplit.cutPerm k) (p * swap a b)
    (fun t => (orbitEnumeration p a t).val)
    (Subtype.val_injective.comp (orbitEnumeration p a).injective)
    (cutOrbitEmbedding_step p a b hab) k x).property
  change componentOf (p * swap a b) (orbitEnumeration p a j).val =
    componentOf (p * swap a b) (orbitEnumeration p a (cutMarkIndex p a b hab)).val at h
  rw [cutMarkIndex_enumerate] at h
  exact h

theorem cutTail_component (p : Perm α) (a b : α)
    (hab : p.SameCycle a b)
    (j : Fin (Fintype.card (Fibre p (componentOf p a))))
    (hj : FiniteCycleSplit.cutSide (cutMarkIndex p a b hab) j = false) :
    componentOf (p * swap a b) (orbitEnumeration p a j).val =
      componentOf (p * swap a b) a := by
  let k := cutMarkIndex p a b hab
  let x : Fibre (FiniteCycleSplit.cutPerm k) (componentOf (FiniteCycleSplit.cutPerm k) 0) :=
    ⟨j, ((componentOf_eq_iff _ _ _).2
      ((FiniteCycleSplit.cut_sameCycle_zero_iff k j).2 hj)).symm⟩
  have h := (orbitFibreEquivOfEmbedding (FiniteCycleSplit.cutPerm k) (p * swap a b)
    (fun t => (orbitEnumeration p a t).val)
    (Subtype.val_injective.comp (orbitEnumeration p a).injective)
    (cutOrbitEmbedding_step p a b hab) 0 x).property
  change componentOf (p * swap a b) (orbitEnumeration p a j).val =
    componentOf (p * swap a b) (orbitEnumeration p a 0).val at h
  rw [orbitEnumeration_zero] at h
  exact h

end DirectGLSSW.PermutationOrbits


