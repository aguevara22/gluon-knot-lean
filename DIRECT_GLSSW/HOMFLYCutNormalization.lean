import HOMFLYCutIntervalOrder
import HOMFLYOrbitEmbedding
import DirectGLSSW.PermutationSplitJoin

set_option autoImplicit false

namespace DirectGLSSW.PermutationOrbits
open Equiv
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- The second cut port in the actual old root's orbit coordinates. -/
noncomputable def cutMarkIndex (p : Perm α) (a b : α) (hab : p.SameCycle a b) :
    Fin (Fintype.card (Fibre p (componentOf p a))) :=
  (orbitEnumeration p a).symm ⟨b, ((componentOf_eq_iff p a b).2 hab).symm⟩

@[simp] theorem cutMarkIndex_enumerate (p : Perm α) (a b : α)
    (hab : p.SameCycle a b) :
    (orbitEnumeration p a (cutMarkIndex p a b hab)).val = b := by
  simp [cutMarkIndex]

theorem cutMarkIndex_ne_zero (p : Perm α) (a b : α) (hne : a ≠ b)
    (hab : p.SameCycle a b) : cutMarkIndex p a b hab ≠ 0 := by
  intro h
  have he := cutMarkIndex_enumerate p a b hab
  rw [h, orbitEnumeration_zero] at he
  exact hne he

/-- The normalized two-interval cut maps into the actual whole-diagram
cut continuation by the old rooted orbit enumeration. -/
theorem cutOrbitEmbedding_step (p : Perm α) (a b : α)
    (hab : p.SameCycle a b)
    (j : Fin (Fintype.card (Fibre p (componentOf p a)))) :
    (orbitEnumeration p a
      (FiniteCycleSplit.cutPerm (cutMarkIndex p a b hab) j)).val =
      (p * swap a b) (orbitEnumeration p a j).val := by
  let e := orbitEnumeration p a
  let k := cutMarkIndex p a b hab
  have he0 : (e 0).val = a := orbitEnumeration_zero p a
  have hek : (e k).val = b := cutMarkIndex_enumerate p a b hab
  change (e (cyclicSuccessorPerm _ (swap 0 k j))).val = _
  rw [orbitEnumeration_successor, fibrePerm_apply_val, Perm.mul_apply]
  have hs := (Subtype.val_injective.comp e.injective).map_swap 0 k j
  simpa only [Function.comp_apply, he0, hek] using congrArg p hs

/-- The normalized middle-cycle coordinate is the actual cut-cycle position;
the target cycle belongs to the whole original arc set, not merely a model. -/
theorem cutMiddle_actual_orbitPosition (p : Perm α) (a b : α)
    (hne : a ≠ b) (hab : p.SameCycle a b)
    (j : Fin (Fintype.card (Fibre p (componentOf p a))))
    (hj : FiniteCycleSplit.cutSide (cutMarkIndex p a b hab) j = true)
    (hjk : j ≠ cutMarkIndex p a b hab) :
    let k := cutMarkIndex p a b hab
    let e := fun t => (orbitEnumeration p a t).val
    let x : Fibre (FiniteCycleSplit.cutPerm k)
        (componentOf (FiniteCycleSplit.cutPerm k) k) :=
      ⟨j, ((componentOf_eq_iff _ _ _).2
        ((FiniteCycleSplit.cut_sameCycle_mark_iff k
          (cutMarkIndex_ne_zero p a b hne hab) j).2 hj)).symm⟩
    ((orbitEnumeration (p * swap a b) (e k)).symm
      (orbitFibreEquivOfEmbedding (FiniteCycleSplit.cutPerm k) (p * swap a b)
        e (Subtype.val_injective.comp (orbitEnumeration p a).injective)
        (cutOrbitEmbedding_step p a b hab) k x)).val = j.val := by
  dsimp only
  refine (orbitPosition_embedding (FiniteCycleSplit.cutPerm (cutMarkIndex p a b hab))
    (p * swap a b) (fun t => (orbitEnumeration p a t).val)
    (Subtype.val_injective.comp (orbitEnumeration p a).injective)
    (cutOrbitEmbedding_step p a b hab) (cutMarkIndex p a b hab) _).trans ?_
  exact FiniteCycleSplit.cutMark_orbitPosition _
    (cutMarkIndex_ne_zero p a b hne hab) j hj hjk

/-- The normalized tail-cycle coordinate is likewise the actual cut position. -/
theorem cutTail_actual_orbitPosition (p : Perm α) (a b : α)
    (hab : p.SameCycle a b)
    (j : Fin (Fintype.card (Fibre p (componentOf p a))))
    (hj : FiniteCycleSplit.cutSide (cutMarkIndex p a b hab) j = false)
    (hj0 : j ≠ 0) :
    let k := cutMarkIndex p a b hab
    let e := fun t => (orbitEnumeration p a t).val
    let x : Fibre (FiniteCycleSplit.cutPerm k)
        (componentOf (FiniteCycleSplit.cutPerm k) 0) :=
      ⟨j, ((componentOf_eq_iff _ _ _).2
        ((FiniteCycleSplit.cut_sameCycle_zero_iff k j).2 hj)).symm⟩
    ((orbitEnumeration (p * swap a b) (e 0)).symm
      (orbitFibreEquivOfEmbedding (FiniteCycleSplit.cutPerm k) (p * swap a b)
        e (Subtype.val_injective.comp (orbitEnumeration p a).injective)
        (cutOrbitEmbedding_step p a b hab) 0 x)).val = j.val - k.val := by
  dsimp only
  refine (orbitPosition_embedding (FiniteCycleSplit.cutPerm (cutMarkIndex p a b hab))
    (p * swap a b) (fun t => (orbitEnumeration p a t).val)
    (Subtype.val_injective.comp (orbitEnumeration p a).injective)
    (cutOrbitEmbedding_step p a b hab) 0 _).trans ?_
  exact FiniteCycleSplit.cutZero_orbitPosition _ j hj hj0

end DirectGLSSW.PermutationOrbits







