import HOMFLYCutNormalization
set_option autoImplicit false
namespace DirectGLSSW.PermutationOrbits
open Equiv
variable {α : Type} [Fintype α] [DecidableEq α]

theorem orbitPosition_root_congr (p : Perm α) (r s x : α) (hrs : r = s)
    (hx : componentOf p x = componentOf p r)
    (hy : componentOf p x = componentOf p s) :
    ((orbitEnumeration p r).symm ⟨x,hx⟩).val =
      ((orbitEnumeration p s).symm ⟨x,hy⟩).val := by
  subst s
  rfl

theorem orbitPosition_perm_congr (p q : Perm α) (hpq : p = q) (r x : α)
    (hx : componentOf p x = componentOf p r)
    (hy : componentOf q x = componentOf q r) :
    ((orbitEnumeration p r).symm ⟨x,hx⟩).val =
      ((orbitEnumeration q r).symm ⟨x,hy⟩).val := by
  subst q
  rfl

theorem cutMiddle_orbitPosition (p : Perm α) (a b : α) (hne : a ≠ b)
    (hab : p.SameCycle a b)
    (j : Fin (Fintype.card (Fibre p (componentOf p a))))
    (hj : FiniteCycleSplit.cutSide (cutMarkIndex p a b hab) j = true)
    (hjk : j ≠ cutMarkIndex p a b hab)
    (hc : componentOf (p * swap a b) (orbitEnumeration p a j).val =
      componentOf (p * swap a b) b) :
    ((orbitEnumeration (p * swap a b) b).symm
      ⟨(orbitEnumeration p a j).val,hc⟩).val = j.val := by
  have h := cutMiddle_actual_orbitPosition p a b hne hab j hj hjk
  dsimp only at h
  exact (orbitPosition_root_congr (p * swap a b) b
    (orbitEnumeration p a (cutMarkIndex p a b hab)).val
    (orbitEnumeration p a j).val (cutMarkIndex_enumerate p a b hab).symm hc _).trans h

theorem cutTail_orbitPosition (p : Perm α) (a b : α)
    (hab : p.SameCycle a b)
    (j : Fin (Fintype.card (Fibre p (componentOf p a))))
    (hj : FiniteCycleSplit.cutSide (cutMarkIndex p a b hab) j = false)
    (hj0 : j ≠ 0)
    (hc : componentOf (p * swap a b) (orbitEnumeration p a j).val =
      componentOf (p * swap a b) a) :
    ((orbitEnumeration (p * swap a b) a).symm
      ⟨(orbitEnumeration p a j).val,hc⟩).val = j.val - (cutMarkIndex p a b hab).val := by
  have h := cutTail_actual_orbitPosition p a b hab j hj hj0
  dsimp only at h
  exact h

end DirectGLSSW.PermutationOrbits


