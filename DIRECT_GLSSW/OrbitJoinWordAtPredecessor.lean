import OrbitJoinWord
import OrbitWordSuccessorShift

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PermutationOrbits
variable {A : Type*} [Fintype A]
attribute [local instance] Classical.decEq

/-- The joined word based at the physical predecessor of the first cut.
The two cut labels remain visible here, before physical retention. -/
theorem orbitWord_mul_swap_join_predecessor (p : Equiv.Perm A) (s a b : A)
    (hab : ¬p.SameCycle a b) (hsa : s ≠ a) (hs : p s = a) :
    orbitWord (p * Equiv.swap a b) s =
      [s,a] ++ (orbitWord p b).tail ++ [b] ++ (orbitWord p s).drop 2 := by
  classical
  have hsb : s ≠ b := by
    intro he
    subst s
    apply hab
    apply (componentOf_eq_iff p a b).mp
    rw [← hs,componentOf_apply]
  have hrs : (p * Equiv.swap a b) s = a := by
    simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hsa hsb,hs]
  have hp := orbitWord_successor_tail p s
  rw [hs,orbitWord_first_two p s a hsa hs] at hp
  have hpt : (orbitWord p a).tail = (orbitWord p s).drop 2 ++ [s] := by
    rw [hp]
    simp only [List.tail_cons,List.cons_append]
  have hr := orbitWord_successor_tail (p * Equiv.swap a b) s
  rw [hrs] at hr
  have hj := orbitWord_mul_swap_join p hab
  rw [hpt] at hj
  have hh : (orbitWord (p * Equiv.swap a b) s).tail ++ [s] =
      ((a :: (orbitWord p b).tail) ++ b :: (orbitWord p s).drop 2) ++ [s] := by
    rw [← hr,hj]
    simp only [List.append_assoc,List.cons_append]
  have ht := List.append_cancel_right hh
  rw [orbitWord_cons_tail (p * Equiv.swap a b) s,ht]
  simp only [List.cons_append,List.nil_append,List.append_assoc]

end DirectGLSSW.PermutationOrbits
