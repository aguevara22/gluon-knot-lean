import OrbitWordSuccessorShift

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PermutationOrbits
variable {A : Type*} [Fintype A]

theorem orbitWord_root_not_mem_tail (p : Equiv.Perm A) (b : A) :
    b ∉ (orbitWord p b).tail := by
  have hn := orbitWord_nodup p b
  rw [orbitWord_cons_tail p b] at hn
  exact (List.nodup_cons.mp hn).1

theorem orbitWord_separated_not_mem_tail (p : Equiv.Perm A) (a b : A)
    (hab : ¬ p.SameCycle a b) : a ∉ (orbitWord p b).tail := by
  intro hh
  exact hab ((mem_orbitWord_iff p b a).mp (List.mem_of_mem_tail hh)).symm

theorem orbitWord_second_not_mem_drop_two (p : Equiv.Perm A) (s a : A)
    (hsa : s ≠ a) (hs : p s = a) : a ∉ (orbitWord p s).drop 2 := by
  have hn := orbitWord_nodup p s
  rw [orbitWord_first_two p s a hsa hs] at hn
  exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1

theorem orbitWord_separated_not_mem_drop_two (p : Equiv.Perm A) (s a b : A)
    (hs : p s = a) (hab : ¬ p.SameCycle a b) : b ∉ (orbitWord p s).drop 2 := by
  intro hh
  have hsb := (mem_orbitWord_iff p s b).mp (List.mem_of_mem_drop hh)
  have hsa : p.SameCycle s a := by
    apply (componentOf_eq_iff p s a).mp
    rw [← hs, componentOf_apply]
  exact hab (hsa.symm.trans hsb)

end DirectGLSSW.PermutationOrbits
