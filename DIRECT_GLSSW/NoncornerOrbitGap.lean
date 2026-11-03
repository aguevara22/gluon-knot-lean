import DirectGLSSW.DaughterFirstReturn

set_option autoImplicit false
namespace DirectGLSSW.NoncornerOrbitGap
open FiniteFirstReturn
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every omitted coordinate lies strictly after a retained coordinate and before
its first return. The root coordinate supplies a predecessor without wrapping. -/
theorem exists_preceding_retained {N : ℕ} (hN : 0 < N) (P : Fin N → Prop)
    (hzero : P ⟨0,hN⟩) (r : Fin N) (hr : ¬ P r) :
    ∃ c : {i : Fin N // P i}, ∃ k : ℕ, 0 < k ∧
      k < forwardGap c.val (orderedCyclicSuccessor {i : Fin N // P i} c).val ∧
      (cyclicSuccessorPerm N ^ k) c.val = r := by
  classical
  let A : Finset (Fin N) := Finset.univ.filter fun i => P i ∧ i ≤ r
  have hA : A.Nonempty := ⟨⟨0,hN⟩,by simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨hzero,Fin.le_iff_val_le_val.mpr (Nat.zero_le _)⟩⟩
  let a := A.max' hA
  have hamem : a ∈ A := Finset.max'_mem A hA
  have hap : P a ∧ a ≤ r := (Finset.mem_filter.mp hamem).2
  let c : {i : Fin N // P i} := ⟨a,hap.1⟩
  have har : a < r := lt_of_le_of_ne hap.2 (fun h => hr (h ▸ hap.1))
  let next := orderedCyclicSuccessor {i : Fin N // P i} c
  let k := r.val-a.val
  have hkpos : 0 < k := by change 0 < r.val-a.val; exact Nat.sub_pos_of_lt har
  have hkle : k < N := by dsimp [k]; have := r.isLt; omega
  have hgap : k < forwardGap c.val next.val := by
    unfold forwardGap
    split_ifs with hcn
    · have hrnext : r < next.val := by
        apply lt_of_not_ge
        intro hnr
        have hnmem : next.val ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,next.property,hnr⟩
        have hnle := Finset.le_max' A next.val hnmem
        change next.val ≤ a at hnle
        change a.val < next.val.val at hcn
        omega
      change k < next.val.val-a.val
      dsimp [k]
      change r.val < next.val.val at hrnext
      change a.val < r.val at har
      omega
    · change k < N-a.val+next.val.val
      dsimp [k]
      have := r.isLt
      change a.val < r.val at har
      omega
  refine ⟨c,k,hkpos,hgap,?_⟩
  apply Fin.ext
  rw [cyclicSuccessorPerm_pow_val_of_lt c.val hkle]
  have hsum : c.val.val+k = r.val := by change a.val+(r.val-a.val)=r.val; exact Nat.add_sub_of_le hap.2
  rw [hsum,if_pos r.isLt]


end
end DirectGLSSW.NoncornerOrbitGap
