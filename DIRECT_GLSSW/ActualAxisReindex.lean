import ActualAxisWholePartition

set_option autoImplicit false
noncomputable section
open DirectGLSSW
attribute [local instance] Classical.propDecidable

namespace DirectGLSSW.HOMFLY.PLWinding

/-- Exact reindexing of a finite cyclic word with its selected initial
edge removed by the natural labels of the remaining edges. -/
theorem actualWord_sum_erase_zero_eq_range (m : ℕ) (hm : 0 < m)
    (g : Fin m → ℝ) :
    (∑ j ∈ (Finset.univ : Finset (Fin m)).erase (⟨0, hm⟩ : Fin m), g j) =
      ∑ k ∈ Finset.range (m-1),
        g (⟨(k+1) % m, Nat.mod_lt _ hm⟩ : Fin m) := by
  apply Finset.sum_bij (fun j _ => j.val - 1)
  · intro j hj
    have hne : j ≠ (⟨0, hm⟩ : Fin m) := (Finset.mem_erase.mp hj).1
    have hjpos : 0 < j.val := by
      have hz : j.val ≠ 0 := by intro he; exact hne (Fin.ext he)
      omega
    exact Finset.mem_range.mpr (by omega)
  · intro j hj t ht he
    apply Fin.ext
    have hjne : j ≠ (⟨0, hm⟩ : Fin m) := (Finset.mem_erase.mp hj).1
    have htne : t ≠ (⟨0, hm⟩ : Fin m) := (Finset.mem_erase.mp ht).1
    have hjpos : 0 < j.val := by
      have hz : j.val ≠ 0 := by intro he; exact hjne (Fin.ext he)
      omega
    have htpos : 0 < t.val := by
      have hz : t.val ≠ 0 := by intro he; exact htne (Fin.ext he)
      omega
    omega
  · intro k hk
    have hkm : k + 1 < m := by
      have := Finset.mem_range.mp hk
      omega
    let j : Fin m := ⟨k+1, hkm⟩
    refine ⟨j, ?_, ?_⟩
    · apply Finset.mem_erase.mpr
      constructor
      · intro he
        have hv := congrArg Fin.val he
        dsimp [j] at hv
        omega
      · exact Finset.mem_univ _
    · dsimp [j]
  · intro j hj
    have hne : j ≠ (⟨0, hm⟩ : Fin m) := (Finset.mem_erase.mp hj).1
    have hjpos : 0 < j.val := by
      have hz : j.val ≠ 0 := by intro he; exact hne (Fin.ext he)
      omega
    congr 1
    apply Fin.ext
    dsimp
    rw [Nat.sub_add_cancel (by omega : 1 ≤ j.val), Nat.mod_eq_of_lt j.isLt]

end DirectGLSSW.HOMFLY.PLWinding
