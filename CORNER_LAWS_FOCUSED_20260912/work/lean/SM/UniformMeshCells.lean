import SM.UniformMesh

/-! Actual closed cells of the strict uniform mesh cover the entire interval.
Distinct cells can intersect only at an adjacent shared endpoint. -/

namespace SM

open Set

noncomputable section

def uniformMeshCell (N : ℕ) (hN : 0 < N) (j : Fin N) : Set unitInterval :=
  Icc (uniformMeshPoint N hN j.castSucc) (uniformMeshPoint N hN j.succ)

theorem isClosed_uniformMeshCell (N : ℕ) (hN : 0 < N) (j : Fin N) :
    IsClosed (uniformMeshCell N hN j) := isClosed_Icc

theorem uniformMeshCell_left_mem (N : ℕ) (hN : 0 < N) (j : Fin N) :
    uniformMeshPoint N hN j.castSucc ∈ uniformMeshCell N hN j := by
  refine ⟨le_rfl, (uniformMeshPoint_strictMono N hN).monotone ?_⟩
  change j.val ≤ j.val + 1
  omega

theorem uniformMeshCell_right_mem (N : ℕ) (hN : 0 < N) (j : Fin N) :
    uniformMeshPoint N hN j.succ ∈ uniformMeshCell N hN j := by
  exact ⟨(uniformMeshCell_left_mem N hN j).2, le_rfl⟩

theorem exists_uniformMeshCell (N : ℕ) (hN : 0 < N) (t : unitInterval) :
    ∃ j : Fin N, t ∈ uniformMeshCell N hN j := by
  classical
  by_cases ht : t = 0
  · subst t
    refine ⟨⟨0, hN⟩, ?_⟩
    have hm := uniformMeshCell_left_mem N hN (⟨0, hN⟩ : Fin N)
    have he : uniformMeshPoint N hN (⟨0, hN⟩ : Fin N).castSucc = 0 :=
      uniformMeshPoint_first N hN
    rwa [he] at hm
  · let S : Finset (Fin (N + 1)) := Finset.univ.filter fun k => t ≤ uniformMeshPoint N hN k
    have hlast : (⟨N, by omega⟩ : Fin (N + 1)) ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, uniformMeshPoint_last]
      exact t.property.2
    have hS : S.Nonempty := ⟨_, hlast⟩
    let k := S.min' hS
    have hk : k ∈ S := Finset.min'_mem S hS
    have hupper : t ≤ uniformMeshPoint N hN k := (Finset.mem_filter.mp hk).2
    have hkpos : 0 < k.val := by
      by_contra hneg
      have hv : k.val = 0 := by omega
      have hkzero : k = (⟨0, by omega⟩ : Fin (N + 1)) := Fin.ext hv
      rw [hkzero, uniformMeshPoint_first] at hupper
      apply ht
      exact le_antisymm hupper t.property.1
    let j : Fin N := ⟨k.val - 1, by have := k.isLt; omega⟩
    have hsucc : j.succ = k := Fin.ext (by dsimp [j]; omega)
    have hlower : uniformMeshPoint N hN j.castSucc ≤ t := by
      by_contra hnot
      have hmem : j.castSucc ∈ S := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (lt_of_not_ge hnot).le⟩
      have hminimal : k ≤ j.castSucc := Finset.min'_le S _ hmem
      change k.val ≤ j.val at hminimal
      dsimp [j] at hminimal
      omega
    exact ⟨j, hlower, by simpa only [hsucc] using hupper⟩

theorem iUnion_uniformMeshCell (N : ℕ) (hN : 0 < N) :
    ⋃ j : Fin N, uniformMeshCell N hN j = univ := by
  apply eq_univ_of_forall
  intro t
  obtain ⟨j, hj⟩ := exists_uniformMeshCell N hN t
  exact mem_iUnion.mpr ⟨j, hj⟩

theorem uniformMeshCell_ordered_intersection (N : ℕ) (hN : 0 < N)
    (i j : Fin N) (hij : i < j) (t : unitInterval)
    (hi : t ∈ uniformMeshCell N hN i) (hj : t ∈ uniformMeshCell N hN j) :
    j.val = i.val + 1 ∧ t = uniformMeshPoint N hN i.succ ∧
      t = uniformMeshPoint N hN j.castSucc := by
  have hji : j.castSucc ≤ i.succ :=
    (uniformMeshPoint_strictMono N hN).le_iff_le.mp (hj.1.trans hi.2)
  have hindex : j.val = i.val + 1 := by
    change j.val ≤ i.val + 1 at hji
    change i.val < j.val at hij
    omega
  have he : i.succ = j.castSucc := Fin.ext hindex.symm
  have ht : t = uniformMeshPoint N hN i.succ :=
    le_antisymm hi.2 (by simpa only [he] using hj.1)
  exact ⟨hindex, ht, by simpa only [he] using ht⟩

end

end SM
