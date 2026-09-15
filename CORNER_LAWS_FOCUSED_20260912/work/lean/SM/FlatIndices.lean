import SM.TurnSupports

/-! The only nonincident edge/vertex triples with the flat turn support.
No exceptional small polygon or wraparound case is omitted. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem second_successor_not_mem_turnSupport (hn : 4 ≤ n) (j : ZMod n) :
    j + 1 + 1 ∉ turnSupport j := by
  have h1 : (1 : ZMod n) ≠ 0 := by
    simpa using small_natCast_ne_zero (n := n) (m := 1) (by omega) (by omega)
  have h2 : (2 : ZMod n) ≠ 0 := by
    simpa using small_natCast_ne_zero (n := n) (m := 2) (by omega) (by omega)
  have h3 : (3 : ZMod n) ≠ 0 := by
    simpa using small_natCast_ne_zero (n := n) (m := 3) (by omega) (by omega)
  intro hm
  simp only [turnSupport, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm | hm
  · exact h3 (by linear_combination hm)
  · exact h2 (by linear_combination hm)
  · exact h1 (by linear_combination hm)

theorem edge_vertex_turnSupport_cases (hn : 4 ≤ n) {i j k : ZMod n}
    (hk0 : k ≠ i) (hk1 : k ≠ i + 1)
    (he : ({i, i + 1, k} : Finset (ZMod n)) = turnSupport j) :
    (i = j - 1 ∧ k = j + 1) ∨ (i = j ∧ k = j - 1) := by
  have hi : i ∈ turnSupport j := by rw [← he]; simp
  have hk : k ∈ turnSupport j := by rw [← he]; simp
  simp only [turnSupport, Finset.mem_insert, Finset.mem_singleton] at hi hk
  rcases hi with hi | hi | hi
  · left
    refine ⟨hi, ?_⟩
    rcases hk with hk | hk | hk
    · exact (hk0 (hk.trans hi.symm)).elim
    · have hh : k = i + 1 := by rw [hi, sub_add_cancel]; exact hk
      exact (hk1 hh).elim
    · exact hk
  · right
    refine ⟨hi, ?_⟩
    rcases hk with hk | hk | hk
    · exact hk
    · exact (hk0 (hk.trans hi.symm)).elim
    · have hh : k = i + 1 := by rw [hi]; exact hk
      exact (hk1 hh).elim
  · have hm : i + 1 ∈ turnSupport j := by rw [← he]; simp
    rw [hi] at hm
    exact (second_successor_not_mem_turnSupport hn j hm).elim

end SM
