import SM.NonFlatCenter

/-! Actual nonconsecutive supports and the central geometry of a pure cut. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

def NoConsecutive (S : Finset (ZMod n)) : Prop :=
  ∀ i ∈ S, i + 1 ∉ S

theorem noConsecutive_size {S : Finset (ZMod n)}
    (hs : S.card = 3) (h : NoConsecutive S) : 6 ≤ n := by
  have hinj : Function.Injective (fun i : ZMod n => i + 1) := by
    intro i j he
    exact add_right_cancel he
  have hdis : Disjoint S (S.image (fun i => i + 1)) := by
    apply Finset.disjoint_left.mpr
    intro i hi him
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp him
    exact h j hj hi
  have hc := Finset.card_le_card (Finset.subset_univ (S ∪ S.image (fun i => i + 1)))
  rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ hinj,
    hs, Finset.card_univ, ZMod.card] at hc
  exact hc

theorem noConsecutive_ne_turnSupport {S : Finset (ZMod n)}
    (h : NoConsecutive S) (i : ZMod n) : S ≠ turnSupport i := by
  intro he
  exact h i (by rw [he]; simp [turnSupport]) (by rw [he]; simp [turnSupport])

theorem noConsecutive_vertex_exclusion (hn : 3 ≤ n)
    {S : Finset (ZMod n)} (hz : pointZeroTriples P = {S})
    (h : NoConsecutive S) : ∀ k i, ¬ incident k i → P k ∉ edgeSegment P i := by
  letI : Fact (1 < n) := ⟨by omega⟩
  intro k i hki hp
  obtain ⟨hk0, hk1⟩ := (nonincident_iff k i).mp hki
  obtain ⟨t, _, _, ht⟩ := hp
  have hchi : chi P i (i + 1) k = 0 := by
    rw [chi_edge, ht, det_edge_line]
    simp
  have hm := (mem_pointZeroTriples P {i, i + 1, k}).mpr
    ((pointZeroTriple_iff (next_ne_self i).symm hk1.symm hk0.symm).mpr hchi)
  rw [hz, Finset.mem_singleton] at hm
  exact h i (by rw [← hm]; simp) (by rw [← hm]; simp)

theorem pureCut_crossingGeometry {S : Finset (ZMod n)}
    (hz : pointZeroTriples P = {S}) (h : NoConsecutive S)
    (hc : concurrenceTriples P = ∅) : CrossingGeometry P := by
  have hn := noConsecutive_size (singlePointTriple_data hz).1 h
  exact singlePointTriple_nonflat_crossingGeometry (by omega) hz
    (noConsecutive_ne_turnSupport h) (noConsecutive_vertex_exclusion (by omega) hz h) hc

end SM
