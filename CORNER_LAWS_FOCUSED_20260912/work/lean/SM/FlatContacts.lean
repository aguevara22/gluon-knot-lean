import SM.FlatIndices
import SM.AffineSegments
import SM.WeakGeometry

/-! The flat centre has no vertex on any nonincident closed edge segment.
Its permitted collinear triple puts each exceptional vertex beyond that edge. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {j : ZMod n}

theorem flat_nonincident_vertex_exclusion (hn : 4 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1))) :
    ∀ k i, ¬ incident k i → P k ∉ edgeSegment P i := by
  letI : Fact (1 < n) := ⟨by omega⟩
  intro k i hki hp
  obtain ⟨hk0, hk1⟩ := (nonincident_iff k i).mp hki
  obtain ⟨t, ht0, ht1, ht⟩ := hp
  have hchi : chi P i (i + 1) k = 0 := by
    rw [chi_edge, ht, det_edge_line]
    simp
  have hm := (mem_pointZeroTriples P {i, i + 1, k}).mpr
    ((pointZeroTriple_iff (next_ne_self i).symm hk1.symm hk0.symm).mpr hchi)
  rw [hz, Finset.mem_singleton] at hm
  rcases edge_vertex_turnSupport_cases hn hk0 hk1 hm with ⟨hi, hk⟩ | ⟨hi, hk⟩
  · apply strictBetween_right_not_on_left hb
    refine ⟨t, ht0, ht1, ?_⟩
    simpa only [hi, hk, edgePoint, edge, sub_add_cancel] using ht
  · apply strictBetween_left_not_on_right hb
    refine ⟨t, ht0, ht1, ?_⟩
    simpa only [hi, hk, edgePoint, edge] using ht

end SM
