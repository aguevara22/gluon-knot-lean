import SM.SinglePointTriple
import SM.WeakGeometry

/-! With only one collinear vertex triple, remote segments cannot meet with
parallel directions. Such a meeting would give two different zero supports. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

theorem parallel_meeting_anchor_area_zero {a b u v : Plane} {s t : ℝ}
    (hd : det u v = 0) (he : a + s • u = b + t • v) : det u (b - a) = 0 := by
  have hi := intersection_parameter_identity he.symm
  rw [det_swap u v, hd, neg_zero, mul_zero] at hi
  have ha : det u (b - a) = det (a - b) u := by dsimp [det]; ring
  exact ha.trans hi

theorem singlePointTriple_remote_transverse (hn : 4 ≤ n)
    {S : Finset (ZMod n)} (h : pointZeroTriples P = {S}) {i j : ZMod n}
    (hr : remote i j) {x : Plane} (hi : x ∈ edgeSegment P i)
    (hj : x ∈ edgeSegment P j) : det (edge P i) (edge P j) ≠ 0 := by
  letI : Fact (1 < n) := ⟨by omega⟩
  intro hd
  obtain ⟨s, _, _, hs⟩ := hi
  obtain ⟨t, _, _, ht⟩ := hj
  have hz := parallel_meeting_anchor_area_zero hd (hs.symm.trans ht)
  have hz' : det (edge P i) (P (j + 1) - P i) = 0 := by
    have he : det (edge P i) (P (j + 1) - P i) =
        det (edge P i) (P j - P i) + det (edge P i) (edge P j) := by
      dsimp [edge, det]
      ring
    rw [he, hz, hd, add_zero]
  have hchi : chi P i (i + 1) j = 0 := by
    rw [chi_edge, hz]
    simp
  have hchi' : chi P i (i + 1) (j + 1) = 0 := by
    rw [chi_edge, hz']
    simp
  obtain ⟨hji, hji1, hj1i, hj1i1⟩ := remote_endpoints i j hr
  have hs0 := (mem_pointZeroTriples P {i, i + 1, j}).mpr
    ((pointZeroTriple_iff (next_ne_self i).symm hji1.symm hji.symm).mpr hchi)
  have hs1 := (mem_pointZeroTriples P {i, i + 1, j + 1}).mpr
    ((pointZeroTriple_iff (next_ne_self i).symm hj1i1.symm hj1i.symm).mpr hchi')
  rw [h, Finset.mem_singleton] at hs0 hs1
  have hm : j ∈ ({i, i + 1, j + 1} : Finset (ZMod n)) := by
    rw [hs1, ← hs0]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm | hm
  · exact hji hm
  · exact hji1 hm
  · exact (next_ne_self j).symm hm

end SM
