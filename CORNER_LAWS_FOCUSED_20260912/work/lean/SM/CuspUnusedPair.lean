import SM.CuspNeedle
import SM.WallSegmentStability

/-! The other potentially critical remote pair is actually disjoint at
the cusp centre, and compact disjointness persists in a neighbourhood. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n]

theorem edgeLine_parameter_of_det_zero {P : LabelledTuple n} {i : ZMod n} {x : Plane}
    (he : edge P i ≠ 0) (hd : det (edge P i) (x - P i) = 0) :
    ∃ t : ℝ, x = edgePoint P i t := by
  have hx := scalar_of_det_zero he hd
  refine ⟨planeDot (edge P i) (x - P i) / planeDot (edge P i) (edge P i), ?_⟩
  change x = P i + _ • edge P i
  rw [← hx]
  abel

theorem segments_disjoint_of_exterior_line_contact {P : LabelledTuple n} {i k : ZMod n}
    (hd : det (edge P i) (edge P k) ≠ 0) {x : Plane}
    (hi : ∃ s : ℝ, x = edgePoint P i s) (hk : ∃ t : ℝ, x = edgePoint P k t)
    (hout : x ∉ edgeSegment P i) : ¬ (edgeSegment P i ∩ edgeSegment P k).Nonempty := by
  obtain ⟨s, hs⟩ := hi
  obtain ⟨t, ht⟩ := hk
  rintro ⟨y, ⟨u, hu0, hu1, hu⟩, ⟨v, hv0, hv1, hv⟩⟩
  have he := intersection_parameters_unique hd (hs.symm.trans ht) (hu.symm.trans hv)
  exact hout ⟨u, hu0, hu1, by rw [← he.1]; exact hs⟩

theorem cusp_unused_delta_ne_zero (hn : 4 ≤ n) {P : LabelledTuple n} {j : ZMod n}
    (hz : pointZeroTriples P = {turnSupport j}) {b : Bool} (hc : CuspCase P j b) :
    cuspDelta P (!b) j ≠ 0 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  cases b
  · obtain ⟨_, t, ht0, _, ht⟩ := hc
    have he : edge P (j - 1) = (-t) • edge P j := by
      simp only [edge, sub_add_cancel]
      rw [ht]
      ext <;> dsimp <;> ring
    have hd : det (edge P j) (edge P (j + 1)) ≠ 0 := by
      have hh := sign_ne_zero.mp ((turn_det P (j + 1)) ▸
        singlePointTriple_turn_ne_zero hn hz (next_ne_self j))
      simpa only [add_sub_cancel_right] using hh
    have hi := cusp_indices_A j
    change cuspDelta P true j ≠ 0
    simp only [cuspDelta, hi.1, hi.2.1, he]
    have hid : det ((-t) • edge P j) (edge P (j + 1)) =
        (-t) * det (edge P j) (edge P (j + 1)) := by dsimp [det]; ring
    rw [hid]
    exact mul_ne_zero (neg_ne_zero.mpr ht0.ne') hd
  · obtain ⟨r, hr, he⟩ := cusp_negative_pair hc
    have hd : det (edge P (j - 2)) (edge P (j - 1)) ≠ 0 := by
      have hh := sign_ne_zero.mp ((turn_det P (j - 1)) ▸
        singlePointTriple_turn_ne_zero hn hz (prev_ne_self j))
      have heq : j - 1 - 1 = j - 2 := by ring
      simpa only [heq] using hh
    have hi := cusp_indices_B j
    change cuspDelta P false j ≠ 0
    simp only [cuspDelta, hi.1, hi.2.1, he, det_smul_right]
    exact mul_ne_zero hr.ne hd

theorem cusp_unused_disjoint (hn : 4 ≤ n) {P : LabelledTuple n} {j : ZMod n}
    (hz : pointZeroTriples P = {turnSupport j}) {b : Bool} (hc : CuspCase P j b) :
    ¬ (edgeSegment P (cuspFirst (!b) j) ∩ edgeSegment P (cuspLast (!b) j)).Nonempty := by
  have hd := cusp_unused_delta_ne_zero hn hz hc
  have hturn : det (edge P (j - 1)) (edge P j) = 0 := by
    exact sign_eq_zero_iff.mp ((turn_det P j) ▸ singlePointTriple_turn_zero hz)
  cases b
  · have hi := cusp_indices_A j
    have hx : det (edge P (j - 1)) (P (j + 1) - P (j - 1)) = 0 := by
      have he : det (edge P (j - 1)) (P (j + 1) - P (j - 1)) =
          det (edge P (j - 1)) (edge P j) := by
        simp only [edge, sub_add_cancel]
        dsimp [det]; ring
      rw [he, hturn]
    have hline := edgeLine_parameter_of_det_zero (singlePointTriple_edge_ne_zero hn hz (j - 1)) hx
    have hout : P (j + 1) ∉ edgeSegment P (j - 1) := by
      rintro ⟨t, ht0, ht1, ht⟩
      apply strictBetween_right_not_on_left hc
      refine ⟨1 - t, by linarith, by linarith, ?_⟩
      apply affine_segment_reverse
      simpa only [edgePoint, edge, sub_add_cancel] using ht
    change ¬ (edgeSegment P (cuspFirst true j) ∩ edgeSegment P (cuspLast true j)).Nonempty
    change cuspDelta P true j ≠ 0 at hd
    simp only [cuspDelta, hi.1, hi.2.1] at hd ⊢
    exact segments_disjoint_of_exterior_line_contact hd hline
      ⟨0, by simp [edgePoint]⟩ hout
  · have hi := cusp_indices_B j
    have hx : det (edge P j) (P (j - 1) - P j) = 0 := by
      have he : det (edge P j) (P (j - 1) - P j) =
          det (edge P (j - 1)) (edge P j) := by
        simp only [edge, sub_add_cancel]
        dsimp [det]; ring
      rw [he, hturn]
    have hline := edgeLine_parameter_of_det_zero (singlePointTriple_edge_ne_zero hn hz j) hx
    have hout : P (j - 1) ∉ edgeSegment P j := by
      rintro ⟨t, ht0, ht1, ht⟩
      apply strictBetween_right_not_on_left (strictBetween_reverse hc)
      exact ⟨t, ht0, ht1, ht⟩
    have hlast : ∃ t : ℝ, P (j - 1) = edgePoint P (j - 2) t := by
      refine ⟨1, ?_⟩
      rw [edgePoint_one]
      congr 1
      ring
    change ¬ (edgeSegment P (cuspFirst false j) ∩ edgeSegment P (cuspLast false j)).Nonempty
    change cuspDelta P false j ≠ 0 at hd
    simp only [cuspDelta, hi.1, hi.2.1] at hd ⊢
    have hd' : det (edge P j) (edge P (j - 2)) ≠ 0 := by
      rw [det_swap]; exact neg_ne_zero.mpr hd
    have hh := segments_disjoint_of_exterior_line_contact hd' hline hlast hout
    simpa only [Set.inter_comm] using hh

theorem cusp_unused_disjoint_persists (hn : 4 ≤ n) {P : LabelledTuple n} {j : ZMod n}
    (hz : pointZeroTriples P = {turnSupport j}) {b : Bool} (hc : CuspCase P j b) :
    ∀ᶠ Q in 𝓝 P, ¬ IsCrossing Q {cuspFirst (!b) j, cuspLast (!b) j} := by
  let i := cuspFirst (!b) j
  let k := cuspLast (!b) j
  have hd : ¬ segmentsMeet (P i) (P k) (edge P i) (edge P k) := by
    intro hm
    obtain ⟨x, hx, hy⟩ := (segmentsMeet_iff _ _ _ _).mp hm
    exact cusp_unused_disjoint hn hz hc ⟨x, hx, hy⟩
  have hp := disjoint_segments_persist (continuous_vertex i).continuousAt
    (continuous_vertex k).continuousAt (continuous_edge i).continuousAt
    (continuous_edge k).continuousAt hd
  filter_upwards [hp] with Q hQ
  rw [isCrossing_pair Q i k (cusp_newborn_remote hn (!b) j)]
  rintro ⟨x, hx, hy⟩
  exact hQ ((segmentsMeet_iff _ _ _ _).mpr ⟨x, hx, hy⟩)

end SM
