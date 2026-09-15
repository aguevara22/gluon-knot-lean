import SM.CuspDefinition
import SM.SingleTripleTransverse

/-! Actual nonzero cusp edges, the two remote newborn pairs, the nonzero
selected determinant and the unique antiparallel central corner. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {j : ZMod n}

theorem remote_two_step (hn : 4 ≤ n) (i : ZMod n) : remote i (i + 2) := by
  have h1 := small_natCast_ne_zero (n := n) (m := 1) (by omega) (by omega)
  have h2 := small_natCast_ne_zero (n := n) (m := 2) (by omega) (by omega)
  have h3 := small_natCast_ne_zero (n := n) (m := 3) (by omega) (by omega)
  rintro (he | he | he)
  · exact h3 (by linear_combination he)
  · exact h2 (by linear_combination he)
  · exact h1 (by linear_combination he)

theorem cusp_newborn_remote (hn : 4 ≤ n) (b : Bool) (j : ZMod n) :
    remote (cuspFirst b j) (cuspLast b j) := remote_two_step hn _

theorem cusp_delta_ne_zero (hn : 4 ≤ n) (hz : pointZeroTriples P = {turnSupport j})
    {b : Bool} (hc : CuspCase P j b) : cuspDelta P b j ≠ 0 := by
  have hr := cusp_newborn_remote hn b j
  cases b
  · have hi := (cusp_indices_B j)
    simp only [hi.1, hi.2.1] at hr
    have hm : P (j - 1) ∈ edgeSegment P (j - 2) := by
      refine ⟨1, by norm_num, by norm_num, ?_⟩
      simp only [edgePoint_one]
      congr 1
      ring
    have hn' : P (j - 1) ∈ edgeSegment P j :=
      edgeInterior_subset_edgeSegment P j hc.2
    change det (edge P (cuspFirst false j)) (edge P (cuspLast false j)) ≠ 0
    rw [hi.1, hi.2.1]
    exact singlePointTriple_remote_transverse hn hz hr hm hn'
  · have hi := cusp_indices_A j
    simp only [hi.1, hi.2.1] at hr
    have hm : P (j + 1) ∈ edgeSegment P (j - 1) := by
      obtain ⟨r, hr0, hr1, hr⟩ := hc.2
      exact ⟨r, hr0.le, hr1.le, by simpa only [edgePoint, edge, sub_add_cancel] using hr⟩
    have hn' : P (j + 1) ∈ edgeSegment P (j + 1) := ⟨0, le_rfl, zero_le_one, by simp [edgePoint]⟩
    change det (edge P (cuspFirst true j)) (edge P (cuspLast true j)) ≠ 0
    rw [hi.1, hi.2.1]
    exact singlePointTriple_remote_transverse hn hz hr hm hn'

theorem cusp_negative_pair {b : Bool} (hc : CuspCase P j b) :
    ∃ r : ℝ, r < 0 ∧ edge P j = r • edge P (j - 1) := by
  cases b
  · obtain ⟨_, t, ht0, ht1, ht⟩ := hc
    have he : edge P (j - 1) = (-t) • edge P j := by
      simp only [edge, sub_add_cancel]
      rw [ht]
      ext <;> dsimp <;> ring
    refine ⟨-1 / t, div_neg_of_neg_of_pos (by norm_num) ht0, ?_⟩
    rw [he, smul_smul]
    have hs : (-1 / t) * -t = 1 := by field_simp
    rw [hs, one_smul]
  · obtain ⟨_, t, ht0, ht1, ht⟩ := hc
    refine ⟨t - 1, sub_neg.mpr ht1, ?_⟩
    simp only [edge, sub_add_cancel]
    rw [ht]
    ext <;> dsimp <;> ring

theorem cusp_other_turn_regular (hn : 4 ≤ n) (hz : pointZeroTriples P = {turnSupport j})
    {i : ZMod n} (hi : i ≠ j) : RegularPair (edge P (i - 1)) (edge P i) := by
  have hd : det (edge P (i - 1)) (edge P i) ≠ 0 :=
    sign_ne_zero.mp ((turn_det P i) ▸ singlePointTriple_turn_ne_zero hn hz hi)
  refine ⟨singlePointTriple_edge_ne_zero hn hz _, singlePointTriple_edge_ne_zero hn hz _, ?_⟩
  rintro ⟨r, _, hr⟩
  exact no_multiple_of_det_ne_zero hd r hr

theorem cusp_rotor_negative_real (hn : 4 ≤ n) (hz : pointZeroTriples P = {turnSupport j})
    {b : Bool} (hc : CuspCase P j b) :
    (cornerRotor (edge P (j - 1)) (edge P j)).re < 0 ∧
      (cornerRotor (edge P (j - 1)) (edge P j)).im = 0 := by
  rw [cornerRotor_re, cornerRotor_im]
  exact (negativeScalar_iff_dot_det (singlePointTriple_edge_ne_zero hn hz _)).mp (cusp_negative_pair hc)

theorem cusp_not_regular {b : Bool} (hc : CuspCase P j b) : ¬ Regular P :=
  fun h => (h j).2.2 (cusp_negative_pair hc)

end SM
