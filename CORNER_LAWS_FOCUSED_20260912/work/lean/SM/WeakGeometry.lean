import SM.WeakGeneric

/-! Geometry for lem:weak-open, using exactly weak hypotheses, never G1. -/

namespace SM

variable {n : ℕ}

theorem nonincident_iff (k i : ZMod n) :
    ¬ incident k i ↔ k ≠ i ∧ k ≠ i + 1 := by
  constructor
  · intro h
    refine ⟨fun he => h (Or.inr he.symm), ?_⟩
    intro he
    apply h
    left
    rw [he, add_sub_cancel_right]
  · rintro ⟨h0, h1⟩ (he | he)
    · apply h1
      linear_combination -he
    · exact h0 he.symm

theorem turns_successive_intersection {P : LabelledTuple n}
    (hturn : ∀ i, turn P i ≠ 0) (i : ZMod n) :
    edgeSegment P i ∩ edgeSegment P (i + 1) = {P (i + 1)} := by
  have hd : det (edge P i) (edge P (i + 1)) ≠ 0 := by
    have ht := hturn (i + 1)
    rw [turn_det] at ht
    simpa only [add_sub_cancel_right] using sign_ne_zero.mp ht
  have hbase : edgePoint P i 1 = edgePoint P (i + 1) 0 := by
    rw [edgePoint_one, edgePoint_zero]
  ext x
  constructor
  · rintro ⟨⟨s, _, _, hs⟩, ⟨t, _, _, ht⟩⟩
    have hp := intersection_parameters_unique hd (hs.symm.trans ht) hbase
    change x = P (i + 1)
    rw [hs, hp.1, edgePoint_one]
  · intro hx
    have hx' : x = P (i + 1) := hx
    subst x
    exact ⟨⟨1, by norm_num, le_rfl, (edgePoint_one P i).symm⟩,
      ⟨0, le_rfl, by norm_num, (edgePoint_zero P (i + 1)).symm⟩⟩

theorem turns_adjacent_intersection {P : LabelledTuple n}
    (hturn : ∀ i, turn P i ≠ 0) {i j : ZMod n} (hne : i ≠ j) (hadj : adjacent i j) :
    (j = i + 1 ∧ edgeSegment P i ∩ edgeSegment P j = {P j}) ∨
    (i = j + 1 ∧ edgeSegment P i ∩ edgeSegment P j = {P i}) := by
  rcases adjacent_distinct_cases hne hadj with he | he
  · left
    refine ⟨he, ?_⟩
    subst j
    exact turns_successive_intersection hturn i
  · right
    refine ⟨he, ?_⟩
    subst i
    rw [Set.inter_comm]
    exact turns_successive_intersection hturn j

theorem weak_base_common_interiors_remote {P : LabelledTuple n}
    (hedge : ∀ i, edge P i ≠ 0) (hturn : ∀ i, turn P i ≠ 0)
    {i j : ZMod n} (hne : i ≠ j) {x : Plane}
    (hi : x ∈ edgeInterior P i) (hj : x ∈ edgeInterior P j) : remote i j := by
  intro hadj
  have hc : x ∈ edgeSegment P i ∩ edgeSegment P j :=
    ⟨edgeInterior_subset_edgeSegment P i hi, edgeInterior_subset_edgeSegment P j hj⟩
  rcases turns_adjacent_intersection hturn hne hadj with ⟨_, hset⟩ | ⟨_, hset⟩
  · rw [hset] at hc
    have hx : x = P j := hc
    obtain ⟨t, ht0, _, ht⟩ := hj
    have hparam : t = 0 := edgePoint_injective (hedge j)
      (ht.symm.trans (hx.trans (edgePoint_zero P j).symm))
    exact (ne_of_gt ht0) hparam
  · rw [hset] at hc
    have hx : x = P i := hc
    obtain ⟨s, hs0, _, hs⟩ := hi
    have hparam : s = 0 := edgePoint_injective (hedge i)
      (hs.symm.trans (hx.trans (edgePoint_zero P i).symm))
    exact (ne_of_gt hs0) hparam

theorem remote_closed_point_interior {P : LabelledTuple n}
    (hvertex : ∀ k i, ¬ incident k i → P k ∉ edgeSegment P i)
    {i j : ZMod n} (hr : remote i j) {x : Plane}
    (hi : x ∈ edgeSegment P i) (hj : x ∈ edgeSegment P j) : x ∈ edgeInterior P i := by
  obtain ⟨s, hs0, hs1, hs⟩ := hi
  obtain ⟨hj0, hj1, hjp0, hjp1⟩ := remote_endpoints i j hr
  have hsne0 : s ≠ 0 := by
    intro he
    have hx : x = P i := by simpa [he, edgePoint] using hs
    exact hvertex i j ((nonincident_iff i j).mpr ⟨hj0.symm, hjp0.symm⟩) (hx ▸ hj)
  have hsne1 : s ≠ 1 := by
    intro he
    have hx : x = P (i + 1) := by simpa [he, edgePoint, edge] using hs
    exact hvertex (i + 1) j ((nonincident_iff (i + 1) j).mpr
      ⟨hj1.symm, hjp1.symm⟩) (hx ▸ hj)
  exact ⟨s, lt_of_le_of_ne hs0 hsne0.symm, lt_of_le_of_ne hs1 hsne1, hs⟩

theorem weak_base_g2_iff_no_remote_closed_triples {P : LabelledTuple n}
    (hedge : ∀ i, edge P i ≠ 0) (hturn : ∀ i, turn P i ≠ 0)
    (hvertex : ∀ k i, ¬ incident k i → P k ∉ edgeSegment P i) :
    G2 P ↔ ∀ i j k, remote i j → remote j k → remote i k → ¬ ClosedTripleMeet P i j k := by
  constructor
  · intro hG i j k hij hjk hik
    rintro ⟨x, hi, hj, hk⟩
    exact hG ⟨i, j, k, x, (remote_endpoints i j hij).1.symm,
      (remote_endpoints j k hjk).1.symm, (remote_endpoints i k hik).1.symm,
      remote_closed_point_interior hvertex hij hi hj,
      remote_closed_point_interior hvertex (remote_symm hij) hj hi,
      remote_closed_point_interior hvertex (remote_symm hik) hk hi⟩
  · intro hG
    rintro ⟨i, j, k, x, hij, hjk, hik, hi, hj, hk⟩
    exact hG i j k (weak_base_common_interiors_remote hedge hturn hij hi hj)
      (weak_base_common_interiors_remote hedge hturn hjk hj hk)
      (weak_base_common_interiors_remote hedge hturn hik hi hk)
      ⟨x, edgeInterior_subset_edgeSegment P i hi, edgeInterior_subset_edgeSegment P j hj,
        edgeInterior_subset_edgeSegment P k hk⟩

theorem transverse_segments_unique {P : LabelledTuple n} {i j : ZMod n}
    (hd : det (edge P i) (edge P j) ≠ 0) {x y : Plane}
    (hxi : x ∈ edgeSegment P i) (hxj : x ∈ edgeSegment P j)
    (hyi : y ∈ edgeSegment P i) (hyj : y ∈ edgeSegment P j) : x = y := by
  obtain ⟨s, _, _, hs⟩ := hxi
  obtain ⟨t, _, _, ht⟩ := hxj
  obtain ⟨s', _, _, hs'⟩ := hyi
  obtain ⟨t', _, _, ht'⟩ := hyj
  have hp := intersection_parameters_unique hd (hs.symm.trans ht) (hs'.symm.trans ht')
  rw [hs, hs', hp.1]

end SM
