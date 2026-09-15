import SM.FlatContacts
import SM.FlatCenter

/-! Adjacent flat-centre edges meet only at their common endpoint. This
includes the positive collinear pair and yields full central G2 from the
printed absence of pairwise-remote concurrence triples. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {j : ZMod n}

theorem flat_successive_intersection (hn : 4 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1))) (i : ZMod n) :
    edgeSegment P i ∩ edgeSegment P (i + 1) = {P (i + 1)} := by
  ext x
  constructor
  · rintro ⟨hxi, hxnext⟩
    change x = P (i + 1)
    by_cases hi : i + 1 = j
    · have hij : i = j - 1 := by linear_combination hi
      have hbet : StrictBetween (P i) (P (i + 1)) (P (i + 1 + 1)) := by
        simpa only [hij, sub_add_cancel] using hb
      obtain ⟨s, hs0, hs1, hs⟩ := hxi
      obtain ⟨t, ht0, ht1, ht⟩ := hxnext
      exact strictBetween_subsegments_intersection hbet hs0 hs1 ht0 ht1 hs ht
    · have hturn := singlePointTriple_turn_ne_zero hn hz hi
      rw [turn_det] at hturn
      have hd : det (edge P i) (edge P (i + 1)) ≠ 0 := by
        simpa only [add_sub_cancel_right] using sign_ne_zero.mp hturn
      exact transverse_segments_unique hd hxi hxnext
        ⟨1, by norm_num, le_rfl, (edgePoint_one P i).symm⟩
        ⟨0, le_rfl, by norm_num, (edgePoint_zero P (i + 1)).symm⟩
  · intro hx
    have hx' : x = P (i + 1) := hx
    subst x
    exact ⟨⟨1, by norm_num, le_rfl, (edgePoint_one P i).symm⟩,
      ⟨0, le_rfl, by norm_num, (edgePoint_zero P (i + 1)).symm⟩⟩

theorem flat_adjacent_intersection (hn : 4 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    {i k : ZMod n} (hne : i ≠ k) (hadj : adjacent i k) :
    (k = i + 1 ∧ edgeSegment P i ∩ edgeSegment P k = {P k}) ∨
    (i = k + 1 ∧ edgeSegment P i ∩ edgeSegment P k = {P i}) := by
  rcases adjacent_distinct_cases hne hadj with he | he
  · left
    refine ⟨he, ?_⟩
    subst k
    exact flat_successive_intersection hn hz hb i
  · right
    refine ⟨he, ?_⟩
    subst i
    rw [Set.inter_comm]
    exact flat_successive_intersection hn hz hb k

theorem flat_common_interiors_remote (hn : 4 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    {i k : ZMod n} (hne : i ≠ k) {x : Plane}
    (hi : x ∈ edgeInterior P i) (hk : x ∈ edgeInterior P k) : remote i k := by
  intro hadj
  have hc : x ∈ edgeSegment P i ∩ edgeSegment P k :=
    ⟨edgeInterior_subset_edgeSegment P i hi, edgeInterior_subset_edgeSegment P k hk⟩
  rcases flat_adjacent_intersection hn hz hb hne hadj with ⟨_, hset⟩ | ⟨_, hset⟩
  · rw [hset] at hc
    have hx : x = P k := hc
    obtain ⟨t, ht0, _, ht⟩ := hk
    have he : t = 0 := edgePoint_injective (singlePointTriple_edge_ne_zero hn hz k)
      (ht.symm.trans (hx.trans (edgePoint_zero P k).symm))
    exact ht0.ne' he
  · rw [hset] at hc
    have hx : x = P i := hc
    obtain ⟨t, ht0, _, ht⟩ := hi
    have he : t = 0 := edgePoint_injective (singlePointTriple_edge_ne_zero hn hz i)
      (ht.symm.trans (hx.trans (edgePoint_zero P i).symm))
    exact ht0.ne' he

theorem flat_center_g2 (hn : 4 ≤ n) (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) : G2 P := by
  rintro ⟨i, k, l, x, hik, hkl, hil, hi, hk, hl⟩
  have hrik := flat_common_interiors_remote hn hz hb hik hi hk
  have hrkl := flat_common_interiors_remote hn hz hb hkl hk hl
  have hril := flat_common_interiors_remote hn hz hb hil hi hl
  have hm := (mem_concurrenceTriples P {i, k, l}).mpr
    ((concurrenceTriple_iff hrik hrkl hril).mpr ⟨x, hi, hk, hl⟩)
  simpa only [hc, Finset.notMem_empty] using hm

end SM
