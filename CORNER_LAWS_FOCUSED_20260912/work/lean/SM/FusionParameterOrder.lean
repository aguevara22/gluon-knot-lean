import SM.FusionVisits

/-! Actual within-piece visit order and the strict separation between visits
on the first and second pieces of the fused edge. Full cyclic-cut transport
is a separate remaining obligation. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem fusionParameter_strictMono {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (j k : ZMod (n + 1)) : StrictMono (fusionParameter r j k) := by
  intro a b hab
  unfold fusionParameter
  split_ifs
  · simpa only [add_comm] using add_lt_add_left (mul_lt_mul_of_pos_left hab (sub_pos.mpr hr1)) r
  · exact mul_lt_mul_of_pos_left hab hr0
  · exact hab

theorem fusionParameter_first_lt_second {r a b : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (ha1 : a < 1) (hb0 : 0 < b) (j : ZMod (n + 1)) :
    fusionParameter r j (j - 1) a < fusionParameter r j j b := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  letI : Fact (1 < n + 1) := ⟨by omega⟩
  simp only [fusionParameter, prev_ne_self j, ↓reduceIte]
  have ha : r * a < r := by simpa only [mul_one] using mul_lt_mul_of_pos_left ha1 hr0
  have hb : r < r + (1 - r) * b := lt_add_of_pos_right r (mul_pos (sub_pos.mpr hr1) hb0)
  exact ha.trans hb

theorem fusionVisit_same_edge_order (hn : 3 ≤ n)
    {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) (v w : Visit P) (hedge : v.2.val = w.2.val) :
    visitParameter (fusionVisitEquiv hn hz hb hc v) <
      visitParameter (fusionVisitEquiv hn hz hb hc w) ↔ visitParameter v < visitParameter w := by
  obtain ⟨r, hr0, hr1, hm⟩ := hb.2
  rw [visitParameter_fusion hn hz hb hc hm v, visitParameter_fusion hn hz hb hc hm w, hedge]
  exact (fusionParameter_strictMono hr0 hr1 j w.2.val).lt_iff_lt

theorem fusionVisit_first_before_second (hn : 3 ≤ n)
    {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) (v w : Visit P)
    (hv : v.2.val = j - 1) (hw : w.2.val = j) :
    visitParameter (fusionVisitEquiv hn hz hb hc v) <
      visitParameter (fusionVisitEquiv hn hz hb hc w) := by
  obtain ⟨r, hr0, hr1, hm⟩ := hb.2
  have hgeom := flat_crossingGeometry (by omega) hz hb hc
  have hvp := crossingParameter_interior_of_geometry hgeom v.1 v.2.val v.2.property
  have hwp := crossingParameter_interior_of_geometry hgeom w.1 w.2.val w.2.property
  rw [visitParameter_fusion hn hz hb hc hm v, visitParameter_fusion hn hz hb hc hm w, hv, hw]
  exact fusionParameter_first_lt_second hr0 hr1 hvp.2 hwp.1 j

end SM
