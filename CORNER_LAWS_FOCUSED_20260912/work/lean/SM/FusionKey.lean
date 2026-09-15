import SM.FusionParameterOrder
import SM.TraversalRelabel

/-! Actual traversal-coordinate compression under fusion. The piecewise affine
map is strictly increasing and transports the actual shifted visit keys; this
proves global cyclic visit order without assuming Generic at the flat centre. -/

namespace SM

noncomputable def positiveBend (c r x : ℝ) : ℝ :=
  if x < c then x else c + r * (x - c)

theorem positiveBend_strictMono (c : ℝ) {r : ℝ} (hr : 0 < r) :
    StrictMono (positiveBend c r) := by
  intro x y hxy
  by_cases hx : x < c
  · by_cases hy : y < c
    · simpa only [positiveBend, hx, hy, ↓reduceIte] using hxy
    · simp only [positiveBend, hx, hy, ↓reduceIte]
      have hp := mul_nonneg hr.le (sub_nonneg.mpr (le_of_not_gt hy))
      linarith
  · by_cases hy : y < c
    · exact (hx (hxy.trans hy)).elim
    · simp only [positiveBend, hx, hy, ↓reduceIte]
      have hp := mul_pos hr (sub_pos.mpr hxy)
      nlinarith

theorem positiveBend_upper (c r : ℝ) : positiveBend c r (c + 1) = c + r := by
  have hc : ¬ c + 1 < c := by linarith
  simp only [positiveBend, hc, ↓reduceIte]
  ring

noncomputable def fusionKey (c r x : ℝ) : ℝ :=
  if x < c + 1 then positiveBend c r x else c + r + (1 - r) * (x - (c + 1))

theorem fusionKey_strictMono (c : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    StrictMono (fusionKey c r) := by
  intro x y hxy
  by_cases hx : x < c + 1
  · by_cases hy : y < c + 1
    · simp only [fusionKey, hx, hy, ↓reduceIte]
      exact positiveBend_strictMono c hr0 hxy
    · simp only [fusionKey, hx, hy, ↓reduceIte]
      have hxb := positiveBend_strictMono c hr0 hx
      rw [positiveBend_upper] at hxb
      have hp := mul_nonneg (sub_pos.mpr hr1).le (sub_nonneg.mpr (le_of_not_gt hy))
      linarith
  · by_cases hy : y < c + 1
    · exact (hx (hxy.trans hy)).elim
    · simp only [fusionKey, hx, hy, ↓reduceIte]
      have hp := mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hxy)
      nlinarith

theorem fusionKey_low {c r x : ℝ} (hx : x < c) : fusionKey c r x = x := by
  have hx' : x < c + 1 := by linarith
  simp only [fusionKey, positiveBend, hx, hx', ↓reduceIte]

theorem fusionKey_middle {c r x : ℝ} (hx : c ≤ x) (hx' : x < c + 1) :
    fusionKey c r x = c + r * (x - c) := by
  simp only [fusionKey, positiveBend, hx', not_lt.mpr hx, ↓reduceIte]

theorem fusionKey_high {c r x : ℝ} (hx : c + 1 ≤ x) :
    fusionKey c r x = c + r + (1 - r) * (x - (c + 1)) := by
  simp only [fusionKey, not_lt.mpr hx, ↓reduceIte]

theorem retained_shift_index {n : ℕ} [NeZero n] {j k : ZMod (n + 1)} (hk : k ≠ j) :
    k - (j + 1) = insertIndex (fusionIndex j k) := by
  obtain ⟨i, rfl⟩ := deletionIndex_exhaust j hk
  rw [fusionIndex_deletionIndex]
  simp only [deletionIndex, add_sub_cancel_right]

theorem fusionVisitKey_compression {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) {r : ℝ}
    (hm : P j = P (j - 1) + r • (P (j + 1) - P (j - 1))) (v : Visit P) :
    geometricVisitKey (generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc))
      (fusionVisitEquiv hn hz hb hc v) =
    fusionKey ((n : ℝ) - 1) r
      (traversalKey (traversalShift (j + 1)
        (geometricVisitPosition (flat_crossingGeometry (by omega) hz hb hc) v))) := by
  let k := v.2.val
  let t := visitParameter v
  have ht : 0 < t ∧ t < 1 := crossingParameter_interior_of_geometry
    (flat_crossingGeometry (by omega) hz hb hc) v.1 v.2.val v.2.property
  change ((fusionIndex j k).val : ℝ) + visitParameter (fusionVisitEquiv hn hz hb hc v) =
    fusionKey ((n : ℝ) - 1) r (((k - (j + 1)).val : ℝ) + t)
  rw [visitParameter_fusion hn hz hb hc hm v]
  change ((fusionIndex j k).val : ℝ) + fusionParameter r j k t = _
  have hlast : ((-1 : ZMod n).val : ℝ) = (n : ℝ) - 1 := by
    have he : ((-1 : ZMod n).val : ℝ) + 1 = (n : ℝ) := by
      exact_mod_cast (last_index_val_succ (n := n))
    linarith
  by_cases hk : k = j
  · rw [hk, fusionIndex_deleted, hlast]
    have he : j - (j + 1) = (-1 : ZMod (n + 1)) := by ring
    have hv : ((-1 : ZMod (n + 1)).val : ℝ) = (n : ℝ) := by
      rw [← insertedIndex_eq_neg_one, insertedIndex_val]
    rw [he, hv]
    simp only [fusionParameter, ↓reduceIte]
    rw [fusionKey_high (by linarith [ht.1])]
    ring
  · rw [retained_shift_index hk, insertIndex_val]
    by_cases hp : k = j - 1
    · have hne : j - 1 ≠ j := fun he => hk (hp.trans he)
      rw [hp, fusionIndex_prev, hlast]
      simp only [fusionParameter, hne, ↓reduceIte]
      rw [fusionKey_middle (by linarith [ht.1]) (by linarith [ht.2])]
      ring
    · simp only [fusionParameter, hk, hp, ↓reduceIte]
      have hnat : (fusionIndex j k).val + 2 ≤ n := by
        have hv := (fusionIndex j k).val_lt
        have hl := last_index_val_succ (n := n)
        by_contra h
        have he : (fusionIndex j k).val = (-1 : ZMod n).val := by omega
        exact fusionIndex_ne_last hk hp (ZMod.val_injective n he)
      have hreal : ((fusionIndex j k).val : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hnat
      exact (fusionKey_low (by linarith [ht.2])).symm

theorem fusionVisit_cyclic_order {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) (v w u : Visit P) :
    traversalBetween
      (geometricVisitPosition (generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc))
        (fusionVisitEquiv hn hz hb hc v))
      (geometricVisitPosition (generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc))
        (fusionVisitEquiv hn hz hb hc w))
      (geometricVisitPosition (generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc))
        (fusionVisitEquiv hn hz hb hc u)) ↔
    traversalBetween
      (geometricVisitPosition (flat_crossingGeometry (by omega) hz hb hc) v)
      (geometricVisitPosition (flat_crossingGeometry (by omega) hz hb hc) w)
      (geometricVisitPosition (flat_crossingGeometry (by omega) hz hb hc) u) := by
  let hP := flat_crossingGeometry (by omega) hz hb hc
  let hQ := generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc)
  let e := fusionVisitEquiv hn hz hb hc
  obtain ⟨r, hr0, hr1, hm⟩ := hb.2
  have hmono := fusionKey_strictMono ((n : ℝ) - 1) hr0 hr1
  have hkey (x : Visit P) : geometricVisitKey hQ (e x) =
      fusionKey ((n : ℝ) - 1) r
        (traversalKey (traversalShift (j + 1) (geometricVisitPosition hP x))) :=
    fusionVisitKey_compression hn hz hb hc hm x
  have hiff (x y : Visit P) :
      traversalKey (geometricVisitPosition hQ (e x)) <
        traversalKey (geometricVisitPosition hQ (e y)) ↔
      traversalKey (traversalShift (j + 1) (geometricVisitPosition hP x)) <
        traversalKey (traversalShift (j + 1) (geometricVisitPosition hP y)) := by
    change geometricVisitKey hQ (e x) < geometricVisitKey hQ (e y) ↔ _
    rw [hkey x, hkey y]
    exact hmono.lt_iff_lt
  have he : traversalBetween (geometricVisitPosition hQ (e v))
      (geometricVisitPosition hQ (e w)) (geometricVisitPosition hQ (e u)) ↔
      traversalBetween (traversalShift (j + 1) (geometricVisitPosition hP v))
        (traversalShift (j + 1) (geometricVisitPosition hP w))
        (traversalShift (j + 1) (geometricVisitPosition hP u)) := by
    simp only [traversalBetween, hiff]
  exact he.trans (traversalBetween_shift (j + 1) _ _ _)

end SM
