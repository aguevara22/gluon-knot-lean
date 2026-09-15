import SM.StrictBetween

/-! Closed affine segment parameters at a strict subdivision point. -/

namespace SM

theorem affine_segment_reverse {a b x : Plane} {t : ℝ}
    (h : x = a + t • (b - a)) : x = b + (1 - t) • (a - b) := by
  rw [h]
  ext <;> dsimp <;> ring

theorem strictBetween_right_not_on_left {a x b : Plane} (h : StrictBetween a x b) :
    ¬ ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ b = a + s • (x - a) := by
  rintro ⟨s, _, hs1, hs⟩
  have hw : b - a ≠ 0 := sub_ne_zero.mpr h.1.symm
  obtain ⟨t, ht0, ht1, hu, _⟩ := strictBetween_fusion h
  have he : (1 : ℝ) • (b - a) = (s * t) • (b - a) := by
    rw [one_smul, ← smul_smul, ← hu, hs]
    abel
  have hst : 1 = s * t := smul_left_injective ℝ hw he
  have hle := mul_le_mul_of_nonneg_right hs1 ht0.le
  nlinarith

theorem strictBetween_left_not_on_right {a x b : Plane} (h : StrictBetween a x b) :
    ¬ ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ a = x + s • (b - x) := by
  rintro ⟨s, hs0, hs1, hs⟩
  apply strictBetween_right_not_on_left (strictBetween_reverse h)
  exact ⟨1 - s, sub_nonneg.mpr hs1, by linarith, affine_segment_reverse hs⟩

theorem strictBetween_subsegments_intersection {a x b y : Plane}
    (h : StrictBetween a x b) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hy1 : y = a + s • (x - a)) (hy2 : y = x + t • (b - x)) : y = x := by
  have hw : b - a ≠ 0 := sub_ne_zero.mpr h.1.symm
  obtain ⟨r, hr0, hr1, hx⟩ := h.2
  obtain ⟨r', _, _, hu, hv⟩ := strictBetween_fusion h
  have hrr : r' = r := by
    apply smul_left_injective ℝ hw
    change r' • (b - a) = r • (b - a)
    rw [← hu, hx]
    abel
  subst r'
  have hleft : y = a + (s * r) • (b - a) := by rw [hy1, hu, smul_smul]
  have hright : y = a + (r + t * (1 - r)) • (b - a) := by
    rw [hy2, hv, hx, smul_smul, add_smul]
    abel
  have he : s * r = r + t * (1 - r) :=
    smul_left_injective ℝ hw (add_left_cancel (hleft.symm.trans hright))
  have hsle := mul_le_mul_of_nonneg_right hs1 hr0.le
  have htpos := mul_nonneg ht0 (sub_pos.mpr hr1).le
  have hs : s = 1 := by nlinarith
  rw [hy1, hs, one_smul]
  abel

end SM
