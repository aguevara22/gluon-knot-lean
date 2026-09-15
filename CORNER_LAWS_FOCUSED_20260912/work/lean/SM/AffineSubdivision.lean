import SM.StrictBetween

/-! An interior point of the whole oriented segment, other than its strict
subdivision point, belongs to one of the two open subsegments. -/

namespace SM

theorem affine_interior_subdivision {a m b x : Plane} {r q : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1)
    (hm : m = a + r • (b - a)) (hq0 : 0 < q) (hq1 : q < 1)
    (hx : x = a + q • (b - a)) (hxm : x ≠ m) :
    (∃ s : ℝ, 0 < s ∧ s < 1 ∧ x = a + s • (m - a)) ∨
    (∃ s : ℝ, 0 < s ∧ s < 1 ∧ x = m + s • (b - m)) := by
  have hqr : q ≠ r := by
    intro he
    exact hxm (by rw [hx, he, ← hm])
  have hu : m - a = r • (b - a) := by rw [hm]; abel
  have hv : b - m = (1 - r) • (b - a) := by
    rw [hm]
    ext <;> dsimp <;> ring
  rcases lt_or_gt_of_ne hqr with hlt | hgt
  · left
    refine ⟨q / r, div_pos hq0 hr0, (div_lt_one hr0).mpr hlt, ?_⟩
    rw [hu, smul_smul, div_mul_cancel₀ _ hr0.ne']
    exact hx
  · right
    have hden : 0 < 1 - r := sub_pos.mpr hr1
    refine ⟨(q - r) / (1 - r), div_pos (sub_pos.mpr hgt) hden,
      (div_lt_one hden).mpr (by linarith), ?_⟩
    rw [hv, smul_smul, div_mul_cancel₀ _ hden.ne', hm, hx]
    ext <;> dsimp <;> ring

end SM
