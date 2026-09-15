import SM.AffineSegments

/-! The two exclusive strict betweenness cases for three distinct collinear
points whose named cusp vertex lies outside the closed opposite segment. -/

namespace SM

theorem strictBetween_of_exterior_parameter {A M B : Plane} (hAB : A ≠ B)
    {r : ℝ} (hr : M = A + r • (B - A)) (houtside : ¬ (0 ≤ r ∧ r ≤ 1)) :
    StrictBetween A B M ∨ StrictBetween M A B := by
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr hAB.symm
  have hMA : M - A = r • (B - A) := by rw [hr]; abel
  by_cases hr0 : r < 0
  · right
    have hMB : M ≠ B := by
      intro he
      have heq : r = 1 := smul_left_injective ℝ hBA (by
        change r • (B - A) = 1 • (B - A)
        rw [← hMA, he, one_smul])
      linarith
    have hden : 0 < 1 - r := by linarith
    refine ⟨hMB, -r / (1 - r), div_pos (neg_pos.mpr hr0) hden, ?_, ?_⟩
    · apply (div_lt_one hden).mpr
      linarith
    · rw [hr]
      ext <;> dsimp <;> field_simp [hden.ne'] <;> ring
  · left
    have hr1 : 1 < r := lt_of_not_ge (fun hr1 => houtside ⟨le_of_not_gt hr0, hr1⟩)
    have hrpos : 0 < r := by linarith
    have hAM : A ≠ M := by
      intro he
      have heq : r = 0 := smul_left_injective ℝ hBA (by
        change r • (B - A) = 0 • (B - A)
        rw [← hMA, ← he, sub_self, zero_smul])
      linarith
    refine ⟨hAM, 1 / r, div_pos zero_lt_one hrpos, (div_lt_one hrpos).mpr hr1, ?_⟩
    rw [hMA, smul_smul, one_div_mul_cancel hrpos.ne', one_smul]
    abel

theorem collinear_exterior_cases {A M B : Plane} (hAB : A ≠ B)
    (hc : det (B - A) (M - A) = 0)
    (hout : ¬ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ M = A + t • (B - A)) :
    (StrictBetween A B M ∨ StrictBetween M A B) ∧
      ¬ (StrictBetween A B M ∧ StrictBetween M A B) := by
  let r := planeDot (B - A) (M - A) / planeDot (B - A) (B - A)
  have he : M - A = r • (B - A) := scalar_of_det_zero (sub_ne_zero.mpr hAB.symm) hc
  have hr : M = A + r • (B - A) := by rw [← he]; abel
  refine ⟨strictBetween_of_exterior_parameter hAB hr (fun h => hout ⟨r, h.1, h.2, hr⟩), ?_⟩
  rintro ⟨hA, hB⟩
  obtain ⟨t, ht0, ht1, ht⟩ := hB.2
  exact strictBetween_right_not_on_left (strictBetween_reverse hA) ⟨t, ht0.le, ht1.le, ht⟩

end SM
