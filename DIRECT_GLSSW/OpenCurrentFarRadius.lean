import OpenCurrentTurnProjector

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.OpenCurrentFarRadius
open OpenFirstEdgeGeometry ShortEdgeSignStability

private theorem scalarSignValue_of_neg_iff {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x < 0 ↔ y < 0) : scalarSignValue x = scalarSignValue y := by
  by_cases hn : y < 0
  · simp [scalarSignValue, hx, hy, hn, h.mpr hn]
  · have hn' : ¬ x < 0 := mt h.mp hn
    simp [scalarSignValue, hx, hy, hn, hn']

/-- A common finite radius controls only the far determinants used by the
short-first current identity; no all-prefix genericity is assumed. -/
theorem exists_far_radius_entry_short_first (q : ℕ → PlanarPoint ℝ) (N : ℕ)
    (hfar : ∀ k j, 1 < k → k < j → j ≤ N → polygonHDet q 1 k j ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < r →
      (∀ k j, 1 < k → k < j → j ≤ N →
        polygonSignArray (approach q ε) 0 k j = polygonSignArray q 1 k j) ∧
      (∀ j, 1 < j → j ≤ N →
        OpenMarkedCurrent.entry (polygonSignArray (approach q ε)) 0 j =
          (((1 + polygonSignArray q 0 1 2) / 2) - 1) *
            OpenMarkedCurrent.entry (polygonSignArray q) 1 j) := by
  let s := Finset.range (N + 1) ×ˢ Finset.range (N + 1)
  let P : ℕ × ℕ → ℝ → Prop := fun z ε =>
    1 < z.1 → z.1 < z.2 → z.2 ≤ N →
      polygonSignArray (approach q ε) 0 z.1 z.2 = polygonSignArray q 1 z.1 z.2
  have hlocal : ∀ z, z ∈ s → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ → P z ε := by
    intro z hz
    by_cases hg : 1 < z.1 ∧ z.1 < z.2 ∧ z.2 ≤ N
    · obtain ⟨δ, hδ, hgood⟩ := exists_affine_sign_radius
        (polygonHDet q 1 z.1 z.2)
        (polygonHDet q 0 z.1 z.2 - polygonHDet q 1 z.1 z.2)
        (hfar z.1 z.2 hg.1 hg.2.1 hg.2.2)
      refine ⟨δ, hδ, ?_⟩
      intro ε hε hεδ _ _ _
      change polygonSignArray (approach q ε) 0 z.1 z.2 = polygonSignArray q 1 z.1 z.2
      unfold polygonSignArray
      rw [polygonHDet_far_affine q ε (by omega : 0 < z.1) (by omega : 0 < z.2)]
      exact scalarSignValue_of_neg_iff (hgood ε hε hεδ).1
        (hfar z.1 z.2 hg.1 hg.2.1 hg.2.2) (hgood ε hε hεδ).2
    · refine ⟨1, by norm_num, ?_⟩
      intro ε _ _ hk hkj hj
      exact False.elim (hg ⟨hk, hkj, hj⟩)
  obtain ⟨δ, hδ, hgood⟩ := exists_finset_common_radius s P hlocal
  refine ⟨min δ 1, lt_min hδ (by norm_num), min_le_right _ _, ?_⟩
  intro ε hε hεδ
  have hSigns : ∀ k j, 1 < k → k < j → j ≤ N →
      polygonSignArray (approach q ε) 0 k j = polygonSignArray q 1 k j := by
    intro k j hk hkj hj
    have hmem : (k, j) ∈ s := by simp [s]; omega
    exact hgood ε hε (lt_of_lt_of_le hεδ (min_le_left _ _)) (k, j) hmem hk hkj hj
  constructor
  · exact hSigns
  · intro j hj hjN
    have hrow : ∀ k t, 1 < k → k < t → t ≤ N →
        polygonSignArray (approach q ε) 0 k t =
          polygonSignArray (approach q ε) 1 k t := by
      intro k t hk hkt htN
      have hfirst := hSigns k t hk hkt htN
      have htail := polygonSignArray_tail q ε (by omega : 0 < 1)
        (by omega : 0 < k) (by omega : 0 < t)
      exact hfirst.trans htail.symm
    have hentry := OpenCurrentShortFirst.entry_short_first
      (polygonSignArray (approach q ε)) 0 N hrow j (by omega) hjN
    have htailM : OpenMarkedCurrent.entry (polygonSignArray (approach q ε)) 1 j =
        OpenMarkedCurrent.entry (polygonSignArray q) 1 j :=
      OpenFirstEdgeGeometry.openMarkedCurrent_tail q ε (i := 1) (j := j)
        (by omega) (by omega)
    rw [polygonSignArray_turn q hε, htailM] at hentry
    exact hentry

end DirectGLSSW.OpenCurrentFarRadius

#check @DirectGLSSW.OpenCurrentFarRadius.exists_far_radius_entry_short_first

