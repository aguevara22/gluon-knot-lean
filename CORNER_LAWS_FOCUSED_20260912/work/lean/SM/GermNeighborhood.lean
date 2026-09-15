import SM.GermDefinition

/-! The exact bridge from a neighbourhood in the genuine interval subtype to
one common positive real radius on both punctured sides. -/

namespace SM.WallGerm

open Filter Topology

variable {n : ℕ} (g : WallGerm n)

theorem eventually_center_iff_radius (A : g.Parameter → Prop) :
    (∀ᶠ t in 𝓝 g.zeroParameter, A t) ↔
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter, |t.val| < δ → A t := by
  constructor
  · intro h
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp h
    refine ⟨min δ g.radius, lt_min hδ g.radius_pos, min_le_right _ _, ?_⟩
    intro t ht
    apply hball
    change dist t g.zeroParameter < δ
    change dist t.val (0 : ℝ) < δ
    rw [Real.dist_eq, sub_zero]
    exact lt_of_lt_of_le ht (min_le_left _ _)
  · rintro ⟨δ, hδ, _, h⟩
    apply Filter.mem_of_superset (Metric.ball_mem_nhds g.zeroParameter hδ)
    intro t ht
    apply h t
    change dist t.val (0 : ℝ) < δ at ht
    simpa only [Real.dist_eq, sub_zero] using ht

end SM.WallGerm
