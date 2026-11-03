import ActiveArcExposedAuxiliary
import Mathlib.Topology.Compactness.Compact
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CursorSegmentStability
open Filter Set Topology
/-- Uniform separation on the full compact pair of segment parameters. -/
theorem eventually_parameterized_segment_separation
    (F G : ℝ → ℝ → PlanarPoint ℝ) (a b : ℝ)
    (hF : Continuous (fun z : ℝ × (ℝ × ℝ) => F z.1 z.2.1))
    (hG : Continuous (fun z : ℝ × (ℝ × ℝ) => G z.1 z.2.2))
    (hdis : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1, F 0 t ≠ G 0 s) :
    ∀ᶠ η in 𝓝 (0 : ℝ), ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
      F η t ≠ G η s := by
  have hk : IsCompact (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hh := hk.eventually_forall_of_forall_eventually (x₀ := (0 : ℝ))
    (P := fun η y => F η y.1 ≠ G η y.2) (by
      intro y hy
      exact (hF.continuousAt.ne_iff_eventually_ne hG.continuousAt).mp
        (hdis y.1 hy.1 y.2 hy.2))
  filter_upwards [hh] with η hη t ht s hs
  exact hη (t,s) ⟨ht,hs⟩

theorem exists_parameterized_segment_separation_radius
    (F G : ℝ → ℝ → PlanarPoint ℝ) (a b : ℝ)
    (hF : Continuous (fun z : ℝ × (ℝ × ℝ) => F z.1 z.2.1))
    (hG : Continuous (fun z : ℝ × (ℝ × ℝ) => G z.1 z.2.2))
    (hdis : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1, F 0 t ≠ G 0 s) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℝ, |η| < δ →
      ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1, F η t ≠ G η s := by
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp
    (eventually_parameterized_segment_separation F G a b hF hG hdis)
  refine ⟨δ,hδ,?_⟩
  intro η hη
  apply hball
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hη

/-- The head segment may translate together while either endpoint of a later
side may translate independently, covering both the W1--W2 side and fixed tails. -/
theorem exists_translated_segments_separation_radius
    (p q x y w u v : PlanarPoint ℝ) (a b : ℝ)
    (hdis : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
      affinePoint p q t ≠ affinePoint x y s) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℝ, |η| < δ →
      ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
        affinePoint (p + η • w) (q + η • w) t ≠
          affinePoint (x + η • u) (y + η • v) s := by
  apply exists_parameterized_segment_separation_radius
    (fun η t => affinePoint (p + η • w) (q + η • w) t)
    (fun η s => affinePoint (x + η • u) (y + η • v) s) a b
  · unfold affinePoint
    fun_prop
  · unfold affinePoint
    fun_prop
  · simpa only [zero_smul, add_zero] using hdis
end DirectGLSSW.CursorSegmentStability




