import DirectGLSSW.AffineSegments
import Mathlib.Topology.Instances.Real.Lemmas
import DirectGLSSW.NonincidentEdgeClearance
import DirectGLSSW.CrossingFreeVertexBall

namespace DirectGLSSW

open DirectGLSSW.ShortEdgeGenericity

private theorem dist_affine_point_left_nonneg
    (A P : PlanarPoint ℝ) (c : ℝ) (hc : 0 ≤ c) :
    dist (affinePoint A P c) A = c * dist P A := by
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [affinePoint]
  have hfst : A.1 + c * (P.1 - A.1) - A.1 = c * (P.1 - A.1) := by ring
  have hsnd : A.2 + c * (P.2 - A.2) - A.2 = c * (P.2 - A.2) := by ring
  rw [hfst, hsnd, abs_mul, abs_of_nonneg hc, abs_mul, abs_of_nonneg hc]
  let u := |P.1 - A.1|
  let v := |P.2 - A.2|
  have hu : 0 ≤ u := abs_nonneg _
  have hv : 0 ≤ v := abs_nonneg _
  simp only [Real.dist_eq]
  change max (c * u) (c * v) = c * max u v
  rcases le_total u v with huv | hvu
  · have hcuv : c * u ≤ c * v := mul_le_mul_of_nonneg_left huv hc
    rw [max_eq_right huv, max_eq_right hcuv]
  · have hcvu : c * v ≤ c * u := mul_le_mul_of_nonneg_left hvu hc
    rw [max_eq_left hvu, max_eq_left hcvu]

theorem exists_shortening_points_small_radius
    (A P C : PlanarPoint ℝ) (scale ρ : ℝ)
    (hscale : 0 < scale) (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ε < 1 ∧ ε * scale < 1 ∧
      dist (A + ε • (P - A)) A < ρ ∧
      dist (A + (ε * scale) • (C - A)) A < ρ := by
  let dP := dist P A
  let dC := dist C A
  let δ : ℝ := min 1 (min (1 / scale)
    (min (ρ / (dP + 1)) (ρ / (scale * (dC + 1)))))
  have hdP : 0 ≤ dP := dist_nonneg
  have hdC : 0 ≤ dC := dist_nonneg
  have hscaleInv : 0 < 1 / scale := div_pos one_pos hscale
  have hPden : 0 < dP + 1 := by positivity
  have hCden : 0 < scale * (dC + 1) := by positivity
  have hPbound : 0 < ρ / (dP + 1) := div_pos hρ hPden
  have hCbound : 0 < ρ / (scale * (dC + 1)) := div_pos hρ hCden
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min zero_lt_one (lt_min hscaleInv (lt_min hPbound hCbound))
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  rcases lt_min_iff.mp hεδ with ⟨hεone, hrest⟩
  rcases lt_min_iff.mp hrest with ⟨hεscale, hrest⟩
  rcases lt_min_iff.mp hrest with ⟨hεP, hεC⟩
  have hεscale' : ε * scale < 1 := by
    rwa [lt_div_iff₀ hscale] at hεscale
  have hεP' : ε * (dP + 1) < ρ := by
    rwa [lt_div_iff₀ hPden] at hεP
  have hεC' : ε * (scale * (dC + 1)) < ρ := by
    rwa [lt_div_iff₀ hCden] at hεC
  have hboundP : ε * dP < ρ := by nlinarith
  have hboundC : (ε * scale) * dC < ρ := by nlinarith
  have hpointP : A + ε • (P - A) = affinePoint A P ε := by
    ext <;> simp [affinePoint]
  have hpointC : A + (ε * scale) • (C - A) = affinePoint A C (ε * scale) := by
    ext <;> simp [affinePoint]
  have hdistP : dist (A + ε • (P - A)) A = ε * dP := by
    rw [hpointP, dist_affine_point_left_nonneg A P ε (le_of_lt hε)]
  have hdistC : dist (A + (ε * scale) • (C - A)) A =
      (ε * scale) * dC := by
    rw [hpointC, dist_affine_point_left_nonneg A C (ε * scale)
      (mul_nonneg (le_of_lt hε) (le_of_lt hscale))]
  rw [hdistP, hdistC]
  exact ⟨hεone, hεscale', hboundP, hboundC⟩

theorem exists_combined_vertex_clearance_radius
    {n : ℕ} (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ)
    (hq : cyclicNoncollinear q) (a : Fin n) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ e : Fin n, e ≠ a → cyclicSuccessor e ≠ a →
        ∀ x : PlanarPoint ℝ, dist x (q a) < ρ → ¬ edgeClosed q e x) ∧
      (∀ x : PlanarPoint ℝ, dist x (q a) < ρ → ¬ IsCrossingPoint q x) := by
  obtain ⟨δ₁, hδ₁, hnonincident⟩ :=
    ShortEdgeGenericity.exists_nonincident_edge_clearance hn q hq a
  obtain ⟨δ₂, hδ₂, hcrossing⟩ :=
    ShortEdgeGenericity.exists_crossing_free_vertex_ball hn q hq a
  let ρ := min δ₁ δ₂
  have hρ : 0 < ρ := lt_min hδ₁ hδ₂
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro e hea hsea x hx
    exact hnonincident e hea hsea x
      (lt_of_lt_of_le hx (min_le_left δ₁ δ₂))
  · intro x hx
    exact hcrossing x (lt_of_lt_of_le hx (min_le_right δ₁ δ₂))

end DirectGLSSW
