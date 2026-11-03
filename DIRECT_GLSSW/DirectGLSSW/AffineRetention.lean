import DirectGLSSW.AffineSegments
import Mathlib.Topology.Instances.Real.Lemmas

namespace DirectGLSSW

private theorem dist_affinePoint_left_of_nonneg
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

private theorem dist_affinePoint_right_of_nonneg
    (P A : PlanarPoint ℝ) (t : ℝ) (ht : t ≤ 1) :
    dist (affinePoint P A t) A = (1 - t) * dist P A := by
  have hrev : affinePoint P A t = affinePoint A P (1 - t) := by
    calc
      affinePoint P A t = affinePoint P A (1 - (1 - t)) := by congr 1; ring
      _ = affinePoint A P (1 - t) := affinePoint_reverse A P (1 - t)
  rw [hrev]
  exact dist_affinePoint_left_of_nonneg A P (1 - t) (sub_nonneg.mpr ht)

theorem affinePoint_outside_ball_retained_after_shortening
    (A P x : PlanarPoint ℝ) (ε t ρ : ℝ)
    (hxseg : x = affinePoint A P t)
    (hε0 : 0 < ε) (hε1 : ε < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hout : ρ ≤ dist x A)
    (hin : dist (affinePoint A P ε) A < ρ) :
    ε < t ∧ 0 < (t - ε) / (1 - ε) ∧ (t - ε) / (1 - ε) < 1 ∧
      x = affinePoint (affinePoint A P ε) P ((t - ε) / (1 - ε))
 := by
  have hmul : ε * dist P A < t * dist P A := by
    have hin' : ε * dist P A < ρ := by
      rw [dist_affinePoint_left_of_nonneg A P ε (le_of_lt hε0)] at hin
      exact hin
    have hout' : ρ ≤ t * dist P A := by
      rw [hxseg, dist_affinePoint_left_of_nonneg A P t (le_of_lt ht0)] at hout
      exact hout
    exact lt_of_lt_of_le hin' hout'
  have hd : 0 < dist P A := by
    by_cases hd : 0 < dist P A
    · exact hd
    · have heq : dist P A = 0 := le_antisymm (le_of_not_gt hd) (dist_nonneg)
      rw [heq] at hmul
      simp at hmul
  have horder : ε < t := (mul_lt_mul_right hd).mp hmul
  have hden : 0 < 1 - ε := sub_pos.mpr hε1
  have hnum : 0 < t - ε := sub_pos.mpr horder
  have hu0 : 0 < (t - ε) / (1 - ε) := div_pos hnum hden
  have hu1 : (t - ε) / (1 - ε) < 1 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  have hcompose :
      affinePoint (affinePoint A P ε) P ((t - ε) / (1 - ε)) =
        affinePoint A P t := by
    ext <;> simp only [affinePoint] <;>
      field_simp [ne_of_gt hden] <;> ring
  exact ⟨horder, hu0, hu1, hxseg.trans hcompose.symm⟩

theorem affinePoint_incoming_outside_ball_retained_after_shortening
    (P A x : PlanarPoint ℝ) (ε t ρ : ℝ)
    (hxseg : x = affinePoint P A t)
    (hε0 : 0 < ε) (hε1 : ε < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hout : ρ ≤ dist x A)
    (hin : dist (affinePoint A P ε) A < ρ) :
    t < 1 - ε ∧ 0 < t / (1 - ε) ∧ t / (1 - ε) < 1 ∧
      x = affinePoint P (affinePoint A P ε) (t / (1 - ε))
 := by
  have hmul : ε * dist P A < (1 - t) * dist P A := by
    have hin' : ε * dist P A < ρ := by
      rw [dist_affinePoint_left_of_nonneg A P ε (le_of_lt hε0)] at hin
      exact hin
    have hout' : ρ ≤ (1 - t) * dist P A := by
      rw [hxseg, dist_affinePoint_right_of_nonneg P A t (le_of_lt ht1)] at hout
      exact hout
    exact lt_of_lt_of_le hin' hout'
  have hd : 0 < dist P A := by
    by_cases hd : 0 < dist P A
    · exact hd
    · have heq : dist P A = 0 := le_antisymm (le_of_not_gt hd) (dist_nonneg)
      rw [heq] at hmul
      simp at hmul
  have horder : ε < 1 - t := (mul_lt_mul_right hd).mp hmul
  have horderOut : t < 1 - ε := by linarith
  have hden : 0 < 1 - ε := sub_pos.mpr hε1
  have hu0 : 0 < t / (1 - ε) := div_pos ht0 hden
  have hu1 : t / (1 - ε) < 1 := by
    rw [div_lt_iff₀ hden]
    linarith
  have hcompose :
      affinePoint P (affinePoint A P ε) (t / (1 - ε)) =
        affinePoint P A t := by
    ext <;> simp only [affinePoint] <;>
      field_simp [ne_of_gt hden] <;> ring
  exact ⟨horderOut, hu0, hu1, hxseg.trans hcompose.symm⟩

end DirectGLSSW
