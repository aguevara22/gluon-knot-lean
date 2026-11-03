import DirectGLSSW.CapCriticalEventGeometry
import DirectGLSSW.AffineSegments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW.ActualEventGeometry

open DirectGLSSW
open DirectGLSSW.CapCriticalEventGeometry
open DirectGLSSW.CapCrossingEvent
open DirectGLSSW.EndpointEventGeometry

/-- A negative affine ray parameter makes the origin point an actual member
of the open segment, with parameter `-τ/(1-τ)`. -/
theorem open_segment_of_negative_ray_parameter
    (a p b : PlanarPoint ℝ) (τ : ℝ)
    (hτ : τ < 0)
    (hrel : a = p + τ • (b - p)) :
    OnOpenSegment a b p := by
  let s := -τ / (1 - τ)
  have hden : 0 < 1 - τ := by linarith
  have hspos : 0 < s := by
    dsimp [s]
    exact div_pos (by linarith) hden
  have hslt : s < 1 := by
    dsimp [s]
    rw [div_lt_one hden]
    linarith
  have hax : a.1 = p.1 + τ * (b.1 - p.1) := by
    simpa [smul_eq_mul] using congrArg Prod.fst hrel
  have hay : a.2 = p.2 + τ * (b.2 - p.2) := by
    simpa [smul_eq_mul] using congrArg Prod.snd hrel
  refine ⟨s, hspos, hslt, ?_⟩
  apply Prod.ext
  · change p.1 = a.1 + s * (b.1 - a.1)
    dsimp [s]
    field_simp [ne_of_gt hden]
    nlinarith [hax]
  · change p.2 = a.2 + s * (b.2 - a.2)
    dsimp [s]
    field_simp [ne_of_gt hden]
    nlinarith [hay]

/-- A horizontal-line point on the carrier of `a,b` gives the source ray
relation, with the coefficient determined by the endpoint heights. -/
private theorem ray_relation_of_horizontal_collinearity
    (a p b : PlanarPoint ℝ) (τ : ℝ)
    (hp : p.2 = 0) (hb : b.2 ≠ 0)
    (hcol : planarDet (a - p) (b - p) = 0)
    (ha : a.2 = τ * b.2) :
    a = p + τ • (b - p) := by
  have hdetx : (a.1 - p.1) * b.2 - a.2 * (b.1 - p.1) = 0 := by
    simpa [planarDet, hp] using hcol
  apply Prod.ext
  · change a.1 = p.1 + τ * (b.1 - p.1)
    have hτ : τ = a.2 / b.2 := by
      field_simp [hb]
      rw [ha]
    rw [hτ]
    field_simp [hb]
    nlinarith [hdetx]
  · change a.2 = p.2 + τ * (b.2 - p.2)
    rw [hp, sub_zero]
    rw [ha]
    field_simp [hb]

private theorem critical_root_event_hdet_zero
    (q : ℕ → PlanarPoint ℝ) (k : ℕ)
    (hk : 0 < k)
    (hden : planarDet (q k - q (k+1)) (1, 0) ≠ 0) :
    polygonHDet (horizontalMove q (criticalRoot q (k,k+1))) 0 k (k+1) = 0 := by
  change polygonHDet (moveEndpoint q (1,0) (criticalRoot q (k,k+1)))
      0 k (k+1) = 0
  rw [moveEndpoint_farDet q (1, 0) hk (by omega : k < k+1)
    (criticalRoot q (k,k+1))]
  dsimp [criticalRoot]
  field_simp [hden]

/-- The selected adjacent critical event is an actual open-segment crossing
exactly in the negative endpoint-height-ratio case. -/
theorem criticalRoot_event_onOpenSegment_iff_negative_height_ratio
    (q : ℕ → PlanarPoint ℝ) (k : ℕ)
    (hk : 0 < k)
    (hzero : (q 0).2 = 0)
    (_hAk : (q k).2 ≠ 0)
    (hBk : (q (k+1)).2 ≠ 0) :
    OnOpenSegment (q k) (q (k+1))
      (horizontalMove q (criticalRoot q (k,k+1)) 0) ↔
        (q k).2 / (q (k+1)).2 < 0 := by
  let a := q k
  let b := q (k+1)
  let p := horizontalMove q (criticalRoot q (k,k+1)) 0
  constructor
  · intro hsegment
    obtain ⟨s, hs0, hs1, hpoint⟩ := hsegment
    have hpzero : p.2 = 0 := by
      simp [p, horizontalMove, moveEndpoint, hzero]
    have hbalance : (1-s) * a.2 + s * b.2 = 0 := by
      have hy := congrArg Prod.snd hpoint
      simp [affinePoint, hpzero] at hy
      nlinarith [hy]
    rcases lt_trichotomy b.2 0 with hbneg | hbzero | hbpos
    · have hapos : 0 < a.2 := by
        by_contra h
        have ha_nonpos : a.2 ≤ 0 := le_of_not_gt h
        have hleft : (1-s) * a.2 ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) ha_nonpos
        have hright : s * b.2 < 0 := mul_neg_of_pos_of_neg hs0 hbneg
        linarith
      exact div_neg_iff.mpr (Or.inl ⟨hapos, hbneg⟩)
    · exact (hBk hbzero).elim
    · have haneg : a.2 < 0 := by
        by_contra h
        have ha_nonneg : 0 ≤ a.2 := le_of_not_gt h
        have hleft : 0 ≤ (1-s) * a.2 :=
          mul_nonneg (by linarith) ha_nonneg
        have hright : 0 < s * b.2 := mul_pos hs0 hbpos
        linarith
      exact div_neg_iff.mpr (Or.inr ⟨haneg, hbpos⟩)
  · intro hτ
    have hsign := div_neg_iff.mp hτ
    have hne : a.2 ≠ b.2 := by
      intro heq
      rcases hsign with ⟨hapos, hbneg⟩ | ⟨haneg, hbpos⟩ <;> linarith
    have hden : planarDet (a - b) (1, 0) ≠ 0 := by
      have hformula : planarDet (a - b) (1, 0) = b.2 - a.2 := by
        simp [planarDet]
      rw [hformula]
      exact sub_ne_zero.mpr (Ne.symm hne)
    have hevent := critical_root_event_hdet_zero q k hk hden
    have hqk : horizontalMove q (criticalRoot q (k,k+1)) k = a := by
      change (if k = 0 then q 0 + criticalRoot q (k,k+1) • (1,0) else q k) = q k
      rw [if_neg (ne_of_gt hk)]
    have hqknext : horizontalMove q (criticalRoot q (k,k+1)) (k+1) = b := by
      change (if k+1 = 0 then q 0 + criticalRoot q (k,k+1) • (1,0) else q (k+1)) = q (k+1)
      rw [if_neg (by omega : k+1 ≠ 0)]
    have hdet : planarDet (a - b) (p - b) = 0 := by
      simpa [polygonHDet, p, hqk, hqknext] using hevent
    have hcol : planarDet (a - p) (b - p) = 0 := by
      have hid : planarDet (a - p) (b - p) =
          -planarDet (a - b) (p - b) := by
        simp [planarDet]
        ring
      rw [hid, hdet]
      simp
    have hpzero : p.2 = 0 := by simp [p, horizontalMove, moveEndpoint, hzero]
    have haheight : a.2 = (a.2 / b.2) * b.2 := by
      field_simp [hBk]
    have hrel := ray_relation_of_horizontal_collinearity
      a p b (a.2 / b.2) hpzero hBk hcol haheight
    exact open_segment_of_negative_ray_parameter a p b (a.2 / b.2) hτ hrel






end DirectGLSSW.ActualEventGeometry
