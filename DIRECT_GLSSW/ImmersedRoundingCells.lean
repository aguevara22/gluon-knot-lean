import ImmersedBezierCorner
import ContinuousRoundedTangent
set_option autoImplicit false
open scoped Topology
namespace DirectGLSSW.ImmersedGlobalRounding
open DirectGLSSW.HOMFLY.PrincipalTurning DirectGLSSW.ImmersedPolygonRotation
noncomputable def corner (c v w : ℂ) (δ t : ℝ) : ℂ :=
  c + δ • ((-((1-t)^2)) • v + t^2 • w)
noncomputable def cornerVelocity (v w : ℂ) (δ t : ℝ) : ℂ :=
  (2*δ) • ((1-t) • v + t • w)
theorem corner_hasDerivAt (c v w : ℂ) (δ t : ℝ) :
    HasDerivAt (corner c v w δ) (cornerVelocity v w δ t) t :=
  bezier_corner_hasDerivAt c v w δ t
noncomputable def straight (c w : ℂ) (δ : RoundingFraction) (t : ℝ) : ℂ :=
  c + δ.val • w + (t-1) • ((2*δ.val) • w)
noncomputable def step (c v w : ℂ) (δ : RoundingFraction) (t : ℝ) : ℂ :=
  if t ≤ 1 then corner c v w δ.val t else straight c w δ t
noncomputable def stepVelocity (v w : ℂ) (δ : RoundingFraction) (t : ℝ) : ℂ :=
  if t ≤ 1 then cornerVelocity v w δ.val t else (2*δ.val) • w

theorem straight_hasDerivAt (c w : ℂ) (δ : RoundingFraction) (t : ℝ) :
    HasDerivAt (straight c w δ) ((2*δ.val) • w) t := by
  unfold straight
  simpa only [one_smul] using
    (((hasDerivAt_id t).sub_const 1).smul_const ((2*δ.val) • w)).const_add (c+δ.val • w)
theorem corner_straight_join (c v w : ℂ) (δ : RoundingFraction) :
    corner c v w δ.val 1 = straight c w δ 1 := by simp [corner,straight]
theorem corner_velocity_end (v w : ℂ) (δ : RoundingFraction) :
    cornerVelocity v w δ.val 1 = (2*δ.val) • w := by simp [cornerVelocity]
theorem step_hasDerivAt_join (c v w : ℂ)
    (δ : RoundingFraction) :
    HasDerivAt (step c v w δ) ((2 * δ.val) • w) 1 := by
  have hl : HasDerivWithinAt (step c v w δ)
      ((2 * δ.val) • w) (Set.Iic 1) 1 := by
    have h : HasDerivWithinAt (corner c v w δ.val)
        (cornerVelocity v w δ.val 1) (Set.Iic 1) 1 :=
      (corner_hasDerivAt c v w δ.val 1).hasDerivWithinAt
    rw [corner_velocity_end v w δ] at h
    apply h.congr
    · intro t ht
      simp only [Set.mem_Iic] at ht
      simp [step, ht]
    · simp [step]
  have hr : HasDerivWithinAt (step c v w δ)
      ((2 * δ.val) • w) (Set.Ici 1) 1 := by
    apply (straight_hasDerivAt c w δ 1).hasDerivWithinAt.congr
    · intro t ht
      simp only [Set.mem_Ici] at ht
      by_cases h : t ≤ 1
      · have heq : t = 1 := le_antisymm h ht
        subst t
        simp only [step, le_refl, if_true]
        exact corner_straight_join c v w δ
      · simp [step, h]
    · simp only [step, le_refl, if_true]
      exact corner_straight_join c v w δ
  simpa only [Set.Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr

theorem step_hasDerivAt (c v w : ℂ)
    (δ : RoundingFraction) (t : ℝ) :
    HasDerivAt (step c v w δ) (stepVelocity v w δ t) t := by
  rcases lt_trichotomy t 1 with ht | ht | ht
  · have h : HasDerivWithinAt (step c v w δ)
        (cornerVelocity v w δ.val t) (Set.Iic 1) t := by
      apply (corner_hasDerivAt c v w δ.val t).hasDerivWithinAt.congr
      · intro x hx
        have hx' : x ≤ 1 := hx
        simp [step, hx']
      · simp [step, ht.le]
    simpa [stepVelocity, ht.le] using h.hasDerivAt (Iic_mem_nhds ht)
  · subst t
    simpa [stepVelocity, corner_velocity_end] using
      step_hasDerivAt_join c v w δ
  · have h : HasDerivWithinAt (step c v w δ)
        ((2 * δ.val) • w) (Set.Ici 1) t := by
      apply (straight_hasDerivAt c w δ t).hasDerivWithinAt.congr
      · intro x hx
        by_cases hx' : x ≤ 1
        · have heq : x = 1 := le_antisymm hx' hx
          subst x
          simp only [step, le_refl, if_true]
          exact corner_straight_join c v w δ
        · simp [step, hx']
      · simp [step, not_le.mpr ht]
    simpa [stepVelocity, not_le.mpr ht] using h.hasDerivAt (Ici_mem_nhds ht)

noncomputable def cell (c v w : ℂ) (δ : RoundingFraction) (t : ℝ) : ℂ :=
  step c v w δ (t/(2*δ.val))
noncomputable def velocity (v w : ℂ) (δ : RoundingFraction) (t : ℝ) : ℂ :=
  (1/(2*δ.val)) • stepVelocity v w δ (t/(2*δ.val))
theorem cell_hasDerivAt (c v w : ℂ) (δ : RoundingFraction) (t : ℝ) :
    HasDerivAt (cell c v w δ) (velocity v w δ t) t := by
  simpa only [cell,velocity,one_div] using
    (step_hasDerivAt c v w δ (t/(2*δ.val))).scomp t
      ((hasDerivAt_id t).div_const (2*δ.val))
theorem velocity_continuous (v w : ℂ) (δ : RoundingFraction) :
    Continuous (velocity v w δ) := by
  have hs : Continuous (stepVelocity v w δ) := by
    unfold stepVelocity
    apply Continuous.if
    · intro t ht
      have heq : t = 1 := frontier_Iic_subset 1 ht
      subst t
      exact corner_velocity_end v w δ
    · unfold cornerVelocity
      fun_prop
    · exact continuous_const
  exact (hs.comp (continuous_id.div_const (2*δ.val))).const_smul (1/(2*δ.val))
theorem velocity_endpoints (v w : ℂ) (δ : RoundingFraction) :
    velocity v w δ 0 = v ∧ velocity v w δ 1 = w := by
  have hp : 2*δ.val ≠ 0 := ne_of_gt (mul_pos (by norm_num) δ.property.1)
  have hd : ¬ 1/(2*δ.val) ≤ 1 := not_le.mpr (roundingStepDuration_gt_one δ)
  have hc : (1/(2*δ.val))*(2*δ.val)=1 := by field_simp
  constructor
  · simp only [velocity,zero_div,stepVelocity,zero_le_one,if_true,cornerVelocity,
      sub_zero,one_smul,zero_smul,add_zero,smul_smul,hc,one_smul]
  · simp only [velocity,stepVelocity,hd,if_false,smul_smul,hc,one_smul]
theorem cell_endpoints (c v w : ℂ) (δ : RoundingFraction) :
    cell c v w δ 0 = c-δ.val • v ∧ cell c v w δ 1 = c+(1-δ.val) • w := by
  have hd : ¬ 1/(2*δ.val) ≤ 1 := not_le.mpr (roundingStepDuration_gt_one δ)
  constructor
  · simp [cell,step,corner,sub_eq_add_neg]
  · simp only [cell,step,hd,if_false,straight,smul_smul]
    have h : δ.val + (1/(2*δ.val)-1)*(2*δ.val) = 1-δ.val := by
      field_simp [ne_of_gt δ.property.1]
      <;> ring
    rw [add_assoc,← add_smul,h]
theorem velocity_ne_zero (v w : ℂ) (hv : v ≠ 0) (hw : w ≠ 0)
    (hshort : w/v ∈ Complex.slitPlane) (δ : RoundingFraction)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : velocity v w δ t ≠ 0 := by
  have hp : 0 < 2*δ.val := mul_pos (by norm_num) δ.property.1
  rw [velocity,Complex.real_smul]
  apply mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (one_div_pos.mpr hp)))
  unfold stepVelocity
  split_ifs with h
  · exact bezier_corner_regular v w hv hshort δ.val _ δ.property.1
      ⟨div_nonneg ht.1 hp.le,h⟩
  · rw [Complex.real_smul]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hp)) hw
end DirectGLSSW.ImmersedGlobalRounding





