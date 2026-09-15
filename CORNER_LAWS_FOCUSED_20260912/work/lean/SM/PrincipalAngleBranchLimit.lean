import SM.RotationContinuity
import SM.GermTurnSigns

/-! The two principal-angle limits at a nonzero antiparallel pair.
The actual determinant sign selects the branch; no angle at the centre is used. -/

namespace SM

open Filter Topology

theorem tendsto_principalAngle_at_antiparallel {ι : Type*} {l : Filter ι}
    {u v : ι → Plane} {u₀ v₀ : Plane} {s : SignType}
    (hu : Tendsto u l (𝓝 u₀)) (hv : Tendsto v l (𝓝 v₀))
    (hre : (cornerRotor u₀ v₀).re < 0) (him : (cornerRotor u₀ v₀).im = 0)
    (hs : s ≠ 0) (hsgn : ∀ a, SignType.sign (det (u a) (v a)) = s) :
    Tendsto (fun a => principalAngle (u a) (v a)) l (𝓝 ((s : ℝ) * Real.pi)) := by
  have hc : Tendsto (fun a => cornerRotor (u a) (v a)) l (𝓝 (cornerRotor u₀ v₀)) :=
    ((continuous_planeComplex.tendsto u₀).comp hu).star.mul
      ((continuous_planeComplex.tendsto v₀).comp hv)
  rcases signType_nonzero_cases hs with rfl | rfl
  · have hw : Tendsto (fun a => cornerRotor (u a) (v a)) l
        (𝓝[{z : ℂ | z.im < 0}] (cornerRotor u₀ v₀)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hc, Filter.Eventually.of_forall (fun a => ?_)⟩
      change (cornerRotor (u a) (v a)).im < 0
      rw [cornerRotor_im]
      exact sign_eq_neg_one_iff.mp (hsgn a)
    simpa only [Function.comp_def, SignType.coe_neg, SignType.coe_one, neg_one_mul, principalAngle]
      using (Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him).comp hw
  · have hw : Tendsto (fun a => cornerRotor (u a) (v a)) l
        (𝓝[{z : ℂ | 0 ≤ z.im}] (cornerRotor u₀ v₀)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hc, Filter.Eventually.of_forall (fun a => ?_)⟩
      change 0 ≤ (cornerRotor (u a) (v a)).im
      rw [cornerRotor_im]
      exact (sign_eq_one_iff.mp (hsgn a)).le
    simpa only [Function.comp_def, SignType.coe_one, one_mul, principalAngle]
      using (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hre him).comp hw

end SM
