import UnitLoopPositionalIndex

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex

/-- One downward crossing of the negative-real cut gives an actual continuous
argument with increment +2π. The cut and local germ are geometric inputs only. -/
theorem exists_single_cut_argument (f : C(I, ℂ)) (hclosed : f 1 = f 0)
    (t₀ : I) (ht₀ : 0 < t₀) (ht₁ : t₀ < 1)
    (r k ε : ℝ) (hr : 0 < r) (hk : 0 < k) (hε : 0 < ε)
    (hcut : ∀ u : I, u ≠ t₀ → f u ∈ Complex.slitPlane)
    (hgerm : ∀ u : I, |(u:ℝ)-(t₀:ℝ)| < ε →
      f u = (⟨-r,k*((t₀:ℝ)-(u:ℝ))⟩ : ℂ)) :
    (∀ u, f u ≠ 0) ∧ ∃ θ : C(I, ℝ),
      (∀ u, (θ u : Real.Angle) = ((f u).arg : Real.Angle)) ∧
      θ 1-θ 0 = 2*Real.pi := by
  have hg₀ := hgerm t₀ (by simpa using hε)
  have hnonzero (u : I) : f u ≠ 0 := by
    by_cases hu : u = t₀
    · subst u
      intro hzero
      have hre := congrArg Complex.re hzero
      rw [hg₀] at hre
      change -r = 0 at hre
      linarith
    · exact Complex.slitPlane_ne_zero (hcut u hu)
  let θ : I → ℝ := fun u => if u ≤ t₀ then (f u).arg else (f u).arg + 2*Real.pi
  have hcont : Continuous θ := by
    apply continuous_iff_continuousAt.mpr
    intro u
    rcases lt_trichotomy u t₀ with hlt | heq | hgt
    · have ha : ContinuousAt (fun v : I => (f v).arg) u :=
        ContinuousAt.comp' (f := fun v : I => f v) (g := Complex.arg) (x := u)
          (Complex.continuousAt_arg (hcut u (ne_of_lt hlt))) f.continuous.continuousAt
      apply ha.congr
      filter_upwards [Iio_mem_nhds hlt] with v hv
      change v < t₀ at hv
      simp only [θ, if_pos (le_of_lt hv)]
    · subst u
      have hre : 0 < (-f t₀).re := by
        rw [hg₀]
        simpa using hr
      have ha : ContinuousAt (fun v : I => (-f v).arg + Real.pi) t₀ :=
        (ContinuousAt.comp' (f := fun v : I => -f v) (g := Complex.arg) (x := t₀)
          (Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr (Or.inl hre)))
          f.continuous.neg.continuousAt).add_const Real.pi
      have hc : Continuous (fun v : I => |(v:ℝ)-(t₀:ℝ)|) :=
        (continuous_subtype_val.sub continuous_const).abs
      have hnear : ∀ᶠ v : I in 𝓝 t₀, |(v:ℝ)-(t₀:ℝ)| < ε :=
        (hc.tendsto t₀).eventually (Iio_mem_nhds (by simpa using hε))
      apply ha.congr
      filter_upwards [hnear] with v hv
      have hg := hgerm v hv
      by_cases hle : v ≤ t₀
      · have harg : (-f v).arg = (f v).arg - Real.pi := by
          apply Complex.arg_neg_eq_arg_sub_pi_iff.mpr
          rcases lt_or_eq_of_le hle with hvlt | hveq
          · left
            rw [hg]
            change 0 < k*((t₀:ℝ)-(v:ℝ))
            exact mul_pos hk (sub_pos.mpr hvlt)
          · right
            subst v
            rw [hg₀]
            constructor
            · simp
            · change -r < 0
              linarith
        dsimp only [θ]
        rw [if_pos hle]
        linarith
      · have him : (f v).im < 0 := by
          rw [hg]
          change k*((t₀:ℝ)-(v:ℝ)) < 0
          exact mul_neg_of_pos_of_neg hk (sub_neg.mpr (lt_of_not_ge hle))
        have harg := Complex.arg_neg_eq_arg_add_pi_of_im_neg him
        dsimp only [θ]
        rw [if_neg hle]
        linarith
    · have ha : ContinuousAt (fun v : I => (f v).arg + 2*Real.pi) u :=
        (ContinuousAt.comp' (f := fun v : I => f v) (g := Complex.arg) (x := u)
          (Complex.continuousAt_arg (hcut u (ne_of_gt hgt))) f.continuous.continuousAt).add_const _
      apply ha.congr
      filter_upwards [Ioi_mem_nhds hgt] with v hv
      change t₀ < v at hv
      simp only [θ, if_neg (not_le.mpr hv)]
  refine ⟨hnonzero,⟨θ,hcont⟩,?_,?_⟩
  · intro u
    change ((if u ≤ t₀ then (f u).arg else (f u).arg + 2*Real.pi : ℝ) : Real.Angle) = _
    split_ifs
    · rfl
    · rw [Real.Angle.coe_add,Real.Angle.coe_two_pi,add_zero]
  · change (if (1:I) ≤ t₀ then (f 1).arg else (f 1).arg + 2*Real.pi) -
      (if (0:I) ≤ t₀ then (f 0).arg else (f 0).arg + 2*Real.pi) = _
    rw [if_neg (not_le.mpr ht₁),if_pos (le_of_lt ht₀),hclosed]
    ring

/-- Index +1 is derived from the explicit argument lift; avoidance is produced. -/
theorem unitPositionalIndex_one_of_single_cut (f : C(I, ℂ)) (hclosed : f 1 = f 0)
    (t₀ : I) (ht₀ : 0 < t₀) (ht₁ : t₀ < 1)
    (r k ε : ℝ) (hr : 0 < r) (hk : 0 < k) (hε : 0 < ε)
    (hcut : ∀ u : I, u ≠ t₀ → f u ∈ Complex.slitPlane)
    (hgerm : ∀ u : I, |(u:ℝ)-(t₀:ℝ)| < ε →
      f u = (⟨-r,k*((t₀:ℝ)-(u:ℝ))⟩ : ℂ)) :
    ∃ havoid : ∀ u, f u ≠ 0, unitPositionalIndex f hclosed 0 havoid = 1 := by
  obtain ⟨havoid,θ,hθ,hinc⟩ :=
    exists_single_cut_argument f hclosed t₀ ht₀ ht₁ r k ε hr hk hε hcut hgerm
  refine ⟨havoid,?_⟩
  have hi := unitPositionalIndex_any_lift f hclosed 0 havoid θ
    (fun u => by simpa only [sub_zero] using hθ u)
  rw [hinc] at hi
  have hc : (unitPositionalIndex f hclosed 0 havoid : ℝ) = 1 :=
    mul_right_cancel₀ (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero)
      (by simpa only [one_mul] using hi.symm)
  exact_mod_cast hc

end DirectGLSSW.HOMFLY.PositionalIndex


