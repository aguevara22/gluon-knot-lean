import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.ImmersedPolygonRotation

/-- The convex segment from one to a slit-plane ratio stays in the slit plane.
This includes positive real ratios, hence permits zero turns. -/
theorem relative_tangent_mem_slitPlane (z : ℂ) (hz : z ∈ Complex.slitPlane)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ((1-t:ℝ):ℂ)+(t:ℂ)*z ∈ Complex.slitPlane := by
  by_cases ht0 : t = 0
  · subst t
    simp only [sub_zero,Complex.ofReal_one,Complex.ofReal_zero,zero_mul,add_zero]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    rw [Complex.mem_slitPlane_iff] at hz ⊢
    rcases hz with hz | hz
    · left
      simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero]
      nlinarith [ht.2]
    · right
      simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,add_zero,zero_add]
      exact mul_ne_zero ht0 hz

theorem bezier_corner_hasDerivAt (c v w : ℂ) (δ t : ℝ) :
    HasDerivAt (fun x : ℝ => c + δ • ((-((1-x)^2)) • v + x^2 • w))
      ((2*δ) • ((1-t) • v + t • w)) t := by
  have h1 : HasDerivAt (fun x : ℝ => -((1-x)^2)) (2*(1-t)) t := by
    simpa using (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow 2).neg
  have h2 : HasDerivAt (fun x : ℝ => x^2) (2*t) t := by
    simpa using (hasDerivAt_id t).pow 2
  have h := (((h1.smul_const v).add (h2.smul_const w)).const_smul δ).const_add c
  convert h using 1
  simp only [smul_add,smul_smul]
  congr 1 <;> congr 1 <;> ring

theorem bezier_tangent_factor (v w : ℂ) (hv : v ≠ 0) (t : ℝ) :
    (1-t) • v + t • w = v * (((1-t:ℝ):ℂ)+(t:ℂ)*(w/v)) := by
  rw [Complex.real_smul,Complex.real_smul]
  field_simp
  <;> ring

/-- Nonzero derivative of the literal quadratic rounding under only the local
short-turn condition, with no remote-incidence hypotheses. -/
theorem bezier_corner_regular (v w : ℂ) (hv : v ≠ 0)
    (hshort : w/v ∈ Complex.slitPlane) (δ t : ℝ) (hδ : 0 < δ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (2*δ) • ((1-t) • v + t • w) ≠ 0 := by
  rw [Complex.real_smul,bezier_tangent_factor v w hv]
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (mul_pos (by norm_num) hδ)))
    (mul_ne_zero hv (Complex.slitPlane_ne_zero (relative_tangent_mem_slitPlane _ hshort t ht)))

/-- A continuous real lift of the actual Bezier derivative angle. Its endpoint
increment is precisely the principal turn, strictly between -pi and pi. -/
theorem exists_bezier_tangent_lift (v w : ℂ) (hv : v ≠ 0)
    (hshort : w/v ∈ Complex.slitPlane) (δ : ℝ) (hδ : 0 < δ) :
    ∃ θ : C(I,ℝ),
      (∀ t : I, (θ t : Real.Angle) =
        (Complex.arg ((2*δ) • ((1-t.val) • v + t.val • w)) : Real.Angle)) ∧
      θ 0 = v.arg ∧ θ 1 - θ 0 = (w/v).arg ∧
      -Real.pi < θ 1 - θ 0 ∧ θ 1 - θ 0 < Real.pi := by
  let z : I → ℂ := fun t => ((1-t.val:ℝ):ℂ)+(t.val:ℂ)*(w/v)
  have hz : ∀ t : I, z t ∈ Complex.slitPlane := fun t =>
    relative_tangent_mem_slitPlane _ hshort t.val t.property
  have hzc : Continuous z := by dsimp [z]; fun_prop
  have hc : Continuous (fun t : I => v.arg+(z t).arg) := by
    apply continuous_const.add
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp' (f := z) (g := Complex.arg) (x := t)
      (Complex.continuousAt_arg (hz t)) hzc.continuousAt
  let θ : C(I,ℝ) := ⟨fun t => v.arg+(z t).arg,hc⟩
  have hθ0 : θ 0 = v.arg := by simp [θ,z]
  have hθinc : θ 1 - θ 0 = (w/v).arg := by simp [θ,z]
  refine ⟨θ,?_,hθ0,hθinc,?_,?_⟩
  · intro t
    rw [Complex.real_smul,bezier_tangent_factor v w hv]
    rw [Complex.arg_real_mul _ (mul_pos (by norm_num) hδ)]
    rw [Complex.arg_mul_coe_angle hv (Complex.slitPlane_ne_zero (hz t))]
    rfl
  · rw [hθinc]
    exact Complex.neg_pi_lt_arg _
  · rw [hθinc]
    exact lt_of_le_of_ne (Complex.arg_le_pi _) (Complex.slitPlane_arg_ne_pi hshort)

end DirectGLSSW.ImmersedPolygonRotation





