import SegmentArgumentAdditivity
import PositionalAngleLiftUniqueness

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- A chord avoiding zero has a continuous principal argument after
normalization at its initial endpoint. -/
theorem segment_arg_ratio_continuousOn (a c : ℂ)
    (havoid : (0 : ℂ) ∉ segment ℝ a c) :
    ContinuousOn (fun z : ℂ => Complex.arg (z/a)) (segment ℝ a c) := by
  have ha : a ≠ 0 := fun h => havoid (h ▸ left_mem_segment ℝ a c)
  intro b hb
  have hsub : segment ℝ a b ⊆ segment ℝ a c :=
    (convex_segment a c).segment_subset (left_mem_segment ℝ a c) hb
  have hab : (0 : ℂ) ∉ segment ℝ a b := fun hz => havoid (hsub hz)
  have hb0 : b ≠ 0 := fun h => hab (h ▸ right_mem_segment ℝ a b)
  have hslit : b/a ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff_arg.mpr
      ⟨ne_of_lt (segment_avoids_zero_arg_lt_pi a b hab), div_ne_zero hb0 ha⟩
  have hinner : ContinuousAt (fun z : ℂ => z/a) b :=
    continuousAt_id.div_const a
  have hc : ContinuousAt (fun z : ℂ => Complex.arg (z/a)) b :=
    ContinuousAt.comp (f := fun z : ℂ => z/a) (x := b)
      (Complex.continuousAt_arg hslit) hinner
  exact hc.continuousWithinAt

/-- Every continuous real argument lift of an actual zero-free affine
chord has its principal-argument endpoint increment. -/
theorem zeroFreeChord_lift_increment (a c : ℂ)
    (havoid : (0 : ℂ) ∉ segment ℝ a c)
    (θ : C(unitInterval, ℝ))
    (hθ : ∀ t : unitInterval, (θ t : Real.Angle) =
      (( ((1-t.val : ℝ) : ℂ)*a + (t.val : ℂ)*c ).arg : Real.Angle)) :
    θ 1 - θ 0 = Complex.arg (c/a) := by
  let γ : unitInterval → ℂ :=
    fun t => ((1-t.val : ℝ) : ℂ)*a + (t.val : ℂ)*c
  have hγ : Continuous γ := by dsimp [γ]; fun_prop
  have hmem (t : unitInterval) : γ t ∈ segment ℝ a c := by
    refine ⟨1-t.val,t.val,by linarith [t.property.2],t.property.1,by ring,?_⟩
    simp only [γ,Complex.real_smul]
  have ha : a ≠ 0 := fun h => havoid (h ▸ left_mem_segment ℝ a c)
  have hγ0 (t : unitInterval) : γ t ≠ 0 := fun h => havoid (h ▸ hmem t)
  let ψ : unitInterval → ℝ := fun t => Complex.arg a + Complex.arg (γ t/a)
  have hψ : Continuous ψ := by
    apply continuous_const.add
    exact (segment_arg_ratio_continuousOn a c havoid).comp_continuous hγ hmem
  have hangle (t : unitInterval) : (θ t : Real.Angle) = (ψ t : Real.Angle) := by
    change (θ t : Real.Angle) = ((Complex.arg a + Complex.arg (γ t/a) : ℝ) : Real.Angle)
    rw [Real.Angle.coe_add,Complex.arg_div_coe_angle (hγ0 t) ha]
    have ht := hθ t
    change (θ t : Real.Angle) = (Complex.arg (γ t) : Real.Angle) at ht
    rw [ht]
    abel
  have hdiff := PositionalIndex.angle_lift_difference_constant θ ψ θ.continuous hψ
    hangle (1 : unitInterval) (0 : unitInterval)
  have hψ0 : ψ 0 = Complex.arg a := by
    simp [ψ,γ,ha]
  have hψ1 : ψ 1 = Complex.arg a + Complex.arg (c/a) := by
    simp [ψ,γ]
  rw [hψ0,hψ1] at hdiff
  linarith

end DirectGLSSW.HOMFLY.PrincipalTurning

