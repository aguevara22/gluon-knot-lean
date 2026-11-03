import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.ZMultiples

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Continuous real lifts of the same angle-valued map differ by a constant.
This proves well-definedness of their period increments. -/
theorem continuous_angle_lifts_sub_constant (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (heq : ∀ x, (f x : Real.Angle) = (g x : Real.Angle)) (x y : ℝ) :
    f x - g x = f y - g y := by
  have hmaps : Set.MapsTo (fun z => f z - g z) Set.univ
      (AddSubgroup.zmultiples (2 * Real.pi) : Set ℝ) := by
    intro z _
    have hz : ((f z - g z : ℝ) : Real.Angle) = 0 := by
      rw [Real.Angle.coe_sub, heq z, sub_self]
    obtain ⟨n, hn⟩ := Real.Angle.coe_eq_zero_iff.mp hz
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, hn⟩
  letI : DiscreteTopology {x : ℝ // x ∈
      (AddSubgroup.zmultiples (2 * Real.pi) : Set ℝ)} := by
    change DiscreteTopology (AddSubgroup.zmultiples (2 * Real.pi))
    infer_instance
  exact isPreconnected_univ.constant_of_mapsTo (hf.sub hg).continuousOn hmaps
    (Set.mem_univ x) (Set.mem_univ y)

theorem continuous_angle_lifts_same_increment (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (heq : ∀ x, (f x : Real.Angle) = (g x : Real.Angle)) (x T : ℝ) :
    f (x + T) - f x = g (x + T) - g x := by
  have h := continuous_angle_lifts_sub_constant f g hf hg heq (x + T) x
  linarith

end DirectGLSSW.HOMFLY.PrincipalTurning


