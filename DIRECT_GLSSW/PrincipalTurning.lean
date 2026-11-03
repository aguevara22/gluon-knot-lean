import DirectGLSSW.HOMFLY.PLDiagrams
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY.PrincipalTurning

open scoped BigOperators

/-- Actual oriented straight-arc displacement in the standard complex plane. -/
def arcVector (D : PLLinkDiagram) (e : Fin D.nArc) : ℂ :=
  ⟨(D.vertexPoint (D.arcTarget e)).1 - (D.vertexPoint (D.arcSource e)).1,
    (D.vertexPoint (D.arcTarget e)).2 - (D.vertexPoint (D.arcSource e)).2⟩

theorem arcVector_ne_zero (D : PLLinkDiagram) (e : Fin D.nArc) :
    arcVector D e ≠ 0 := by
  intro h
  have hre : (D.vertexPoint (D.arcTarget e)).1 = (D.vertexPoint (D.arcSource e)).1 := by
    have := congrArg Complex.re h
    simpa only [arcVector, Complex.zero_re] using sub_eq_zero.mp this
  have him : (D.vertexPoint (D.arcTarget e)).2 = (D.vertexPoint (D.arcSource e)).2 := by
    have := congrArg Complex.im h
    simpa only [arcVector, Complex.zero_im] using sub_eq_zero.mp this
  have hp := Prod.ext hre him
  exact D.arc_endpoints_distinct e (D.vertexPoint_injective hp).symm

/-- The signed principal tangent turn, in radians. Arc nonvanishing is proved above. -/
noncomputable def turn (D : PLLinkDiagram) (e : Fin D.nArc) : ℝ :=
  Complex.arg (arcVector D (D.continuation e) / arcVector D e)

/-- Finite sum of signed turns of every oriented component. -/
noncomputable def totalTurn (D : PLLinkDiagram) : ℝ :=
  ∑ e : Fin D.nArc, turn D e

theorem totalTurn_coe_angle_zero (D : PLLinkDiagram) :
    (totalTurn D : Real.Angle) = 0 := by
  change Real.Angle.coeHom (∑ e : Fin D.nArc, turn D e) = 0
  rw [map_sum]
  simp only [Real.Angle.coe_coeHom, turn,
    Complex.arg_div_coe_angle (arcVector_ne_zero D _) (arcVector_ne_zero D _)]
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ e : Fin D.nArc, ((arcVector D (D.continuation e)).arg : Real.Angle)) =
      ∑ e : Fin D.nArc, ((arcVector D e).arg : Real.Angle) :=
    Fintype.sum_equiv D.continuation _ _ (fun _ => rfl)
  rw [hsum, sub_self]

/-- Unique integer represented by the actual finite total tangent turn. -/
theorem existsUnique_turnInteger (D : PLLinkDiagram) :
    ∃! r : ℤ, totalTurn D = (r : ℝ) * (2 * Real.pi) := by
  obtain ⟨r, hr⟩ := Real.Angle.coe_eq_zero_iff.mp (totalTurn_coe_angle_zero D)
  refine ⟨r, ?_, ?_⟩
  · simpa only [zsmul_eq_mul] using hr.symm
  · intro s hs
    have hr' : totalTurn D = (r : ℝ) * (2 * Real.pi) := by
      simpa only [zsmul_eq_mul] using hr.symm
    have hcast : (s : ℝ) = (r : ℝ) :=
      mul_right_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
        (hs.symm.trans hr')
    exact_mod_cast hcast

/-- Choice from the proved unique integer, without a fallback value. This is a
finite principal-turn construction; source rounding identification is a separate gate. -/
noncomputable def turnInteger (D : PLLinkDiagram) : ℤ :=
  Classical.choose (existsUnique_turnInteger D)

theorem totalTurn_eq_turnInteger (D : PLLinkDiagram) :
    totalTurn D = (turnInteger D : ℝ) * (2 * Real.pi) :=
  (Classical.choose_spec (existsUnique_turnInteger D)).1

theorem turnInteger_unique (D : PLLinkDiagram) (r : ℤ)
    (hr : totalTurn D = (r : ℝ) * (2 * Real.pi)) : turnInteger D = r :=
  ((Classical.choose_spec (existsUnique_turnInteger D)).2 r hr).symm

/-- Reciprocal tangent turns cancel away from the forbidden half-turn. -/
theorem reciprocal_turns_cancel (u v : ℂ) (h : Complex.arg (v / u) ≠ Real.pi) :
    Complex.arg (v / u) + Complex.arg (u / v) = 0 := by
  have hinv : u / v = (v / u)⁻¹ := by simp [div_eq_mul_inv]
  rw [hinv, Complex.arg_inv, if_neg h]
  exact add_neg_cancel _


/-- The geometric transverse determinant rules out the half-turn branch. -/
theorem reciprocal_turns_cancel_of_det (u v : ℂ)
    (hdet : u.re * v.im - u.im * v.re ≠ 0) :
    Complex.arg (v / u) + Complex.arg (u / v) = 0 := by
  have hu : u ≠ 0 := by
    intro hz
    subst u
    simp at hdet
  have him : (v / u).im ≠ 0 := by
    rw [Complex.div_im, ← sub_div]
    apply div_ne_zero
    · simpa only [mul_comm] using hdet
    · exact mt Complex.normSq_eq_zero.mp hu
  apply reciprocal_turns_cancel
  intro hp
  exact him (Complex.arg_eq_pi_iff.mp hp).2


/-- Switching over/under data leaves every geometric tangent unchanged. -/
theorem totalTurn_switch (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    totalTurn (switchCrossing D c) = totalTurn D := rfl

theorem turnInteger_switch (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    turnInteger (switchCrossing D c) = turnInteger D := by
  apply turnInteger_unique
  rw [totalTurn_switch]
  exact totalTurn_eq_turnInteger D

/-- Actual crossing tangents have cancelling opposite oriented exchange turns. -/
theorem crossing_exchange_turns_cancel (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    let u : ℂ := ⟨(strandTangent D c 0).1, (strandTangent D c 0).2⟩
    let v : ℂ := ⟨(strandTangent D c 1).1, (strandTangent D c 1).2⟩
    Complex.arg (v / u) + Complex.arg (u / v) = 0 := by
  apply reciprocal_turns_cancel_of_det
  exact D.crossing_transverse c


/-- The actual connector construction uses the same direction u+v twice.
The four replacement bends cancel by reciprocal pairs; no wrapped addition
of principal angles is asserted. -/
theorem four_smoothing_bends_cancel (u v : ℂ)
    (hdet : u.re * v.im - u.im * v.re ≠ 0) :
    Complex.arg ((u + v) / u) + Complex.arg (v / (u + v)) +
      Complex.arg ((u + v) / v) + Complex.arg (u / (u + v)) = 0 := by
  have hu : u.re * (u + v).im - u.im * (u + v).re ≠ 0 := by
    have heq : u.re * (u + v).im - u.im * (u + v).re =
        u.re * v.im - u.im * v.re := by
      simp only [Complex.add_re, Complex.add_im]
      ring
    rw [heq]
    exact hdet
  have hv : v.re * (u + v).im - v.im * (u + v).re ≠ 0 := by
    have heq : v.re * (u + v).im - v.im * (u + v).re =
        -(u.re * v.im - u.im * v.re) := by
      simp only [Complex.add_re, Complex.add_im]
      ring
    rw [heq]
    exact neg_ne_zero.mpr hdet
  have h1 := reciprocal_turns_cancel_of_det u (u + v) hu
  have h2 := reciprocal_turns_cancel_of_det v (u + v) hv
  linarith


/-- Positive shortening/rescaling of either tangent preserves its principal turn. -/
theorem turn_positive_rescale (u v : ℂ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Complex.arg (((a : ℂ) * v) / ((b : ℂ) * u)) = Complex.arg (v / u) := by
  rw [mul_div_mul_comm, ← Complex.ofReal_div]
  exact Complex.arg_real_mul (v / u) (div_pos ha hb)

/-- The local four-bend identity at an actual crossing, with no added premise. -/
theorem crossing_four_smoothing_bends_cancel (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    let u : ℂ := ⟨(strandTangent D c 0).1, (strandTangent D c 0).2⟩
    let v : ℂ := ⟨(strandTangent D c 1).1, (strandTangent D c 1).2⟩
    Complex.arg ((u + v) / u) + Complex.arg (v / (u + v)) +
      Complex.arg ((u + v) / v) + Complex.arg (u / (u + v)) = 0 := by
  apply four_smoothing_bends_cancel
  exact D.crossing_transverse c

end DirectGLSSW.HOMFLY.PrincipalTurning
























