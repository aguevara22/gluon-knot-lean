import PrincipalTurning

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Two consecutive concrete arcs cannot point in exactly opposite directions:
otherwise their open straight segments overlap. -/
theorem adjacent_not_negative_multiple (D : PLLinkDiagram) (e : Fin D.nArc)
    (k : ℝ) (hk : 0 < k) :
    arcVector D (D.continuation e) ≠ (-k : ℂ) * arcVector D e := by
  intro hv
  have hef : e ≠ D.continuation e := by
    intro heq
    have hi := D.continuation_incidence e
    rw [← heq] at hi
    exact D.arc_endpoints_distinct e hi.symm
  let t : ℝ := 1 / (2 * (k + 1))
  have hden : 0 < 2 * (k + 1) := by positivity
  have ht : 0 < t := one_div_pos.mpr hden
  have hprod : (2 * (k + 1)) * t = 1 := mul_one_div_cancel (ne_of_gt hden)
  have hkt : 0 < k * t := mul_pos hk ht
  have ht1 : t < 1 := by nlinarith
  have hs0 : 0 < 1 - k * t := by nlinarith
  have hs1 : 1 - k * t < 1 := by linarith
  have hre := congrArg Complex.re hv
  have him := congrArg Complex.im hv
  simp only [arcVector, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, zero_mul, sub_zero, add_zero] at hre him
  have hi := congrArg D.vertexPoint (D.continuation_incidence e)
  have hp : DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcTarget e)) (1 - k * t) =
      DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.continuation e)))
        (D.vertexPoint (D.arcTarget (D.continuation e))) t := by
    rw [← hi]
    apply Prod.ext
    · simp only [DirectGLSSW.affinePoint, Prod.fst]
      rw [← hi] at hre
      have ht := congrArg (fun x : ℝ => t * x) hre
      dsimp only at ht
      nlinarith only [ht]
    · simp only [DirectGLSSW.affinePoint, Prod.snd]
      rw [← hi] at him
      have ht := congrArg (fun x : ℝ => t * x) him
      dsimp only at ht
      nlinarith only [ht]
  exact D.arc_interiors_disjoint e (D.continuation e) hef (1 - k * t) t hs0 hs1 ht ht1 hp

/-- The forbidden half-turn is excluded by actual segment geometry, not a new assumption. -/
theorem turn_ne_pi (D : PLLinkDiagram) (e : Fin D.nArc) : turn D e ≠ Real.pi := by
  intro hp
  have hneg := (Complex.arg_eq_pi_iff.mp hp).1
  have him := (Complex.arg_eq_pi_iff.mp hp).2
  let q := arcVector D (D.continuation e) / arcVector D e
  have hq : q = (q.re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact him
  have heq : arcVector D (D.continuation e) = (q.re : ℂ) * arcVector D e := by
    have hdiv := (div_eq_iff (arcVector_ne_zero D e)).mp hq
    exact hdiv
  have hk : 0 < -q.re := neg_pos.mpr hneg
  exact adjacent_not_negative_multiple D e (-q.re) hk (by simpa using heq)

theorem turn_mem_open_semicircle (D : PLLinkDiagram) (e : Fin D.nArc) :
    -Real.pi < turn D e ∧ turn D e < Real.pi := by
  exact ⟨Complex.neg_pi_lt_arg _, lt_of_le_of_ne (Complex.arg_le_pi _) (turn_ne_pi D e)⟩

end DirectGLSSW.HOMFLY.PrincipalTurning



