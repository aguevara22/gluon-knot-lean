import SM.CoordinateWaypointLeg

/-! Actual univariate parameter polynomials on a central coordinate leg. The
parameter slope includes the real scalar step; its constant is the actual control
value at the initial hybrid. Evaluation equality requires coordinate affinity. -/

namespace SM

open MvPolynomial

noncomputable section

variable {κ σ : Type*}

theorem coordinateSlope_eq_zero_of_not_mem (z : σ) (p : MvPolynomial σ ℝ)
    (hz : z ∉ p.vars) : coordinateSlope z p = 0 := by
  have hd : p.degreeOf z = 0 := by
    simpa only [mem_vars_iff_degreeOf_ne_zero, not_not] using hz
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [isolateCoordinate_natDegree, hd]
  decide

def CoordinateWaypointLeg.parameterSlope (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) (p : MvPolynomial σ ℝ) : ℝ :=
  eval (leg.fixedAssignment W) (coordinateSlope leg.moving p) *
    (leg.endpoint true W leg.moving - leg.endpoint false W leg.moving)

def CoordinateWaypointLeg.parameterPolynomial (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) (p : MvPolynomial σ ℝ) : Polynomial ℝ :=
  realAffinePolynomial (leg.parameterSlope W p) (eval (leg.endpoint false W) p)

theorem CoordinateWaypointLeg.parameterPolynomial_eval (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) (p : MvPolynomial σ ℝ) (hp : p.degreeOf leg.moving ≤ 1) (t : ℝ) :
    (leg.parameterPolynomial W p).eval t = eval (leg.assignment W t) p := by
  have hη : (fun w : {w : σ // w ≠ leg.moving} => leg.assignment W t w) =
      leg.fixedAssignment W := by
    funext w
    exact leg.assignment_other W t w
  have he := eval_coordinate_affine leg.moving p hp (leg.assignment W t)
  rw [hη] at he
  have hm : leg.assignment W t leg.moving = leg.endpoint false W leg.moving +
      t * (leg.endpoint true W leg.moving - leg.endpoint false W leg.moving) := by
    simp only [assignment, extendCoordinateAssignment_self]
  rw [hm] at he
  have h0 := eval_coordinate_affine leg.moving p hp (leg.endpoint false W)
  change eval (leg.endpoint false W) p =
    eval (leg.fixedAssignment W) (coordinateSlope leg.moving p) *
      leg.endpoint false W leg.moving +
    eval (leg.fixedAssignment W) (coordinateIntercept leg.moving p) at h0
  rw [parameterPolynomial, realAffinePolynomial_eval, h0, he]
  unfold parameterSlope
  ring

theorem CoordinateWaypointLeg.parameterSlope_of_independent (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) (p : MvPolynomial σ ℝ) (hp : leg.moving ∉ p.vars) :
    leg.parameterSlope W p = 0 := by
  rw [parameterSlope, coordinateSlope_eq_zero_of_not_mem _ _ hp, map_zero, zero_mul]

theorem CoordinateWaypointLeg.parameterPolynomial_of_independent
    (leg : CoordinateWaypointLeg κ σ) (W : κ × σ → ℝ) (p : MvPolynomial σ ℝ)
    (hp : leg.moving ∉ p.vars) :
    leg.parameterPolynomial W p = Polynomial.C (eval (leg.endpoint false W) p) := by
  simp only [parameterPolynomial, leg.parameterSlope_of_independent W p hp,
    realAffinePolynomial, map_zero, zero_mul, zero_add]

theorem CoordinateWaypointLeg.eval_assignment_of_independent
    (leg : CoordinateWaypointLeg κ σ) (W : κ × σ → ℝ) (p : MvPolynomial σ ℝ)
    (ha : p.degreeOf leg.moving ≤ 1) (hp : leg.moving ∉ p.vars) (t : ℝ) :
    eval (leg.assignment W t) p = eval (leg.endpoint false W) p := by
  rw [← leg.parameterPolynomial_eval W p ha, leg.parameterPolynomial_of_independent W p hp]
  simp

theorem CoordinateWaypointLeg.parameterPolynomial_eval_zero
    (leg : CoordinateWaypointLeg κ σ) (W : κ × σ → ℝ) (p : MvPolynomial σ ℝ) :
    (leg.parameterPolynomial W p).eval 0 = eval (leg.endpoint false W) p := by
  simp [parameterPolynomial]

theorem CoordinateWaypointLeg.parameterPolynomial_eval_one
    (leg : CoordinateWaypointLeg κ σ) (W : κ × σ → ℝ) (p : MvPolynomial σ ℝ)
    (hp : p.degreeOf leg.moving ≤ 1) :
    (leg.parameterPolynomial W p).eval 1 = eval (leg.endpoint true W) p := by
  rw [leg.parameterPolynomial_eval W p hp, leg.assignment_one]

end

end SM
