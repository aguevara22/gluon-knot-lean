import SM.JointWaypointConstraints
import SM.CentralLegPolynomial
import SM.RealAffineCrossing

/-! Exact parameter-root consequences of the constructed central-leg conditions
for the actual finite named Δ/T family. Independent controls remain nonzero;
dependent roots are simple, have nonzero time derivative, and change sign. -/

namespace SM

open MvPolynomial

noncomputable section

variable {κ : Type*} {n : ℕ}

theorem central_parameterSlope_ne_zero (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (name : PolynomialControlName n) (hdep : leg.moving ∈ (namedControlPolynomial name).vars) :
    leg.parameterSlope W (namedControlPolynomial name) ≠ 0 :=
  mul_ne_zero (h.dependent_slopes name hdep) h.scalar_step

theorem central_parameterPolynomial_ne_zero
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (name : PolynomialControlName n) : leg.parameterPolynomial W (namedControlPolynomial name) ≠ 0 := by
  intro hz
  have he := leg.parameterPolynomial_eval_zero W (namedControlPolynomial name)
  rw [hz, Polynomial.eval_zero] at he
  exact h.endpoint_controls false name he.symm

theorem central_independent_control_nonzero
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (name : PolynomialControlName n) (hdep : leg.moving ∉ (namedControlPolynomial name).vars)
    (t : ℝ) : eval (leg.assignment W t) (namedControlPolynomial name) ≠ 0 := by
  rw [leg.eval_assignment_of_independent W _ (namedControlPolynomial_affine name _) hdep]
  exact h.endpoint_controls false name

theorem central_root_forces_dependency
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (name : PolynomialControlName n) (t : ℝ)
    (hr : (leg.parameterPolynomial W (namedControlPolynomial name)).IsRoot t) :
    leg.moving ∈ (namedControlPolynomial name).vars := by
  by_contra hdep
  apply central_independent_control_nonzero leg W h name hdep t
  rw [← leg.parameterPolynomial_eval W _ (namedControlPolynomial_affine name _)]
  exact hr

theorem central_parameter_root_iff_coordinate_root
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (name : PolynomialControlName n) (t : ℝ) :
    (leg.parameterPolynomial W (namedControlPolynomial name)).IsRoot t ↔
      (specializeCoordinate leg.moving (namedControlPolynomial name)
        (leg.fixedAssignment W)).IsRoot
        (leg.endpoint false W leg.moving +
          t * (leg.endpoint true W leg.moving - leg.endpoint false W leg.moving)) := by
  simp only [Polynomial.IsRoot]
  rw [leg.parameterPolynomial_eval W _ (namedControlPolynomial_affine name _),
    specializeCoordinate_eval _ _ (namedControlPolynomial_affine name _)]
  rfl

theorem central_parameter_no_common_root
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (u v : PolynomialControlName n) (hne : u ≠ v) (t : ℝ) :
    ¬ ((leg.parameterPolynomial W (namedControlPolynomial u)).IsRoot t ∧
      (leg.parameterPolynomial W (namedControlPolynomial v)).IsRoot t) := by
  rintro ⟨hu, hv⟩
  have hdu := central_root_forces_dependency leg W h u t hu
  have hdv := central_root_forces_dependency leg W h v t hv
  have hr := h.pair_resultants u v hne hdu hdv
  apply specializeCoordinate_no_common_root leg.moving _ _
    (namedControlPolynomial_affine u _) (namedControlPolynomial_affine v _)
    (leg.fixedAssignment W) hr
  exact ⟨(central_parameter_root_iff_coordinate_root leg W u t).mp hu,
    (central_parameter_root_iff_coordinate_root leg W v t).mp hv⟩

theorem central_parameter_no_zero_root
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (name : PolynomialControlName n) :
    ¬ (leg.parameterPolynomial W (namedControlPolynomial name)).IsRoot 0 := by
  change (leg.parameterPolynomial W (namedControlPolynomial name)).eval 0 ≠ 0
  rw [leg.parameterPolynomial_eval_zero]
  exact h.endpoint_controls false name

theorem central_parameter_no_one_root
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (name : PolynomialControlName n) :
    ¬ (leg.parameterPolynomial W (namedControlPolynomial name)).IsRoot 1 := by
  change (leg.parameterPolynomial W (namedControlPolynomial name)).eval 1 ≠ 0
  rw [leg.parameterPolynomial_eval_one W _ (namedControlPolynomial_affine name _)]
  exact h.endpoint_controls true name

theorem central_parameter_root_unique
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (name : PolynomialControlName n) (r s : ℝ)
    (hr : (leg.parameterPolynomial W (namedControlPolynomial name)).IsRoot r)
    (hs : (leg.parameterPolynomial W (namedControlPolynomial name)).IsRoot s) : r = s := by
  have ha := central_parameterSlope_ne_zero leg W h name
    (central_root_forces_dependency leg W h name r hr)
  exact ((realAffinePolynomial_root_iff _ _ ha r).mp hr).trans
    ((realAffinePolynomial_root_iff _ _ ha s).mp hs).symm

theorem central_parameter_root_simple
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (name : PolynomialControlName n) (r : ℝ)
    (hr : (leg.parameterPolynomial W (namedControlPolynomial name)).IsRoot r) :
    (leg.parameterPolynomial W (namedControlPolynomial name)).rootMultiplicity r = 1 := by
  have ha := central_parameterSlope_ne_zero leg W h name
    (central_root_forces_dependency leg W h name r hr)
  exact realAffinePolynomial_simple_at_root _ _ r ha hr

theorem central_control_hasDerivAt
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (name : PolynomialControlName n) (t : ℝ) :
    HasDerivAt (fun s => eval (leg.assignment W s) (namedControlPolynomial name))
      (leg.parameterSlope W (namedControlPolynomial name)) t := by
  have he : (fun s => eval (leg.assignment W s) (namedControlPolynomial name)) =
      fun s => (leg.parameterPolynomial W (namedControlPolynomial name)).eval s := by
    funext s
    exact (leg.parameterPolynomial_eval W _ (namedControlPolynomial_affine name _) s).symm
  rw [he]
  exact realAffinePolynomial_hasDerivAt _ _ t

theorem central_control_crossing_product
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (name : PolynomialControlName n) (r u v : ℝ)
    (hr : (leg.parameterPolynomial W (namedControlPolynomial name)).IsRoot r)
    (hu : u < r) (hv : r < v) :
    eval (leg.assignment W u) (namedControlPolynomial name) *
      eval (leg.assignment W v) (namedControlPolynomial name) < 0 := by
  have ha := central_parameterSlope_ne_zero leg W h name
    (central_root_forces_dependency leg W h name r hr)
  rw [← leg.parameterPolynomial_eval W _ (namedControlPolynomial_affine name _),
    ← leg.parameterPolynomial_eval W _ (namedControlPolynomial_affine name _)]
  exact realAffinePolynomial_crossing_product _ _ r u v ha hr hu hv

end

end SM
