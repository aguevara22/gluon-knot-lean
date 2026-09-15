import SM.CentralLegFiniteRoots

open SM MvPolynomial

-- Independent definition/type/axiom review of the frozen root-control scope.
#print SM.CoordinateWaypointLeg.parameterSlope
#print SM.CoordinateWaypointLeg.parameterPolynomial
#print SM.centralControlRootSet
#print SM.labelledCentralRootSet
#check @SM.coordinateSlope_eq_zero_of_not_mem
#print axioms SM.coordinateSlope_eq_zero_of_not_mem
#check @SM.CoordinateWaypointLeg.parameterPolynomial_eval
#print axioms SM.CoordinateWaypointLeg.parameterPolynomial_eval
#check @SM.CoordinateWaypointLeg.eval_assignment_of_independent
#print axioms SM.CoordinateWaypointLeg.eval_assignment_of_independent
#check @SM.realAffinePolynomial_hasDerivAt
#print axioms SM.realAffinePolynomial_hasDerivAt
#check @SM.realAffinePolynomial_simple_at_root
#print axioms SM.realAffinePolynomial_simple_at_root
#check @SM.realAffinePolynomial_crossing_product
#print axioms SM.realAffinePolynomial_crossing_product
#check @SM.central_parameterSlope_ne_zero
#print axioms SM.central_parameterSlope_ne_zero
#check @SM.central_parameterPolynomial_ne_zero
#print axioms SM.central_parameterPolynomial_ne_zero
#check @SM.central_independent_control_nonzero
#print axioms SM.central_independent_control_nonzero
#check @SM.central_root_forces_dependency
#print axioms SM.central_root_forces_dependency
#check @SM.central_parameter_root_iff_coordinate_root
#print axioms SM.central_parameter_root_iff_coordinate_root
#check @SM.central_parameter_no_common_root
#print axioms SM.central_parameter_no_common_root
#check @SM.central_parameter_no_zero_root
#print axioms SM.central_parameter_no_zero_root
#check @SM.central_parameter_no_one_root
#print axioms SM.central_parameter_no_one_root
#check @SM.central_parameter_root_unique
#print axioms SM.central_parameter_root_unique
#check @SM.central_parameter_root_simple
#print axioms SM.central_parameter_root_simple
#check @SM.central_control_hasDerivAt
#print axioms SM.central_control_hasDerivAt
#check @SM.central_control_crossing_product
#print axioms SM.central_control_crossing_product
#check @SM.area_nonzero_of_named_controls
#print axioms SM.area_nonzero_of_named_controls
#check @SM.concurrence_nonzero_of_named_controls
#print axioms SM.concurrence_nonzero_of_named_controls
#check @SM.generic_of_named_controls_nonzero
#print axioms SM.generic_of_named_controls_nonzero
#check @SM.finite_centralControlRootSet
#print axioms SM.finite_centralControlRootSet
#check @SM.finite_labelledCentralRootSet
#print axioms SM.finite_labelledCentralRootSet
#check @SM.central_root_unique_name
#print axioms SM.central_root_unique_name
#check @SM.finite_real_set_isolated
#print axioms SM.finite_real_set_isolated
#check @SM.central_roots_isolated
#print axioms SM.central_roots_isolated
#check @SM.central_root_zero_excluded
#print axioms SM.central_root_zero_excluded
#check @SM.central_root_one_excluded
#print axioms SM.central_root_one_excluded
#check @SM.central_generic_of_not_root
#print axioms SM.central_generic_of_not_root
#check @SM.central_nongeneric_subset_roots
#print axioms SM.central_nongeneric_subset_roots
#check @SM.finite_central_nongeneric
#print axioms SM.finite_central_nongeneric

-- An actual evaluation zero yields a nonzero derivative in the actual time parameter.
example {κ : Type*} {n : ℕ} (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (name : PolynomialControlName n) (r : ℝ)
    (hr : eval (leg.assignment W r) (namedControlPolynomial name) = 0) :
    ∃ a : ℝ, a ≠ 0 ∧
      HasDerivAt (fun t => eval (leg.assignment W t) (namedControlPolynomial name)) a r := by
  have hroot : (leg.parameterPolynomial W (namedControlPolynomial name)).IsRoot r := by
    change (leg.parameterPolynomial W (namedControlPolynomial name)).eval r = 0
    rw [leg.parameterPolynomial_eval W _ (namedControlPolynomial_affine name _)]
    exact hr
  exact ⟨leg.parameterSlope W (namedControlPolynomial name),
    central_parameterSlope_ne_zero leg W h name (central_root_forces_dependency leg W h name r hroot),
    central_control_hasDerivAt leg W name r⟩
