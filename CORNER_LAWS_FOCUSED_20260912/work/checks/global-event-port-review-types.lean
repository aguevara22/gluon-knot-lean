import SM.GlobalEventCertificate

set_option pp.fullNames true
set_option pp.universes false

#check SM.exists_timedCoordinatePolyline
#print axioms SM.exists_timedCoordinatePolyline

#check SM.quotient_remainder_successor
#print axioms SM.quotient_remainder_successor

#check SM.exists_multiCellCoordinatePolyline
#print axioms SM.exists_multiCellCoordinatePolyline

#check SM.multiScalarBranch_affine
#print axioms SM.multiScalarBranch_affine

#check SM.fine_uniformMeshCell_subset_coarse
#print axioms SM.fine_uniformMeshCell_subset_coarse

#check SM.CurveCubeSubdivision.nonempty_cubeCoordinateApproximation
#print axioms SM.CurveCubeSubdivision.nonempty_cubeCoordinateApproximation

#check SM.CurveCubeSubdivision.CubeCoordinateApproximation.central_branch
#print axioms SM.CurveCubeSubdivision.CubeCoordinateApproximation.central_branch

#check SM.CurveCubeSubdivision.CubeCoordinateApproximation.collision_free
#print axioms SM.CurveCubeSubdivision.CubeCoordinateApproximation.collision_free

#check SM.CurveCubeSubdivision.CubeCoordinateApproximation.finite_nongeneric
#print axioms SM.CurveCubeSubdivision.CubeCoordinateApproximation.finite_nongeneric

#check SM.CurveCubeSubdivision.exists_joint_cubeCoordinateApproximation
#print axioms SM.CurveCubeSubdivision.exists_joint_cubeCoordinateApproximation

#check SM.CurveCubeSubdivision.CubeCoordinateApproximation.generic_endpoint_collar
#print axioms SM.CurveCubeSubdivision.CubeCoordinateApproximation.generic_endpoint_collar

#check SM.CurveCubeSubdivision.CubeCoordinateApproximation.nongeneric_central_time
#print axioms SM.CurveCubeSubdivision.CubeCoordinateApproximation.nongeneric_central_time

#check SM.CurveCubeSubdivision.CubeCoordinateApproximation.nongeneric_has_timed_wallGerm
#print axioms SM.CurveCubeSubdivision.CubeCoordinateApproximation.nongeneric_has_timed_wallGerm

#check SM.CentralRootPatch.scaledToWallGerm
#print axioms SM.CentralRootPatch.scaledToWallGerm

#check SM.CentralRootPatch.scaled_control_hasDerivAt
#print axioms SM.CentralRootPatch.scaled_control_hasDerivAt

#check SM.contDiffOn_coordinateRootFunction
#print axioms SM.contDiffOn_coordinateRootFunction

#check SM.coordinate_graph_actual_assignment
#print axioms SM.coordinate_graph_actual_assignment

#check SM.coordinate_graph_injective
#print axioms SM.coordinate_graph_injective

#check SM.contDiffOn_coordinate_graph
#print axioms SM.contDiffOn_coordinate_graph

#check SM.coordinate_graph_projection
#print axioms SM.coordinate_graph_projection

#check SM.contDiff_remaining_projection
#print axioms SM.contDiff_remaining_projection

#check SM.coordinate_zero_set_eq_graph
#print axioms SM.coordinate_zero_set_eq_graph

#check SM.central_root_smooth_graph
#print axioms SM.central_root_smooth_graph

#check SM.CurveCubeSubdivision.indexedCentralLeg
#print axioms SM.CurveCubeSubdivision.indexedCentralLeg

#check SM.CurveCubeSubdivision.TimedEventCertificate
#print axioms SM.CurveCubeSubdivision.TimedEventCertificate

#check SM.CurveCubeSubdivision.CubeCoordinateApproximation.nonempty_timedEventCertificate
#print axioms SM.CurveCubeSubdivision.CubeCoordinateApproximation.nonempty_timedEventCertificate

#print SM.CurveCubeSubdivision.CubeCoordinateApproximation
#print SM.CurveCubeSubdivision.TimedEventCertificate

open Set MvPolynomial
open scoped ContDiff

-- Raw source hypotheses construct ONE actual approximation, and EVERY
-- actual nongeneric time has the full stronger event certificate.
example {n : ℕ} (hn : 3 ≤ n)
    (gamma : unitInterval → SM.LabelledTuple n) (hgamma : Continuous gamma)
    (hregular : ∀ t, SM.Regular (gamma t))
    (hfirst : SM.Generic (gamma 0)) (hlast : SM.Generic (gamma 1))
    (delta : ℝ) (hdelta : 0 < delta) :
    letI : NeZero n := ⟨by omega⟩
    ∃ d : SM.CurveCubeSubdivision gamma delta,
      ∃ W : d.InternalWaypoint × SM.ScalarCoordinate n → ℝ,
      ∃ A : d.CubeCoordinateApproximation W,
        Continuous A.path ∧ A.path 0 = gamma 0 ∧ A.path 1 = gamma 1 ∧
        (∀ t, SM.Regular (A.path t)) ∧
        (∀ t, dist (SM.tupleCoordinates (A.path t)) (SM.tupleCoordinates (gamma t)) < delta) ∧
        (∀ t, Function.Injective (A.path t)) ∧
        {t : unitInterval | ¬ SM.Generic (A.path t)}.Finite ∧
        (∀ t, ¬ SM.Generic (A.path t) → Nonempty (SM.CurveCubeSubdivision.TimedEventCertificate A hn t)) := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨d⟩ := SM.nonempty_curveCubeSubdivision hn gamma hgamma hregular hfirst hlast delta hdelta
  obtain ⟨W, A, hJ, hinj, hfinite⟩ := d.exists_joint_cubeCoordinateApproximation hn
  exact ⟨d, W, A, A.continuous, A.first, A.last, A.regular, A.close, hinj, hfinite,
    fun t hng => A.nonempty_timedEventCertificate hn hJ t hng⟩

-- The certificate TYPE itself attaches the returned germ center to the
-- graph of its own returned control and coordinate; no constructor unfolding.
example {n : ℕ} [NeZero n] {gamma : unitInterval → SM.LabelledTuple n} {delta : ℝ}
    {d : SM.CurveCubeSubdivision gamma delta}
    {W : d.InternalWaypoint × SM.ScalarCoordinate n → ℝ}
    (A : d.CubeCoordinateApproximation W) (hn : 3 ≤ n) (t : unitInterval)
    (c : SM.CurveCubeSubdivision.TimedEventCertificate A hn t) :
    let leg := SM.CurveCubeSubdivision.indexedCentralLeg hn c.index c.central
    SM.scalarCoordinates c.germ.center ∈
      (fun eta : {j : SM.ScalarCoordinate n // j ≠ leg.moving} → ℝ =>
        SM.extendCoordinateAssignment leg.moving eta
          (SM.coordinateRootFunction leg.moving (SM.namedControlPolynomial c.control) eta)) ''
        SM.coordinateSlopeDomain leg.moving (SM.namedControlPolynomial c.control) := by
  dsimp only
  rw [← SM.coordinate_zero_set_eq_graph _ _ (SM.namedControlPolynomial_affine c.control _)]
  refine ⟨c.point_graph_domain, ?_⟩
  rw [c.germ_center]
  exact c.root

-- Both retained curve identities attach the actual shifted path to the
-- same explicit affine expression used in the certificate derivative.
example {n : ℕ} [NeZero n] {gamma : unitInterval → SM.LabelledTuple n} {delta : ℝ}
    {d : SM.CurveCubeSubdivision gamma delta}
    {W : d.InternalWaypoint × SM.ScalarCoordinate n → ℝ}
    (A : d.CubeCoordinateApproximation W) (hn : 3 ≤ n) (t : unitInterval)
    (c : SM.CurveCubeSubdivision.TimedEventCertificate A hn t) (s : c.germ.Parameter) :
    ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
      SM.scalarCoordinates (A.path ⟨(t : ℝ) + s.val, hs⟩) =
        (SM.CurveCubeSubdivision.indexedCentralLeg hn c.index c.central).assignment W
          (SM.uniformMeshLocalTime _ c.index t + (d.count * (2*n) : ℕ) * s.val) := by
  obtain ⟨hs, he⟩ := c.curve_on_path s
  refine ⟨hs, ?_⟩
  rw [← he, c.curve_on_leg s, SM.scalarCoordinates_tupleOf]

-- A genuine control root with the actual joint conditions gives the full
-- concrete graph geometry at its actual scalar assignment. No slope or
-- smoothness premise is supplied, and n>=3 discharges NeZero locally.
example {kappa : Type*} {n : ℕ} (hn : 3 ≤ n)
    (leg : SM.CoordinateWaypointLeg kappa (SM.ScalarCoordinate n))
    (W : kappa × SM.ScalarCoordinate n → ℝ) (h : SM.JointLegConditions leg W)
    (name : SM.PolynomialControlName n) (r : ℝ)
    (hr : eval (leg.assignment W r) (SM.namedControlPolynomial name) = 0) :
    letI : NeZero n := ⟨by omega⟩
    let U := SM.coordinateSlopeDomain leg.moving (SM.namedControlPolynomial name)
    let G := fun eta : {j : SM.ScalarCoordinate n // j ≠ leg.moving} → ℝ =>
      SM.extendCoordinateAssignment leg.moving eta
        (SM.coordinateRootFunction leg.moving (SM.namedControlPolynomial name) eta)
    let R := fun rho : SM.ScalarCoordinate n → ℝ =>
      fun j : {j : SM.ScalarCoordinate n // j ≠ leg.moving} => rho j
    IsOpen U ∧ leg.fixedAssignment W ∈ U ∧ ContDiffOn ℝ ∞ G U ∧
      Function.Injective G ∧ ContDiff ℝ ∞ R ∧ (∀ eta, R (G eta) = eta) ∧
      IsOpen (R ⁻¹' U) ∧ leg.assignment W r ∈ R ⁻¹' U ∧
      {rho : SM.ScalarCoordinate n → ℝ | R rho ∈ U ∧
        eval rho (SM.namedControlPolynomial name) = 0} = G '' U ∧
      leg.assignment W r ∈ G '' U := by
  letI : NeZero n := ⟨by omega⟩
  dsimp only
  have hroot : (leg.parameterPolynomial W (SM.namedControlPolynomial name)).IsRoot r := by
    change (leg.parameterPolynomial W (SM.namedControlPolynomial name)).eval r = 0
    rw [leg.parameterPolynomial_eval W _ (SM.namedControlPolynomial_affine name _)]
    exact hr
  have hs := h.dependent_slopes name (SM.central_root_forces_dependency leg W h name r hroot)
  have hfixed : (fun j : {j : SM.ScalarCoordinate n // j ≠ leg.moving} =>
      leg.assignment W r j) = leg.fixedAssignment W := by
    funext j
    exact leg.assignment_other W r j
  have heta : (fun j : {j : SM.ScalarCoordinate n // j ≠ leg.moving} => leg.assignment W r j) ∈
      SM.coordinateSlopeDomain leg.moving (SM.namedControlPolynomial name) := by
    simpa only [hfixed, SM.coordinateSlopeDomain, Set.mem_setOf_eq] using hs
  have hz := SM.coordinate_zero_set_eq_graph leg.moving (SM.namedControlPolynomial name)
    (SM.namedControlPolynomial_affine name _)
  refine ⟨SM.isOpen_coordinateSlopeDomain _ _, hs,
    SM.contDiffOn_coordinate_graph _ _, SM.coordinate_graph_injective _ _,
    SM.contDiff_remaining_projection _, SM.coordinate_graph_projection _ _,
    SM.isOpen_coordinate_graph_ambient_domain _ _, heta, hz, ?_⟩
  rw [← hz]
  exact ⟨heta, hr⟩

-- The remaining-coordinate projection is also a right inverse on every
-- actual ambient zero in the slope neighborhood, not merely a left inverse.
example {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (i : sigma) (p : MvPolynomial sigma ℝ) (hp : p.degreeOf i ≤ 1)
    (rho : sigma → ℝ)
    (hdom : (fun j : {j : sigma // j ≠ i} => rho j) ∈ SM.coordinateSlopeDomain i p)
    (hz : eval rho p = 0) :
    SM.extendCoordinateAssignment i (fun j => rho j)
      (SM.coordinateRootFunction i p (fun j => rho j)) = rho := by
  have he := (SM.coordinate_graph_actual_assignment i p hp rho hdom).mp hz
  rw [← he, SM.extendCoordinateAssignment_reconstruct]
