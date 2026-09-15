import SM.CentralRootGerms
import SM.RegularScalarBoxes
import SM.OrderedCoordinateLegs

set_option pp.universes false
#check SM.scalarOpenBox
#print axioms SM.scalarOpenBox
#check SM.scalarClosedBox
#print axioms SM.scalarClosedBox
#check SM.isOpen_scalarOpenBox
#print axioms SM.isOpen_scalarOpenBox
#check SM.isClosed_scalarClosedBox
#print axioms SM.isClosed_scalarClosedBox
#check SM.scalarOpenBox_subset_closed
#print axioms SM.scalarOpenBox_subset_closed
#check SM.closure_scalarOpenBox_subset_closed
#print axioms SM.closure_scalarOpenBox_subset_closed
#check SM.scalarOpenBox_self
#print axioms SM.scalarOpenBox_self
#check SM.scalarOpenBox_eq_pi
#print axioms SM.scalarOpenBox_eq_pi
#check SM.convex_scalarOpenBox
#print axioms SM.convex_scalarOpenBox
#check SM.scalarOpenBox_mem_of_coordinates
#print axioms SM.scalarOpenBox_mem_of_coordinates
#check SM.scalarAssignmentLine_mem_box
#print axioms SM.scalarAssignmentLine_mem_box
#check SM.exists_scalarBox_closed_subset
#print axioms SM.exists_scalarBox_closed_subset
#check SM.exists_scalarBox_closure_subset
#print axioms SM.exists_scalarBox_closure_subset
#check SM.tupleScalarBox
#print axioms SM.tupleScalarBox
#check SM.isOpen_tupleScalarBox
#print axioms SM.isOpen_tupleScalarBox
#check SM.tupleScalarBox_self
#print axioms SM.tupleScalarBox_self
#check SM.exists_tupleScalarBox_closure_diameter
#print axioms SM.exists_tupleScalarBox_closure_diameter
#check SM.central_control_continuous
#print axioms SM.central_control_continuous
#check SM.central_root_other_control_ne_zero
#print axioms SM.central_root_other_control_ne_zero
#check SM.central_root_other_products_eventually
#print axioms SM.central_root_other_products_eventually
#check SM.central_root_neighborhood
#print axioms SM.central_root_neighborhood
#print SM.CentralRootPatch
#check SM.nonempty_centralRootPatch
#print axioms SM.nonempty_centralRootPatch
#check SM.chooseCentralRootPatch
#print axioms SM.chooseCentralRootPatch
#check SM.CentralRootPatch.time_mem_leg
#print axioms SM.CentralRootPatch.time_mem_leg
#check SM.CentralRootPatch.toWallGerm
#print axioms SM.CentralRootPatch.toWallGerm
#check SM.CentralRootPatch.toWallGerm_center
#print axioms SM.CentralRootPatch.toWallGerm_center
#check SM.CentralRootPatch.toWallGerm_curve_eq
#print axioms SM.CentralRootPatch.toWallGerm_curve_eq
#check SM.CentralRootPatch.toWallGerm_curve_collision_free
#print axioms SM.CentralRootPatch.toWallGerm_curve_collision_free
#check SM.CentralRootPatch.toWallGerm_other_products
#print axioms SM.CentralRootPatch.toWallGerm_other_products
#check SM.CentralRootPatch.parameter_isRoot
#print axioms SM.CentralRootPatch.parameter_isRoot
#check SM.CentralRootPatch.toWallGerm_control_signChanges
#print axioms SM.CentralRootPatch.toWallGerm_control_signChanges
#check SM.CentralRootPatch.parameterSlope_ne_zero
#print axioms SM.CentralRootPatch.parameterSlope_ne_zero
#check SM.CentralRootPatch.centered_control_hasDerivAt
#print axioms SM.CentralRootPatch.centered_control_hasDerivAt
#check SM.central_nongeneric_has_wallGerm
#print axioms SM.central_nongeneric_has_wallGerm
#check SM.CoordinateWaypointLeg.endpoint_mem_box
#print axioms SM.CoordinateWaypointLeg.endpoint_mem_box
#check SM.CoordinateWaypointLeg.assignment_mem_box
#print axioms SM.CoordinateWaypointLeg.assignment_mem_box
#check SM.CoordinateWaypointLeg.tuple_assignment_mem_box
#print axioms SM.CoordinateWaypointLeg.tuple_assignment_mem_box
#check SM.exists_regular_tupleScalarBox
#print axioms SM.exists_regular_tupleScalarBox
#check SM.exists_generic_tupleScalarBox
#print axioms SM.exists_generic_tupleScalarBox
#check SM.scalarCoordinateOrder
#print axioms SM.scalarCoordinateOrder
#check SM.orderedHybrid
#print axioms SM.orderedHybrid
#check SM.orderedHybrid_zero
#print axioms SM.orderedHybrid_zero
#check SM.orderedHybrid_last
#print axioms SM.orderedHybrid_last
#check SM.orderedHybrid_mem_box
#print axioms SM.orderedHybrid_mem_box
#check SM.orderedScalarLeg
#print axioms SM.orderedScalarLeg
#check SM.orderedScalarLeg_zero
#print axioms SM.orderedScalarLeg_zero
#check SM.orderedScalarLeg_one
#print axioms SM.orderedScalarLeg_one
#check SM.orderedScalarLeg_join
#print axioms SM.orderedScalarLeg_join
#check SM.orderedScalarLeg_start
#print axioms SM.orderedScalarLeg_start
#check SM.orderedScalarLeg_finish
#print axioms SM.orderedScalarLeg_finish
#check SM.continuous_orderedScalarLeg
#print axioms SM.continuous_orderedScalarLeg
#check SM.orderedScalarLeg_mem_box
#print axioms SM.orderedScalarLeg_mem_box
#check SM.orderedWaypointLeg
#print axioms SM.orderedWaypointLeg
#check SM.orderedWaypointLeg_endpoint_false
#print axioms SM.orderedWaypointLeg_endpoint_false
#check SM.orderedWaypointLeg_endpoint_true
#print axioms SM.orderedWaypointLeg_endpoint_true
#check SM.orderedWaypointLeg_assignment
#print axioms SM.orderedWaypointLeg_assignment
#print SM.CentralRootPatch.toWallGerm
#print SM.orderedHybrid
#print SM.orderedWaypointLeg
#print SM.scalarCoordinateOrder

open Set MvPolynomial

-- No root equation, control name, slope or derivative is an input here.
example {κ : Type*} {n : ℕ} (hn : 3 ≤ n)
    (leg : SM.CoordinateWaypointLeg κ (SM.ScalarCoordinate n))
    (W : κ × SM.ScalarCoordinate n → ℝ) (h : SM.JointLegConditions leg W)
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hng : ¬ SM.Generic (SM.tupleOfScalarCoordinates (leg.assignment W r))) :
    ∃ g : SM.WallGerm n,
      g.center = SM.tupleOfScalarCoordinates (leg.assignment W r) ∧
      (∀ t : g.Parameter, t.val ≠ 0 → SM.Generic (g.curve t)) ∧
      (∀ t : g.Parameter, Function.Injective (g.curve t)) ∧
      ∃ name : SM.PolynomialControlName n, ∃ d : ℝ, d ≠ 0 ∧ HasDerivAt
        (fun s : ℝ => eval (leg.assignment W (r+s)) (SM.namedControlPolynomial name)) d 0 := by
  obtain ⟨name, g, hc, _, _, hcol, _, _, hd⟩ :=
    SM.central_nongeneric_has_wallGerm hn leg W h r hr hng
  exact ⟨g, hc, g.generic_punctured, hcol, name, hd⟩

example {n : ℕ} (hn : 3 ≤ n) :
    ∃ order : SM.ScalarCoordinate n ≃ Fin (2*n),
      (∀ c, order.symm (order c) = c) ∧
      (∀ j, order (order.symm j) = j) ∧ 0 < 2*n := by
  haveI : NeZero n := ⟨by omega⟩
  exact ⟨SM.scalarCoordinateOrder n, (SM.scalarCoordinateOrder n).symm_apply_apply,
    (SM.scalarCoordinateOrder n).apply_symm_apply, by omega⟩

-- Generic cube containment gives individual endpoint-collar legs, even if
-- polynomials vanish at the original endpoints; no such nonvanishing is assumed.
example {n : ℕ} {m : ℕ} (order : SM.ScalarCoordinate n ≃ Fin m)
    (P Q R : SM.LabelledTuple n) (radius : ℝ)
    (hc : closure (SM.tupleScalarBox P radius) ⊆ {U | SM.Regular U ∧ SM.Generic U})
    (hQ : Q ∈ SM.tupleScalarBox P radius) (hR : R ∈ SM.tupleScalarBox P radius)
    (j : Fin m) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    SM.Regular (SM.tupleOfScalarCoordinates
      (SM.orderedScalarLeg order (SM.scalarCoordinates Q) (SM.scalarCoordinates R) j t)) ∧
    SM.Generic (SM.tupleOfScalarCoordinates
      (SM.orderedScalarLeg order (SM.scalarCoordinates Q) (SM.scalarCoordinates R) j t)) := by
  apply hc
  apply subset_closure
  change SM.scalarCoordinates (SM.tupleOfScalarCoordinates
    (SM.orderedScalarLeg order (SM.scalarCoordinates Q) (SM.scalarCoordinates R) j t)) ∈
      SM.scalarOpenBox (SM.scalarCoordinates P) radius
  rw [SM.scalarCoordinates_tupleOf]
  exact SM.orderedScalarLeg_mem_box order (SM.scalarCoordinates P)
    (SM.scalarCoordinates Q) (SM.scalarCoordinates R) radius hQ hR j t ht
