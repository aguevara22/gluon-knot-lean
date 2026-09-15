import SM.CentralLegCollision

-- Independent review of actual tuple topology and collision-free coordinate legs.
#print SM.scalarCoordinateHomeomorph
#print SM.otherPlaneCoordinate
#check @SM.continuous_scalarCoordinates
#print axioms SM.continuous_scalarCoordinates
#check @SM.continuous_tupleOfScalarCoordinates
#print axioms SM.continuous_tupleOfScalarCoordinates
#check @SM.scalarCoordinateHomeomorph
#print axioms SM.scalarCoordinateHomeomorph
#check @SM.CoordinateWaypointLeg.assignment_eq_line
#print axioms SM.CoordinateWaypointLeg.assignment_eq_line
#check @SM.CoordinateWaypointLeg.continuous_assignment
#print axioms SM.CoordinateWaypointLeg.continuous_assignment
#check @SM.otherPlaneCoordinate_ne
#print axioms SM.otherPlaneCoordinate_ne
#check @SM.tupleOfScalarCoordinates_eq_component
#print axioms SM.tupleOfScalarCoordinates_eq_component
#check @SM.central_leg_collision_free
#print axioms SM.central_leg_collision_free
#check @SM.continuous_central_tuple_leg
#print axioms SM.continuous_central_tuple_leg

example {κ : Type*} {n : ℕ} (leg : SM.CoordinateWaypointLeg κ (SM.ScalarCoordinate n))
    (W : κ × SM.ScalarCoordinate n → ℝ) :
    SM.tupleOfScalarCoordinates (leg.assignment W 0) =
      SM.tupleOfScalarCoordinates (leg.endpoint false W) := by
  rw [leg.assignment_zero W]

example {κ : Type*} {n : ℕ} (leg : SM.CoordinateWaypointLeg κ (SM.ScalarCoordinate n))
    (W : κ × SM.ScalarCoordinate n → ℝ) :
    SM.tupleOfScalarCoordinates (leg.assignment W 1) =
      SM.tupleOfScalarCoordinates (leg.endpoint true W) := by
  rw [leg.assignment_one W]
