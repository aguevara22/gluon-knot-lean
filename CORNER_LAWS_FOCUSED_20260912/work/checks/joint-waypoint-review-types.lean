import SM.WaypointOpenDomain

-- Independent inspection of the frozen five-module choice implementation.
#print SM.CoordinateWaypointLeg
#print SM.waypointSelection
#print SM.waypointPullback
#print SM.remainingWaypointSelection
#print SM.remainingWaypointPullback
#print SM.CoordinateWaypointLeg.beforeTag
#print SM.CoordinateWaypointLeg.afterTag
#print SM.CoordinateWaypointLeg.endpoint
#print SM.CoordinateWaypointLeg.fixedAssignment
#print SM.CoordinateWaypointLeg.stepPolynomial
#print SM.CoordinateWaypointLeg.assignment
#print SM.JointLegCondition
#print SM.jointLegConstraint
#print SM.JointLegConditions
#print SM.waypointDomain
#print SM.exists_joint_waypoint_conditions_in_domains
#check @SM.waypointSelection_injective
#print axioms SM.waypointSelection_injective
#check @SM.waypointPullback_injective
#print axioms SM.waypointPullback_injective
#check @SM.waypointPullback_ne_zero
#print axioms SM.waypointPullback_ne_zero
#check @SM.eval_waypointPullback
#print axioms SM.eval_waypointPullback
#check @SM.remainingWaypointSelection_injective
#print axioms SM.remainingWaypointSelection_injective
#check @SM.remainingWaypointPullback_injective
#print axioms SM.remainingWaypointPullback_injective
#check @SM.remainingWaypointPullback_ne_zero
#print axioms SM.remainingWaypointPullback_ne_zero
#check @SM.eval_remainingWaypointPullback
#print axioms SM.eval_remainingWaypointPullback
#check @SM.waypoint_coordinateDifference_ne_zero
#print axioms SM.waypoint_coordinateDifference_ne_zero
#check @SM.CoordinateWaypointLeg.endpoints_agree_other
#print axioms SM.CoordinateWaypointLeg.endpoints_agree_other
#check @SM.CoordinateWaypointLeg.endpoint_reconstruct
#print axioms SM.CoordinateWaypointLeg.endpoint_reconstruct
#check @SM.CoordinateWaypointLeg.stepPolynomial_ne_zero
#print axioms SM.CoordinateWaypointLeg.stepPolynomial_ne_zero
#check @SM.CoordinateWaypointLeg.eval_stepPolynomial
#print axioms SM.CoordinateWaypointLeg.eval_stepPolynomial
#check @SM.CoordinateWaypointLeg.assignment_zero
#print axioms SM.CoordinateWaypointLeg.assignment_zero
#check @SM.CoordinateWaypointLeg.assignment_one
#print axioms SM.CoordinateWaypointLeg.assignment_one
#check @SM.CoordinateWaypointLeg.assignment_other
#print axioms SM.CoordinateWaypointLeg.assignment_other
#check @SM.jointLegConstraint_ne_zero
#print axioms SM.jointLegConstraint_ne_zero
#check @SM.jointLegConditions_iff
#print axioms SM.jointLegConditions_iff
#check @SM.exists_joint_waypoint_conditions
#print axioms SM.exists_joint_waypoint_conditions
#check @SM.continuous_waypointProjection
#print axioms SM.continuous_waypointProjection
#check @SM.isOpen_waypointDomain
#print axioms SM.isOpen_waypointDomain
#check @SM.nonempty_waypointDomain
#print axioms SM.nonempty_waypointDomain
#check @SM.exists_joint_waypoint_conditions_in_domains
#print axioms SM.exists_joint_waypoint_conditions_in_domains
