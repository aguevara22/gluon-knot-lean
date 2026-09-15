import SM.TransportPolynomials
import SM.CoordinateWaypointLeg
import SM.MultivariateAvoidance

/-! The actual finite joint polynomial conditions for central coordinate legs.
Every required polynomial is proved nonzero before simultaneous avoidance is
applied. Internal waypoint labels are independent variables; fixed original path
endpoints are not substituted into this joint variable space. -/

namespace SM

open MvPolynomial

noncomputable section

variable {κ : Type*} {n : ℕ}

abbrev DependentControlName (n : ℕ) (z : ScalarCoordinate n) :=
  {name : PolynomialControlName n // z ∈ (namedControlPolynomial name).vars}

abbrev ResultantControlName (n : ℕ) (z : ScalarCoordinate n) :=
  {uv : PolynomialControlName n × PolynomialControlName n //
    uv.1 ≠ uv.2 ∧ z ∈ (namedControlPolynomial uv.1).vars ∧
      z ∈ (namedControlPolynomial uv.2).vars}

abbrev VertexCoordinateDifferenceName (n : ℕ) :=
  {ij : ZMod n × ZMod n // ij.1 ≠ ij.2} × Fin 2

abbrev JointLegCondition (n : ℕ) (z : ScalarCoordinate n) :=
  (Bool × PolynomialControlName n) ⊕ DependentControlName n z ⊕
    ResultantControlName n z ⊕ Unit ⊕ (Bool × VertexCoordinateDifferenceName n)

instance jointLegConditionFintype [NeZero n] (z : ScalarCoordinate n) :
    Fintype (JointLegCondition n z) := Fintype.ofFinite _

def jointLegConstraint (leg : CoordinateWaypointLeg κ (ScalarCoordinate n)) :
    JointLegCondition n leg.moving → MvPolynomial (κ × ScalarCoordinate n) ℝ
  | .inl (b, name) => waypointPullback (leg.tag b) (namedControlPolynomial name)
  | .inr (.inl name) => remainingWaypointPullback leg.moving leg.beforeTag
      (coordinateSlope leg.moving (namedControlPolynomial name.val))
  | .inr (.inr (.inl uv)) => remainingWaypointPullback leg.moving leg.beforeTag
      (coordinateResultant leg.moving (namedControlPolynomial uv.val.1)
        (namedControlPolynomial uv.val.2))
  | .inr (.inr (.inr (.inl _))) => leg.stepPolynomial
  | .inr (.inr (.inr (.inr (b, ij, c)))) => waypointPullback (leg.tag b)
      (X (ij.val.1, c) - X (ij.val.2, c))

theorem jointLegConstraint_ne_zero (hn : 3 ≤ n)
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (condition : JointLegCondition n leg.moving) : jointLegConstraint leg condition ≠ 0 := by
  rcases condition with ⟨b, name⟩ | name | uv | step | ⟨b, ij, c⟩
  · exact waypointPullback_ne_zero _ _ (namedControlPolynomial_ne_zero hn name)
  · exact remainingWaypointPullback_ne_zero _ _ _
      (coordinateSlope_ne_zero _ _ (namedControlPolynomial_affine name.val _) name.property)
  · exact remainingWaypointPullback_ne_zero _ _ _
      (coordinateResultant_ne_zero _ _ _
        (namedControlPolynomial_affine uv.val.1 _) (namedControlPolynomial_affine uv.val.2 _)
        uv.property.2.1 (namedControlPolynomial_irreducible hn uv.val.1)
        (namedControlPolynomial_irreducible hn uv.val.2)
        (namedControlPolynomial_not_associated hn _ _ uv.property.1))
  · exact leg.stepPolynomial_ne_zero
  · apply waypoint_coordinateDifference_ne_zero
    intro h
    exact ij.property (congrArg Prod.fst h)

structure JointLegConditions (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) : Prop where
  endpoint_controls : ∀ (b : Bool) (name : PolynomialControlName n),
    eval (leg.endpoint b W) (namedControlPolynomial name) ≠ 0
  dependent_slopes : ∀ name : PolynomialControlName n,
    leg.moving ∈ (namedControlPolynomial name).vars →
      eval (leg.fixedAssignment W) (coordinateSlope leg.moving (namedControlPolynomial name)) ≠ 0
  pair_resultants : ∀ u v : PolynomialControlName n, u ≠ v →
    leg.moving ∈ (namedControlPolynomial u).vars →
    leg.moving ∈ (namedControlPolynomial v).vars →
      eval (leg.fixedAssignment W)
        (coordinateResultant leg.moving (namedControlPolynomial u) (namedControlPolynomial v)) ≠ 0
  scalar_step : leg.endpoint true W leg.moving - leg.endpoint false W leg.moving ≠ 0
  vertex_differences : ∀ (b : Bool) (i j : ZMod n) (c : Fin 2), i ≠ j →
    leg.endpoint b W (i, c) - leg.endpoint b W (j, c) ≠ 0

theorem jointLegConditions_iff (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) :
    JointLegConditions leg W ↔ ∀ condition, eval W (jointLegConstraint leg condition) ≠ 0 := by
  have hfixed : (fun w : {w : ScalarCoordinate n // w ≠ leg.moving} =>
      waypointHybrid leg.beforeTag W w) = leg.fixedAssignment W := rfl
  constructor
  · intro h condition
    rcases condition with ⟨b, name⟩ | name | uv | step | ⟨b, ij, c⟩
    · simpa only [jointLegConstraint, eval_waypointPullback, CoordinateWaypointLeg.endpoint] using h.endpoint_controls b name
    · simpa only [jointLegConstraint, eval_remainingWaypointPullback, hfixed] using
        h.dependent_slopes name.val name.property
    · simpa only [jointLegConstraint, eval_remainingWaypointPullback, hfixed] using
        h.pair_resultants uv.val.1 uv.val.2 uv.property.1 uv.property.2.1 uv.property.2.2
    · exact leg.eval_stepPolynomial W ▸ h.scalar_step
    · simpa only [jointLegConstraint, eval_waypoint_coordinateDifference, CoordinateWaypointLeg.endpoint] using
        h.vertex_differences b ij.val.1 ij.val.2 c ij.property
  · intro h
    constructor
    · intro b name
      simpa only [jointLegConstraint, eval_waypointPullback, CoordinateWaypointLeg.endpoint] using h (.inl (b, name))
    · intro name hdep
      simpa only [jointLegConstraint, eval_remainingWaypointPullback, hfixed] using
        h (.inr (.inl ⟨name, hdep⟩))
    · intro u v hne hu hv
      simpa only [jointLegConstraint, eval_remainingWaypointPullback, hfixed] using
        h (.inr (.inr (.inl ⟨(u, v), hne, hu, hv⟩)))
    · simpa only [jointLegConstraint, CoordinateWaypointLeg.eval_stepPolynomial] using
        h (.inr (.inr (.inr (.inl ()))))
    · intro b i j c hij
      simpa only [jointLegConstraint, eval_waypoint_coordinateDifference, CoordinateWaypointLeg.endpoint] using
        h (.inr (.inr (.inr (.inr (b, ⟨(i, j), hij⟩, c)))))

/-- A single joint assignment satisfies all source conditions for all chosen
central legs. The nonzero constraints are derived for the concrete Δ/T family. -/
theorem exists_joint_waypoint_conditions [NeZero n] (hn : 3 ≤ n)
    {ι : Type*} [Finite ι] (legs : ι → CoordinateWaypointLeg κ (ScalarCoordinate n))
    (U : Set (κ × ScalarCoordinate n → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ W ∈ U, ∀ i, JointLegConditions (legs i) W := by
  let p : (Σ i : ι, JointLegCondition n (legs i).moving) →
      MvPolynomial (κ × ScalarCoordinate n) ℝ := fun c => jointLegConstraint (legs c.1) c.2
  have hp : ∀ c, p c ≠ 0 := fun c => jointLegConstraint_ne_zero hn (legs c.1) c.2
  obtain ⟨W, hWU, hW⟩ := exists_simultaneous_nonzero_in_open p hp U hU hne
  refine ⟨W, hWU, fun i => (jointLegConditions_iff (legs i) W).mpr ?_⟩
  exact fun c => hW ⟨i, c⟩

end

end SM
