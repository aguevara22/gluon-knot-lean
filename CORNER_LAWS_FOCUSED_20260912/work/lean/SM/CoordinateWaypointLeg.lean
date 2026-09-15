import SM.WaypointPullback
import SM.CoefficientSpecialization

/-! A central coordinate leg between two independent internal waypoints. The
already switched coordinates use the right waypoint; exactly one further scalar
changes on this leg. All other scalar assignments agree at its two endpoints. -/

namespace SM

open MvPolynomial

noncomputable section

variable {κ σ : Type*}

structure CoordinateWaypointLeg (κ σ : Type*) where
  left : κ
  right : κ
  left_ne_right : left ≠ right
  moving : σ
  switched : Set σ
  moving_not_switched : moving ∉ switched

def CoordinateWaypointLeg.beforeTag (leg : CoordinateWaypointLeg κ σ) : σ → κ := by
  classical
  exact fun w => if w ∈ leg.switched then leg.right else leg.left

def CoordinateWaypointLeg.afterTag (leg : CoordinateWaypointLeg κ σ) : σ → κ := by
  classical
  exact fun w => if w = leg.moving then leg.right else leg.beforeTag w

def CoordinateWaypointLeg.tag (leg : CoordinateWaypointLeg κ σ) (b : Bool) : σ → κ :=
  if b then leg.afterTag else leg.beforeTag

@[simp] theorem CoordinateWaypointLeg.beforeTag_moving (leg : CoordinateWaypointLeg κ σ) :
    leg.beforeTag leg.moving = leg.left := by
  simp [beforeTag, leg.moving_not_switched]

@[simp] theorem CoordinateWaypointLeg.afterTag_moving (leg : CoordinateWaypointLeg κ σ) :
    leg.afterTag leg.moving = leg.right := by
  simp [afterTag]

theorem CoordinateWaypointLeg.afterTag_other (leg : CoordinateWaypointLeg κ σ)
    (w : σ) (hw : w ≠ leg.moving) : leg.afterTag w = leg.beforeTag w := by
  simp [afterTag, hw]

@[simp] theorem CoordinateWaypointLeg.tag_false (leg : CoordinateWaypointLeg κ σ) :
    leg.tag false = leg.beforeTag := rfl

@[simp] theorem CoordinateWaypointLeg.tag_true (leg : CoordinateWaypointLeg κ σ) :
    leg.tag true = leg.afterTag := rfl

def CoordinateWaypointLeg.endpoint (leg : CoordinateWaypointLeg κ σ)
    (b : Bool) (W : κ × σ → ℝ) : σ → ℝ := waypointHybrid (leg.tag b) W

def CoordinateWaypointLeg.fixedAssignment (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) : {w : σ // w ≠ leg.moving} → ℝ :=
  fun w => leg.endpoint false W w

@[simp] theorem CoordinateWaypointLeg.endpoint_false_moving (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) : leg.endpoint false W leg.moving = W (leg.left, leg.moving) := by
  simp [endpoint, waypointHybrid, waypointSelection]

@[simp] theorem CoordinateWaypointLeg.endpoint_true_moving (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) : leg.endpoint true W leg.moving = W (leg.right, leg.moving) := by
  simp [endpoint, waypointHybrid, waypointSelection]

theorem CoordinateWaypointLeg.endpoints_agree_other (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) (w : σ) (hw : w ≠ leg.moving) :
    leg.endpoint true W w = leg.endpoint false W w := by
  simp only [endpoint, waypointHybrid, waypointSelection, tag_true, tag_false,
    leg.afterTag_other w hw]

theorem CoordinateWaypointLeg.endpoint_fixed (leg : CoordinateWaypointLeg κ σ)
    (b : Bool) (W : κ × σ → ℝ) (w : {w : σ // w ≠ leg.moving}) :
    leg.endpoint b W w = leg.fixedAssignment W w := by
  cases b
  · rfl
  · exact leg.endpoints_agree_other W w w.property

theorem CoordinateWaypointLeg.endpoint_reconstruct (leg : CoordinateWaypointLeg κ σ)
    (b : Bool) (W : κ × σ → ℝ) :
    extendCoordinateAssignment leg.moving (leg.fixedAssignment W)
      (leg.endpoint b W leg.moving) = leg.endpoint b W := by
  have h : leg.fixedAssignment W =
      fun w : {w : σ // w ≠ leg.moving} => leg.endpoint b W w := by
    funext w
    exact (leg.endpoint_fixed b W w).symm
  rw [h]
  exact extendCoordinateAssignment_reconstruct _ _

def CoordinateWaypointLeg.stepPolynomial (leg : CoordinateWaypointLeg κ σ) :
    MvPolynomial (κ × σ) ℝ := X (leg.right, leg.moving) - X (leg.left, leg.moving)

theorem CoordinateWaypointLeg.stepPolynomial_ne_zero (leg : CoordinateWaypointLeg κ σ) :
    leg.stepPolynomial ≠ 0 := by
  apply coordinateDifference_ne_zero
  intro h
  exact leg.left_ne_right (congrArg Prod.fst h).symm

@[simp] theorem CoordinateWaypointLeg.eval_stepPolynomial (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) : eval W leg.stepPolynomial =
      leg.endpoint true W leg.moving - leg.endpoint false W leg.moving := by
  simp [stepPolynomial]

def CoordinateWaypointLeg.assignment (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) (t : ℝ) : σ → ℝ :=
  extendCoordinateAssignment leg.moving (leg.fixedAssignment W)
    (leg.endpoint false W leg.moving +
      t * (leg.endpoint true W leg.moving - leg.endpoint false W leg.moving))

@[simp] theorem CoordinateWaypointLeg.assignment_zero (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) : leg.assignment W 0 = leg.endpoint false W := by
  simp only [assignment, zero_mul, add_zero]
  exact leg.endpoint_reconstruct false W

@[simp] theorem CoordinateWaypointLeg.assignment_one (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) : leg.assignment W 1 = leg.endpoint true W := by
  simp only [assignment, one_mul, add_sub_cancel]
  exact leg.endpoint_reconstruct true W

theorem CoordinateWaypointLeg.assignment_other (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) (t : ℝ) (w : {w : σ // w ≠ leg.moving}) :
    leg.assignment W t w = leg.fixedAssignment W w :=
  extendCoordinateAssignment_other _ _ _ w

end

end SM
