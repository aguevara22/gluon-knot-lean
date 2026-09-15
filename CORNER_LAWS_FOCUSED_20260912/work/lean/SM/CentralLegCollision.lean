import SM.JointWaypointConstraints
import SM.ScalarCoordinateTopology

/-! Actual continuous affine central coordinate legs are collision-free under
the source's proved endpoint coordinate-difference conditions. The component not
being moved remains unchanged for every vertex, and separates every pair. -/

namespace SM

noncomputable section

variable {κ σ : Type*} {n : ℕ}

theorem CoordinateWaypointLeg.assignment_eq_line (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) (t : ℝ) :
    leg.assignment W t = scalarAssignmentLine (leg.endpoint false W) (leg.endpoint true W) t := by
  classical
  funext w
  by_cases hw : w = leg.moving
  · subst w
    simp only [assignment, extendCoordinateAssignment_self, scalarAssignmentLine]
  · have he := leg.endpoints_agree_other W w hw
    have ha := leg.assignment_other W t ⟨w, hw⟩
    change leg.assignment W t w = _ at ha
    rw [ha]
    simp only [scalarAssignmentLine, he, sub_self, mul_zero, add_zero]
    rfl

theorem CoordinateWaypointLeg.continuous_assignment (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) : Continuous (leg.assignment W) := by
  have he : leg.assignment W = scalarAssignmentLine (leg.endpoint false W) (leg.endpoint true W) :=
    funext (leg.assignment_eq_line W)
  rw [he]
  exact continuous_scalarAssignmentLine _ _

def otherPlaneCoordinate (c : Fin 2) : Fin 2 := if c = 0 then 1 else 0

theorem otherPlaneCoordinate_ne (c : Fin 2) : otherPlaneCoordinate c ≠ c := by
  fin_cases c <;> decide

theorem tupleOfScalarCoordinates_eq_component (x : ScalarCoordinate n → ℝ)
    (i j : ZMod n) (h : tupleOfScalarCoordinates x i = tupleOfScalarCoordinates x j)
    (c : Fin 2) : x (i, c) = x (j, c) := by
  fin_cases c
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

theorem central_leg_collision_free (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W) (t : ℝ) :
    Function.Injective (tupleOfScalarCoordinates (leg.assignment W t)) := by
  intro i j hij
  by_contra hne
  let c := otherPlaneCoordinate leg.moving.2
  have hc : c ≠ leg.moving.2 := otherPlaneCoordinate_ne leg.moving.2
  have hi : (i, c) ≠ leg.moving := fun he => hc (congrArg Prod.snd he)
  have hj : (j, c) ≠ leg.moving := fun he => hc (congrArg Prod.snd he)
  have he := tupleOfScalarCoordinates_eq_component _ i j hij c
  have hei := leg.assignment_other W t ⟨(i, c), hi⟩
  have hej := leg.assignment_other W t ⟨(j, c), hj⟩
  change leg.assignment W t (i, c) = leg.endpoint false W (i, c) at hei
  change leg.assignment W t (j, c) = leg.endpoint false W (j, c) at hej
  rw [hei, hej] at he
  exact h.vertex_differences false i j c hne (sub_eq_zero.mpr he)

theorem continuous_central_tuple_leg (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) :
    Continuous (fun t => tupleOfScalarCoordinates (leg.assignment W t)) :=
  continuous_tupleOfScalarCoordinates.comp (leg.continuous_assignment W)

end

end SM
