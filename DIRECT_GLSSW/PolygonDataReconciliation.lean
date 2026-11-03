import OriginalLeftTurnLocality
import PolygonRotationSum

set_option autoImplicit false
namespace DirectGLSSW.PolygonDataReconciliation
open DirectGLSSW.OriginalLeftTurnLocality
open DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW.HOMFLY.PrincipalTurning
open DirectGLSSW.HOMFLY

/-- The existing left-turn count is literally the source's count at the
incoming/outgoing tangent pair of every labelled polygon vertex. -/
theorem leftTurnCount_literal {n : ℕ} (q : Fin n → PlanarPoint ℝ) :
    leftTurnCount q =
      (Finset.univ.filter (fun i : Fin n =>
        0 < planarDet
          (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i))
          (cyclicTangent q i))).card := rfl

/-- Reconcile the source corner sum with the already existing finite-diagram
turn integer. This makes no new rotation definition. -/
theorem originalCornerTotalTurn_eq_actualTurnInteger {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    originalCornerTotalTurn q =
      (turnInteger (positivePolygonEventDiagram q hq) : ℝ) * (2 * Real.pi) := by
  rw [← positivePolygonEventDiagram_totalTurn q hq]
  exact totalTurn_eq_turnInteger _

/-- The same integer is the degree of the literal rounded polygon tangent:
the existing provider proves every continuous lift has this increment. -/
theorem actualLift_increment_eq_actualTurnInteger {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin (positivePolygonEventDiagram q hq).nArc)
    (δ : RoundingFraction) (f : ℝ → ℝ) (hf : Continuous f)
    (hangle : ∀ t, (f t : Real.Angle) =
      ((roundedComponentVelocity (positivePolygonEventDiagram q hq) e δ t).arg : Real.Angle)) :
    f (componentArcLength (positivePolygonEventDiagram q hq) e) - f 0 =
      (turnInteger (positivePolygonEventDiagram q hq) : ℝ) * (2 * Real.pi) := by
  rw [positivePolygon_any_actual_tangent_lift_increment q hq e δ f hf hangle]
  exact originalCornerTotalTurn_eq_actualTurnInteger q hq

end DirectGLSSW.PolygonDataReconciliation




