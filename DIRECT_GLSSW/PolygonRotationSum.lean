import PolygonPrincipalTurns

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open PrincipalTurning PolygonDrawing EventSegmentGeometry PermutationOrbits
open scoped BigOperators
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

theorem positivePolygonEventDiagram_totalTurn :
    totalTurn (positivePolygonEventDiagram q hq) = originalCornerTotalTurn q := by
  classical
  calc
    totalTurn (positivePolygonEventDiagram q hq) =
        ∑ x : PolygonEvent q, turn (positivePolygonEventDiagram q hq) (eventFin q x) := by
      exact (Fintype.sum_equiv (eventFin q) _ _ (fun _ => rfl)).symm
    _ = ∑ y : PolygonEvent q, turn (positivePolygonEventDiagram q hq)
        (eventFin q ((polygonEventSuccessor q hq.g2).symm y)) := by
      apply Fintype.sum_equiv (polygonEventSuccessor q hq.g2)
      intro x
      simp only [Equiv.symm_apply_apply]
    _ = originalCornerTotalTurn q := by
      simp only [polygonEvent_turn_at_destination]
      change (∑ y : Fin n ⊕ CrossingVisit q, match y with
        | Sum.inl i => originalCornerTurn q i
        | Sum.inr _ => 0) = _
      rw [Fintype.sum_sum_type]
      simp only [Finset.sum_const_zero,add_zero,originalCornerTotalTurn]

theorem positivePolygonEventDiagram_componentTotalTurn
    (e : Fin (positivePolygonEventDiagram q hq).nArc) :
    componentTotalTurn (positivePolygonEventDiagram q hq)
      (componentOf (positivePolygonEventDiagram q hq).continuation e) = originalCornerTotalTurn q := by
  classical
  let D := positivePolygonEventDiagram q hq
  have hp : D.continuation.IsCycleOn Set.univ := polygonEventDiagram_isCycleOn q hq
  let E : Fibre D.continuation (componentOf D.continuation e) ≃ Fin D.nArc :=
    { toFun := fun x => x.val
      invFun := fun x => ⟨x, (componentOf_eq_iff D.continuation x e).mpr
        (hp.2 (Set.mem_univ x) (Set.mem_univ e))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : componentTotalTurn D (componentOf D.continuation e) = totalTurn D :=
    Fintype.sum_equiv E _ _ (fun _ => rfl)
  exact hs.trans (positivePolygonEventDiagram_totalTurn q hq)

include hq in
/-- The original polygon corner sum represents a unique integer. This is
proved using the actual concrete single component, rather than assigned. -/
theorem originalCornerTotalTurn_existsUnique_integer :
    ∃! r : ℤ, originalCornerTotalTurn q = (r : ℝ) * (2 * Real.pi) := by
  rw [← positivePolygonEventDiagram_totalTurn q hq]
  exact existsUnique_turnInteger (positivePolygonEventDiagram q hq)

/-- Every starting time of the actual rounded polygon tangent has exactly
the original n-corner sum as its increment. No rounding-independence claim
for unspecified other roundings is included. -/
theorem positivePolygon_actualTangentLift_shift
    (e : Fin (positivePolygonEventDiagram q hq).nArc)
    (δ : RoundingFraction) (t : ℝ) :
    actualTangentLift (positivePolygonEventDiagram q hq) e δ
        (t + (componentArcLength (positivePolygonEventDiagram q hq) e : ℝ)) -
      actualTangentLift (positivePolygonEventDiagram q hq) e δ t = originalCornerTotalTurn q := by
  rw [actualTangentLift_shift,positivePolygonEventDiagram_componentTotalTurn]

/-- The actual continuous tangent degree of this explicit rounding equals
the uniquely represented original polygon corner sum. -/
theorem positivePolygon_any_actual_tangent_lift_increment
    (e : Fin (positivePolygonEventDiagram q hq).nArc) (δ : RoundingFraction)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hangle : ∀ t, (f t : Real.Angle) =
      ((roundedComponentVelocity (positivePolygonEventDiagram q hq) e δ t).arg : Real.Angle)) :
    f (componentArcLength (positivePolygonEventDiagram q hq) e) - f 0 = originalCornerTotalTurn q := by
  rw [any_actual_tangent_lift_increment _ _ _ f hf hangle,
    positivePolygonEventDiagram_componentTotalTurn]

end DirectGLSSW.HOMFLY.PolygonDrawingBridge





