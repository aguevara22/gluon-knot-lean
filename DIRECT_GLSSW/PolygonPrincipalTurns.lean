import PolygonPositiveDiagram
import ActualAdmissibleRounding

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open PrincipalTurning PolygonDrawing EventSegmentGeometry
open scoped BigOperators
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

def polygonEdgeVector (i : Fin n) : ℂ :=
  ⟨(cyclicTangent q i).1,(cyclicTangent q i).2⟩

noncomputable def originalCornerTurn (i : Fin n) : ℝ :=
  Complex.arg (polygonEdgeVector q i / polygonEdgeVector q ((cyclicSuccessorPerm n).symm i))

noncomputable def originalCornerTotalTurn : ℝ := ∑ i : Fin n, originalCornerTurn q i

theorem polygonEvent_arcVector (x : PolygonEvent q) :
    arcVector (positivePolygonEventDiagram q hq) (eventFin q x) =
      (stepScale q hq x : ℂ) * polygonEdgeVector q (polygonEventEdge q x) := by
  apply Complex.equivRealProd.injective
  have h := arc_vector_eq q hq x
  simpa only [arcVector,positivePolygonEventDiagram,positiveDiagram,
    polygonEventDiagram_arcTarget,polygonEventDiagram_arcSource,
    polygonEventDiagram_vertexPoint,Complex.equivRealProd_apply,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    polygonEdgeVector,zero_mul,mul_zero,
    sub_zero,zero_add,add_zero,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Prod.smul_mk] using h

theorem polygonEvent_turn (x : PolygonEvent q) :
    turn (positivePolygonEventDiagram q hq) (eventFin q x) =
      Complex.arg (polygonEdgeVector q (polygonEventEdge q (polygonEventSuccessor q hq.g2 x)) /
        polygonEdgeVector q (polygonEventEdge q x)) := by
  change Complex.arg (arcVector (positivePolygonEventDiagram q hq)
    ((polygonEventDiagram q hq).continuation (eventFin q x)) / _) = _
  rw [polygonEventDiagram_continuation,polygonEvent_arcVector,polygonEvent_arcVector]
  exact turn_positive_rescale _ _ _ _ (stepScale_pos q hq _) (stepScale_pos q hq _)

/-- Each original anchor contributes its actual original corner; crossing
subdivision visits contribute zero. The sum is indexed by destination event. -/
theorem polygonEvent_turn_at_destination (y : PolygonEvent q) :
    turn (positivePolygonEventDiagram q hq)
      (eventFin q ((polygonEventSuccessor q hq.g2).symm y)) =
      match y with
      | Sum.inl i => originalCornerTurn q i
      | Sum.inr _ => 0 := by
  rw [polygonEvent_turn]
  simp only [Equiv.apply_symm_apply]
  have hclass := polygonEventSuccessor_sameEdge_next_or_nextAnchor q hq.g2 hq.size_ge_three
    ((polygonEventSuccessor q hq.g2).symm y)
  simp only [Equiv.apply_symm_apply] at hclass
  cases y with
  | inl i =>
    have he : polygonEventEdge q ((polygonEventSuccessor q hq.g2).symm (Sum.inl i)) =
        (cyclicSuccessorPerm n).symm i := by
      rcases hclass with hs | hn
      · have hp : polygonEventParameter q
            ((polygonEventSuccessor q hq.g2).symm (Sum.inl i)) < 0 := hs.2.1
        have hnonneg : 0 ≤ polygonEventParameter q
            ((polygonEventSuccessor q hq.g2).symm (Sum.inl i)) := by
          cases hx : (polygonEventSuccessor q hq.g2).symm (Sum.inl i) with
          | inl a => simp [hx,polygonEventParameter]
          | inr v => exact (crossingVisitParameter_spec q v).1.le
        exact (not_lt_of_ge hnonneg hp).elim
      · have hi := Sum.inl.inj hn.1
        have hperm : i = cyclicSuccessorPerm n (polygonEventEdge q
            ((polygonEventSuccessor q hq.g2).symm (Sum.inl i))) := hi
        simpa only [Equiv.symm_apply_apply] using
          (congrArg (cyclicSuccessorPerm n).symm hperm).symm
    rw [he]
    rfl
  | inr v =>
    have he : polygonEventEdge q (Sum.inr v) =
        polygonEventEdge q ((polygonEventSuccessor q hq.g2).symm (Sum.inr v)) := by
      rcases hclass with hs | hn
      · exact hs.1
      · exact (Sum.noConfusion hn.1)
    rw [he]
    have hz : polygonEdgeVector q (polygonEventEdge q
        ((polygonEventSuccessor q hq.g2).symm (Sum.inr v))) ≠ 0 := by
      intro hz
      apply cyclicTangent_ne_zero hq.size_ge_three q hq.g1
        (polygonEventEdge q ((polygonEventSuccessor q hq.g2).symm (Sum.inr v)))
      apply Prod.ext
      · exact congrArg Complex.re hz
      · exact congrArg Complex.im hz
    simp [div_self hz]

end DirectGLSSW.HOMFLY.PolygonDrawingBridge



