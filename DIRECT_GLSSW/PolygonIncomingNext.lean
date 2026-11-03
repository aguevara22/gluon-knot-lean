import OrderedMarkedNext
import MarkedIncomingEvaluatorComparison
import PolygonPositiveDiagram
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open Equiv PolygonDrawing MarkedCycleGaps
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {κ : Type*} [Fintype κ] (u : κ ≃ PolygonCrossing q)

include hq in
theorem polygon_visitMark_injective :
    Function.Injective (fun m : κ × Fin 2 => visit q (u m.1) m.2) := by
  intro x y h
  have he := congrArg (fun z => (polygonEventSuccessor q hq.g2).symm z) h
  apply labelledIncoming_injective (positivePolygonEventDiagram q hq) (u.trans (crossingFin q))
  simpa only [positivePolygonEventDiagram, positiveDiagram, polygonEventDiagram,
    incomingIndex, Equiv.trans_apply, Equiv.symm_apply_apply] using congrArg (eventFin q) he

theorem polygon_incoming_next_eq_visits :
    next (positivePolygonEventDiagram q hq).continuation
      (fun m : κ × Fin 2 => (positivePolygonEventDiagram q hq).incoming
        ((u.trans (crossingFin q)) m.1) m.2)
      (labelledIncoming_injective _ _) =
    next (polygonEventSuccessor q hq.g2)
      (fun m : κ × Fin 2 => visit q (u m.1) m.2)
      (polygon_visitMark_injective q hq u) := by
  let D := positivePolygonEventDiagram q hq
  let mark : κ × Fin 2 → Fin D.nArc := fun m => D.incoming ((u.trans (crossingFin q)) m.1) m.2
  let hi : Function.Injective mark := labelledIncoming_injective D (u.trans (crossingFin q))
  have hs := next_conjugacy D.continuation D.continuation D.continuation (fun _ => rfl) mark hi
  have hcont (x : Fin D.nArc) : (eventFin q).symm (D.continuation x) =
      polygonEventSuccessor q hq.g2 ((eventFin q).symm x) := by
    change (eventFin q).symm ((polygonEventDiagram q hq).continuation x) = _
    obtain ⟨z,rfl⟩ := (eventFin q).surjective x
    rw [polygonEventDiagram_continuation, (eventFin q).symm_apply_apply]
    exact congrArg (polygonEventSuccessor q hq.g2) ((eventFin q).symm_apply_apply z).symm
  have he := next_conjugacy D.continuation (polygonEventSuccessor q hq.g2)
    (eventFin q).symm hcont (D.continuation ∘ mark) (D.continuation.injective.comp hi)
  have hm : (eventFin q).symm ∘ (D.continuation ∘ mark) =
        (fun m : κ × Fin 2 => visit q (u m.1) m.2) := by
    funext m
    change (eventFin q).symm (D.continuation (D.incoming ((u.trans (crossingFin q)) m.1) m.2)) = _
    rw [D.continuation_crossing]
    simp only [D, positivePolygonEventDiagram, positiveDiagram, polygonEventDiagram,
      outgoingIndex, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.refl_apply]
  apply (hs.trans he).trans
  congr 1
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
