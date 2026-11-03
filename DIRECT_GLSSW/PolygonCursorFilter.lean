import FutureCursorParameter
import PositivePolygonInitialEncounter
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open PolygonDrawing EventSegmentGeometry
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

theorem incoming_terminal_parameter (c : PolygonCrossing q) (i : Fin 2) :
    polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three (incoming q hq c i) =
      polygonEventParameter q (visit q c i) := by
  unfold polygonEventSuccessorTerminalParameter
  rw [incoming_successor,if_pos (incoming_edge q hq c i).symm]

/-- The actual successor gap determines the carrier/parameter suffix filter. -/
theorem incoming_cursor_filter (c d : PolygonCrossing q) (i j : Fin 2) (θ : ℝ)
    (hlo : polygonEventParameter q (incoming q hq c i) < θ)
    (hhi : θ < polygonEventParameter q (visit q c i)) :
    letI := polygonEventOrder q hq.g2
    incoming q hq c i ≤ incoming q hq d j ↔
      polygonEventEdge q (visit q c i) < polygonEventEdge q (visit q d j) ∨
      (polygonEventEdge q (visit q c i) = polygonEventEdge q (visit q d j) ∧
        θ < polygonEventParameter q (visit q d j)) := by
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
  have hcx := polygonEventSuccessorTerminalParameter_bounds q hq.g2 hq.size_ge_three (incoming q hq c i)
  have hdx := polygonEventSuccessorTerminalParameter_bounds q hq.g2 hq.size_ge_three (incoming q hq d j)
  rw [incoming_terminal_parameter] at hcx hdx
  constructor
  · intro hle
    rcases lt_or_eq_of_le hle with hlt|heq
    · rcases (polygonEvent_lt_iff q hq.g2 _ _).mp hlt with he|⟨he,hp⟩
      · exact Or.inl (by simpa only [incoming_edge] using he)
      · right
        refine ⟨by simpa only [incoming_edge] using he,?_⟩
        have hn := no_event_in_subarc q hq (incoming q hq c i) (incoming q hq d j) he.symm hp
        rw [incoming_terminal_parameter] at hn
        exact lt_trans hhi (lt_of_le_of_lt (le_of_not_gt hn) hdx.1)
    · have hv : visit q c i = visit q d j := by
        simpa only [incoming_successor] using congrArg (polygonEventSuccessor q hq.g2) heq
      exact Or.inr ⟨congrArg (polygonEventEdge q) hv,hv ▸ hhi⟩
  · rintro (he|⟨he,hθ⟩)
    · apply le_of_lt
      apply (polygonEvent_lt_iff q hq.g2 _ _).mpr
      exact Or.inl (by simpa only [incoming_edge] using he)
    · apply le_of_not_gt
      intro hlt
      have he' : polygonEventEdge q (incoming q hq d j) = polygonEventEdge q (incoming q hq c i) := by
        simpa only [incoming_edge] using he.symm
      have hp := (polygonEvent_sameEdge_lt_iff q hq.g2 _ _ he').mp hlt
      have hn := no_event_in_subarc q hq (incoming q hq d j) (incoming q hq c i) he'.symm hp
      rw [incoming_terminal_parameter] at hn
      exact hn (lt_trans hlo hθ)

end DirectGLSSW.HOMFLY.PolygonDrawingBridge

namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open PolygonDrawing
attribute [local instance] Classical.propDecidable

theorem initial_incoming_cursor_filter {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (c d : PolygonCrossing q) (i j : Fin 2) (θ : ℝ)
    (hlo : polygonEventParameter q (incoming q hq c i) < θ)
    (hhi : θ < polygonEventParameter q (visit q c i)) :
    visitPosition (initialAnchorTraversal q hq) ((positivePolygonEventDiagram q hq).incoming (crossingFin q c) i) ≤
      visitPosition (initialAnchorTraversal q hq) ((positivePolygonEventDiagram q hq).incoming (crossingFin q d) j) ↔
      polygonEventEdge q (visit q c i) < polygonEventEdge q (visit q d j) ∨
      (polygonEventEdge q (visit q c i) = polygonEventEdge q (visit q d j) ∧
        θ < polygonEventParameter q (visit q d j)) := by
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
  have hin (c : PolygonCrossing q) (i : Fin 2) :
      (positivePolygonEventDiagram q hq).incoming (crossingFin q c) i = eventFin q (incoming q hq c i) := by
    simp only [positivePolygonEventDiagram,positiveDiagram,polygonEventDiagram,incomingIndex,Equiv.symm_apply_apply]
  rw [hin,hin,initialAnchorTraversal_visitPosition,initialAnchorTraversal_visitPosition]
  change ((polygonEventEnumeration q hq.g2).symm (incoming q hq c i) ≤
    (polygonEventEnumeration q hq.g2).symm (incoming q hq d j)) ↔ _
  rw [OrderIso.le_iff_le]
  exact incoming_cursor_filter q hq c d i j θ hlo hhi
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
