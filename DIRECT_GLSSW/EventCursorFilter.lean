import PolygonCursorFilter
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open PolygonDrawing EventSegmentGeometry
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

/-- An arbitrary original event bounds the actual future incoming ports.
The cursor may equal this event's source parameter. -/
theorem event_cursor_filter (x : PolygonEvent q) (d : PolygonCrossing q) (j : Fin 2) (θ : ℝ)
    (hlo : polygonEventParameter q x ≤ θ)
    (hhi : θ < polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three x) :
    letI := polygonEventOrder q hq.g2
    x ≤ incoming q hq d j ↔
      polygonEventEdge q x < polygonEventEdge q (visit q d j) ∨
      (polygonEventEdge q x = polygonEventEdge q (visit q d j) ∧
        θ < polygonEventParameter q (visit q d j)) := by
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
  have hdx := polygonEventSuccessorTerminalParameter_bounds q hq.g2 hq.size_ge_three (incoming q hq d j)
  rw [incoming_terminal_parameter] at hdx
  constructor
  · intro hle
    rcases lt_or_eq_of_le hle with hlt|heq
    · rcases (polygonEvent_lt_iff q hq.g2 _ _).mp hlt with he|⟨he,hp⟩
      · exact Or.inl (by simpa only [incoming_edge] using he)
      · right
        refine ⟨by simpa only [incoming_edge] using he,?_⟩
        have hn := no_event_in_subarc q hq x (incoming q hq d j) he.symm hp
        exact lt_trans hhi (lt_of_le_of_lt (le_of_not_gt hn) hdx.1)
    · subst x
      exact Or.inr ⟨incoming_edge q hq d j,by simpa only [incoming_terminal_parameter] using hhi⟩
  · rintro (he|⟨he,hθ⟩)
    · apply le_of_lt
      apply (polygonEvent_lt_iff q hq.g2 _ _).mpr
      exact Or.inl (by simpa only [incoming_edge] using he)
    · apply le_of_not_gt
      intro hlt
      have he' : polygonEventEdge q (incoming q hq d j) = polygonEventEdge q x := by
        simpa only [incoming_edge] using he.symm
      have hp := (polygonEvent_sameEdge_lt_iff q hq.g2 _ _ he').mp hlt
      have hn := no_event_in_subarc q hq (incoming q hq d j) x he'.symm hp
      rw [incoming_terminal_parameter] at hn
      exact hn (lt_of_le_of_lt hlo hθ)

/-- The exact stored initial traversal realizes the arbitrary event filter. -/
theorem initial_event_cursor_filter (x : PolygonEvent q) (d : PolygonCrossing q) (j : Fin 2) (θ : ℝ)
    (hlo : polygonEventParameter q x ≤ θ)
    (hhi : θ < polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three x) :
    visitPosition (initialAnchorTraversal q hq) (eventFin q x) ≤
      visitPosition (initialAnchorTraversal q hq) ((positivePolygonEventDiagram q hq).incoming (crossingFin q d) j) ↔
      polygonEventEdge q x < polygonEventEdge q (visit q d j) ∨
      (polygonEventEdge q x = polygonEventEdge q (visit q d j) ∧ θ < polygonEventParameter q (visit q d j)) := by
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
  have hin : (positivePolygonEventDiagram q hq).incoming (crossingFin q d) j = eventFin q (incoming q hq d j) := by
    simp only [positivePolygonEventDiagram,positiveDiagram,polygonEventDiagram,incomingIndex,Equiv.symm_apply_apply]
  rw [hin,initialAnchorTraversal_visitPosition,initialAnchorTraversal_visitPosition]
  change ((polygonEventEnumeration q hq.g2).symm x ≤
    (polygonEventEnumeration q hq.g2).symm (incoming q hq d j)) ↔ _
  rw [OrderIso.le_iff_le]
  exact event_cursor_filter q hq x d j θ hlo hhi



end DirectGLSSW.HOMFLY.PolygonDrawingBridge
