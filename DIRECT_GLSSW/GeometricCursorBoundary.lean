import BoundaryEventAdvance
import BoundaryOriginalTail
import HistoryPhysicalCrossingEquiv
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY
/-- The complete old tail advances with the same trace across either of the
preceding geometric event cases; its origin is exactly the original successor. -/
theorem MarkedParentTrace.boundaryOrigin_advance {s t : MarkedParentState}
    (h : MarkedParentTrace s t) (a : Fin t.1.nArc)
    (B : CursorBoundary t (visitPosition t.2.1 a))
    (B' : CursorBoundary t (visitPosition t.2.1 (t.1.continuation a))) :
    h.boundaryOrigin (t.1.continuation a) B'=s.1.continuation (h.boundaryOrigin a B) := by
  exact (h.arcOrigin_continuation a (t.1.continuation a) _ _ rfl
    (h.boundaryOrigin_spec a B) (h.boundaryOrigin_spec (t.1.continuation a) B')).symm
end DirectGLSSW.HOMFLY
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open PermutationOrbits PolygonDrawingBridge PolygonDrawing SmoothingCornerGeometry EventSegmentGeometry
open ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable

/-- The original event carrying an arbitrary actual cursor boundary. -/
def originalEvent {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (a : Fin t.1.nArc) (B : CursorBoundary t (visitPosition t.2.1 a)) : PolygonEvent q :=
  (eventFin q).symm (h.boundaryOrigin a B)

/-- Literal geometric comparison state: the actual marked history, a boundary
in its stored-root order, and the original suffix with a cursor in the original
event interval. The source endpoint is permitted, including after a smoothed
connector. No framed value equation or desired transition is stored. -/
structure GeometricCursor {n m : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (p : Fin (m+2) → PlanarPoint ℝ) (t : MarkedParentState)
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t) where
  boundaryArc : Fin t.1.nArc
  boundary : CursorBoundary t (visitPosition t.2.1 boundaryArc)
  offset : ℕ
  size : offset+m=n
  parameter : ℝ
  nonnegative : 0≤parameter
  beforeEnd : parameter<1
  carrier : (polygonEventEdge q (originalEvent q hq h boundaryArc boundary)).val=offset+1
  afterSource : polygonEventParameter q (originalEvent q hq h boundaryArc boundary)≤parameter
  beforeTarget : parameter<polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three
    (originalEvent q hq h boundaryArc boundary)
  word : p=ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) offset m size) parameter

/-- The stored physical head is exactly the point on the original carrier
at the stored parameter; it need not lie inside a beveled descendant arc. -/
theorem GeometricCursor.cursor_point {n m : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (p : Fin (m+2) → PlanarPoint ℝ) (t : MarkedParentState)
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (C : GeometricCursor q hq p t h) :
    p 0=affinePoint (q (polygonEventEdge q (originalEvent q hq h C.boundaryArc C.boundary)))
      (q (cyclicSuccessor (polygonEventEdge q (originalEvent q hq h C.boundaryArc C.boundary))))
      C.parameter := by
  have hp := congrFun C.word (0 : Fin (m+2))
  rw [ActiveArc.Cursor.moveStart_zero] at hp
  refine hp.trans ?_
  have hv0 : ActiveArc.Split.suffixWord (cutArc q 0) C.offset m C.size 0 =
      q (polygonEventEdge q (originalEvent q hq h C.boundaryArc C.boundary)) := by
    rw [ActiveArc.Split.suffixWord_vertex]
    unfold cutArc
    congr 1
    apply Fin.ext
    change (0+1+(C.offset+0))%(n+2)=_
    rw [C.carrier,Nat.mod_eq_of_lt (by have := C.size;omega)]
    omega
  have hv1 : ActiveArc.Split.suffixWord (cutArc q 0) C.offset m C.size 1 =
      q (cyclicSuccessor (polygonEventEdge q (originalEvent q hq h C.boundaryArc C.boundary))) := by
    rw [ActiveArc.Split.suffixWord_vertex]
    unfold cutArc
    congr 1
    apply Fin.ext
    change (0+1+(C.offset+1))%(n+2)=(_+1+0)%(n+2)
    rw [C.carrier]
    congr 1
    omega
  rw [hv0,hv1]

def openingArc {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    Fin (positivePolygonEventDiagram q hq).nArc := eventFin q (Sum.inl ⟨1,by omega⟩)

/-- The actual exposed opening starts at anchor one while the knot's stored
root remains anchor zero. No original crossing occurs on the removed edge. -/
theorem opening_boundary {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q 0) :
    CursorBoundary (positivePolygonMarkedState q hq (initialAnchorTraversal q hq))
      (visitPosition (initialAnchorTraversal q hq) (openingArc q hq)) := by
  let s := positivePolygonMarkedState q hq (initialAnchorTraversal q hq)
  refine ⟨le_of_lt (visitPosition_lt_nArc s _),?_,?_⟩
  · intro a ha
    exact (Finset.not_mem_empty a ha).elim
  · intro c hc i
    let d := (crossingFin q).symm c
    have hin : (positivePolygonEventDiagram q hq).incoming c i=eventFin q (incoming q hq d i) := by
      simp only [d,positivePolygonEventDiagram,positiveDiagram,polygonEventDiagram,incomingIndex]
    have hedge : 1≤(polygonEventEdge q (incoming q hq d i)).val := by
      rw [incoming_edge]
      have hzero : polygonEventEdge q (visit q d i) ≠ 0 := by
        fin_cases i
        · exact fun hh => leftExposed_no_incident_crossing q hq 0 he d (Or.inl hh)
        · exact fun hh => leftExposed_no_incident_crossing q hq 0 he d (Or.inr hh)
      have hv : (polygonEventEdge q (visit q d i)).val ≠ 0 := fun hh => hzero (Fin.ext hh)
      omega
    letI : LinearOrder (Fin (n+2) ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
    letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
    have hev : (Sum.inl ⟨1,by omega⟩ : PolygonEvent q) ≤ incoming q hq d i := by
      apply le_of_not_gt
      intro hh
      rcases (polygonEvent_lt_iff q hq.g2 _ _).mp hh with hl|⟨_,hp⟩
      · change (polygonEventEdge q (incoming q hq d i)).val<1 at hl
        omega
      · change polygonEventParameter q (incoming q hq d i)<0 at hp
        exact (not_lt_of_ge (polygonEventParameter_bounds q _).1) hp
    change visitPosition (initialAnchorTraversal q hq) (openingArc q hq) ≤
      visitPosition (initialAnchorTraversal q hq) ((positivePolygonEventDiagram q hq).incoming c i)
    rw [hin]
    unfold openingArc
    rw [initialAnchorTraversal_visitPosition,initialAnchorTraversal_visitPosition]
    exact (polygonEventEnumeration q hq.g2).symm.monotone hev

/-- Source initialization of the geometric cursor, with the original actual
marked state and original framing, at the literal exposed cut word. -/
def initial_cursor {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q 0) :
    GeometricCursor q hq (cutArc q 0)
      (positivePolygonMarkedState q hq (initialAnchorTraversal q hq))
      (.nil (positivePolygonMarkedState q hq (initialAnchorTraversal q hq))) := by
  let s := positivePolygonMarkedState q hq (initialAnchorTraversal q hq)
  let h : MarkedParentTrace s s := .nil s
  let B := opening_boundary q hq he
  have ho : originalEvent q hq h (openingArc q hq) B = Sum.inl ⟨1,by omega⟩ := by
    have hs := h.boundaryOrigin_spec (openingArc q hq) B
    have hh : h.boundaryOrigin (openingArc q hq) B=openingArc q hq :=
      (Option.some.inj hs).symm
    unfold originalEvent
    rw [hh]
    exact (eventFin q).symm_apply_apply _
  refine ⟨openingArc q hq,B,0,by omega,0,le_refl _,by norm_num,?_,?_,?_,?_⟩
  · rw [ho];rfl
  · rw [ho];exact le_refl _
  · rw [ho]
    exact (polygonEventSuccessorTerminalParameter_bounds q hq.g2 hq.size_ge_three
      (Sum.inl ⟨1,by omega⟩)).1
  · funext i
    rw [ActiveArc.Cursor.moveStart]
    by_cases hi : i=0
    · subst i
      simp only [Function.update_self,affinePoint,zero_mul,add_zero]
      rw [ActiveArc.Split.suffixWord_vertex]
      rfl
    · rw [Function.update_of_ne hi,ActiveArc.Split.suffixWord_vertex]
      congr 1
      apply Fin.ext
      simp only [Nat.zero_add]
end DirectGLSSW.HOMFLY.PhysicalCursorComparison
