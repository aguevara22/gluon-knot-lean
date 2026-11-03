import GeometricCursorBoundary
import BoundaryPositionProgress
import BoundaryPhysicalCrossingEquiv
import PhysicalSuffixCrossingData
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open PermutationOrbits PolygonDrawingBridge PolygonDrawing SmoothingCornerGeometry EventSegmentGeometry
open ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable

private theorem anchor_le_event {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (x : PolygonEvent q) (hx : e.val≤(polygonEventEdge q x).val) :
    letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
    letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
    (Sum.inl e : PolygonEvent q) ≤ x := by
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
  apply le_of_not_gt
  intro hh
  rcases (polygonEvent_lt_iff q hq.g2 _ _).mp hh with he|⟨_,hp⟩
  · change (polygonEventEdge q x).val<e.val at he
    omega
  · change polygonEventParameter q x<0 at hp
    exact (not_lt_of_ge (polygonEventParameter_bounds q x).1) hp

private theorem moveStart_zero_word {m : ℕ} (p : Fin (m+2) → PlanarPoint ℝ) :
    ActiveArc.Cursor.moveStart p 0=p := by
  funext i
  by_cases hi : i=0
  · subst i
    rw [ActiveArc.Cursor.moveStart_zero]
    ext <;> simp only [affinePoint,zero_mul,add_zero]
  · simp only [ActiveArc.Cursor.moveStart,Function.update_of_ne hi]

private theorem corner_word {n b : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (A : ℕ) (hs : A+(1+b)=n) (θ : ℝ) :
    ActiveArc.Split.suffix (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord q A (1+b) hs) θ) =
      ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord q (A+1) b (by omega)) 0 := by
  rw [moveStart_zero_word]
  funext i
  have hi : ActiveArc.Split.vertex (a:=1) (b:=b) i ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    change 1+i.val=0 at hv
    omega
  change ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord q A (1+b) hs) θ
    (ActiveArc.Split.vertex (a:=1) (b:=b) i) = _
  rw [ActiveArc.Cursor.moveStart,Function.update_of_ne hi,
    ActiveArc.Split.suffixWord_vertex,ActiveArc.Split.suffixWord_vertex]
  congr 1
  apply Fin.ext
  change A+(1+i.val)=A+1+i.val
  omega

private theorem boundary_at_original {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (a : Fin t.1.nArc) (B : CursorBoundary t (visitPosition t.2.1 a))
    (E : Fin s.1.nArc)
    (hE : visitPosition s.2.1 (h.boundaryOrigin a B)≤visitPosition s.2.1 E)
    (hbad : ∀ d : Fin t.1.nCrossing,badAt t.2.1 d → ∀ i : Fin 2,
      visitPosition s.2.1 E≤visitPosition s.2.1 (s.1.incoming (h.crossingOrigin d) i)) :
    ∃ e : Fin t.1.nArc, ∃ B' : CursorBoundary t (visitPosition t.2.1 e),
      h.boundaryOrigin e B'=E := by
  obtain ⟨e,he,hle⟩ := h.exists_boundary_arc_of_original a B E hE
  have hoff := h.boundary_position_offset a B e E hle he
  have B' : CursorBoundary t (visitPosition t.2.1 e) := by
    refine ⟨le_of_lt (visitPosition_lt_nArc t e),?_,?_⟩
    · intro x hx
      exact lt_of_lt_of_le (B.marksBefore x hx) hle
    · intro d hd i
      have hpos := h.boundary_position_offset a B (t.1.incoming d i)
        (s.1.incoming (h.crossingOrigin d) i) (B.badAfter d hd i) (h.crossingOrigin_incoming d i)
      have hh := hbad d hd i
      omega
  refine ⟨e,B',?_⟩
  exact Option.some.inj ((h.boundaryOrigin_spec e B').symm.trans he)

/-- A genuine crossing-free physical corner advances the full geometric cursor,
keeping the actual marked state, original root and framing. -/
theorem exists_corner_cursor {n b : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (he : LeftExposed q 0)
    (p : Fin (1+b+2) → PlanarPoint ℝ) (t : MarkedParentState)
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (C : GeometricCursor q hq p t h)
    (hfree : ∀ d : ActiveArc.Crossing p,d.val.1≠0) :
    Nonempty (GeometricCursor q hq (ActiveArc.Split.suffix p) t h) := by
  letI : LinearOrder (Fin (n+2) ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
  rcases C with ⟨a,B,A,hs,θ,hθ0,hθ1,hcarrier,hlo,hhi,rfl⟩
  let s := positivePolygonMarkedState q hq (initialAnchorTraversal q hq)
  let next : Fin (n+2) := ⟨A+2,by omega⟩
  let E := eventFin q (Sum.inl next)
  let P := ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) A (1+b) hs) θ
  let F := boundaryPhysicalCrossingEquiv q hq he h a B A (1+b) hs θ hcarrier hlo hhi
  have hE : visitPosition s.2.1 (h.boundaryOrigin a B)≤visitPosition s.2.1 E := by
    letI := polygonEventOrder q hq.g2
    have hx : (eventFin q).symm (h.boundaryOrigin a B) < (Sum.inl next : PolygonEvent q) := by
      apply (polygonEvent_lt_iff q hq.g2 _ _).mpr
      left
      change (polygonEventEdge q ((eventFin q).symm (h.boundaryOrigin a B))).val<A+2
      change (polygonEventEdge q ((eventFin q).symm (h.boundaryOrigin a B))).val=A+1 at hcarrier
      omega
    have hz := (polygonEventEnumeration q hq.g2).symm.monotone (le_of_lt hx)
    have hid : eventFin q ((eventFin q).symm (h.boundaryOrigin a B))=h.boundaryOrigin a B :=
      (eventFin q).apply_symm_apply _
    change visitPosition (initialAnchorTraversal q hq) _ ≤ visitPosition (initialAnchorTraversal q hq) _
    rw [← hid,initialAnchorTraversal_visitPosition,initialAnchorTraversal_visitPosition]
    exact hz
  have hbad : ∀ d : Fin t.1.nCrossing,badAt t.2.1 d → ∀ i : Fin 2,
      visitPosition s.2.1 E≤visitPosition s.2.1 (s.1.incoming (h.crossingOrigin d) i) := by
    intro d hd i
    let d' : SuffixCrossing t a := ⟨d,B.badAfter d hd⟩
    let z : ActiveArc.Crossing P := F.symm d'
    let z0 := (ActiveArc.Split.suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq)
      A (1+b) hs θ hθ0 hθ1 z).val
    have horigin : h.crossingOrigin d=crossingFin q (exposedCrossingEquiv q 0 hq he z0) := by
      have hh := boundaryPhysicalCrossingEquiv_origin q hq he h a B A (1+b) hs θ hcarrier hlo hhi z
      have hz : (F z).val=d := congrArg Subtype.val (F.apply_symm_apply d')
      change h.crossingOrigin (F z).val=_ at hh
      rw [hz] at hh
      exact hh
    have hzpos : 0<z.val.1.val := by
      have hn := hfree z
      have hh : z.val.1.val≠0 := fun heq => hn (Fin.ext heq)
      omega
    have hlow : A+2≤(exposedCrossingEquiv q 0 hq he z0).val.1.val := by
      rw [exposedCrossing_firstEdge]
      have hh := ActiveArc.Split.suffixWordCrossingEquiv_left_label
        (cutArc q 0) (cutArc_regular q 0 hq) A (1+b) hs θ hθ0 hθ1 z
      change z0.val.1.val=A+z.val.1.val at hh
      omega
    have hedge : next.val≤(polygonEventEdge q (incoming q hq
        (exposedCrossingEquiv q 0 hq he z0) i)).val := by
      rw [incoming_edge]
      fin_cases i
      · exact hlow
      · have hh := (exposedCrossingEquiv q 0 hq he z0).property.1
        change (exposedCrossingEquiv q 0 hq he z0).val.1.val<
          (exposedCrossingEquiv q 0 hq he z0).val.2.val at hh
        change A+2≤(exposedCrossingEquiv q 0 hq he z0).val.2.val
        omega
    change visitPosition (initialAnchorTraversal q hq) E≤
      visitPosition (initialAnchorTraversal q hq) ((positivePolygonEventDiagram q hq).incoming (h.crossingOrigin d) i)
    rw [horigin]
    have hin : (positivePolygonEventDiagram q hq).incoming
        (crossingFin q (exposedCrossingEquiv q 0 hq he z0)) i =
        eventFin q (incoming q hq (exposedCrossingEquiv q 0 hq he z0) i) := by
      simp only [positivePolygonEventDiagram,positiveDiagram,polygonEventDiagram,incomingIndex,Equiv.symm_apply_apply]
    rw [hin]
    change visitPosition (initialAnchorTraversal q hq) (eventFin q (Sum.inl next))≤_
    rw [initialAnchorTraversal_visitPosition,initialAnchorTraversal_visitPosition]
    exact (polygonEventEnumeration q hq.g2).symm.monotone (anchor_le_event q hq next _ hedge)
  obtain ⟨a',B',hOrigin⟩ := boundary_at_original h a B E hE hbad
  have ho : originalEvent q hq h a' B'=Sum.inl next := by
    unfold originalEvent
    rw [hOrigin]
    exact (eventFin q).symm_apply_apply _
  refine ⟨⟨a',B',A+1,by omega,0,le_refl _,by norm_num,?_,?_,?_,?_⟩⟩
  · rw [ho];rfl
  · rw [ho];exact le_refl _
  · rw [ho]
    exact (polygonEventSuccessorTerminalParameter_bounds q hq.g2 hq.size_ge_three (Sum.inl next)).1
  · exact corner_word (cutArc q 0) A hs θ
end DirectGLSSW.HOMFLY.PhysicalCursorComparison
