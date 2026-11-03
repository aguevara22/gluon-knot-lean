import PhysicalCursorEvent
import GeometricCursorCrossingEquiv
import BoundaryPositionProgress
import CursorAffineStep
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open PermutationOrbits PolygonDrawingBridge PolygonDrawing SmoothingCornerGeometry EventSegmentGeometry
open ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable
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

/-- A physically first crossing which is good in the actual marked state admits
an original-event radius preserving every geometric cursor field. -/
theorem exists_good_cursor_radius {n m : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) (p : Fin (m+2) → PlanarPoint ℝ)
    (t : MarkedParentState)
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (C : GeometricCursor q hq p t h) (hR : ActiveArc.Regular p)
    (c : ActiveArc.Crossing p) (hc : ActiveArc.Cursor.FirstCrossing p c)
    (hgood : ¬badAt t.2.1 ((C.crossingEquiv he) c).val) :
    ∃ R : ℝ, 0<R ∧ ∀ ε : ℝ, 0<ε → ε<R →
      ActiveArc.leftParameter p c+ε<ActiveArc.Cursor.afterBound p c →
      Nonempty (GeometricCursor q hq
        (ActiveArc.Cursor.moveStart p (ActiveArc.leftParameter p c+ε)) t h) := by
  letI : LinearOrder (Fin (n+2) ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
  rcases C with ⟨a,B,A,hs,θ,hθ0,hθ1,hcarrier,hlo,hhi,rfl⟩
  let s := positivePolygonMarkedState q hq (initialAnchorTraversal q hq)
  let P := ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) A m hs) θ
  let F := boundaryPhysicalCrossingEquiv q hq he h a B A m hs θ hcarrier hlo hhi
  change ¬badAt t.2.1 (F c).val at hgood
  let zc := (ActiveArc.Split.suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq)
    A m hs θ hθ0 hθ1 c).val
  let x := visit q (exposedCrossingEquiv q 0 hq he zc) 0
  have hx := physical_first_original_event q hq he A hs θ hθ0 hθ1 c hc.1
  change (polygonEventEdge q x).val=A+1 ∧
    polygonEventParameter q x=θ+(1-θ)*ActiveArc.leftParameter P c at hx
  let η := polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three x
  have hgap : θ+(1-θ)*ActiveArc.leftParameter P c<η := by
    rw [← hx.2]
    exact (polygonEventSuccessorTerminalParameter_bounds q hq.g2 hq.size_ge_three x).1
  obtain ⟨R,hRpos,HR⟩ := ActiveArc.Cursor.exists_original_event_radius θ (ActiveArc.leftParameter P c) η hθ1 hgap
  refine ⟨R,hRpos,?_⟩
  intro ε hε hεR hτb
  let τ := ActiveArc.leftParameter P c+ε
  let θ' := θ+(1-θ)*τ
  have hτc : ActiveArc.leftParameter P c<τ := lt_add_of_pos_right _ hε
  have hθ'lo : polygonEventParameter q x≤θ' := by
    rw [hx.2]
    exact (HR ε hε hεR).1.le
  have hθ'hi : θ'<η := (HR ε hε hεR).2
  have hθ'0 : 0≤θ' := le_trans (polygonEventParameter_bounds q x).1 hθ'lo
  have hθ'1 : θ'<1 := lt_of_lt_of_le hθ'hi
    (polygonEventSuccessorTerminalParameter_bounds q hq.g2 hq.size_ge_three x).2
  let E := eventFin q x
  have hE : visitPosition s.2.1 (h.boundaryOrigin a B)≤visitPosition s.2.1 E := by
    have heq : polygonEventEdge q ((eventFin q).symm (h.boundaryOrigin a B))=polygonEventEdge q x := by
      apply Fin.ext
      exact hcarrier.trans hx.1.symm
    have hp : polygonEventParameter q ((eventFin q).symm (h.boundaryOrigin a B))<polygonEventParameter q x := by
      rw [hx.2]
      have hσ := (ActiveArc.leftParameter_spec P c).1
      have hpos : 0<(1-θ)*ActiveArc.leftParameter P c := mul_pos (sub_pos.mpr hθ1) hσ
      exact lt_of_le_of_lt hlo (lt_add_of_pos_right _ hpos)
    have hle : (eventFin q).symm (h.boundaryOrigin a B)≤x :=
      le_of_lt ((polygonEvent_lt_iff q hq.g2 _ _).mpr (Or.inr ⟨heq,hp⟩))
    have hid : eventFin q ((eventFin q).symm (h.boundaryOrigin a B))=h.boundaryOrigin a B :=
      (eventFin q).apply_symm_apply _
    change visitPosition (initialAnchorTraversal q hq) _≤visitPosition (initialAnchorTraversal q hq) _
    rw [← hid,initialAnchorTraversal_visitPosition,initialAnchorTraversal_visitPosition]
    exact (polygonEventEnumeration q hq.g2).symm.monotone hle
  have hbad : ∀ d : Fin t.1.nCrossing,badAt t.2.1 d → ∀ i : Fin 2,
      visitPosition s.2.1 E≤visitPosition s.2.1 (s.1.incoming (h.crossingOrigin d) i) := by
    intro d hd
    let d' : SuffixCrossing t a := ⟨d,B.badAfter d hd⟩
    let z : ActiveArc.Crossing P := F.symm d'
    let z0 := (ActiveArc.Split.suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq)
      A m hs θ hθ0 hθ1 z).val
    have hz : (F z).val=d := congrArg Subtype.val (F.apply_symm_apply d')
    have hne : z≠c := by
      intro hzc
      rw [hzc] at hz
      exact hgood (hz ▸ hd)
    have horigin : h.crossingOrigin d=crossingFin q (exposedCrossingEquiv q 0 hq he z0) := by
      have hh := boundaryPhysicalCrossingEquiv_origin q hq he h a B A m hs θ hcarrier hlo hhi z
      change h.crossingOrigin (F z).val=_ at hh
      rw [hz] at hh
      exact hh
    have hfilter : A≤z0.val.1.val ∧ (z0.val.1.val=A → θ'<ActiveArc.leftParameter (cutArc q 0) z0) := by
      constructor
      · exact (ActiveArc.Split.suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq)
          A m hs θ hθ0 hθ1 z).property.1
      · intro hz0
        have hlabel := ActiveArc.Split.suffixWordCrossingEquiv_left_label
          (cutArc q 0) (cutArc_regular q 0 hq) A m hs θ hθ0 hθ1 z
        change z0.val.1.val=A+z.val.1.val at hlabel
        have hzfirst : z.val.1=0 := by
          apply Fin.ext
          change z.val.1.val=0
          omega
        have hsurv := (ActiveArc.Cursor.survives_after_first_iff P hR c hc τ hτc hτb z).mpr hne
        have hlocal := hsurv hzfirst
        have hp := suffixWordCrossingEquiv_leftParameter q (cutArc_regular q 0 hq)
          A m hs θ hθ0 hθ1 z hzfirst
        change ActiveArc.leftParameter (cutArc q 0) z0=θ+(1-θ)*ActiveArc.leftParameter P z at hp
        rw [hp]
        exact add_lt_add_left (mul_lt_mul_of_pos_left hlocal (sub_pos.mpr hθ1)) θ
    have H := (original_event_physical_filter q hq he x A θ' hx.1 hθ'lo hθ'hi z0).mp hfilter
    intro i
    change visitPosition (initialAnchorTraversal q hq) E≤
      visitPosition (initialAnchorTraversal q hq) ((positivePolygonEventDiagram q hq).incoming (h.crossingOrigin d) i)
    rw [horigin]
    exact H i
  obtain ⟨a',B',hOrigin⟩ := boundary_at_original h a B E hE hbad
  have ho : originalEvent q hq h a' B'=x := by
    unfold originalEvent
    rw [hOrigin]
    exact (eventFin q).symm_apply_apply _
  refine ⟨⟨a',B',A,hs,θ',hθ'0,hθ'1,?_,?_,?_,?_⟩⟩
  · rw [ho];exact hx.1
  · rw [ho];exact hθ'lo
  · rw [ho];exact hθ'hi
  · exact ActiveArc.Cursor.moveStart_moveStart (ActiveArc.Split.suffixWord (cutArc q 0) A m hs) θ τ
end DirectGLSSW.HOMFLY.PhysicalCursorComparison
