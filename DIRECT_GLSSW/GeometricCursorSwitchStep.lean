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

/-- Append the literal canonical switch to the actual history. -/
def switchedTrace {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) (hg : MarkedG.GoodBefore t c) :
    MarkedParentTrace s (MarkedG.switchedState t c hc hg) :=
  MarkedPolynomial.append h (.cons (.switched t.2.2 c hc hg) (.nil _))

theorem switchedTrace_arcOrigin {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) (hg : MarkedG.GoodBefore t c)
    (e : Fin t.1.nArc) : (switchedTrace h c hc hg).arcOrigin e=h.arcOrigin e := by
  rw [switchedTrace,PhysicalParentHistory.arcOrigin_append]
  rfl

/-- The literal canonical switched history has a full geometric cursor after
a sufficiently small move past the actual first physical under crossing. -/
theorem exists_switched_cursor_radius {n m : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) (p : Fin (m+2) → PlanarPoint ℝ)
    (t : MarkedParentState)
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (C : GeometricCursor q hq p t h) (hR : ActiveArc.Regular p)
    (c : ActiveArc.Crossing p) (hc : ActiveArc.Cursor.FirstCrossing p c)
    (hb : badAt t.2.1 ((C.crossingEquiv he) c).val)
    (hg : MarkedG.GoodBefore t ((C.crossingEquiv he) c).val) :
    ∃ R : ℝ, 0<R ∧ ∀ ε : ℝ, 0<ε → ε<R →
      ActiveArc.leftParameter p c+ε<ActiveArc.Cursor.afterBound p c →
      Nonempty (GeometricCursor q hq
        (ActiveArc.Cursor.moveStart p (ActiveArc.leftParameter p c+ε))
        (MarkedG.switchedState t ((C.crossingEquiv he) c).val hb hg)
        (switchedTrace h ((C.crossingEquiv he) c).val hb hg)) := by
  letI : LinearOrder (Fin (n+2) ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
  rcases C with ⟨a,B,A,hs,θ,hθ0,hθ1,hcarrier,hlo,hhi,rfl⟩
  let s := positivePolygonMarkedState q hq (initialAnchorTraversal q hq)
  let P := ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) A m hs) θ
  let F := boundaryPhysicalCrossingEquiv q hq he h a B A m hs θ hcarrier hlo hhi
  change badAt t.2.1 (F c).val at hb
  change MarkedG.GoodBefore t (F c).val at hg
  let selected := (F c).val
  let u := MarkedG.switchedState t selected hb hg
  let H := switchedTrace h selected hb hg
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
  have hbad : ∀ d : Fin t.1.nCrossing,badAt u.2.1 d → ∀ i : Fin 2,
      visitPosition s.2.1 E≤visitPosition s.2.1 (s.1.incoming (h.crossingOrigin d) i) := by
    intro d hdu
    have hdne : d≠selected := by
      intro heq
      subst d
      exact (badAt_switch_toggle t.2.1 selected).mp hdu hb
    have hd : badAt t.2.1 d := (badAt_switch_same t.2.1 selected d hdne).mp hdu
    let d' : SuffixCrossing t a := ⟨d,B.badAfter d hd⟩
    let z : ActiveArc.Crossing P := F.symm d'
    let z0 := (ActiveArc.Split.suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq)
      A m hs θ hθ0 hθ1 z).val
    have hz : (F z).val=d := congrArg Subtype.val (F.apply_symm_apply d')
    have hne : z≠c := by
      intro hzc
      rw [hzc] at hz
      exact hdne hz.symm
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
  obtain ⟨a',ha',hle⟩ := h.exists_boundary_arc_of_original a B E hE
  have hoff := h.boundary_position_offset a B a' E hle ha'
  change visitPosition t.2.1 a'+visitPosition s.2.1 (h.boundaryOrigin a B)=visitPosition t.2.1 a+visitPosition s.2.1 E at hoff
  have hselorigin : h.crossingOrigin selected=crossingFin q (exposedCrossingEquiv q 0 hq he zc) :=
    boundaryPhysicalCrossingEquiv_origin q hq he h a B A m hs θ hcarrier hlo hhi c
  have hbranch : firstVisitedBranch t.2.1 selected=0 := history_selected_branch_zero q hq h selected hb
  have hselbefore : visitPosition t.2.1 (t.1.incoming selected (firstVisitedBranch t.2.1 selected))<
      visitPosition t.2.1 a' := by
    rw [hbranch]
    have hseloffset := h.boundary_position_offset a B (t.1.incoming selected 0)
      (s.1.incoming (h.crossingOrigin selected) 0) ((F c).property 0) (h.crossingOrigin_incoming selected 0)
    have hlt : visitPosition s.2.1 (s.1.incoming (h.crossingOrigin selected) 0)<visitPosition s.2.1 E := by
      change visitPosition (initialAnchorTraversal q hq)
        ((positivePolygonEventDiagram q hq).incoming (h.crossingOrigin selected) 0)<_
      rw [hselorigin]
      have hin : (positivePolygonEventDiagram q hq).incoming
          (crossingFin q (exposedCrossingEquiv q 0 hq he zc)) 0=
          eventFin q (incoming q hq (exposedCrossingEquiv q 0 hq he zc) 0) := by
        simp only [positivePolygonEventDiagram,positiveDiagram,polygonEventDiagram,incomingIndex,Equiv.symm_apply_apply]
      rw [hin]
      change visitPosition (initialAnchorTraversal q hq) _<visitPosition (initialAnchorTraversal q hq) (eventFin q x)
      rw [initialAnchorTraversal_visitPosition,initialAnchorTraversal_visitPosition]
      apply (polygonEventEnumeration q hq.g2).symm.strictMono
      apply (polygonEvent_lt_iff q hq.g2 _ _).mpr
      right
      refine ⟨incoming_edge q hq _ 0,?_⟩
      have hh := (polygonEventSuccessorTerminalParameter_bounds q hq.g2 hq.size_ge_three
        (incoming q hq (exposedCrossingEquiv q 0 hq he zc) 0)).1
      rw [incoming_terminal_parameter] at hh
      exact hh
    change visitPosition t.2.1 (t.1.incoming selected 0)+visitPosition s.2.1 (h.boundaryOrigin a B)=
      visitPosition t.2.1 a+visitPosition s.2.1 (s.1.incoming (h.crossingOrigin selected) 0) at hseloffset
    omega
  have B' : CursorBoundary u (visitPosition u.2.1 a') := by
    refine ⟨le_of_lt (visitPosition_lt_nArc u _),?_,?_⟩
    · intro e he
      change e∈insert (t.1.incoming selected (firstVisitedBranch t.2.1 selected)) t.2.2.marks at he
      rcases Finset.mem_insert.mp he with rfl|he
      · exact hselbefore
      · exact lt_of_lt_of_le (B.marksBefore e he) hle
    · intro d hd i
      have hdne : d≠selected := by
        intro heq;subst d
        exact (badAt_switch_toggle t.2.1 selected).mp hd hb
      have hdold : badAt t.2.1 d := (badAt_switch_same t.2.1 selected d hdne).mp hd
      have hpos := h.boundary_position_offset a B (t.1.incoming d i)
        (s.1.incoming (h.crossingOrigin d) i) (B.badAfter d hdold i) (h.crossingOrigin_incoming d i)
      have hh := hbad d hd i
      change visitPosition t.2.1 (t.1.incoming d i)+visitPosition s.2.1 (h.boundaryOrigin a B)=
        visitPosition t.2.1 a+visitPosition s.2.1 (s.1.incoming (h.crossingOrigin d) i) at hpos
      change visitPosition t.2.1 a'≤visitPosition t.2.1 (t.1.incoming d i)
      omega
  have hOrigin : H.boundaryOrigin a' B'=E := by
    have hh := H.boundaryOrigin_spec a' B'
    rw [switchedTrace_arcOrigin] at hh
    exact Option.some.inj (hh.symm.trans ha')
  have ho : originalEvent q hq H a' B'=x := by
    unfold originalEvent
    rw [hOrigin]
    exact (eventFin q).symm_apply_apply _
  change Nonempty (GeometricCursor q hq (ActiveArc.Cursor.moveStart P τ) u H)
  refine ⟨⟨a',B',A,hs,θ',hθ'0,hθ'1,?_,?_,?_,?_⟩⟩
  · rw [ho];exact hx.1
  · rw [ho];exact hθ'lo
  · rw [ho];exact hθ'hi
  · exact ActiveArc.Cursor.moveStart_moveStart (ActiveArc.Split.suffixWord (cutArc q 0) A m hs) θ τ
end DirectGLSSW.HOMFLY.PhysicalCursorComparison
