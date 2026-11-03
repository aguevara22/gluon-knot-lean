import HistoryPhysicalCrossingEquiv
import ActiveArcFirstCrossing
import PolygonCursorFilter
import PolygonDrawingInteriors
import PhysicalSuffixCrossingData

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
noncomputable section

namespace DirectGLSSW.HOMFLY

open PolygonDrawingBridge PolygonDrawing SmoothingCornerGeometry EventSegmentGeometry
open ActiveArc.Cursor ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable

/-- The visit immediately following a cursor's incoming event is the first
same-edge visit after the cursor parameter. -/
theorem incoming_visit_first_after_cursor {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (c d : PolygonCrossing q) (i j : Fin 2) (θ : ℝ)
    (hlo : polygonEventParameter q (PolygonDrawing.incoming q hq c i) < θ)
    (hhi : θ < polygonEventParameter q (PolygonDrawing.visit q c i))
    (hedge : polygonEventEdge q (PolygonDrawing.visit q c i) =
      polygonEventEdge q (PolygonDrawing.visit q d j))
    (hθ : θ < polygonEventParameter q (PolygonDrawing.visit q d j)) :
    polygonEventParameter q (PolygonDrawing.visit q c i) ≤
      polygonEventParameter q (PolygonDrawing.visit q d j) := by
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  letI : LinearOrder (PolygonEvent q) := by
    change LinearOrder (Fin n ⊕ CrossingVisit q)
    exact polygonEventOrder q hq.g2
  let x := PolygonDrawing.incoming q hq c i
  let z := PolygonDrawing.incoming q hq d j
  have hle : x ≤ z := by
    apply (PolygonDrawingBridge.incoming_cursor_filter q hq c d i j θ hlo hhi).2
    exact Or.inr ⟨hedge, hθ⟩
  by_cases heq : x = z
  · have hv : PolygonDrawing.visit q c i = PolygonDrawing.visit q d j := by
      have hsucc := congrArg (polygonEventSuccessor q hq.g2) heq
      simpa only [x, z, PolygonDrawing.incoming_successor] using hsucc
    rw [hv]
  · have hlt : x < z := lt_of_le_of_ne hle heq
    have hxe : polygonEventEdge q x = polygonEventEdge q (PolygonDrawing.visit q c i) := by
      simp [x, PolygonDrawing.incoming_edge]
    have hze : polygonEventEdge q z = polygonEventEdge q (PolygonDrawing.visit q d j) := by
      simp [z, PolygonDrawing.incoming_edge]
    have he : polygonEventEdge q z = polygonEventEdge q x :=
      hze.trans (hedge.symm.trans hxe.symm)
    rcases (polygonEvent_lt_iff q hq.g2 x z).mp hlt with hstrict | ⟨_, hparam⟩
    · exact False.elim ((ne_of_lt hstrict) he.symm)
    · have hno := PolygonDrawing.no_event_in_subarc q hq x z he hparam
      rw [PolygonDrawingBridge.incoming_terminal_parameter] at hno
      have hzb := polygonEventSuccessorTerminalParameter_bounds q hq.g2 hq.size_ge_three z
      rw [PolygonDrawingBridge.incoming_terminal_parameter] at hzb
      exact le_trans (le_of_not_gt hno) (le_of_lt hzb.1)

/-- The lower visit of a cut-arc crossing is represented by its actual
original-polygon branch; the branch is derived from incident-edge transport. -/
theorem exposed_lower_visit_parameter {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (he : LeftExposed q 0)
    (z : ActiveArc.Crossing (ActiveArc.ExposedChart.cutArc q 0)) :
    ∃ j : Fin 2,
      polygonEventEdge q (PolygonDrawing.visit q (ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he z) j) =
        edgeLabel 0 (ActiveArc.visitEdge (ActiveArc.ExposedChart.cutArc q 0) (z,false)) ∧
      polygonEventParameter q (PolygonDrawing.visit q (ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he z) j) =
        ActiveArc.leftParameter (ActiveArc.ExposedChart.cutArc q 0) z := by
  let b := ActiveArc.ExposedChart.visitBoolEquiv q 0 hq he z false
  let j : Fin 2 := if b then 1 else 0
  refine ⟨j, ?_, ?_⟩
  · have hv : PolygonDrawing.visit q (ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he z) j =
        Sum.inr (ActiveArc.ExposedChart.visitEquiv q 0 hq he (z,false)) := by
      cases b <;> simp [j, b, PolygonDrawing.visit, ActiveArc.ExposedChart.visitEquiv,
        ActiveArc.ExposedChart.visitBoolEquiv]
    rw [hv]
    change crossingVisitEdge q (ActiveArc.ExposedChart.visitEquiv q 0 hq he (z,false)) = _
    rw [ActiveArc.ExposedChart.visitEquiv_edge]
  · have hv : PolygonDrawing.visit q (ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he z) j =
        Sum.inr (ActiveArc.ExposedChart.visitEquiv q 0 hq he (z,false)) := by
      cases b <;> simp [j, b, PolygonDrawing.visit, ActiveArc.ExposedChart.visitEquiv,
        ActiveArc.ExposedChart.visitBoolEquiv]
    rw [hv]
    change crossingVisitParameter q (ActiveArc.ExposedChart.visitEquiv q 0 hq he (z,false)) = _
    rw [ActiveArc.ExposedChart.visitEquiv_parameter]
    change ActiveArc.visitParameter (cutArc q 0) (z,false) = _
    rfl

/-- Opening at vertex zero preserves the order of the two crossing carriers. -/
theorem exposedCrossing_firstEdge {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (he : LeftExposed q 0)
    (z : ActiveArc.Crossing (ActiveArc.ExposedChart.cutArc q 0)) :
    ((ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he z).val).1.val = z.val.1.val+1 := by
  have hl := ActiveArc.ExposedChart.crossingEquiv_visit_edge q 0 hq z false
  have hr := ActiveArc.ExposedChart.crossingEquiv_visit_edge q 0 hq z true
  change edgeLabel 0 z.val.1 = _ ∨ edgeLabel 0 z.val.1 = _ at hl
  change edgeLabel 0 z.val.2 = _ ∨ edgeLabel 0 z.val.2 = _ at hr
  have hlt : edgeLabel 0 z.val.1 < edgeLabel 0 z.val.2 := by
    change (edgeLabel 0 z.val.1).val < (edgeLabel 0 z.val.2).val
    rw [ActiveArc.ExposedChart.zero_edgeLabel_val, ActiveArc.ExposedChart.zero_edgeLabel_val]
    exact Nat.succ_lt_succ z.property.1
  have hcross := (ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he z).property.1
  rcases hl with hgood|hbad
  · have hval := congrArg Fin.val hgood
    rw [ActiveArc.ExposedChart.zero_edgeLabel_val] at hval
    simpa only [ActiveArc.ExposedChart.exposedCrossingEquiv] using hval.symm
  · rcases hr with hrev|heq
    · have hback : ((ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he z).val).2.val <
          ((ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he z).val).1.val := by
        simpa only [hbad, hrev] using hlt
      exact False.elim (not_lt_of_ge (le_of_lt hcross) hback)
    · have heq' : edgeLabel 0 z.val.1 = edgeLabel 0 z.val.2 := hbad.trans heq.symm
      exact False.elim ((ne_of_lt hlt) heq')

/-- On the selected original edge, the crossing visit immediately following
the history cursor is earliest among all actual lower-carrier visits after it. -/
theorem exposed_cut_lower_parameter_min {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) (c0 : PolygonCrossing q)
    (a : ℕ) (hce : c0.val.1.val = a+1) (θ : ℝ)
    (hlo : polygonEventParameter q (PolygonDrawing.incoming q hq c0 0) < θ)
    (hhi : θ < polygonEventParameter q (PolygonDrawing.visit q c0 0))
    (z0 : ActiveArc.Crossing (ActiveArc.ExposedChart.cutArc q 0))
    (hz0 : z0.val.1.val=a)
    (hmap : ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he z0=c0) :
    ∀ z : ActiveArc.Crossing (ActiveArc.ExposedChart.cutArc q 0),
      z.val.1.val=a → θ < ActiveArc.leftParameter (ActiveArc.ExposedChart.cutArc q 0) z →
      ActiveArc.leftParameter (ActiveArc.ExposedChart.cutArc q 0) z0 ≤
        ActiveArc.leftParameter (ActiveArc.ExposedChart.cutArc q 0) z := by
  have hpar0 : ActiveArc.leftParameter (ActiveArc.ExposedChart.cutArc q 0) z0 =
      polygonEventParameter q (PolygonDrawing.visit q c0 0) := by
    obtain ⟨j,hjEdge,hjParam⟩ := exposed_lower_visit_parameter q hq he z0
    have hjEdge' := hjEdge
    rw [hmap] at hjEdge'
    have hj0 : j=0 := by
      fin_cases j
      · rfl
      · have hval := congrArg Fin.val hjEdge'
        simp [PolygonDrawing.visit, polygonEventEdge, crossingVisitEdge] at hval
        rw [ActiveArc.ExposedChart.zero_edgeLabel_val] at hval
        change c0.val.2.val = z0.val.1.val + 1 at hval
        rw [hz0] at hval
        have hc := c0.property.1
        omega
    rw [hmap, hj0] at hjParam
    exact hjParam.symm
  intro z hze hθ
  obtain ⟨j,hjEdge,hjParam⟩ := exposed_lower_visit_parameter q hq he z
  have hj0 : j=0 := by
    fin_cases j
    · rfl
    · have hval := congrArg Fin.val hjEdge
      simp [PolygonDrawing.visit, polygonEventEdge, crossingVisitEdge] at hval
      rw [ActiveArc.ExposedChart.zero_edgeLabel_val] at hval
      change ((ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he z).val).2.val =
        z.val.1.val + 1 at hval
      rw [hze] at hval
      have hcross := (ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he z).property.1
      have hfirst := exposedCrossing_firstEdge q hq he z
      omega
  have hedge : polygonEventEdge q (PolygonDrawing.visit q c0 0) =
      polygonEventEdge q (PolygonDrawing.visit q (ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he z) j) := by
    rw [hj0]
    apply Fin.ext
    simp [PolygonDrawing.visit, polygonEventEdge, crossingVisitEdge]
    have hleft : c0.val.1.val = a+1 := hce
    have hright : ((ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he z).val).1.val = a+1 := by
      rw [exposedCrossing_firstEdge q hq he z, hze]
    omega
  have hθj : θ < polygonEventParameter q
      (PolygonDrawing.visit q (ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he z) j) := by
    rw [hjParam]
    exact hθ
  have hmin := incoming_visit_first_after_cursor q hq c0
    (ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he z) 0 j θ hlo hhi hedge
      hθj
  exact le_trans (le_of_eq hpar0) (le_trans hmin (le_of_eq hjParam))

/-- The suffix and cursor crossing transports preserve the expected affine
parameter on the selected first edge. -/
theorem suffixWordCrossingEquiv_leftParameter {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hR : ActiveArc.Regular (ActiveArc.ExposedChart.cutArc q 0))
    (a b : ℕ) (hs : a+b=n) (θ : ℝ) (h0 : 0≤θ) (h1 : θ<1)
    (d : ActiveArc.Crossing (ActiveArc.Cursor.moveStart
      (ActiveArc.Split.suffixWord (ActiveArc.ExposedChart.cutArc q 0) a b hs) θ))
    (hd : d.val.1=0) :
    ActiveArc.leftParameter (ActiveArc.ExposedChart.cutArc q 0)
        (ActiveArc.Split.suffixWordCrossingEquiv (ActiveArc.ExposedChart.cutArc q 0)
          hR a b hs θ h0 h1 d).val =
      θ+(1-θ)*ActiveArc.leftParameter
        (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord
          (ActiveArc.ExposedChart.cutArc q 0) a b hs) θ) d := by
  subst n
  change ActiveArc.leftParameter (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.Split.suffixCrossingToOriginal (ActiveArc.ExposedChart.cutArc q 0)
        ((ActiveArc.Cursor.crossingEquiv (ActiveArc.Split.suffix
          (ActiveArc.ExposedChart.cutArc q 0))
          (ActiveArc.Split.regular_suffix (ActiveArc.ExposedChart.cutArc q 0) hR)
          θ h0 h1 d).val)) = _
  have hparam := ActiveArc.Split.suffixCrossing_leftParameter
    (ActiveArc.ExposedChart.cutArc q 0) hR
    ((ActiveArc.Cursor.crossingEquiv (ActiveArc.Split.suffix
      (ActiveArc.ExposedChart.cutArc q 0))
      (ActiveArc.Split.regular_suffix (ActiveArc.ExposedChart.cutArc q 0) hR)
      θ h0 h1 d).val)
  rw [hparam]
  have hfirst : ((ActiveArc.Cursor.crossingEquiv (ActiveArc.Split.suffix
      (ActiveArc.ExposedChart.cutArc q 0))
      (ActiveArc.Split.regular_suffix (ActiveArc.ExposedChart.cutArc q 0) hR)
      θ h0 h1 d).val.val).1 = 0 := by
    simpa only [ActiveArc.Cursor.crossingEquiv_val] using hd
  have hm := ActiveArc.Cursor.crossingEquiv_firstParameter
    (ActiveArc.Split.suffix (ActiveArc.ExposedChart.cutArc q 0))
    (ActiveArc.Split.regular_suffix (ActiveArc.ExposedChart.cutArc q 0) hR)
    θ h0 h1 d hfirst
  simpa [ActiveArc.Split.suffixWord, ActiveArc.Split.suffix] using hm

/-- Expose the original edge index hidden by the physical-suffix existence
construction, together with the exact history filter at that same cursor. -/
theorem exists_history_physical_suffix_edge_data {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q) (he : LeftExposed q 0)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) (ξ : ℝ) (hξ0 : 0<ξ) (hξ1 : ξ<1) :
    let d0 := (crossingFin q).symm (h.crossingOrigin c)
    ∃ a b : ℕ, ∃ hs : a+b=n, ∃ θ : ℝ, ∃ h0 : 0<θ, ∃ h1 : θ<1,
      polygonEventParameter q (PolygonDrawing.incoming q hq d0 0)<θ ∧
      θ<polygonEventParameter q (PolygonDrawing.visit q d0 0) ∧
      ActiveArc.Regular (ActiveArc.Cursor.moveStart
        (ActiveArc.Split.suffixWord (ActiveArc.ExposedChart.cutArc q 0) a b hs) θ) ∧
      ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord
        (ActiveArc.ExposedChart.cutArc q 0) a b hs) θ 0 = historyCursorPoint t c ξ ∧
      d0.val.1.val=a+1 ∧
      ∀ d : ActiveArc.Crossing (ActiveArc.ExposedChart.cutArc q 0),
        (a≤d.val.1.val ∧ (d.val.1.val=a → θ < ActiveArc.leftParameter
          (ActiveArc.ExposedChart.cutArc q 0) d)) ↔
        ∀ i : Fin 2,
          visitPosition (initialAnchorTraversal q hq)
            ((positivePolygonEventDiagram q hq).incoming (h.crossingOrigin c)
              (firstVisitedBranch t.2.1 c)) ≤
          visitPosition (initialAnchorTraversal q hq)
            ((positivePolygonEventDiagram q hq).incoming
              (crossingFin q (ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he d)) i) := by
  dsimp only
  let d0 := (crossingFin q).symm (h.crossingOrigin c)
  have hrne : d0.val.1 ≠ 0 := fun hh =>
    leftExposed_no_incident_crossing q hq 0 he d0 (Or.inl hh)
  have hrpos : 0 < d0.val.1.val := by
    have hne : d0.val.1.val ≠ 0 := by
      intro hz
      apply hrne
      apply Fin.ext
      exact hz
    exact Nat.pos_of_ne_zero hne
  let a := d0.val.1.val-1
  let b := n-a
  have ha : a≤n := by have := d0.val.1.isLt; dsimp [a]; omega
  have hs : a+b=n := by dsimp [b]; omega
  have har : d0.val.1.val=a+1 := by dsimp [a]; omega
  have har' : (((crossingFin q).symm (h.crossingOrigin c)).val.1).val=a+1 := har
  have hb := history_selected_branch_zero q hq h c hc
  obtain ⟨θ,hlo,hhi,h0,h1,hpoint,hno⟩ :=
    historyCursorPoint_parameter q hq (initialAnchorTraversal q hq) h c ξ hξ0 hξ1
  rw [hb] at hlo hhi hpoint hno
  rw [incoming_terminal_parameter] at hhi
  rw [PolygonDrawing.incoming_edge] at hpoint hno
  have hfilter : ∀ d : PolygonCrossing q,
      (∀ i : Fin 2,
        visitPosition (initialAnchorTraversal q hq)
          ((positivePolygonEventDiagram q hq).incoming (h.crossingOrigin c)
            (firstVisitedBranch t.2.1 c)) ≤
        visitPosition (initialAnchorTraversal q hq)
          ((positivePolygonEventDiagram q hq).incoming (crossingFin q d) i)) ↔
      ∀ i : Fin 2, d0.val.1 < polygonEventEdge q (visit q d i) ∨
        (d0.val.1 = polygonEventEdge q (visit q d i) ∧ θ < polygonEventParameter q (visit q d i)) := by
    intro d
    rw [hb]
    have H (i : Fin 2) := initial_incoming_cursor_filter q hq d0 d 0 i θ hlo hhi
    simp only [d0,Equiv.apply_symm_apply,visit,polygonEventEdge,crossingVisitEdge,
      Fin.isValue,ite_true] at H
    exact forall_congr' H
  refine ⟨a,b,hs,θ,h0,h1,hlo,hhi,?_,?_,har,?_⟩
  · exact ActiveArc.ExposedChart.exposed_suffix_regular q hq he a b hs d0.val.1 har θ
      (le_of_lt h0) h1 hno
  · rw [ActiveArc.Cursor.moveStart_zero]
    have hv0 : ActiveArc.Split.suffixWord (ActiveArc.ExposedChart.cutArc q 0) a b hs 0=q d0.val.1 := by
      rw [ActiveArc.Split.suffixWord_vertex]
      unfold ActiveArc.ExposedChart.cutArc
      congr 1
      apply Fin.ext
      change (0+1+(a+0))%(n+2)=d0.val.1.val
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hv1 : ActiveArc.Split.suffixWord (ActiveArc.ExposedChart.cutArc q 0) a b hs 1=
        q (cyclicSuccessor d0.val.1) := by
      rw [ActiveArc.Split.suffixWord_vertex]
      unfold ActiveArc.ExposedChart.cutArc
      congr 1
      apply Fin.ext
      change (0+1+(a+1))%(n+2)=(d0.val.1.val+1+0)%(n+2)
      rw [har]
      congr 1
      omega
    rw [hv0,hv1]
    exact hpoint.symm
  · intro d
    rw [ActiveArc.ExposedChart.exposed_crossing_cursor_filter q hq he]
    apply Iff.trans ?_ (hfilter (ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he d)).symm
    constructor
    · intro hh i
      fin_cases i
      · simpa only [PolygonDrawing.visit,Fin.isValue,Fin.reduceEq,ite_true,ite_false,
          polygonEventEdge,polygonEventParameter,Fin.lt_iff_val_lt_val,Fin.ext_iff,d0,har'] using hh false
      · simpa only [PolygonDrawing.visit,Fin.isValue,Fin.reduceEq,ite_true,ite_false,
          polygonEventEdge,polygonEventParameter,Fin.lt_iff_val_lt_val,Fin.ext_iff,d0,har'] using hh true
    · intro hh z
      cases z
      · simpa only [PolygonDrawing.visit,Fin.isValue,Fin.reduceEq,ite_true,ite_false,
          polygonEventEdge,polygonEventParameter,Fin.lt_iff_val_lt_val,Fin.ext_iff,d0,har'] using hh 0
      · simpa only [PolygonDrawing.visit,Fin.isValue,Fin.reduceEq,ite_true,ite_false,
          polygonEventEdge,polygonEventParameter,Fin.lt_iff_val_lt_val,Fin.ext_iff,d0,har'] using hh 1

/-- The selected bad current crossing is the first actual crossing on the
history cursor's physical suffix edge. Its original label is preserved. -/
theorem exists_history_physical_first_crossing {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q) (he : LeftExposed q 0)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) (ξ : ℝ) (hξ0 : 0<ξ) (hξ1 : ξ<1) :
    let d0 := (crossingFin q).symm (h.crossingOrigin c)
    ∃ a b : ℕ, ∃ hs : a+b=n, ∃ θ : ℝ, ∃ h0 : 0<θ, ∃ h1 : θ<1,
      ActiveArc.Regular (ActiveArc.Cursor.moveStart
        (ActiveArc.Split.suffixWord (ActiveArc.ExposedChart.cutArc q 0) a b hs) θ) ∧
      ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord
        (ActiveArc.ExposedChart.cutArc q 0) a b hs) θ 0 = historyCursorPoint t c ξ ∧
      ∃ d : ActiveArc.Crossing (ActiveArc.Cursor.moveStart
          (ActiveArc.Split.suffixWord (ActiveArc.ExposedChart.cutArc q 0) a b hs) θ),
        ActiveArc.Cursor.FirstCrossing
          (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord
            (ActiveArc.ExposedChart.cutArc q 0) a b hs) θ) d ∧
        crossingFin q (ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he
          (ActiveArc.Split.suffixWordCrossingEquiv (ActiveArc.ExposedChart.cutArc q 0)
            (ActiveArc.ExposedChart.cutArc_regular q 0 hq) a b hs θ (le_of_lt h0) h1 d).val) =
          h.crossingOrigin c := by
  dsimp only
  obtain ⟨a,b,hs,θ,h0,h1,hlo,hhi,hR,hpoint,har,hfilter⟩ :=
    exists_history_physical_suffix_edge_data q hq he h c hc ξ hξ0 hξ1
  let s0 := positivePolygonMarkedState q hq (initialAnchorTraversal q hq)
  let dOrig := (crossingFin q).symm (h.crossingOrigin c)
  let exposed := ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he
  let C := {z : ActiveArc.Crossing (ActiveArc.ExposedChart.cutArc q 0) //
      a≤z.val.1.val ∧ (z.val.1.val=a → θ<ActiveArc.leftParameter
        (ActiveArc.ExposedChart.cutArc q 0) z)}
  let f : C → SuffixCrossing s0
      (s0.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) :=
    fun z => ⟨crossingFin q (exposed z.val), (hfilter z.val).mp z.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z w hzw
      apply Subtype.ext
      apply exposed.injective
      apply (crossingFin q).injective
      exact congrArg Subtype.val hzw
    · intro x
      let z := exposed.symm ((crossingFin q).symm x.val)
      have hz : crossingFin q (exposed z)=x.val := by simp [z, exposed]
      have hp : a≤z.val.1.val ∧ (z.val.1.val=a → θ<
          ActiveArc.leftParameter (ActiveArc.ExposedChart.cutArc q 0) z) := by
        apply (hfilter z).mpr
        have hx := x.property
        rw [←hz] at hx
        simpa [s0,positivePolygonMarkedState,positivePolygonEventDiagram] using hx
      exact ⟨⟨z,hp⟩,Subtype.ext hz⟩
  let Ep := ActiveArc.Split.suffixWordCrossingEquiv
    (ActiveArc.ExposedChart.cutArc q 0) (ActiveArc.ExposedChart.cutArc_regular q 0 hq)
    a b hs θ (le_of_lt h0) h1
  let Eo := Equiv.ofBijective f hf
  let Es := h.suffixCrossingEquiv c hc
  let E := Ep.trans (Eo.trans Es.symm)
  let sc := selectedSuffixCrossing t c
  let d := E.symm sc
  have hEd : E d=sc := Equiv.apply_symm_apply E sc
  have hEdval : (E d).val=c := by
    rw [hEd]
    rfl
  have hEorigin (x : ActiveArc.Crossing (ActiveArc.Cursor.moveStart
      (ActiveArc.Split.suffixWord (ActiveArc.ExposedChart.cutArc q 0) a b hs) θ)) :
      h.crossingOrigin (E x).val = crossingFin q (exposed (Ep x).val) := by
    exact congrArg Subtype.val (Es.apply_symm_apply (Eo (Ep x)))
  have hOrigin : h.crossingOrigin c = crossingFin q (exposed (Ep d).val) := by
    rw [←hEdval]
    exact hEorigin d
  let z0 := exposed.symm dOrig
  have hMap0 : exposed z0=dOrig := by simp [z0, exposed]
  have hz0 : z0.val.1.val=a := by
    have heq := exposedCrossing_firstEdge q hq he z0
    rw [hMap0] at heq
    rw [har] at heq
    omega
  have hZ : (Ep d).val=z0 := by
    have hcross : crossingFin q (exposed (Ep d).val) = crossingFin q (exposed z0) := by
      exact hOrigin.symm.trans (by simp [hMap0,dOrig])
    exact exposed.injective ((crossingFin q).injective hcross)
  have hd0 : d.val.1=0 := by
    have hlab := ActiveArc.Split.suffixWordCrossingEquiv_left_label
      (ActiveArc.ExposedChart.cutArc q 0) (ActiveArc.ExposedChart.cutArc_regular q 0 hq)
      a b hs θ (le_of_lt h0) h1 d
    have hcoord : z0.val.1.val=a+d.val.1.val := by
      have hcoordZ := congrArg (fun x : ActiveArc.Crossing (ActiveArc.ExposedChart.cutArc q 0) =>
        x.val.1.val) hZ
      change (Ep d).val.val.1.val=z0.val.1.val at hcoordZ
      calc
        z0.val.1.val = (Ep d).val.val.1.val := hcoordZ.symm
        _ = a+d.val.1.val := hlab
    have hadd : a+0=a+d.val.1.val := by simpa [hz0] using hcoord
    have hdval : d.val.1.val=0 := (Nat.add_left_cancel hadd).symm
    apply Fin.ext
    exact hdval
  have hmember : θ<ActiveArc.leftParameter (ActiveArc.ExposedChart.cutArc q 0) z0 := by
    have hp := (Ep d).property.2
    have hlabel : ((Ep d).val).val.1.val=a := by rw [hZ]; exact hz0
    have := hp hlabel
    simpa [hZ] using this
  have hhi' : θ<polygonEventParameter q (PolygonDrawing.visit q dOrig 0) := by
    simpa [dOrig] using hhi
  have hlo' : polygonEventParameter q (PolygonDrawing.incoming q hq dOrig 0)<θ := by
    simpa [dOrig] using hlo
  have hfirst : ActiveArc.Cursor.FirstCrossing
      (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord
        (ActiveArc.ExposedChart.cutArc q 0) a b hs) θ) d := by
    constructor
    · exact hd0
    · intro e he0
      let z := (Ep e).val
      have hlabel : z.val.1.val=a := by
        have hlab := ActiveArc.Split.suffixWordCrossingEquiv_left_label
          (ActiveArc.ExposedChart.cutArc q 0) (ActiveArc.ExposedChart.cutArc_regular q 0 hq)
          a b hs θ (le_of_lt h0) h1 e
        change z.val.1.val=a+e.val.1.val at hlab
        have heval : e.val.1.val=0 := congrArg Fin.val he0
        rw [heval] at hlab
        simpa using hlab
      have hθz : θ<ActiveArc.leftParameter (ActiveArc.ExposedChart.cutArc q 0) z :=
        (Ep e).property.2 hlabel
      have hmin := exposed_cut_lower_parameter_min q hq he dOrig a har θ hlo' hhi' z0 hz0
        hMap0 z hlabel hθz
      have hparamd := suffixWordCrossingEquiv_leftParameter q
        (ActiveArc.ExposedChart.cutArc_regular q 0 hq) a b hs θ (le_of_lt h0) h1 d hd0
      have hparame := suffixWordCrossingEquiv_leftParameter q
        (ActiveArc.ExposedChart.cutArc_regular q 0 hq) a b hs θ (le_of_lt h0) h1 e he0
      have hparamd' : ActiveArc.leftParameter (ActiveArc.ExposedChart.cutArc q 0) z0 =
          θ+(1-θ)*ActiveArc.leftParameter
            (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord
              (ActiveArc.ExposedChart.cutArc q 0) a b hs) θ) d := by
        change ActiveArc.leftParameter (ActiveArc.ExposedChart.cutArc q 0) (Ep d).val = _ at hparamd
        rw [hZ] at hparamd
        exact hparamd
      have hparame' : ActiveArc.leftParameter (ActiveArc.ExposedChart.cutArc q 0) z =
          θ+(1-θ)*ActiveArc.leftParameter
            (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord
              (ActiveArc.ExposedChart.cutArc q 0) a b hs) θ) e := hparame
      nlinarith [hmin, hparamd', hparame', h1]
  exact ⟨a,b,hs,θ,h0,h1,hR,hpoint,d,hfirst,hOrigin.symm⟩

/- The first-event consumer is developed from the actual cursor interval and
  the physical crossing equivalence.  The origin equality remains explicit in
  the result, so downstream callers can identify the selected original event. -/

end DirectGLSSW.HOMFLY

#check @DirectGLSSW.HOMFLY.selectedSuffixCrossing
#print DirectGLSSW.HOMFLY.selectedSuffixCrossing
#check @DirectGLSSW.HOMFLY.exists_history_physical_first_crossing

