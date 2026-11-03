import ActiveArcCutEvents
import DirectGLSSW.EventSegmentGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ExposedChart
open DirectGLSSW ExposedOpenPrimitive PhysicalSegments EventSegmentGeometry
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2))
variable (hq : CyclicGeneric q) (he : LeftExposed q e)

theorem eventEquiv_sameEdge_lt (x y : ActiveArc.Event (cutArc q e))
    (hxy : ActiveArc.edgeTag (cutArc q e) x=ActiveArc.edgeTag (cutArc q e) y) :
    (letI := ActiveArc.eventOrder (cutArc q e) (cutArc_regular q e hq).noTriple; x<y) ↔
    (letI := polygonEventOrder q hq.g2; eventEquiv q e hq he x<eventEquiv q e hq he y) := by
  rw [polygonEvent_sameEdge_lt_iff q hq.g2 _ _ ((eventEquiv_sameEdge_iff q e hq he x y).mpr hxy)]
  rw [eventEquiv_parameter,eventEquiv_parameter,ActiveArc.event_lt_iff]
  simp only [hxy,lt_self_iff_false,true_and,false_or]

theorem eventEquiv_sameEdge_le (x y : ActiveArc.Event (cutArc q e))
    (hxy : ActiveArc.edgeTag (cutArc q e) x=ActiveArc.edgeTag (cutArc q e) y) :
    (letI := ActiveArc.eventOrder (cutArc q e) (cutArc_regular q e hq).noTriple; x≤y) ↔
    (letI := polygonEventOrder q hq.g2; eventEquiv q e hq he x≤eventEquiv q e hq he y) := by
  letI := ActiveArc.eventOrder (cutArc q e) (cutArc_regular q e hq).noTriple
  letI := polygonEventOrder q hq.g2
  constructor
  · intro hh
    apply le_of_not_gt
    intro hb
    exact (not_lt_of_ge hh) ((eventEquiv_sameEdge_lt q e hq he y x hxy.symm).mpr hb)
  · intro hh
    apply le_of_not_gt
    intro hb
    exact (not_lt_of_ge hh) ((eventEquiv_sameEdge_lt q e hq he y x hxy.symm).mp hb)

theorem active_successor_local_spec (x : ActiveArc.Event (cutArc q e))
    (hx : x≠ActiveArc.terminal (cutArc q e)) :
    letI := ActiveArc.eventOrder (cutArc q e) (cutArc_regular q e hq).noTriple
    let y := ActiveArc.successor (cutArc q e) (cutArc_regular q e hq).noTriple x
    (ActiveArc.edgeTag (cutArc q e) y=ActiveArc.edgeTag (cutArc q e) x ∧
      ActiveArc.parameter (cutArc q e) x<ActiveArc.parameter (cutArc q e) y ∧
      ∀ z, ActiveArc.edgeTag (cutArc q e) z=ActiveArc.edgeTag (cutArc q e) x →
        ActiveArc.parameter (cutArc q e) x<ActiveArc.parameter (cutArc q e) z → y≤z) ∨
    (y=Sum.inl (physicalEdge (cutArc q e) x hx).succ ∧
      ∀ z, ActiveArc.edgeTag (cutArc q e) z=ActiveArc.edgeTag (cutArc q e) x →
        ActiveArc.parameter (cutArc q e) z≤ActiveArc.parameter (cutArc q e) x) := by
  letI := ActiveArc.eventOrder (cutArc q e) (cutArc_regular q e hq).noTriple
  rcases successor_sameEdge_or_anchor (cutArc q e) (cutArc_regular q e hq) x hx with hs|ha
  · left
    refine ⟨hs.1,hs.2,?_⟩
    intro z hz htz
    apply successor_min (cutArc q e) (cutArc_regular q e hq) x z hx
    exact (ActiveArc.event_lt_iff _ _ _ _).mpr (Or.inr ⟨hz.symm,htz⟩)
  · right
    refine ⟨ha,?_⟩
    intro z hz
    apply le_of_not_gt
    intro hh
    have hlt : x<z := (ActiveArc.event_lt_iff _ _ _ _).mpr (Or.inr ⟨hz.symm,hh⟩)
    have hle := successor_min (cutArc q e) (cutArc_regular q e hq) x z hx hlt
    rw [ha] at hle
    have hbad : z<(Sum.inl (physicalEdge (cutArc q e) x hx).succ : ActiveArc.Event (cutArc q e)) := by
      apply (ActiveArc.event_lt_iff _ _ _ _).mpr
      left
      change ActiveArc.edgeTag (cutArc q e) z<ActiveArc.edgeTag (cutArc q e) x+1
      omega
    exact (not_lt_of_ge hle) hbad

theorem eventLabel_nonterminal (x : ActiveArc.Event (cutArc q e))
    (hx : x≠ActiveArc.terminal (cutArc q e)) :
    eventLabel q e x=(physicalEdge (cutArc q e) x hx).castSucc := by
  apply Fin.ext
  exact eventLabel_val q e x

include hq he in
theorem event_on_deleted_eq_anchor (x : PolygonEvent q) (hx : polygonEventEdge q x=e) :
    x=Sum.inl e := by
  cases x with
  | inl i => exact congrArg Sum.inl hx
  | inr v =>
    rcases v with ⟨c,b⟩
    have hn := leftExposed_no_incident_crossing q hq e he c
    cases b
    · exact False.elim (hn (Or.inl hx))
    · exact False.elim (hn (Or.inr hx))

/-- Actual successor conjugacy, including the exposed deleted-edge seam. -/
theorem eventEquiv_successor (x : ActiveArc.Event (cutArc q e)) :
    polygonEventSuccessor q hq.g2 (eventEquiv q e hq he x)=
      eventEquiv q e hq he (ActiveArc.successor (cutArc q e) (cutArc_regular q e hq).noTriple x) := by
  letI := ActiveArc.eventOrder (cutArc q e) (cutArc_regular q e hq).noTriple
  letI := polygonEventOrder q hq.g2
  by_cases hx : x=ActiveArc.terminal (cutArc q e)
  · subst x
    rw [ActiveArc.successor_terminal,eventEquiv_start,eventEquiv_terminal]
    rcases polygonEventSuccessor_sameEdge_next_or_nextAnchor q hq.g2 hq.size_ge_three (Sum.inl e) with hs|ha
    · have hz := event_on_deleted_eq_anchor q e hq he _ hs.1
      have hp := hs.2.1
      rw [hz] at hp
      exact False.elim (lt_irrefl _ hp)
    · exact ha.1
  · let y := ActiveArc.successor (cutArc q e) (cutArc_regular q e hq).noTriple x
    let z := polygonEventSuccessor q hq.g2 (eventEquiv q e hq he x)
    let w := (eventEquiv q e hq he).symm z
    have hw : eventEquiv q e hq he w=z := (eventEquiv q e hq he).apply_symm_apply z
    have hp := polygonEventSuccessor_sameEdge_next_or_nextAnchor q hq.g2 hq.size_ge_three (eventEquiv q e hq he x)
    have ha := active_successor_local_spec q e hq x hx
    rcases ha with ha|ha <;> rcases hp with hp|hp
    · have hwe : ActiveArc.edgeTag (cutArc q e) w=ActiveArc.edgeTag (cutArc q e) x := by
        apply (eventEquiv_sameEdge_iff q e hq he w x).mp
        rw [hw]
        exact hp.1
      have hwp : ActiveArc.parameter (cutArc q e) x<ActiveArc.parameter (cutArc q e) w := by
        rw [← eventEquiv_parameter q e hq he x,← eventEquiv_parameter q e hq he w,hw]
        exact hp.2.1
      have hyw : y≤w := ha.2.2 w hwe hwp
      have hmyz : eventEquiv q e hq he y≤z := by
        rw [← hw]
        exact (eventEquiv_sameEdge_le q e hq he y w (ha.1.trans hwe.symm)).mp hyw
      have hzmy : z≤eventEquiv q e hq he y := hp.2.2 _
        ((eventEquiv_sameEdge_iff q e hq he y x).mpr ha.1)
        (by rw [eventEquiv_parameter,eventEquiv_parameter];exact ha.2.1)
      exact le_antisymm hzmy hmyz
    · have hbad := hp.2 (eventEquiv q e hq he y)
        ((eventEquiv_sameEdge_iff q e hq he y x).mpr ha.1)
      rw [eventEquiv_parameter,eventEquiv_parameter] at hbad
      exact False.elim ((not_lt_of_ge hbad) ha.2.1)
    · have hwe : ActiveArc.edgeTag (cutArc q e) w=ActiveArc.edgeTag (cutArc q e) x := by
        apply (eventEquiv_sameEdge_iff q e hq he w x).mp
        rw [hw]
        exact hp.1
      have hbad := ha.2 w hwe
      have hwp := hp.2.1
      change polygonEventParameter q (eventEquiv q e hq he x)<polygonEventParameter q z at hwp
      rw [← hw,eventEquiv_parameter,eventEquiv_parameter] at hwp
      exact False.elim ((not_lt_of_ge hbad) hwp)
    · rw [hp.1,ha.1,eventEquiv_anchor,eventEquiv_edge,eventLabel_nonterminal q e x hx]
      exact congrArg Sum.inl (edgeLabel_successor e (physicalEdge (cutArc q e) x hx)).symm

end DirectGLSSW.ActiveArc.ExposedChart
