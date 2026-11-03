import SharpDaughterDiagram
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SharpDaughter
open DirectGLSSW PermutationOrbits PolygonDrawingBridge
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)

theorem arc_count_pos : 0 < (sharpDaughterDiagram q hq S C hNA).nArc := by
  change 0 < Fintype.card (Arc q hq S C)
  exact Fintype.card_pos

theorem arc_bijection : Function.Bijective (arcEquiv q hq S C) :=
  (arcEquiv q hq S C).bijective

theorem continuation_conjugacy (a : Fin (sharpDaughterDiagram q hq S C hNA).nArc) :
    arcEquiv q hq S C ((sharpDaughterDiagram q hq S C hNA).continuation a) =
      fibrePerm (P q hq S) C (arcEquiv q hq S C a) := arcEquiv_next q hq S C a

theorem vertex_retained_iff (v : Fin (Parent q hq).nVertex) :
    (∃ w : Fin (sharpDaughterDiagram q hq S C hNA).nVertex, oldVertex q hq S C w = v) ↔
    ∃ x : PolygonEvent q, componentOf (P q hq S) x = C ∧
      ((Parent q hq).arcSource (eventFin q x) = v ∨
       (Parent q hq).arcTarget (eventFin q x) = v) := by
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨a, ha⟩ := (vertexEquiv q hq S C w).property
    exact ⟨a.val, a.property, Or.inl ha⟩
  · rintro ⟨x, hx, hs | ht⟩
    · exact ⟨(vertexEquiv q hq S C).symm ⟨v, ⟨x, hx⟩, hs⟩, by simp [oldVertex]⟩
    · refine ⟨(vertexEquiv q hq S C).symm
        ⟨v, fibrePerm (P q hq S) C ⟨x, hx⟩, ?_⟩, by simp [oldVertex]⟩
      exact (parent_next_incidence q hq S x).symm.trans ht

theorem crossing_retained_iff (c : Fin (Parent q hq).nCrossing) :
    (∃ d : Fin (sharpDaughterDiagram q hq S C hNA).nCrossing, oldCrossing q hq S C d = c) ↔
    ((crossingFin q).symm c) ∉ S ∧
      ∀ i : Fin 2, componentOf (P q hq S)
        ((eventFin q).symm ((Parent q hq).outgoing c i)) = C := by
  constructor
  · rintro ⟨d, rfl⟩; exact (crossingEquiv q hq S C d).property
  · intro hc
    exact ⟨(crossingEquiv q hq S C).symm ⟨c, hc⟩, by simp [oldCrossing]⟩

theorem actual_crossing_retained_iff (c : PolygonCrossing q) :
    (∃ d : Fin (sharpDaughterDiagram q hq S C hNA).nCrossing,
      oldCrossing q hq S C d = crossingFin q c) ↔
    c ∉ S ∧ ∀ b : Bool, componentOf (P q hq S) (Sum.inr (c,b)) = C := by
  rw [crossing_retained_iff]
  constructor
  · rintro ⟨hc, hm⟩
    refine ⟨by simpa only [Equiv.symm_apply_apply] using hc, ?_⟩
    intro b; cases b
    · simpa [outgoing_event, PolygonDrawing.visit] using hm 0
    · simpa [outgoing_event, PolygonDrawing.visit] using hm 1
  · rintro ⟨hc, hm⟩
    refine ⟨by simpa only [Equiv.symm_apply_apply] using hc, ?_⟩
    intro i; fin_cases i
    · simpa [outgoing_event, PolygonDrawing.visit] using hm false
    · simpa [outgoing_event, PolygonDrawing.visit] using hm true

theorem coordinates_preserved (v : Fin (sharpDaughterDiagram q hq S C hNA).nVertex) :
    (sharpDaughterDiagram q hq S C hNA).vertexPoint v =
      (Parent q hq).vertexPoint (oldVertex q hq S C v) := rfl

theorem endpoints_preserved (a : Fin (sharpDaughterDiagram q hq S C hNA).nArc) :
    oldVertex q hq S C ((sharpDaughterDiagram q hq S C hNA).arcSource a) =
      (Parent q hq).arcSource (oldArc q hq S C a) ∧
    oldVertex q hq S C ((sharpDaughterDiagram q hq S C hNA).arcTarget a) =
      (Parent q hq).arcTarget (oldArc q hq S C a) :=
  ⟨old_source q hq S C a, old_target q hq S C a⟩

theorem crossing_data_preserved
    (c : Fin (sharpDaughterDiagram q hq S C hNA).nCrossing) :
    (sharpDaughterDiagram q hq S C hNA).through c = (Parent q hq).through (oldCrossing q hq S C c) ∧
    (sharpDaughterDiagram q hq S C hNA).overBranch c = (Parent q hq).overBranch (oldCrossing q hq S C c) ∧
    (∀ i, oldArc q hq S C ((sharpDaughterDiagram q hq S C hNA).incoming c i) =
      (Parent q hq).incoming (oldCrossing q hq S C c) i) ∧
    (∀ i, oldArc q hq S C ((sharpDaughterDiagram q hq S C hNA).outgoing c i) =
      (Parent q hq).outgoing (oldCrossing q hq S C c) i) :=
  ⟨rfl, rfl, old_incoming q hq S C c, old_outgoing q hq S C c⟩

theorem strand_tangent_preserved
    (c : Fin (sharpDaughterDiagram q hq S C hNA).nCrossing) (i : Fin 2) :
    strandTangent (sharpDaughterDiagram q hq S C hNA) c i =
      strandTangent (Parent q hq) (oldCrossing q hq S C c) i := by
  simp only [strandTangent, sharpDaughterDiagram, old_crossing, old_source, old_incoming]

theorem crossing_det_preserved
    (c : Fin (sharpDaughterDiagram q hq S C hNA).nCrossing) :
    crossingDet (sharpDaughterDiagram q hq S C hNA) c =
      crossingDet (Parent q hq) (oldCrossing q hq S C c) := by
  unfold crossingDet
  rw [strand_tangent_preserved, strand_tangent_preserved]
  rfl

theorem omitted_crossing_regular (c : Fin (Parent q hq).nCrossing)
    (hsome : ∃ i : Fin 2, componentOf (P q hq S)
      ((eventFin q).symm ((Parent q hq).outgoing c i)) = C)
    (hnot : ¬ (((crossingFin q).symm c) ∉ S ∧
      ∀ i : Fin 2, componentOf (P q hq S)
        ((eventFin q).symm ((Parent q hq).outgoing c i)) = C)) :
    ∃ v : Fin (sharpDaughterDiagram q hq S C hNA).nVertex,
      oldVertex q hq S C v = (Parent q hq).crossingVertex c ∧
      (∀ d, (sharpDaughterDiagram q hq S C hNA).crossingVertex d ≠ v) ∧
      (incomingArcs (sharpDaughterDiagram q hq S C hNA).arcTarget v).card = 1 ∧
      (outgoingArcs (sharpDaughterDiagram q hq S C hNA).arcSource v).card = 1 := by
  obtain ⟨i, hi⟩ := hsome
  obtain ⟨v, hv⟩ := (vertex_retained_iff q hq S C hNA ((Parent q hq).crossingVertex c)).mpr
    ⟨(eventFin q).symm ((Parent q hq).outgoing c i), hi,
      Or.inl (by rw [Equiv.apply_symm_apply]; exact (Parent q hq).outgoing_source c i)⟩
  have hreg : ∀ d, (sharpDaughterDiagram q hq S C hNA).crossingVertex d ≠ v := by
    intro d hd
    have heq : oldCrossing q hq S C d = c := (Parent q hq).crossingVertex_injective (by
      have hh := congrArg (oldVertex q hq S C) hd
      change oldVertex q hq S C (crossingIndex q hq S C d) = oldVertex q hq S C v at hh
      simpa only [old_crossing, hv] using hh)
    exact hnot ((crossing_retained_iff q hq S C hNA c).mp ⟨d, heq⟩)
  exact ⟨v, hv, hreg, (sharpDaughterDiagram q hq S C hNA).regular_degree_one v hreg⟩

theorem selected_crossing_regular (c : Fin (Parent q hq).nCrossing)
    (hc : ((crossingFin q).symm c) ∈ S)
    (hsome : ∃ i : Fin 2, componentOf (P q hq S)
      ((eventFin q).symm ((Parent q hq).outgoing c i)) = C) :
    ∃ v : Fin (sharpDaughterDiagram q hq S C hNA).nVertex,
      oldVertex q hq S C v = (Parent q hq).crossingVertex c ∧
      (∀ d, (sharpDaughterDiagram q hq S C hNA).crossingVertex d ≠ v) ∧
      (incomingArcs (sharpDaughterDiagram q hq S C hNA).arcTarget v).card = 1 ∧
      (outgoingArcs (sharpDaughterDiagram q hq S C hNA).arcSource v).card = 1 :=
  omitted_crossing_regular q hq S C hNA c hsome (fun h => h.1 hc)

theorem mixed_crossing_regular (c : Fin (Parent q hq).nCrossing)
    (hc : ((crossingFin q).symm c) ∉ S)
    (hsome : ∃ i : Fin 2, componentOf (P q hq S)
      ((eventFin q).symm ((Parent q hq).outgoing c i)) = C)
    (hnot : ¬ ∀ i : Fin 2, componentOf (P q hq S)
      ((eventFin q).symm ((Parent q hq).outgoing c i)) = C) :
    ∃ v : Fin (sharpDaughterDiagram q hq S C hNA).nVertex,
      oldVertex q hq S C v = (Parent q hq).crossingVertex c ∧
      (∀ d, (sharpDaughterDiagram q hq S C hNA).crossingVertex d ≠ v) ∧
      (incomingArcs (sharpDaughterDiagram q hq S C hNA).arcTarget v).card = 1 ∧
      (outgoingArcs (sharpDaughterDiagram q hq S C hNA).arcSource v).card = 1 :=
  omitted_crossing_regular q hq S C hNA c hsome (fun h => hnot h.2)

theorem unselected_visit_ports (c : Fin (Parent q hq).nCrossing)
    (hc : ((crossingFin q).symm c) ∉ S) (i : Fin 2)
    (hi : componentOf (P q hq S)
      ((eventFin q).symm ((Parent q hq).outgoing c ((Parent q hq).through c i))) = C) :
    ∃ a b : Fin (sharpDaughterDiagram q hq S C hNA).nArc,
      oldArc q hq S C a = (Parent q hq).incoming c i ∧
      oldArc q hq S C b = (Parent q hq).outgoing c ((Parent q hq).through c i) ∧
      (sharpDaughterDiagram q hq S C hNA).continuation a = b := by
  let b : Arc q hq S C := ⟨(eventFin q).symm ((Parent q hq).outgoing c ((Parent q hq).through c i)), hi⟩
  let a : Arc q hq S C := ⟨(eventFin q).symm ((Parent q hq).incoming c i), by
    rw [← p_incoming q hq S c hc i, componentOf_apply] at hi
    exact hi⟩
  refine ⟨(arcEquiv q hq S C).symm a, (arcEquiv q hq S C).symm b, ?_, ?_, ?_⟩
  · simp only [oldArc, Equiv.apply_symm_apply, a]
  · simp only [oldArc, Equiv.apply_symm_apply, b]
  · apply (arcEquiv q hq S C).injective
    rw [continuation_conjugacy, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    apply Subtype.ext
    exact p_incoming q hq S c hc i

theorem unselected_visit_tangents_positive (c : Fin (Parent q hq).nCrossing)
    (hc : ((crossingFin q).symm c) ∉ S) (i : Fin 2)
    (hi : componentOf (P q hq S)
      ((eventFin q).symm ((Parent q hq).outgoing c ((Parent q hq).through c i))) = C) :
    ∃ a b : Fin (sharpDaughterDiagram q hq S C hNA).nArc,
      oldArc q hq S C a = (Parent q hq).incoming c i ∧
      oldArc q hq S C b = (Parent q hq).outgoing c ((Parent q hq).through c i) ∧
      ∃ scale : ℝ, 0 < scale ∧
        ((sharpDaughterDiagram q hq S C hNA).vertexPoint ((sharpDaughterDiagram q hq S C hNA).arcTarget a) -
         (sharpDaughterDiagram q hq S C hNA).vertexPoint ((sharpDaughterDiagram q hq S C hNA).arcSource a)) =
        scale • ((sharpDaughterDiagram q hq S C hNA).vertexPoint ((sharpDaughterDiagram q hq S C hNA).arcTarget b) -
         (sharpDaughterDiagram q hq S C hNA).vertexPoint ((sharpDaughterDiagram q hq S C hNA).arcSource b)) := by
  obtain ⟨a,b,ha,hb,hnext⟩ := unselected_visit_ports q hq S C hNA c hc i hi
  obtain ⟨scale,hscale,htan⟩ := (Parent q hq).through_tangents_positive_collinear c i
  refine ⟨a,b,ha,hb,scale,hscale,?_⟩
  change ((Parent q hq).vertexPoint (oldVertex q hq S C (targetIndex q hq S C a)) -
    (Parent q hq).vertexPoint (oldVertex q hq S C (sourceIndex q hq S C a))) =
    scale • ((Parent q hq).vertexPoint (oldVertex q hq S C (targetIndex q hq S C b)) -
    (Parent q hq).vertexPoint (oldVertex q hq S C (sourceIndex q hq S C b)))
  rw [old_target, old_source, old_target, old_source, ha, hb,
    (Parent q hq).incoming_target, (Parent q hq).outgoing_source]
  exact htan
end DirectGLSSW.HOMFLY.SharpDaughter



