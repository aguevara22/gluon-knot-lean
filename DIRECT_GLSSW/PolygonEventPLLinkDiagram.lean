import PolygonDrawingPorts
import DirectGLSSW.HOMFLY.PLDiagrams

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge

open DirectGLSSW
open DirectGLSSW.HOMFLY.PolygonDrawing
noncomputable section

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

abbrev Vtx := DirectGLSSW.HOMFLY.PolygonDrawing.Vertex q
abbrev Ev := DirectGLSSW.PolygonEvent q
abbrev Cr := DirectGLSSW.PolygonCrossing q

noncomputable def vertexFin : Vtx q ≃ Fin (Fintype.card (Vtx q)) := Fintype.equivFin _
noncomputable def eventFin : Ev q ≃ Fin (Fintype.card (Ev q)) := Fintype.equivFin _
noncomputable def crossingFin : Cr q ≃ Fin (Fintype.card (Cr q)) := Fintype.equivFin _

noncomputable def sourceIndex (a : Fin (Fintype.card (Ev q))) :
    Fin (Fintype.card (Vtx q)) :=
  vertexFin q (PolygonDrawing.arcSource q ((eventFin q).symm a))

noncomputable def targetIndex (a : Fin (Fintype.card (Ev q))) :
    Fin (Fintype.card (Vtx q)) :=
  vertexFin q (PolygonDrawing.arcTarget q hq ((eventFin q).symm a))

noncomputable def crossingVertexIndex (c : Fin (Fintype.card (Cr q))) :
    Fin (Fintype.card (Vtx q)) :=
  vertexFin q (Sum.inr ((crossingFin q).symm c))

noncomputable def incomingIndex (c : Fin (Fintype.card (Cr q))) (i : Fin 2) :
    Fin (Fintype.card (Ev q)) :=
  eventFin q (PolygonDrawing.incoming q hq ((crossingFin q).symm c) i)

noncomputable def outgoingIndex (c : Fin (Fintype.card (Cr q))) (i : Fin 2) :
    Fin (Fintype.card (Ev q)) :=
  eventFin q (PolygonDrawing.visit q ((crossingFin q).symm c) i)

noncomputable def eventSuccessor : Equiv.Perm (Ev q) :=
  polygonEventSuccessor q hq.g2

noncomputable def successorArc : Equiv.Perm (Fin (Fintype.card (Ev q))) :=
  (eventFin q).symm.trans ((eventSuccessor q hq).trans (eventFin q))

noncomputable def coordinate (v : Fin (Fintype.card (Vtx q))) : PlanarPoint ℝ :=
  PolygonDrawing.vertexPoint q ((vertexFin q).symm v)

theorem source_anchor_iff (a : Fin (Fintype.card (Ev q))) (i : Fin n) :
    sourceIndex q a = vertexFin q (Sum.inl i) ↔ a = eventFin q (Sum.inl i) := by
  unfold sourceIndex
  constructor
  · intro h
    have he : PolygonDrawing.eventVertex q ((eventFin q).symm a) = Sum.inl i :=
      (vertexFin q).injective h
    have hx := (PolygonDrawing.eventVertex_eq_anchor_iff q ((eventFin q).symm a) i).mp he
    calc
      a = eventFin q ((eventFin q).symm a) := ((eventFin q).apply_symm_apply a).symm
      _ = eventFin q (Sum.inl i) := congrArg (eventFin q) hx
  · intro h
    subst a
    simp [sourceIndex, eventFin, vertexFin, PolygonDrawing.arcSource, PolygonDrawing.eventVertex]

theorem target_anchor_iff (a : Fin (Fintype.card (Ev q))) (i : Fin n) :
    targetIndex q hq a = vertexFin q (Sum.inl i) ↔
      a = eventFin q ((polygonEventSuccessor q hq.g2).symm (Sum.inl i)) := by
  unfold targetIndex
  constructor
  · intro h
    have he : PolygonDrawing.eventVertex q
        (polygonEventSuccessor q hq.g2 ((eventFin q).symm a)) = Sum.inl i :=
      (vertexFin q).injective h
    have hs := (PolygonDrawing.eventVertex_eq_anchor_iff q
      (polygonEventSuccessor q hq.g2 ((eventFin q).symm a)) i).mp he
    calc
      a = eventFin q ((eventFin q).symm a) := ((eventFin q).apply_symm_apply a).symm
      _ = eventFin q ((polygonEventSuccessor q hq.g2).symm
          (polygonEventSuccessor q hq.g2 ((eventFin q).symm a))) :=
            congrArg (eventFin q) ((polygonEventSuccessor q hq.g2).symm_apply_apply _).symm
      _ = eventFin q ((polygonEventSuccessor q hq.g2).symm (Sum.inl i)) :=
            congrArg (fun x => eventFin q ((polygonEventSuccessor q hq.g2).symm x)) hs
  · intro h
    subst a
    simp [targetIndex, eventFin, vertexFin, PolygonDrawing.arcTarget, PolygonDrawing.eventVertex]

theorem coordinate_source (a : Fin (Fintype.card (Ev q))) :
    coordinate q (sourceIndex q a) =
      PolygonDrawing.vertexPoint q
        (PolygonDrawing.arcSource q ((eventFin q).symm a)) := by
  simp [coordinate, sourceIndex, vertexFin, PolygonDrawing.arcSource,
    PolygonDrawing.vertexPoint_eventVertex]

theorem coordinate_target (a : Fin (Fintype.card (Ev q))) :
    coordinate q (targetIndex q hq a) =
      PolygonDrawing.vertexPoint q
        (PolygonDrawing.arcTarget q hq ((eventFin q).symm a)) := by
  simp [coordinate, targetIndex, vertexFin, PolygonDrawing.arcTarget,
    PolygonDrawing.vertexPoint_eventVertex]

theorem coordinate_crossing (c : Fin (Fintype.card (Cr q))) :
    coordinate q (crossingVertexIndex q c) =
      PolygonDrawing.vertexPoint q (Sum.inr ((crossingFin q).symm c)) := by
  simp [coordinate, crossingVertexIndex, vertexFin]

def polygonEventDiagram : PLLinkDiagram where
  nVertex := Fintype.card (Vtx q)
  nArc := Fintype.card (Ev q)
  nCrossing := Fintype.card (Cr q)
  vertexPoint := coordinate q
  arcSource := sourceIndex q
  arcTarget := targetIndex q hq
  crossingVertex := crossingVertexIndex q
  crossingVertex_injective := by
    intro c d h
    have h' := (vertexFin q).injective h
    have h'' := Sum.inr.inj h'
    exact (crossingFin q).symm.injective h''
  incoming := incomingIndex q hq
  outgoing := outgoingIndex q
  incoming_target := by
    intro c i
    change vertexFin q (PolygonDrawing.arcTarget q hq
      ((eventFin q).symm (eventFin q (PolygonDrawing.incoming q hq ((crossingFin q).symm c) i)))) =
      vertexFin q (Sum.inr ((crossingFin q).symm c))
    rw [(eventFin q).symm_apply_apply]
    exact congrArg (vertexFin q)
      (PolygonDrawing.incoming_target q hq ((crossingFin q).symm c) i)
  outgoing_source := by
    intro c i
    change vertexFin q (PolygonDrawing.arcSource q
      ((eventFin q).symm (eventFin q (PolygonDrawing.visit q ((crossingFin q).symm c) i)))) =
      vertexFin q (Sum.inr ((crossingFin q).symm c))
    rw [(eventFin q).symm_apply_apply]
    exact congrArg (vertexFin q)
      (PolygonDrawing.visit_vertex q ((crossingFin q).symm c) i)
  four_ports_distinct := by
    intro c
    simpa [incomingIndex, outgoingIndex, eventFin, crossingFin] using
      (PolygonDrawing.four_ports_distinct q hq ((crossingFin q).symm c))
  crossing_incidence_complete := by
    intro c a
    change (vertexFin q (PolygonDrawing.arcSource q ((eventFin q).symm a)) =
        vertexFin q (Sum.inr ((crossingFin q).symm c)) ∨
      vertexFin q (PolygonDrawing.arcTarget q hq ((eventFin q).symm a)) =
        vertexFin q (Sum.inr ((crossingFin q).symm c))) ↔
      (a = eventFin q (PolygonDrawing.incoming q hq ((crossingFin q).symm c) 0) ∨
       a = eventFin q (PolygonDrawing.incoming q hq ((crossingFin q).symm c) 1) ∨
       a = eventFin q (PolygonDrawing.visit q ((crossingFin q).symm c) 0) ∨
       a = eventFin q (PolygonDrawing.visit q ((crossingFin q).symm c) 1))
    let x := (eventFin q).symm a
    let k := (crossingFin q).symm c
    have hroot := PolygonDrawing.crossing_incidence_complete q hq k x
    constructor
    · intro h
      have hend : PolygonDrawing.arcSource q x = Sum.inr k ∨
          PolygonDrawing.arcTarget q hq x = Sum.inr k := by
        rcases h with hs | ht
        · exact Or.inl ((vertexFin q).injective hs)
        · exact Or.inr ((vertexFin q).injective ht)
      rcases hroot.mp hend with h0 | h1 | h2 | h3
      · left
        calc
          a = eventFin q x := ((eventFin q).apply_symm_apply a).symm
          _ = eventFin q (PolygonDrawing.incoming q hq k 0) := congrArg (eventFin q) h0
      · right
        left
        calc
          a = eventFin q x := ((eventFin q).apply_symm_apply a).symm
          _ = eventFin q (PolygonDrawing.incoming q hq k 1) := congrArg (eventFin q) h1
      · right
        right
        left
        calc
          a = eventFin q x := ((eventFin q).apply_symm_apply a).symm
          _ = eventFin q (PolygonDrawing.visit q k 0) := congrArg (eventFin q) h2
      · right
        right
        right
        calc
          a = eventFin q x := ((eventFin q).apply_symm_apply a).symm
          _ = eventFin q (PolygonDrawing.visit q k 1) := congrArg (eventFin q) h3
    · intro h
      rcases h with h0 | h1 | h2 | h3
      · have hE := hroot.mpr (Or.inl (by simpa using congrArg (eventFin q).symm h0))
        rcases hE with hs | ht
        · left
          exact congrArg (vertexFin q) hs
        · right
          exact congrArg (vertexFin q) ht
      · have hE := hroot.mpr (Or.inr (Or.inl (by simpa using congrArg (eventFin q).symm h1)))
        rcases hE with hs | ht
        · left
          exact congrArg (vertexFin q) hs
        · right
          exact congrArg (vertexFin q) ht
      · have hE := hroot.mpr (Or.inr (Or.inr (Or.inl (by simpa using congrArg (eventFin q).symm h2))))
        rcases hE with hs | ht
        · left
          exact congrArg (vertexFin q) hs
        · right
          exact congrArg (vertexFin q) ht
      · have hE := hroot.mpr (Or.inr (Or.inr (Or.inr (by simpa using congrArg (eventFin q).symm h3))))
        rcases hE with hs | ht
        · left
          exact congrArg (vertexFin q) hs
        · right
          exact congrArg (vertexFin q) ht
  regular_degree_one := by
    intro v hnocross
    cases hv : (vertexFin q).symm v with
    | inl i =>
      have hv' : v = vertexFin q (Sum.inl i) := by
        have he := (vertexFin q).apply_symm_apply v
        rw [hv] at he
        exact he.symm
      have hout : outgoingArcs (sourceIndex q) v =
          {eventFin q (Sum.inl i)} := by
        ext a
        rw [hv']
        simp only [outgoingArcs, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        exact (source_anchor_iff q a i)
      have hin : incomingArcs (targetIndex q hq) v =
          {eventFin q ((polygonEventSuccessor q hq.g2).symm (Sum.inl i))} := by
        ext a
        rw [hv']
        simp only [incomingArcs, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        exact (target_anchor_iff q hq a i)
      constructor
      · rw [hin]
        simp
      · rw [hout]
        simp
    | inr c =>
      have hv' : v = vertexFin q (Sum.inr c) := by
        have he := (vertexFin q).apply_symm_apply v
        rw [hv] at he
        exact he.symm
      have hc := hnocross ((crossingFin q) c)
      have hcv : crossingVertexIndex q ((crossingFin q) c) =
          vertexFin q (Sum.inr c) := by simp [crossingVertexIndex]
      exact False.elim (hc (hcv.trans hv'.symm))
  through := fun _ => Equiv.refl (Fin 2)
  continuation := successorArc q hq
  continuation_incidence := by
    intro a
    change vertexFin q (PolygonDrawing.arcTarget q hq ((eventFin q).symm a)) =
      vertexFin q (PolygonDrawing.arcSource q ((eventFin q).symm ((successorArc q hq) a)))
    simp only [successorArc, Equiv.trans_apply, Equiv.symm_apply_apply]
    exact congrArg (vertexFin q)
      (PolygonDrawing.continuation_incidence q hq ((eventFin q).symm a))
  continuation_crossing := by
    intro c i
    unfold successorArc incomingIndex outgoingIndex eventSuccessor
    simp [Equiv.trans_apply, PolygonDrawing.incoming_successor]
  overBranch := fun _ => 0
  vertexPoint_injective := by
    intro a b h
    have hv : ((vertexFin q).symm a) = ((vertexFin q).symm b) :=
      PolygonDrawing.vertexPoint_injective q hq h
    have h' := congrArg (vertexFin q) hv
    simpa using h'
  arc_endpoints_distinct := by
    intro a heq
    have he := (vertexFin q).injective heq
    exact (PolygonDrawing.arc_endpoints_distinct q hq ((eventFin q).symm a)) he
  arc_interiors_disjoint := by
    intro a b hab s t hs0 hs1 ht0 ht1 heq
    have hab' : (eventFin q).symm a ≠ (eventFin q).symm b := by
      intro he
      exact hab ((eventFin q).symm.injective he)
    rw [coordinate_source q, coordinate_target q hq,
      coordinate_source q, coordinate_target q hq] at heq
    exact (PolygonDrawing.arc_interiors_disjoint q hq
      ((eventFin q).symm a) ((eventFin q).symm b) hab' s t hs0 hs1 ht0 ht1) heq
  vertices_avoid_arc_interiors := by
    intro v a t ht0 ht1 heq
    rw [coordinate_source q, coordinate_target q hq] at heq
    exact (PolygonDrawing.vertices_avoid_arc_interiors q hq ((vertexFin q).symm v)
      ((eventFin q).symm a) t ht0 ht1) heq
  through_tangents_positive_collinear := by
    intro c i
    simpa [crossingVertexIndex, incomingIndex, outgoingIndex, coordinate,
      sourceIndex, targetIndex, vertexFin, eventFin, crossingFin] using
      (PolygonDrawing.through_tangents_positive_collinear q hq
        ((crossingFin q).symm c) i)
  crossing_transverse := by
    intro c
    simpa [crossingVertexIndex, incomingIndex, coordinate, sourceIndex, vertexFin,
      eventFin, crossingFin] using
      (PolygonDrawing.crossing_transverse q hq ((crossingFin q).symm c))

theorem polygonEventDiagram_vertexPoint (v : Vtx q) :
    (polygonEventDiagram q hq).vertexPoint (vertexFin q v) = PolygonDrawing.vertexPoint q v := by
  simp [polygonEventDiagram, coordinate]

theorem polygonEventDiagram_arcSource (x : Ev q) :
    (polygonEventDiagram q hq).arcSource (eventFin q x) =
      vertexFin q (PolygonDrawing.arcSource q x) := by
  simp [polygonEventDiagram, sourceIndex]

theorem polygonEventDiagram_arcTarget (x : Ev q) :
    (polygonEventDiagram q hq).arcTarget (eventFin q x) =
      vertexFin q (PolygonDrawing.arcTarget q hq x) := by
  simp [polygonEventDiagram, targetIndex]

theorem polygonEventDiagram_crossingVertex (c : Cr q) :
    (polygonEventDiagram q hq).crossingVertex (crossingFin q c) = vertexFin q (Sum.inr c) := by
  simp [polygonEventDiagram, crossingVertexIndex]

theorem polygonEventDiagram_continuation (x : Ev q) :
    (polygonEventDiagram q hq).continuation (eventFin q x) =
      eventFin q (polygonEventSuccessor q hq.g2 x) := by
  simp [polygonEventDiagram, successorArc, eventSuccessor, Equiv.trans_apply]

theorem polygonEventDiagram_arc_card :
    (polygonEventDiagram q hq).nArc = n + 2 * Fintype.card (PolygonCrossing q) := by
  exact polygonEvent_card q









end
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
