import PolygonDrawingInteriors

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY.PolygonDrawing

open EventSegmentGeometry

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

def visit (c : PolygonCrossing q) (i : Fin 2) : PolygonEvent q :=
  Sum.inr (c, if i = 0 then false else true)

theorem visit_injective (c : PolygonCrossing q) : Function.Injective (visit q c) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [visit, PolygonEvent, CrossingVisit]

theorem visit_vertex (c : PolygonCrossing q) (i : Fin 2) :
    eventVertex q (visit q c i) = Sum.inr c := rfl

noncomputable def incoming (c : PolygonCrossing q) (i : Fin 2) : PolygonEvent q :=
  (polygonEventSuccessor q hq.g2).symm (visit q c i)

theorem incoming_successor (c : PolygonCrossing q) (i : Fin 2) :
    polygonEventSuccessor q hq.g2 (incoming q hq c i) = visit q c i :=
  (polygonEventSuccessor q hq.g2).apply_symm_apply _

theorem incoming_target (c : PolygonCrossing q) (i : Fin 2) :
    arcTarget q hq (incoming q hq c i) = Sum.inr c := by
  unfold arcTarget
  rw [incoming_successor]
  exact visit_vertex q c i

theorem four_ports_distinct (c : PolygonCrossing q) :
    incoming q hq c 0 ≠ incoming q hq c 1 ∧ visit q c 0 ≠ visit q c 1 ∧
      ∀ i j, incoming q hq c i ≠ visit q c j := by
  have hinj : Function.Injective (incoming q hq c) :=
    (polygonEventSuccessor q hq.g2).symm.injective.comp (visit_injective q c)
  refine ⟨fun h => Fin.zero_ne_one (hinj h),
    fun h => Fin.zero_ne_one (visit_injective q c h), ?_⟩
  intro i j h
  apply arc_endpoints_distinct q hq (visit q c j)
  have htarget := incoming_target q hq c i
  rw [h] at htarget
  exact (visit_vertex q c j).trans htarget.symm

theorem crossing_incidence_complete (c : PolygonCrossing q) (x : PolygonEvent q) :
    (arcSource q x = Sum.inr c ∨ arcTarget q hq x = Sum.inr c) ↔
      (x = incoming q hq c 0 ∨ x = incoming q hq c 1 ∨
        x = visit q c 0 ∨ x = visit q c 1) := by
  have hsource : arcSource q x = Sum.inr c ↔ x = visit q c 0 ∨ x = visit q c 1 := by
    simpa [arcSource, visit] using eventVertex_eq_crossing_iff q x c
  have htarget : arcTarget q hq x = Sum.inr c ↔
      x = incoming q hq c 0 ∨ x = incoming q hq c 1 := by
    unfold arcTarget
    rw [eventVertex_eq_crossing_iff]
    have h0 : (Sum.inr (c,false) : PolygonEvent q) = visit q c 0 := by simp [visit]
    have h1 : (Sum.inr (c,true) : PolygonEvent q) = visit q c 1 := by simp [visit]
    rw [h0,h1]
    constructor
    · rintro (h | h)
      · exact Or.inl (by simpa only [Equiv.symm_apply_apply] using congrArg (polygonEventSuccessor q hq.g2).symm h)
      · exact Or.inr (by simpa only [Equiv.symm_apply_apply] using congrArg (polygonEventSuccessor q hq.g2).symm h)
    · rintro (rfl | rfl) <;> simp only [incoming_successor, or_true, true_or]
  rw [hsource,htarget]
  tauto

theorem incoming_edge (c : PolygonCrossing q) (i : Fin 2) :
    polygonEventEdge q (incoming q hq c i) = polygonEventEdge q (visit q c i) := by
  rcases polygonEventSuccessor_sameEdge_next_or_nextAnchor q hq.g2 hq.size_ge_three
      (incoming q hq c i) with ⟨he,_,_⟩ | ⟨hnext,_⟩
  · rw [incoming_successor] at he
    exact he.symm
  · rw [incoming_successor] at hnext
    simp [visit, PolygonEvent] at hnext

noncomputable def stepScale (x : PolygonEvent q) : ℝ :=
  polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three x -
    polygonEventParameter q x

theorem stepScale_pos (x : PolygonEvent q) : 0 < stepScale q hq x :=
  (polygonEventSuccessor_positive_elementary_step q hq.g2 hq.size_ge_three x).2.2.1

theorem arc_vector_eq (x : PolygonEvent q) :
    vertexPoint q (arcTarget q hq x) - vertexPoint q (arcSource q x) =
      stepScale q hq x • cyclicTangent q (polygonEventEdge q x) := by
  unfold arcTarget arcSource
  rw [vertexPoint_eventVertex,vertexPoint_eventVertex]
  exact (polygonEventSuccessor_positive_elementary_step q hq.g2 hq.size_ge_three x).2.2.2.2

theorem incoming_vector_eq (c : PolygonCrossing q) (i : Fin 2) :
    vertexPoint q (Sum.inr c) - vertexPoint q (arcSource q (incoming q hq c i)) =
      stepScale q hq (incoming q hq c i) • cyclicTangent q (polygonEventEdge q (visit q c i)) := by
  have h := arc_vector_eq q hq (incoming q hq c i)
  rw [incoming_target,incoming_edge] at h
  exact h

theorem through_tangents_positive_collinear (c : PolygonCrossing q) (i : Fin 2) :
    ∃ scale : ℝ, 0 < scale ∧
      vertexPoint q (Sum.inr c) - vertexPoint q (arcSource q (incoming q hq c i)) =
        scale • (vertexPoint q (arcTarget q hq (visit q c i)) - vertexPoint q (Sum.inr c)) := by
  have hin := stepScale_pos q hq (incoming q hq c i)
  have hout := stepScale_pos q hq (visit q c i)
  refine ⟨stepScale q hq (incoming q hq c i) / stepScale q hq (visit q c i),
    div_pos hin hout, ?_⟩
  have hv : vertexPoint q (Sum.inr c) = vertexPoint q (arcSource q (visit q c i)) := rfl
  rw [incoming_vector_eq, hv, arc_vector_eq, smul_smul]
  rw [div_mul_cancel₀ _ (ne_of_gt hout)]

theorem crossing_transverse (c : PolygonCrossing q) :
    planarDet
      (vertexPoint q (Sum.inr c) - vertexPoint q (arcSource q (incoming q hq c 0)))
      (vertexPoint q (Sum.inr c) - vertexPoint q (arcSource q (incoming q hq c 1))) ≠ 0 := by
  rw [incoming_vector_eq,incoming_vector_eq]
  have hdet := DirectGLSSW.crossing_transverse hq.size_ge_three q hq.g1 c
  have hi := ne_of_gt (stepScale_pos q hq (incoming q hq c 0))
  have hj := ne_of_gt (stepScale_pos q hq (incoming q hq c 1))
  have heq : planarDet
      (stepScale q hq (incoming q hq c 0) • cyclicTangent q (polygonEventEdge q (visit q c 0)))
      (stepScale q hq (incoming q hq c 1) • cyclicTangent q (polygonEventEdge q (visit q c 1))) =
      stepScale q hq (incoming q hq c 0) * stepScale q hq (incoming q hq c 1) *
        planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2) := by
    simp [visit,polygonEventEdge,crossingVisitEdge,planarDet]
    ring
  rw [heq]
  exact mul_ne_zero (mul_ne_zero hi hj) hdet

end DirectGLSSW.HOMFLY.PolygonDrawing






