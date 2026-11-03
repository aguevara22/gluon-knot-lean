import PolygonEventPLLinkDiagram
import DirectGLSSW.HOMFLY.PositiveDiagram

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge

open PolygonDrawing

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

theorem polygonEventDiagram_continuation_pow (k : ℕ) (x : Ev q) :
    ((polygonEventDiagram q hq).continuation ^ k) (eventFin q x) =
      eventFin q ((polygonEventSuccessor q hq.g2 ^ k) x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      ih, polygonEventDiagram_continuation]

theorem polygonEventDiagram_isCycleOn :
    (polygonEventDiagram q hq).continuation.IsCycleOn Set.univ := by
  refine ⟨?_, ?_⟩
  · exact (polygonEventDiagram q hq).continuation.bijective.bijOn_univ
  · intro a ha b hb
    obtain ⟨k,hk⟩ := (polygonEventSuccessor_zeroBasedTraversal q hq.g2
      ((eventFin q).symm a)).2 ((eventFin q).symm b)
    refine ⟨(k.val : ℤ), ?_⟩
    rw [zpow_natCast]
    have h := polygonEventDiagram_continuation_pow q hq k.val ((eventFin q).symm a)
    simpa only [Equiv.apply_symm_apply, hk] using h

theorem polygonEventDiagram_componentCount : diagramComponentCount (polygonEventDiagram q hq) = 1 := by
  letI : Nonempty (Fin (polygonEventDiagram q hq).nArc) :=
    ⟨eventFin q (Sum.inl ⟨0, by have := hq.size_ge_three; omega⟩)⟩
  exact PermutationOrbits.componentCount_eq_one _ (polygonEventDiagram_isCycleOn q hq)

theorem polygonEventDiagram_strandTangent (c : Cr q) (i : Fin 2) :
    strandTangent (polygonEventDiagram q hq) (crossingFin q c) i =
      stepScale q hq (incoming q hq c i) •
        cyclicTangent q (polygonEventEdge q (visit q c i)) := by
  simp only [strandTangent, polygonEventDiagram, crossingVertexIndex, incomingIndex,
    sourceIndex, coordinate, Equiv.symm_apply_apply]
  exact incoming_vector_eq q hq c i

theorem polygonEventDiagram_orderedDet (c : Cr q) :
    planarDet (strandTangent (polygonEventDiagram q hq) (crossingFin q c) 0)
      (strandTangent (polygonEventDiagram q hq) (crossingFin q c) 1) =
    (stepScale q hq (incoming q hq c 0) * stepScale q hq (incoming q hq c 1)) *
      planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2) := by
  rw [polygonEventDiagram_strandTangent, polygonEventDiagram_strandTangent]
  simp [visit, polygonEventEdge, crossingVisitEdge, planarDet]
  ring

theorem polygonEventDiagram_orderedDet_pos_iff (c : Cr q) :
    0 < planarDet (strandTangent (polygonEventDiagram q hq) (crossingFin q c) 0)
      (strandTangent (polygonEventDiagram q hq) (crossingFin q c) 1) ↔
      0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2) := by
  rw [polygonEventDiagram_orderedDet]
  exact mul_pos_iff_of_pos_left (mul_pos (stepScale_pos q hq _) (stepScale_pos q hq _))

/-- Internal concrete positive event drawing. Source identification and review
are separate obligations; this is not an author-approved frozen source anchor. -/
noncomputable def positivePolygonEventDiagram : PLLinkDiagram :=
  positiveDiagram (polygonEventDiagram q hq)

theorem positivePolygonEventDiagram_componentCount :
    diagramComponentCount (positivePolygonEventDiagram q hq) = 1 :=
  polygonEventDiagram_componentCount q hq

theorem positivePolygonEventDiagram_crossingSign (c : Fin (positivePolygonEventDiagram q hq).nCrossing) :
    crossingSign (positivePolygonEventDiagram q hq) c = Sign.pos :=
  positiveDiagram_crossingSign (polygonEventDiagram q hq) c

theorem positivePolygonEventDiagram_overBranch (c : Cr q) :
    (positivePolygonEventDiagram q hq).overBranch (crossingFin q c) =
      if 0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2) then 0 else 1 := by
  simp only [positivePolygonEventDiagram, positiveDiagram, positiveOverBranch,
    polygonEventDiagram_orderedDet_pos_iff]

theorem positivePolygonEventDiagram_overEdge (c : Cr q) :
    polygonEventEdge q ((eventFin q).symm
      ((positivePolygonEventDiagram q hq).incoming (crossingFin q c)
        ((positivePolygonEventDiagram q hq).overBranch (crossingFin q c)))) =
      crossingOver q c := by
  rw [positivePolygonEventDiagram_overBranch]
  simp only [positivePolygonEventDiagram, positiveDiagram, polygonEventDiagram,
    incomingIndex, Equiv.symm_apply_apply, incoming_edge]
  unfold crossingOver
  split_ifs <;> simp [visit, polygonEventEdge, crossingVisitEdge]

end DirectGLSSW.HOMFLY.PolygonDrawingBridge







