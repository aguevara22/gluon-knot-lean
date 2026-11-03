import PositivePolygonAnchorTraversal

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW PermutationOrbits PolygonDrawing
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

private theorem incoming_representation (c : PolygonCrossing q) (i : Fin 2) :
    (positivePolygonEventDiagram q hq).incoming (crossingFin q c) i =
      eventFin q (incoming q hq c i) := by
  simp only [positivePolygonEventDiagram,positiveDiagram,polygonEventDiagram,
    incomingIndex,Equiv.symm_apply_apply]

/-- The first physical carrier has the earlier actual incoming arc. -/
theorem initialAnchorTraversal_incoming_before (c : PolygonCrossing q) :
    rankBefore (visitRank (initialAnchorTraversal q hq)
      ((positivePolygonEventDiagram q hq).incoming (crossingFin q c) 0))
      (visitRank (initialAnchorTraversal q hq)
      ((positivePolygonEventDiagram q hq).incoming (crossingFin q c) 1)) := by
  letI := polygonEventOrder q hq.g2
  have hlt : incoming q hq c 0 < incoming q hq c 1 := by
    apply (polygonEvent_lt_iff q hq.g2 _ _).mpr
    left
    rw [incoming_edge,incoming_edge]
    simpa [visit,polygonEventEdge,crossingVisitEdge] using c.property.1
  right
  constructor
  · apply congrArg (initialAnchorTraversal q hq).componentIndex
    have h0 := ((initialAnchorTraversal q hq).baseArc
      (componentOf (positivePolygonEventDiagram q hq).continuation
        ((positivePolygonEventDiagram q hq).incoming (crossingFin q c) 0))).property
    have h1 := ((initialAnchorTraversal q hq).baseArc
      (componentOf (positivePolygonEventDiagram q hq).continuation
        ((positivePolygonEventDiagram q hq).incoming (crossingFin q c) 1))).property
    exact h0.symm.trans h1
  · change visitPosition _ _ < visitPosition _ _
    rw [incoming_representation,incoming_representation,
      initialAnchorTraversal_visitPosition,initialAnchorTraversal_visitPosition]
    exact (polygonEventEnumeration q hq.g2).symm.strictMono hlt

/-- No supplied traversal-order premise: the lower labelled physical carrier is first. -/
theorem initialAnchorTraversal_firstVisitedBranch (c : PolygonCrossing q) :
    firstVisitedBranch (initialAnchorTraversal q hq) (crossingFin q c)=0 := by
  simp only [firstVisitedBranch,if_pos (initialAnchorTraversal_incoming_before q hq c)]

/-- Initial bad crossings are exactly physical first-under crossings. -/
theorem initialAnchorTraversal_badAt_iff (c : PolygonCrossing q) :
    badAt (initialAnchorTraversal q hq) (crossingFin q c) ↔
      crossingUnder q c=c.val.1 := by
  rw [badAt,initialAnchorTraversal_firstVisitedBranch,positivePolygonEventDiagram_overBranch]
  unfold crossingUnder
  by_cases h : 0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2)
  · simp [h,Ne.symm (crossing_edges_ne q c)]
  · simp [h]

/-- A genuine based traversal at the original zero anchor realizes the initial physical encounter rule. -/
theorem exists_initialAnchorTraversal :
    ∃ T : BasedTraversal (positivePolygonEventDiagram q hq),
      (∀ C, (T.baseArc C).val=eventFin q (initialAnchor q hq)) ∧
      ∀ c : PolygonCrossing q,
        firstVisitedBranch T (crossingFin q c)=0 ∧
        (badAt T (crossingFin q c) ↔ crossingUnder q c=c.val.1) := by
  exact ⟨initialAnchorTraversal q hq,initialAnchorTraversal_baseArc q hq,
    fun c => ⟨initialAnchorTraversal_firstVisitedBranch q hq c,
      initialAnchorTraversal_badAt_iff q hq c⟩⟩
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
