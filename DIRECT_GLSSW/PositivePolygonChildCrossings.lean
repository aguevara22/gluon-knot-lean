import PositivePolygonVisitCut

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW PermutationOrbits PolygonDrawing Equiv
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

/-- The actual geometric smoothing component containing the middle-interval connector. -/
def positiveSmoothedChildComponent (c : PolygonCrossing q) :
    diagramComponent (smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)) :=
  componentOf (smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).continuation
    (smoothArcEquiv (positivePolygonEventDiagram q hq) (Sum.inr (1 : Fin 2)))

/-- The actual retained crossing label after smoothing a different crossing. -/
def positiveSmoothedCrossing (c d : PolygonCrossing q) (hd : d≠c) :
    Fin (smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).nCrossing :=
  smoothCrossingEquiv (positivePolygonEventDiagram q hq) (crossingFin q c)
    ⟨crossingFin q d,fun h => hd ((crossingFin q).injective h)⟩

private theorem smoothed_incoming (c d : PolygonCrossing q) (hd : d≠c) (i : Fin 2) :
    (smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).incoming
      (positiveSmoothedCrossing q hq c d hd) i =
      smoothArcEquiv (positivePolygonEventDiagram q hq) (Sum.inl (eventFin q (incoming q hq d i))) := by
  change smoothIncoming (positivePolygonEventDiagram q hq) (crossingFin q c)
    (positiveSmoothedCrossing q hq c d hd) i = _
  simp only [positiveSmoothedCrossing,smoothIncoming,Equiv.symm_apply_apply]
  simp only [positivePolygonEventDiagram,positiveDiagram,polygonEventDiagram,incomingIndex,
    Equiv.symm_apply_apply]

/-- Exactly the retained physical crossings with both visits strictly between
c's two visits are self-crossings of the actual detached component. -/
theorem positiveSmoothedChild_selfCrossing_iff (c d : PolygonCrossing q) (hd : d≠c) :
    letI := polygonEventOrder q hq.g2
    (∀ i : Fin 2,
      componentOf (smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).continuation
        ((smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).incoming
          (positiveSmoothedCrossing q hq c d hd) i) = positiveSmoothedChildComponent q hq c) ↔
      visit q c 0 < visit q d 0 ∧ visit q d 1 < visit q c 1 := by
  letI := polygonEventOrder q hq.g2
  have hd01 : visit q d 0 < visit q d 1 :=
    (polygon_incoming_lt_iff_visit_lt q hq d d 0 1).mp (polygon_incoming_zero_lt_one q hq d)
  have hne : visit q d 1 ≠ visit q c 1 := by
    intro he
    apply hd
    exact congrArg Prod.fst (Sum.inr.inj he)
  have hi (i : Fin 2) :
      componentOf (smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).continuation
        ((smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).incoming
          (positiveSmoothedCrossing q hq c d hd) i) = positiveSmoothedChildComponent q hq c ↔
      visit q c 0 < visit q d i ∧ visit q d i ≤ visit q c 1 := by
    rw [smoothed_incoming]
    exact smooth_child_component_incoming_iff q hq c d i
  constructor
  · intro h
    exact ⟨((hi 0).mp (h 0)).1,lt_of_le_of_ne ((hi 1).mp (h 1)).2 hne⟩
  · rintro ⟨h0,h1⟩ i
    apply (hi i).mpr
    fin_cases i
    · exact ⟨h0,(hd01.trans h1).le⟩
    · exact ⟨h0.trans hd01,h1.le⟩
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
