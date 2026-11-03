import FirstDetachedChildCrossingEquiv

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open DirectGLSSW HOMFLY PolygonDrawingBridge
attribute [local instance] Classical.propDecidable

variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
  (hQ : CyclicGeneric q) (hR : ActiveArc.Regular q)
  (c : ActiveArc.Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)

/-- An exact component restriction has precisely the actual child crossing count. -/
theorem firstDetachedChildRestriction_nCrossing_eq_card
    (R : HOMFLY.LowestRowContract.ComponentRestriction
      (HOMFLY.smoothCrossing (positivePolygonEventDiagram q hQ)
        (crossingFin q (ActiveArc.polygonCrossingOfArc q c)))
      (positiveSmoothedChildComponent q hQ (ActiveArc.polygonCrossingOfArc q c))) :
    R.diagram.nCrossing = Fintype.card (PolygonCrossing (child q hR c hfirst hcut)) := by
  let E := firstDetachedChildRestrictionCrossingEquiv q hQ hR c hfirst hcut R
  calc
    R.diagram.nCrossing = Fintype.card (Fin R.diagram.nCrossing) := by simp
    _ = Fintype.card (PolygonCrossing (child q hR c hfirst hcut)) := Fintype.card_congr E

/-- The first detached component has strictly fewer crossings than the original
positive event diagram: its exact component-crossing subtype sits inside the
smoothed diagram, and smoothing removes the selected crossing. -/
theorem firstDetachedChildRestriction_nCrossing_lt
    (R : HOMFLY.LowestRowContract.ComponentRestriction
      (HOMFLY.smoothCrossing (positivePolygonEventDiagram q hQ)
        (crossingFin q (ActiveArc.polygonCrossingOfArc q c)))
      (positiveSmoothedChildComponent q hQ (ActiveArc.polygonCrossingOfArc q c))) :
    R.diagram.nCrossing < (positivePolygonEventDiagram q hQ).nCrossing := by
  have hsub : R.diagram.nCrossing ≤ (HOMFLY.smoothCrossing (positivePolygonEventDiagram q hQ)
      (crossingFin q (ActiveArc.polygonCrossingOfArc q c))).nCrossing := by
    have hcard := Fintype.card_le_of_injective
      (fun x : Fin R.diagram.nCrossing => (R.crossingEquiv x).val)
      (by
        intro x y h
        exact R.crossingEquiv.injective (Subtype.ext h))
    simpa using hcard
  have hdrop := HOMFLY.smoothCrossing_crossing_count_drop
    (positivePolygonEventDiagram q hQ) (crossingFin q (ActiveArc.polygonCrossingOfArc q c))
  change R.diagram.nCrossing ≤
    (HOMFLY.smoothCrossing (positivePolygonEventDiagram q hQ)
      (crossingFin q (ActiveArc.polygonCrossingOfArc q c))).nCrossing at hsub
  omega

end DirectGLSSW.ActiveArc.Split
