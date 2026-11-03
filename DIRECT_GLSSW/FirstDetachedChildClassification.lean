import FirstDetachedChildMembership
import PositivePolygonChildNoClosing
import ArcPolygonCrossingRange

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open HOMFLY HOMFLY.PolygonDrawingBridge PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- Exhaustive classification of ALL surviving polygon crossings in the actual
first detached component by unique crossings of the literal Split.child.
Closing-edge crossings are excluded by the proved component geometry. -/
theorem firstDetachedChild_all_crossings_iff {a b : ℕ}
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hQ : CyclicGeneric q) (hR : Regular q)
    (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)
    (d : PolygonCrossing q) (hd : d≠polygonCrossingOfArc q c) :
    (∀ i : Fin 2,
      componentOf (smoothCrossing (positivePolygonEventDiagram q hQ)
        (crossingFin q (polygonCrossingOfArc q c))).continuation
        ((smoothCrossing (positivePolygonEventDiagram q hQ)
          (crossingFin q (polygonCrossingOfArc q c))).incoming
          (positiveSmoothedCrossing q hQ (polygonCrossingOfArc q c) d hd) i) =
        positiveSmoothedChildComponent q hQ (polygonCrossingOfArc q c)) ↔
    ∃! e : PolygonCrossing (child q hR c hfirst hcut),
      polygonCrossingOfArc q (childCrossingToOriginal q hR c hfirst hcut e)=d := by
  constructor
  · intro hself
    have hlast := positiveSmoothedChild_no_closing_edge q hQ c d hd hself
    obtain ⟨e,rfl⟩ := (polygonCrossingOfArc_range q d).mpr hlast
    have hec : e≠c := fun h => hd (congrArg (polygonCrossingOfArc q) h)
    obtain ⟨z,hz,hu⟩ := (firstDetachedChild_crossing_iff q hQ hR c e hfirst hcut hec).mp hself
    refine ⟨z,congrArg (polygonCrossingOfArc q) hz,?_⟩
    intro z' hz'
    exact hu z' (ActiveArc.polygonCrossingOfArc_injective q hz')
  · rintro ⟨z,rfl,_⟩
    have hec : childCrossingToOriginal q hR c hfirst hcut z≠c :=
      fun h => hd (congrArg (polygonCrossingOfArc q) h)
    apply (firstDetachedChild_crossing_iff q hQ hR c
      (childCrossingToOriginal q hR c hfirst hcut z) hfirst hcut hec).mpr
    refine ⟨z,rfl,?_⟩
    intro z' hz'
    exact childCrossingToOriginal_injective q hR c hfirst hcut hz'
end DirectGLSSW.ActiveArc.Split
