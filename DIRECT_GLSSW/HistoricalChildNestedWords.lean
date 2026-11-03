import HistoricalChildRetainedMap
import HistoricalChildNonalternation
import HistoricalChildPairing
import FirstReturnPairing
import FirstReturnOrbitWordReused
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
open ActualLocalSupports LocalCoordinates DaughterFirstReturn
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))




variable (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))



variable (S : Finset (PolygonCrossing (historicalSharpPolygon q hq h c hc R)))

theorem historicalChild_second_firstReturn
    (x : PolygonEvent (historicalSharpPolygon q hq h c hc R)) :
    ∃d : ℕ, 0<d ∧
      (smoothingDartPermutation q hq.g2 (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S)^d)
        (retainedEventMap q hq h c hc R x) =
      retainedEventMap q hq h c hc R
        (smoothingDartPermutation _ (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2 S x) ∧
      ∀k : ℕ, 0<k → k<d →
        (smoothingDartPermutation q hq.g2 (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S)^k)
          (retainedEventMap q hq h c hc R x) ∉ Set.range (retainedEventMap q hq h c hc R) := by
  rw [smoothingDartPermutation_union q hq.g2 _ _
    (historicalChildLift_disjoint q hq h c hc R he hAux S)]
  exact FirstReturnOrbitWord.firstReturn_pairing
    (smoothingDartPermutation q hq.g2 (sharpSupport q hq h c))
    (polygonEventSuccessor _ (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2)
    (retainedEventMap q hq h c hc R)
    (smoothingPairing q (historicalChildLift q hq h c hc R S))
    (smoothingPairing (historicalSharpPolygon q hq h c hc R) S)
    (retainedEventMap_pairing q hq h c hc R he hAux S)
    (historicalChildLift_pairing_fixed_of_not_range q hq h c hc R he hAux S)
    (retainedEventMap_firstReturn q hq h c hc R he hAux) x

theorem historicalChild_second_orbitWord
    (x : PolygonEvent (historicalSharpPolygon q hq h c hc R)) :
    (orbitWord (smoothingDartPermutation _
      (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2 S) x).map
      (retainedEventMap q hq h c hc R) =
    (orbitWord (smoothingDartPermutation q hq.g2
      (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S))
        (retainedEventMap q hq h c hc R x)).filter
      (fun y => decide (y ∈ Set.range (retainedEventMap q hq h c hc R))) :=
  FirstReturnOrbitWord.orbitWord_map_eq_filter _ _ _
    (retainedEventMap_injective q hq h c hc R he hAux)
    (historicalChild_second_firstReturn q hq h c hc R he hAux S) x

theorem historicalChild_second_retained_word
    (x : PolygonEvent (historicalSharpPolygon q hq h c hc R)) :
    ((orbitWord (smoothingDartPermutation _
      (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2 S) x).filter
      (fun y => decide (retainedCorner _ S y))).map (retainedEventMap q hq h c hc R) =
    ((orbitWord (smoothingDartPermutation q hq.g2
      (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S))
        (retainedEventMap q hq h c hc R x)).filter
      (fun y => decide (y ∈ Set.range (retainedEventMap q hq h c hc R)))).filter
      (fun y => decide (retainedCorner q
        (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S) y)) := by
  have heq : (fun y => decide (retainedCorner (historicalSharpPolygon q hq h c hc R) S y)) =
      (fun y => decide (retainedCorner q (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S)
        (retainedEventMap q hq h c hc R y))) := by
    funext y
    exact congrArg (fun p : Prop => decide p)
      (propext (retainedEventMap_retained_iff q hq h c hc R he hAux S y).symm)
  rw [heq]
  have hh := DaughterPointListFilter.map_filter_comp (retainedEventMap q hq h c hc R)
    (fun y => decide (retainedCorner q (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S) y))
    (orbitWord (smoothingDartPermutation _
      (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2 S) x)
  exact hh.trans (congrArg (List.filter (fun y => decide
    (retainedCorner q (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S) y)))
    (historicalChild_second_orbitWord q hq h c hc R he hAux S x))

theorem historicalChild_second_retained_filter
    (hS : PolygonNonalternation.polygonNonalternating _
      (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2 S)
    (x : PolygonEvent (historicalSharpPolygon q hq h c hc R)) :
    ((orbitWord (smoothingDartPermutation q hq.g2
      (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S))
        (retainedEventMap q hq h c hc R x)).filter
      (fun y => decide (y ∈ Set.range (retainedEventMap q hq h c hc R)))).filter
      (fun y => decide (retainedCorner q
        (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S) y)) =
    (orbitWord (smoothingDartPermutation q hq.g2
      (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S))
        (retainedEventMap q hq h c hc R x)).filter
      (fun y => decide (retainedCorner q
        (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S) y)) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro y hy
  by_cases hr : retainedCorner q (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S) y
  · have hcy := (mem_orbitWord_iff _ _ _).mp hy
    have hold := PolygonNonalternation.dart_refines_of_subset q hq.g2 (sharpSupport q hq h c)
      (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S) Finset.subset_union_left
      (historicalChildLift_nonalternating q hq h c hc R he hAux S hS) hcy
    have hcomp := ((componentOf_eq_iff _ _ _).mpr hold).symm.trans
      (retainedEventMap_mem q hq h c hc R x)
    have hR := retained_refinement_event_in_range q hq h c hc R S y hcomp hr
    simp only [hr,hR,decide_true,Bool.true_and]
  · simp only [hr,decide_false,Bool.false_and]

theorem historicalChild_daughterPointList_nested_eq
    (hS : PolygonNonalternation.polygonNonalternating _
      (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2 S)
    (x : PolygonEvent (historicalSharpPolygon q hq h c hc R)) :
    daughterPointList (historicalSharpPolygon q hq h c hc R)
      (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2 S x =
    daughterPointList q hq.g2 (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S)
      (retainedEventMap q hq h c hc R x) := by
  rw [DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map,
    DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map]
  have hh := congrArg (List.map (polygonEventPoint q))
    (historicalChild_second_retained_word q hq h c hc R he hAux S x)
  rw [historicalChild_second_retained_filter q hq h c hc R he hAux S hS x] at hh
  simpa only [List.map_map,Function.comp_def,retainedEventMap_point] using hh
end DirectGLSSW.HOMFLY.ProcessedExposedChild
