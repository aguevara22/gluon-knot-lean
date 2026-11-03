import DaughterSecondWord
import DaughterAffectedComponents

set_option autoImplicit false
namespace DirectGLSSW.DaughterNestedPointList
open DaughterFirstReturn DaughterEventLift DaughterKeptEvents DaughterPairingLift
  DaughterSecondWord DaughterAffectedComponents DaughterG2Inheritance PolygonNonalternation PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

theorem orbit_retained_kept
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (x : PolygonEvent (daughterVertex P hP.g2 S root)) (y : PolygonEvent P)
    (hy : y ∈ orbitWord (smoothingDartPermutation P hP.g2 (S ∪ liftedSupport P hP S hS root hroot T))
      (eventLift P hP S hS root hroot x))
    (hr : retainedCorner P (S ∪ liftedSupport P hP S hS root hroot T) y) :
    keptEvent P hP S root y := by
  apply retained_final_kept P hP S hS root hroot T y hr
  have hc := (componentOf_eq_iff _ _ _).mpr ((mem_orbitWord_iff _ _ _).mp hy)
  have ho := congrArg (oldComponentOfFinal P hP S hS root hroot T) hc
  exact ho.symm.trans (eventLift_component P hP S hS root hroot x)

theorem retained_filter_eq
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    ((orbitWord (smoothingDartPermutation P hP.g2 (S ∪ liftedSupport P hP S hS root hroot T))
      (eventLift P hP S hS root hroot x)).filter (fun y => decide (keptEvent P hP S root y))).filter
        (fun y => decide (retainedCorner P (S ∪ liftedSupport P hP S hS root hroot T) y)) =
      (orbitWord (smoothingDartPermutation P hP.g2 (S ∪ liftedSupport P hP S hS root hroot T))
        (eventLift P hP S hS root hroot x)).filter
          (fun y => decide (retainedCorner P (S ∪ liftedSupport P hP S hS root hroot T) y)) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro y hy
  by_cases hr : retainedCorner P (S ∪ liftedSupport P hP S hS root hroot T) y
  · have hk := orbit_retained_kept P hP S hS root hroot T x y hy hr
    simp [hr,hk]
  · simp [hr]

/-- The literal second-stage retained polygon is exactly the original
union-support polygon, rooted at the lifted event. -/
theorem daughterPointList_nested_eq
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    daughterPointList (daughterVertex P hP.g2 S root)
      (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) T x =
    daughterPointList P hP.g2 (S ∪ liftedSupport P hP S hS root hroot T)
      (eventLift P hP S hS root hroot x) := by
  rw [secondStage_pointList_filtered,retained_filter_eq,
    DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map]




end
end DirectGLSSW.DaughterNestedPointList
