import FirstReturnOrbitWord
import DaughterSecondReturn

set_option autoImplicit false
namespace DirectGLSSW.DaughterSecondWord
open DaughterFirstReturn DaughterEventLift DaughterKeptEvents DaughterPairingLift
  DaughterSecondReturn DaughterG2Inheritance PolygonNonalternation PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

theorem secondStage_firstReturn_range
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    ∃ d : ℕ, 0 < d ∧
      (smoothingDartPermutation P hP.g2 (S ∪ liftedSupport P hP S hS root hroot T) ^ d)
          (eventLift P hP S hS root hroot x) =
        eventLift P hP S hS root hroot
          (smoothingDartPermutation (daughterVertex P hP.g2 S root)
            (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) T x) ∧
      ∀ k : ℕ, 0 < k → k < d → ¬ Set.range (eventLift P hP S hS root hroot)
        ((smoothingDartPermutation P hP.g2 (S ∪ liftedSupport P hP S hS root hroot T) ^ k)
          (eventLift P hP S hS root hroot x)) := by
  obtain ⟨d,hd,hr,hn⟩ := secondStage_firstReturn P hP S hS root hroot T x
  refine ⟨d,hd,hr,?_⟩
  intro k hk0 hkd hy
  exact hn k hk0 hkd ((exists_eventLift_iff P hP S hS root hroot _).mp hy)

theorem secondStage_word
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    (orbitWord (smoothingDartPermutation (daughterVertex P hP.g2 S root)
        (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) T) x).map
        (eventLift P hP S hS root hroot) =
      (orbitWord (smoothingDartPermutation P hP.g2 (S ∪ liftedSupport P hP S hS root hroot T))
        (eventLift P hP S hS root hroot x)).filter (fun y => decide (keptEvent P hP S root y)) := by
  have h := FirstReturnOrbitWord.orbitWord_map_eq_filter _ _
    (eventLift P hP S hS root hroot) (eventLift_injective P hP S hS root hroot)
    (secondStage_firstReturn_range P hP S hS root hroot T) x
  have heq : (fun y => decide (y ∈ Set.range (eventLift P hP S hS root hroot))) =
      (fun y => decide (keptEvent P hP S root y)) := by
    funext y
    apply decide_eq_decide.mpr
    exact exists_eventLift_iff P hP S hS root hroot y
  rw [heq] at h
  exact h

theorem secondStage_retained_word
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    ((orbitWord (smoothingDartPermutation (daughterVertex P hP.g2 S root)
        (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) T) x).filter
        (fun y => decide (retainedCorner (daughterVertex P hP.g2 S root) T y))).map
        (eventLift P hP S hS root hroot) =
      ((orbitWord (smoothingDartPermutation P hP.g2 (S ∪ liftedSupport P hP S hS root hroot T))
        (eventLift P hP S hS root hroot x)).filter (fun y => decide (keptEvent P hP S root y))).filter
        (fun y => decide (retainedCorner P (S ∪ liftedSupport P hP S hS root hroot T) y)) := by
  have heq : (fun y => decide (retainedCorner (daughterVertex P hP.g2 S root) T y)) =
      (fun y => decide (retainedCorner P (S ∪ liftedSupport P hP S hS root hroot T)
        (eventLift P hP S hS root hroot y))) := by
    funext y
    exact congrArg (fun p : Prop => decide p) (propext (eventLift_retained_union_iff P hP S hS root hroot T y))
  rw [heq]
  have hm := DaughterPointListFilter.map_filter_comp (eventLift P hP S hS root hroot)
    (fun y => decide (retainedCorner P (S ∪ liftedSupport P hP S hS root hroot T) y))
    (orbitWord (smoothingDartPermutation (daughterVertex P hP.g2 S root)
      (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) T) x)
  rw [secondStage_word] at hm
  exact hm

theorem secondStage_pointList_filtered
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    daughterPointList (daughterVertex P hP.g2 S root)
      (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) T x =
      (((orbitWord (smoothingDartPermutation P hP.g2 (S ∪ liftedSupport P hP S hS root hroot T))
        (eventLift P hP S hS root hroot x)).filter (fun y => decide (keptEvent P hP S root y))).filter
        (fun y => decide (retainedCorner P (S ∪ liftedSupport P hP S hS root hroot T) y))).map
          (polygonEventPoint P) := by
  rw [DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map]
  have h := congrArg (List.map (polygonEventPoint P)) (secondStage_retained_word P hP S hS root hroot T x)
  simpa only [List.map_map,Function.comp_def,eventLift_point] using h





end
end DirectGLSSW.DaughterSecondWord
