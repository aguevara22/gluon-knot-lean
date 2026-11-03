import DaughterLiftParameters
import DaughterOrbitOrder

set_option autoImplicit false
namespace DirectGLSSW.DaughterLiftOrder
open DaughterFirstReturn DaughterEventLift DaughterLiftParameters DaughterOrbitOrder
  DaughterG2Inheritance PolygonNonalternation PermutationOrbits FiniteCycleOrder
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

def liftRank (x : PolygonEvent (daughterVertex P hP.g2 S root)) : OrbitCoord P hP.g2 S root :=
  eventRank P hP S root (eventLift P hP S hS root hroot x)
    (eventLift_component P hP S hS root hroot x)

theorem orbitEventAt_liftRank (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    orbitEventAt P hP.g2 S root (liftRank P hP S hS root hroot x) =
      eventLift P hP S hS root hroot x := orbitEventAt_eventRank P hP S root _ _

/-- Actual daughter event order embeds in its old component's actual traversal. -/
theorem liftRank_strictMono :
    letI := polygonEventOrder (daughterVertex P hP.g2 S root)
      (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root)
    StrictMono (liftRank P hP S hS root hroot) := by
  letI := polygonEventOrder (daughterVertex P hP.g2 S root)
    (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root)
  intro x y hxy
  rcases (polygonEvent_lt_iff _ _ x y).mp hxy with he | ⟨he,hparam⟩
  · exact eventRank_lt_of_carrier_lt P hP S root hS hroot _ _
      (eventLift_component P hP S hS root hroot x)
      (eventLift_component P hP S hS root hroot y) _ _
      (eventLift_carrier P hP S hS root hroot x)
      (eventLift_carrier P hP S hS root hroot y) he
  · have hey : polygonEventEdge P (eventLift P hP S hS root hroot y) =
        daughterCarrier P hP.g2 S root (polygonEventEdge (daughterVertex P hP.g2 S root) x) := by
      rw [eventLift_carrier,he]
    apply (eventRank_lt_iff_parameter_lt P hP S root hS hroot _ _
      (eventLift_component P hP S hS root hroot x)
      (eventLift_component P hP S hS root hroot y) _
      (eventLift_carrier P hP S hS root hroot x) hey).mpr
    exact (eventLift_parameter_lt_iff P hP S hS root hroot x y he).mpr hparam

def liftRankEmbedding :
    letI := polygonEventOrder (daughterVertex P hP.g2 S root)
      (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root)
    PolygonEvent (daughterVertex P hP.g2 S root) ↪o OrbitCoord P hP.g2 S root := by
  letI := polygonEventOrder (daughterVertex P hP.g2 S root)
    (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root)
  exact {toFun := liftRank P hP S hS root hroot
         inj' := (liftRank_strictMono P hP S hS root hroot).injective
         map_rel_iff' := (liftRank_strictMono P hP S hS root hroot).le_iff_le}

theorem strictCyclicBetween_liftRank
    (x y z : PolygonEvent (daughterVertex P hP.g2 S root)) :
    letI := polygonEventOrder (daughterVertex P hP.g2 S root)
      (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root)
    strictCyclicBetween (liftRank P hP S hS root hroot x)
      (liftRank P hP S hS root hroot y) (liftRank P hP S hS root hroot z) ↔
      strictCyclicBetween x y z := by
  letI := polygonEventOrder (daughterVertex P hP.g2 S root)
    (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root)
  simp only [strictCyclicBetween,(liftRank_strictMono P hP S hS root hroot).lt_iff_lt]






end
end DirectGLSSW.DaughterLiftOrder
