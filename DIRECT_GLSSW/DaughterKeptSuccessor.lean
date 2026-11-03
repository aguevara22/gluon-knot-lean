import DaughterLiftOrder

set_option autoImplicit false
namespace DirectGLSSW.DaughterKeptSuccessor
open DaughterFirstReturn DaughterEventLift DaughterKeptEvents DaughterLiftOrder
  DaughterG2Inheritance PolygonNonalternation PermutationOrbits FiniteFirstReturn
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

abbrev KeptCoord := {r : OrbitCoord P hP.g2 S root //
  keptEvent P hP S root (orbitEventAt P hP.g2 S root r)}

instance keptCoordFintype : Fintype (KeptCoord P hP S root) := inferInstance

def keptCoordOrderIso :
    letI := polygonEventOrder (daughterVertex P hP.g2 S root)
      (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root)
    PolygonEvent (daughterVertex P hP.g2 S root) ≃o KeptCoord P hP S root := by
  letI := polygonEventOrder (daughterVertex P hP.g2 S root)
    (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root)
  let f : PolygonEvent (daughterVertex P hP.g2 S root) → KeptCoord P hP S root := fun x =>
    ⟨liftRank P hP S hS root hroot x,by rw [orbitEventAt_liftRank]; exact eventLift_kept P hP S hS root hroot x⟩
  have hf : Function.Injective f := fun _ _ h =>
    (liftRank_strictMono P hP S hS root hroot).injective (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro r
    obtain ⟨x,hx⟩ := (exists_eventLift_iff P hP S hS root hroot _).mpr r.property
    refine ⟨x,Subtype.ext ?_⟩
    apply (orbitEnumeration (DartPerm P hP.g2 S) root).injective
    apply Subtype.ext
    change orbitEventAt P hP.g2 S root (liftRank P hP S hS root hroot x) =
      orbitEventAt P hP.g2 S root r.val
    rw [orbitEventAt_liftRank,hx]
  exact {toEquiv := Equiv.ofBijective f ⟨hf,hs⟩
         map_rel_iff' := (liftRank_strictMono P hP S hS root hroot).le_iff_le}

theorem keptCoordOrderIso_apply (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    (keptCoordOrderIso P hP S hS root hroot x).val = liftRank P hP S hS root hroot x := rfl

theorem keptCoordOrderIso_successor (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    keptCoordOrderIso P hP S hS root hroot
      (polygonEventSuccessor (daughterVertex P hP.g2 S root)
        (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) x) =
      orderedCyclicSuccessor (KeptCoord P hP S root) (keptCoordOrderIso P hP S hS root hroot x) := by
  letI := polygonEventOrder (daughterVertex P hP.g2 S root)
    (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root)
  exact (orderedCyclicSuccessor_naturality _ (keptCoordOrderIso P hP S hS root hroot) x).symm

/-- The actual daughter successor skips exactly omitted original events. -/
theorem eventLift_successor_firstReturn
    (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    ∃ d : ℕ, 0 < d ∧
      (smoothingDartPermutation P hP.g2 S ^ d) (eventLift P hP S hS root hroot x) =
        eventLift P hP S hS root hroot
          (polygonEventSuccessor (daughterVertex P hP.g2 S root)
            (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) x) ∧
      ∀ k : ℕ, 0 < k → k < d → ¬ keptEvent P hP S root
        ((smoothingDartPermutation P hP.g2 S ^ k) (eventLift P hP S hS root hroot x)) := by
  let E := keptCoordOrderIso P hP S hS root hroot
  let next := polygonEventSuccessor (daughterVertex P hP.g2 S root)
    (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) x
  let d := forwardGap (E x).val (E next).val
  have hfr := orderedSubtype_firstReturn
    (fun r : OrbitCoord P hP.g2 S root => keptEvent P hP S root (orbitEventAt P hP.g2 S root r)) (E x)
  have hnext : orderedCyclicSuccessor (KeptCoord P hP S root) (E x) = E next :=
    (keptCoordOrderIso_successor P hP S hS root hroot x).symm
  rw [hnext] at hfr
  rcases hfr with ⟨hd,_,hreach,hno⟩
  refine ⟨d,hd,?_,?_⟩
  · have hiter := orbitEventAt_iterate P hP.g2 S root (E x).val d
    rw [hreach] at hiter
    simpa only [E,keptCoordOrderIso_apply,orbitEventAt_liftRank] using hiter.symm
  · intro k hk0 hkd hkept
    apply hno k hk0 hkd
    change keptEvent P hP S root (orbitEventAt P hP.g2 S root
      ((cyclicSuccessorPerm (orbitCard P hP.g2 S root) ^ k) (E x).val))
    rw [orbitEventAt_iterate]
    simpa only [E,keptCoordOrderIso_apply,orbitEventAt_liftRank] using hkept







end
end DirectGLSSW.DaughterKeptSuccessor
