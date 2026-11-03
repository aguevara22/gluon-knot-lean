import NonalternatingEndpointTransport
import DaughterLiftOrder

set_option autoImplicit false
namespace DirectGLSSW.DaughterDartNonalternation
open DaughterFirstReturn DaughterG2Inheritance DaughterLocalCrossingEquiv DaughterVisitLift
open DaughterEventLift DaughterLiftOrder DaughterOrbitOrder PolygonNonalternation
open PermutationOrbits LocalCoordinates ChordNonalternation FiniteCycleOrder NonalternatingEndpointTransport
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

theorem localEndpoint_liftRank (c : PolygonCrossing (daughterVertex P hP.g2 S root)) (b : Bool) :
    localEndpoint P (DartPerm P hP.g2 S) S (componentOf (DartPerm P hP.g2 S) root) ⟨root,rfl⟩
      (localCrossingEquiv P hP S hS root hroot c,parentSide P hP S root c b) =
      liftRank P hP S hS root hroot (Sum.inr (c,b)) := by
  cases h : parentSide P hP S root c b <;>
    simp [localEndpoint,rootedEnumeration,liftRank,eventRank,eventLift,visitLift,
      localVisitLift,h,localCrossingEquiv_apply]

/-- Actual daughter nonalternation is exactly old dart-fibre nonalternation.
The original false/true labels are explicitly allowed to reverse per crossing. -/
theorem daughter_nonalternating_iff_dartLocal
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root))) :
    polygonNonalternating (daughterVertex P hP.g2 S root)
      (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) T ↔
    Nonalternating (localEndpoint P (DartPerm P hP.g2 S) S
      (componentOf (DartPerm P hP.g2 S) root) ⟨root,rfl⟩)
      (T.map (localCrossingEquiv P hP S hS root hroot).toEmbedding) := by
  classical
  let D := daughterVertex P hP.g2 S root
  let hD := daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root
  letI := polygonEventOrder D hD
  let F := localCrossingEquiv P hP S hS root hroot
  let e := localEndpoint P (DartPerm P hP.g2 S) S
    (componentOf (DartPerm P hP.g2 S) root) ⟨root,rfl⟩
  let e₀ : PolygonCrossing D × Bool → OrbitCoord P hP.g2 S root := fun v => e (F v.1,v.2)
  let flip : PolygonCrossing D → Bool := fun c => parentSide P hP S root c false
  have he₀ : Function.Injective e₀ :=
    (localEndpoint_injective P (DartPerm P hP.g2 S) S _ ⟨root,rfl⟩).comp
      (Equiv.prodCongr F (Equiv.refl Bool)).injective
  have heq : relabelEndpoint e₀ flip =
      fun v => liftRank P hP S hS root hroot (Sum.inr v) := by
    funext v
    rcases v with ⟨c,b⟩
    rw [← localEndpoint_liftRank]
    by_cases h : daughterCarrier P hP.g2 S root c.val.1 < daughterCarrier P hP.g2 S root c.val.2
    · cases b <;> simp [relabelEndpoint,e₀,flip,e,F,parentSide,h]
    · cases b <;> simp [relabelEndpoint,e₀,flip,e,F,parentSide,h]
  have hrank : polygonNonalternating D hD T ↔
      Nonalternating (fun v => liftRank P hP S hS root hroot (Sum.inr v)) T := by
    constructor
    · intro h c hc d hd hcd
      rw [strictCyclicBetween_liftRank,strictCyclicBetween_liftRank]
      exact h c hc d hd hcd
    · intro h c hc d hd hcd
      have hp := h c hc d hd hcd
      rwa [strictCyclicBetween_liftRank,strictCyclicBetween_liftRank] at hp
  rw [nonalternating_map]
  change polygonNonalternating D hD T ↔ Nonalternating e₀ T
  exact hrank.trans (heq ▸ nonalternating_relabel e₀ he₀ flip T)



end
end DirectGLSSW.DaughterDartNonalternation
