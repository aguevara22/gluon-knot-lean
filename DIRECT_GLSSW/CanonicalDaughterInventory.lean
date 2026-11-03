import CanonicalDaughterGenericity
import SuppliedCycleCaps

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain CarrierScaleTransport DaughterFirstReturn
open GeometricSmoothingWeights

theorem canonical_daughter_supplied_incidence {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
    (hroot : retainedCorner q S root) :
    ∀ i, lineValue (polygonCarrierCoordinates q (daughterCarrier q hq.g2 S root i))
        (daughterVertex q hq.g2 S root i) = 0 ∧
      lineValue (polygonCarrierCoordinates q (daughterCarrier q hq.g2 S root i))
        (daughterVertex q hq.g2 S root (cyclicSuccessor i)) = 0 := by
  intro i
  refine ⟨(DaughterCarrierIntersection.actual_daughter_carrier_intersection q hq S root hroot i).1,?_⟩
  have h := (DaughterCarrierIntersection.actual_daughter_carrier_intersection q hq S root hroot
    (cyclicSuccessor i)).2.1
  have hp : (cyclicSuccessorPerm (Fintype.card (CornerCoord q hq.g2 S root)))⁻¹
      (cyclicSuccessor i) = i :=
    Equiv.symm_apply_apply (cyclicSuccessorPerm _) i
  simpa only [hp] using h

/-- The SAME explicit inventory passes to every actual separating daughter.
Both the daughter domain and its injective carrier list are produced here. -/
theorem canonical_inventory_daughter {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hU : UniversalLocus (polygonCarrierCoordinates q))
    (hT : PairTransverse (polygonCarrierCoordinates q))
    (hC : allCycleSecantExclusions (polygonCarrierCoordinates q))
    (S : Finset (PolygonCrossing q))
    (hS : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (root : PolygonEvent q) (hroot : retainedCorner q S root) :
    ∃ hd : CyclicGeneric (daughterVertex q hq.g2 S root),
      auxiliaryGenericity (daughterVertex q hq.g2 S root) hd ∧
      UniversalLocus (polygonCarrierCoordinates (daughterVertex q hq.g2 S root)) ∧
      PairTransverse (polygonCarrierCoordinates (daughterVertex q hq.g2 S root)) ∧
      allCycleSecantExclusions (polygonCarrierCoordinates (daughterVertex q hq.g2 S root)) := by
  let d := daughterVertex q hq.g2 S root
  let f := daughterCarrier q hq.g2 S root
  have hd : CyclicGeneric d := auxiliaryGenericity_of_canonical_universal q hq hU S hS root
  have hf : Function.Injective f := daughterCarrier_injective q hq.g2 S hq.size_ge_three hS root
  let L := polygonCarrierCoordinates q ∘ f
  have hUL : UniversalLocus L := universalLocus_comap _ hU f hf
  have hTL : PairTransverse L := pairTransverse_comap _ hT f hf
  have hCL : allCycleSecantExclusions L := allCycleSecantExclusions_comap _ hC f hf
  have hi := canonical_daughter_supplied_incidence q hq S root hroot
  have hu := canonical_universal_of_supplied d hd L hUL hTL hi
  have hc := canonical_all_cycles_of_supplied d hd L hTL hCL hi
  exact ⟨hd,auxiliaryGenericity_of_canonical_universal d hd hu.1,hu.1,hu.2,hc⟩

end DirectGLSSW.CyclicCarrierClearing


