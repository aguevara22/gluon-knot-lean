import TruncatedCarrierInjection
import CanonicalDaughterSecants

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain CarrierScaleTransport TruncationDirection
open GeometricSmoothingWeights

/-- The actual truncated polygon consumes the augmented-family inventory.
Genericity and new-line endpoint incidence are produced by the geometric window
lemma; neither is hidden in the carrier list. -/
theorem truncated_canonical_inventory {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (a p : Fin n) (hp : cyclicSuccessor p = a) (scale ε : ℝ) (K : CarrierLine)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (hleft : lineValue K (q a+ε • (q p-q a)) = 0)
    (hright : lineValue K (q a+(ε*scale) • (q (cyclicSuccessor a)-q a)) = 0)
    (hU : UniversalLocus (canonicalAugmentedCarrier q K))
    (hT : PairTransverse (canonicalAugmentedCarrier q K))
    (hC : allCycleSecantExclusions (canonicalAugmentedCarrier q K)) :
    auxiliaryGenericity (truncateCyclicCorner q a p scale ε) hQ ∧
      actualDaughterSecants (truncateCyclicCorner q a p scale ε) hQ ∧
      UniversalLocus (polygonCarrierCoordinates (truncateCyclicCorner q a p scale ε)) ∧
      PairTransverse (polygonCarrierCoordinates (truncateCyclicCorner q a p scale ε)) ∧
      allCycleSecantExclusions (polygonCarrierCoordinates (truncateCyclicCorner q a p scale ε)) := by
  let Q := truncateCyclicCorner q a p scale ε
  let L := canonicalAugmentedCarrier q K ∘ truncatedCarrierLabel a
  have hi := truncated_augmented_carrier_incidence q a p hp scale ε K hleft hright
  have hUL : UniversalLocus L := universalLocus_comap _ hU _ (truncatedCarrierLabel_injective a)
  have hTL : PairTransverse L := pairTransverse_comap _ hT _ (truncatedCarrierLabel_injective a)
  have hCL : allCycleSecantExclusions L := allCycleSecantExclusions_comap _ hC _ (truncatedCarrierLabel_injective a)
  have hu := canonical_universal_of_supplied Q hQ L hUL hTL hi
  have hc := canonical_all_cycles_of_supplied Q hQ L hTL hCL hi
  exact ⟨auxiliaryGenericity_of_canonical_universal Q hQ hu.1,
    actualDaughterSecants_of_canonical_inventory Q hQ hu.1 hu.2 hc,hu.1,hu.2,hc⟩

end DirectGLSSW.CyclicCarrierClearing

