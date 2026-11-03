import CanonicalDaughterInventory
import ActualDaughterCapRealization

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain DaughterFirstReturn GeometricSmoothingWeights

theorem actualDaughterSecants_of_canonical_inventory {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hU : UniversalLocus (polygonCarrierCoordinates q))
    (hT : PairTransverse (polygonCarrierCoordinates q))
    (hC : allCycleSecantExclusions (polygonCarrierCoordinates q)) : actualDaughterSecants q hq := by
  intro S hS root hroot
  have hd := auxiliaryGenericity_of_canonical_universal q hq hU S hS root
  exact actual_secants_of_supplied_cycle (daughterVertex q hq.g2 S root) hd
    (polygonCarrierCoordinates q) hT hC (daughterCarrier q hq.g2 S root)
    (daughterCarrier_injective q hq.g2 S hq.size_ge_three hS root)
    (canonical_daughter_supplied_incidence q hq S root hroot)

end DirectGLSSW.CyclicCarrierClearing

