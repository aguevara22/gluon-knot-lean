import FixedScaleInventory

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain

/-- The actual good auxiliary line fixes one scale. All sufficiently small
positive truncations at that very scale inherit the entire augmented inventory.
Geometric support/amplitude limits at this scale are separate consumer facts. -/
theorem fixed_scale_inventory_of_good_line {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (K : CarrierLine)
    (a U D : PlanarPoint ℝ) (scale ε₀ : ℝ) (hε : ε₀ ≠ 0)
    (hv : scale • D-U ≠ 0) (hK : K.1 ≠ 0)
    (hA : lineValue K (a+ε₀ • U) = 0)
    (hB : lineValue K (a+(ε₀*scale) • D) = 0)
    (hU : UniversalLocus (canonicalAugmentedCarrier q K))
    (hT : PairTransverse (canonicalAugmentedCarrier q K))
    (hC : allCycleSecantExclusions (canonicalAugmentedCarrier q K)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      UniversalLocus (canonicalAugmentedCarrier q
        (scale • D-U,-planarDet (scale • D-U) (a+ε • U))) ∧
      PairTransverse (canonicalAugmentedCarrier q
        (scale • D-U,-planarDet (scale • D-U) (a+ε • U))) ∧
      allCycleSecantExclusions (canonicalAugmentedCarrier q
        (scale • D-U,-planarDet (scale • D-U) (a+ε • U))) := by
  obtain ⟨s,hs,he⟩ := line_eq_smul_normalized_support K a U D scale ε₀ hε hv hK hA hB
  rw [he] at hU hT hC
  have hi := augmented_inventory_of_last_smul q _ s hs hU hT hC
  exact fixed_direction_inventory_punctured q a U (scale • D-U) ε₀ hi.1 hi.2.1 hi.2.2

end DirectGLSSW.CyclicCarrierClearing

