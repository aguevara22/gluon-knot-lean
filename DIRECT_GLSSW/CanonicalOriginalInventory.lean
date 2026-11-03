import OriginalVertexAuxiliaryWindows
import CanonicalDaughterSecants

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain GeometricSmoothingWeights MvPolynomial Set

theorem original_inventory_of_augmented {n : ℕ} (q : Fin n → PlanarPoint ℝ) (K : CarrierLine)
    (hU : UniversalLocus (canonicalAugmentedCarrier q K))
    (hT : PairTransverse (canonicalAugmentedCarrier q K))
    (hC : allCycleSecantExclusions (canonicalAugmentedCarrier q K)) :
    UniversalLocus (polygonCarrierCoordinates q) ∧ PairTransverse (polygonCarrierCoordinates q) ∧
      allCycleSecantExclusions (polygonCarrierCoordinates q) := by
  have he : canonicalAugmentedCarrier q K ∘ (Fin.castSucc : Fin n → Fin (n+1)) =
      polygonCarrierCoordinates q := by
    funext i
    simp [canonicalAugmentedCarrier]
  have hu := universalLocus_comap _ hU Fin.castSucc (Fin.castSucc_injective n)
  have ht := pairTransverse_comap _ hT Fin.castSucc (Fin.castSucc_injective n)
  have hc := allCycleSecantExclusions_comap _ hC Fin.castSucc (Fin.castSucc_injective n)
  simpa only [he] using And.intro hu (And.intro ht hc)

/-- A proper original-coordinate exclusion simultaneously supplies all actual
separating daughter domains and secants, plus a good augmented line in every
open geometric window. No auxiliary predicate is selected or defined here. -/
theorem exists_original_coefficient_with_daughter_inventory {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∃ c : MvPolynomial (Fin n × Fin 2) ℝ, c ≠ 0 ∧
      Dense {r : Fin n → PlanarPoint ℝ |
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0} ∧
      IsOpen {r : Fin n → PlanarPoint ℝ |
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0} ∧
      ∀ (r : Fin n → PlanarPoint ℝ) (hr : CyclicGeneric r),
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0 →
        auxiliaryGenericity r hr ∧ actualDaughterSecants r hr ∧
        UniversalLocus (polygonCarrierCoordinates r) ∧
        PairTransverse (polygonCarrierCoordinates r) ∧
        allCycleSecantExclusions (polygonCarrierCoordinates r) ∧
        ∀ V : Set CarrierLine, IsOpen V → V.Nonempty → ∃ K ∈ V,
          PairTransverse (canonicalAugmentedCarrier r K) ∧
          UniversalLocus (canonicalAugmentedCarrier r K) ∧
          allCycleSecantExclusions (canonicalAugmentedCarrier r K) := by
  obtain ⟨c,hc,hD,hO,hW⟩ := exists_original_vertex_coefficient_and_windows q hq
  refine ⟨c,hc,hD,hO,?_⟩
  intro r hr hrc
  obtain ⟨K,_,hT,hU,hC⟩ := hW r hrc Set.univ isOpen_univ ⟨0,Set.mem_univ _⟩
  have hi := original_inventory_of_augmented r K hU hT hC
  exact ⟨auxiliaryGenericity_of_canonical_universal r hr hi.1,
    actualDaughterSecants_of_canonical_inventory r hr hi.1 hi.2.1 hi.2.2,
    hi.1,hi.2.1,hi.2.2,hW r hrc⟩

end DirectGLSSW.CyclicCarrierClearing


