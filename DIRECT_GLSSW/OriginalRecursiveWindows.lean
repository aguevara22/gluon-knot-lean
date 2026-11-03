import OriginalSubcycleAugmentation
import CanonicalOriginalInventory

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain MvPolynomial Set

/-- ONE proper original-coordinate exclusion controls new auxiliary choices for
EVERY injective actual original-carrier subcycle, in every geometric open window.
The source consumers produce the subcycle incidence/injectivity; no extracted
polynomial is assumed nonzero or dense. -/
theorem exists_original_coefficient_for_all_subcycle_windows {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∃ c : MvPolynomial (Fin n × Fin 2) ℝ, c ≠ 0 ∧
      Dense {r : Fin n → PlanarPoint ℝ |
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0} ∧
      IsOpen {r : Fin n → PlanarPoint ℝ |
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0} ∧
      ∀ (r : Fin n → PlanarPoint ℝ) (hr : CyclicGeneric r),
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0 →
        GeometricSmoothingWeights.auxiliaryGenericity r hr ∧ actualDaughterSecants r hr ∧
        ∀ (m : ℕ) (d : Fin m → PlanarPoint ℝ) (hd : CyclicGeneric d)
          (f : Fin m → Fin n), Function.Injective f →
          (∀ i, lineValue (polygonCarrierCoordinates r (f i)) (d i) = 0 ∧
            lineValue (polygonCarrierCoordinates r (f i)) (d (cyclicSuccessor i)) = 0) →
          ∀ V : Set CarrierLine, IsOpen V → V.Nonempty → ∃ K ∈ V,
            UniversalLocus (canonicalAugmentedCarrier d K) ∧
            PairTransverse (canonicalAugmentedCarrier d K) ∧
            allCycleSecantExclusions (canonicalAugmentedCarrier d K) := by
  obtain ⟨c,hc,hD,hO,hW⟩ := exists_original_coefficient_with_daughter_inventory q hq
  refine ⟨c,hc,hD,hO,?_⟩
  intro r hr hrc
  obtain ⟨hAux,hSec,_,_,_,hWindow⟩ := hW r hr hrc
  refine ⟨hAux,hSec,?_⟩
  intro m d hd f hf hi V hV hVn
  obtain ⟨K,hK,hT,hU,hC⟩ := hWindow V hV hVn
  exact ⟨K,hK,canonical_augmented_of_original_subcycle r d hd f hf hi K hU hT hC⟩

end DirectGLSSW.CyclicCarrierClearing

