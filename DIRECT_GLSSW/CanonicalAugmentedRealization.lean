import CanonicalCycleTransport
import AugmentedCarrierRealization

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain CarrierScaleTransport Set Filter Topology

/-- Literal old canonical edge lines with one independently specified last line. -/
def canonicalAugmentedCarrier {n : ℕ} (q : Fin n → PlanarPoint ℝ) (K : CarrierLine) :
    Fin (n+1) → CarrierLine := fun i =>
  if h : i.val < n then polygonCarrierCoordinates q ⟨i.val,h⟩ else K

theorem canonicalAugmentedCarrier_eq {n : ℕ} (q : Fin n → PlanarPoint ℝ) (K : CarrierLine)
    (i : Fin (n+1)) : canonicalAugmentedCarrier q K i =
      if h : i.val < n then polygonCarrierCoordinates q ⟨i.val,h⟩ else K := rfl

theorem canonical_augmented_of_supplied {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (K : CarrierLine) (L : Fin (n+1) → CarrierLine)
    (hlast : L (Fin.last n) = K) (hU : UniversalLocus L) (hT : PairTransverse L)
    (hC : allCycleSecantExclusions L)
    (hinc : ∀ i : Fin n, lineValue (L i.castSucc) (q i) = 0 ∧
      lineValue (L i.castSucc) (q (cyclicSuccessor i)) = 0) :
    UniversalLocus (canonicalAugmentedCarrier q K) ∧
      PairTransverse (canonicalAugmentedCarrier q K) ∧
      allCycleSecantExclusions (canonicalAugmentedCarrier q K) := by
  let M : Fin n → CarrierLine := fun i => L i.castSucc
  have hTM : PairTransverse M := pairTransverse_comap L hT Fin.castSucc (Fin.castSucc_injective n)
  obtain ⟨s,hs,he⟩ := exists_supplied_scales q hq M hTM hinc
  let s' : Fin (n+1) → ℝ := fun i => if h : i.val < n then s ⟨i.val,h⟩ else 1
  have hs' : ∀ i, s' i ≠ 0 := by
    intro i
    dsimp [s']
    split <;> simp_all
  have he' : L = fun i => s' i • canonicalAugmentedCarrier q K i := by
    funext i
    by_cases hi : i.val < n
    · have hh := congrFun he (⟨i.val,hi⟩ : Fin n)
      simpa only [M, canonicalAugmentedCarrier, s', dif_pos hi] using hh
    · have hiLast : i = Fin.last n := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
      subst i
      simp [s', canonicalAugmentedCarrier, hlast]
  rw [he'] at hU hT hC
  exact ⟨universalLocus_of_smul _ s' hU, pairTransverse_of_smul _ s' hT,
    allCycleSecantExclusions_of_smul _ s' hs' hT hC⟩

theorem exists_canonical_augmented_realization {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (K : CarrierLine)
    (W : Set ((Fin n → PlanarPoint ℝ) × CarrierLine)) (hW : W ∈ 𝓝 (q,K)) :
    ∃ r K', (r,K') ∈ W ∧ ∃ hr : CyclicGeneric r,
      GeometricSmoothingWeights.auxiliaryGenericity r hr ∧ actualDaughterSecants r hr ∧
      UniversalLocus (canonicalAugmentedCarrier r K') ∧
      PairTransverse (canonicalAugmentedCarrier r K') ∧
      allCycleSecantExclusions (canonicalAugmentedCarrier r K') := by
  obtain ⟨r,K',hW',hr,hAux,hSec,L,hl,hU,hT,hC,hi⟩ := exists_augmented_realization q hq K W hW
  exact ⟨r,K',hW',hr,hAux,hSec,canonical_augmented_of_supplied r hr K' L hl hU hT hC hi⟩

end DirectGLSSW.CyclicCarrierClearing



