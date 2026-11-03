import OriginalCarrierTransitivity
import SuppliedCycleCaps

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain MvPolynomial Set
open EdgeAffineNormalization ExtendedReturnArcGeometry InteriorEdgeEvents

/-- An explicit sufficient finite-calculation certificate on a proper
original-coordinate polynomial complement. This is not a definition of, or
an equivalence with, the manuscript's auxiliary domain. -/
theorem exists_original_coefficient_with_subcycle_caps_and_windows {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∃ c : MvPolynomial (Fin n × Fin 2) ℝ, c ≠ 0 ∧
      Dense {r : Fin n → PlanarPoint ℝ |
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0} ∧
      IsOpen {r : Fin n → PlanarPoint ℝ |
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0} ∧
      ∀ (r : Fin n → PlanarPoint ℝ) (hr : CyclicGeneric r),
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0 →
        GeometricSmoothingWeights.auxiliaryGenericity r hr ∧ actualDaughterSecants r hr ∧
        UniversalLocus (polygonCarrierCoordinates r) ∧
        PairTransverse (polygonCarrierCoordinates r) ∧
        allCycleSecantExclusions (polygonCarrierCoordinates r) ∧
        ∀ (m : ℕ) (d : Fin m → PlanarPoint ℝ) (hd : CyclicGeneric d)
          (f : Fin m → Fin n), Function.Injective f →
          (∀ i, lineValue (polygonCarrierCoordinates r (f i)) (d i) = 0 ∧
            lineValue (polygonCarrierCoordinates r (f i)) (d (cyclicSuccessor i)) = 0) →
          GeometricSmoothingWeights.auxiliaryGenericity d hd ∧ actualDaughterSecants d hd ∧
          UniversalLocus (polygonCarrierCoordinates d) ∧
          PairTransverse (polygonCarrierCoordinates d) ∧
          allCycleSecantExclusions (polygonCarrierCoordinates d) ∧
          (∀ e : Fin m,
            let P := normalizedPolygon d e ∘ cyclicVertexEquiv e
            ∃ ε : ℝ, 0 < ε ∧ ε < geometricRadius hd.size_ge_three P ∧
              Set.InjOn (CapCriticalEventGeometry.criticalRoot (extendedArc hd.size_ge_three P ε))
                ↑(CapCriticalTimes.criticalPairs (extendedArc hd.size_ge_three P ε) m) ∧
              ∀ t : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
                ∀ a b : Fin m, a.val < b.val →
                  CyclicGeneric (GlobalCapEntry.lineCapCore
                    (CapCrossingEvent.horizontalMove (extendedArc hd.size_ge_three P ε) (t+s)) a b)) ∧
          ∀ V : Set CarrierLine, IsOpen V → V.Nonempty → ∃ K ∈ V,
            UniversalLocus (canonicalAugmentedCarrier d K) ∧
            PairTransverse (canonicalAugmentedCarrier d K) ∧
            allCycleSecantExclusions (canonicalAugmentedCarrier d K) := by
  obtain ⟨c,hc,hD,hO,hW⟩ := exists_original_coefficient_with_daughter_inventory q hq
  refine ⟨c,hc,hD,hO,?_⟩
  intro r hr hrc
  obtain ⟨hA,hS,hU,hT,hC,hWin⟩ := hW r hr hrc
  refine ⟨hA,hS,hU,hT,hC,?_⟩
  intro m d hd f hf hi
  have hUd := CarrierScaleTransport.canonical_universal_of_supplied d hd
    (polygonCarrierCoordinates r ∘ f) (universalLocus_comap _ hU f hf)
    (pairTransverse_comap _ hT f hf) hi
  have hCd := canonical_all_cycles_of_supplied d hd (polygonCarrierCoordinates r ∘ f)
    (pairTransverse_comap _ hT f hf) (allCycleSecantExclusions_comap _ hC f hf) hi
  refine ⟨auxiliaryGenericity_of_canonical_universal d hd hUd.1,
    actualDaughterSecants_of_canonical_inventory d hd hUd.1 hUd.2 hCd,
    hUd.1,hUd.2,hCd,?_,?_⟩
  · intro e
    exact cap_realization_of_supplied_cycle d hd (polygonCarrierCoordinates r) hT hC f hf hi e
  · intro V hV hVn
    obtain ⟨K,hK,hTK,hUK,hCK⟩ := hWin V hV hVn
    exact ⟨K,hK,canonical_augmented_of_original_subcycle r d hd f hf hi K hUK hTK hCK⟩

end DirectGLSSW.CyclicCarrierClearing

