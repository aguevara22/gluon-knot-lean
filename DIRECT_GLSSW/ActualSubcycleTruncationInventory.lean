import FiniteCalculationCertificate
import TruncationLineWindow
import TruncatedCanonicalInventory
import SupportedSourceTruncation

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.SourceSubcycleTruncationComposition

open DirectGLSSW DirectGLSSW.CyclicCarrierClearing
  DirectGLSSW.SourceTruncationLineWindow DirectGLSSW.SourceTruncationSupport
  DirectGLSSW.ExposedOpenPrimitive DirectGLSSW.EdgeAffineNormalization
  DirectGLSSW.ExtendedReturnArcGeometry DirectGLSSW.CapCriticalEventGeometry
  DirectGLSSW.CapCriticalTimes DirectGLSSW.CapCrossingEvent DirectGLSSW.GlobalCapEntry
  GeometricSmoothingWeights UniversalCarrierDomain AuxiliaryCarrierChart TruncationDirection
  Filter Topology MvPolynomial Set

private theorem exists_supported_truncation_in_windows
    (hRI : GLSSWRootIndependence) {m : ℕ}
    (d : Fin m → PlanarPoint ℝ) (hd : CyclicGeneric d)
    (hAux : auxiliaryGenericity d hd)
    (a p : Fin m) (hp : cyclicSuccessor p = a)
    (hturn : 0 < planarDet (d a-d p) (d (cyclicSuccessor a)-d a))
    (v : PlanarPoint ℝ)
    (hexposed : ∀ i : Fin m, i ≠ a → 0 < planarDet v (d i-d a))
    (hWindows : ∀ V : Set CarrierLine, IsOpen V → V.Nonempty →
      ∃ K ∈ V, UniversalLocus (canonicalAugmentedCarrier d K) ∧
        PairTransverse (canonicalAugmentedCarrier d K) ∧
        allCycleSecantExclusions (canonicalAugmentedCarrier d K)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ scale : ℝ, 0 < scale ∧
      ε < 1 ∧ ε*scale < 1 ∧
      ∃ hQ : CyclicGeneric (truncateCyclicCorner d a p scale ε),
      ∃ hAuxQ : auxiliaryGenericity (truncateCyclicCorner d a p scale ε) hQ,
        LeftExposed (truncateCyclicCorner d a p scale ε) a.castSucc ∧
        actualDaughterSecants (truncateCyclicCorner d a p scale ε) hQ ∧
        UniversalLocus (polygonCarrierCoordinates (truncateCyclicCorner d a p scale ε)) ∧
        PairTransverse (polygonCarrierCoordinates (truncateCyclicCorner d a p scale ε)) ∧
        allCycleSecantExclusions (polygonCarrierCoordinates (truncateCyclicCorner d a p scale ε)) ∧
        ∃ K : CarrierLine,
          lineValue K (truncateCyclicCorner d a p scale ε a.castSucc)=0 ∧
          lineValue K (truncateCyclicCorner d a p scale ε
            ⟨a.val+1, by have := a.isLt; omega⟩)=0 ∧
          UniversalLocus (canonicalAugmentedCarrier d K) ∧
          PairTransverse (canonicalAugmentedCarrier d K) ∧
          allCycleSecantExclusions (canonicalAugmentedCarrier d K) := by
  obtain ⟨scale,hs,δ,hδ,hSupported⟩ :=
    exists_exposed_corner_truncation_with_support_data hRI d hd hAux a p hp hturn v hexposed
  let ε0 := δ/2
  have hε0 : 0 < ε0 := by dsimp [ε0]; linarith
  have hε0δ : ε0 < δ := by dsimp [ε0]; linarith
  obtain ⟨hε01,hε0s1,hQ0,hAuxQ0,_hAmp,_hSum,_hAmpParity,_hSumParity,hLeft0,
      _E,_hLabels,_hPoints,_hSupportEq,_hDaughterAmp⟩ := hSupported ε0 hε0 hε0δ
  let U : PlanarPoint ℝ := d p-d a
  let D : PlanarPoint ℝ := d (cyclicSuccessor a)-d a
  let v0 : PlanarPoint ℝ := scale • D-U
  let K0 : CarrierLine := (v0,-planarDet v0 (d a+ε0 • U))
  let recoveredEpsilon : CarrierLine → ℝ := fun K =>
    -lineValue K (d a) / planarDet K.1 U
  let recoveredScale : CarrierLine → ℝ := fun K =>
    planarDet K.1 U / planarDet K.1 D
  let truncation : CarrierLine → Fin (m+1) → PlanarPoint ℝ := fun K =>
    truncateCyclicCorner d a p (recoveredScale K) (recoveredEpsilon K)
  obtain ⟨W,hWopen,hK0,hLine⟩ :=
    exists_open_supported_truncation_line_window d hd a p hp hturn scale ε0 hs hε0
      hε01 hε0s1 hQ0 hLeft0
  obtain ⟨K,hKW,hU,hT,hC⟩ := hWindows W hWopen ⟨K0,hK0⟩
  have hWindowK := hLine K hKW
  rcases hWindowK with ⟨hE,hE1,hScale,hProd,hProd1,hQgeneric,hLeftK,hAnchor,hNew⟩
  have hAnchor' : lineValue K
      (truncateCyclicCorner d a p (recoveredScale K) (recoveredEpsilon K) a.castSucc)=0 := by
    change lineValue K (truncateCyclicCorner d a p (recoveredScale K)
      (recoveredEpsilon K) a.castSucc)=0 at hAnchor
    exact hAnchor
  have hNew' : lineValue K
      (truncateCyclicCorner d a p (recoveredScale K) (recoveredEpsilon K)
        ⟨a.val+1, by have := a.isLt; omega⟩)=0 := by
    change lineValue K (truncateCyclicCorner d a p (recoveredScale K)
      (recoveredEpsilon K) ⟨a.val+1, by have := a.isLt; omega⟩)=0 at hNew
    exact hNew
  have hleft : lineValue K (d a+recoveredEpsilon K • (d p-d a))=0 := by
    have hi : (a.castSucc : Fin (m+1)) = (⟨a.val, by have := a.isLt; omega⟩ : Fin (m+1)) := rfl
    rw [hi,truncateCyclicCorner_anchor] at hAnchor'
    exact hAnchor'
  have hright : lineValue K
      (d a+(recoveredEpsilon K*recoveredScale K) •
        (d (cyclicSuccessor a)-d a))=0 := by
    rw [truncateCyclicCorner_new] at hNew'
    exact hNew'
  have hInv := truncated_canonical_inventory d a p hp (recoveredScale K)
    (recoveredEpsilon K) K hQgeneric hleft hright hU hT hC
  rcases hInv with ⟨hAuxActual,hDaughtersActual,hUactual,hTactual,hCactual⟩
  refine ⟨recoveredEpsilon K,hE,recoveredScale K,hScale,hE1,hProd1,
    hQgeneric,hAuxActual,hLeftK,hDaughtersActual,hUactual,hTactual,hCactual,
    K,?_,?_,hU,hT,hC⟩
  · change lineValue K (truncateCyclicCorner d a p (recoveredScale K)
      (recoveredEpsilon K) a.castSucc)=0
    exact hAnchor
  · change lineValue K (truncateCyclicCorner d a p (recoveredScale K)
      (recoveredEpsilon K) ⟨a.val+1, by have := a.isLt; omega⟩)=0
    exact hNew

/-- One coefficient controls actual original-coordinate polygons and every
actual injective original-carrier subcycle. On each subcycle, every open new
carrier-line window can be used to produce a supported generic truncation
with the full canonical and daughter inventory. Subcycle incidence is kept as
an explicit source premise until a recursive-carrier provenance theorem is
consumed. -/
theorem exists_original_coefficient_with_supported_subcycle_truncations
    (hRI : GLSSWRootIndependence) {n : ℕ}
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
        ∀ (m : ℕ) (d : Fin m → PlanarPoint ℝ) (hd : CyclicGeneric d)
          (f : Fin m → Fin n), Function.Injective f →
          (∀ i, lineValue (polygonCarrierCoordinates r (f i)) (d i)=0 ∧
            lineValue (polygonCarrierCoordinates r (f i)) (d (cyclicSuccessor i))=0) →
          auxiliaryGenericity d hd ∧ actualDaughterSecants d hd ∧
          UniversalLocus (polygonCarrierCoordinates d) ∧
          PairTransverse (polygonCarrierCoordinates d) ∧
          allCycleSecantExclusions (polygonCarrierCoordinates d) ∧
          (∀ e : Fin m,
            let P := normalizedPolygon d e ∘ cyclicVertexEquiv e
            ∃ ε : ℝ, 0 < ε ∧ ε < geometricRadius hd.size_ge_three P ∧
              Set.InjOn (criticalRoot (extendedArc hd.size_ge_three P ε))
                ↑(criticalPairs (extendedArc hd.size_ge_three P ε) m) ∧
              ∀ t : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
                ∀ a b : Fin m, a.val < b.val →
                  CyclicGeneric (lineCapCore (horizontalMove (extendedArc hd.size_ge_three P ε) (t+s)) a b)) ∧
          (∀ V : Set CarrierLine, IsOpen V → V.Nonempty →
            ∃ K ∈ V, UniversalLocus (canonicalAugmentedCarrier d K) ∧
              PairTransverse (canonicalAugmentedCarrier d K) ∧
              allCycleSecantExclusions (canonicalAugmentedCarrier d K)) ∧
          ∀ (a p : Fin m) (hp : cyclicSuccessor p = a)
            (hturn : 0 < planarDet (d a-d p) (d (cyclicSuccessor a)-d a))
            (v : PlanarPoint ℝ)
            (hexposed : ∀ i : Fin m, i ≠ a → 0 < planarDet v (d i-d a)),
            ∃ ε : ℝ, 0 < ε ∧ ∃ scale : ℝ, 0 < scale ∧
              ε < 1 ∧ ε*scale < 1 ∧
              ∃ hQ : CyclicGeneric (truncateCyclicCorner d a p scale ε),
              ∃ hAuxQ : auxiliaryGenericity (truncateCyclicCorner d a p scale ε) hQ,
                LeftExposed (truncateCyclicCorner d a p scale ε) a.castSucc ∧
                actualDaughterSecants (truncateCyclicCorner d a p scale ε) hQ ∧
                UniversalLocus (polygonCarrierCoordinates (truncateCyclicCorner d a p scale ε)) ∧
                PairTransverse (polygonCarrierCoordinates (truncateCyclicCorner d a p scale ε)) ∧
                allCycleSecantExclusions (polygonCarrierCoordinates (truncateCyclicCorner d a p scale ε)) ∧
                ∃ K : CarrierLine,
                  lineValue K (truncateCyclicCorner d a p scale ε a.castSucc)=0 ∧
                  lineValue K (truncateCyclicCorner d a p scale ε
                    ⟨a.val+1, by have := a.isLt; omega⟩)=0 ∧
                  UniversalLocus (canonicalAugmentedCarrier d K) ∧
                  PairTransverse (canonicalAugmentedCarrier d K) ∧
                  allCycleSecantExclusions (canonicalAugmentedCarrier d K) := by
  obtain ⟨c,hc,hDense,hOpen,hCertificate⟩ :=
    exists_original_coefficient_with_subcycle_caps_and_windows q hq
  refine ⟨c,hc,hDense,hOpen,?_⟩
  intro r hr hrc
  obtain ⟨hAuxR,hDaughtersR,hUR,hTR,hCR,hSubcycles⟩ := hCertificate r hr hrc
  refine ⟨hAuxR,hDaughtersR,hUR,hTR,hCR,?_⟩
  intro m d hd f hf hIncidence
  obtain ⟨hAuxD,hDaughtersD,hUD,hTD,hCD,hCaps,hWindows⟩ :=
    hSubcycles m d hd f hf hIncidence
  refine ⟨hAuxD,hDaughtersD,hUD,hTD,hCD,hCaps,hWindows,?_⟩
  intro a p hp hturn v hexposed
  exact exists_supported_truncation_in_windows hRI d hd hAuxD a p hp hturn v hexposed hWindows

end DirectGLSSW.SourceSubcycleTruncationComposition

