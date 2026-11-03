import TruncationLineWindow
import CanonicalOriginalInventory
import TruncatedCanonicalInventory
import SupportedSourceTruncation

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.SourceTruncationCanonicalComposition

open DirectGLSSW DirectGLSSW.CyclicCarrierClearing
  DirectGLSSW.SourceTruncationLineWindow DirectGLSSW.SourceTruncationSupport
  DirectGLSSW.ExposedOpenPrimitive
  GeometricSmoothingWeights UniversalCarrierDomain AuxiliaryCarrierChart
  TruncationDirection Filter Topology MvPolynomial

/-- On the original coefficient's actual open dense domain, a supported
short-corner replacement can be retuned to a good new carrier line. The
truncated polygon receives its daughter and canonical-carrier inventories
from the literal truncated carrier theorem. -/
theorem exists_original_coefficient_with_supported_truncation_inventory
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
        ∀ (a p : Fin n) (hp : cyclicSuccessor p = a)
          (hturn : 0 < planarDet (r a-r p) (r (cyclicSuccessor a)-r a))
          (v : PlanarPoint ℝ)
          (hexposed : ∀ i : Fin n, i ≠ a → 0 < planarDet v (r i-r a)),
          ∃ ε : ℝ, 0 < ε ∧ ∃ scale : ℝ, 0 < scale ∧
            ε < 1 ∧ ε*scale < 1 ∧
            ∃ hQ : CyclicGeneric (truncateCyclicCorner r a p scale ε),
            ∃ hAuxQ : auxiliaryGenericity (truncateCyclicCorner r a p scale ε) hQ,
              LeftExposed (truncateCyclicCorner r a p scale ε) a.castSucc ∧
              actualDaughterSecants (truncateCyclicCorner r a p scale ε) hQ ∧
              UniversalLocus (polygonCarrierCoordinates (truncateCyclicCorner r a p scale ε)) ∧
              PairTransverse (polygonCarrierCoordinates (truncateCyclicCorner r a p scale ε)) ∧
              allCycleSecantExclusions (polygonCarrierCoordinates (truncateCyclicCorner r a p scale ε)) ∧
              ∃ K : CarrierLine,
                lineValue K (truncateCyclicCorner r a p scale ε a.castSucc)=0 ∧
                lineValue K (truncateCyclicCorner r a p scale ε
                  ⟨a.val+1, by have := a.isLt; omega⟩)=0 ∧
                PairTransverse (canonicalAugmentedCarrier r K) ∧
                UniversalLocus (canonicalAugmentedCarrier r K) ∧
                allCycleSecantExclusions (canonicalAugmentedCarrier r K) := by
  obtain ⟨c,hc,hDense,hOpen,hInventory⟩ :=
    exists_original_coefficient_with_daughter_inventory q hq
  refine ⟨c,hc,hDense,hOpen,?_⟩
  intro r hr hrc
  obtain ⟨hAux,hDaughters,hU0,hT0,hC0,hWindows⟩ := hInventory r hr hrc
  refine ⟨hAux,hDaughters,hU0,hT0,hC0,?_⟩
  intro a p hp hturn v hexposed
  obtain ⟨scale,hs,δ,hδ,hSupported⟩ :=
    exists_exposed_corner_truncation_with_support_data hRI r hr hAux a p hp hturn v hexposed
  let ε0 := δ/2
  have hε0 : 0 < ε0 := by dsimp [ε0]; linarith
  have hε0δ : ε0 < δ := by dsimp [ε0]; linarith
  obtain ⟨hε01,hε0s1,hQ0,hAuxQ0,_hAmp,_hSum,_hAmpParity,_hSumParity,hLeft0,
      _E,_hLabels,_hPoints,_hSupportEq,_hDaughterAmp⟩ := hSupported ε0 hε0 hε0δ
  let U : PlanarPoint ℝ := r p-r a
  let D : PlanarPoint ℝ := r (cyclicSuccessor a)-r a
  let v0 : PlanarPoint ℝ := scale • D-U
  let K0 : CarrierLine := (v0,-planarDet v0 (r a+ε0 • U))
  let recoveredEpsilon : CarrierLine → ℝ := fun K =>
    -lineValue K (r a) / planarDet K.1 U
  let recoveredScale : CarrierLine → ℝ := fun K =>
    planarDet K.1 U / planarDet K.1 D
  let truncation : CarrierLine → Fin (n+1) → PlanarPoint ℝ := fun K =>
    truncateCyclicCorner r a p (recoveredScale K) (recoveredEpsilon K)
  obtain ⟨W,hWopen,hK0,hLine⟩ :=
    exists_open_supported_truncation_line_window r hr a p hp hturn scale ε0 hs hε0
      hε01 hε0s1 hQ0 hLeft0
  obtain ⟨K,hKW,hT,hU,hC⟩ := hWindows W hWopen ⟨K0,hK0⟩
  have hWindowK := hLine K hKW
  rcases hWindowK with ⟨hE,hE1,hScale,hProd,hProd1,hQgeneric,hLeftK,hAnchor,hNew⟩
  have hAnchor' : lineValue K
      (truncateCyclicCorner r a p (recoveredScale K) (recoveredEpsilon K) a.castSucc)=0 := by
    change lineValue K (truncateCyclicCorner r a p (recoveredScale K)
      (recoveredEpsilon K) a.castSucc)=0 at hAnchor
    exact hAnchor
  have hNew' : lineValue K
      (truncateCyclicCorner r a p (recoveredScale K) (recoveredEpsilon K)
        ⟨a.val+1, by have := a.isLt; omega⟩)=0 := by
    change lineValue K (truncateCyclicCorner r a p (recoveredScale K)
      (recoveredEpsilon K) ⟨a.val+1, by have := a.isLt; omega⟩)=0 at hNew
    exact hNew
  have hleft : lineValue K (r a+recoveredEpsilon K • (r p-r a))=0 := by
    have hi : (a.castSucc : Fin (n+1)) = (⟨a.val, by have := a.isLt; omega⟩ : Fin (n+1)) := rfl
    rw [hi,truncateCyclicCorner_anchor] at hAnchor'
    exact hAnchor'
  have hright : lineValue K
      (r a+(recoveredEpsilon K*recoveredScale K) •
        (r (cyclicSuccessor a)-r a))=0 := by
    rw [truncateCyclicCorner_new] at hNew'
    exact hNew'
  have hInv := truncated_canonical_inventory r a p hp (recoveredScale K)
    (recoveredEpsilon K) K hQgeneric
    hleft hright hU hT hC
  rcases hInv with ⟨hAuxActual,hDaughtersActual,hUactual,hTactual,hCactual⟩
  refine ⟨recoveredEpsilon K,hE,recoveredScale K,hScale,hE1,hProd1,
    hQgeneric,hAuxActual,hLeftK,hDaughtersActual,hUactual,hTactual,hCactual,
    K,?_,?_,hT,hU,hC⟩
  · change lineValue K (truncateCyclicCorner r a p (recoveredScale K)
      (recoveredEpsilon K) a.castSucc)=0
    exact hAnchor
  · change lineValue K (truncateCyclicCorner r a p (recoveredScale K)
      (recoveredEpsilon K) ⟨a.val+1, by have := a.isLt; omega⟩)=0
    exact hNew

end DirectGLSSW.SourceTruncationCanonicalComposition

