import ExposedScaleStability
import SupportedScaleConsumer
import TruncationLineWindow
import FixedScaleFromGoodLine
import TruncatedCanonicalInventory

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.SourceTruncationScaleStability

open DirectGLSSW DirectGLSSW.SourceTruncationSupport
  DirectGLSSW.SourceTruncationLineWindow DirectGLSSW.CyclicCarrierClearing
  DirectGLSSW.AuxiliaryCarrierChart DirectGLSSW.UniversalCarrierDomain
  DirectGLSSW.TruncationDirection Filter Topology
open DaughterFirstReturn GeometricSmoothingWeights PermutationOrbits
open TruncationEdgeLift PolygonNonalternation TruncationDaughterEvents
open ExposedOpenPrimitive

/-- A good line is selected inside the open region where its recovered scale
retains the actual strict support and event avoidance. At that single scale,
all sufficiently small truncations have source transport and canonical
inventory. -/
theorem exists_supported_truncation_with_windows_at_scale {m : ℕ}
    (hRI : GLSSWRootIndependence)
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
    ∃ scale : ℝ, 0 < scale ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ε < 1 ∧ ε*scale < 1 ∧
        ∃ hQ : CyclicGeneric (truncateCyclicCorner d a p scale ε),
        ∃ hAuxQ : auxiliaryGenericity (truncateCyclicCorner d a p scale ε) hQ,
          LeftExposed (truncateCyclicCorner d a p scale ε) a.castSucc ∧
          polygonAmplitude (truncateCyclicCorner d a p scale ε) hQ =
            -polygonAmplitude d hd ∧
          separatingSmoothingSum (truncateCyclicCorner d a p scale ε) hQ hAuxQ =
            -separatingSmoothingSum d hd hAux ∧
          (-1 : ℚ)^(m+1)*polygonAmplitude (truncateCyclicCorner d a p scale ε) hQ =
            (-1 : ℚ)^m*polygonAmplitude d hd ∧
          (-1 : ℚ)^(m+1)*separatingSmoothingSum
              (truncateCyclicCorner d a p scale ε) hQ hAuxQ =
            (-1 : ℚ)^m*separatingSmoothingSum d hd hAux ∧
          ∃ E : PolygonCrossing d ≃ PolygonCrossing (truncateCyclicCorner d a p scale ε),
            (∀ c : PolygonCrossing d,
              (E c).val = (edgeLift a c.val.1,edgeLift a c.val.2)) ∧
            (∀ c : PolygonCrossing d,
              crossingPoint (truncateCyclicCorner d a p scale ε) (E c) =
                crossingPoint d c) ∧
            (∀ S : Finset (PolygonCrossing d),
              polygonNonalternating d hd.g2 S ↔
                polygonNonalternating (truncateCyclicCorner d a p scale ε) hQ.g2
                  (S.map E.toEmbedding)) ∧
            (∀ (S : Finset (PolygonCrossing d)) (hS : polygonNonalternating d hd.g2 S),
              ∃ hNew : CyclicGeneric (daughterVertex (truncateCyclicCorner d a p scale ε)
                hQ.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)),
                polygonAmplitude (daughterVertex (truncateCyclicCorner d a p scale ε)
                  hQ.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)) hNew =
                -polygonAmplitude (daughterVertex d hd.g2 S (Sum.inl a))
                  (hAux S hS (Sum.inl a))) ∧
          actualDaughterSecants (truncateCyclicCorner d a p scale ε) hQ ∧
          UniversalLocus (polygonCarrierCoordinates (truncateCyclicCorner d a p scale ε)) ∧
          PairTransverse (polygonCarrierCoordinates (truncateCyclicCorner d a p scale ε)) ∧
          allCycleSecantExclusions (polygonCarrierCoordinates (truncateCyclicCorner d a p scale ε)) := by
  classical
  obtain ⟨scale0,hscale0,hsupport0,havoid0,hScaleEvent⟩ :=
    exists_exposed_scale_support_and_avoidance_neighborhood d hd a p hp hturn v hexposed
  obtain ⟨δ0,hδ0,hseed⟩ :=
    exists_supported_truncation_data_at_scale hRI d hd hAux a p hp hturn
      scale0 hscale0 hsupport0 havoid0
  let ε0 := δ0/2
  have hε0 : 0 < ε0 := by dsimp [ε0]; linarith
  have hε0δ : ε0 < δ0 := by dsimp [ε0]; linarith
  obtain ⟨hε01,hε0s1,hQ0,hAuxQ0,_hAmp0,_hSum0,_hAmpParity0,
      _hSumParity0,hLeft0,_E0,_hLabels0,_hPoints0,_hSupportEq0,_hDaughterAmp0⟩ :=
    hseed ε0 hε0 hε0δ
  let U : PlanarPoint ℝ := d p-d a
  let D : PlanarPoint ℝ := d (cyclicSuccessor a)-d a
  let v0 : PlanarPoint ℝ := scale0 • D-U
  let K0 : CarrierLine := (v0,-planarDet v0 (d a+ε0 • U))
  let recoveredEpsilon : CarrierLine → ℝ := fun K =>
    -lineValue K (d a) / planarDet K.1 U
  let recoveredScale : CarrierLine → ℝ := fun K =>
    planarDet K.1 U / planarDet K.1 D
  let truncation : CarrierLine → Fin (m+1) → PlanarPoint ℝ := fun K =>
    truncateCyclicCorner d a p (recoveredScale K) (recoveredEpsilon K)
  obtain ⟨W,hWopen,hK0,hLine⟩ :=
    exists_open_supported_truncation_line_window d hd a p hp hturn scale0 ε0
      hscale0 hε0 hε01 hε0s1 hQ0 hLeft0
  have hUD : 0 < planarDet D U := by
    have heq : planarDet D U = planarDet (d a-d p) (d (cyclicSuccessor a)-d a) := by
      simp [D,U,planarDet]
      ring
    rw [heq]
    exact hturn
  have hdetD : 0 < planarDet v0 D := by
    have heq : planarDet v0 D = planarDet D U := by
      simp [v0,planarDet]
      ring
    rw [heq]
    exact hUD
  have hscaleCont : ContinuousAt recoveredScale K0 := by
    unfold recoveredScale
    apply ContinuousAt.div
    · unfold planarDet
      fun_prop
    · unfold planarDet
      fun_prop
    · exact ne_of_gt hdetD
  have hscaleK0 : recoveredScale K0 = scale0 := by
    unfold recoveredScale
    have hnum : planarDet v0 U = scale0*planarDet D U := by
      simp [v0,planarDet]
      ring
    have hden : planarDet v0 D = planarDet D U := by
      simp [v0,planarDet]
      ring
    rw [hnum,hden]
    field_simp [ne_of_gt hUD]
  obtain ⟨V,hVsub,hVopen,hscale0V⟩ := mem_nhds_iff.mp hScaleEvent
  have hscaleK0V : recoveredScale K0 ∈ V := by rw [hscaleK0]; exact hscale0V
  have hscaleNear : ∀ᶠ K : CarrierLine in 𝓝 K0, recoveredScale K ∈ V :=
    hscaleCont.eventually (hVopen.mem_nhds hscaleK0V)
  obtain ⟨Wscale,hWscaleSub,hWscaleOpen,hK0Wscale⟩ :=
    mem_nhds_iff.mp hscaleNear
  let W' : Set CarrierLine := W ∩ Wscale
  have hW'open : IsOpen W' := hWopen.inter hWscaleOpen
  have hW'nonempty : W'.Nonempty := ⟨K0,⟨hK0,hK0Wscale⟩⟩
  obtain ⟨K,hKW,hU,hT,hC⟩ := hWindows W' hW'open hW'nonempty
  have hKWline : K ∈ W := hKW.1
  have hKscaleNear : recoveredScale K ∈ V := hWscaleSub hKW.2
  have hStable := hVsub hKscaleNear
  have hLineK := hLine K hKWline
  rcases hLineK with ⟨hE,hE1,hS,hProd,hProd1,hQgeneric,hLeftK,hAnchor,hNew⟩
  have hsupportK : ∀ i : Fin m, i ≠ a →
      0 < planarDet (recoveredScale K • (d (cyclicSuccessor a)-d a)-(d p-d a))
        (d i-d a) := by
    intro i hi
    simpa [D,U] using hStable.1 i hi
  have havoidK : ∀ e : PolygonEvent d, polygonEventPoint d e ≠ d a →
      planarDet (recoveredScale K • (d (cyclicSuccessor a)-d a)-(d p-d a))
        (polygonEventPoint d e-d a) ≠ 0 := by
    intro e he
    simpa [D,U] using hStable.2 e he
  obtain ⟨δA,hδA,hAmplitude⟩ :=
    exists_supported_truncation_data_at_scale hRI d hd hAux a p hp hturn
      (recoveredScale K) hS hsupportK havoidK
  have hU0 : U = d p-d a := rfl
  have hD0 : D = d (cyclicSuccessor a)-d a := rfl
  have hv : recoveredScale K • D-U ≠ 0 := by
    intro hz
    have hdet : planarDet (recoveredScale K • D-U) U = 0 := by rw [hz]; simp [planarDet]
    have hdet' : planarDet (recoveredScale K • D-U) U =
        recoveredScale K*planarDet D U := by
      simp [planarDet,Prod.smul_fst,Prod.smul_snd]
      ring
    rw [hdet'] at hdet
    exact (ne_of_gt (mul_pos hS hUD)) hdet
  have hKdir : K.1 ≠ 0 := by
    intro hz
    have hdet0 : planarDet K.1 D = 0 := by simp [hz,planarDet]
    have hscaleZero : recoveredScale K = 0 := by
      simp [recoveredScale,hdet0]
    change 0 < recoveredScale K at hS
    rw [hscaleZero] at hS
    exact (lt_irrefl 0) hS
  have hAnchorAffine : lineValue K (d a+recoveredEpsilon K • U)=0 := by
    have hEq := hAnchor
    simpa [U] using (show truncateCyclicCorner d a p (recoveredScale K)
      (recoveredEpsilon K) a.castSucc = d a+recoveredEpsilon K • U by
        simpa [U] using truncateCyclicCorner_anchor d a p
          (recoveredScale K) (recoveredEpsilon K)) ▸ hEq
  have hNewAffine : lineValue K
      (d a+(recoveredEpsilon K*recoveredScale K) • D)=0 := by
    have hEq := hNew
    simpa [D] using (show truncateCyclicCorner d a p (recoveredScale K)
      (recoveredEpsilon K) ⟨a.val+1, by have := a.isLt; omega⟩ =
      d a+(recoveredEpsilon K*recoveredScale K) • D by
        simpa [D] using truncateCyclicCorner_new d a p
          (recoveredScale K) (recoveredEpsilon K)) ▸ hEq
  obtain ⟨δI,hδI,hInventory⟩ :=
    fixed_scale_inventory_of_good_line d K (d a) U D (recoveredScale K) (recoveredEpsilon K)
      (ne_of_gt hE) hv hKdir hAnchorAffine hNewAffine hU hT hC
  let δ := min δA δI
  have hδ : 0 < δ := lt_min hδA hδI
  have hδA' : δ ≤ δA := min_le_left δA δI
  have hδI' : δ ≤ δI := min_le_right δA δI
  refine ⟨recoveredScale K,hS,δ,hδ,?_⟩
  intro ε hε hεδ
  obtain ⟨hε1,hεscale1,hQ,hAuxQ,hamp,hsum,hAmpParity,hSumParity,hLeft,
      E,hlabels,hpoints,hsep,hAffected⟩ := hAmplitude ε hε
        (lt_of_lt_of_le hεδ hδA')
  obtain ⟨hUeps,hTeps,hCeps⟩ := hInventory ε hε
    (lt_of_lt_of_le hεδ hδI')
  let Kε : CarrierLine :=
    (recoveredScale K • D-U,
      -planarDet (recoveredScale K • D-U) (d a+ε • U))
  have hlineAffine (t : ℝ) (X : PlanarPoint ℝ) :
      lineValue Kε (d a+t • X) =
        lineValue Kε (d a)+t*planarDet Kε.1 X := by
    simp [AuxiliaryCarrierChart.lineValue,planarDet,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd]
    ring
  have hbase : lineValue Kε (d a+ε • U)=0 := by
    simp [Kε,AuxiliaryCarrierChart.lineValue,planarDet]
  have hdet : planarDet (recoveredScale K • D-U) U =
      recoveredScale K*planarDet D U := by
    simp [planarDet,Prod.smul_fst,Prod.smul_snd]
    ring
  have hdet2 : planarDet (recoveredScale K • D-U) D = planarDet D U := by
    simp [planarDet,Prod.smul_fst,Prod.smul_snd]
    ring
  have hbaseOrigin : lineValue Kε (d a) = -ε*planarDet Kε.1 U := by
    have htmp := hlineAffine ε U
    rw [hbase] at htmp
    linarith
  have hlineRight : lineValue Kε
      (d a+(ε*recoveredScale K) • D)=0 := by
    rw [hlineAffine (ε*recoveredScale K) D]
    rw [hbaseOrigin,hdet,hdet2]
    ring
  have hleftQ : lineValue Kε (truncateCyclicCorner d a p (recoveredScale K) ε a.castSucc)=0 := by
    have hEq : truncateCyclicCorner d a p (recoveredScale K) ε a.castSucc = d a+ε • U := by
      simpa [U] using truncateCyclicCorner_anchor d a p (recoveredScale K) ε
    rw [hEq]
    exact hbase
  have hrightQ : lineValue Kε
      (truncateCyclicCorner d a p (recoveredScale K) ε
        ⟨a.val+1, by have := a.isLt; omega⟩)=0 := by
    have hEq : truncateCyclicCorner d a p (recoveredScale K) ε
        ⟨a.val+1, by have := a.isLt; omega⟩ =
          d a+(ε*recoveredScale K) • D := by
      simpa [D] using truncateCyclicCorner_new d a p (recoveredScale K) ε
    rw [hEq]
    exact hlineRight
  have hInv := truncated_canonical_inventory d a p hp (recoveredScale K) ε Kε hQ
    hbase hlineRight hUeps hTeps hCeps
  rcases hInv with ⟨hAuxActual,hDaughtersActual,hUactual,hTactual,hCactual⟩
  refine ⟨hε1,hεscale1,hQ,hAuxQ,hLeft,hamp,hsum,hAmpParity,hSumParity,
    E,hlabels,hpoints,hsep,hAffected,hDaughtersActual,hUactual,hTactual,hCactual⟩

end DirectGLSSW.SourceTruncationScaleStability
