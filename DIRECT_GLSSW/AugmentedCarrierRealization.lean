import AugmentedCarrierDensity

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart DaughterFirstReturn ActualCarrierTransport LocalCrossingTransport
open UniversalCarrierDomain CarrierFamilyDensity GeometricSmoothingWeights Filter Topology

/-- Joint perturbation of the actual old polygon and one freely chosen auxiliary
line. This is not a fixed-original-family extension theorem. -/
theorem exists_augmented_realization_of_auxiliary {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (hAux : auxiliaryGenericity q hq)
    (K : CarrierLine) (W : Set ((Fin n → PlanarPoint ℝ) × CarrierLine))
    (hW : W ∈ 𝓝 (q,K)) :
    ∃ r K', (r,K') ∈ W ∧ ∃ hr : CyclicGeneric r,
      auxiliaryGenericity r hr ∧ actualDaughterSecants r hr ∧
      ∃ L : Fin (n+1) → CarrierLine,
        L (Fin.last n) = K' ∧ UniversalLocus L ∧ PairTransverse L ∧ allCycleSecantExclusions L ∧
        (∀ i : Fin n, lineValue (L i.castSucc) (r i) = 0 ∧
          lineValue (L i.castSucc) (r (cyclicSuccessor i)) = 0) := by
  classical
  let L₀ : Fin (n+1) → CarrierLine := fun i =>
    if h : i.val < n then polygonCarrierCoordinates q ⟨i.val,h⟩ else K
  have hold : (fun i : Fin n => L₀ i.castSucc) = polygonCarrierCoordinates q := by
    funext i
    simp only [L₀, Fin.coe_castSucc, dif_pos i.isLt]
  have hlast : L₀ (Fin.last n) = K := by simp [L₀]
  have hrestrict : Tendsto (fun L : Fin (n+1) → CarrierLine => fun i : Fin n => L i.castSucc)
      (𝓝 L₀) (𝓝 (polygonCarrierCoordinates q)) := by
    have hh : Continuous (fun L : Fin (n+1) → CarrierLine => fun i : Fin n => L i.castSucc) := by fun_prop
    simpa only [ContinuousAt, hold] using (hh.continuousAt (x := L₀))
  have hrec := reconstructPolygon_continuousAt q hq
  have htend : Tendsto (fun L : Fin (n+1) → CarrierLine => reconstructPolygon (fun i => L i.castSucc))
      (𝓝 L₀) (𝓝 q) := by
    have hrecT : Tendsto (fun M : Fin n → CarrierLine => reconstructPolygon M)
        (𝓝 (polygonCarrierCoordinates q)) (𝓝 q) := by
      simpa only [ContinuousAt, reconstructPolygon_polygonCarrierCoordinates q hq] using hrec
    exact hrecT.comp hrestrict
  have hpair : Tendsto (fun L : Fin (n+1) → CarrierLine =>
      (reconstructPolygon (fun i => L i.castSucc), L (Fin.last n)))
      (𝓝 L₀) (𝓝 (q,K)) := by
    have hnew : Tendsto (fun L : Fin (n+1) → CarrierLine => L (Fin.last n)) (𝓝 L₀) (𝓝 K) := by
      simpa only [ContinuousAt, hlast] using (continuous_apply (Fin.last n)).continuousAt (x := L₀)
    exact htend.prodMk_nhds hnew
  have hnear := hpair.eventually hW
  have hlocal := htend.eventually (ConfigurationEventLocality.eventually_configuration_event_order q hq)
  have hp := hrestrict.eventually (eventually_parent_carrier_denominators q hq)
  have hd := hrestrict.eventually (eventually_daughter_carrier_denominators q hq)
  have hjoint := hnear.and (hp.and (hd.and hlocal))
  have hDense := (augmented_joint_dense_open q hq hAux).1
  obtain ⟨L, hL, hnum⟩ := mem_closure_iff_nhds.mp (hDense L₀) _ hjoint
  rcases hL with ⟨hLW, hp, hd, hr, E, hlabels, horder⟩
  let M : Fin n → CarrierLine := fun i => L i.castSucc
  have hinc := reconstruct_incidence M hp
  refine ⟨reconstructPolygon M, L (Fin.last n), hLW, hr, ?_, ?_, L, rfl,
    hnum.2.2.1, hnum.2.2.2.1, hnum.2.2.2.2, hinc⟩
  · exact auxiliaryGenericity_of_carrier_numerators q (reconstructPolygon M) hq hr E
      hlabels horder M hinc hd hnum.2.1
  · exact actualDaughterSecants_of_carriers q (reconstructPolygon M) hq hr E
      hlabels horder M hinc hd hnum.1

/-- Source-density quantifiers: q is arbitrary G1/G2; old q and the auxiliary
line vary simultaneously inside any specified joint neighborhood. -/
theorem exists_augmented_realization {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (K : CarrierLine) (W : Set ((Fin n → PlanarPoint ℝ) × CarrierLine))
    (hW : W ∈ 𝓝 (q,K)) :
    ∃ r K', (r,K') ∈ W ∧ ∃ hr : CyclicGeneric r,
      auxiliaryGenericity r hr ∧ actualDaughterSecants r hr ∧
      ∃ L : Fin (n+1) → CarrierLine,
        L (Fin.last n) = K' ∧ UniversalLocus L ∧ PairTransverse L ∧ allCycleSecantExclusions L ∧
        (∀ i : Fin n, lineValue (L i.castSucc) (r i) = 0 ∧
          lineValue (L i.castSucc) (r (cyclicSuccessor i)) = 0) := by
  obtain ⟨V, hVW, hV, hqV⟩ := mem_nhds_iff.mp hW
  have hc : Continuous (fun r : Fin n → PlanarPoint ℝ => (r,K)) := by fun_prop
  have hslice : {r : Fin n → PlanarPoint ℝ | (r,K) ∈ V} ∈ 𝓝 q :=
    (hV.preimage hc).mem_nhds hqV
  obtain ⟨s, hsV, hs, hAux, _⟩ := ActualAuxiliaryDensity.exists_auxiliaryGenericity_mem_nhds q hq _ hslice
  obtain ⟨r,K',hrV,hr,hrest⟩ := exists_augmented_realization_of_auxiliary s hs hAux K V (hV.mem_nhds hsV)
  exact ⟨r,K',hVW hrV,hr,hrest⟩

end DirectGLSSW.CyclicCarrierClearing


