import CyclicCarrierTransport

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart DaughterFirstReturn ActualCarrierTransport LocalCrossingTransport LocalDaughterTransport
open UniversalCarrierDomain CarrierFamilyDensity GeometricSmoothingWeights Filter Topology

/-- Exactly the four/six-slot cap exclusions for every retained actual daughter.
This inventory is not a definition of the full source auxiliary domain. -/
def actualDaughterSecants {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) : Prop :=
  ∀ S : Finset (PolygonCrossing q),
    PolygonNonalternation.polygonNonalternating q hq.g2 S →
    ∀ root : PolygonEvent q, retainedCorner q S root →
      (∀ l : Fin 4 → Fin (Fintype.card (CornerCoord q hq.g2 S root)),
        Function.Injective l → OriginalOuterProperness.outerNumerator
          (daughterVertex q hq.g2 S root ∘ l) ≠ 0) ∧
      (∀ l : Fin 6 → Fin (Fintype.card (CornerCoord q hq.g2 S root)),
        Function.Injective l → OriginalSecantProperness.secantNumerator
          (daughterVertex q hq.g2 S root ∘ l) ≠ 0)

 theorem actualDaughterSecants_of_carriers {n : ℕ}
    (q r : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (hr : CyclicGeneric r)
    (E : PolygonCrossing q ≃ PolygonCrossing r)
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      ((polygonEventOrder q hq.g2).lt x y ↔
        (polygonEventOrder r hr.g2).lt (polygonEventMapEquiv E x) (polygonEventMapEquiv E y)))
    (L : Fin n → CarrierLine)
    (hinc : ∀ e, lineValue (L e) (r e) = 0 ∧ lineValue (L e) (r (cyclicSuccessor e)) = 0)
    (hden : ∀ (S : Finset (PolygonCrossing q)) (root : PolygonEvent q),
      retainedCorner q S root → ∀ i : Fin (Fintype.card (CornerCoord q hq.g2 S root)),
        lineDenominator (L (daughterCarrier q hq.g2 S root ((cyclicSuccessorPerm _)⁻¹ i)))
          (L (daughterCarrier q hq.g2 S root i)) ≠ 0)
    (hnum : daughterSecantExclusions q hq L) : actualDaughterSecants r hr := by
  classical
  intro T hT y hy
  obtain ⟨S, rfl⟩ := E.finsetCongr.surjective T
  obtain ⟨root, rfl⟩ := (polygonEventMapEquiv E).surjective y
  have hS := (LocalSupportConjugacy.polygonNonalternating_map_iff q r hq hr E hlabels horder S).mpr hT
  have hroot := (polygonEventMapEquiv_retained q r E S root).mp hy
  have hdart := LocalSupportConjugacy.smoothingDartPermutation_map q r hq hr E hlabels horder S
  exact ⟨mapped_daughter_outer q r hq hr E hlabels S hdart L hinc root hroot
      (hden S root hroot) (hnum S hS root),
    mapped_daughter_secant q r hq hr E hlabels S hdart L hinc root hroot
      (hden S root hroot) (hnum S hS root)⟩

 theorem exists_joint_realization_of_auxiliary {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (hAux : auxiliaryGenericity q hq)
    (U : Set (Fin n → PlanarPoint ℝ)) (hU : U ∈ 𝓝 q) :
    ∃ r ∈ U, ∃ hr : CyclicGeneric r,
      auxiliaryGenericity r hr ∧ actualDaughterSecants r hr ∧
      ∃ L : Fin n → CarrierLine, UniversalLocus L ∧ PairTransverse L ∧
        (∀ e, lineValue (L e) (r e) = 0 ∧ lineValue (L e) (r (cyclicSuccessor e)) = 0) := by
  have hrec := reconstructPolygon_continuousAt q hq
  have hnear : ∀ᶠ L in 𝓝 (polygonCarrierCoordinates q), reconstructPolygon L ∈ U := by
    apply hrec.eventually
    simpa only [reconstructPolygon_polygonCarrierCoordinates q hq] using hU
  have hlocal : ∀ᶠ L in 𝓝 (polygonCarrierCoordinates q),
      ∃ ht : CyclicGeneric (reconstructPolygon L),
      ∃ E : PolygonCrossing q ≃ PolygonCrossing (reconstructPolygon L),
        (∀ c, (E c).val = c.val) ∧
        ∀ x y : PolygonEvent q,
          ((polygonEventOrder q hq.g2).lt x y ↔
            (polygonEventOrder (reconstructPolygon L) ht.g2).lt
              (polygonEventMapEquiv E x) (polygonEventMapEquiv E y)) := by
    have htend : Tendsto (fun L : Fin n → CarrierLine => reconstructPolygon L)
        (𝓝 (polygonCarrierCoordinates q)) (𝓝 q) := by
      simpa only [ContinuousAt, reconstructPolygon_polygonCarrierCoordinates q hq] using hrec
    exact htend.eventually (ConfigurationEventLocality.eventually_configuration_event_order q hq)
  have hjoint := hnear.and ((eventually_parent_carrier_denominators q hq).and
    ((eventually_daughter_carrier_denominators q hq).and hlocal))
  have hnew := joint_daughter_universal_dense_open q hq hAux
  have hold := all_nonalternating_support_daughter_numerator_locus_dense_open
    q hq.g2 hq.size_ge_three hq.g1
  have hdense := hnew.1.inter_of_isOpen_left hold.1 hnew.2
  obtain ⟨L, hL, hnum⟩ := mem_closure_iff_nhds.mp (hdense (polygonCarrierCoordinates q)) _ hjoint
  rcases hL with ⟨hLU, hp, hd, ht, E, hlabels, horder⟩
  have hinc := reconstruct_incidence L hp
  refine ⟨reconstructPolygon L, hLU, ht, ?_, ?_, L, hnum.1.2.1, hnum.1.2.2, hinc⟩
  · exact auxiliaryGenericity_of_carrier_numerators q (reconstructPolygon L) hq ht E
      hlabels horder L hinc hd hnum.2
  · exact actualDaughterSecants_of_carriers q (reconstructPolygon L) hq ht E
      hlabels horder L hinc hd hnum.1.1

/-- Full G1/G2 parent input, no hAux or properness witness: every neighborhood
contains an actual parent with all retained-daughter four/six-slot exclusions
and one universal supplied original carrier family. -/
 theorem exists_joint_realization {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (U : Set (Fin n → PlanarPoint ℝ)) (hU : U ∈ 𝓝 q) :
    ∃ r ∈ U, ∃ hr : CyclicGeneric r,
      auxiliaryGenericity r hr ∧ actualDaughterSecants r hr ∧
      ∃ L : Fin n → CarrierLine, UniversalLocus L ∧ PairTransverse L ∧
        (∀ e, lineValue (L e) (r e) = 0 ∧ lineValue (L e) (r (cyclicSuccessor e)) = 0) := by
  obtain ⟨V, hVU, hV, hqV⟩ := mem_nhds_iff.mp hU
  obtain ⟨s, hsV, hs, hAux, _⟩ := ActualAuxiliaryDensity.exists_auxiliaryGenericity_mem_nhds
    q hq V (hV.mem_nhds hqV)
  obtain ⟨r, hrV, hr, hrest⟩ := exists_joint_realization_of_auxiliary s hs hAux V (hV.mem_nhds hsV)
  exact ⟨r, hVU hrV, hr, hrest⟩

end DirectGLSSW.CyclicCarrierClearing




