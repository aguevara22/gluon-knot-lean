import ActualNumeratorTransport
import CarrierDenominatorNeighborhood

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActualCarrierTransport
open DaughterFirstReturn AuxiliaryCarrierChart LocalDaughterTransport LocalCrossingTransport
open GeometricSmoothingWeights CarrierFamilyDensity

 theorem auxiliaryGenericity_of_carrier_numerators {n : ℕ}
    (q q' : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      ((polygonEventOrder q hq.g2).lt x y ↔
        (polygonEventOrder q' hq'.g2).lt (polygonEventMapEquiv E x) (polygonEventMapEquiv E y)))
    (L : Fin n → CarrierLine)
    (hinc : ∀ e, lineValue (L e) (q' e) = 0 ∧
      lineValue (L e) (q' (cyclicSuccessor e)) = 0)
    (hden : ∀ (S : Finset (PolygonCrossing q)) (root : PolygonEvent q),
      retainedCorner q S root →
      ∀ i : Fin (Fintype.card (CornerCoord q hq.g2 S root)),
        lineDenominator
          (L (daughterCarrier q hq.g2 S root ((cyclicSuccessorPerm _)⁻¹ i)))
          (L (daughterCarrier q hq.g2 S root i)) ≠ 0)
    (hnum : allNonalternatingSupportDaughterNumeratorsNonzero q hq.g2 L) :
    auxiliaryGenericity q' hq' := by
  classical
  apply auxiliaryGenericity_of_retained q' hq'
  intro T hT y hy
  obtain ⟨S, rfl⟩ := E.finsetCongr.surjective T
  obtain ⟨root, rfl⟩ := (polygonEventMapEquiv E).surjective y
  have hS := (LocalSupportConjugacy.polygonNonalternating_map_iff
    q q' hq hq' E hlabels horder S).mpr hT
  have hr := (polygonEventMapEquiv_retained q q' E S root).mp hy
  have hdart := LocalSupportConjugacy.smoothingDartPermutation_map
    q q' hq hq' E hlabels horder S
  refine ⟨?_, ?_, ?_⟩
  · exact DaughterTurns.daughterVertexCount_ge_three q' hq'.g2 (S.map E.toEmbedding)
      hq'.size_ge_three hq'.g1 (polygonEventMapEquiv E root) hy
  · exact mapped_daughter_noncollinear q q' hq hq' E hlabels S hdart L hinc root hr
      (hden S root hr) (hnum S hS)
  · exact DaughterClosedContainment.daughter_no_triple q' (S.map E.toEmbedding)
      hq' hT (polygonEventMapEquiv E root) hy


end DirectGLSSW.ActualCarrierTransport
