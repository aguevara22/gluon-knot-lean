import ActualAuxiliaryDensity

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActualAuxiliaryDensity
open DaughterFirstReturn LocalCrossingTransport LocalDaughterTransport
open GeometricSmoothingWeights Filter Topology

/-- Full actual auxiliary density with one common exact event map and explicit
index-preserving daughter-list formulas for every support and every root. -/
theorem exists_auxiliaryGenericity_daughter_transport_mem_nhds {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (U : Set (Fin n → PlanarPoint ℝ)) (hU : U ∈ 𝓝 q) :
    ∃ q' ∈ U, ∃ hq' : CyclicGeneric q',
      auxiliaryGenericity q' hq' ∧
      ∃ E : PolygonCrossing q ≃ PolygonCrossing q',
        (∀ c, (E c).val = c.val) ∧
        (∀ x y : PolygonEvent q,
          ((polygonEventOrder q hq.g2).lt x y ↔
            (polygonEventOrder q' hq'.g2).lt
              (polygonEventMapEquiv E x) (polygonEventMapEquiv E y))) ∧
        ∀ (S : Finset (PolygonCrossing q)) (root : PolygonEvent q),
          daughterPointList q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root) =
            List.ofFn (daughterVertexFormula q hq.g2 S root q') := by
  obtain ⟨q', hq'U, hq', haux, E, hlabels, horder⟩ :=
    exists_auxiliaryGenericity_mem_nhds q hq U hU
  refine ⟨q', hq'U, hq', haux, E, hlabels, horder, ?_⟩
  intro S root
  exact daughterPointList_eq_formula_of_order q q' E S hq hq' hlabels horder root


end DirectGLSSW.ActualAuxiliaryDensity
