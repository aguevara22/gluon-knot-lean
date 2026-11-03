import ActualAuxiliaryCarrier
import ConfigurationEventLocality

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActualAuxiliaryDensity
open DaughterFirstReturn AuxiliaryCarrierChart LocalCrossingTransport
open GeometricSmoothingWeights CarrierFamilyDensity ActualCarrierTransport
open Filter Topology

/-- Every neighborhood of an actual G1/G2 polygon contains an actual polygon
with all nonalternating daughters G1/G2, preserving crossing labels and event order.
No auxiliary genericity or polynomial properness is assumed. -/
theorem exists_auxiliaryGenericity_mem_nhds {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (U : Set (Fin n → PlanarPoint ℝ)) (hU : U ∈ 𝓝 q) :
    ∃ q' ∈ U, ∃ hq' : CyclicGeneric q',
      auxiliaryGenericity q' hq' ∧
      ∃ E : PolygonCrossing q ≃ PolygonCrossing q',
        (∀ c, (E c).val = c.val) ∧
        ∀ x y : PolygonEvent q,
          ((polygonEventOrder q hq.g2).lt x y ↔
            (polygonEventOrder q' hq'.g2).lt
              (polygonEventMapEquiv E x) (polygonEventMapEquiv E y)) := by
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
    have hh := htend.eventually
      (ConfigurationEventLocality.eventually_configuration_event_order q hq)
    exact hh
  have hjoint := hnear.and ((eventually_parent_carrier_denominators q hq).and
    ((eventually_daughter_carrier_denominators q hq).and hlocal))
  have hdense := (all_nonalternating_support_daughter_numerator_locus_dense_open
    q hq.g2 hq.size_ge_three hq.g1).1
  obtain ⟨L, hL, hnum⟩ := mem_closure_iff_nhds.mp (hdense (polygonCarrierCoordinates q))
    _ hjoint
  rcases hL with ⟨hLU, hp, hd, ht, E, hlabels, horder⟩
  refine ⟨reconstructPolygon L, hLU, ht, ?_, E, hlabels, horder⟩
  exact auxiliaryGenericity_of_carrier_numerators q (reconstructPolygon L) hq ht E
    hlabels horder L (reconstruct_incidence L hp) hd hnum

theorem exists_auxiliaryGenericity_dist_lt {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q', dist q' q < ε ∧ ∃ hq' : CyclicGeneric q',
      auxiliaryGenericity q' hq' ∧
      ∃ E : PolygonCrossing q ≃ PolygonCrossing q',
        (∀ c, (E c).val = c.val) ∧
        ∀ x y : PolygonEvent q,
          ((polygonEventOrder q hq.g2).lt x y ↔
            (polygonEventOrder q' hq'.g2).lt
              (polygonEventMapEquiv E x) (polygonEventMapEquiv E y)) := by
  exact exists_auxiliaryGenericity_mem_nhds q hq (Metric.ball q ε)
    (Metric.ball_mem_nhds q hε)



end DirectGLSSW.ActualAuxiliaryDensity
