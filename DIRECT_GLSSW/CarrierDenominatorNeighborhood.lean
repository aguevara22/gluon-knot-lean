import ActualCarrierTransport

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActualCarrierTransport
open DaughterFirstReturn AuxiliaryCarrierChart Filter Topology

 theorem continuous_lineDenominator_apply {n : ℕ} (e f : Fin n) :
    Continuous (fun L : Fin n → CarrierLine => lineDenominator (L e) (L f)) := by
  unfold lineDenominator planarDet
  fun_prop

 theorem eventually_parent_carrier_denominators {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ L in 𝓝 (polygonCarrierCoordinates q), ∀ e,
      lineDenominator (L ((cyclicSuccessorPerm n)⁻¹ e)) (L e) ≠ 0 := by
  apply Filter.eventually_all.mpr
  intro e
  exact (continuous_lineDenominator_apply _ _).continuousAt.eventually_ne
    (polygonCarrierDenominator_ne_zero q hq e)

 theorem eventually_daughter_carrier_denominators {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ L in 𝓝 (polygonCarrierCoordinates q),
      ∀ (S : Finset (PolygonCrossing q)) (root : PolygonEvent q),
        retainedCorner q S root →
        ∀ i : Fin (Fintype.card (CornerCoord q hq.g2 S root)),
          lineDenominator
            (L (daughterCarrier q hq.g2 S root ((cyclicSuccessorPerm _)⁻¹ i)))
            (L (daughterCarrier q hq.g2 S root i)) ≠ 0 := by
  classical
  apply Filter.eventually_all.mpr
  intro S
  apply Filter.eventually_all.mpr
  intro root
  by_cases hr : retainedCorner q S root
  · have hall : ∀ᶠ L in 𝓝 (polygonCarrierCoordinates q),
        ∀ i : Fin (Fintype.card (CornerCoord q hq.g2 S root)),
          lineDenominator
            (L (daughterCarrier q hq.g2 S root ((cyclicSuccessorPerm _)⁻¹ i)))
            (L (daughterCarrier q hq.g2 S root i)) ≠ 0 := by
      apply Filter.eventually_all.mpr
      intro i
      exact (continuous_lineDenominator_apply _ _).continuousAt.eventually_ne
        (DaughterCarrierIntersection.actual_daughter_carrier_intersection q hq S root hr i).2.2.1
    exact hall.mono (fun _ h _ => h)
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (hr h))



end DirectGLSSW.ActualCarrierTransport
