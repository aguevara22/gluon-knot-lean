import ActiveArcOpenRegularNeighborhood
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc AuxiliaryCarrierChart ConfigurationLocality Filter Topology

/-- Actual carrier perturbations reconstruct regular source-G1 open arcs in any
prescribed neighborhood, with all physical incidences and denominator validity. -/
theorem eventually_reconstructOpen_regular_G1 {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hR : Regular q) (hG1 : cyclicNoncollinear q)
    (U : Set (Fin (n+2) → PlanarPoint ℝ)) (hU : U ∈ 𝓝 q) :
    ∀ᶠ L in 𝓝 (openChartLines q),
      OpenChartNondegenerate q L ∧ reconstructOpen q L∈U ∧
      Regular (reconstructOpen q L) ∧ cyclicNoncollinear (reconstructOpen q L) ∧
      (∀ e : Fin (n+1),
        lineValue (L (Sum.inl e)) (reconstructOpen q L e.castSucc)=0 ∧
        lineValue (L (Sum.inl e)) (reconstructOpen q L e.succ)=0) ∧
      lineValue (initialLine q) (reconstructOpen q L 0)=0 ∧
      lineValue (L (Sum.inr ())) (reconstructOpen q L ⟨n+1,by omega⟩)=0 := by
  have ht : Tendsto (reconstructOpen q) (𝓝 (openChartLines q)) (𝓝 q) := by
    simpa only [ContinuousAt,reconstructOpen_recovery q hR hG1] using
      reconstructOpen_continuousAt q hR hG1
  filter_upwards [eventually_reconstructOpen_valid_mem q hR hG1 U hU,
    ht.eventually (eventually_regular_G1 q hR hG1)] with L hL hreg
  exact ⟨hL.1,hL.2.1,hreg.1,hreg.2,hL.2.2,reconstructOpen_endpoint_incidence q L hL.1⟩


end DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW.ActiveArc.ConfigurationLocality
#check @vertex_closed_incident
#check @closed_triple_no_anchor
#check @no_three_physical_closed
#check @eventually_no_three_closed
#check @eventually_vertex_G1
#check @eventually_regular_G1
#check @DirectGLSSW.ActiveArc.OpenCarrier.eventually_reconstructOpen_regular_G1






