import ActiveArcGammaMUnderOverTransport
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords EndpointEventGeometry CompatibleWords SingletonWords
attribute [local instance] Classical.propDecidable
/-- Actual first-over passage preserves the vertex-parity normalized current. -/
theorem exists_normalized_first_over_transport
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (hRI : GLSSWRootIndependence) (hAux : ClosedAuxiliary q hR)
    (hcut : c.val.2.val=a) (hG1 : cyclicNoncollinear q)
    (hL : OpenCarrier.parentFarLocus q hR c hcut (OpenCarrier.parentChartLines q))
    (hF : ∀ U : Support q hR, c∉U.val → EventCarrierNonvanishing q hR c U)
    (ho : crossingOver q (polygonCrossingOfArc q c)=(polygonCrossingOfArc q c).val.1) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ ε : ℝ, 0<ε → ε<ρ →
    ∃ (hm0 : 0≤leftParameter q c-ε) (hmc : leftParameter q c-ε<leftParameter q c)
      (hcp : leftParameter q c<leftParameter q c+ε)
      (hpb : leftParameter q c+ε<afterBound q c),
    let hB := before_first_regular (a:=a+b) (b:=0) q hR c hc _ hm0 hmc
    let ht0 : 0≤leftParameter q c+ε := (lt_trans (leftParameter_spec q c).1 hcp).le
    let hA := (regular_first_window_iff q hR c hc _ ht0 hpb).mpr (ne_of_gt hcp)
    (-1:ℚ)^(List.ofFn (moveStart q (leftParameter q c-ε))).length *
      GammaM (moveStart q (leftParameter q c-ε)) hB
        (BeforeFirst.closedAuxiliary q hR c hc _ hm0 hmc hAux) =
    (-1:ℚ)^(List.ofFn (moveStart q (leftParameter q c+ε))).length *
      GammaM (moveStart q (leftParameter q c+ε)) hA
        (Surviving.after_first_closedAuxiliary q hR c hc _ hcp hpb hAux) := by
  obtain ⟨ρ,hρ,htransport⟩ := exists_GammaM_under_over_transport q hR c hc hRI hAux hcut hG1 hL hF
  refine ⟨ρ,hρ,?_⟩
  intro ε he her
  obtain ⟨hm0,hmc,hcp,hpb,hunder,hover⟩ := htransport ε he her
  refine ⟨hm0,hmc,hcp,hpb,?_⟩
  have hj := hover ho
  dsimp only at hj ⊢
  simp only [List.length_ofFn]
  congr 1
  exact (sub_eq_zero.mp hj).symm

end DirectGLSSW.ActiveArc.Primitive
