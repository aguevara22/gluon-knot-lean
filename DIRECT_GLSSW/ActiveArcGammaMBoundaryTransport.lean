import ActiveArcGammaMSelectedConstant
import ActiveArcNoCutContribution

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords EndpointEventGeometry CompatibleWords SingletonWords
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Full physical GammaM crossing jump on the explicit auxiliary carrier
nonvanishing and canonical parent-far domain. Simultaneous density and
continuation of that domain are separate obligations. -/
theorem exists_GammaM_boundary_transport
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (hRI : GLSSWRootIndependence) (hAux : ClosedAuxiliary q hR)
    (hcut : c.val.2.val=a) (hG1 : cyclicNoncollinear q)
    (hL : OpenCarrier.parentFarLocus q hR c hcut (OpenCarrier.parentChartLines q))
    (hF : ∀ U : Support q hR, c∉U.val → EventCarrierNonvanishing q hR c U) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ ε : ℝ, 0<ε → ε<ρ →
    ∃ (hm0 : 0≤leftParameter q c-ε) (hmc : leftParameter q c-ε<leftParameter q c)
      (hcp : leftParameter q c<leftParameter q c+ε)
      (hpb : leftParameter q c+ε<afterBound q c),
    let hB := before_first_regular (a:=a+b) (b:=0) q hR c hc _ hm0 hmc
    let ht0 : 0≤leftParameter q c+ε :=
      (lt_trans (leftParameter_spec q c).1 hcp).le
    let hA := (regular_first_window_iff q hR c hc _ ht0 hpb).mpr (ne_of_gt hcp)
    GammaM (moveStart q (leftParameter q c+ε)) hA
        (Surviving.after_first_closedAuxiliary q hR c hc _ hcp hpb hAux) -
      GammaM (moveStart q (leftParameter q c-ε)) hB
        (BeforeFirst.closedAuxiliary q hR c hc _ hm0 hmc hAux) =
      ((scalarSignValue (planarDet (q 1-q 0)
        (q c.val.2.succ-q c.val.2.castSucc))-1)/2) *
        (GeometricSmoothingWeights.separatingSmoothingSum
          (Split.child q hR c hc.1 hcut)
          (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
          (child_auxiliaryGenericity q hR c hc hcut hAux) *
          GammaM (Split.parent q c hcut) (Split.regular_parent q hR c hcut)
            (parent_closedAuxiliary q hR c hc hcut hAux)) := by
  obtain ⟨ρs,hρs,hselected⟩ := exists_GammaM_jump_minus_selected_constant
    q hR c hc hRI hAux hcut hG1 hL
  obtain ⟨ρu,hρu,hunselected⟩ := exists_unselected_current_contribution
    q hR c hc hcut hRI hAux hF
  refine ⟨min ρs ρu,lt_min hρs hρu,?_⟩
  intro ε he her
  obtain ⟨hm0,hmc,hcp,hpb,hvalue⟩ := hselected ε he
    (lt_of_lt_of_le her (min_le_left _ _))
  have hu := hunselected ε he (lt_of_lt_of_le her (min_le_right _ _))
  refine ⟨hm0,hmc,hcp,hpb,?_⟩
  dsimp only at hu hvalue ⊢
  rw [hu] at hvalue
  rw [hvalue]
  ring


end DirectGLSSW.ActiveArc.Primitive
