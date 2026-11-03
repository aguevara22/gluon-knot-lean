import ActiveArcPositiveFirstCrossing

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords EndpointEventGeometry CompatibleWords SingletonWords
attribute [local instance] Classical.propDecidable

/-- Full physical transport at the actual canonical first crossing: minus the
child-parent product on the under branch, and zero on the over branch. The
source auxiliary carrier domain remains explicit. -/
theorem exists_GammaM_under_over_transport
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
    let jump := GammaM (moveStart q (leftParameter q c+ε)) hA
        (Surviving.after_first_closedAuxiliary q hR c hc _ hcp hpb hAux) -
      GammaM (moveStart q (leftParameter q c-ε)) hB
        (BeforeFirst.closedAuxiliary q hR c hc _ hm0 hmc hAux)
    let product := GeometricSmoothingWeights.separatingSmoothingSum
          (Split.child q hR c hc.1 hcut)
          (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
          (child_auxiliaryGenericity q hR c hc hcut hAux) *
          GammaM (Split.parent q c hcut) (Split.regular_parent q hR c hcut)
            (parent_closedAuxiliary q hR c hc hcut hAux)
    let C := polygonCrossingOfArc q c
    (crossingUnder q C=C.val.1 → jump= -product) ∧
      (crossingOver q C=C.val.1 → jump=0) := by
  obtain ⟨ρ,hρ,hjump⟩ := exists_GammaM_boundary_transport q hR c hc hRI hAux hcut hG1 hL hF
  refine ⟨ρ,hρ,?_⟩
  intro ε he her
  obtain ⟨hm0,hmc,hcp,hpb,hvalue⟩ := hjump ε he her
  refine ⟨hm0,hmc,hcp,hpb,?_⟩
  have hsign := polygonCrossingOfArc_first_sign q c hc hG1
  dsimp only at hvalue hsign ⊢
  constructor
  · intro hu
    rw [hvalue, hsign.2.2.2.2.2.mpr hu]
    ring
  · intro ho
    rw [hvalue, hsign.2.2.2.2.1.mpr ho]
    ring


end DirectGLSSW.ActiveArc.Primitive
