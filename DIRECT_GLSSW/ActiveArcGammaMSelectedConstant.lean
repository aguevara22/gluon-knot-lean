import ActiveArcGammaMJumpDecomposition
import ActiveArcSelectedCutPhysicalWindow
import ActiveArcSelectedSumReindex

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords EndpointEventGeometry CompatibleWords SingletonWords
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The full actual GammaM jump with its disappearing selected family
already evaluated. The remaining sum is exactly the unselected open-current
jump with original closed factors; no no-cut identity is assumed. -/
theorem exists_GammaM_jump_minus_selected_constant
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (hRI : GLSSWRootIndependence) (hAux : ClosedAuxiliary q hR)
    (hcut : c.val.2.val=a) (hG1 : cyclicNoncollinear q)
    (hL : OpenCarrier.parentFarLocus q hR c hcut (OpenCarrier.parentChartLines q)) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ ε : ℝ, 0<ε → ε<ρ →
    ∃ (hm0 : 0≤leftParameter q c-ε) (hmc : leftParameter q c-ε<leftParameter q c)
      (hcp : leftParameter q c<leftParameter q c+ε)
      (hpb : leftParameter q c+ε<afterBound q c),
    let hB := before_first_regular (a:=a+b) (b:=0) q hR c hc _ hm0 hmc
    let ht0 : 0≤leftParameter q c+ε :=
      (lt_trans (leftParameter_spec q c).1 hcp).le
    let hA := (regular_first_window_iff q hR c hc _ ht0 hpb).mpr (ne_of_gt hcp)
    let F := fun (U : Support q hR) (s : ℝ) =>
      OpenMarkedCurrent.entry
        (polygonSignArray (moveEndpoint (eventOpenWord q hR U c) (q 1-q 0) s))
        0 (openCount q hR U.val-1)
    let P := fun U : Support q hR =>
      ∏ D∈Finset.univ.erase (openComponent q hR.noTriple U.val),
        closedWeight q hR hAux U D
    GammaM (moveStart q (leftParameter q c+ε)) hA
        (Surviving.after_first_closedAuxiliary q hR c hc _ hcp hpb hAux) -
      GammaM (moveStart q (leftParameter q c-ε)) hB
        (BeforeFirst.closedAuxiliary q hR c hc _ hm0 hmc hAux) =
      (∑ U : {U : Support q hR // c∉U.val},
        (-1 : ℚ)^U.val.val.card * ((F U.val ε-F U.val (-ε))*P U.val)) -
      ((1+scalarSignValue (planarDet (q 1-q 0)
        (q c.val.2.succ-q c.val.2.castSucc)))/2) *
        (GeometricSmoothingWeights.separatingSmoothingSum
          (Split.child q hR c hc.1 hcut)
          (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
          (child_auxiliaryGenericity q hR c hc hcut hAux) *
          GammaM (Split.parent q c hcut) (Split.regular_parent q hR c hcut)
            (parent_closedAuxiliary q hR c hc hcut hAux)) := by
  obtain ⟨ρs,hs,hselected⟩ := CarrierDomainSelectedCut.exists_physical_selectedCut_constant
    q hR c hc hcut hAux hRI hG1 hL
  obtain ⟨ρw,hw,hwindow⟩ := exists_physical_event_window q hR c hc
  refine ⟨min ρs ρw,lt_min hs hw,?_⟩
  intro ε he her
  obtain ⟨hs0,hsc,hsel⟩ := hselected ε he (lt_of_lt_of_le her (min_le_left _ _))
  obtain ⟨hm0,hmc,hcp,hpb,_,_⟩ := hwindow ε he (lt_of_lt_of_le her (min_le_right _ _))
  refine ⟨hm0,hmc,hcp,hpb,?_⟩
  have hdecomp := GammaM_physical_jump_decomposition q hR c hc hRI hAux ε hm0 hmc hcp hpb
  have hreindex := BeforeFirst.selected_sum_eq_original_event q hR c hc
    (leftParameter q c-ε) hm0 hmc hRI hAux
  dsimp only at hsel hreindex hdecomp ⊢
  have hsum := hreindex.symm.trans hsel
  have hparam : leftParameter q c-ε-leftParameter q c=-ε := by ring
  simp only [hparam] at hsum
  rw [hdecomp,hsum]


end DirectGLSSW.ActiveArc.Primitive
