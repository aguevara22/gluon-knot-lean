import ActiveArcLiteralTinyGammaM
import ActiveArcCarrierDomainSelectedCut

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split SingletonWords Primitive RetainedWords CompatibleWords OpenFirstEdgeGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Literal tiny-parent current equals its source limit for all sufficiently
small positive heads. Every support, retained word and closed factor is actual. -/
theorem exists_actual_tinyParent_GammaM_limit
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : ClosedAuxiliary q hR) (hRI : GLSSWRootIndependence)
    (hG1 : cyclicNoncollinear q)
    (hL : OpenCarrier.parentFarLocus q hR c hcut (OpenCarrier.parentChartLines q)) :
    ∃ (ρ : ℝ) (_hρ : 0<ρ) (hρ1 : ρ≤1), ∀ (η : ℝ) (hη : 0<η) (hηρ : η<ρ),
      GammaM (tinyParent q c hcut η)
        (regular_tinyParent q hR c hc hcut η hη (lt_of_lt_of_le hηρ hρ1))
        (tinyParent_closedAuxiliary_from_original q hR c hc hcut η hη
          (lt_of_lt_of_le hηρ hρ1) hAux) =
      -((1+scalarSignValue (planarDet (q 1-q 0)
        (q c.val.2.succ-q c.val.2.castSucc)))/2) *
        GammaM (parent q c hcut) (regular_parent q hR c hcut)
          (parent_closedAuxiliary q hR c hc hcut hAux) := by
  obtain ⟨ρ,hρ,hρ1,hvalue⟩ := TinyParentFarProjector.exists_weighted_parent_projector
    q hR c hc hcut hAux (OpenCarrier.parentFarLocus_prefix_far q hR c hcut hG1 hL)
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro η hη hηρ
  rw [tinyParent_GammaM_eq_weighted_approach q hR c hc hcut η hη
    (lt_of_lt_of_le hηρ hρ1) hRI hAux]
  exact hvalue η hη hηρ

/-- Removing the actual pre-event supports containing the cut crossing
contributes the negative selected sum, with the physical child and parent. -/
theorem exists_removed_pre_first_cut_contribution
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : Primitive.ClosedAuxiliary q hR) (hRI : GLSSWRootIndependence)
    (hG1 : cyclicNoncollinear q)
    (hL : OpenCarrier.parentFarLocus q hR c hcut (OpenCarrier.parentChartLines q)) :
    ∃ (r : ℝ) (_hr : 0<r) (hr1 : r≤1), ∀ (ε : ℝ) (he : 0<ε) (her : ε<r),
    let t := leftParameter q c*(1-ε)
    let bounds := approach_parameter_bounds q c ε he (lt_of_lt_of_le her hr1)
    let qm := moveStart q t
    let hm := before_first_regular q hR c hc t bounds.1 bounds.2
    let C := crossingFromOriginal q t (lt_trans bounds.2 (leftParameter_spec q c).2.1)
      c (survives_before_first q c hc t bounds.2 c)
    let hAm := BeforeFirst.closedAuxiliary q hR c hc t bounds.1 bounds.2 hAux
    (-(∑ U : {U : Primitive.Support qm hm // C ∈ U.val},
      (-1 : ℚ)^U.val.val.card *
        (Primitive.openCurrent qm hm U.val *
          ∏ D ∈ Finset.univ.erase (openComponent qm hm.noTriple U.val.val),
            Primitive.closedWeight qm hm hAm U.val D)) =
      -((1+scalarSignValue (planarDet (q 1-q 0)
        (q c.val.2.succ-q c.val.2.castSucc)))/2) *
        (GeometricSmoothingWeights.separatingSmoothingSum
          (child q hR c hc.1 hcut)
          (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
          (child_auxiliaryGenericity q hR c hc hcut hAux) *
          Primitive.GammaM (parent q c hcut) (regular_parent q hR c hcut)
            (parent_closedAuxiliary q hR c hc hcut hAux))) := by
  obtain ⟨ρ,hρ,hρ1,hvalue⟩ := CarrierDomainSelectedCut.exists_pre_first_selectedCut_constant_of_parentFarLocus
    q hR c hc hcut hAux hRI hG1 hL
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro η hη hηρ
  have hv := hvalue η hη hηρ
  dsimp only at hv ⊢
  rw [hv]
  ring

end DirectGLSSW.ActiveArc.LiteralTinyParent
