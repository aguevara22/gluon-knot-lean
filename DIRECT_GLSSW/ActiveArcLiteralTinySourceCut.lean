import ActiveArcLiteralTinyLimit

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split SingletonWords Primitive RetainedWords CompatibleWords OpenFirstEdgeGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- At each positive pre-event head size, the selected supports factor through
 the GammaM of the actual tiny parent, including its genuine closed weights. -/
theorem selectedCut_eq_actual_tinyParent
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : ClosedAuxiliary q hR) (hRI : GLSSWRootIndependence)
    (η : ℝ) (hη : 0<η) (hη1 : η<1) :
    let t := leftParameter q c*(1-η)
    let bounds := approach_parameter_bounds q c η hη hη1
    let qm := moveStart q t
    let hm := before_first_regular q hR c hc t bounds.1 bounds.2
    let C := crossingFromOriginal q t (lt_trans bounds.2 (leftParameter_spec q c).2.1)
      c (survives_before_first q c hc t bounds.2 c)
    let hAm := BeforeFirst.closedAuxiliary q hR c hc t bounds.1 bounds.2 hAux
    (∑ U : {U : Primitive.Support qm hm // C ∈ U.val},
      (-1 : ℚ)^U.val.val.card *
        (Primitive.openCurrent qm hm U.val *
          ∏ D ∈ Finset.univ.erase (openComponent qm hm.noTriple U.val.val),
            Primitive.closedWeight qm hm hAm U.val D)) =
      -(GeometricSmoothingWeights.separatingSmoothingSum
        (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
        (child_auxiliaryGenericity q hR c hc hcut hAux)) *
      GammaM (tinyParent q c hcut η)
        (regular_tinyParent q hR c hc hcut η hη hη1)
        (tinyParent_closedAuxiliary_from_original q hR c hc hcut η hη hη1 hAux) := by
  have htiny := tinyParent_GammaM_eq_weighted_approach q hR c hc hcut η hη hη1 hRI hAux
  simp only [parent_prefix_approach_endpoint q hR c hc hcut] at htiny
  have bounds := approach_parameter_bounds q c η hη hη1
  have hfactor := gammaM_selectedCut_before_first q hR c hc hcut hAux hRI
    (leftParameter q c*(1-η)) bounds.1 bounds.2
  dsimp only
  rw [hfactor, ← htiny]

/-- The selected-cut constant is obtained by substituting the actual tiny-parent
 limit into the finite factorization. No separate selected-cut projector is used. -/
theorem exists_selectedCut_constant_from_actual_tinyParent
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
    (∑ U : {U : Primitive.Support qm hm // C ∈ U.val},
      (-1 : ℚ)^U.val.val.card *
        (Primitive.openCurrent qm hm U.val *
          ∏ D ∈ Finset.univ.erase (openComponent qm hm.noTriple U.val.val),
            Primitive.closedWeight qm hm hAm U.val D)) =
      ((1+scalarSignValue (planarDet (q 1-q 0)
        (q c.val.2.succ-q c.val.2.castSucc)))/2) *
        (GeometricSmoothingWeights.separatingSmoothingSum
          (child q hR c hc.1 hcut)
          (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
          (child_auxiliaryGenericity q hR c hc hcut hAux) *
          Primitive.GammaM (parent q c hcut) (regular_parent q hR c hcut)
            (parent_closedAuxiliary q hR c hc hcut hAux)) := by
  obtain ⟨r,hr,hr1,hvalue⟩ := exists_actual_tinyParent_GammaM_limit
    q hR c hc hcut hAux hRI hG1 hL
  refine ⟨r,hr,hr1,?_⟩
  intro η hη hηr
  have hfinite := selectedCut_eq_actual_tinyParent q hR c hc hcut hAux hRI
    η hη (lt_of_lt_of_le hηr hr1)
  have hlimit := hvalue η hη hηr
  dsimp only at hfinite ⊢
  rw [hfinite,hlimit]
  ring

end DirectGLSSW.ActiveArc.LiteralTinyParent
