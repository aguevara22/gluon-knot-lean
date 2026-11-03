import ActiveArcPhysicalCurrentTransport
import ActiveArcBeforeFirstWeights

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.BeforeFirst
open DirectGLSSW ActiveArc Primitive RetainedWords EndpointEventGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
variable (t : ℝ) (ht0 : 0≤t) (htc : t<leftParameter q c)

/-- The literal surviving moved crossing is selected exactly when its original
crossing is selected in the actual transported support. -/
theorem selected_support_membership :
    let hM := before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc
    let Cm := crossingFromOriginal q t (lt_trans htc (leftParameter_spec q c).2.1)
      c (survives_before_first q c hc t htc c)
    ∀ V : Support (moveStart q t) hM,
      c ∈ (supportEquiv q hR c hc t ht0 htc V).val ↔ Cm ∈ V.val := by
  dsimp only
  intro V
  let Cm := crossingFromOriginal q t (lt_trans htc (leftParameter_spec q c).2.1)
    c (survives_before_first q c hc t htc c)
  have himage : crossingEquiv_before_first q hR c hc t ht0 htc Cm = c := by
    apply Subtype.ext
    rfl
  change c ∈ selectionEquiv q hR c hc t ht0 htc V.val ↔ Cm ∈ V.val
  have hmem := selectionEquiv_mem q hR c hc t ht0 htc V.val Cm
  simpa only [himage] using hmem

/-- Restrict the actual pre-first support equivalence to the full selected
subtypes, using proved physical crossing membership. -/
def selectedSupportEquiv :
    let hM := before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc
    let Cm := crossingFromOriginal q t (lt_trans htc (leftParameter_spec q c).2.1)
      c (survives_before_first q c hc t htc c)
    {V : Support (moveStart q t) hM // Cm ∈ V.val} ≃
      {U : Support q hR // c ∈ U.val} := by
  dsimp only
  exact (supportEquiv q hR c hc t ht0 htc).subtypeEquiv
    (fun V => (selected_support_membership q hR c hc t ht0 htc V).symm)

/-- Exact selected-subtype reindex of the actual physical pre-first sum into
original selected supports and their literal endpoint-event currents. -/
theorem selected_sum_eq_original_event
    (hRI : GLSSWRootIndependence) (hAux : ClosedAuxiliary q hR) :
    let hM := before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc
    let Cm := crossingFromOriginal q t (lt_trans htc (leftParameter_spec q c).2.1)
      c (survives_before_first q c hc t htc c)
    let hAm := closedAuxiliary q hR c hc t ht0 htc hAux
    (∑ V : {V : Support (moveStart q t) hM // Cm ∈ V.val},
      (-1 : ℚ)^V.val.val.card *
        (openCurrent (moveStart q t) hM V.val *
          ∏ C∈Finset.univ.erase (openComponent (moveStart q t) hM.noTriple V.val.val),
            closedWeight (moveStart q t) hM hAm V.val C)) =
    (∑ U : {U : Support q hR // c ∈ U.val},
      (-1 : ℚ)^U.val.val.card *
        (OpenMarkedCurrent.entry
          (polygonSignArray (moveEndpoint (eventOpenWord q hR U.val c)
            (q 1-q 0) (t-leftParameter q c))) 0 (openCount q hR U.val.val-1) *
          ∏ C∈Finset.univ.erase (openComponent q hR.noTriple U.val.val),
            closedWeight q hR hAux U.val C)) := by
  dsimp only
  let e := selectedSupportEquiv q hR c hc t ht0 htc
  apply Fintype.sum_equiv e
  intro V
  have hcard := supportEquiv_card q hR c hc t ht0 htc V.val
  have hprod := closedWeight_product_eq q hR c hc t ht0 htc hRI hAux V.val
  have hcur := before_first_openCurrent_eq_event q hR c hc t ht0 htc
    (supportEquiv q hR c hc t ht0 htc V.val)
  dsimp only at hcur
  rw [Equiv.symm_apply_apply] at hcur
  change (-1 : ℚ)^V.val.val.card * (_ * _) =
    (-1 : ℚ)^(supportEquiv q hR c hc t ht0 htc V.val).val.card * (_ * _)
  rw [hcard, ← hprod, hcur]
  rfl




end DirectGLSSW.ActiveArc.Cursor.BeforeFirst
