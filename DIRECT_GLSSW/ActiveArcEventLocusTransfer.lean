import ActiveArcConfigurationEventPairs
import ActiveArcEventSuppliedLines
import ActiveArcEventCarrierFamily
import ActiveArcFirstCrossingTransport
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ConfigurationTransport
open DirectGLSSW ActiveArc ConfigurationLocality Cursor RetainedWords OpenCarrier Primitive AuxiliaryCarrierChart
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q r : Fin (n+2) → PlanarPoint ℝ) (hQ : Regular q) (hR : Regular r)
variable (E : Crossing q ≃ Crossing r) (hlabels : ∀ c, (E c).val=c.val)
variable (horder : ∀ x y : Event q, (eventOrder q hQ.noTriple).lt x y ↔
  (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y))
variable (c : Crossing q) (hc : FirstCrossing q c)
variable (L : Fin (n+1) ⊕ Unit → CarrierLine)
variable (hinc : ∀ e : Fin (n+1), lineValue (L (Sum.inl e)) (r e.castSucc)=0 ∧
  lineValue (L (Sum.inl e)) (r e.succ)=0)
variable (hterminal : lineValue (L (Sum.inr ())) (r ⟨n+1,by omega⟩)=0)
variable (hden : ∀ U : Support q hQ, ∀ i : Fin (openCount q hQ U.val),
  lineDenominator (L (eventCarrierPair q hQ c U i).1) (L (eventCarrierPair q hQ c U i).2)≠0)

include hlabels horder hinc hterminal hden hc in
/-- Fixed original event pairs evaluated at supplied lines recover mapped actual
nearby event-word coordinates. -/
theorem mapped_event_supplied_intersection (U : Support q hQ)
    (i : Fin (openCount r hR (supportEquiv q r hQ hR E horder U).val)) :
    let j := Fin.cast (event_open_count q r hQ hR E horder U) i
    lineIntersection (L (eventCarrierPair q hQ c U j).1)
      (L (eventCarrierPair q hQ c U j).2)=
      eventOpenWord r hR (supportEquiv q r hQ hR E horder U) (E c) i.val := by
  intro j
  have hp := event_pair_eq q r hQ hR E hlabels horder U c i j rfl
  have hd : lineDenominator (L (eventCarrierPair r hR (E c) (supportEquiv q r hQ hR E horder U) i).1)
      (L (eventCarrierPair r hR (E c) (supportEquiv q r hQ hR E horder U) i).2)≠0 := by
    rw [hp];exact hden U j
  have hh := event_pair_supplied_intersection r hR (E c) (supportEquiv q r hQ hR E horder U)
    L hinc hterminal (firstCrossing_transport_of_event_order q r hQ hR E hlabels horder c hc) i hd
  rw [hp] at hh
  exact hh

include hlabels horder hinc hterminal hden hc in
/-- The simultaneous original-label locus supplies the actual mapped support's
finite determinant domain, with its actual crossed-carrier exception. -/
theorem mapped_event_nonvanishing (hF : eventCarrierLocus q hQ c L)
    (U : Support q hQ) (hu : c∉U.val) :
    EventCarrierNonvanishing r hR (E c) (supportEquiv q r hQ hR E horder U) := by
  let V := supportEquiv q r hQ hR E horder U
  let hn := event_open_count q r hQ hR E horder U
  intro i j k hij hjk hkN hexc
  change k≤openCount r hR V.val-1 at hkN
  have hiN : i<openCount r hR V.val := by omega
  have hjN : j<openCount r hR V.val := by omega
  have hkN' : k<openCount r hR V.val := by omega
  let ii : Fin (openCount r hR V.val) := ⟨i,hiN⟩
  let jj : Fin (openCount r hR V.val) := ⟨j,hjN⟩
  let kk : Fin (openCount r hR V.val) := ⟨k,hkN'⟩
  let i0 := Fin.cast hn ii
  let j0 := Fin.cast hn jj
  let k0 := Fin.cast hn kk
  have hjS : j<openCount r hR V.val-1 := by omega
  have hexc' : i0.val≠0 ∨ k0.val≠j0.val+1 ∨ eventCarrierChain q hQ U j0≠Sum.inl c.val.2 := by
    rcases hexc with hh|hh|hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
    · right;right
      intro he
      apply hh
      have hx := event_chain_eq q r hQ hR E hlabels horder U jj j0 rfl
      rw [he] at hx
      have hy : eventCarrierChain r hR V jj=Sum.inl (E c).val.2 := by
        simpa only [hlabels] using hx
      simpa only [eventCarrierChain,jj,Fin.val_mk,dif_pos hjS,Sum.inl.injEq] using hy
  have hnz := hF U hu i0 j0 k0 hij hjk hexc'
  intro hz
  apply hnz
  unfold eventTripleNumerator
  apply (carrierTripleNumerator_zero_iff _ _ _ _ _ _ (hden U i0) (hden U j0) (hden U k0)).mpr
  rw [mapped_event_supplied_intersection q r hQ hR E hlabels horder c hc L hinc hterminal hden U ii,
    mapped_event_supplied_intersection q r hQ hR E hlabels horder c hc L hinc hterminal hden U jj,
    mapped_event_supplied_intersection q r hQ hR E hlabels horder c hc L hinc hterminal hden U kk]
  have hsign : planarDet (eventOpenWord r hR V (E c) j-eventOpenWord r hR V (E c) i)
      (eventOpenWord r hR V (E c) k-eventOpenWord r hR V (E c) i)=
      -polygonHDet (eventOpenWord r hR V (E c)) i j k := by
    simp only [polygonHDet,planarDet,Prod.fst_sub,Prod.snd_sub];ring
  exact hsign.trans (by rw [hz,neg_zero])

include hlabels horder hinc hterminal hden hc in
/-- Inverse support transport covers every actual nearby c-excluded support. -/
theorem all_event_nonvanishing (hF : eventCarrierLocus q hQ c L)
    (V : Support r hR) (hv : E c∉V.val) : EventCarrierNonvanishing r hR (E c) V := by
  obtain ⟨U,rfl⟩ := (supportEquiv q r hQ hR E horder).surjective V
  have hu : c∉U.val := by
    intro hh
    apply hv
    exact (selectionEquiv_mem q r E U.val c).mpr hh
  exact mapped_event_nonvanishing q r hQ hR E hlabels horder c hc L hinc hterminal hden hF U hu
end DirectGLSSW.ActiveArc.ConfigurationTransport
