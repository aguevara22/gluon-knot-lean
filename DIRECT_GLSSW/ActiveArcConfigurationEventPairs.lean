import ActiveArcConfigurationOrbits
import ActiveArcOrderedEventPair
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ConfigurationTransport
open DirectGLSSW ActiveArc ConfigurationLocality Cursor RetainedWords OpenCarrier Primitive
attribute [local instance] Classical.propDecidable
private theorem ofFn_at_equal_indices {α : Type*} {m n : ℕ} (f : Fin m → α) (g : Fin n → α)
    (h : List.ofFn f=List.ofFn g) (i : Fin m) (j : Fin n) (hij : i.val=j.val) : f i=g j := by
  have hmn : m=n := by simpa only [List.length_ofFn] using congrArg List.length h
  subst n
  have hfg := List.ofFn_injective h
  rw [hfg,Fin.ext hij]
variable {n : ℕ} (q r : Fin (n+2) → PlanarPoint ℝ) (hQ : Regular q) (hR : Regular r)
variable (E : Crossing q ≃ Crossing r) (hlabels : ∀ c, (E c).val=c.val)
variable (horder : ∀ x y : Event q, (eventOrder q hQ.noTriple).lt x y ↔
  (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y))
variable (U : Support q hQ)

theorem event_open_count :
    openCount r hR (supportEquiv q r hQ hR E horder U).val=openCount q hQ U.val :=
  retained_count q r hQ hR E horder U.val (start q)

include hlabels in
theorem event_sideCarrier_eq
    (i : Fin (openCount r hR (supportEquiv q r hQ hR E horder U).val-1))
    (j : Fin (openCount q hQ U.val-1)) (hij : i.val=j.val) :
    openSideCarrier r hR (supportEquiv q r hQ hR E horder U).val i=
      openSideCarrier q hQ U.val j := by
  apply Fin.ext
  exact ofFn_at_equal_indices _ _ (retained_carrier_word q r hQ hR E horder hlabels U.val (start q))
    ⟨i.val,by change i.val < openCount r hR (supportEquiv q r hQ hR E horder U).val;have := i.isLt;omega⟩
    ⟨j.val,by change j.val < openCount q hQ U.val;have := j.isLt;omega⟩ hij

include hlabels in
theorem event_chain_eq
    (i : Fin (openCount r hR (supportEquiv q r hQ hR E horder U).val))
    (j : Fin (openCount q hQ U.val)) (hij : i.val=j.val) :
    eventCarrierChain r hR (supportEquiv q r hQ hR E horder U) i=
      eventCarrierChain q hQ U j := by
  have hn := event_open_count q r hQ hR E horder U
  by_cases hi : i.val<openCount r hR (supportEquiv q r hQ hR E horder U).val-1
  · have hj : j.val<openCount q hQ U.val-1 := by omega
    simp only [eventCarrierChain,dif_pos hi,dif_pos hj]
    exact congrArg Sum.inl (event_sideCarrier_eq q r hQ hR E hlabels horder U _ _ hij)
  · have hj : ¬j.val<openCount q hQ U.val-1 := by omega
    simp only [eventCarrierChain,dif_neg hi,dif_neg hj]

include hlabels in
theorem event_pair_eq (c : Crossing q)
    (i : Fin (openCount r hR (supportEquiv q r hQ hR E horder U).val))
    (j : Fin (openCount q hQ U.val)) (hij : i.val=j.val) :
    eventCarrierPair r hR (E c) (supportEquiv q r hQ hR E horder U) i=
      eventCarrierPair q hQ c U j := by
  by_cases hi : i.val=0
  · have hj : j.val=0 := hij.symm.trans hi
    simp only [eventCarrierPair,if_pos hi,if_pos hj,hlabels]
    exact congrArg (fun x : Fin (n+1) ⊕ Unit => (x,Sum.inl c.val.2))
      (event_chain_eq q r hQ hR E hlabels horder U _ _ rfl)
  · have hj : j.val≠0 := fun hh => hi (hij.trans hh)
    simp only [eventCarrierPair,if_neg hi,if_neg hj]
    exact Prod.ext (event_chain_eq q r hQ hR E hlabels horder U _ _ (by simp only [hij]))
      (event_chain_eq q r hQ hR E hlabels horder U _ _ hij)
end DirectGLSSW.ActiveArc.ConfigurationTransport
