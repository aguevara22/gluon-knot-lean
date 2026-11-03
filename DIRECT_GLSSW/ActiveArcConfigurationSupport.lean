import ActiveArcEventMap
import ActiveArcGammaM
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ConfigurationTransport
open DirectGLSSW ActiveArc Nonalternation FiniteCycleOrder ConfigurationLocality
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q r : Fin (n+2) → PlanarPoint ℝ) (hQ : Regular q) (hR : Regular r)
variable (E : Crossing q ≃ Crossing r)
variable (horder : ∀ x y : Event q, (eventOrder q hQ.noTriple).lt x y ↔
  (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y))

/-- Internal order isomorphism induced by the actual crossing map; the configuration
neighborhood theorem supplies its order premise. -/
def eventOrderIso :
    letI := eventOrder q hQ.noTriple
    letI := eventOrder r hR.noTriple
    Event q ≃o Event r := by
  letI := eventOrder q hQ.noTriple
  letI := eventOrder r hR.noTriple
  refine {toEquiv := eventMapEquiv q r E, map_rel_iff' := ?_}
  intro x y
  simpa only [not_lt] using not_congr (horder y x).symm

include horder in
theorem event_between (x y z : Event q) :
    Nonalternation.between r hR (eventMapEquiv q r E x) (eventMapEquiv q r E y) (eventMapEquiv q r E z) ↔
      Nonalternation.between q hQ x y z := by
  letI := eventOrder q hQ.noTriple
  letI := eventOrder r hR.noTriple
  exact strictCyclicBetween_orderIso (eventOrderIso q r hQ hR E horder) x y z

/-- Actual finite supports transported by the same crossing equivalence. -/
def selectionEquiv : Finset (Crossing q) ≃ Finset (Crossing r) := E.finsetCongr

@[simp] theorem selectionEquiv_mem (S : Finset (Crossing q)) (c : Crossing q) :
    E c∈selectionEquiv q r E S ↔ c∈S := by
  change E c∈S.map E.toEmbedding ↔ c∈S
  simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply]

@[simp] theorem selectionEquiv_card (S : Finset (Crossing q)) :
    (selectionEquiv q r E S).card=S.card := Finset.card_map _

include horder in
theorem selectionEquiv_nonalternating (S : Finset (Crossing q)) :
    Nonalternation.Nonalternating r hR (selectionEquiv q r E S) ↔
      Nonalternation.Nonalternating q hQ S := by
  have hb (d e : Crossing q) (b : Bool) :
      Nonalternation.between r hR (Sum.inr (E d,false)) (Sum.inr (E e,b)) (Sum.inr (E d,true)) ↔
      Nonalternation.between q hQ (Sum.inr (d,false)) (Sum.inr (e,b)) (Sum.inr (d,true)) :=
    event_between q r hQ hR E horder (Sum.inr (d,false)) (Sum.inr (e,b)) (Sum.inr (d,true))
  constructor
  · intro h d hd e he hde
    have hh := h (E d) (Finset.mem_map.mpr ⟨d,hd,rfl⟩)
      (E e) (Finset.mem_map.mpr ⟨e,he,rfl⟩) (fun hh => hde (E.injective hh))
    exact (hb d e false).symm.trans (hh.trans (hb d e true))
  · intro h d hd e he hde
    obtain ⟨d',hd',hdd⟩ := Finset.mem_map.mp (show d∈S.map E.toEmbedding from hd)
    obtain ⟨e',he',hee⟩ := Finset.mem_map.mp (show e∈S.map E.toEmbedding from he)
    subst d; subst e
    have hh := h d' hd' e' he' (fun hh => hde (congrArg E hh))
    exact (hb d' e' false).trans (hh.trans (hb d' e' true).symm)

/-- The exact actual nonalternating support equivalence induced by event order. -/
def supportEquiv : Primitive.Support q hQ ≃ Primitive.Support r hR :=
  (selectionEquiv q r E).subtypeEquiv (fun S => (selectionEquiv_nonalternating q r hQ hR E horder S).symm)

@[simp] theorem supportEquiv_val (S : Primitive.Support q hQ) :
    (supportEquiv q r hQ hR E horder S).val=selectionEquiv q r E S.val := rfl

@[simp] theorem supportEquiv_card (S : Primitive.Support q hQ) :
    (supportEquiv q r hQ hR E horder S).val.card=S.val.card := Finset.card_map _

end DirectGLSSW.ActiveArc.ConfigurationTransport
