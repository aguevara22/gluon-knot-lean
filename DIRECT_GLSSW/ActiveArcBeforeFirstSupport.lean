import ActiveArcBeforeFirstEvents

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.BeforeFirst
open DirectGLSSW ActiveArc Nonalternation FiniteCycleOrder
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
variable (t : ℝ) (ht0 : 0 ≤ t) (htc : t < leftParameter q c)

theorem eventEquiv_between (x y z : Event (moveStart q t)) :
    Nonalternation.between q hR (eventEquiv q hR c hc t ht0 htc x)
      (eventEquiv q hR c hc t ht0 htc y) (eventEquiv q hR c hc t ht0 htc z) ↔
    Nonalternation.between (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc) x y z := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (moveStart q t)
    (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple
  exact strictCyclicBetween_orderIso (eventOrderIso q hR c hc t ht0 htc) x y z

/-- Actual finite physical crossing selections transported to their unchanged original labels. -/
def selectionEquiv : Finset (Crossing (moveStart q t)) ≃ Finset (Crossing q) :=
  (crossingEquiv_before_first q hR c hc t ht0 htc).finsetCongr

@[simp] theorem selectionEquiv_card (S : Finset (Crossing (moveStart q t))) :
    (selectionEquiv q hR c hc t ht0 htc S).card = S.card := Finset.card_map _

theorem selectionEquiv_nonalternating (S : Finset (Crossing (moveStart q t))) :
    Nonalternation.Nonalternating q hR (selectionEquiv q hR c hc t ht0 htc S) ↔
    Nonalternation.Nonalternating (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc) S := by
  let E := crossingEquiv_before_first q hR c hc t ht0 htc
  have hb (d e : Crossing (moveStart q t)) (b : Bool) :
      Nonalternation.between q hR (Sum.inr (E d,false)) (Sum.inr (E e,b)) (Sum.inr (E d,true)) ↔
      Nonalternation.between (moveStart q t)
        (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc)
        (Sum.inr (d,false)) (Sum.inr (e,b)) (Sum.inr (d,true)) :=
    eventEquiv_between q hR c hc t ht0 htc (Sum.inr (d,false)) (Sum.inr (e,b)) (Sum.inr (d,true))
  constructor
  · intro h d hd e he hde
    have hh := h (E d) (Finset.mem_map.mpr ⟨d,hd,rfl⟩)
      (E e) (Finset.mem_map.mpr ⟨e,he,rfl⟩) (fun hh => hde (E.injective hh))
    exact (hb d e false).symm.trans (hh.trans (hb d e true))
  · intro h d hd e he hde
    obtain ⟨d',hd',hdd⟩ := Finset.mem_map.mp (show d ∈ S.map E.toEmbedding from hd)
    obtain ⟨e',he',hee⟩ := Finset.mem_map.mp (show e ∈ S.map E.toEmbedding from he)
    subst d; subst e
    have hh := h d' hd' e' he' (fun hh => hde (congrArg E hh))
    exact (hb d' e' false).trans (hh.trans (hb d' e' true).symm)

/-- Exact actual nonalternating support equivalence throughout the pre-first chamber. -/
def supportEquiv :
    Primitive.Support (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc) ≃ Primitive.Support q hR :=
  (selectionEquiv q hR c hc t ht0 htc).subtypeEquiv
    (fun S => (selectionEquiv_nonalternating q hR c hc t ht0 htc S).symm)

@[simp] theorem supportEquiv_val
    (S : Primitive.Support (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc)) :
    (supportEquiv q hR c hc t ht0 htc S).val = selectionEquiv q hR c hc t ht0 htc S.val := rfl

@[simp] theorem supportEquiv_card
    (S : Primitive.Support (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc)) :
    (supportEquiv q hR c hc t ht0 htc S).val.card = S.val.card := Finset.card_map _

end DirectGLSSW.ActiveArc.Cursor.BeforeFirst
