import ActiveArcBeforeFirstDaughters
import ActiveArcGammaM

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.BeforeFirst
open DirectGLSSW ActiveArc Nonalternation
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
variable (t : ℝ) (ht0 : 0 ≤ t) (htc : t < leftParameter q c)

/-- Literal anchors are fixed and each actual visit retains its physical crossing label. -/
def eventEquiv : Event (moveStart q t) ≃ Event q :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr
    (crossingEquiv_before_first q hR c hc t ht0 htc) (Equiv.refl Bool))

@[simp] theorem eventEquiv_anchor (i : Fin (n+2)) :
    eventEquiv q hR c hc t ht0 htc (Sum.inl i) = Sum.inl i := rfl

@[simp] theorem eventEquiv_visit (d : Crossing (moveStart q t)) (b : Bool) :
    eventEquiv q hR c hc t ht0 htc (Sum.inr (d,b)) =
      Sum.inr (crossingEquiv_before_first q hR c hc t ht0 htc d,b) := rfl

@[simp] theorem eventEquiv_edgeTag (x : Event (moveStart q t)) :
    edgeTag q (eventEquiv q hR c hc t ht0 htc x) = edgeTag (moveStart q t) x := by
  cases x with
  | inl i => rfl
  | inr v => rcases v with ⟨d,b⟩; cases b <;> rfl

/-- First-edge visit parameters change by the actual positive affine coordinate map. -/
theorem visitParameter_first (v : Visit (moveStart q t)) (hv : visitEdge (moveStart q t) v = 0) :
    visitParameter q (crossingEquiv_before_first q hR c hc t ht0 htc v.1,v.2) =
      t + (1-t) * visitParameter (moveStart q t) v := by
  rcases v with ⟨d,b⟩
  cases b with
  | false =>
    exact crossingEquiv_firstParameter q hR t ht0
      (lt_trans htc (leftParameter_spec q c).2.1) d hv
  | true =>
    have hh := d.property.1
    change d.val.2=0 at hv
    rw [hv] at hh
    exact False.elim ((not_lt_of_ge (Fin.zero_le _)) hh)

/-- Parameters on all other physical edges are unchanged. -/
theorem visitParameter_other (v : Visit (moveStart q t)) (hv : visitEdge (moveStart q t) v ≠ 0) :
    visitParameter q (crossingEquiv_before_first q hR c hc t ht0 htc v.1,v.2) =
      visitParameter (moveStart q t) v := by
  rcases v with ⟨d,b⟩
  cases b with
  | false =>
    exact crossingEquiv_leftParameter q hR t ht0
      (lt_trans htc (leftParameter_spec q c).2.1) d hv
  | true =>
    exact crossingEquiv_rightParameter q hR t ht0
      (lt_trans htc (leftParameter_spec q c).2.1) d

/-- For events on one edge, parameter order is unchanged, including the zero anchor. -/
theorem eventEquiv_parameter_lt (x y : Event (moveStart q t))
    (he : edgeTag (moveStart q t) x = edgeTag (moveStart q t) y) :
    parameter q (eventEquiv q hR c hc t ht0 htc x) <
      parameter q (eventEquiv q hR c hc t ht0 htc y) ↔
    parameter (moveStart q t) x < parameter (moveStart q t) y := by
  cases x with
  | inl i =>
    cases y with
    | inl j => rfl
    | inr v =>
      change 0 < visitParameter q (_,v.2) ↔ 0 < visitParameter (moveStart q t) v
      exact iff_of_true (visitParameter_spec q _).1 (visitParameter_spec (moveStart q t) v).1
  | inr v =>
    cases y with
    | inl j =>
      change visitParameter q (_,v.2) < 0 ↔ visitParameter (moveStart q t) v < 0
      exact iff_of_false (not_lt_of_ge (visitParameter_spec q _).1.le)
        (not_lt_of_ge (visitParameter_spec (moveStart q t) v).1.le)
    | inr w =>
      have hev : visitEdge (moveStart q t) v = visitEdge (moveStart q t) w := Fin.ext he
      change visitParameter q (_,v.2) < visitParameter q (_,w.2) ↔
        visitParameter (moveStart q t) v < visitParameter (moveStart q t) w
      by_cases hv : visitEdge (moveStart q t) v = 0
      · have hw := hev.symm.trans hv
        rw [visitParameter_first q hR c hc t ht0 htc v hv,
          visitParameter_first q hR c hc t ht0 htc w hw]
        exact (add_lt_add_iff_left t).trans (mul_lt_mul_left (by
          have := lt_trans htc (leftParameter_spec q c).2.1
          linarith : 0 < 1-t))
      · have hw : visitEdge (moveStart q t) w ≠ 0 := fun h => hv (hev.trans h)
        rw [visitParameter_other q hR c hc t ht0 htc v hv,
          visitParameter_other q hR c hc t ht0 htc w hw]

/-- The complete physical event order is preserved before the first event. -/
theorem eventEquiv_lt (x y : Event (moveStart q t)) :
    (letI := eventOrder q hR.noTriple;
      eventEquiv q hR c hc t ht0 htc x < eventEquiv q hR c hc t ht0 htc y) ↔
    (letI := eventOrder (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple; x < y) := by
  rw [event_lt_iff,event_lt_iff,eventEquiv_edgeTag,eventEquiv_edgeTag]
  by_cases he : edgeTag (moveStart q t) x = edgeTag (moveStart q t) y
  · rw [eventEquiv_parameter_lt q hR c hc t ht0 htc x y he]
  · simp only [he,false_and,or_false]

/-- Actual event order isomorphism, with proved label and order characterizations. -/
def eventOrderIso :
    letI := eventOrder q hR.noTriple
    letI := eventOrder (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple
    Event (moveStart q t) ≃o Event q := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (moveStart q t)
    (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple
  refine { toEquiv := eventEquiv q hR c hc t ht0 htc, map_rel_iff' := ?_ }
  intro x y
  simpa only [not_lt] using not_congr (eventEquiv_lt q hR c hc t ht0 htc y x)

end DirectGLSSW.ActiveArc.Cursor.BeforeFirst
