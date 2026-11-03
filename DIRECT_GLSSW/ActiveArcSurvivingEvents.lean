import ActiveArcFirstCrossing
import ActiveArcRetainedDeletion
import ActiveArcGammaM

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.Surviving
open DirectGLSSW ActiveArc PermutationOrbits CompatibleWords
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)

/-- Surviving event inclusion: anchors retain their labels; only surviving
physical crossings have visits. This is NOT a full-event equivalence. -/
def eventMap : Event (moveStart q t) → Event q
  | Sum.inl i => Sum.inl i
  | Sum.inr (d,b) => Sum.inr (crossingToOriginal q t ht0 ht1 d,b)

theorem eventMap_injective : Function.Injective (eventMap q t ht0 ht1) := by
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (Sum.inl.inj h)
    | inr v => cases h
  | inr v =>
    cases y with
    | inl i => cases h
    | inr w =>
      rcases v with ⟨d,b⟩
      rcases w with ⟨e,a⟩
      have hp := Sum.inr.inj h
      have hd : d = e := Subtype.ext (congrArg (fun z => z.1.val) hp)
      have hb : b = a := congrArg Prod.snd hp
      subst e a
      rfl

@[simp] theorem eventMap_edgeTag (x : Event (moveStart q t)) :
    edgeTag q (eventMap q t ht0 ht1 x) = edgeTag (moveStart q t) x := by
  cases x with
  | inl i => rfl
  | inr v => rcases v with ⟨d,b⟩; cases b <;> rfl

include hR in
theorem visitParameter_first (v : Visit (moveStart q t))
    (hv : visitEdge (moveStart q t) v = 0) :
    visitParameter q (crossingToOriginal q t ht0 ht1 v.1,v.2) =
      t+(1-t)*visitParameter (moveStart q t) v := by
  rcases v with ⟨d,b⟩
  cases b with
  | false => exact crossingEquiv_firstParameter q hR t ht0 ht1 d hv
  | true =>
    have hh := d.property.1
    change d.val.2=0 at hv
    rw [hv] at hh
    exact False.elim ((not_lt_of_ge (Fin.zero_le _)) hh)

include hR in
theorem visitParameter_other (v : Visit (moveStart q t))
    (hv : visitEdge (moveStart q t) v ≠ 0) :
    visitParameter q (crossingToOriginal q t ht0 ht1 v.1,v.2) =
      visitParameter (moveStart q t) v := by
  rcases v with ⟨d,b⟩
  cases b with
  | false => exact crossingEquiv_leftParameter q hR t ht0 ht1 d hv
  | true => exact crossingEquiv_rightParameter q hR t ht0 ht1 d

include hR in
theorem eventMap_parameter_lt (x y : Event (moveStart q t))
    (he : edgeTag (moveStart q t) x = edgeTag (moveStart q t) y) :
    parameter q (eventMap q t ht0 ht1 x) < parameter q (eventMap q t ht0 ht1 y) ↔
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
        rw [visitParameter_first q hR t ht0 ht1 v hv,visitParameter_first q hR t ht0 ht1 w hw]
        exact (add_lt_add_iff_left t).trans (mul_lt_mul_left (by linarith : 0 < 1-t))
      · have hw : visitEdge (moveStart q t) w ≠ 0 := fun h => hv (hev.trans h)
        rw [visitParameter_other q hR t ht0 ht1 v hv,visitParameter_other q hR t ht0 ht1 w hw]

theorem eventMap_lt (hM : Regular (moveStart q t)) (x y : Event (moveStart q t)) :
    (eventOrder q hR.noTriple).lt (eventMap q t ht0 ht1 x) (eventMap q t ht0 ht1 y) ↔
      (eventOrder (moveStart q t) hM.noTriple).lt x y := by
  rw [event_lt_iff,event_lt_iff,eventMap_edgeTag,eventMap_edgeTag]
  by_cases he : edgeTag (moveStart q t) x = edgeTag (moveStart q t) y
  · rw [eventMap_parameter_lt q hR t ht0 ht1 x y he]
  · simp only [he,false_and,or_false]

/-- Actual moved selection, pulled back along the inclusion of surviving
physical crossing labels. -/
def movingSelection (S : Finset (Crossing q)) : Finset (Crossing (moveStart q t)) :=
  Finset.univ.filter (fun d => crossingToOriginal q t ht0 ht1 d ∈ S)

@[simp] theorem movingSelection_mem (S : Finset (Crossing q)) (d : Crossing (moveStart q t)) :
    d ∈ movingSelection q t ht0 ht1 S ↔ crossingToOriginal q t ht0 ht1 d ∈ S := by
  simp only [movingSelection,Finset.mem_filter,Finset.mem_univ,true_and]

theorem eventMap_retained (S : Finset (Crossing q)) (x : Event (moveStart q t)) :
    retained q S (eventMap q t ht0 ht1 x) ↔ retained (moveStart q t) (movingSelection q t ht0 ht1 S) x := by
  cases x with
  | inl i => rfl
  | inr v => exact (movingSelection_mem q t ht0 ht1 S v.1).symm

theorem eventMap_pairing (S : Finset (Crossing q)) (x : Event (moveStart q t)) :
    eventMap q t ht0 ht1 (pairing (moveStart q t) (movingSelection q t ht0 ht1 S) x) =
      pairing q S (eventMap q t ht0 ht1 x) := by
  cases x with
  | inl i => rfl
  | inr v =>
    rcases v with ⟨d,b⟩
    by_cases hd : crossingToOriginal q t ht0 ht1 d ∈ S <;> cases b <;>
      simp [pairing,pairingMap,eventMap,movingSelection_mem,hd]

include hR in
theorem eventMap_point (x : Event (moveStart q t)) (hx : x ≠ start (moveStart q t)) :
    eventPoint (moveStart q t) x = eventPoint q (eventMap q t ht0 ht1 x) := by
  cases x with
  | inl i => exact moveStart_eq q t i (fun h => hx (congrArg Sum.inl h))
  | inr v => exact (crossingToOriginal_point q hR t ht0 ht1 v.1).symm

end DirectGLSSW.ActiveArc.Cursor.Surviving
