import ActiveArcLiteralTinyParentCrossings
import ActiveArcExposedSupports
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split Primitive OpenFirstEdgeGeometry Nonalternation FiniteCycleOrder
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (η : ℝ) (hη : 0<η) (hη1 : η<1)

theorem crossingFromParent_visit_lt
    (d e : Crossing (parent q c hcut)) (s t : Bool) :
    (eventOrder (tinyParent q c hcut η) (regular_tinyParent q hR c hc hcut η hη hη1).noTriple).lt
      (Sum.inr (crossingFromParent q c hcut η d,s))
      (Sum.inr (crossingFromParent q c hcut η e,t)) ↔
    (eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple).lt
      (Sum.inr (d,s)) (Sum.inr (e,t)) := by
  rw [event_lt_iff,event_lt_iff]
  have htag (d : Crossing (parent q c hcut)) (s : Bool) :
      edgeTag (tinyParent q c hcut η) (Sum.inr (crossingFromParent q c hcut η d,s))=
        edgeTag (parent q c hcut) (Sum.inr (d,s))+1 := by
    cases s <;> rfl
  have hparam (d : Crossing (parent q c hcut)) (s : Bool) :
      parameter (tinyParent q c hcut η) (Sum.inr (crossingFromParent q c hcut η d,s))=
        parameter (parent q c hcut) (Sum.inr (d,s)) := by
    cases s
    · exact crossingFromParent_leftParameter q hR c hc hcut η hη hη1 d
    · exact crossingFromParent_rightParameter q hR c hc hcut η hη hη1 d
  simp only [htag,hparam,Nat.add_lt_add_iff_right,Nat.add_right_cancel_iff]

theorem crossingFromParent_between
    (d e f : Crossing (parent q c hcut)) (s t u : Bool) :
    Nonalternation.between (tinyParent q c hcut η) (regular_tinyParent q hR c hc hcut η hη hη1)
      (Sum.inr (crossingFromParent q c hcut η d,s))
      (Sum.inr (crossingFromParent q c hcut η e,t))
      (Sum.inr (crossingFromParent q c hcut η f,u)) ↔
    Nonalternation.between (parent q c hcut) (regular_parent q hR c hcut)
      (Sum.inr (d,s)) (Sum.inr (e,t)) (Sum.inr (f,u)) := by
  simp only [Nonalternation.between,strictCyclicBetween,
    crossingFromParent_visit_lt q hR c hc hcut η hη hη1]

/-- Actual selection map; neither nonalternation nor cardinality is an input. -/
def parentTinySelection (S : Finset (Crossing (parent q c hcut))) :
    Finset (Crossing (tinyParent q c hcut η)) :=
  S.map ⟨crossingFromParent q c hcut η,crossingFromParent_injective q c hcut η⟩

theorem parentTinySelection_card (S : Finset (Crossing (parent q c hcut))) :
    (parentTinySelection q c hcut η S).card=S.card := Finset.card_map _

theorem parentTinySelection_nonalternating
    (S : Finset (Crossing (parent q c hcut))) :
    Nonalternation.Nonalternating (tinyParent q c hcut η)
      (regular_tinyParent q hR c hc hcut η hη hη1) (parentTinySelection q c hcut η S) ↔
    Nonalternation.Nonalternating (parent q c hcut) (regular_parent q hR c hcut) S := by
  constructor
  · intro h d hd e he hde
    have hdm : crossingFromParent q c hcut η d ∈ parentTinySelection q c hcut η S :=
      Finset.mem_map.mpr ⟨d,hd,rfl⟩
    have hem : crossingFromParent q c hcut η e ∈ parentTinySelection q c hcut η S :=
      Finset.mem_map.mpr ⟨e,he,rfl⟩
    have hh:=h _ hdm _ hem (fun hh=>hde (crossingFromParent_injective q c hcut η hh))
    simpa only [crossingFromParent_between q hR c hc hcut η hη hη1] using hh
  · intro h d hd e he hde
    obtain ⟨d',hd',rfl⟩:=Finset.mem_map.mp hd
    obtain ⟨e',he',rfl⟩:=Finset.mem_map.mp he
    have hh:=h d' hd' e' he' (fun hh=>hde (congrArg (crossingFromParent q c hcut η) hh))
    change (Nonalternation.between _ _
      (Sum.inr (crossingFromParent q c hcut η d',false))
      (Sum.inr (crossingFromParent q c hcut η e',false))
      (Sum.inr (crossingFromParent q c hcut η d',true)) ↔
      Nonalternation.between _ _
      (Sum.inr (crossingFromParent q c hcut η d',false))
      (Sum.inr (crossingFromParent q c hcut η e',true))
      (Sum.inr (crossingFromParent q c hcut η d',true)))
    rw [crossingFromParent_between q hR c hc hcut η hη hη1,
      crossingFromParent_between q hR c hc hcut η hη hη1]
    exact hh

/-- All actual supports of the literal tiny parent correspond to parent supports. -/
def tinyParentSupportEquiv :
    Nonalternation.Support (tinyParent q c hcut η) (regular_tinyParent q hR c hc hcut η hη hη1) ≃
      Nonalternation.Support (parent q c hcut) (regular_parent q hR c hcut) := by
  let e := (tinyParentCrossingEquiv q hR c hc hcut η hη hη1).symm
  have he (S : Finset (Crossing (parent q c hcut))) :
      e.finsetCongr S=parentTinySelection q c hcut η S := rfl
  exact (e.finsetCongr.subtypeEquiv (fun S => by
    rw [he]
    exact (parentTinySelection_nonalternating q hR c hc hcut η hη hη1 S).symm)).symm

@[simp] theorem tinyParentSupportEquiv_symm_val
    (S : Nonalternation.Support (parent q c hcut) (regular_parent q hR c hcut)) :
    ((tinyParentSupportEquiv q hR c hc hcut η hη hη1).symm S).val=
      parentTinySelection q c hcut η S.val := rfl

@[simp] theorem tinyParentSupportEquiv_card
    (S : Nonalternation.Support (tinyParent q c hcut η) (regular_tinyParent q hR c hc hcut η hη hη1)) :
    (tinyParentSupportEquiv q hR c hc hcut η hη hη1 S).val.card=S.val.card := by
  have h:=parentTinySelection_card q c hcut η
    (tinyParentSupportEquiv q hR c hc hcut η hη hη1 S).val
  rw [←tinyParentSupportEquiv_symm_val q hR c hc hcut η hη hη1,
    Equiv.symm_apply_apply] at h
  exact h.symm

end DirectGLSSW.ActiveArc.LiteralTinyParent
