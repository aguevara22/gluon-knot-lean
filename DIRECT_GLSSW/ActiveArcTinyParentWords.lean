import ActiveArcLiteralTinyParentSupports
import ActiveArcGammaM
import DirectGLSSW.PermutationInsertionWords

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split Primitive OpenFirstEdgeGeometry Nonalternation RetainedWords PhysicalSegments PermutationOrbits
attribute [local instance] Classical.propDecidable

variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (η : ℝ) (hη : 0<η) (hη1 : η<1)

abbrev Tiny := tinyParent q c hcut η
abbrev Parent := parent q c hcut
abbrev TinyReg := regular_tinyParent q hR c hc hcut η hη hη1
abbrev ParentReg := regular_parent q hR c hcut

/-- The old parent event order is embedded after the new initial anchor. -/
def parentEventIntoTiny (x : Event (parent q c hcut)) : Event (tinyParent q c hcut η) :=
  match x with
  | .inl i => .inl i.succ
  | .inr v => .inr (crossingFromParent q c hcut η v.1,v.2)

theorem parentEventIntoTiny_injective :
    Function.Injective (parentEventIntoTiny q c hcut η) := by
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      have hh : i.succ=j.succ := by
        change Sum.inl i.succ=Sum.inl j.succ at hxy
        exact Sum.inl.inj hxy
      exact congrArg Sum.inl (Fin.succ_inj.mp hh)
    | inr v => cases hxy
  | inr v =>
    cases y with
    | inl j => cases hxy
    | inr w =>
      have hp : (crossingFromParent q c hcut η v.1,v.2)=
          (crossingFromParent q c hcut η w.1,w.2) := by
        change Sum.inr (crossingFromParent q c hcut η v.1,v.2)=
          Sum.inr (crossingFromParent q c hcut η w.1,w.2) at hxy
        exact Sum.inr.inj hxy
      have hfirst := congrArg Prod.fst hp
      have hsecond := congrArg Prod.snd hp
      exact congrArg Sum.inr
        (Prod.ext (crossingFromParent_injective q c hcut η hfirst) hsecond)

theorem parentEventIntoTiny_tag (x : Event (parent q c hcut)) :
    edgeTag (tinyParent q c hcut η) (parentEventIntoTiny q c hcut η x)=
      edgeTag (parent q c hcut) x+1 := by
  cases x with
  | inl i => simp [parentEventIntoTiny,edgeTag]
  | inr v =>
    rcases v with ⟨d,side⟩
    cases side <;> simp [parentEventIntoTiny,edgeTag,visitEdge,crossingFromParent]

theorem parentEventIntoTiny_parameter (hR : Regular q) (hc : FirstCrossing q c)
    (hη : 0<η) (hη1 : η<1) (x : Event (parent q c hcut)) :
    parameter (tinyParent q c hcut η) (parentEventIntoTiny q c hcut η x)=
      parameter (parent q c hcut) x := by
  cases x with
  | inl i => rfl
  | inr v =>
    rcases v with ⟨d,side⟩
    cases side
    · exact crossingFromParent_leftParameter q hR c hc hcut η hη hη1 d
    · exact crossingFromParent_rightParameter q hR c hc hcut η hη hη1 d

theorem parentEventIntoTiny_order (hR : Regular q) (hc : FirstCrossing q c)
    (hη : 0<η) (hη1 : η<1) (x y : Event (parent q c hcut)) :
    (letI := eventOrder (tinyParent q c hcut η)
      (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
    ;
      parentEventIntoTiny q c hcut η x < parentEventIntoTiny q c hcut η y) ↔
    (letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple; x<y) := by
  have hpx := parentEventIntoTiny_parameter (q:=q) (hR:=hR) (c:=c) (hc:=hc)
    (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) x
  have hpy := parentEventIntoTiny_parameter (q:=q) (hR:=hR) (c:=c) (hc:=hc)
    (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) y
  rw [event_lt_iff,event_lt_iff,parentEventIntoTiny_tag,parentEventIntoTiny_tag,hpx,hpy]
  simp only [Nat.add_lt_add_iff_right,Nat.add_right_cancel_iff]

theorem parentEventIntoTiny_le (hR : Regular q) (hc : FirstCrossing q c)
    (hη : 0<η) (hη1 : η<1) (x y : Event (parent q c hcut)) :
    (letI := eventOrder (tinyParent q c hcut η)
      (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
    ;
      parentEventIntoTiny q c hcut η x ≤ parentEventIntoTiny q c hcut η y) ↔
    (letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple; x≤y) := by
  letI := eventOrder (tinyParent q c hcut η)
    (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
  letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
  constructor
  · intro h
    rcases le_iff_lt_or_eq.mp h with hlt|he
    · exact le_of_lt ((parentEventIntoTiny_order (q:=q) (hR:=hR) (c:=c) (hc:=hc)
        (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) x y).mp hlt)
    · exact le_of_eq (parentEventIntoTiny_injective q c hcut η he)
  · intro h
    rcases le_iff_lt_or_eq.mp h with hlt|he
    · exact le_of_lt ((parentEventIntoTiny_order (q:=q) (hR:=hR) (c:=c) (hc:=hc)
        (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) x y).mpr hlt)
    · exact le_of_eq (congrArg (parentEventIntoTiny q c hcut η) he)

theorem parentEventIntoTiny_surjective_nonstart (hR : Regular q)
    (hc : FirstCrossing q c) (hη : 0<η) (hη1 : η<1)
    (z : Event (tinyParent q c hcut η)) (hz : z≠start (tinyParent q c hcut η)) :
    ∃ x : Event (parent q c hcut), parentEventIntoTiny q c hcut η x=z := by
  cases z with
  | inl i =>
    have hi : i≠0 := by
      intro hh
      apply hz
      apply congrArg Sum.inl
      exact hh
    obtain ⟨j,hj⟩ := Fin.exists_succ_eq_of_ne_zero hi
    exact ⟨Sum.inl j,by simp [parentEventIntoTiny,hj]⟩
  | inr v =>
    obtain ⟨d,hd⟩ := crossingFromParent_surjective (q:=q) (hR:=hR)
      (c:=c) (hc:=hc) (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) v.1
    exact ⟨Sum.inr (d,v.2),by simp [parentEventIntoTiny,hd]⟩

theorem parentEventIntoTiny_successor (hR : Regular q) (hc : FirstCrossing q c)
    (hη : 0<η) (hη1 : η<1) (x : Event (parent q c hcut))
    (hx : x≠terminal (parent q c hcut)) :
    successor (tinyParent q c hcut η)
      (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
      (parentEventIntoTiny q c hcut η x)=
    parentEventIntoTiny q c hcut η
      (successor (parent q c hcut) (regular_parent q hR c hcut).noTriple x) := by
  letI := eventOrder (tinyParent q c hcut η)
    (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
  letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
  change orderedCyclicSuccessor (Event (tinyParent q c hcut η))
    (parentEventIntoTiny q c hcut η x)=_
  apply orderedCyclicSuccessor_eq_of_order_spec
  left
  constructor
  · exact (parentEventIntoTiny_order (q:=q) (hR:=hR) (c:=c) (hc:=hc)
      (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) x
      (successor (parent q c hcut) (regular_parent q hR c hcut).noTriple x)).mpr
      (successor_strict_before_terminal (parent q c hcut)
        (regular_parent q hR c hcut).noTriple x hx)
  · intro z hzx
    have hz : z≠start (tinyParent q c hcut η) := by
      intro he
      subst z
      have hs := start_le (tinyParent q c hcut η)
        (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
        (parentEventIntoTiny q c hcut η x)
      exact (not_lt_of_ge hs) hzx
    obtain ⟨y,rfl⟩ := parentEventIntoTiny_surjective_nonstart
      (q:=q) (hR:=hR) (c:=c) (hc:=hc) (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) z hz
    have hxy := (parentEventIntoTiny_order (q:=q) (hR:=hR) (c:=c) (hc:=hc)
      (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) x y).mp hzx
    have hmin := successor_min (parent q c hcut)
      (regular_parent q hR c hcut) x y hx hxy
    exact (parentEventIntoTiny_le (q:=q) (hR:=hR) (c:=c) (hc:=hc)
      (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1)
      (successor (parent q c hcut) (regular_parent q hR c hcut).noTriple x) y).mpr hmin

theorem parentEventIntoTiny_ne_start (hR : Regular q) (hc : FirstCrossing q c)
    (hη : 0<η) (hη1 : η<1) (x : Event (parent q c hcut)) :
    parentEventIntoTiny q c hcut η x≠start (tinyParent q c hcut η) := by
  intro h
  have ht := congrArg (edgeTag (tinyParent q c hcut η)) h
  rw [parentEventIntoTiny_tag] at ht
  simp only [start,edgeTag] at ht
  omega

def parentEventIntoTinyNonstart (hR : Regular q) (hc : FirstCrossing q c)
    (hη : 0<η) (hη1 : η<1) :
    Event (parent q c hcut) ≃ {z : Event (tinyParent q c hcut η) // z≠start (tinyParent q c hcut η)} :=
  Equiv.ofBijective
    (fun x => ⟨parentEventIntoTiny q c hcut η x,
      parentEventIntoTiny_ne_start (q:=q) (hR:=hR) (c:=c) (hc:=hc)
        (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) x⟩)
    ⟨fun x y hxy => parentEventIntoTiny_injective q c hcut η (congrArg Subtype.val hxy),
      fun z => by
        obtain ⟨x,hx⟩ := parentEventIntoTiny_surjective_nonstart
          (q:=q) (hR:=hR) (c:=c) (hc:=hc) (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1)
          z.val z.property
        exact ⟨x,Subtype.ext hx⟩⟩

theorem tinyParent_start_successor (hR : Regular q) (hc : FirstCrossing q c)
    (hη : 0<η) (hη1 : η<1) :
    successor (tinyParent q c hcut η)
      (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
      (start (tinyParent q c hcut η))=
    Sum.inl (1 : Fin (b+3)) := by
  letI := eventOrder (tinyParent q c hcut η)
    (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
  change orderedCyclicSuccessor (Event (tinyParent q c hcut η)) _ = _
  apply orderedCyclicSuccessor_eq_of_order_spec
  left
  constructor
  · have hlt : start (tinyParent q c hcut η) <
        (Sum.inl (⟨1,by omega⟩ : Fin (b+3)) : Event (tinyParent q c hcut η)) := by
      apply (event_lt_iff (tinyParent q c hcut η)
        (regular_tinyParent q hR c hc hcut η hη hη1).noTriple _ _).2
      left
      simp [edgeTag,start]
    exact hlt
  · intro z hsz
    have htag : 1≤edgeTag (tinyParent q c hcut η) z := by
      cases z with
      | inl i =>
        have hi : i.val≠0 := by
          intro hh
          have hEq : start (tinyParent q c hcut η)=Sum.inl i := by
            apply congrArg Sum.inl
            exact (Fin.ext hh).symm
          exact (ne_of_lt hsz) hEq
        simpa [edgeTag] using (Nat.one_le_iff_ne_zero.mpr hi)
      | inr v =>
        rcases v with ⟨d,side⟩
        have hleft := tinyParent_no_first_crossing q hR c hc hcut η hη hη1 d
        cases side
        · have hv : d.val.1.val≠0 := by
            intro hh
            exact hleft (Fin.ext hh)
          simpa [edgeTag,visitEdge] using (Nat.one_le_iff_ne_zero.mpr hv)
        · have hv : d.val.2.val≠0 := by
            intro hh
            have hd := d.property.1
            have hleftv := d.val.1.isLt
            omega
          simpa [edgeTag,visitEdge] using (Nat.one_le_iff_ne_zero.mpr hv)
    exact anchor_le_of_tag_le (tinyParent q c hcut η)
      (regular_tinyParent q hR c hc hcut η hη hη1)
      (⟨1,by omega⟩ : Fin (b+3)) z htag

theorem parentEventIntoTiny_pairing (hR : Regular q) (hc : FirstCrossing q c)
    (hη : 0<η) (hη1 : η<1)
    (T : Nonalternation.Support (parent q c hcut) (regular_parent q hR c hcut))
    (x : Event (parent q c hcut)) :
    parentEventIntoTiny q c hcut η
      (pairing (parent q c hcut) T.val x)=
    pairing (tinyParent q c hcut η) (parentTinySelection q c hcut η T.val)
      (parentEventIntoTiny q c hcut η x) := by
  cases x with
  | inl i => rfl
  | inr v =>
    rcases v with ⟨d,side⟩
    have hmem : crossingFromParent q c hcut η d ∈ parentTinySelection q c hcut η T.val ↔
        d∈T.val := by
      constructor
      · intro hh
        obtain ⟨e,he,heq⟩ := Finset.mem_map.mp hh
        have he' := crossingFromParent_injective q c hcut η heq
        simpa [he'] using he
      · intro hh
        exact Finset.mem_map.mpr ⟨d,hh,rfl⟩
    by_cases hd : d∈T.val
    · have hmt := hmem.mpr hd
      cases side <;> simp [parentEventIntoTiny,pairing,pairingMap,hd,hmt]
    · have hmt : crossingFromParent q c hcut η d∉parentTinySelection q c hcut η T.val :=
        fun hh => hd (hmem.mp hh)
      cases side <;> simp [parentEventIntoTiny,pairing,pairingMap,hd,hmt]

theorem parentEventIntoTiny_incoming (hR : Regular q) (hc : FirstCrossing q c)
    (hη : 0<η) (hη1 : η<1)
    (T : Nonalternation.Support (parent q c hcut) (regular_parent q hR c hcut))
    (x : Event (parent q c hcut)) (hx : x≠terminal (parent q c hcut)) :
    parentEventIntoTiny q c hcut η (incoming (parent q c hcut)
      (regular_parent q hR c hcut).noTriple T.val x)=
    incoming (tinyParent q c hcut η)
      (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
      (parentTinySelection q c hcut η T.val) (parentEventIntoTiny q c hcut η x) := by
  have hxpair : pairing (parent q c hcut) T.val x≠terminal (parent q c hcut) := by
    intro hh
    have hterm : pairing (parent q c hcut) T.val (terminal (parent q c hcut))=
        terminal (parent q c hcut) := rfl
    exact hx ((pairing (parent q c hcut) T.val).injective (hh.trans hterm.symm))
  calc
    parentEventIntoTiny q c hcut η (incoming (parent q c hcut)
        (regular_parent q hR c hcut).noTriple T.val x) =
      parentEventIntoTiny q c hcut η
        (successor (parent q c hcut) (regular_parent q hR c hcut).noTriple
          (pairing (parent q c hcut) T.val x)) := rfl
    _ = successor (tinyParent q c hcut η)
        (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
        (parentEventIntoTiny q c hcut η (pairing (parent q c hcut) T.val x)) :=
      (parentEventIntoTiny_successor (q:=q) (hR:=hR) (c:=c) (hc:=hc)
        (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) (pairing (parent q c hcut) T.val x)
        hxpair).symm
    _ = successor (tinyParent q c hcut η)
        (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
        (pairing (tinyParent q c hcut η) (parentTinySelection q c hcut η T.val)
          (parentEventIntoTiny q c hcut η x)) := by
      rw [parentEventIntoTiny_pairing (q:=q) (hR:=hR) (c:=c) (hc:=hc)
        (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T x]
    _ = incoming (tinyParent q c hcut η)
        (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
        (parentTinySelection q c hcut η T.val)
        (parentEventIntoTiny q c hcut η x) := rfl

def tinyParentEventInsertionEquiv (hR : Regular q) (hc : FirstCrossing q c)
    (hη : 0<η) (hη1 : η<1) :
    Event (parent q c hcut) ≃
      {z : Event (tinyParent q c hcut η) // z≠start (tinyParent q c hcut η)} :=
  parentEventIntoTinyNonstart (q:=q) (hR:=hR) (c:=c) (hc:=hc)
    (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1)

theorem tinyParent_incoming_start (hR : Regular q) (hc : FirstCrossing q c)
    (hη : 0<η) (hη1 : η<1)
    (T : Nonalternation.Support (parent q c hcut) (regular_parent q hR c hcut)) :
    incoming (tinyParent q c hcut η)
      (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
      (parentTinySelection q c hcut η T.val) (start (tinyParent q c hcut η))=
    (tinyParentEventInsertionEquiv (q:=q) (hR:=hR) (c:=c) (hc:=hc)
      (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1)
      (start (parent q c hcut))).val := by
  change successor (tinyParent q c hcut η)
    (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
    (start (tinyParent q c hcut η))=parentEventIntoTiny q c hcut η (start (parent q c hcut))
  rw [tinyParent_start_successor (q:=q) (hR:=hR) (c:=c) (hc:=hc)
    (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1)]
  rfl

theorem tinyParent_incoming_step (hR : Regular q) (hc : FirstCrossing q c)
    (hη : 0<η) (hη1 : η<1)
    (T : Nonalternation.Support (parent q c hcut) (regular_parent q hR c hcut))
    (x : Event (parent q c hcut)) :
    incoming (tinyParent q c hcut η)
      (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
      (parentTinySelection q c hcut η T.val)
      (tinyParentEventInsertionEquiv (q:=q) (hR:=hR) (c:=c) (hc:=hc)
        (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) x).val=
    if incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T.val x=
      start (parent q c hcut)
    then start (tinyParent q c hcut η)
    else (tinyParentEventInsertionEquiv (q:=q) (hR:=hR) (c:=c) (hc:=hc)
      (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1)
      (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T.val x)).val := by
  by_cases hx : x=terminal (parent q c hcut)
  · subst x
    have hp := incoming_terminal_eq_start (parent q c hcut)
      (regular_parent q hR c hcut).noTriple T.val
    have ht := incoming_terminal_eq_start (tinyParent q c hcut η)
      (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
      (parentTinySelection q c hcut η T.val)
    rw [show (tinyParentEventInsertionEquiv (q:=q) (hR:=hR) (c:=c) (hc:=hc)
        (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1)
        (terminal (parent q c hcut))).val=terminal (tinyParent q c hcut η) by rfl]
    rw [hp,ht]
    simp [tinyParentEventInsertionEquiv,parentEventIntoTinyNonstart,parentEventIntoTiny]
  · have hmap := parentEventIntoTiny_incoming (q:=q) (hR:=hR) (c:=c) (hc:=hc)
      (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T x hx
    have hnot : incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T.val x ≠
        start (parent q c hcut) := by
      intro hh
      have heq := (unique_seam_predecessor (parent q c hcut)
        (regular_parent q hR c hcut).noTriple T.val x).mp hh
      exact hx heq
    simp only [tinyParentEventInsertionEquiv,parentEventIntoTinyNonstart]
    simp only [Equiv.ofBijective_apply]
    simp [hnot] at hmap ⊢
    exact hmap.symm

theorem tinyParent_openEventWord (hR : Regular q) (hc : FirstCrossing q c)
    (hη : 0<η) (hη1 : η<1)
    (T : Nonalternation.Support (parent q c hcut) (regular_parent q hR c hcut)) :
    orbitWord (incoming (tinyParent q c hcut η)
      (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
      (parentTinySelection q c hcut η T.val)) (start (tinyParent q c hcut η))=
    start (tinyParent q c hcut η) ::
      (orbitWord (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T.val)
        (start (parent q c hcut))).map
        (fun x => (tinyParentEventInsertionEquiv (q:=q) (hR:=hR) (c:=c) (hc:=hc)
          (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) x).val) := by
  exact DirectGLSSW.PermutationInsertion.inserted_orbitWord
    (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T.val)
    (incoming (tinyParent q c hcut η)
      (regular_tinyParent q hR c hc hcut η hη hη1).noTriple
      (parentTinySelection q c hcut η T.val))
    (start (parent q c hcut)) (start (tinyParent q c hcut η))
    (tinyParentEventInsertionEquiv (q:=q) (hR:=hR) (c:=c) (hc:=hc)
      (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1))
    (tinyParent_incoming_start (q:=q) (hR:=hR) (c:=c) (hc:=hc)
      (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T)
    (tinyParent_incoming_step (q:=q) (hR:=hR) (c:=c) (hc:=hc)
      (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T)


end DirectGLSSW.ActiveArc.LiteralTinyParent
