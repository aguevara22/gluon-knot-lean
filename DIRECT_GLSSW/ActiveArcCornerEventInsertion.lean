import ActiveArcCornerSuffix
import OpenFirstEdgeGeometry
import DirectGLSSW.PermutationInsertionWords

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Primitive OpenFirstEdgeGeometry Nonalternation RetainedWords PhysicalSegments PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ)

/-- The old parent event order is embedded after the new initial anchor. -/
def suffixEventIntoOriginal (hfree : ∀ d : Crossing q, d.val.1 ≠ 0) (x : Event (suffix q)) : Event q :=
  match x with
  | .inl i => .inl (vertex (a:=1) i)
  | .inr v => .inr (firstEdgeFreeCrossingEquiv q hfree v.1,v.2)

theorem suffixEventIntoOriginal_injective (hfree : ∀ d : Crossing q, d.val.1 ≠ 0) :
    Function.Injective (suffixEventIntoOriginal q hfree) := by
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      exact congrArg Sum.inl (vertex_injective (Sum.inl.inj hxy))
    | inr v => cases hxy
  | inr v =>
    cases y with
    | inl j => cases hxy
    | inr w =>
      have hp := Sum.inr.inj hxy
      have hfirst : v.1=w.1 := (firstEdgeFreeCrossingEquiv q hfree).injective (congrArg Prod.fst hp)
      have hsecond : v.2=w.2 := congrArg (fun z : Crossing q × Bool => z.2) hp
      exact congrArg Sum.inr (Prod.ext hfirst hsecond)

theorem suffixEventIntoOriginal_tag (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (x : Event (suffix q)) :
    edgeTag q (suffixEventIntoOriginal q hfree x) = edgeTag (suffix q) x+1 := by
  cases x with
  | inl i => simp [suffixEventIntoOriginal,edgeTag,vertex]; omega
  | inr v =>
    rcases v with ⟨d,side⟩
    cases side
    · exact firstEdgeFreeCrossingEquiv_label q hfree d
    · exact firstEdgeFreeCrossingEquiv_otherLabel q hfree d

theorem suffixEventIntoOriginal_parameter (hR : Regular q)
    (hfree : ∀ d : Crossing q, d.val.1 ≠ 0) (x : Event (suffix q)) :
    parameter q (suffixEventIntoOriginal q hfree x)=parameter (suffix q) x := by
  cases x with
  | inl i => rfl
  | inr v =>
    rcases v with ⟨d,side⟩
    cases side
    · exact firstEdgeFreeCrossingEquiv_leftParameter q hfree hR d
    · exact firstEdgeFreeCrossingEquiv_rightParameter q hfree hR d

theorem suffixEventIntoOriginal_order (hR : Regular q)
    (hfree : ∀ d : Crossing q, d.val.1 ≠ 0) (x y : Event (suffix q)) :
    (letI := eventOrder q hR.noTriple;
      suffixEventIntoOriginal q hfree x < suffixEventIntoOriginal q hfree y) ↔
    (letI := eventOrder (suffix q) (regular_suffix q hR).noTriple; x<y) := by
  rw [event_lt_iff,event_lt_iff,suffixEventIntoOriginal_tag,suffixEventIntoOriginal_tag,
    suffixEventIntoOriginal_parameter q hR hfree,suffixEventIntoOriginal_parameter q hR hfree]
  simp only [Nat.add_lt_add_iff_right,Nat.add_right_cancel_iff]

theorem suffixEventIntoOriginal_le (hR : Regular q)
    (hfree : ∀ d : Crossing q, d.val.1 ≠ 0) (x y : Event (suffix q)) :
    (letI := eventOrder q hR.noTriple;
      suffixEventIntoOriginal q hfree x ≤ suffixEventIntoOriginal q hfree y) ↔
    (letI := eventOrder (suffix q) (regular_suffix q hR).noTriple; x≤y) := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (suffix q) (regular_suffix q hR).noTriple
  constructor
  · intro h
    rcases le_iff_lt_or_eq.mp h with hlt|he
    · exact le_of_lt ((suffixEventIntoOriginal_order q hR hfree x y).mp hlt)
    · exact le_of_eq (suffixEventIntoOriginal_injective q hfree he)
  · intro h
    rcases le_iff_lt_or_eq.mp h with hlt|he
    · exact le_of_lt ((suffixEventIntoOriginal_order q hR hfree x y).mpr hlt)
    · exact le_of_eq (congrArg (suffixEventIntoOriginal q hfree) he)

theorem suffixEventIntoOriginal_surjective_nonstart (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (z : Event q) (hz : z≠start q) :
    ∃ x : Event (suffix q), suffixEventIntoOriginal q hfree x=z := by
  cases z with
  | inl i =>
    have hi : i.val≠0 := by
      intro hh
      exact hz (congrArg Sum.inl (Fin.ext hh))
    let j : Fin (b+2) := ⟨i.val-1,by have hh:=i.isLt; omega⟩
    refine ⟨Sum.inl j,?_⟩
    apply congrArg Sum.inl
    apply Fin.ext
    simp [suffixEventIntoOriginal,vertex,j]
    omega
  | inr v =>
    obtain ⟨d,hd⟩ := (firstEdgeFreeCrossingEquiv q hfree).surjective v.1
    exact ⟨Sum.inr (d,v.2),by simp [suffixEventIntoOriginal,hd]⟩

theorem suffixEventIntoOriginal_successor (hR : Regular q) (hfree : ∀ d : Crossing q, d.val.1 ≠ 0) (x : Event (suffix q))
    (hx : x≠terminal (suffix q)) :
    successor q
      hR.noTriple
      (suffixEventIntoOriginal q hfree x)=
    suffixEventIntoOriginal q hfree
      (successor (suffix q) (regular_suffix q hR).noTriple x) := by
  letI := eventOrder q
    hR.noTriple
  letI := eventOrder (suffix q) (regular_suffix q hR).noTriple
  change orderedCyclicSuccessor (Event q)
    (suffixEventIntoOriginal q hfree x)=_
  apply orderedCyclicSuccessor_eq_of_order_spec
  left
  constructor
  · exact (suffixEventIntoOriginal_order (q:=q) (hR:=hR) (hfree:=hfree) x
      (successor (suffix q) (regular_suffix q hR).noTriple x)).mpr
      (successor_strict_before_terminal (suffix q)
        (regular_suffix q hR).noTriple x hx)
  · intro z hzx
    have hz : z≠start q := by
      intro he
      subst z
      have hs := start_le q
        hR.noTriple
        (suffixEventIntoOriginal q hfree x)
      exact (not_lt_of_ge hs) hzx
    obtain ⟨y,rfl⟩ := suffixEventIntoOriginal_surjective_nonstart
      (q:=q) (hfree:=hfree) z hz
    have hxy := (suffixEventIntoOriginal_order (q:=q) (hR:=hR) (hfree:=hfree) x y).mp hzx
    have hmin := successor_min (suffix q)
      (regular_suffix q hR) x y hx hxy
    exact (suffixEventIntoOriginal_le (q:=q) (hR:=hR) (hfree:=hfree)
      (successor (suffix q) (regular_suffix q hR).noTriple x) y).mpr hmin

theorem suffixEventIntoOriginal_ne_start (hR : Regular q) (hfree : ∀ d : Crossing q, d.val.1 ≠ 0) (x : Event (suffix q)) :
    suffixEventIntoOriginal q hfree x≠start q := by
  intro h
  have ht := congrArg (edgeTag q) h
  rw [suffixEventIntoOriginal_tag] at ht
  simp only [start,edgeTag] at ht
  omega

def suffixEventIntoOriginalNonstart (hR : Regular q) (hfree : ∀ d : Crossing q, d.val.1 ≠ 0) :
    Event (suffix q) ≃ {z : Event q // z≠start q} :=
  Equiv.ofBijective
    (fun x => ⟨suffixEventIntoOriginal q hfree x,
      suffixEventIntoOriginal_ne_start (q:=q) (hR:=hR) (hfree:=hfree) x⟩)
    ⟨fun x y hxy => suffixEventIntoOriginal_injective q hfree (congrArg Subtype.val hxy),
      fun z => by
        obtain ⟨x,hx⟩ := suffixEventIntoOriginal_surjective_nonstart
          (q:=q) (hfree:=hfree)
          z.val z.property
        exact ⟨x,Subtype.ext hx⟩⟩

theorem corner_start_successor (hR : Regular q) (hfree : ∀ d : Crossing q, d.val.1 ≠ 0) :
    successor q
      hR.noTriple
      (start q)=
    Sum.inl (1 : Fin (1+b+2)) := by
  letI := eventOrder q
    hR.noTriple
  change orderedCyclicSuccessor (Event q) _ = _
  apply orderedCyclicSuccessor_eq_of_order_spec
  left
  constructor
  · have hlt : start q <
        (Sum.inl (⟨1,by omega⟩ : Fin (1+b+2)) : Event q) := by
      apply (event_lt_iff q
        hR.noTriple _ _).2
      left
      simp [edgeTag,start]
    exact hlt
  · intro z hsz
    have htag : 1≤edgeTag q z := by
      cases z with
      | inl i =>
        have hi : i.val≠0 := by
          intro hh
          have hEq : start q=Sum.inl i := by
            apply congrArg Sum.inl
            exact (Fin.ext hh).symm
          exact (ne_of_lt hsz) hEq
        simpa [edgeTag] using (Nat.one_le_iff_ne_zero.mpr hi)
      | inr v =>
        rcases v with ⟨d,side⟩
        have hleft := hfree d
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
    exact anchor_le_of_tag_le q
      hR
      (⟨1,by omega⟩ : Fin (1+b+2)) z htag

theorem suffixEventIntoOriginal_pairing (hR : Regular q) (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (T : Nonalternation.Support (suffix q) (regular_suffix q hR))
    (x : Event (suffix q)) :
    suffixEventIntoOriginal q hfree
      (pairing (suffix q) T.val x)=
    pairing q ((firstEdgeFreeSupportEquiv q hfree hR T).val)
      (suffixEventIntoOriginal q hfree x) := by
  cases x with
  | inl i => rfl
  | inr v =>
    rcases v with ⟨d,side⟩
    have hmem : firstEdgeFreeCrossingEquiv q hfree d ∈ (firstEdgeFreeSupportEquiv q hfree hR T).val ↔
        d∈T.val := by
      constructor
      · intro hh
        obtain ⟨e,he,heq⟩ := Finset.mem_map.mp hh
        have he' := (firstEdgeFreeCrossingEquiv q hfree).injective heq
        simpa [he'] using he
      · intro hh
        exact Finset.mem_map.mpr ⟨d,hh,rfl⟩
    by_cases hd : d∈T.val
    · have hmt := hmem.mpr hd
      cases side <;> simp [suffixEventIntoOriginal,pairing,pairingMap,hd,hmt]
    · have hmt : firstEdgeFreeCrossingEquiv q hfree d∉(firstEdgeFreeSupportEquiv q hfree hR T).val :=
        fun hh => hd (hmem.mp hh)
      cases side <;> simp [suffixEventIntoOriginal,pairing,pairingMap,hd,hmt]

theorem suffixEventIntoOriginal_incoming (hR : Regular q) (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (T : Nonalternation.Support (suffix q) (regular_suffix q hR))
    (x : Event (suffix q)) (hx : x≠terminal (suffix q)) :
    suffixEventIntoOriginal q hfree (incoming (suffix q)
      (regular_suffix q hR).noTriple T.val x)=
    incoming q
      hR.noTriple
      ((firstEdgeFreeSupportEquiv q hfree hR T).val) (suffixEventIntoOriginal q hfree x) := by
  have hxpair : pairing (suffix q) T.val x≠terminal (suffix q) := by
    intro hh
    have hterm : pairing (suffix q) T.val (terminal (suffix q))=
        terminal (suffix q) := rfl
    exact hx ((pairing (suffix q) T.val).injective (hh.trans hterm.symm))
  calc
    suffixEventIntoOriginal q hfree (incoming (suffix q)
        (regular_suffix q hR).noTriple T.val x) =
      suffixEventIntoOriginal q hfree
        (successor (suffix q) (regular_suffix q hR).noTriple
          (pairing (suffix q) T.val x)) := rfl
    _ = successor q
        hR.noTriple
        (suffixEventIntoOriginal q hfree (pairing (suffix q) T.val x)) :=
      (suffixEventIntoOriginal_successor (q:=q) (hR:=hR) (hfree:=hfree) (pairing (suffix q) T.val x)
        hxpair).symm
    _ = successor q
        hR.noTriple
        (pairing q ((firstEdgeFreeSupportEquiv q hfree hR T).val)
          (suffixEventIntoOriginal q hfree x)) := by
      rw [suffixEventIntoOriginal_pairing (q:=q) (hR:=hR) (hfree:=hfree) T x]
    _ = incoming q
        hR.noTriple
        ((firstEdgeFreeSupportEquiv q hfree hR T).val)
        (suffixEventIntoOriginal q hfree x) := rfl

def cornerEventInsertionEquiv (hR : Regular q) (hfree : ∀ d : Crossing q, d.val.1 ≠ 0) :
    Event (suffix q) ≃
      {z : Event q // z≠start q} :=
  suffixEventIntoOriginalNonstart (q:=q) (hR:=hR) (hfree:=hfree)

theorem corner_incoming_start (hR : Regular q) (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (T : Nonalternation.Support (suffix q) (regular_suffix q hR)) :
    incoming q
      hR.noTriple
      ((firstEdgeFreeSupportEquiv q hfree hR T).val) (start q)=
    (cornerEventInsertionEquiv (q:=q) (hR:=hR) (hfree:=hfree)
      (start (suffix q))).val := by
  change successor q
    hR.noTriple
    (start q)=suffixEventIntoOriginal q hfree (start (suffix q))
  rw [corner_start_successor (q:=q) (hR:=hR) (hfree:=hfree)]
  apply congrArg Sum.inl
  apply Fin.ext
  simp [cornerEventInsertionEquiv,suffixEventIntoOriginalNonstart,suffixEventIntoOriginal,start,vertex]

theorem corner_incoming_step (hR : Regular q) (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (T : Nonalternation.Support (suffix q) (regular_suffix q hR))
    (x : Event (suffix q)) :
    incoming q
      hR.noTriple
      ((firstEdgeFreeSupportEquiv q hfree hR T).val)
      (cornerEventInsertionEquiv (q:=q) (hR:=hR) (hfree:=hfree) x).val=
    if incoming (suffix q) (regular_suffix q hR).noTriple T.val x=
      start (suffix q)
    then start q
    else (cornerEventInsertionEquiv (q:=q) (hR:=hR) (hfree:=hfree)
      (incoming (suffix q) (regular_suffix q hR).noTriple T.val x)).val := by
  by_cases hx : x=terminal (suffix q)
  · subst x
    have hp := incoming_terminal_eq_start (suffix q)
      (regular_suffix q hR).noTriple T.val
    have ht := incoming_terminal_eq_start q
      hR.noTriple
      ((firstEdgeFreeSupportEquiv q hfree hR T).val)
    rw [show (cornerEventInsertionEquiv (q:=q) (hR:=hR) (hfree:=hfree)
        (terminal (suffix q))).val=terminal q by
        apply congrArg Sum.inl
        apply Fin.ext
        simp [cornerEventInsertionEquiv,suffixEventIntoOriginalNonstart,suffixEventIntoOriginal,terminal,vertex]
        omega]
    rw [hp,ht]
    simp [cornerEventInsertionEquiv,suffixEventIntoOriginalNonstart,suffixEventIntoOriginal]
  · have hmap := suffixEventIntoOriginal_incoming (q:=q) (hR:=hR) (hfree:=hfree) T x hx
    have hnot : incoming (suffix q) (regular_suffix q hR).noTriple T.val x ≠
        start (suffix q) := by
      intro hh
      have heq := (unique_seam_predecessor (suffix q)
        (regular_suffix q hR).noTriple T.val x).mp hh
      exact hx heq
    simp only [cornerEventInsertionEquiv,suffixEventIntoOriginalNonstart]
    simp only [Equiv.ofBijective_apply]
    simp [hnot] at hmap ⊢
    exact hmap.symm

theorem corner_openEventWord (hR : Regular q) (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (T : Nonalternation.Support (suffix q) (regular_suffix q hR)) :
    orbitWord (incoming q
      hR.noTriple
      ((firstEdgeFreeSupportEquiv q hfree hR T).val)) (start q)=
    start q ::
      (orbitWord (incoming (suffix q) (regular_suffix q hR).noTriple T.val)
        (start (suffix q))).map
        (fun x => (cornerEventInsertionEquiv (q:=q) (hR:=hR) (hfree:=hfree) x).val) := by
  exact DirectGLSSW.PermutationInsertion.inserted_orbitWord
    (incoming (suffix q) (regular_suffix q hR).noTriple T.val)
    (incoming q
      hR.noTriple
      ((firstEdgeFreeSupportEquiv q hfree hR T).val))
    (start (suffix q)) (start q)
    (cornerEventInsertionEquiv (q:=q) (hR:=hR) (hfree:=hfree))
    (corner_incoming_start (q:=q) (hR:=hR) (hfree:=hfree) T)
    (corner_incoming_step (q:=q) (hR:=hR) (hfree:=hfree) T)


end DirectGLSSW.ActiveArc.Split
