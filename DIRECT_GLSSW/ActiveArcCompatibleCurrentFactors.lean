import ActiveArcCompatibleWordSplice
import ActiveArcChildAuxiliary
import OpenCurrentSpliceFactors
import ActiveArcVirtualEventGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW Cursor Split SingletonWords Primitive RetainedWords
attribute [local instance] Classical.propDecidable

private theorem ofFn_head_override {α : Type*} {m : ℕ}
    (f : Fin m → α) (p : α) (hm : 0 < m) :
    List.ofFn (fun i : Fin m => if i.val=0 then p else f i) =
      p :: (List.ofFn f).tail := by
  cases m with
  | zero => omega
  | succ m => simp [List.ofFn_succ]

/-- The proved actual compatible word splice identifies the whole child
prefix, its auxiliary genericity, and the exact parent marked current. -/
theorem compatible_event_current_factors
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : ClosedAuxiliary q hR)
    (S : {S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
      PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
        (child_noTriple q hR c hc.1 hcut) S})
    (T : Support (parent q c hcut) (regular_parent q hR c hcut)) :
    let U : Support q hR := ⟨pieceSelections q hR c hc hcut S.val T.val,
      (pieceSelections_nonalternating_iff q hR c hc hcut S.val T.val).mpr
        ⟨S.property,T.property⟩⟩
    let Q := DaughterFirstReturn.daughterVertex (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0)
    let m := Fintype.card (DaughterFirstReturn.CornerCoord (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0))
    let W := eventOpenWord q hR U c
    3 ≤ m ∧ openCount q hR U.val = m+openCount (parent q c hcut)
      (regular_parent q hR c hcut) T.val-1 ∧
    (∀ i : Fin m, W i.val=Q i) ∧
    CyclicGeneric (fun i : Fin m => W i.val) ∧
    OpenMarkedCurrent.entry
      (polygonSignArray (fun i => if i=0 then W 0 else W (m-1+i)))
      0 ((openCount q hR U.val-1)-(m-1)) =
      openCurrent (parent q c hcut) (regular_parent q hR c hcut) T := by
  let U : Support q hR := ⟨pieceSelections q hR c hc hcut S.val T.val,
    (pieceSelections_nonalternating_iff q hR c hc hcut S.val T.val).mpr
      ⟨S.property,T.property⟩⟩
  let Q := DaughterFirstReturn.daughterVertex (child q hR c hc.1 hcut)
    (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0)
  let m := Fintype.card (DaughterFirstReturn.CornerCoord (child q hR c hc.1 hcut)
    (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0))
  let P := OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T
  let W := eventOpenWord q hR U c
  have hQ : CyclicGeneric Q := child_auxiliaryGenericity q hR c hc hcut hAux
    S.val S.property (Sum.inl 0)
  have hms : 3 ≤ m := hQ.size_ge_three
  have hm : 0 < m := by omega
  have ht := open_count_ge_two (parent q c hcut) (regular_parent q hR c hcut) T.val
  have htpos : 0 < openCount (parent q c hcut) (regular_parent q hR c hcut) T.val :=
    lt_of_lt_of_le (by decide : 0<2) ht
  have hh : (List.ofFn Q).head?=some (crossingPoint q c) :=
    selected_child_word_head q hR c hc hcut S.val
  have hQzero : Q ⟨0,hm⟩=crossingPoint q c := by
    rw [List.head?_eq_getElem?,List.getElem?_ofFn] at hh
    change (if h : 0<m then some (Q ⟨0,h⟩) else none)=some (crossingPoint q c) at hh
    simpa only [dif_pos hm,Option.some.injEq] using hh
  have hPzero : P ⟨0,htpos⟩=crossingPoint q c := by
    change eventPoint (parent q c hcut)
      (cornerEvent (parent q c hcut) (regular_parent q hR c hcut) T.val
        (start (parent q c hcut)) ⟨0,htpos⟩)=_
    rw [cornerEvent_zero (parent q c hcut) (regular_parent q hR c hcut) T.val
      (start (parent q c hcut)) (endpoints_retained _ _).1]
    simpa only [eventPoint,start] using parent_zero q c hcut
  have hzero : P ⟨0,htpos⟩=Q ⟨0,hm⟩ := hPzero.trans hQzero.symm
  have hlen := open_count_ge_two q hR U.val
  have hfun : (fun i : Fin (openCount q hR U.val) => W i.val) =
      fun i => if i.val=0 then crossingPoint q c else OpenVertex q hR U i := by
    funext i
    by_cases hi : i.val=0
    · simp only [W,eventOpenWord,hi,ite_true]
    · simpa only [if_neg hi] using eventOpenWord_pos q hR U c i.val
        (Nat.pos_of_ne_zero hi) i.isLt
  have hw : List.ofFn (fun i : Fin (openCount q hR U.val) => W i.val) =
      List.ofFn Q ++ (List.ofFn P).tail := by
    rw [hfun,ofFn_head_override _ _ (lt_of_lt_of_le (by decide : 0<2) hlen)]
    exact unselected_event_pointWord_splice q hR c hc hcut S.val T.val
  obtain ⟨hcount,hprefix,hparent⟩ := ofFn_splice_coordinates W Q P hm htpos hzero hw
  have hge : CyclicGeneric (fun i : Fin m => W i.val) := by
    have hf : (fun i : Fin m => W i.val)=Q := funext hprefix
    rw [hf]
    exact hQ
  change 3≤m ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨hms,hcount,hprefix,hge,?_⟩
  exact boundary_parent_current_of_splice W Q P hm ht hzero hw


end DirectGLSSW.ActiveArc.CompatibleWords
