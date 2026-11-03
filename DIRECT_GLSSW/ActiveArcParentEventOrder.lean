import ActiveArcParentEventMap

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open Split Cursor
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)

theorem parentEventMap_edgeTag (x : Event (parent q c hcut)) (hx : x≠start (parent q c hcut)) :
    edgeTag q (parentEventMap q hR c hc hcut x)=a+edgeTag (parent q c hcut) x := by
  cases x with
  | inl i =>
    have hi : i≠0 := fun he => hx (congrArg Sum.inl he)
    simp only [parentEventMap,if_neg hi,edgeTag,Split.vertex]
  | inr v =>
    change (visitEdge q (parentVisitMap q c hcut v)).val=a+(visitEdge (parent q c hcut) v).val
    rw [parentVisitMap_edge]
    rfl

theorem parentEventMap_parameter (x : Event (parent q c hcut)) (hx : x≠start (parent q c hcut)) :
    parameter q (parentEventMap q hR c hc hcut x)=
      if edgeTag (parent q c hcut) x=0 then
        rightParameter q c+(1-rightParameter q c)*parameter (parent q c hcut) x
      else parameter (parent q c hcut) x := by
  cases x with
  | inl i =>
    have hi : i≠0 := fun he => hx (congrArg Sum.inl he)
    have hiv : i.val≠0 := fun he => hi (Fin.ext he)
    simp [parentEventMap,hi,edgeTag,parameter,hiv]
  | inr v =>
    change visitParameter q (parentVisitMap q c hcut v)=_
    rw [parentVisitMap_parameter q hR]
    by_cases hv : visitEdge (parent q c hcut) v=0
    · simp [parentOffset,tangentScale,edgeTag,parameter,hv]
    · have hvv : (visitEdge (parent q c hcut) v).val≠0 := fun he => hv (Fin.ext he)
      simp [parentOffset,tangentScale,edgeTag,parameter,hv,hvv]

theorem parent_start_lt_image (x : Event (parent q c hcut)) (hx : x≠start (parent q c hcut)) :
    (eventOrder q hR.noTriple).lt (Sum.inr (c,false)) (parentEventMap q hR c hc hcut x) := by
  letI := eventOrder q hR.noTriple
  cases x with
  | inl i =>
    have hi : i≠0 := fun he => hx (congrArg Sum.inl he)
    simp only [parentEventMap,if_neg hi]
    apply (event_lt_iff q hR.noTriple _ _).mpr
    left
    change c.val.1.val<a+i.val
    rw [hc.1]
    have hip : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi
    change (0 : ℕ) < a+i.val
    omega
  | inr v =>
    have h0 := first_left_lt_other_left q hR c hc _ (parentCrossing_ne_cut q hR c hcut v.1)
    have h1 := left_visit_lt_right q hR (parentCrossingToOriginal q c hcut v.1)
    rcases v with ⟨d,z⟩;cases z
    · exact h0
    · exact lt_trans h0 h1

theorem parentEventMap_lt_nonstart (x y : Event (parent q c hcut))
    (hx : x≠start (parent q c hcut)) (hy : y≠start (parent q c hcut)) :
    (eventOrder q hR.noTriple).lt (parentEventMap q hR c hc hcut x) (parentEventMap q hR c hc hcut y) ↔
      (eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple).lt x y := by
  rw [event_lt_iff,event_lt_iff,parentEventMap_edgeTag q hR c hc hcut x hx,
    parentEventMap_edgeTag q hR c hc hcut y hy,parentEventMap_parameter q hR c hc hcut x hx,
    parentEventMap_parameter q hR c hc hcut y hy]
  simp only [Nat.add_lt_add_iff_left,Nat.add_left_cancel_iff]
  by_cases he : edgeTag (parent q c hcut) x=edgeTag (parent q c hcut) y
  · rw [he]
    simp only [lt_self_iff_false,true_and,false_or]
    split_ifs
    · exact (add_lt_add_iff_left _).trans (mul_lt_mul_left (sub_pos.mpr (rightParameter_spec q c).2.1))
    · rfl
  · simp only [he,false_and,or_false]

theorem parentEventMap_lt (x y : Event (parent q c hcut)) :
    (eventOrder q hR.noTriple).lt (parentEventMap q hR c hc hcut x) (parentEventMap q hR c hc hcut y) ↔
      (eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple).lt x y := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
  by_cases hx : x=start (parent q c hcut)
  · subst x
    by_cases hy : y=start (parent q c hcut)
    · subst y;exact iff_of_false (lt_irrefl _) (lt_irrefl _)
    · rw [parentEventMap_start]
      exact iff_of_true (parent_start_lt_image q hR c hc hcut y hy)
        (lt_of_le_of_ne (start_le _ _ y) (Ne.symm hy))
  · by_cases hy : y=start (parent q c hcut)
    · subst y
      rw [parentEventMap_start]
      exact iff_of_false (not_lt_of_ge (le_of_lt (parent_start_lt_image q hR c hc hcut x hx)))
        (not_lt_of_ge (start_le _ _ x))
    · exact parentEventMap_lt_nonstart q hR c hc hcut x y hx hy

end DirectGLSSW.ActiveArc.CompatibleWords
