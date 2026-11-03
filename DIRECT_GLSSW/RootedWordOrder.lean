import InsertedRootedWordFilter
import DirectGLSSW.HOMFLY.BasedTraversal

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open PermutationOrbits
noncomputable section

/-- Filtering retained letters preserves their first-occurrence order. -/
theorem idxOf_filter_lt_iff {α : Type*} [DecidableEq α]
    (l : List α) (p : α → Bool) (x y : α)
    (hx : p x = true) (hy : p y = true) :
    (l.filter p).idxOf x < (l.filter p).idxOf y ↔ l.idxOf x < l.idxOf y := by
  induction l with
  | nil => simp
  | cons b l ih =>
    by_cases hb : p b = true
    · rw [List.filter_cons_of_pos hb]
      by_cases hbx : b = x
      · subst b
        by_cases hxy : x = y
        · subst y; simp
        · simp only [List.idxOf_cons_self, List.idxOf_cons_ne _ hxy, Nat.zero_lt_succ, iff_self]
      · by_cases hby : b = y
        · subst b
          simp only [List.idxOf_cons_self, List.idxOf_cons_ne _ hbx, Nat.not_lt_zero, iff_self]
        · simpa only [List.idxOf_cons_ne _ hbx, List.idxOf_cons_ne _ hby,
            Nat.succ_lt_succ_iff] using ih
    · have hbx : b ≠ x := fun h => hb (h.symm ▸ hx)
      have hby : b ≠ y := fun h => hb (h.symm ▸ hy)
      rw [List.filter_cons_of_neg hb, List.idxOf_cons_ne _ hbx,
        List.idxOf_cons_ne _ hby, Nat.succ_lt_succ_iff]
      exact ih

/-- Only injectivity on the queried letter's preimage in the word is needed. -/
theorem idxOf_map_eq_of_preimage {α β : Type*} [DecidableEq α] [DecidableEq β]
    (l : List α) (f : α → β) (x : α)
    (hinj : ∀ y ∈ l, f y = f x → y = x) :
    (l.map f).idxOf (f x) = l.idxOf x := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hi : ∀ y ∈ l, f y = f x → y = x := fun y hy => hinj y (List.mem_cons_of_mem b hy)
    by_cases hb : b = x
    · subst b; simp
    · have hf : f b ≠ f x := fun h => hb (hinj b List.mem_cons_self h)
      simp only [List.map_cons, List.idxOf_cons_ne _ hf, List.idxOf_cons_ne _ hb, ih hi]

/-- The evaluator's numeric visit position is its index in the actual rooted
orbit word; this is derived from the finite orbit enumeration. -/
theorem visitPosition_eq_idxOf {D : PLLinkDiagram} (T : BasedTraversal D) (e : Fin D.nArc) :
    visitPosition T e =
      (orbitWord D.continuation (T.baseArc (componentOf D.continuation e)).val).idxOf e := by
  classical
  let base := T.baseArc (componentOf D.continuation e)
  let y : Fibre D.continuation (componentOf D.continuation base.val) :=
    ⟨e, base.property.symm⟩
  let k := (orbitEnumeration D.continuation base.val).symm y
  have hk : k.val < (orbitWord D.continuation base.val).length := by
    simpa only [orbitWord_length] using k.isLt
  have he : (orbitWord D.continuation base.val)[k.val] = e := by
    have h := congrArg Subtype.val ((orbitEnumeration D.continuation base.val).apply_symm_apply y)
    simpa only [orbitWord, List.getElem_ofFn] using h
  change k.val = (orbitWord D.continuation base.val).idxOf e
  exact (List.idxOf_getElem (orbitWord_nodup _ _) k.val hk).symm.trans
    (congrArg (fun a => (orbitWord D.continuation base.val).idxOf a) he)

end
end DirectGLSSW.HOMFLY




