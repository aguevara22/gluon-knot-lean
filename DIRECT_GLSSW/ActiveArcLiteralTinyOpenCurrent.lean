import ActiveArcTinyParentIndexedWord
import OpenCurrentWordCongruence
import ActiveArcParentFarProjector

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split Primitive RetainedWords OpenFirstEdgeGeometry
attribute [local instance] Classical.propDecidable

/-- The actual tiny-parent open current is exactly the short-first approach
of the literal parent retained word, throughout its used finite range. -/
theorem tinyParent_openCurrent_eq_approach
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (η : ℝ) (hη : 0<η) (hη1 : η<1)
    (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut)) :
    openCurrent (tinyParent q c hcut η) (regular_tinyParent q hR c hc hcut η hη hη1)
      (tinySupportOfParent q hR c hc hcut η hη hη1 T) =
    OpenMarkedCurrent.entry (polygonSignArray
      (approach (fun k => if k=0 then q 0 else
        rootedPolygonWord (OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T)
          (openLast (parent q c hcut) (regular_parent q hR c hcut) T.val) (k-1)) η))
      0 (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val) := by
  have hcount := tinyParent_openCount q hR c hc hcut η hη hη1 T
  dsimp only [ParentArc,ParentRegular] at hcount
  have hp := open_count_ge_two (parent q c hcut) (regular_parent q hR c hcut) T.val
  unfold openCurrent
  change OpenMarkedCurrent.entry (polygonSignArray
    (rootedPolygonWord (OpenVertex (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (tinySupportOfParent q hR c hc hcut η hη hη1 T))
      (openLast (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
        (parentTinySelection q c hcut η T.val))))
    0 (openCount (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (parentTinySelection q c hcut η T.val)-1)=_
  rw [hcount,Nat.add_sub_cancel]
  apply openMarkedCurrent_entry_congr_of_word_eq
    (N:=openCount (parent q c hcut) (regular_parent q hR c hcut) T.val) _ _
    (lt_of_lt_of_le (by decide : 0<2) hp)
  intro k hk
  have hkt : k<openCount (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (parentTinySelection q c hcut η T.val) := by rw [hcount];omega
  rw [tinyParent_rootedWord_prefix q hR c hc hcut η hη hη1 T k hkt]
  by_cases hz : k=0
  · subst k
    rw [approach_zero]
    simp only [ite_true,show (1:ℕ)≠0 by decide,ite_false,Nat.sub_self]
    have hw := openCurrent_word (parent q c hcut) (regular_parent q hR c hcut) T 0 (by omega)
    rw [openVertex_zero,parent_zero] at hw
    rw [hw]
  · rw [approach_pos _ η (Nat.pos_of_ne_zero hz)]
    simp only [if_neg hz]

end DirectGLSSW.ActiveArc.LiteralTinyParent
