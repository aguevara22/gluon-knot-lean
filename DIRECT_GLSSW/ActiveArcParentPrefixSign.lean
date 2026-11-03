import ActiveArcParentInitialTurn

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Cursor Primitive

private theorem scalarSignValue_neg_real (x : ℝ) :
    scalarSignValue (-x) = -scalarSignValue x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hp : 0 < -x := neg_pos.mpr hx
    simp [scalarSignValue,ne_of_lt hx,ne_of_gt hp,hx,not_lt_of_ge hp.le]
  · subst x; simp [scalarSignValue]
  · have hn : -x < 0 := neg_neg_of_pos hx
    simp [scalarSignValue,ne_of_gt hx,ne_of_lt hn,hn,not_lt_of_ge hx.le]

/-- The sign array of the literal prefixed retained parent has H(0,1,2)=-delta,
where delta is the Cartesian determinant sign of the actual crossing edges. -/
theorem parent_prefixed_sign012
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val = a)
    (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut)) :
    polygonSignArray (fun k => if k=0 then q 0 else
      rootedPolygonWord (Primitive.OpenVertex (parent q c hcut)
        (regular_parent q hR c hcut) T)
        (RetainedWords.openLast (parent q c hcut)
          (regular_parent q hR c hcut) T.val) (k-1)) 0 1 2 =
      -scalarSignValue (planarDet (q 1 - q 0)
        (q c.val.2.succ - q c.val.2.castSucc)) := by
  let p := parent q c hcut
  let hp := regular_parent q hR c hcut
  let w : ℕ → PlanarPoint ℝ := fun k => if k=0 then q 0 else
    rootedPolygonWord (Primitive.OpenVertex p hp T)
      (RetainedWords.openLast p hp T.val) (k-1)
  have h0 : w 0 = q 0 := by simp [w]
  have h1 : w 1 = crossingPoint q c := by
    simp only [w,show (1:ℕ) ≠ 0 by decide,ite_false,Nat.sub_self]
    rw [Primitive.openCurrent_word p hp T 0
      (lt_of_lt_of_le (by decide : 0 < 2) (RetainedWords.open_count_ge_two p hp T.val))]
    rw [Primitive.openVertex_zero]
    exact parent_zero q c hcut
  have h2 : w 2 = Primitive.OpenVertex p hp T
      ⟨1,lt_of_lt_of_le (by decide : 1 < 2) (RetainedWords.open_count_ge_two p hp T.val)⟩ := by
    simp only [w,show (2:ℕ) ≠ 0 by decide,ite_false,show (2:ℕ)-1=1 by decide]
    exact Primitive.openCurrent_word p hp T 1 _
  change polygonSignArray w 0 1 2 = _
  rw [polygonSignArray,polygonHDet_eq_neg_turn,scalarSignValue_neg_real]
  simp only [polygonChord,h0,h1,h2]
  exact congrArg Neg.neg (parent_retained_initial_turn_sign q hR c hc hcut T)

end DirectGLSSW.ActiveArc.Split
