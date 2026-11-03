import ActiveArcSuffix
import ActiveArcOpenFirstSide
import DirectGLSSW.HorizontalShortEdge

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Primitive RetainedWords

private theorem scalarSignValue_neg_real (x : ℝ) :
    scalarSignValue (-x) = -scalarSignValue x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hp : 0 < -x := neg_pos.mpr hx
    simp [scalarSignValue, ne_of_lt hx, ne_of_gt hp, hx, not_lt_of_ge hp.le]
  · subst x
    simp [scalarSignValue]
  · have hn : -x < 0 := neg_neg_of_pos hx
    simp [scalarSignValue, ne_of_gt hx, ne_of_lt hn, hn, not_lt_of_ge hx.le]

/-- The first two actual retained vertices of the ordinary suffix word have
the original corner's turn sign, with the sign-array convention negated. -/
theorem suffix_retained_prefix_sign012
    {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (T : Primitive.Support (suffix (a:=1) q) (regular_suffix (a:=1) q hR)) :
    polygonSignArray (fun k => if k=0 then q 0 else
      rootedPolygonWord (Primitive.OpenVertex (suffix (a:=1) q)
        (regular_suffix (a:=1) q hR) T)
        (RetainedWords.openLast (suffix (a:=1) q)
          (regular_suffix (a:=1) q hR) T.val) (k-1)) 0 1 2 =
      -scalarSignValue (planarDet (q 1-q 0) (q 2-q 1)) := by
  let r := suffix (a:=1) q
  let hr := regular_suffix (a:=1) q hR
  let w : ℕ → PlanarPoint ℝ := fun k => if k=0 then q 0 else
    rootedPolygonWord (Primitive.OpenVertex r hr T)
      (RetainedWords.openLast r hr T.val) (k-1)
  have h0 : w 0 = q 0 := by simp [w]
  have h1 : w 1 = q 1 := by
    simp only [w, show (1:ℕ) ≠ 0 by decide, ite_false, Nat.sub_self]
    rw [Primitive.openCurrent_word r hr T 0
      (lt_of_lt_of_le (by decide : 0 < 2) (RetainedWords.open_count_ge_two r hr T.val))]
    rw [Primitive.openVertex_zero]
    change r ⟨0, by omega⟩ = q 1
    simp [r, suffix, vertex]
  have h2 : w 2 = Primitive.OpenVertex r hr T
      ⟨1,lt_of_lt_of_le (by decide : 1 < 2) (RetainedWords.open_count_ge_two r hr T.val)⟩ := by
    simp only [w, show (2:ℕ) ≠ 0 by decide, ite_false, show (2:ℕ)-1=1 by decide]
    exact Primitive.openCurrent_word r hr T 1 _
  obtain ⟨s,hs,_,hy⟩ := Primitive.openVertex_one_firstEdge r hr T
  have hr0 : r 0 = q 1 := by simp [r, suffix, vertex]
  have hr1 : r 1 = q 2 := by
    have hN : 2 < 1+b+2 := by omega
    change q (vertex (a:=1) (⟨1, by omega⟩ : Fin (b+2))) = q 2
    apply congrArg q
    have hidx : vertex (a:=1) (⟨1, by omega⟩ : Fin (b+2)) =
        (Fin.ofNat' (1+b+2) 2) := by
      apply Fin.ext
      change 1 + 1 = (Fin.ofNat' (1+b+2) 2).val
      rw [Fin.val_ofNat', Nat.mod_eq_of_lt hN]
    exact hidx
  rw [hr0,hr1] at hy
  have hmove : affinePoint (q 1) (q 2) s - q 1 = s • (q 2-q 1) := by
    ext <;> simp [affinePoint] <;> ring
  have hturn : planarDet (w 1-w 0) (w 2-w 1) =
      s * planarDet (q 1-q 0) (q 2-q 1) := by
    rw [h1,h0,h2,hy,hmove]
    simp [planarDet]
    ring
  have hturn' : planarDet (polygonChord w 0 1) (polygonChord w 1 2) =
      s * planarDet (q 1-q 0) (q 2-q 1) := by
    simpa [polygonChord] using hturn
  change scalarSignValue (polygonHDet w 0 1 2) = _
  rw [polygonHDet_eq_neg_turn, hturn', scalarSignValue_neg_real,
    DirectGLSSW.HorizontalShortEdge.scalarSignValue_positive_mul _ _ hs]

/-- A left original corner therefore gives the actual retained prefix sign -1. -/
theorem suffix_retained_prefix_sign012_eq_neg_one
    {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (T : Primitive.Support (suffix (a:=1) q) (regular_suffix (a:=1) q hR))
    (hleft : 0 < planarDet (q 1-q 0) (q 2-q 1)) :
    polygonSignArray (fun k => if k=0 then q 0 else
      rootedPolygonWord (Primitive.OpenVertex (suffix (a:=1) q)
        (regular_suffix (a:=1) q hR) T)
        (RetainedWords.openLast (suffix (a:=1) q)
          (regular_suffix (a:=1) q hR) T.val) (k-1)) 0 1 2 = -1 := by
  rw [suffix_retained_prefix_sign012 q hR T]
  simp [scalarSignValue, ne_of_gt hleft, not_lt_of_ge hleft.le]

end DirectGLSSW.ActiveArc.Split
