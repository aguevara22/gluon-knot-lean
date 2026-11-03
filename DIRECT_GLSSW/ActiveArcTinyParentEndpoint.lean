import OpenFirstEdgeGeometry
import ActiveArcBeforeFirstDaughters
import ActiveArcParentPrefixSign

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor
open Split Primitive OpenFirstEdgeGeometry

/-- Positive shortening of the first physical edge preserves its Cartesian
crossing sign against any actual later crossing edge. -/
theorem moveStart_crossing_sign {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (c : Crossing q) (t : ℝ) (ht : t<1) :
    scalarSignValue (planarDet (moveStart q t 1-moveStart q t 0)
      (moveStart q t c.val.2.succ-moveStart q t c.val.2.castSucc)) =
      scalarSignValue (planarDet (q 1-q 0) (q c.val.2.succ-q c.val.2.castSucc)) := by
  have hc : c.val.2 ≠ 0 := by
    intro h
    have hlt := c.property.1
    rw [h] at hlt
    exact (not_lt_of_ge (Fin.zero_le _)) hlt
  rw [first_tangent,moveStart_succ,moveStart_eq q t _ (castSucc_ne_zero hc)]
  have hdet : planarDet ((1-t) • (q 1-q 0)) (q c.val.2.succ-q c.val.2.castSucc) =
      (1-t)*planarDet (q 1-q 0) (q c.val.2.succ-q c.val.2.castSucc) := by
    simp [planarDet]; ring
  rw [hdet]
  let d := planarDet (q 1-q 0) (q c.val.2.succ-q c.val.2.castSucc)
  change scalarSignValue ((1-t)*d) = scalarSignValue d
  have hp : 0<1-t := by linarith
  rcases lt_trichotomy d 0 with hd | hd | hd
  · have hm := mul_neg_of_pos_of_neg hp hd
    simp [scalarSignValue,ne_of_lt hd,ne_of_lt hm,hd,hm]
  · rw [hd]
    simp [scalarSignValue]
  · have hm := mul_pos hp hd
    simp [scalarSignValue,ne_of_gt hd,ne_of_gt hm,not_lt_of_ge hd.le,not_lt_of_ge hm.le]

/-- The short-first approach of every actual prefixed parent word is exactly
the physical mark path. This is a point-function identity, not a support-motion theorem. -/
theorem parent_prefix_approach_endpoint
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut))
    (ε : ℝ) :
    approach (fun k => if k=0 then q 0 else
      rootedPolygonWord (Primitive.OpenVertex (parent q c hcut)
        (regular_parent q hR c hcut) T)
        (RetainedWords.openLast (parent q c hcut)
          (regular_parent q hR c hcut) T.val) (k-1)) ε =
      fun k => if k=0 then moveStart q (leftParameter q c*(1-ε)) 0 else
        rootedPolygonWord (Primitive.OpenVertex (parent q c hcut)
          (regular_parent q hR c hcut) T)
          (RetainedWords.openLast (parent q c hcut)
            (regular_parent q hR c hcut) T.val) (k-1) := by
  let p := parent q c hcut
  let hp := regular_parent q hR c hcut
  let w := rootedPolygonWord (Primitive.OpenVertex p hp T) (RetainedWords.openLast p hp T.val)
  have hw : w 0=crossingPoint q c := by
    dsimp only [w]
    rw [Primitive.openCurrent_word p hp T 0
      (lt_of_lt_of_le (by decide : 0<2) (RetainedWords.open_count_ge_two p hp T.val))]
    rw [Primitive.openVertex_zero]
    exact parent_zero q c hcut
  change approach (fun k => if k=0 then q 0 else w (k-1)) ε = _
  funext k
  by_cases hk : k=0
  · subst k
    rw [approach_zero]
    simp only [if_pos rfl,show (1:ℕ) ≠ 0 by decide,if_neg,Nat.sub_self,hw]
    exact (moveStart_approach_endpoint q c hc ε).symm
  · rw [approach_pos _ ε (Nat.pos_of_ne_zero hk)]
    simp only [if_neg hk]
    rfl

end DirectGLSSW.ActiveArc.Cursor
