import ActiveArcChildVisitOrder
import DirectGLSSW.SpinorGates

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)

/-- Exact positive scaling on every physical side, including the closing side. -/
theorem child_cyclicTangent (e : Fin (a+1)) :
    cyclicTangent (child q hR c hfirst hcut) e =
      childScale q c e • (q (childEdge (b:=b) e).succ-
        q (childEdge (b:=b) e).castSucc) := by
  have h0 := child_affine q hR c hfirst hcut e 0
  have h1 := child_affine q hR c hfirst hcut e 1
  simp only [affinePoint_zero, mul_zero, add_zero] at h0
  simp only [affinePoint_one, mul_one] at h1
  unfold cyclicTangent
  rw [h0,h1]
  apply Prod.ext <;> simp [affinePoint] <;> ring

/-- The ordered child determinant is the old physical determinant times
an explicitly positive product of the two shortening factors. -/
theorem child_cyclicTangent_det (e f : Fin (a+1)) :
    planarDet (cyclicTangent (child q hR c hfirst hcut) e)
      (cyclicTangent (child q hR c hfirst hcut) f) =
      (childScale q c e*childScale q c f)*
        planarDet (q (childEdge (b:=b) e).succ-q (childEdge (b:=b) e).castSucc)
          (q (childEdge (b:=b) f).succ-q (childEdge (b:=b) f).castSucc) := by
  rw [child_cyclicTangent q hR c hfirst hcut e,
    child_cyclicTangent q hR c hfirst hcut f]
  simp [planarDet]
  ring

theorem child_cyclicTangent_det_pos_iff (e f : Fin (a+1)) :
    0<planarDet (cyclicTangent (child q hR c hfirst hcut) e)
      (cyclicTangent (child q hR c hfirst hcut) f) ↔
      0<planarDet (q (childEdge (b:=b) e).succ-q (childEdge (b:=b) e).castSucc)
        (q (childEdge (b:=b) f).succ-q (childEdge (b:=b) f).castSucc) := by
  rw [child_cyclicTangent_det q hR c hfirst hcut]
  exact mul_pos_iff_of_pos_left (mul_pos (childScale_pos q c e) (childScale_pos q c f))

theorem child_cyclicTangent_det_sign (e f : Fin (a+1)) :
    scalarSignValue (planarDet (cyclicTangent (child q hR c hfirst hcut) e)
      (cyclicTangent (child q hR c hfirst hcut) f)) =
      scalarSignValue (planarDet
        (q (childEdge (b:=b) e).succ-q (childEdge (b:=b) e).castSucc)
        (q (childEdge (b:=b) f).succ-q (childEdge (b:=b) f).castSucc)) := by
  rw [child_cyclicTangent_det q hR c hfirst hcut]
  have hp := mul_pos (childScale_pos q c e) (childScale_pos q c f)
  have hneg (x : ℝ) :
      (childScale q c e*childScale q c f)*x<0 ↔ x<0 := by
    simpa only [mul_zero] using
      (mul_lt_mul_left hp : (childScale q c e*childScale q c f)*x <
        (childScale q c e*childScale q c f)*0 ↔ x<0)
  simp only [scalarSignValue, mul_eq_zero, ne_of_gt hp, false_or, hneg]

end DirectGLSSW.ActiveArc.Split
