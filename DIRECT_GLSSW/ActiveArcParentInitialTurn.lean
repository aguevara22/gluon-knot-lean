import ActiveArcOpenFirstSide
import ActiveArcClosedChildGeometry
import DirectGLSSW.HorizontalShortEdge

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Cursor Primitive
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val = a)

include hc

/-- The actual retained parent begins in the positive direction of the crossed physical edge. -/
theorem parent_retained_initial_turn_factor
    (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut)) :
    ∃ scale : ℝ, 0 < scale ∧
      planarDet (crossingPoint q c - q 0)
        (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T
          ⟨1,lt_of_lt_of_le (by decide : 1 < 2)
            (RetainedWords.open_count_ge_two _ _ T.val)⟩ - crossingPoint q c) =
      scale * planarDet (q 1 - q 0) (q c.val.2.succ - q c.val.2.castSucc) := by
  obtain ⟨s,hs,_,hy⟩ := Primitive.openVertex_one_firstEdge
    (parent q c hcut) (regular_parent q hR c hcut) T
  have hparent1 : parent q c hcut 1 = q c.val.2.succ := by
    change parent q c hcut (0 : Fin (b+1)).succ = _
    rw [parent_succ]
    congr 1
    apply Fin.ext
    simp only [vertex,Fin.val_succ,Fin.val_zero]
    omega
  rw [parent_zero,hparent1] at hy
  have hl : crossingPoint q c = affinePoint (q 0) (q 1) (leftParameter q c) := by
    simpa only [hc.1] using (leftParameter_spec q c).2.2
  have hr := (rightParameter_spec q c).2.2
  have hleft : crossingPoint q c - q 0 = leftParameter q c • (q 1 - q 0) := by
    rw [hl]
    ext <;> simp [affinePoint]
  have hright : Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T
      ⟨1,lt_of_lt_of_le (by decide : 1 < 2)
        (RetainedWords.open_count_ge_two _ _ T.val)⟩ - crossingPoint q c =
      (s * (1-rightParameter q c)) • (q c.val.2.succ - q c.val.2.castSucc) := by
    rw [hy,hr]
    ext <;> simp [affinePoint] <;> ring
  refine ⟨leftParameter q c * (s * (1-rightParameter q c)),
    mul_pos (leftParameter_spec q c).1 (mul_pos hs (sub_pos.mpr (rightParameter_spec q c).2.1)),?_⟩
  rw [hleft,hright]
  simp [planarDet]
  ring

/-- The initial Cartesian turn of every actual retained tiny-parent word has the physical crossing sign. -/
theorem parent_retained_initial_turn_sign
    (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut)) :
    scalarSignValue (planarDet (crossingPoint q c - q 0)
        (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T
          ⟨1,lt_of_lt_of_le (by decide : 1 < 2)
            (RetainedWords.open_count_ge_two _ _ T.val)⟩ - crossingPoint q c)) =
      scalarSignValue (planarDet (q 1 - q 0) (q c.val.2.succ - q c.val.2.castSucc)) := by
  obtain ⟨scale,hscale,he⟩ := parent_retained_initial_turn_factor q hR c hc hcut T
  rw [he]
  exact HorizontalShortEdge.scalarSignValue_positive_mul _ _ hscale

end DirectGLSSW.ActiveArc.Split
