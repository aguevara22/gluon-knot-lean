import ActiveArcParentCarrierChain
import ActiveArcOpenLineGeometry
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc RetainedWords Split AuxiliaryCarrierChart Cursor
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hcut : c.val.2.val=a)

/-- Every point of a parent physical carrier belongs to its original physical carrier. -/
theorem parent_affine_original (e : Fin (b+1)) (t : ℝ) :
    ∃ s : ℝ, affinePoint (parent q c hcut e.castSucc) (parent q c hcut e.succ) t =
      affinePoint (q (edge (a:=a) e).castSucc) (q (edge (a:=a) e).succ) s := by
  by_cases he : e=0
  · subst e
    refine ⟨rightParameter q c+(1-rightParameter q c)*t,?_⟩
    change affinePoint (moveStart (suffix q) (rightParameter q c) 0)
      (moveStart (suffix q) (rightParameter q c) 1) t=_
    rw [moveStart_zero,moveStart_eq _ _ 1 (by exact Fin.ne_of_val_ne (by simp)),affinePoint_suffix]
    rfl
  · refine ⟨t,?_⟩
    change affinePoint (moveStart (suffix q) (rightParameter q c) e.castSucc)
      (moveStart (suffix q) (rightParameter q c) e.succ) t=_
    rw [moveStart_eq _ _ _ (castSucc_ne_zero he),moveStart_succ]
    simp only [suffix,vertex_castSucc,vertex_succ]

variable (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut))

/-- Literal retained parent side endpoints have their actual original line parameters. -/
theorem parent_side_original
    (i : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val-1)) :
    ∃ s t : ℝ,
      Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T
        ⟨i.val,by change i.val < openCount (parent q c hcut) (regular_parent q hR c hcut) T.val; have := i.isLt; omega⟩ =
        affinePoint (q (edge (a:=a) (openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val i)).castSucc)
          (q (edge (a:=a) (openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val i)).succ) s ∧
      Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T
        ⟨i.val+1,by change i.val+1 < openCount (parent q c hcut) (regular_parent q hR c hcut) T.val; have := i.isLt; omega⟩ =
        affinePoint (q (edge (a:=a) (openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val i)).castSucc)
          (q (edge (a:=a) (openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val i)).succ) t := by
  obtain ⟨s,t,_,_,_,hs,ht⟩ := openSideCarrier_physical (parent q c hcut) (regular_parent q hR c hcut) T.val i
  obtain ⟨u,hu⟩ := parent_affine_original q c hcut (openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val i) s
  obtain ⟨v,hv⟩ := parent_affine_original q c hcut (openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val i) t
  exact ⟨u,v,hs.trans hu,ht.trans hv⟩

/-- Evaluate the coordinate-only terminal label separately from all physical edge labels. -/
def parentChartLines : Fin (a+b+1) ⊕ Unit → CarrierLine :=
  Sum.elim (physicalLine q) (fun _ => terminalLine q)

end DirectGLSSW.ActiveArc.OpenCarrier
