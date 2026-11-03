import ActiveArcOpenSideGeometry
import ActiveArcGammaM
import ActiveArcOpenParent
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc RetainedWords Split
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hcut : c.val.2.val = a)
variable (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut))

/-- The actual parent side carriers, preceded by c's original incoming edge and
followed by a fresh coordinate-line label. The fresh label is not a physical edge. -/
def parentCarrierChain
    (i : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val + 1)) :
    Fin (a+b+1) ⊕ Unit :=
  if h0 : i.val=0 then Sum.inl c.val.1 else
  if hm : i.val=openCount (parent q c hcut) (regular_parent q hR c hcut) T.val then Sum.inr () else
  Sum.inl (edge (a:=a) (openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val
    ⟨i.val-1,by have := i.isLt; omega⟩))

theorem parentCarrierChain_zero :
    parentCarrierChain q hR c hcut T 0 = Sum.inl c.val.1 := by
  simp [parentCarrierChain]

theorem parentCarrierChain_last :
    parentCarrierChain q hR c hcut T
      ⟨openCount (parent q c hcut) (regular_parent q hR c hcut) T.val,by omega⟩ = Sum.inr () := by
  have hm := open_count_ge_two (parent q c hcut) (regular_parent q hR c hcut) T.val
  simp [parentCarrierChain,show openCount (parent q c hcut) (regular_parent q hR c hcut) T.val ≠ 0 by omega]

theorem parentCarrierChain_middle
    (i : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val - 1)) :
    parentCarrierChain q hR c hcut T ⟨i.val+1,by have := i.isLt; omega⟩ =
    Sum.inl (edge (a:=a) (openSideCarrier (parent q c hcut) (regular_parent q hR c hcut) T.val i)) := by
  have hi := i.isLt
  simp [parentCarrierChain,show i.val+1 ≠ openCount (parent q c hcut) (regular_parent q hR c hcut) T.val by omega]

/-- All coordinate-chain labels are distinct, derived from actual NA side uniqueness. -/
theorem parentCarrierChain_injective : Function.Injective (parentCarrierChain q hR c hcut T) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hc := c.property.1
  change c.val.1.val<c.val.2.val at hc
  have hleft : c.val.1.val<a := by omega
  have he : ∀ e : Fin (b+1), c.val.1 ≠ edge (a:=a) e := by
    intro e h
    have hh := congrArg Fin.val h
    change c.val.1.val=a+e.val at hh
    omega
  by_cases hi0 : i.val=0
  · by_cases hj0 : j.val=0
    · exact Fin.ext (hi0.trans hj0.symm)
    · by_cases hjm : j.val=openCount (parent q c hcut) (regular_parent q hR c hcut) T.val
      · simp only [parentCarrierChain,dif_pos hi0,dif_neg hj0,dif_pos hjm,Sum.inl_ne_inr,Sum.inr_ne_inl] at hij
      · simp only [parentCarrierChain,dif_pos hi0,dif_neg hj0,dif_neg hjm,Sum.inl.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at hij
        exact False.elim (he _ hij)
  · by_cases hj0 : j.val=0
    · by_cases him : i.val=openCount (parent q c hcut) (regular_parent q hR c hcut) T.val
      · simp only [parentCarrierChain,dif_neg hi0,dif_pos him,dif_pos hj0,Sum.inl_ne_inr,Sum.inr_ne_inl] at hij
      · simp only [parentCarrierChain,dif_neg hi0,dif_neg him,dif_pos hj0,Sum.inl.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at hij
        exact False.elim (he _ hij.symm)
    · by_cases him : i.val=openCount (parent q c hcut) (regular_parent q hR c hcut) T.val
      · by_cases hjm : j.val=openCount (parent q c hcut) (regular_parent q hR c hcut) T.val
        · exact Fin.ext (him.trans hjm.symm)
        · simp only [parentCarrierChain,dif_neg hi0,dif_pos him,dif_neg hj0,dif_neg hjm,Sum.inl_ne_inr,Sum.inr_ne_inl] at hij
      · by_cases hjm : j.val=openCount (parent q c hcut) (regular_parent q hR c hcut) T.val
        · simp only [parentCarrierChain,dif_neg hi0,dif_neg him,dif_neg hj0,dif_pos hjm,Sum.inl_ne_inr,Sum.inr_ne_inl] at hij
        · simp only [parentCarrierChain,dif_neg hi0,dif_neg him,dif_neg hj0,dif_neg hjm,Sum.inl.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at hij
          have hh := openSideCarrier_injective (parent q c hcut) (regular_parent q hR c hcut) T.val T.property
            (edge_injective hij)
          have hv := congrArg Fin.val hh
          apply Fin.ext
          dsimp at hv
          omega

end DirectGLSSW.ActiveArc.OpenCarrier
