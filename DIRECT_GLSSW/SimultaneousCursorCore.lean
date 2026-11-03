import GenericCursorWithoutCrossing
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open Cursor RetainedWords Primitive AuxiliaryCarrierChart UniversalCarrierDomain EndpointEventGeometry

/-- One positive parameter simultaneously avoids both reflected affine wall
families over every original support. No independent-density intersection is used. -/
theorem exists_symmetric_all_support_core {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (L : Fin (n+1) ⊕ Unit → CarrierLine) (hL : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (n+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨n+1,by omega⟩)=0)
    (t₀ δ : ℝ) (hδ : 0<δ) :
    ∃ ε : ℝ, 0<ε ∧ ε<δ ∧
      ∀ s : Bool, ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
        (moveEndpoint (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val))
          (q 1-q 0) (t₀+(if s then ε else -ε))) (openCount q hR U.val-1) := by
  classical
  let I := Σ U : Support q hR, {ij : Fin (openCount q hR U.val) × Fin (openCount q hR U.val) //
    0 < ij.1.val ∧ ij.1.val < ij.2.val}
  let W := fun U : Support q hR => rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)
  let A := fun x : I => planarDet (W x.1 x.2.val.1-W x.1 x.2.val.2) (q 1-q 0)
  let B := fun x : I => polygonHDet (W x.1) 0 x.2.val.1 x.2.val.2+t₀*A x
  let C := fun x : Bool × I => if x.1 then A x.2 else -A x.2
  have hp (x : Bool × I) : C x≠0 ∨ B x.2≠0 := by
    have hh := supplied_head_affine_proper q hR L hL hT hinc hterminal x.2.1
      x.2.2.val.1 x.2.2.val.2 x.2.2.property.1 x.2.2.property.2 x.2.2.val.2.isLt
    change A x.2≠0 ∨ polygonHDet (W x.2.1) 0 x.2.2.val.1 x.2.2.val.2≠0 at hh
    by_cases hz : A x.2=0
    · right
      simpa only [B,hz,mul_zero,add_zero] using hh.resolve_left (not_not.mpr hz)
    · left
      dsimp only [C]
      split_ifs
      · exact hz
      · exact neg_ne_zero.mpr hz
  obtain ⟨ε,hε,hεδ,havoid⟩ := CursorWallTransport.exists_small_affine_avoidance C (fun x => B x.2) hp δ hδ
  refine ⟨ε,hε,hεδ,?_⟩
  intro s U i j k hij hjk hk hz
  have hkc : k<openCount q hR U.val := by have := open_count_ge_two q hR U.val;omega
  by_cases hi : i=0
  · subst i
    let x : I := ⟨U,⟨(⟨j,by omega⟩,⟨k,hkc⟩),hij,hjk⟩⟩
    apply havoid (s,x)
    rw [moveEndpoint_farDet (W U) (q 1-q 0) hij hjk] at hz
    change polygonHDet (W U) 0 j k+(t₀+(if s then ε else -ε))*A x=0 at hz
    change (if s then A x else -A x)*ε+(polygonHDet (W U) 0 j k+t₀*A x)=0
    cases s <;> simp only [Bool.false_eq_true,if_false,if_true] at hz ⊢ <;> nlinarith [hz]
  · have hj0 : j≠0 := by omega
    have hk0 : k≠0 := by omega
    simp only [polygonHDet,moveEndpoint,if_neg hi,if_neg hj0,if_neg hk0] at hz
    exact supplied_tail_noncollinear q hR L hL hT hinc hterminal U i j k (by omega) hij hjk hkc hz
end DirectGLSSW.ActiveArc.OpenCarrier
