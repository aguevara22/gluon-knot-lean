import CursorGenericityWithoutCrossing
import ParallelSecantAvoidance
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open Cursor RetainedWords Primitive AuxiliaryCarrierChart UniversalCarrierDomain EndpointEventGeometry

/-- Every nonempty parameter interval contains ONE all-support generic cursor
parameter. No actual crossing, first-crossing or crossing-free premise is needed. -/
theorem exists_all_support_core_in_interval {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (L : Fin (n+1) ⊕ Unit → CarrierLine) (hL : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (n+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨n+1,by omega⟩)=0)
    (a b : ℝ) (hab : a<b) :
    ∃ t : ℝ, a<t ∧ t<b ∧
      ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
        (moveEndpoint (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (q 1-q 0) t)
        (openCount q hR U.val-1) := by
  classical
  let I := Σ U : Support q hR, {ij : Fin (openCount q hR U.val) × Fin (openCount q hR U.val) //
    0 < ij.1.val ∧ ij.1.val < ij.2.val}
  let W := fun U : Support q hR => rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)
  let A := fun x : I => planarDet (W x.1 x.2.val.1-W x.1 x.2.val.2) (q 1-q 0)
  let B := fun x : I => polygonHDet (W x.1) 0 x.2.val.1 x.2.val.2+a*A x
  have hp (x : I) : A x≠0 ∨ B x≠0 := by
    have hh := supplied_head_affine_proper q hR L hL hT hinc hterminal x.1
      x.2.val.1 x.2.val.2 x.2.property.1 x.2.property.2 x.2.val.2.isLt
    dsimp only at hh
    change A x≠0 ∨ polygonHDet (W x.1) 0 x.2.val.1 x.2.val.2≠0 at hh
    rcases hh with hh|hh
    · exact Or.inl hh
    · by_cases hz : A x=0
      · exact Or.inr (by simpa only [B,hz,mul_zero,add_zero] using hh)
      · exact Or.inl hz
  obtain ⟨η,hη,hηb,havoid⟩ := CursorWallTransport.exists_small_affine_avoidance A B hp (b-a) (sub_pos.mpr hab)
  refine ⟨a+η,by linarith,by linarith,?_⟩
  intro U i j k hij hjk hk hz
  have hkc : k<openCount q hR U.val := by have := open_count_ge_two q hR U.val;omega
  by_cases hi : i=0
  · subst i
    let x : I := ⟨U,⟨(⟨j,by omega⟩,⟨k,hkc⟩),hij,hjk⟩⟩
    apply havoid x
    rw [moveEndpoint_farDet (W U) (q 1-q 0) hij hjk] at hz
    change polygonHDet (W U) 0 j k+(a+η)*A x=0 at hz
    change A x*η+(polygonHDet (W U) 0 j k+a*A x)=0
    nlinarith [hz]
  · have hj0 : j≠0 := by omega
    have hk0 : k≠0 := by omega
    simp only [polygonHDet,moveEndpoint,if_neg hi,if_neg hj0,if_neg hk0] at hz
    exact supplied_tail_noncollinear q hR L hL hT hinc hterminal U i j k (by omega) hij hjk hkc hz
end DirectGLSSW.ActiveArc.OpenCarrier
