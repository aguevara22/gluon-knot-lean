import ActualTailCarrierDomain
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open Cursor RetainedWords Primitive AuxiliaryCarrierChart UniversalCarrierDomain
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (L : Fin (n+1) ⊕ Unit → CarrierLine)
variable (hinc : ∀ e : Fin (n+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
  lineValue (L (Sum.inl e)) (q e.succ)=0)
variable (hterminal : lineValue (L (Sum.inr ())) (q ⟨n+1,by omega⟩)=0)

private theorem supplied_affine_value (K : CarrierLine) (x y : PlanarPoint ℝ) (t : ℝ)
    (hx : lineValue K x=0) (hy : lineValue K y=0) : lineValue K (affinePoint x y t)=0 := by
  have he : lineValue K (affinePoint x y t)=(1-t)*lineValue K x+t*lineValue K y := by
    dsimp [lineValue,affinePoint,planarDet];ring
  rw [he,hx,hy];ring

include hinc hterminal in
/-- Positive retained-vertex incidence requires no crossing of the first edge,
or even the existence of a crossing anywhere in the physical arc. -/
theorem tail_vertex_supplied_incidence_without_crossing (U : Support q hR)
    (i : Fin (openCount q hR U.val-1)) :
    let f := eventCarrierChain q hR U
    let W := rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)
    lineValue (L (f ⟨i.val,by have := i.isLt;omega⟩)) (W (i.val+1))=0 ∧
      lineValue (L (f ⟨i.val+1,by have := i.isLt;omega⟩)) (W (i.val+1))=0 := by
  dsimp only
  have hi : i.val+1<openCount q hR U.val := by have := i.isLt;omega
  rw [openCurrent_word q hR U (i.val+1) hi]
  constructor
  · simp only [eventCarrierChain,dif_pos i.isLt]
    obtain ⟨s,t,_,_,_,_,ht⟩ := openSideCarrier_physical q hR U.val i
    change lineValue (L (Sum.inl (openSideCarrier q hR U.val i)))
      (RetainedWords.vertex q hR U.val (start q) ⟨i.val+1,hi⟩)=0
    rw [ht]
    exact supplied_affine_value _ _ _ _ (hinc _).1 (hinc _).2
  · by_cases hj : i.val+1<openCount q hR U.val-1
    · simp only [eventCarrierChain,dif_pos hj]
      obtain ⟨s,t,_,_,_,hs,_⟩ := openSideCarrier_physical q hR U.val ⟨i.val+1,hj⟩
      change lineValue (L (Sum.inl (openSideCarrier q hR U.val ⟨i.val+1,hj⟩)))
        (RetainedWords.vertex q hR U.val (start q) ⟨i.val+1,hi⟩)=0
      rw [hs]
      exact supplied_affine_value _ _ _ _ (hinc _).1 (hinc _).2
    · simp only [eventCarrierChain,dif_neg hj]
      have hv : (⟨i.val+1,hi⟩ : Fin (openCount q hR U.val))=openLast q hR U.val := by
        apply Fin.ext
        change i.val+1=openCount q hR U.val-1
        omega
      change lineValue (L (Sum.inr ())) (RetainedWords.vertex q hR U.val (start q) ⟨i.val+1,hi⟩)=0
      rw [hv,open_vertex_last]
      exact hterminal
end DirectGLSSW.ActiveArc.OpenCarrier
