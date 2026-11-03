import UniversalChainVertices
import ActiveArcEventSuppliedLines
import ActualCursorConstancy
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open Cursor RetainedWords Primitive AuxiliaryCarrierChart UniversalCarrierDomain
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
variable (L : Fin (n+1) ⊕ Unit → CarrierLine)
variable (hL : UniversalLocus L) (hT : PairTransverse L)
variable (hinc : ∀ e : Fin (n+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
  lineValue (L (Sum.inl e)) (q e.succ)=0)
variable (hterminal : lineValue (L (Sum.inr ())) (q ⟨n+1,by omega⟩)=0)

include hc hinc hterminal in
theorem tail_vertex_supplied_incidence (U : Support q hR)
    (i : Fin (openCount q hR U.val-1)) :
    let f := eventCarrierChain q hR U
    let W := rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)
    lineValue (L (f ⟨i.val,by have := i.isLt;omega⟩)) (W (i.val+1))=0 ∧
      lineValue (L (f ⟨i.val+1,by have := i.isLt;omega⟩)) (W (i.val+1))=0 := by
  dsimp only
  have hi : i.val+1<openCount q hR U.val := by have := i.isLt;omega
  have hp : i.val+1≠0 := by omega
  have hh := event_pair_supplied_incidence q hR c U L hinc hterminal hc ⟨i.val+1,hi⟩
  rw [eventOpenWord_pos q hR U c (i.val+1) (by omega) hi] at hh
  rw [openCurrent_word q hR U (i.val+1) hi]
  simpa only [eventCarrierPair,if_neg hp,Nat.add_sub_cancel_right] using hh

include hc hL hT hinc hterminal in
theorem actual_tail_noncollinear (U : Support q hR) (i j k : ℕ)
    (hi : 0 < i) (hij : i < j) (hjk : j < k) (hk : k < openCount q hR U.val) :
    polygonHDet (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) i j k≠0 := by
  let M := openCount q hR U.val-1
  have hM : M+1=openCount q hR U.val := by have := open_count_ge_two q hR U.val;omega
  let f := fun v : Fin (M+1) => eventCarrierChain q hR U (Fin.cast hM v)
  let V := fun v : Fin M => rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val) (v.val+1)
  have hf : Function.Injective f := (eventCarrierChain_injective q hR U).comp (Fin.cast_injective hM)
  have hV (v : Fin M) : lineValue (L (f v.castSucc)) (V v)=0 ∧ lineValue (L (f v.succ)) (V v)=0 :=
    tail_vertex_supplied_incidence q hR c hc L hinc hterminal U v
  have hh := chain_vertices_noncollinear L hL hT f hf V hV
    ⟨i-1,by dsimp [M];omega⟩ ⟨j-1,by dsimp [M];omega⟩ ⟨k-1,by dsimp [M];omega⟩ (by change i-1 < j-1;omega) (by change j-1 < k-1;omega)
  simpa only [V,Nat.sub_add_cancel (show 1 ≤ i by omega),Nat.sub_add_cancel (show 1 ≤ j by omega),
    Nat.sub_add_cancel (show 1 ≤ k by omega),polygonHDet] using hh

include hc hL hT hinc hterminal in
theorem actual_head_affine_proper (U : Support q hR) (i j : ℕ)
    (hi : 0 < i) (hij : i < j) (hj : j < openCount q hR U.val) :
    let W := rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)
    planarDet (W i-W j) (q 1-q 0)≠0 ∨ polygonHDet W 0 i j≠0 := by
  dsimp only
  let W := rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)
  let M := openCount q hR U.val-1
  have hM : M+1=openCount q hR U.val := by have := open_count_ge_two q hR U.val;omega
  let f := fun v : Fin (M+1) => eventCarrierChain q hR U (Fin.cast hM v)
  let V := fun v : Fin M => W (v.val+1)
  have hf : Function.Injective f := (eventCarrierChain_injective q hR U).comp (Fin.cast_injective hM)
  have hV (v : Fin M) : lineValue (L (f v.castSucc)) (V v)=0 ∧ lineValue (L (f v.succ)) (V v)=0 :=
    tail_vertex_supplied_incidence q hR c hc L hinc hterminal U v
  have hd : W i≠W j := by
    simpa only [V,Nat.sub_add_cancel (show 1 ≤ i by omega),Nat.sub_add_cancel (show 1 ≤ j by omega)] using
      chain_vertices_distinct L hL hT f hf V hV ⟨i-1,by dsimp [M];omega⟩
        ⟨j-1,by dsimp [M];omega⟩ (by change i-1 < j-1;omega)
  have hoff : lineValue (L (Sum.inl 0)) (W j)≠0 := by
    have hh := chain_vertex_off_first L hL hT f hf V hV ⟨j-1,by dsimp [M];omega⟩ (by change 0 < j-1;omega)
    have hf0 : f 0=Sum.inl 0 := eventCarrierChain_zero q hR U
    simpa only [hf0,V,Nat.sub_add_cancel (show 1 ≤ j by omega)] using hh
  have hdet := first_line_off_det (L (Sum.inl 0)) (q 0) (q 1) (W j)
    (hinc 0).1 (hinc 0).2 (fun he => hR.edge_nonzero 0 (by change q 1-q 0=0;rw [he,sub_self])) hoff
  have hW0 : W 0=q 0 := by dsimp [W];rw [openCurrent_word q hR U 0 (by have := open_count_ge_two q hR U.val;omega),openVertex_zero]
  have hh := moving_head_affine_proper (q 0) (q 1-q 0) (W i) (W j) hd hdet
  change planarDet (W i-W j) (q 1-q 0)≠0 ∨ planarDet (W i-W j) (W 0-W j)≠0
  rw [hW0]
  exact hh
end DirectGLSSW.ActiveArc.OpenCarrier
