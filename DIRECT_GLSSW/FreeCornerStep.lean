import FreeCornerGluing
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CornerProjector
open Cursor Split Primitive RetainedWords OpenCarrier AuxiliaryCarrierChart UniversalCarrierDomain

/-- Actual recursive corner step: equality and every suffix invariant are
produced for the literal suffix and the injectively restricted original family. -/
theorem firstEdgeFree_left_corner_step {b : ℕ}
    (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (hfree : ∀ c : Crossing q, c.val.1≠0) (hAux : ClosedAuxiliary q hR)
    (hRI : GLSSWRootIndependence) (hleft : TraversalClosure.RemainingLeft q)
    (hcore : ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (openCount q hR U.val-1))
    (L : Fin (1+b+1) ⊕ Unit → CarrierLine) (hL : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (1+b+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨1+b+1,by omega⟩)=0) :
    let M := L ∘ suffixCarrierMap (a:=1) (b:=b)
    ((-1:ℚ)^(List.ofFn q).length * GammaM q hR hAux =
      (-1:ℚ)^(List.ofFn (suffix q)).length * GammaM (suffix q) (regular_suffix q hR)
        (corner_closedAuxiliary_suffix q hR hfree hAux)) ∧
    Regular (suffix q) ∧ ClosedAuxiliary (suffix q) (regular_suffix q hR) ∧
    TraversalClosure.RemainingLeft (suffix q) ∧
    (∀ U : Support (suffix q) (regular_suffix q hR), ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex _ _ U) (openLast _ _ U.val))
      (openCount (suffix q) (regular_suffix q hR) U.val-1)) ∧
    UniversalLocus M ∧ PairTransverse M ∧
    (∀ e : Fin (b+1), lineValue (M (Sum.inl e)) (suffix q e.castSucc)=0 ∧
      lineValue (M (Sum.inl e)) (suffix q e.succ)=0) ∧
    lineValue (M (Sum.inr ())) (suffix q ⟨b+1,by omega⟩)=0 := by
  intro M
  have hfirst : 0<planarDet (q 1-q 0) (q 2-q 1) := by
    have hh := hleft (⟨0,by omega⟩ : Fin (1+b))
    have h0 : (⟨0,by omega⟩ : Fin (1+b)).castSucc.castSucc=(0 : Fin (1+b+2)) := Fin.ext rfl
    have h1 : (⟨0,by omega⟩ : Fin (1+b)).castSucc.succ=(1 : Fin (1+b+2)) := by
      apply Fin.ext
      change 1=1 % (1+b+2)
      exact (Nat.mod_eq_of_lt (by omega : 1<1+b+2)).symm
    have h2 : (⟨0,by omega⟩ : Fin (1+b)).succ.succ=(2 : Fin (1+b+2)) := by
      apply Fin.ext
      change 2=2 % (1+b+2)
      exact (Nat.mod_eq_of_lt (by omega : 2<1+b+2)).symm
    rw [h0,h1,h2] at hh
    exact hh
  have hf := suffixCarrierMap_injective (a:=1) (b:=b)
  exact ⟨firstEdgeFree_normalized_left_corner_eq q hR hfree hAux hRI hfirst hcore L hL hT hinc hterminal,
    regular_suffix q hR,corner_closedAuxiliary_suffix q hR hfree hAux,
    TraversalClosure.remainingLeft_suffix q hleft,
    suffix_all_support_core_of_supplied q hR L hL hT hinc hterminal,
    universalLocus_comap L hL _ hf,pairTransverse_comap L hT _ hf,
    supplied_suffix_incidence q L hinc hterminal⟩
end DirectGLSSW.ActiveArc.CornerProjector
