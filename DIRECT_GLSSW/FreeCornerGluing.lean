import FreeCornerDomain
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CornerProjector
open Cursor Split Primitive RetainedWords OpenCarrier AuxiliaryCarrierChart UniversalCarrierDomain

/-- Full corner equality at the original arc. All near-corner and far-sign
conditions are produced internally; only the initial endpoint Core is supplied. -/
theorem firstEdgeFree_normalized_left_corner_eq {b : ℕ}
    (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (hfree : ∀ c : Crossing q, c.val.1≠0) (hAux : ClosedAuxiliary q hR)
    (hRI : GLSSWRootIndependence) (hleft : 0<planarDet (q 1-q 0) (q 2-q 1))
    (hcore : ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (openCount q hR U.val-1))
    (L : Fin (1+b+1) ⊕ Unit → CarrierLine) (hL : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (1+b+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨1+b+1,by omega⟩)=0) :
    (-1:ℚ)^(List.ofFn q).length * GammaM q hR hAux =
    (-1:ℚ)^(List.ofFn (suffix q)).length * GammaM (suffix q) (regular_suffix q hR)
      (corner_closedAuxiliary_suffix q hR hfree hAux) := by
  obtain ⟨ρ,hρ,hρ1,H⟩ := exists_normalized_left_corner_transport q hR hfree hAux hRI hleft
    (suffix_projector_far_of_supplied q hR L hL hT hinc hterminal)
  obtain ⟨t,htlo,ht1,hcoret⟩ := exists_all_support_core_in_interval q hR L hL hT hinc hterminal
    (1-ρ/2) 1 (by linarith)
  have ht0 : 0≤t := by linarith
  have hη : 0<1-t := by linarith
  have hηρ : 1-t<ρ := by linarith
  have hj := H (1-t) hη hηρ
  dsimp only at hj
  have ht : 1-(1-t)=t := by ring
  simp only [ht] at hj
  have hc := firstEdgeFree_normalized_GammaM_constancy q hR hfree hRI hAux t ht0 ht1 hcore hcoret
  exact hc.symm.trans hj
end DirectGLSSW.ActiveArc.CornerProjector
