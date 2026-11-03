import SimultaneousCursorCore
import AfterCursorCore
import UniversalCarrierTransportApplication
import UniversalCarrierParentCore
import ActiveArcNormalizedOverTransport
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open Cursor RetainedWords EndpointEventGeometry OpenCarrier AuxiliaryCarrierChart UniversalCarrierDomain

/-- Joint endpoint selection below an arbitrary requested positive radius.
The radius is an internal gluing input, discharged by the actual jump consumer. -/
theorem exists_crossing_endpoint_state {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q) (hG : cyclicNoncollinear q)
    (hAux : ClosedAuxiliary q hR) (hleft : TraversalClosure.RemainingLeft q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (L : Fin (n+1) ⊕ Unit → CarrierLine) (hL : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (n+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨n+1,by omega⟩)=0)
    (δ : ℝ) (hδ : 0<δ) :
    ∃ ε : ℝ, 0<ε ∧ ε<δ ∧
    ∃ (hm0 : 0≤leftParameter q c-ε) (hmc : leftParameter q c-ε<leftParameter q c)
      (hcp : leftParameter q c<leftParameter q c+ε) (hpb : leftParameter q c+ε<afterBound q c),
    let ht0 : 0≤leftParameter q c+ε := (lt_trans (leftParameter_spec q c).1 hcp).le
    let hA := (regular_first_window_iff q hR c hc _ ht0 hpb).mpr (ne_of_gt hcp)
    (∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
      (moveEndpoint (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val))
        (q 1-q 0) (leftParameter q c-ε)) (openCount q hR U.val-1)) ∧
    cyclicNoncollinear (moveStart q (leftParameter q c+ε)) ∧
    ClosedAuxiliary (moveStart q (leftParameter q c+ε)) hA ∧
    TraversalClosure.RemainingLeft (moveStart q (leftParameter q c+ε)) ∧
    (∀ V : Support (moveStart q (leftParameter q c+ε)) hA, ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex _ _ V) (openLast _ _ V.val))
      (openCount (moveStart q (leftParameter q c+ε)) hA V.val-1)) ∧
    (∀ e : Fin (n+1), lineValue (L (Sum.inl e)) (moveStart q (leftParameter q c+ε) e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (moveStart q (leftParameter q c+ε) e.succ)=0) ∧
    lineValue (L (Sum.inr ())) (moveStart q (leftParameter q c+ε) ⟨n+1,by omega⟩)=0 := by
  obtain ⟨ρ,hρ,H⟩ := TraversalClosure.after_first_state_closure q hR hG hAux c hc
  let d := min δ (min ρ (min (leftParameter q c) (afterBound q c-leftParameter q c)))
  have hd : 0<d := lt_min hδ (lt_min hρ (lt_min (leftParameter_spec q c).1
    (sub_pos.mpr (parameter_lt_afterBound q c))))
  obtain ⟨ε,hε,hεd,hcore⟩ := exists_symmetric_all_support_core q hR L hL hT hinc hterminal
    (leftParameter q c) d hd
  have heδ : ε<δ := lt_of_lt_of_le hεd (min_le_left _ _)
  have heρ : ε<ρ := lt_of_lt_of_le hεd (le_trans (min_le_right _ _) (min_le_left _ _))
  have hec : ε<leftParameter q c := lt_of_lt_of_le hεd
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have heb : ε<afterBound q c-leftParameter q c := lt_of_lt_of_le hεd
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hm0 : 0≤leftParameter q c-ε := by linarith
  have hmc : leftParameter q c-ε<leftParameter q c := by linarith
  have hcp : leftParameter q c<leftParameter q c+ε := by linarith
  have hpb : leftParameter q c+ε<afterBound q c := by linarith
  obtain ⟨hM,hGM,hAM⟩ := H (leftParameter q c+ε) hcp hpb (by
    rw [add_sub_cancel_left,abs_of_pos hε];exact heρ)
  refine ⟨ε,hε,heδ,hm0,hmc,hcp,hpb,?_,hGM,hAM,
    TraversalClosure.remainingLeft_moveStart q hleft _ (lt_of_lt_of_le hpb (afterBound_le_one q c)),?_,
    supplied_moveStart_incidence q L hinc hterminal _⟩
  · simpa only [Bool.false_eq_true,if_false,sub_eq_add_neg] using hcore false
  · apply after_first_all_support_core q hR c hc _ hcp hpb
    simpa only [if_true] using hcore true
end DirectGLSSW.ActiveArc.Primitive
