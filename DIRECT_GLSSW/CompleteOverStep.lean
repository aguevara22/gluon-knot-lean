import CrossingEndpointState
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open Cursor RetainedWords EndpointEventGeometry OpenCarrier AuxiliaryCarrierChart UniversalCarrierDomain

/-- Full first-over step starting at the original arc, with a single actual
post-event state whose geometry and all-support endpoint domain are produced. -/
theorem exists_complete_first_over_step {a b : ℕ}
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q) (hG : cyclicNoncollinear q)
    (hAux : ClosedAuxiliary q hR) (hleft : TraversalClosure.RemainingLeft q)
    (hRI : GLSSWRootIndependence) (c : Crossing q) (hc : FirstCrossing q c)
    (hcut : c.val.2.val=a)
    (hcore : ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (openCount q hR U.val-1))
    (L : Fin (a+b+1) ⊕ Unit → CarrierLine) (hL : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (a+b+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨a+b+1,by omega⟩)=0)
    (ho : crossingOver q (polygonCrossingOfArc q c)=(polygonCrossingOfArc q c).val.1) :
    ∃ ε : ℝ, 0<ε ∧
    ∃ (hm0 : 0≤leftParameter q c-ε) (hmc : leftParameter q c-ε<leftParameter q c)
      (hcp : leftParameter q c<leftParameter q c+ε) (hpb : leftParameter q c+ε<afterBound q c),
    let ht0 : 0≤leftParameter q c+ε := (lt_trans (leftParameter_spec q c).1 hcp).le
    let hA := (regular_first_window_iff q hR c hc _ ht0 hpb).mpr (ne_of_gt hcp)
    ((-1:ℚ)^(List.ofFn q).length * GammaM q hR hAux =
      (-1:ℚ)^(List.ofFn (moveStart q (leftParameter q c+ε))).length *
        GammaM (moveStart q (leftParameter q c+ε)) hA
          (Surviving.after_first_closedAuxiliary q hR c hc _ hcp hpb hAux)) ∧
    cyclicNoncollinear (moveStart q (leftParameter q c+ε)) ∧
    ClosedAuxiliary (moveStart q (leftParameter q c+ε)) hA ∧
    TraversalClosure.RemainingLeft (moveStart q (leftParameter q c+ε)) ∧
    (∀ V : Support (moveStart q (leftParameter q c+ε)) hA, ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex _ _ V) (openLast _ _ V.val))
      (openCount (moveStart q (leftParameter q c+ε)) hA V.val-1)) ∧
    (∀ e : Fin (a+b+1), lineValue (L (Sum.inl e)) (moveStart q (leftParameter q c+ε) e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (moveStart q (leftParameter q c+ε) e.succ)=0) ∧
    lineValue (L (Sum.inr ())) (moveStart q (leftParameter q c+ε) ⟨a+b+1,by omega⟩)=0 := by
  obtain ⟨ρ,hρ,H⟩ := exists_normalized_first_over_transport q hR c hc hRI hAux hcut hG
    (canonical_parent_far_of_supplied q hR hG c hcut L hL hT hinc hterminal)
    (event_domain_of_supplied q hR c hc L hL hT hinc hterminal) ho
  obtain ⟨ε,hε,hερ,hm0,hmc,hcp,hpb,hbefore,hpost⟩ :=
    exists_crossing_endpoint_state q hR hG hAux hleft c hc L hL hT hinc hterminal ρ hρ
  obtain ⟨hm0',hmc',hcp',hpb',hj⟩ := H ε hε hερ
  have he := before_first_normalized_GammaM_constancy q hR c hc hRI hAux _ hm0 hmc hcore hbefore
  refine ⟨ε,hε,hm0,hmc,hcp,hpb,he.symm.trans hj,hpost⟩
end DirectGLSSW.ActiveArc.Primitive
