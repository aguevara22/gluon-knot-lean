import PhysicalCalculationExists
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.FiniteCalculation
open Cursor Split Primitive RetainedWords OpenCarrier AuxiliaryCarrierChart UniversalCarrierDomain

/-- Explicit-input source-domain consumer. No supplied domain package,
transition callback, finite itinerary or recursive-current identity is assumed. -/
theorem actual_finite_calculation {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q) (hG : cyclicNoncollinear q)
    (hAux : ClosedAuxiliary q hR) (hleft : TraversalClosure.RemainingLeft q)
    (hcore : ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (openCount q hR U.val-1))
    (L : Fin (n+1) ⊕ Unit → CarrierLine) (hL : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (n+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨n+1,by omega⟩)=0)
    (hRI : GLSSWRootIndependence) :
    Calculation q ⟨hR,hG,hAux,hleft,hcore,L,hL,hT,hinc,hterminal⟩ :=
  calculation_exists hRI q ⟨hR,hG,hAux,hleft,hcore,L,hL,hT,hinc,hterminal⟩
end DirectGLSSW.ActiveArc.FiniteCalculation
