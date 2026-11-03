import ActiveArcIncompatibleCarrierClassification
import ActiveArcNoEventCurrent
import ActiveArcVirtualNoJump

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords EndpointEventGeometry

/-- Actual incompatible current stability under the explicit finite carrier
nonvanishing domain. No event geometry or jump equality is assumed. -/
theorem exists_incompatible_carrier_domain_current_eq
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (U : Support q hR) (hu : c∉U.val)
    (hbad : ∃ d∈U.val, ¬Split.Compatible (a:=n) (b:=0) q hR c d)
    (hF : EventCarrierNonvanishing q hR c U) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ ε : ℝ, 0<ε → ε<ρ →
      OpenMarkedCurrent.entry
        (polygonSignArray (moveEndpoint (eventOpenWord q hR U c) (q 1-q 0) ε))
        0 (openCount q hR U.val-1) -
      OpenMarkedCurrent.entry
        (polygonSignArray (moveEndpoint (eventOpenWord q hR U c) (q 1-q 0) (-ε)))
        0 (openCount q hR U.val-1) = 0 := by
  rcases incompatible_eventCarrierNonvanishing_classification q hR c hc U hu hbad hF
      with hCore | ⟨k,hk,hkn,τ,htpos,ht1,hne,hcol,htrans,hiso⟩
  · obtain ⟨ρ,hρ,hgood⟩ := generic_eventOpenWord_openCurrent_eq q hR c U hCore
    exact ⟨ρ,hρ,fun ε he her => sub_eq_zero.mpr (hgood ε he her).2.2⟩
  · obtain ⟨ρ,hρ,hgood⟩ := incompatible_isolated_event_openCurrent_eq
      q hR c hc U hu hbad k (k+1) hk (by omega) hkn τ hcol htrans hiso
    exact ⟨ρ,hρ,fun ε he her => sub_eq_zero.mpr (hgood ε he her).2.2⟩


end DirectGLSSW.ActiveArc.Primitive
