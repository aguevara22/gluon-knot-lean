import ActiveArcRightCarrierSecant

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords OpenCarrier

/-- Under the literal finite auxiliary determinant condition, an incompatible
actual support either has no endpoint event or has one adjacent transverse
virtual secant. All indices, collinearity, transversality and endpoint
noncoincidence are derived from its physical right-carrier side. -/
theorem incompatible_eventCarrierNonvanishing_classification
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (U : Support q hR) (hu : c∉U.val)
    (hbad : ∃ d∈U.val, ¬Split.Compatible (a:=n) (b:=0) q hR c d)
    (hF : EventCarrierNonvanishing q hR c U) :
    ShortEdgeSignStability.CoreHGeneric (eventOpenWord q hR U c) (openCount q hR U.val-1) ∨
      ∃ k : ℕ, 0<k ∧ k+1≤openCount q hR U.val-1 ∧ ∃ τ : ℝ,
        0<τ ∧ τ≠1 ∧
        eventOpenWord q hR U c 0≠eventOpenWord q hR U c (k+1) ∧
        eventOpenWord q hR U c k = eventOpenWord q hR U c 0+
          τ • (eventOpenWord q hR U c (k+1)-eventOpenWord q hR U c 0) ∧
        planarDet (eventOpenWord q hR U c k-eventOpenWord q hR U c (k+1)) (q 1-q 0)≠0 ∧
        ∀ i j l, i<j → j<l → l≤openCount q hR U.val-1 →
          (i≠0 ∨ j≠k ∨ l≠k+1) → polygonHDet (eventOpenWord q hR U c) i j l≠0 := by
  classical
  by_cases hex : ∃ k : Fin (openCount q hR U.val-1), openSideCarrier q hR U.val k=c.val.2
  · obtain ⟨k,hkcar⟩ := hex
    obtain ⟨hk0,τ,hcol,htrans,ht0,ht1,hne⟩ := event_right_carrier_secant q hR c hc U hu k hkcar
    have htpos : 0<τ := by
      rcases lt_or_gt_of_ne ht0 with htneg|htpos
      · have hnot := eventOpenWord_negative_event_not_adjacent q hR c hc U hu hbad
          k.val (k.val+1) hk0 (by omega) (by have := k.isLt;omega) τ htneg hcol
        exact False.elim (hnot rfl)
      · exact htpos
    exact Or.inr ⟨k.val,hk0,by have := k.isLt;omega,τ,htpos,ht1,hne,hcol,htrans,
      eventCarrierNonvanishing_isolated_of_carrier q hR c U hF k hkcar⟩
  · apply Or.inl
    apply eventCarrierNonvanishing_core_of_no_carrier q hR c U hF
    intro k hk
    exact hex ⟨k,hk⟩

end DirectGLSSW.ActiveArc.Primitive
