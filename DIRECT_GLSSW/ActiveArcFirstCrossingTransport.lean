import ActiveArcConfigurationEventOrder
import ActiveArcFirstCrossing

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

noncomputable section

namespace DirectGLSSW.ActiveArc.ConfigurationLocality

open DirectGLSSW ActiveArc Filter Topology

variable {n : ℕ}
variable (q r : Fin (n + 2) → PlanarPoint ℝ)

/-- An order-preserving, edge-label-preserving crossing correspondence carries the
literal minimum crossing on the first physical edge to the literal minimum. -/
theorem firstCrossing_transport_of_event_order
    (hQ : Regular q) (hR : Regular r)
    (E : Crossing q ≃ Crossing r)
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : Event q,
      ((eventOrder q hQ.noTriple).lt x y ↔
        (eventOrder r hR.noTriple).lt
          (eventMapEquiv q r E x) (eventMapEquiv q r E y)))
    (c : Crossing q) (hc : Cursor.FirstCrossing q c) :
    Cursor.FirstCrossing r (E c) := by
  refine ⟨?_, ?_⟩
  · have h := congrArg Prod.fst (hlabels c)
    rw [h]
    exact hc.1
  · intro d hd
    have hval : d.val = (E.symm d).val :=
      (congrArg Subtype.val (E.apply_symm_apply d)).symm.trans (hlabels (E.symm d))
    have hdin : (E.symm d).val.1 = 0 := by rw [← hval]; exact hd
    have hnot : ¬ leftParameter r d < leftParameter r (E c) := by
      intro hlt
      let x : Event q := Sum.inr (E.symm d, false)
      let y : Event q := Sum.inr (c, false)
      have hxmap : eventMapEquiv q r E x = Sum.inr (d, false) := by
        change Sum.inr (E (E.symm d), false) = Sum.inr (d, false)
        rw [E.apply_symm_apply]
      have hymap : eventMapEquiv q r E y = Sum.inr (E c, false) := by
        rfl
      have hEc0 : (E c).val.1 = 0 := by rw [hlabels c]; exact hc.1
      have hltR : (eventOrder r hR.noTriple).lt
          (Sum.inr (d, false)) (Sum.inr (E c, false)) := by
        rw [event_lt_iff r hR.noTriple]
        right
        constructor
        · simp [edgeTag, visitEdge, hd, hEc0]
        · simpa [parameter, visitParameter] using hlt
      have hltQ := (horder x y).mpr (by simpa [hxmap, hymap] using hltR)
      have hparts := (event_lt_iff q hQ.noTriple x y).mp hltQ
      have heq : edgeTag q x = edgeTag q y := by
        simp [x, y, edgeTag, visitEdge, hdin, hc.1]
      have hparam : leftParameter q (E.symm d) < leftParameter q c := by
        rcases hparts with htag | ⟨htag, hp⟩
        · exact False.elim ((ne_of_lt htag) heq)
        · simpa [x, y, parameter, visitParameter] using hp
      exact not_lt_of_ge (hc.2 (E.symm d) hdin) hparam
    exact le_of_not_gt hnot

/-- The actual event-order neighborhood transports both the first-crossing witness
and a selected right-cut label, using only original Regular and vertex G1. -/
theorem eventually_firstCrossing_transport
    (hQ : Regular q) (hG1 : cyclicNoncollinear q)
    (c : Crossing q) (hc : Cursor.FirstCrossing q c)
    {a : ℕ} (hcut : c.val.2.val = a) :
    ∀ᶠ r in 𝓝 q, ∃ hR : Regular r, ∃ E : Crossing q ≃ Crossing r,
      (∀ d, (E d).val = d.val) ∧
      (∀ x y : Event q,
        ((eventOrder q hQ.noTriple).lt x y ↔
          (eventOrder r hR.noTriple).lt
            (eventMapEquiv q r E x) (eventMapEquiv q r E y))) ∧
      Cursor.FirstCrossing r (E c) ∧ (E c).val.2.val = a := by
  filter_upwards [eventually_configuration_event_order q hQ hG1] with r hchart
  rcases hchart with ⟨hR, E, hlabels, horder⟩
  refine ⟨hR, E, hlabels, horder, ?_, ?_⟩
  · exact firstCrossing_transport_of_event_order q r hQ hR E hlabels horder c hc
  · rw [hlabels c]
    exact hcut

end DirectGLSSW.ActiveArc.ConfigurationLocality



