import ActiveArcEventOrderAssembly
import ActiveArcConfigurationPairs
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ConfigurationLocality
open DirectGLSSW ActiveArc Filter Topology
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)

/-- Actual physical crossing labels and the complete open-arc event order are
locally unchanged on the genuine source vertex-G1 and Regular domain. -/
theorem eventually_configuration_event_order (hR : Regular q) (hG1 : cyclicNoncollinear q) :
    ∀ᶠ r in 𝓝 q, ∃ hr : Regular r, ∃ E : Crossing q ≃ Crossing r,
      (∀ c, (E c).val=c.val) ∧ ∀ x y : Event q,
        ((eventOrder q hR.noTriple).lt x y ↔
         (eventOrder r hr.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y)) := by
  classical
  apply eventually_event_order_of_pair_neighborhood q hR hG1
  apply Filter.eventually_all.mpr
  intro e
  apply Filter.eventually_all.mpr
  intro f
  by_cases hef : e=f
  · exact Eventually.of_forall (fun _ h => False.elim (h hef))
  · exact (eventually_crossing_iff q hR hG1 e f hef).mono (fun _ h _ => h)

/-- The actual event-order chart pulls back along any continuous configuration family. -/
theorem eventually_configuration_event_order_of_continuousAt
    {α : Type*} [TopologicalSpace α] {z : α}
    (Q : α → Fin (n+2) → PlanarPoint ℝ) (hQ : ContinuousAt Q z)
    (hR : Regular (Q z)) (hG1 : cyclicNoncollinear (Q z)) :
    ∀ᶠ t in 𝓝 z, ∃ ht : Regular (Q t), ∃ E : Crossing (Q z) ≃ Crossing (Q t),
      (∀ c, (E c).val=c.val) ∧ ∀ x y : Event (Q z),
        ((eventOrder (Q z) hR.noTriple).lt x y ↔
         (eventOrder (Q t) ht.noTriple).lt
           (eventMapEquiv (Q z) (Q t) E x) (eventMapEquiv (Q z) (Q t) E y)) :=
  hQ.eventually (eventually_configuration_event_order (Q z) hR hG1)

end DirectGLSSW.ActiveArc.ConfigurationLocality
