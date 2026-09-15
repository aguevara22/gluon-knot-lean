import SM.ContactParameters
import SM.ContactPersistence

/-! The order of every pair of persistent visits stays fixed at a V wall.
The only excluded labels are the two explicit contact pairs. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

def ContactOrderAgrees (P Q : LabelledTuple n) (M a : ZMod n) : Prop :=
  ∀ i j k, IsCrossing P {i, j} → ¬ ContactAffected M a {i, j} →
    IsCrossing P {i, k} → ¬ ContactAffected M a {i, k} →
    (edgeParameter Q i j < edgeParameter Q i k ↔ edgeParameter P i j < edgeParameter P i k)

theorem contact_order_persists (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) (hz : pointZeroTriples P = {contactSupport M a})
    (hc : concurrenceTriples P = ∅) : ∀ᶠ Q in 𝓝 P, ContactOrderAgrees P Q M a := by
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  apply eventually_all.mpr
  intro k
  by_cases h : IsCrossing P {i, j} ∧ ¬ ContactAffected M a {i, j} ∧
      IsCrossing P {i, k} ∧ ¬ ContactAffected M a {i, k}
  · by_cases hjk : j = k
    · subst k
      exact Eventually.of_forall (fun _ _ _ _ _ => by simp)
    · exact (continuousAt_preserves_parameter_order
        (continuousAt_contact_edgeParameter hn hsep hz h.1 h.2.1)
        (continuousAt_contact_edgeParameter hn hsep hz h.2.2.1 h.2.2.2)
        (contact_unaffected_parameters_ne hn hsep hz hc hjk h.1 h.2.1 h.2.2.1 h.2.2.2)).mono
        (fun _ hQ _ _ _ _ => hQ)
  · exact Eventually.of_forall (fun _ hij hnij hik hnik => (h ⟨hij, hnij, hik, hnik⟩).elim)

namespace WallGerm

theorem vertexEdge_order_persists (hn : 3 ≤ n) (g : WallGerm n)
    {M a : ZMod n} (h : g.VertexEdgeAt M a) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter, |t.val| < δ →
      ContactOrderAgrees g.center (g.curve t) M a :=
  (g.eventually_center_iff_radius _).mp
    (g.continuous_curve.continuousAt.eventually (contact_order_persists hn h.1 h.2.1 h.2.2.1))

end WallGerm
end SM
