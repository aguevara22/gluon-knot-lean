import SM.ContactWindowGap
import SM.ContactPersistence

/-! A simultaneous contact window: all changing-pair parameters are within
eta of their actual contact values, while every other nearby crossing visit
on those edges is more than three eta away. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {M a : ZMod n}

def ContactParameterWindows (P Q : LabelledTuple n) (M a : ZMod n) (r η : ℝ) : Prop :=
  (∀ s : Finset (ZMod n), ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)) ∧
  (∀ slot : Option Bool, ∀ j : ZMod n,
    IsCrossing Q {contactWindowEdge M a slot, j} →
    ¬ ContactAffected M a {contactWindowEdge M a slot, j} →
    3 * η < |edgeParameter Q (contactWindowEdge M a slot) j - contactWindowCenter r slot|) ∧
  ∀ forward : Bool,
    |edgeParameter Q a (contactLeg forward M) - r| < η ∧
    |edgeParameter Q (contactLeg forward M) a - contactEndpoint forward| < η

theorem contact_persistent_parameters_approach (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ Q in 𝓝 P, ∀ i j : ZMod n, IsCrossing P {i, j} →
      ¬ ContactAffected M a {i, j} → |edgeParameter Q i j - edgeParameter P i j| < η := by
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  by_cases h : IsCrossing P {i, j} ∧ ¬ ContactAffected M a {i, j}
  · exact (continuousAt_approach_value
      (continuousAt_contact_edgeParameter hn hsep hz h.1 h.2) rfl hη).mono
      (fun _ hQ _ _ => hQ)
  · exact Eventually.of_forall (fun _ hc hnc => (h ⟨hc, hnc⟩).elim)

theorem contact_parameter_windows (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hr : P M = edgePoint P a r) :
    ∃ η : ℝ, 0 < η ∧ 4 * η < r ∧ 4 * η < 1 - r ∧
      ∀ᶠ Q in 𝓝 P, ContactParameterWindows P Q M a r η := by
  obtain ⟨η, hη, hηr, hηr1, hgap⟩ := contact_window_gap hn hsep hz r hr0 hr1 hr
  refine ⟨η, hη, hηr, hηr1, ?_⟩
  filter_upwards [contact_unaffected_supports_persist hn hsep hz,
    contact_persistent_parameters_approach hn hsep hz hη,
    contact_parameters_approach hn hsep hz hm r hr hη] with Q hs hmoves ha
  refine ⟨hs, ?_, ha⟩
  intro slot j hc hnc
  have hc0 := (hs _ hnc).mp hc
  have hg := hgap slot j hc0 hnc
  have hmove := hmoves _ j hc0 hnc
  have htri := abs_sub_le (edgeParameter P (contactWindowEdge M a slot) j)
    (edgeParameter Q (contactWindowEdge M a slot) j) (contactWindowCenter r slot)
  rw [abs_sub_comm (edgeParameter P (contactWindowEdge M a slot) j)
    (edgeParameter Q (contactWindowEdge M a slot) j)] at htri
  linarith

namespace WallGerm

theorem vertexEdge_parameter_windows (hn : 3 ≤ n) (g : WallGerm n)
    {M a : ZMod n} (h : g.VertexEdgeAt M a) :
    ∃ r η : ℝ, 0 < r ∧ r < 1 ∧ g.center M = edgePoint g.center a r ∧
      0 < η ∧ 4 * η < r ∧ 4 * η < 1 - r ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter, |t.val| < δ →
        ContactParameterWindows g.center (g.curve t) M a r η := by
  obtain ⟨r, hr0, hr1, hr⟩ := h.2.2.2.1
  obtain ⟨η, hη, hηr, hηr1, hnear⟩ := contact_parameter_windows hn h.1 h.2.1
    h.2.2.2.1 r hr0 hr1 hr
  exact ⟨r, η, hr0, hr1, hr, hη, hηr, hηr1,
    (g.eventually_center_iff_radius _).mp (g.continuous_curve.continuousAt.eventually hnear)⟩

end WallGerm
end SM
