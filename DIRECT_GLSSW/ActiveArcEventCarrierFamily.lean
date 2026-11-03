import ActiveArcEventTripleProperness
import CarrierFamilyDensity

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW Cursor RetainedWords Primitive AuxiliaryCarrierChart
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q) (c : Crossing q)

/-- Simultaneous numerator nonvanishing for every actual unselected support
and every sorted triple except the actual crossed-carrier adjacent event. -/
def eventCarrierLocus (L : Fin (n+1) ⊕ Unit → CarrierLine) : Prop :=
  ∀ U : Support q hR, c∉U.val → ∀ i j k : Fin (openCount q hR U.val),
    i.val < j.val → j.val < k.val →
    (i.val≠0 ∨ k.val≠j.val+1 ∨ eventCarrierChain q hR U j≠Sum.inl c.val.2) →
    eventTripleNumerator q hR c U i j k L≠0

private abbrev EventIndex :=
  Σ U : Support q hR,
    {t : Fin (openCount q hR U.val) × Fin (openCount q hR U.val) × Fin (openCount q hR U.val) //
      c∉U.val ∧ t.1.val < t.2.1.val ∧ t.2.1.val < t.2.2.val ∧
        (t.1.val≠0 ∨ t.2.2.val≠t.2.1.val+1 ∨ eventCarrierChain q hR U t.2.1≠Sum.inl c.val.2)}

/-- The finite actual event-label family has a simultaneous dense open locus
in independent carrier coordinates. Every polynomial witness is produced. -/
theorem event_carrier_family_dense_open (hc : FirstCrossing q c) :
    Dense {L | eventCarrierLocus q hR c L} ∧ IsOpen {L | eventCarrierLocus q hR c L} := by
  classical
  letI : Fintype (EventIndex q hR c) := by unfold EventIndex;infer_instance
  let A : EventIndex q hR c → Set (Fin (n+1) ⊕ Unit → CarrierLine) := fun x =>
    {L | eventTripleNumerator q hR c x.1 x.2.val.1 x.2.val.2.1 x.2.val.2.2 L≠0}
  have hD : ∀ x, Dense (A x) := by
    intro x
    exact eventTripleNumerator_nonzero_dense q hR c x.1 hc x.2.property.1 _ _ _
      x.2.property.2.1 x.2.property.2.2.1 x.2.property.2.2.2
  have hO : ∀ x, IsOpen (A x) := by
    intro x
    exact CarrierDensity.isOpen_assignmentNumerator_ne_zero _ _ _ _ _ _
  have hJoint := CarrierFamilyDensity.finite_family_dense_open A hD hO
  have heq : (⋂ x,A x)={L | eventCarrierLocus q hR c L} := by
    ext L
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    constructor
    · intro h U hu i j k hij hjk hexc
      exact h ⟨U,⟨(i,j,k),hu,hij,hjk,hexc⟩⟩
    · intro h x
      exact h x.1 x.2.property.1 _ _ _ x.2.property.2.1 x.2.property.2.2.1 x.2.property.2.2.2
  rw [heq] at hJoint
  exact hJoint

/-- On actual source geometry the simultaneous numerator locus supplies the
literal finite event-word auxiliary domain, with the identical exception. -/
theorem event_carrier_locus_actual (hc : FirstCrossing q c) (hG1 : cyclicNoncollinear q)
    (hL : eventCarrierLocus q hR c (parentChartLines (a:=n) (b:=0) q)) :
    ∀ U : Support q hR, c∉U.val → EventCarrierNonvanishing q hR c U := by
  intro U hu i j k hij hjk hkN hexc
  have hiN : i<openCount q hR U.val := by omega
  have hjN : j<openCount q hR U.val := by omega
  have hkN' : k<openCount q hR U.val := by omega
  have hjSide : j<openCount q hR U.val-1 := by omega
  have hexc' : i≠0 ∨ k≠j+1 ∨ eventCarrierChain q hR U ⟨j,hjN⟩≠Sum.inl c.val.2 := by
    rcases hexc with hh|hh|hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
    · right;right
      intro he
      apply hh
      simpa only [eventCarrierChain,dif_pos hjSide,Sum.inl.injEq] using he
  have hn := hL U hu ⟨i,hiN⟩ ⟨j,hjN⟩ ⟨k,hkN'⟩ hij hjk hexc'
  intro hz
  exact hn ((eventTripleNumerator_zero_iff q hR c U hc hG1 _ _ _).mpr hz)

end DirectGLSSW.ActiveArc.OpenCarrier
