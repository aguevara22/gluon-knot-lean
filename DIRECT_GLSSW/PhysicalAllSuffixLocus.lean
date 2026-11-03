import PhysicalDropCarrierProjection
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc Cursor RetainedWords Primitive Split AuxiliaryCarrierChart Filter Topology
attribute [local instance] Classical.propDecidable

/-- All actual suffix/cut size decompositions, including drop zero and empty
first-edge crossing cases. The only field is an exact finite size equality. -/
abbrev SuffixShape (N : ℕ) :=
  {t : Fin (N+1) × Fin (N+1) × Fin (N+1) // N=t.1.val+(t.2.1.val+t.2.2.val)}

abbrev suffixWord {N : ℕ} (q : Fin (N+2) → PlanarPoint ℝ) (t : SuffixShape N) :=
  dropWord q t.property
abbrev suffixRegular {N : ℕ} (q : Fin (N+2) → PlanarPoint ℝ) (hQ : Regular q)
    (t : SuffixShape N) := dropWord_regular q t.property hQ

/-- Finite actual first crossings on the literal suffixes, with their exact
cut labels. No event or correspondence is assumed to exist. -/
abbrev SuffixEventIndex {N : ℕ} (q : Fin (N+2) → PlanarPoint ℝ) :=
  Σ t : SuffixShape N, {d : Crossing (suffixWord q t) //
    FirstCrossing (suffixWord q t) d ∧ d.val.2.val=t.val.2.1.val}

def allSuffixCarrierLocus {N : ℕ} (q : Fin (N+2) → PlanarPoint ℝ) (hQ : Regular q)
    (L : Fin (N+1) ⊕ Unit → CarrierLine) : Prop :=
  ∀ i : SuffixEventIndex q,
    eventCarrierLocus (suffixWord q i.1) (suffixRegular q hQ i.1) i.2.val
      (dropCarriers i.1.property L) ∧
    parentFarLocus (suffixWord q i.1) (suffixRegular q hQ i.1) i.2.val i.2.property.2
      (dropCarriers i.1.property L)

/-- All finitely many ACTUAL suffix first-event/cap numerator conditions share
one dense open locus in the ORIGINAL physical carrier coordinates. -/
theorem allSuffixCarrierLocus_dense_open {N : ℕ}
    (q : Fin (N+2) → PlanarPoint ℝ) (hQ : Regular q) :
    Dense {L | allSuffixCarrierLocus q hQ L} ∧ IsOpen {L | allSuffixCarrierLocus q hQ L} := by
  letI : Fintype (SuffixEventIndex q) := inferInstance
  let A := fun i : SuffixEventIndex q => {L : Fin (N+1) ⊕ Unit → CarrierLine |
    eventCarrierLocus (suffixWord q i.1) (suffixRegular q hQ i.1) i.2.val
      (dropCarriers i.1.property L) ∧
    parentFarLocus (suffixWord q i.1) (suffixRegular q hQ i.1) i.2.val i.2.property.2
      (dropCarriers i.1.property L)}
  have hD : ∀ i, Dense (A i) := by
    intro i
    have hh := event_parent_carrier_dense_open (suffixWord q i.1) (suffixRegular q hQ i.1)
      i.2.val i.2.property.1 i.2.property.2
    exact hh.1.preimage (dropCarriers_isOpenMap i.1.property)
  have hO : ∀ i, IsOpen (A i) := by
    intro i
    have hh := event_parent_carrier_dense_open (suffixWord q i.1) (suffixRegular q hQ i.1)
      i.2.val i.2.property.1 i.2.property.2
    exact hh.2.preimage (dropCarriers_continuous i.1.property)
  have hAll := CarrierFamilyDensity.finite_family_dense_open A hD hO
  have heq : (⋂ i, A i)={L | allSuffixCarrierLocus q hQ L} := by
    ext L
    simp only [Set.mem_iInter,Set.mem_setOf_eq,allSuffixCarrierLocus,A]
  simpa only [heq] using hAll
end DirectGLSSW.ActiveArc.OpenCarrier
