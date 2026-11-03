import CyclicCarrierDensity

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart Set UniversalCarrierDomain
open scoped BigOperators

/-- Finite four/six-label inventory for one literal cyclic list of carriers. -/
def cycleSecantExclusions {m n : ℕ} (f : Fin m → Fin n) (L : Fin n → CarrierLine) : Prop :=
  (∀ l : Fin 4 → Fin m, Function.Injective l → outerCycleNumerator L f l ≠ 0) ∧
  (∀ l : Fin 6 → Fin m, Function.Injective l → secantCycleNumerator L f l ≠ 0)

theorem cycleSecantExclusions_iff {m n : ℕ} (f : Fin m → Fin n)
    (L : Fin n → CarrierLine)
    (hd : ∀ i, lineDenominator (L (f ((cyclicSuccessorPerm m)⁻¹ i))) (L (f i)) ≠ 0) :
    cycleSecantExclusions f L ↔
      (∀ l : Fin 4 → Fin m, Function.Injective l →
        OriginalOuterProperness.outerNumerator ((reconstructPolygon (L ∘ f)) ∘ l) ≠ 0) ∧
      (∀ l : Fin 6 → Fin m, Function.Injective l →
        OriginalSecantProperness.secantNumerator ((reconstructPolygon (L ∘ f)) ∘ l) ≠ 0) := by
  have h4 (l : Fin 4 → Fin m) := outerCycleNumerator_eq L f l hd
  have h6 (l : Fin 6 → Fin m) := secantCycleNumerator_eq L f l hd
  unfold cycleSecantExclusions
  simp only [h4, h6, ne_eq, mul_eq_zero, pow_eq_zero_iff, OfNat.ofNat_ne_zero,
    not_false_eq_true, and_true, not_or]
  have hp {s : ℕ} (l : Fin s → Fin m) :
      (∏ i, lineDenominator (L (f ((cyclicSuccessorPerm m)⁻¹ (l i)))) (L (f (l i)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hd (l i))
  simp only [hp, not_false_eq_true, true_and]

theorem cycleSecantExclusions_dense_open {m n : ℕ} (q : Fin m → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (f : Fin m → Fin n) (hf : Function.Injective f) :
    Dense {L | cycleSecantExclusions f L} ∧ IsOpen {L | cycleSecantExclusions f L} := by
  classical
  let A := fun l : {l : Fin 4 → Fin m // Function.Injective l} =>
    {L : Fin n → CarrierLine | outerCycleNumerator L f l.val ≠ 0}
  let B := fun l : {l : Fin 6 → Fin m // Function.Injective l} =>
    {L : Fin n → CarrierLine | secantCycleNumerator L f l.val ≠ 0}
  have hA := CarrierFamilyDensity.finite_family_dense_open A
    (fun l => (outerCycle_dense_open q hq f hf l.val l.property).1)
    (fun l => (outerCycle_dense_open q hq f hf l.val l.property).2)
  have hB := CarrierFamilyDensity.finite_family_dense_open B
    (fun l => (secantCycle_dense_open q hq f hf l.val l.property).1)
    (fun l => (secantCycle_dense_open q hq f hf l.val l.property).2)
  have he : (⋂ l, A l) ∩ (⋂ l, B l) = {L | cycleSecantExclusions f L} := by
    ext L
    simp [A, B, cycleSecantExclusions]
  rw [← he]
  exact ⟨hA.1.inter_of_isOpen_left hB.1 hA.2, hA.2.inter hB.2⟩

/-- This is only the explicit cap-secant inventory, not the source auxiliary domain. -/
def daughterSecantExclusions {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (L : Fin n → CarrierLine) : Prop :=
  ∀ S : Finset (PolygonCrossing q),
    PolygonNonalternation.polygonNonalternating q hq.g2 S →
    ∀ root : PolygonEvent q,
      cycleSecantExclusions (DaughterFirstReturn.daughterCarrier q hq.g2 S root) L

/-- Actual nonalternating daughter cycles are injective; this is derived here,
not a premise on an arbitrary extraction. The auxiliary input supplies only a
witness of the daughter size and is discharged by the next theorem. -/
theorem daughterSecantExclusions_dense_open {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hAux : GeometricSmoothingWeights.auxiliaryGenericity q hq) :
    Dense {L | daughterSecantExclusions q hq L} ∧
    IsOpen {L | daughterSecantExclusions q hq L} := by
  classical
  let I := {S : Finset (PolygonCrossing q) //
    PolygonNonalternation.polygonNonalternating q hq.g2 S} × PolygonEvent q
  let A := fun x : I => {L : Fin n → CarrierLine |
    cycleSecantExclusions (DaughterFirstReturn.daughterCarrier q hq.g2 x.1.val x.2) L}
  have hx (x : I) : Dense (A x) ∧ IsOpen (A x) :=
    cycleSecantExclusions_dense_open
      (DaughterFirstReturn.daughterVertex q hq.g2 x.1.val x.2)
      (hAux x.1.val x.1.property x.2) _
      (DaughterFirstReturn.daughterCarrier_injective q hq.g2 x.1.val
        hq.size_ge_three x.1.property x.2)
  have hh := CarrierFamilyDensity.finite_family_dense_open A (fun x => (hx x).1) (fun x => (hx x).2)
  have he : (⋂ x, A x) = {L | daughterSecantExclusions q hq L} := by
    ext L
    simp only [Set.mem_iInter, Set.mem_setOf_eq, daughterSecantExclusions, A]
    constructor
    · intro h S hS root
      exact h (⟨S, hS⟩, root)
    · intro h x
      exact h x.1.val x.1.property x.2
  rwa [he] at hh

/-- All actual daughter cap exclusions and the universal open-event/far
exclusions are jointly proper on the SAME original carrier-coordinate space. -/
theorem joint_daughter_universal_dense_open {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hAux : GeometricSmoothingWeights.auxiliaryGenericity q hq) :
    Dense {L : Fin n → CarrierLine |
      daughterSecantExclusions q hq L ∧ UniversalLocus L ∧ PairTransverse L} ∧
    IsOpen {L : Fin n → CarrierLine |
      daughterSecantExclusions q hq L ∧ UniversalLocus L ∧ PairTransverse L} := by
  have hD := daughterSecantExclusions_dense_open q hq hAux
  have hU := universal_transverse_dense_open (α := Fin n)
  exact ⟨hD.1.inter_of_isOpen_left hU.1 hD.2, hD.2.inter hU.2⟩

/-- No auxiliary-domain input: every generic neighborhood first supplies an
actual parent whose complete finite daughter-cycle inventory is jointly proper.
This does NOT assert the final source inventory or cap realization. -/
theorem exists_parent_with_joint_proper_inventory {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (U : Set (Fin n → PlanarPoint ℝ)) (hU : U ∈ nhds q) :
    ∃ r ∈ U, ∃ hr : CyclicGeneric r,
      GeometricSmoothingWeights.auxiliaryGenericity r hr ∧
      Dense {L : Fin n → CarrierLine |
        daughterSecantExclusions r hr L ∧ UniversalLocus L ∧ PairTransverse L} ∧
      IsOpen {L : Fin n → CarrierLine |
        daughterSecantExclusions r hr L ∧ UniversalLocus L ∧ PairTransverse L} := by
  obtain ⟨r, hrU, hr, hAux, _⟩ := ActualAuxiliaryDensity.exists_auxiliaryGenericity_mem_nhds q hq U hU
  exact ⟨r, hrU, hr, hAux, joint_daughter_universal_dense_open r hr hAux⟩

end DirectGLSSW.CyclicCarrierClearing






