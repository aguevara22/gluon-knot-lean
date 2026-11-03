import CyclicCarrierCharacterizations

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain Set

/-- Explicit finite stronger inventory. Eligibility requires an actual generic
polygon of the cycle size; no such witness is invented for inadmissible sizes. -/
def allCycleSecantExclusions {N : ℕ} (L : Fin N → CarrierLine) : Prop :=
  ∀ m : ℕ, m ≤ N → ∀ f : Fin m → Fin N, Function.Injective f →
    (∃ q : Fin m → PlanarPoint ℝ, CyclicGeneric q) → cycleSecantExclusions f L

theorem allCycleSecantExclusions_iff {N : ℕ} (L : Fin N → CarrierLine) :
    allCycleSecantExclusions L ↔
      ∀ m : ℕ, m ≤ N → ∀ f : Fin m → Fin N, Function.Injective f →
        (∃ q : Fin m → PlanarPoint ℝ, CyclicGeneric q) → cycleSecantExclusions f L := Iff.rfl

theorem allCycleSecantExclusions_dense_open (N : ℕ) :
    Dense {L : Fin N → CarrierLine | allCycleSecantExclusions L} ∧
    IsOpen {L : Fin N → CarrierLine | allCycleSecantExclusions L} := by
  classical
  let I := Σ m : Fin (N+1), {f : Fin m.val → Fin N //
    Function.Injective f ∧ ∃ q : Fin m.val → PlanarPoint ℝ, CyclicGeneric q}
  let A := fun x : I => {L : Fin N → CarrierLine | cycleSecantExclusions x.2.val L}
  have hx (x : I) : Dense (A x) ∧ IsOpen (A x) := by
    obtain ⟨q,hq⟩ := x.2.property.2
    exact cycleSecantExclusions_dense_open q hq x.2.val x.2.property.1
  have hh := CarrierFamilyDensity.finite_family_dense_open A (fun x => (hx x).1) (fun x => (hx x).2)
  have he : (⋂ x, A x) = {L : Fin N → CarrierLine | allCycleSecantExclusions L} := by
    ext L
    simp only [Set.mem_iInter, Set.mem_setOf_eq, A, allCycleSecantExclusions]
    constructor
    · intro h m hm f hf hq
      exact h ⟨⟨m,by omega⟩,⟨f,hf,hq⟩⟩
    · intro h x
      exact h x.1.val (by have := x.1.isLt; omega) x.2.val x.2.property.1 x.2.property.2
  rwa [he] at hh

/-- An actual generic polygon and injective carrier list discharge both finite
index eligibility and the size bound. -/
theorem allCycleSecantExclusions_apply {m N : ℕ} (L : Fin N → CarrierLine)
    (hL : allCycleSecantExclusions L) (q : Fin m → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (f : Fin m → Fin N) (hf : Function.Injective f) : cycleSecantExclusions f L := by
  have hm : m ≤ N := by simpa using Fintype.card_le_of_injective f hf
  exact hL m hm f hf ⟨q,hq⟩

theorem universal_all_cycles_dense_open (N : ℕ) :
    Dense {L : Fin N → CarrierLine | UniversalLocus L ∧ PairTransverse L ∧ allCycleSecantExclusions L} ∧
    IsOpen {L : Fin N → CarrierLine | UniversalLocus L ∧ PairTransverse L ∧ allCycleSecantExclusions L} := by
  have hU := universal_transverse_dense_open (α := Fin N)
  have hC := allCycleSecantExclusions_dense_open N
  have he : {L : Fin N → CarrierLine | UniversalLocus L ∧ PairTransverse L} ∩
      {L | allCycleSecantExclusions L} =
      {L | UniversalLocus L ∧ PairTransverse L ∧ allCycleSecantExclusions L} := by
    ext L
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]
  rw [← he]
  exact ⟨hU.1.inter_of_isOpen_left hC.1 hU.2, hU.2.inter hC.2⟩

end DirectGLSSW.CyclicCarrierClearing




