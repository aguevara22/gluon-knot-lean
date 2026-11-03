import CarrierDensity
import Mathlib.Topology.Basic
import Mathlib.Order.CompleteLattice.Finset

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.CarrierFamilyDensity

open DirectGLSSW.AuxiliaryCarrierChart
open DirectGLSSW.CarrierWitnessEvaluation
open DirectGLSSW.CarrierDensity
open Set

theorem finite_family_dense_open
    {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (A : ι → Set X) (hD : ∀ i, Dense (A i)) (hO : ∀ i, IsOpen (A i)) :
    Dense (⋂ i, A i) ∧ IsOpen (⋂ i, A i) := by
  classical
  have hFin : ∀ s : Finset ι, Dense (⋂ i ∈ s, A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using (dense_univ : Dense (Set.univ : Set X))
    | @insert i s hi ih =>
        rw [Finset.set_biInter_insert]
        exact (hD i).inter_of_isOpen_left ih (hO i)
  have hDense : Dense (⋂ i : ι, A i) := by
    simpa using hFin (Finset.univ : Finset ι)
  exact ⟨hDense, isOpen_iInter_of_finite hO⟩

abbrev DaughterFamilyIndex {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q)) :=
  Σ r : {root : PolygonEvent q // DaughterFirstReturn.retainedCorner q S root},
    {t : (Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S r.1)) ×
        Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S r.1))) ×
        Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S r.1)) //
      t.1.1 ≠ t.1.2 ∧ t.1.2 ≠ t.2 ∧ t.1.1 ≠ t.2}

noncomputable def indexedDaughterNumerator {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (u : DaughterFamilyIndex q hG2 S) (L : Fin n → CarrierLine) : ℝ :=
  let root := u.1.1
  let t := u.2.1
  let m := Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)
  let prev : Fin m → Fin m := fun v => (cyclicSuccessorPerm m)⁻¹ v
  let car : Fin m → Fin n := DaughterFirstReturn.daughterCarrier q hG2 S root
  assignmentNumerator (car (prev t.1.1)) (car t.1.1)
    (car (prev t.1.2)) (car t.1.2) (car (prev t.2)) (car t.2) L

def allDaughterFamilyNumeratorsNonzero {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (L : Fin n → CarrierLine) : Prop :=
  ∀ root : PolygonEvent q,
    ∀ hroot : DaughterFirstReturn.retainedCorner q S root,
      ∀ i j k : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)),
        i ≠ j → j ≠ k → i ≠ k →
          let m := Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)
          let prev : Fin m → Fin m := fun v => (cyclicSuccessorPerm m)⁻¹ v
          let car : Fin m → Fin n := DaughterFirstReturn.daughterCarrier q hG2 S root
          assignmentNumerator (car (prev i)) (car i) (car (prev j)) (car j)
            (car (prev k)) (car k) L ≠ 0

theorem daughter_family_numerator_locus_dense_open
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hG2 : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (hn : 3 ≤ n) (hG1 : cyclicNoncollinear q)
    (hNA : PolygonNonalternation.polygonNonalternating q hG2 S) :
    Dense {L : Fin n → CarrierLine | allDaughterFamilyNumeratorsNonzero q hG2 S L} ∧
      IsOpen {L : Fin n → CarrierLine | allDaughterFamilyNumeratorsNonzero q hG2 S L} := by
  classical
  letI : Fintype (DaughterFamilyIndex q hG2 S) := by
    unfold DaughterFamilyIndex
    infer_instance
  let A : DaughterFamilyIndex q hG2 S → Set (Fin n → CarrierLine) :=
    fun u => {L | indexedDaughterNumerator q hG2 S u L ≠ 0}
  have hD : ∀ u, Dense (A u) := by
    intro u
    rcases u with ⟨⟨root, hroot⟩, ⟨⟨⟨i, j⟩, k⟩, hijk⟩⟩
    simpa [A, indexedDaughterNumerator] using
      daughter_triple_numerator_dense q hG2 S hn hG1 hNA root hroot i j k
        hijk.1 hijk.2.1 hijk.2.2
  have hO : ∀ u, IsOpen (A u) := by
    intro u
    rcases u with ⟨⟨root, _hroot⟩, ⟨⟨⟨i, j⟩, k⟩, _hijk⟩⟩
    simpa [A, indexedDaughterNumerator] using
      (isOpen_assignmentNumerator_ne_zero
        (DaughterFirstReturn.daughterCarrier q hG2 S root
          ((cyclicSuccessorPerm (Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)))⁻¹ i))
        (DaughterFirstReturn.daughterCarrier q hG2 S root i)
        (DaughterFirstReturn.daughterCarrier q hG2 S root
          ((cyclicSuccessorPerm (Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)))⁻¹ j))
        (DaughterFirstReturn.daughterCarrier q hG2 S root j)
        (DaughterFirstReturn.daughterCarrier q hG2 S root
          ((cyclicSuccessorPerm (Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)))⁻¹ k))
        (DaughterFirstReturn.daughterCarrier q hG2 S root k))
  have hJoint := finite_family_dense_open A hD hO
  have hSet : (⋂ u, A u) =
      {L : Fin n → CarrierLine | allDaughterFamilyNumeratorsNonzero q hG2 S L} := by
    ext L
    simp only [Set.mem_iInter, A, Set.mem_setOf_eq, allDaughterFamilyNumeratorsNonzero]
    constructor
    · intro h root hroot i j k hij hjk hik
      let u : DaughterFamilyIndex q hG2 S :=
        ⟨⟨root, hroot⟩, ⟨⟨⟨i, j⟩, k⟩, ⟨hij, hjk, hik⟩⟩⟩
      simpa [indexedDaughterNumerator, u] using h u
    · intro h u
      rcases u with ⟨⟨root, hroot⟩, ⟨⟨⟨i, j⟩, k⟩, hijk⟩⟩
      exact h root hroot i j k hijk.1 hijk.2.1 hijk.2.2
  rw [← hSet]
  exact hJoint

def allNonalternatingSupportDaughterNumeratorsNonzero {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hG2 : cyclicNoTripleIntersections q)
    (L : Fin n → CarrierLine) : Prop :=
  ∀ S : Finset (PolygonCrossing q),
    PolygonNonalternation.polygonNonalternating q hG2 S →
      allDaughterFamilyNumeratorsNonzero q hG2 S L

theorem all_nonalternating_support_daughter_numerator_locus_dense_open
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hG2 : cyclicNoTripleIntersections q)
    (hn : 3 ≤ n) (hG1 : cyclicNoncollinear q) :
    Dense {L : Fin n → CarrierLine |
      allNonalternatingSupportDaughterNumeratorsNonzero q hG2 L} ∧
    IsOpen {L : Fin n → CarrierLine |
      allNonalternatingSupportDaughterNumeratorsNonzero q hG2 L} := by
  classical
  let ι := {S : Finset (PolygonCrossing q) //
    PolygonNonalternation.polygonNonalternating q hG2 S}
  letI : Fintype ι := by
    dsimp [ι]
    infer_instance
  let A : ι → Set (Fin n → CarrierLine) := fun s =>
    {L | allDaughterFamilyNumeratorsNonzero q hG2 s.1 L}
  have hD : ∀ s, Dense (A s) := by
    intro s
    exact (daughter_family_numerator_locus_dense_open q hG2 s.1 hn hG1 s.2).1
  have hO : ∀ s, IsOpen (A s) := by
    intro s
    exact (daughter_family_numerator_locus_dense_open q hG2 s.1 hn hG1 s.2).2
  have hJoint := finite_family_dense_open A hD hO
  have hSet : (⋂ s, A s) =
      {L : Fin n → CarrierLine |
        allNonalternatingSupportDaughterNumeratorsNonzero q hG2 L} := by
    ext L
    simp only [Set.mem_iInter, A, Set.mem_setOf_eq,
      allNonalternatingSupportDaughterNumeratorsNonzero]
    constructor
    · intro h S hNA
      exact h ⟨S, hNA⟩
    · intro h s
      exact h s.1 s.2
  rw [← hSet]
  exact hJoint

end DirectGLSSW.CarrierFamilyDensity




