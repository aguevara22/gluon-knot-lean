import SM.InterlaceSupports

/-! Full def:interlace, including the equivalence of the two source
formulations, the actual graph, every independent support (including empty),
N and U on arbitrary supports, and transport under cyclic relabelling. -/

namespace SM

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem interlacement_definition (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) :
    (∀ x y : Crossing P, Interlaces hn hP x y ↔
      x ≠ y ∧ ∃ x₀ x₁ : {i // i ∈ x.val}, ∃ y₀ y₁ : {i // i ∈ y.val},
        x₀ ≠ x₁ ∧ y₀ ≠ y₁ ∧
        crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ ∧
        crossingVisitBetween hn hP.1 x x₁ x₀ y y₁) ∧
    (∀ x y : Crossing P, ∀ x₀ x₁ : {i // i ∈ x.val}, x₀ ≠ x₁ →
      (Interlaces hn hP x y ↔ x ≠ y ∧
        (crossingVisitsOnArc hn hP.1 x x₀ x₁ y).card = 1)) ∧
    (∀ x y : Crossing P, Interlaces hn hP x y ↔ Interlaces hn hP y x) ∧
    (∀ x : Crossing P, ¬ Interlaces hn hP x x) ∧
    (∀ x y : Crossing P, (interlacementGraph hn hP).Adj x y ↔ Interlaces hn hP x y) ∧
    (∀ S : Finset (Crossing P), S ∈ independentSupports hn hP ↔
      (interlacementGraph hn hP).IsIndepSet S) ∧
    ∅ ∈ independentSupports hn hP ∧
    (∀ S : Finset (Crossing P), ∀ y : Crossing P,
      y ∈ supportNeighbors hn hP S ↔ ∃ x ∈ S, Interlaces hn hP y x) ∧
    (∀ S : Finset (Crossing P), ∀ y : Crossing P,
      y ∈ supportUnselected hn hP S ↔ y ∉ S ∧ y ∉ supportNeighbors hn hP S) ∧
    (∀ a : ZMod n, ∀ x y : Crossing P,
      Interlaces hn ((generic_shift a P).mpr hP)
        (crossingShiftEquiv a P x) (crossingShiftEquiv a P y) ↔ Interlaces hn hP x y) ∧
    (∀ a : ZMod n, ∀ S : Finset (Crossing P),
      crossingSupportShift a S ∈ independentSupports hn ((generic_shift a P).mpr hP) ↔
        S ∈ independentSupports hn hP) ∧
    (∀ a : ZMod n, ∀ S : Finset (Crossing P),
      supportNeighbors hn ((generic_shift a P).mpr hP) (crossingSupportShift a S) =
        crossingSupportShift a (supportNeighbors hn hP S)) ∧
    (∀ a : ZMod n, ∀ S : Finset (Crossing P),
      supportUnselected hn ((generic_shift a P).mpr hP) (crossingSupportShift a S) =
        crossingSupportShift a (supportUnselected hn hP S)) := by
  exact ⟨fun _ _ => Iff.rfl, interlaces_iff_count hn hP, interlaces_comm hn hP,
    interlaces_irrefl hn hP, interlacementGraph_adj hn hP,
    mem_independentSupports hn hP, empty_mem_independentSupports hn hP,
    mem_supportNeighbors hn hP, mem_supportUnselected hn hP,
    interlaces_shift hn hP, independentSupports_shift hn hP,
    supportNeighbors_shift hn hP, supportUnselected_shift hn hP⟩

end SM
