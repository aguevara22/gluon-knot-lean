import SM.InterlaceRelabel
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! The actual interlacement graph and its finite supports, neighbours and
unselected non-neighbours. All supports, including the empty set, are allowed
as inputs to N and U; independence is imposed only on Ind(G). -/

namespace SM

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {P : LabelledTuple n}

def interlacementGraph (hn : 3 ≤ n) (hP : Generic P) : SimpleGraph (Crossing P) where
  Adj := Interlaces hn hP
  symm := ⟨fun _ _ h => interlaces_symm hn hP h⟩
  loopless := ⟨interlaces_irrefl hn hP⟩

theorem interlacementGraph_adj (hn : 3 ≤ n) (hP : Generic P) (x y : Crossing P) :
    (interlacementGraph hn hP).Adj x y ↔ Interlaces hn hP x y := Iff.rfl

def interlacementGraphShiftIso (hn : 3 ≤ n) (hP : Generic P) (a : ZMod n) :
    interlacementGraph hn hP ≃g interlacementGraph hn ((generic_shift a P).mpr hP) where
  toEquiv := crossingShiftEquiv a P
  map_rel_iff' := interlaces_shift hn hP a _ _

noncomputable def independentSupports (hn : 3 ≤ n) (hP : Generic P) :
    Finset (Finset (Crossing P)) := by
  haveI : NeZero n := ⟨by omega⟩
  exact Finset.univ.powerset.filter fun S => (interlacementGraph hn hP).IsIndepSet S

theorem mem_independentSupports (hn : 3 ≤ n) (hP : Generic P)
    (S : Finset (Crossing P)) : S ∈ independentSupports hn hP ↔
      (interlacementGraph hn hP).IsIndepSet S := by
  haveI : NeZero n := ⟨by omega⟩
  simp only [independentSupports, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_univ, true_and]

theorem mem_independentSupports_iff (hn : 3 ≤ n) (hP : Generic P)
    (S : Finset (Crossing P)) : S ∈ independentSupports hn hP ↔
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ Interlaces hn hP x y := by
  exact mem_independentSupports hn hP S

theorem empty_mem_independentSupports (hn : 3 ≤ n) (hP : Generic P) :
    ∅ ∈ independentSupports hn hP := by
  rw [mem_independentSupports_iff]
  simp

noncomputable def supportNeighbors (hn : 3 ≤ n) (hP : Generic P)
    (S : Finset (Crossing P)) : Finset (Crossing P) := by
  haveI : NeZero n := ⟨by omega⟩
  exact Finset.univ.filter fun y => ∃ x ∈ S, Interlaces hn hP y x

theorem mem_supportNeighbors (hn : 3 ≤ n) (hP : Generic P)
    (S : Finset (Crossing P)) (y : Crossing P) :
    y ∈ supportNeighbors hn hP S ↔ ∃ x ∈ S, Interlaces hn hP y x := by
  haveI : NeZero n := ⟨by omega⟩
  simp only [supportNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def supportUnselected (hn : 3 ≤ n) (hP : Generic P)
    (S : Finset (Crossing P)) : Finset (Crossing P) := by
  haveI : NeZero n := ⟨by omega⟩
  exact Finset.univ \ (S ∪ supportNeighbors hn hP S)

theorem supportUnselected_eq [NeZero n] (hn : 3 ≤ n) (hP : Generic P)
    (S : Finset (Crossing P)) : supportUnselected hn hP S =
      Finset.univ \ (S ∪ supportNeighbors hn hP S) := rfl

theorem mem_supportUnselected (hn : 3 ≤ n) (hP : Generic P)
    (S : Finset (Crossing P)) (y : Crossing P) :
    y ∈ supportUnselected hn hP S ↔ y ∉ S ∧ y ∉ supportNeighbors hn hP S := by
  haveI : NeZero n := ⟨by omega⟩
  simp only [supportUnselected, Finset.mem_sdiff, Finset.mem_univ,
    Finset.mem_union, not_or, true_and]

noncomputable def crossingSupportShift (a : ZMod n) (S : Finset (Crossing P)) :
    Finset (Crossing (shift a P)) := S.map (crossingShiftEquiv a P).toEmbedding

theorem mem_crossingSupportShift (a : ZMod n) (S : Finset (Crossing P))
    (x : Crossing P) : crossingShiftEquiv a P x ∈ crossingSupportShift a S ↔ x ∈ S := by
  simp only [crossingSupportShift, Finset.mem_map_equiv, Equiv.symm_apply_apply]

theorem independentSupports_shift (hn : 3 ≤ n) (hP : Generic P) (a : ZMod n)
    (S : Finset (Crossing P)) :
    crossingSupportShift a S ∈ independentSupports hn ((generic_shift a P).mpr hP) ↔
      S ∈ independentSupports hn hP := by
  rw [mem_independentSupports_iff, mem_independentSupports_iff]
  constructor
  · intro h x hx y hy hxy hI
    exact h _ ((mem_crossingSupportShift a S x).mpr hx)
      _ ((mem_crossingSupportShift a S y).mpr hy)
      (fun he => hxy ((crossingShiftEquiv a P).injective he))
      ((interlaces_shift hn hP a x y).mpr hI)
  · intro h x hx y hy hxy hI
    obtain ⟨x₀, rfl⟩ := (crossingShiftEquiv a P).surjective x
    obtain ⟨y₀, rfl⟩ := (crossingShiftEquiv a P).surjective y
    exact h x₀ ((mem_crossingSupportShift a S x₀).mp hx)
      y₀ ((mem_crossingSupportShift a S y₀).mp hy)
      (fun he => hxy (congrArg (crossingShiftEquiv a P) he))
      ((interlaces_shift hn hP a x₀ y₀).mp hI)

theorem supportNeighbors_shift_mem (hn : 3 ≤ n) (hP : Generic P) (a : ZMod n)
    (S : Finset (Crossing P)) (y : Crossing P) :
    crossingShiftEquiv a P y ∈ supportNeighbors hn ((generic_shift a P).mpr hP)
      (crossingSupportShift a S) ↔ y ∈ supportNeighbors hn hP S := by
  rw [mem_supportNeighbors, mem_supportNeighbors]
  constructor
  · rintro ⟨x, hx, hI⟩
    obtain ⟨x₀, rfl⟩ := (crossingShiftEquiv a P).surjective x
    exact ⟨x₀, (mem_crossingSupportShift a S x₀).mp hx,
      (interlaces_shift hn hP a y x₀).mp hI⟩
  · rintro ⟨x, hx, hI⟩
    exact ⟨crossingShiftEquiv a P x, (mem_crossingSupportShift a S x).mpr hx,
      (interlaces_shift hn hP a y x).mpr hI⟩

theorem supportNeighbors_shift (hn : 3 ≤ n) (hP : Generic P) (a : ZMod n)
    (S : Finset (Crossing P)) :
    supportNeighbors hn ((generic_shift a P).mpr hP) (crossingSupportShift a S) =
      crossingSupportShift a (supportNeighbors hn hP S) := by
  ext y
  obtain ⟨y₀, rfl⟩ := (crossingShiftEquiv a P).surjective y
  rw [mem_crossingSupportShift, supportNeighbors_shift_mem]

theorem supportUnselected_shift (hn : 3 ≤ n) (hP : Generic P) (a : ZMod n)
    (S : Finset (Crossing P)) :
    supportUnselected hn ((generic_shift a P).mpr hP) (crossingSupportShift a S) =
      crossingSupportShift a (supportUnselected hn hP S) := by
  ext y
  obtain ⟨y₀, rfl⟩ := (crossingShiftEquiv a P).surjective y
  simp only [mem_supportUnselected, mem_crossingSupportShift]
  exact and_congr Iff.rfl (not_congr (supportNeighbors_shift_mem hn hP a S y₀))

end SM
