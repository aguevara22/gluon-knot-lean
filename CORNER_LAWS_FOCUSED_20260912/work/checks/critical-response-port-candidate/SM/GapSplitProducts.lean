import SM.CriticalCutSplit

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

namespace IntervalComposition

/-- Products over all raw interior indices equal products over their actual
positions. The unary empty product is included. -/
theorem prod_interiorPositions {R : Type*} [CommMonoid R]
    {I : BoundaryInterval n} (π : IntervalComposition I) (f : Fin n → R) :
    (∏ k : Fin (π.parts - 1), f (π.interiorPosition k)) =
      ∏ x ∈ π.cutSet.interior.val, f x := by
  have h : (π.indexMarks Finset.univ).val = π.cutSet.interior.val := by
    ext x
    change x ∈ Finset.univ.image π.interiorPosition ↔ x ∈ π.cutSet.interior.val
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact (π.mem_interior_iff_exists_index x).symm
  have hp := π.prod_indexMarks Finset.univ f
  rw [h] at hp
  exact hp

/-- Removing a chosen interior index removes exactly its physical position,
without division or any assumption that the omitted scalar is nonzero. -/
theorem prod_interiorPositions_erase {R : Type*} [CommMonoid R]
    {I : BoundaryInterval n} (π : IntervalComposition I) (k : Fin (π.parts - 1))
    (f : Fin n → R) :
    (∏ j ∈ Finset.univ.erase k, f (π.interiorPosition j)) =
      ∏ x ∈ π.cutSet.interior.val.erase (π.interiorPosition k), f x := by
  classical
  have h : (π.indexMarks (Finset.univ.erase k)).val =
      π.cutSet.interior.val.erase (π.interiorPosition k) := by
    ext x
    change x ∈ (Finset.univ.erase k).image π.interiorPosition ↔
      x ∈ π.cutSet.interior.val.erase (π.interiorPosition k)
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨fun he => hj (π.interiorPosition_injective he), π.interiorPosition_mem j⟩
    · rintro ⟨hx, hi⟩
      obtain ⟨j, rfl⟩ := (π.mem_interior_iff_exists_index x).mp hi
      exact ⟨j, fun he => hx (congrArg π.interiorPosition he), rfl⟩
  have hp := π.prod_indexMarks (Finset.univ.erase k) f
  rw [h] at hp
  exact hp

end IntervalComposition

namespace IncreasingBoundaryTriple

/-- The two-gap outer composition retains exactly lower, middle and upper. -/
def gapBaseComposition (t : IncreasingBoundaryTriple n) : IntervalComposition t.spanInterval where
  parts := 2
  parts_pos := by decide
  cut := ![t.lower, t.middle, t.upper]
  strict := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [t.lower_middle, t.middle_upper, lt_trans t.lower_middle t.middle_upper]
  first := rfl
  last := rfl

/-- Every middle-cut composition refines the actual two-gap outer list. -/
def gapRefinement (t : IncreasingBoundaryTriple n) (π : t.MiddleComposition) :
    RefiningCutSet t.gapBaseComposition :=
  ⟨π.val.cutSet, by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    change Fin 3 at k
    fin_cases k
    · exact π.val.cutSet.left_mem
    · exact π.property
    · exact π.val.cutSet.right_mem⟩

/-- The existing complete refinement bijection splits every actual child
factor between the two gaps. Nothing at their common endpoint is duplicated. -/
theorem gapComposition_child_product {R : Type*} [CommMonoid R]
    (t : IncreasingBoundaryTriple n) (π : t.MiddleComposition) (X : BoundaryInterval n → R) :
    (∏ j : Fin π.val.parts, X (π.val.part j)) =
      (∏ j : Fin (t.gapCompositionEquiv π).1.parts, X ((t.gapCompositionEquiv π).1.part j)) *
      (∏ j : Fin (t.gapCompositionEquiv π).2.parts, X ((t.gapCompositionEquiv π).2.part j)) := by
  have h := t.gapBaseComposition.prod_refined_children (t.gapRefinement π) X
  change (∏ k : Fin 2, ∏ j : Fin (t.gapBaseComposition.refinementInner (t.gapRefinement π) k).parts,
    X ((t.gapBaseComposition.refinementInner (t.gapRefinement π) k).part j)) =
      ∏ r : Fin π.val.cutSet.toComposition.parts, X (π.val.cutSet.toComposition.part r) at h
  rw [Fin.prod_univ_two] at h
  change ((∏ j : Fin (t.gapCompositionEquiv π).1.parts, X ((t.gapCompositionEquiv π).1.part j)) *
      (∏ j : Fin (t.gapCompositionEquiv π).2.parts, X ((t.gapCompositionEquiv π).2.part j))) =
    ∏ r : Fin π.val.cutSet.toComposition.parts, X (π.val.cutSet.toComposition.part r) at h
  rw [π.val.cutSet_toComposition] at h
  exact h.symm

/-- The middle cut is the sole extra interior position when the two gap
interior sets are combined. All three pieces use physical boundary positions. -/
theorem gapComposition_interior_union (t : IncreasingBoundaryTriple n) (π : t.MiddleComposition) :
    π.val.cutSet.interior.val = insert t.middle
      ((t.gapCompositionEquiv π).1.cutSet.interior.val ∪
       (t.gapCompositionEquiv π).2.cutSet.interior.val) := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_union, BoundaryCutSet.mem_interior_iff,
    t.gapCompositionEquiv_left_cuts π, t.gapCompositionEquiv_right_cuts π, Finset.mem_filter]
  change (x ∈ π.val.cutSet.cuts ∧ t.lower < x ∧ x < t.upper) ↔
    x = t.middle ∨
    ((x ∈ π.val.cutSet.cuts ∧ t.lower ≤ x ∧ x ≤ t.middle) ∧ t.lower < x ∧ x < t.middle) ∨
    ((x ∈ π.val.cutSet.cuts ∧ t.middle ≤ x ∧ x ≤ t.upper) ∧ t.middle < x ∧ x < t.upper)
  constructor
  · rintro ⟨hx, hl, hr⟩
    rcases lt_trichotomy x t.middle with h | h | h
    · exact Or.inr (Or.inl ⟨⟨hx, le_of_lt hl, le_of_lt h⟩, hl, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨⟨hx, le_of_lt h, le_of_lt hr⟩, h, hr⟩)
  · rintro (rfl | ⟨⟨hx, _, _⟩, hl, hr⟩ | ⟨⟨hx, _, _⟩, hl, hr⟩)
    · exact ⟨π.property, t.lower_middle, t.middle_upper⟩
    · exact ⟨hx, hl, lt_trans hr t.middle_upper⟩
    · exact ⟨hx, lt_trans t.lower_middle hl, hr⟩

theorem gapComposition_interiors_disjoint (t : IncreasingBoundaryTriple n) (π : t.MiddleComposition) :
    Disjoint (t.gapCompositionEquiv π).1.cutSet.interior.val
      (t.gapCompositionEquiv π).2.cutSet.interior.val := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hl := ((t.gapCompositionEquiv π).1.cutSet.interior.property x hx).2
  have hr := ((t.gapCompositionEquiv π).2.cutSet.interior.property x hy).1
  exact (lt_irrefl x) (lt_trans hl hr)

theorem middle_not_gap_interiors (t : IncreasingBoundaryTriple n) (π : t.MiddleComposition) :
    t.middle ∉ (t.gapCompositionEquiv π).1.cutSet.interior.val ∪
      (t.gapCompositionEquiv π).2.cutSet.interior.val := by
  intro h
  rcases Finset.mem_union.mp h with h | h
  · exact (lt_irrefl t.middle) (((t.gapCompositionEquiv π).1.cutSet.interior.property _ h).2)
  · exact (lt_irrefl t.middle) (((t.gapCompositionEquiv π).2.cutSet.interior.property _ h).1)

/-- Exact cut-factor decomposition for any scalar function on physical
positions. The distinguished factor appears once, and unary gap factors are1. -/
theorem gapComposition_cut_product {R : Type*} [CommMonoid R]
    (t : IncreasingBoundaryTriple n) (π : t.MiddleComposition) (f : Fin n → R) :
    (∏ k : Fin (π.val.parts - 1), f (π.val.interiorPosition k)) =
      f t.middle *
      ((∏ k : Fin ((t.gapCompositionEquiv π).1.parts - 1),
        f ((t.gapCompositionEquiv π).1.interiorPosition k)) *
       (∏ k : Fin ((t.gapCompositionEquiv π).2.parts - 1),
        f ((t.gapCompositionEquiv π).2.interiorPosition k))) := by
  rw [π.val.prod_interiorPositions, (t.gapCompositionEquiv π).1.prod_interiorPositions,
    (t.gapCompositionEquiv π).2.prod_interiorPositions]
  rw [t.gapComposition_interior_union π, Finset.prod_insert (t.middle_not_gap_interiors π),
    Finset.prod_union (t.gapComposition_interiors_disjoint π)]

/-- After deleting the critical gate, all remaining cut factors split into
the two complete gap products. This works even when any factor is zero. -/
theorem gapComposition_cut_product_without_middle {R : Type*} [CommMonoid R]
    (t : IncreasingBoundaryTriple n) (π : t.MiddleComposition)
    (k : Fin (π.val.parts - 1)) (hk : π.val.interiorPosition k = t.middle)
    (f : Fin n → R) :
    (∏ j ∈ Finset.univ.erase k, f (π.val.interiorPosition j)) =
      (∏ j : Fin ((t.gapCompositionEquiv π).1.parts - 1),
        f ((t.gapCompositionEquiv π).1.interiorPosition j)) *
      (∏ j : Fin ((t.gapCompositionEquiv π).2.parts - 1),
        f ((t.gapCompositionEquiv π).2.interiorPosition j)) := by
  rw [π.val.prod_interiorPositions_erase, hk,
    (t.gapCompositionEquiv π).1.prod_interiorPositions,
    (t.gapCompositionEquiv π).2.prod_interiorPositions,
    t.gapComposition_interior_union π, Finset.erase_insert (t.middle_not_gap_interiors π),
    Finset.prod_union (t.gapComposition_interiors_disjoint π)]

/-- Reindex and factor the entire middle-cut sum, with arbitrary physical
cut factors and arbitrary interval coordinates. No response law is a premise. -/
theorem middle_weighted_composition_sum {R : Type*} [CommSemiring R]
    (t : IncreasingBoundaryTriple n) (f : Fin n → R) (X : BoundaryInterval n → R) :
    (∑ π : t.MiddleComposition,
      (∏ k : Fin (π.val.parts - 1), f (π.val.interiorPosition k)) *
        ∏ k : Fin π.val.parts, X (π.val.part k)) =
      f t.middle *
        ((∑ L : IntervalComposition t.leftInterval,
          (∏ k : Fin (L.parts - 1), f (L.interiorPosition k)) *
            ∏ k : Fin L.parts, X (L.part k)) *
         (∑ R : IntervalComposition t.rightInterval,
          (∏ k : Fin (R.parts - 1), f (R.interiorPosition k)) *
            ∏ k : Fin R.parts, X (R.part k))) := by
  classical
  have hs := t.sum_middle_compositions (fun π =>
    (∏ k : Fin (π.val.parts - 1), f (π.val.interiorPosition k)) *
      ∏ k : Fin π.val.parts, X (π.val.part k))
  rw [hs, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L _
  apply Finset.sum_congr rfl
  intro R _
  rw [t.gapComposition_cut_product, t.gapComposition_child_product,
    t.gapCompositionEquiv.apply_symm_apply]
  ring

/-- The full response sum after removing the changing gate is the product
of the two gap sums. No cancellation of that gate's scalar is used. -/
theorem middle_erased_weighted_composition_sum {R : Type*} [CommSemiring R]
    (t : IncreasingBoundaryTriple n) (f : Fin n → R) (X : BoundaryInterval n → R) :
    (∑ π : t.MiddleComposition,
      (∏ x ∈ π.val.cutSet.interior.val.erase t.middle, f x) *
        ∏ k : Fin π.val.parts, X (π.val.part k)) =
      (∑ L : IntervalComposition t.leftInterval,
        (∏ k : Fin (L.parts - 1), f (L.interiorPosition k)) *
          ∏ k : Fin L.parts, X (L.part k)) *
      (∑ R : IntervalComposition t.rightInterval,
        (∏ k : Fin (R.parts - 1), f (R.interiorPosition k)) *
          ∏ k : Fin R.parts, X (R.part k)) := by
  classical
  rw [t.sum_middle_compositions, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L _
  apply Finset.sum_congr rfl
  intro R _
  rw [t.gapComposition_interior_union,
    Finset.erase_insert (t.middle_not_gap_interiors _),
    Finset.prod_union (t.gapComposition_interiors_disjoint _),
    t.gapComposition_child_product, t.gapCompositionEquiv.apply_symm_apply]
  rw [L.prod_interiorPositions, R.prod_interiorPositions]
  ring

end IncreasingBoundaryTriple

end
end SM
