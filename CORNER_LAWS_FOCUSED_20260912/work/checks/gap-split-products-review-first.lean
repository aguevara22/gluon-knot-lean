import SM.Farout
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
set_option pp.universes false

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

namespace IncreasingBoundaryTriple

/-- The actual critical boundary interval, before any contraction. -/
def spanInterval (t : IncreasingBoundaryTriple n) : BoundaryInterval n :=
  ⟨t.lower, t.upper, lt_trans t.lower_middle t.middle_upper⟩

/-- All complete cut sets containing the critical middle position. -/
abbrev MiddleCutSet (t : IncreasingBoundaryTriple n) :=
  {S : BoundaryCutSet t.spanInterval // t.middle ∈ S.cuts}

/-- Concatenate both gap cut sets by their union. Their common endpoint is
one actual position; it occurs once in the resulting ordered cut list. -/
def joinGapCuts (t : IncreasingBoundaryTriple n)
    (L : BoundaryCutSet t.leftInterval) (R : BoundaryCutSet t.rightInterval) :
    t.MiddleCutSet :=
  ⟨{ cuts := L.cuts ∪ R.cuts
     left_mem := Finset.mem_union_left _ L.left_mem
     right_mem := Finset.mem_union_right _ R.right_mem
     bounds := by
       intro x hx
       rcases Finset.mem_union.mp hx with hx | hx
       · have h := L.bounds x hx
         exact ⟨h.1, le_trans h.2 (le_of_lt t.middle_upper)⟩
       · have h := R.bounds x hx
         exact ⟨le_trans (le_of_lt t.lower_middle) h.1, h.2⟩ },
    Finset.mem_union_left _ L.right_mem⟩

/-- Split at the retained middle cut, preserving all cuts on both closed gaps. -/
def splitGapCuts (t : IncreasingBoundaryTriple n) (S : t.MiddleCutSet) :
    BoundaryCutSet t.leftInterval × BoundaryCutSet t.rightInterval :=
  (S.val.restrict t.leftInterval S.val.left_mem S.property,
   S.val.restrict t.rightInterval S.property S.val.right_mem)

theorem split_joinGapCuts (t : IncreasingBoundaryTriple n)
    (L : BoundaryCutSet t.leftInterval) (R : BoundaryCutSet t.rightInterval) :
    t.splitGapCuts (t.joinGapCuts L R) = (L, R) := by
  apply Prod.ext
  · apply BoundaryCutSet.ext
    ext x
    change x ∈ (L.cuts ∪ R.cuts).filter (fun x => t.lower ≤ x ∧ x ≤ t.middle) ↔ x ∈ L.cuts
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hl, hr⟩
      · exact hx
      · have hm := (R.bounds x hx).1
        have he : x = t.middle := le_antisymm hr hm
        rw [he]
        exact L.right_mem
    · intro hx
      exact ⟨Or.inl hx, L.bounds x hx⟩
  · apply BoundaryCutSet.ext
    ext x
    change x ∈ (L.cuts ∪ R.cuts).filter (fun x => t.middle ≤ x ∧ x ≤ t.upper) ↔ x ∈ R.cuts
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hl, hr⟩
      · have hm := (L.bounds x hx).2
        have he : x = t.middle := le_antisymm hm hl
        rw [he]
        exact R.left_mem
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, R.bounds x hx⟩

theorem join_splitGapCuts (t : IncreasingBoundaryTriple n) (S : t.MiddleCutSet) :
    t.joinGapCuts (t.splitGapCuts S).1 (t.splitGapCuts S).2 = S := by
  apply Subtype.ext
  apply BoundaryCutSet.ext
  ext x
  change x ∈ (S.val.cuts.filter (fun x => t.lower ≤ x ∧ x ≤ t.middle)) ∪
    (S.val.cuts.filter (fun x => t.middle ≤ x ∧ x ≤ t.upper)) ↔ x ∈ S.val.cuts
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hx, _, _⟩ | ⟨hx, _, _⟩) <;> exact hx
  · intro hx
    have hb := S.val.bounds x hx
    rcases le_total x t.middle with h | h
    · exact Or.inl ⟨hx, hb.1, h⟩
    · exact Or.inr ⟨hx, h, hb.2⟩

/-- The cut-list splitting bijection has the complete Cartesian product
as its range, including the unary composition on either gap. -/
def gapCutEquiv (t : IncreasingBoundaryTriple n) :
    t.MiddleCutSet ≃ BoundaryCutSet t.leftInterval × BoundaryCutSet t.rightInterval where
  toFun := t.splitGapCuts
  invFun := fun p => t.joinGapCuts p.1 p.2
  left_inv := t.join_splitGapCuts
  right_inv := fun p => t.split_joinGapCuts p.1 p.2

/-- The unchanged raw composition domain, with exactly the requirement
that its cut list contains the critical middle vertex. -/
abbrev MiddleComposition (t : IncreasingBoundaryTriple n) :=
  {π : IntervalComposition t.spanInterval // t.middle ∈ π.cutSet.cuts}

def middleCompositionCutEquiv (t : IncreasingBoundaryTriple n) :
    t.MiddleComposition ≃ t.MiddleCutSet :=
  Equiv.subtypeEquiv (IntervalComposition.cutSetEquiv t.spanInterval) (fun _ => Iff.rfl)

/-- Exact raw source compositions split into all pairs of raw gap
compositions. No positivity condition beyond each gap's actual length is added. -/
def gapCompositionEquiv (t : IncreasingBoundaryTriple n) :
    t.MiddleComposition ≃ IntervalComposition t.leftInterval × IntervalComposition t.rightInterval :=
  (t.middleCompositionCutEquiv.trans t.gapCutEquiv).trans
    (Equiv.prodCongr (IntervalComposition.cutSetEquiv t.leftInterval).symm
      (IntervalComposition.cutSetEquiv t.rightInterval).symm)

theorem gapCompositionEquiv_left_cuts (t : IncreasingBoundaryTriple n)
    (π : t.MiddleComposition) :
    (t.gapCompositionEquiv π).1.cutSet.cuts =
      π.val.cutSet.cuts.filter (fun x => t.lower ≤ x ∧ x ≤ t.middle) := by
  change (π.val.cutSet.restrict t.leftInterval π.val.cutSet.left_mem π.property).toComposition.cutSet.cuts = _
  rw [BoundaryCutSet.toComposition_cutSet]
  rfl

theorem gapCompositionEquiv_right_cuts (t : IncreasingBoundaryTriple n)
    (π : t.MiddleComposition) :
    (t.gapCompositionEquiv π).2.cutSet.cuts =
      π.val.cutSet.cuts.filter (fun x => t.middle ≤ x ∧ x ≤ t.upper) := by
  change (π.val.cutSet.restrict t.rightInterval π.property π.val.cutSet.right_mem).toComposition.cutSet.cuts = _
  rw [BoundaryCutSet.toComposition_cutSet]
  rfl

theorem gapCompositionEquiv_symm_cuts (t : IncreasingBoundaryTriple n)
    (L : IntervalComposition t.leftInterval) (R : IntervalComposition t.rightInterval) :
    (t.gapCompositionEquiv.symm (L, R)).val.cutSet.cuts = L.cutSet.cuts ∪ R.cutSet.cuts := by
  change (t.joinGapCuts L.cutSet R.cutSet).val.toComposition.cutSet.cuts = _
  rw [BoundaryCutSet.toComposition_cutSet]
  rfl

/-- Reindex any sum over the full middle-cut domain as the double gap sum.
The summand is arbitrary; no wall-response formula is assumed. -/
theorem sum_middle_compositions {R : Type*} [AddCommMonoid R]
    (t : IncreasingBoundaryTriple n) (f : t.MiddleComposition → R) :
    (∑ π : t.MiddleComposition, f π) =
      ∑ L : IntervalComposition t.leftInterval, ∑ R : IntervalComposition t.rightInterval,
        f (t.gapCompositionEquiv.symm (L, R)) := by
  classical
  calc
    (∑ π : t.MiddleComposition, f π) =
        ∑ p : IntervalComposition t.leftInterval × IntervalComposition t.rightInterval,
          f (t.gapCompositionEquiv.symm p) :=
      Fintype.sum_equiv t.gapCompositionEquiv _ _
        (fun π => congrArg f (t.gapCompositionEquiv.symm_apply_apply π).symm)
    _ = _ := Fintype.sum_prod_type (fun p => f (t.gapCompositionEquiv.symm p))

end IncreasingBoundaryTriple

end
end SM

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

namespace GapSplitProductsIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n]

theorem every_raw_left_child_preserved (t : IncreasingBoundaryTriple n) (π : t.MiddleComposition)
    (j : Fin (t.gapCompositionEquiv π).1.parts) :
    ∃ r : Fin π.val.parts, π.val.part r = (t.gapCompositionEquiv π).1.part j := by
  have h := t.gapBaseComposition.exists_refined_child (t.gapRefinement π) (0 : Fin 2) j
  change ∃ r : Fin π.val.cutSet.toComposition.parts,
    π.val.cutSet.toComposition.part r = (t.gapCompositionEquiv π).1.part j at h
  rw [π.val.cutSet_toComposition] at h
  exact h

theorem every_raw_right_child_preserved (t : IncreasingBoundaryTriple n) (π : t.MiddleComposition)
    (j : Fin (t.gapCompositionEquiv π).2.parts) :
    ∃ r : Fin π.val.parts, π.val.part r = (t.gapCompositionEquiv π).2.part j := by
  have h := t.gapBaseComposition.exists_refined_child (t.gapRefinement π) (1 : Fin 2) j
  change ∃ r : Fin π.val.cutSet.toComposition.parts,
    π.val.cutSet.toComposition.part r = (t.gapCompositionEquiv π).2.part j at h
  rw [π.val.cutSet_toComposition] at h
  exact h

variable {R : Type*} [CommMonoid R]

theorem arbitrary_raw_pair_child_product (t : IncreasingBoundaryTriple n)
    (L : IntervalComposition t.leftInterval) (Q : IntervalComposition t.rightInterval)
    (X : BoundaryInterval n → R) :
    (∏ k : Fin (t.gapCompositionEquiv.symm (L,Q)).val.parts,
      X ((t.gapCompositionEquiv.symm (L,Q)).val.part k)) =
      (∏ k : Fin L.parts, X (L.part k)) * ∏ k : Fin Q.parts, X (Q.part k) := by
  simpa only [Equiv.apply_symm_apply] using
    t.gapComposition_child_product (t.gapCompositionEquiv.symm (L,Q)) X

theorem unary_left_keeps_actual_gap_coordinate (t : IncreasingBoundaryTriple n)
    (Q : IntervalComposition t.rightInterval) (X : BoundaryInterval n → R) :
    (∏ k : Fin (t.gapCompositionEquiv.symm (IntervalComposition.single t.leftInterval,Q)).val.parts,
      X ((t.gapCompositionEquiv.symm (IntervalComposition.single t.leftInterval,Q)).val.part k)) =
      X t.leftInterval * ∏ k : Fin Q.parts, X (Q.part k) := by
  rw [arbitrary_raw_pair_child_product, IntervalComposition.single_product]

theorem unary_right_keeps_actual_gap_coordinate (t : IncreasingBoundaryTriple n)
    (L : IntervalComposition t.leftInterval) (X : BoundaryInterval n → R) :
    (∏ k : Fin (t.gapCompositionEquiv.symm (L,IntervalComposition.single t.rightInterval)).val.parts,
      X ((t.gapCompositionEquiv.symm (L,IntervalComposition.single t.rightInterval)).val.part k)) =
      (∏ k : Fin L.parts, X (L.part k)) * X t.rightInterval := by
  rw [arbitrary_raw_pair_child_product, IntervalComposition.single_product]

theorem erased_product_ignores_omitted_value (t : IncreasingBoundaryTriple n) (π : t.MiddleComposition)
    (f g : Fin n → R) (h : ∀ x, x ≠ t.middle → f x = g x) :
    (∏ x ∈ π.val.cutSet.interior.val.erase t.middle, f x) =
      ∏ x ∈ π.val.cutSet.interior.val.erase t.middle, g x := by
  classical
  apply Finset.prod_congr rfl
  intro x hx
  exact h x (Finset.mem_erase.mp hx).1

theorem two_unary_gaps_leave_empty_gate_product (t : IncreasingBoundaryTriple n)
    (π : t.MiddleComposition) (hL : (t.gapCompositionEquiv π).1.parts = 1)
    (hR : (t.gapCompositionEquiv π).2.parts = 1)
    (k : Fin (π.val.parts - 1)) (hk : π.val.interiorPosition k = t.middle) (f : Fin n → R) :
    (∏ j ∈ Finset.univ.erase k, f (π.val.interiorPosition j)) = 1 := by
  letI : IsEmpty (Fin ((t.gapCompositionEquiv π).1.parts - 1)) :=
    ⟨fun j => by have := j.isLt; omega⟩
  letI : IsEmpty (Fin ((t.gapCompositionEquiv π).2.parts - 1)) :=
    ⟨fun j => by have := j.isLt; omega⟩
  rw [t.gapComposition_cut_product_without_middle π k hk]
  simp

end
end GapSplitProductsIndependentReview

namespace GapSplitProductsIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommSemiring R]

theorem zero_middle_annuls_full_sum (t : IncreasingBoundaryTriple n) (f : Fin n → R)
    (X : BoundaryInterval n → R) (hzero : f t.middle = 0) :
    (∑ π : t.MiddleComposition,
      (∏ k : Fin (π.val.parts - 1), f (π.val.interiorPosition k)) *
        ∏ k : Fin π.val.parts, X (π.val.part k)) = 0 := by
  rw [t.middle_weighted_composition_sum, hzero, zero_mul]

theorem erased_sum_keeps_gap_products_when_middle_zero (t : IncreasingBoundaryTriple n)
    (f : Fin n → R) (X : BoundaryInterval n → R) (_hzero : f t.middle = 0) :
    (∑ π : t.MiddleComposition,
      (∏ x ∈ π.val.cutSet.interior.val.erase t.middle, f x) *
        ∏ k : Fin π.val.parts, X (π.val.part k)) =
      (∑ L : IntervalComposition t.leftInterval,
        (∏ k : Fin (L.parts - 1), f (L.interiorPosition k)) * ∏ k : Fin L.parts, X (L.part k)) *
      (∑ Q : IntervalComposition t.rightInterval,
        (∏ k : Fin (Q.parts - 1), f (Q.interiorPosition k)) * ∏ k : Fin Q.parts, X (Q.part k)) :=
  t.middle_erased_weighted_composition_sum f X

theorem erased_sum_ignores_any_middle_change (t : IncreasingBoundaryTriple n)
    (f g : Fin n → R) (h : ∀ x, x ≠ t.middle → f x = g x) (X : BoundaryInterval n → R) :
    (∑ π : t.MiddleComposition,
      (∏ x ∈ π.val.cutSet.interior.val.erase t.middle, f x) * ∏ k : Fin π.val.parts, X (π.val.part k)) =
    (∑ π : t.MiddleComposition,
      (∏ x ∈ π.val.cutSet.interior.val.erase t.middle, g x) * ∏ k : Fin π.val.parts, X (π.val.part k)) := by
  classical
  apply Finset.sum_congr rfl
  intro π _
  rw [erased_product_ignores_omitted_value t π f g h]

end
end GapSplitProductsIndependentReview

#check SM.IncreasingBoundaryTriple.MiddleCutSet
#print axioms SM.IncreasingBoundaryTriple.MiddleCutSet
#check SM.IncreasingBoundaryTriple.MiddleComposition
#print axioms SM.IncreasingBoundaryTriple.MiddleComposition
#check SM.IncreasingBoundaryTriple.spanInterval
#print axioms SM.IncreasingBoundaryTriple.spanInterval
#check SM.IncreasingBoundaryTriple.joinGapCuts
#print axioms SM.IncreasingBoundaryTriple.joinGapCuts
#check SM.IncreasingBoundaryTriple.splitGapCuts
#print axioms SM.IncreasingBoundaryTriple.splitGapCuts
#check SM.IncreasingBoundaryTriple.split_joinGapCuts
#print axioms SM.IncreasingBoundaryTriple.split_joinGapCuts
#check SM.IncreasingBoundaryTriple.join_splitGapCuts
#print axioms SM.IncreasingBoundaryTriple.join_splitGapCuts
#check SM.IncreasingBoundaryTriple.gapCutEquiv
#print axioms SM.IncreasingBoundaryTriple.gapCutEquiv
#check SM.IncreasingBoundaryTriple.middleCompositionCutEquiv
#print axioms SM.IncreasingBoundaryTriple.middleCompositionCutEquiv
#check SM.IncreasingBoundaryTriple.gapCompositionEquiv
#print axioms SM.IncreasingBoundaryTriple.gapCompositionEquiv
#check SM.IncreasingBoundaryTriple.gapCompositionEquiv_left_cuts
#print axioms SM.IncreasingBoundaryTriple.gapCompositionEquiv_left_cuts
#check SM.IncreasingBoundaryTriple.gapCompositionEquiv_right_cuts
#print axioms SM.IncreasingBoundaryTriple.gapCompositionEquiv_right_cuts
#check SM.IncreasingBoundaryTriple.gapCompositionEquiv_symm_cuts
#print axioms SM.IncreasingBoundaryTriple.gapCompositionEquiv_symm_cuts
#check SM.IncreasingBoundaryTriple.sum_middle_compositions
#print axioms SM.IncreasingBoundaryTriple.sum_middle_compositions
#check SM.IntervalComposition.prod_interiorPositions
#print axioms SM.IntervalComposition.prod_interiorPositions
#check SM.IntervalComposition.prod_interiorPositions_erase
#print axioms SM.IntervalComposition.prod_interiorPositions_erase
#check SM.IncreasingBoundaryTriple.gapBaseComposition
#print axioms SM.IncreasingBoundaryTriple.gapBaseComposition
#check SM.IncreasingBoundaryTriple.gapRefinement
#print axioms SM.IncreasingBoundaryTriple.gapRefinement
#check SM.IncreasingBoundaryTriple.gapComposition_child_product
#print axioms SM.IncreasingBoundaryTriple.gapComposition_child_product
#check SM.IncreasingBoundaryTriple.gapComposition_interior_union
#print axioms SM.IncreasingBoundaryTriple.gapComposition_interior_union
#check SM.IncreasingBoundaryTriple.gapComposition_interiors_disjoint
#print axioms SM.IncreasingBoundaryTriple.gapComposition_interiors_disjoint
#check SM.IncreasingBoundaryTriple.middle_not_gap_interiors
#print axioms SM.IncreasingBoundaryTriple.middle_not_gap_interiors
#check SM.IncreasingBoundaryTriple.gapComposition_cut_product
#print axioms SM.IncreasingBoundaryTriple.gapComposition_cut_product
#check SM.IncreasingBoundaryTriple.gapComposition_cut_product_without_middle
#print axioms SM.IncreasingBoundaryTriple.gapComposition_cut_product_without_middle
#check SM.IncreasingBoundaryTriple.middle_weighted_composition_sum
#print axioms SM.IncreasingBoundaryTriple.middle_weighted_composition_sum
#check SM.IncreasingBoundaryTriple.middle_erased_weighted_composition_sum
#print axioms SM.IncreasingBoundaryTriple.middle_erased_weighted_composition_sum
#print SM.IncreasingBoundaryTriple.spanInterval
#print SM.IncreasingBoundaryTriple.MiddleCutSet
#print SM.IncreasingBoundaryTriple.MiddleComposition
#print SM.IncreasingBoundaryTriple.gapCompositionEquiv
#print SM.IncreasingBoundaryTriple.gapBaseComposition
#print SM.IncreasingBoundaryTriple.gapRefinement
#print SM.IntervalComposition.refinedChildrenEquiv
#print SM.IntervalComposition.refinementInner
#print SM.IntervalComposition.interiorPosition
#print axioms GapSplitProductsIndependentReview.every_raw_left_child_preserved
#print axioms GapSplitProductsIndependentReview.every_raw_right_child_preserved
#print axioms GapSplitProductsIndependentReview.arbitrary_raw_pair_child_product
#print axioms GapSplitProductsIndependentReview.unary_left_keeps_actual_gap_coordinate
#print axioms GapSplitProductsIndependentReview.unary_right_keeps_actual_gap_coordinate
#print axioms GapSplitProductsIndependentReview.erased_product_ignores_omitted_value
#print axioms GapSplitProductsIndependentReview.two_unary_gaps_leave_empty_gate_product
#print axioms GapSplitProductsIndependentReview.zero_middle_annuls_full_sum
#print axioms GapSplitProductsIndependentReview.erased_sum_keeps_gap_products_when_middle_zero
#print axioms GapSplitProductsIndependentReview.erased_sum_ignores_any_middle_change
