import SM.Farout

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

namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- A far sample has the actual coordinate endpoints and its actual interior
cut. These three positions completely determine whether it is critical. -/
theorem farTriple_eq_iff (π : IntervalComposition I)
    (k : Fin (π.parts - 1)) (t : IncreasingBoundaryTriple n) :
    π.farTriple k = t ↔ I = t.spanInterval ∧ π.interiorPosition k = t.middle := by
  constructor
  · intro h
    exact ⟨BoundaryInterval.eq_of_endpoints
      (congrArg IncreasingBoundaryTriple.lower h)
      (congrArg IncreasingBoundaryTriple.upper h),
      congrArg IncreasingBoundaryTriple.middle h⟩
  · rintro ⟨hI, hm⟩
    exact IncreasingBoundaryTriple.eq_of_entries
      (congrArg BoundaryInterval.left hI) hm (congrArg BoundaryInterval.right hI)

/-- Distinct interior cuts cannot give the same far triple. -/
theorem farTriple_injective (π : IntervalComposition I) : Function.Injective π.farTriple := by
  intro k l h
  exact π.interiorPosition_injective (congrArg IncreasingBoundaryTriple.middle h)

/-- A critical triple occurs exactly once precisely when the coordinate is
its full span and the raw composition actually cuts at its middle position. -/
theorem existsUnique_farTriple_iff (π : IntervalComposition I) (t : IncreasingBoundaryTriple n) :
    (∃! k : Fin (π.parts - 1), π.farTriple k = t) ↔
      I = t.spanInterval ∧ t.middle ∈ π.cutSet.cuts := by
  constructor
  · rintro ⟨k, hk, _⟩
    have he := (π.farTriple_eq_iff k t).mp hk
    refine ⟨he.1, ?_⟩
    have hm := π.interiorPosition_mem k
    rw [he.2] at hm
    exact (BoundaryCutSet.mem_interior_iff π.cutSet t.middle).mp hm |>.1
  · rintro ⟨hI, hm⟩
    have hbounds : I.left < t.middle ∧ t.middle < I.right := by
      rw [hI]
      exact ⟨t.lower_middle, t.middle_upper⟩
    have hi : t.middle ∈ π.cutSet.interior.val :=
      (BoundaryCutSet.mem_interior_iff π.cutSet t.middle).mpr ⟨hm, hbounds⟩
    obtain ⟨k, hk⟩ := (π.mem_interior_iff_exists_index t.middle).mp hi
    have ht : π.farTriple k = t := (π.farTriple_eq_iff k t).mpr ⟨hI, hk⟩
    exact ⟨k, ht, fun l hl => π.farTriple_injective (hl.trans ht.symm)⟩

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- On every other coordinate the entire far coefficient is unchanged,
even when the interval contains the critical span as a proper subinterval. -/
theorem farWeight_unchanged_off_span (π : IntervalComposition I)
    (t : IncreasingBoundaryTriple n) (H₁ H₂ : TripleArray n R)
    (h : ∀ u, u ≠ t → H₁ u = H₂ u) (hI : I ≠ t.spanInterval) :
    π.nearFarWeight 0 H₁ = π.nearFarWeight 0 H₂ := by
  rw [nearFarWeight_far_only, nearFarWeight_far_only]
  apply Finset.prod_congr rfl
  intro k _
  rw [h (π.farTriple k) (fun hk => hI ((π.farTriple_eq_iff k t).mp hk).1)]

/-- In the critical coordinate, a composition with no middle cut also has
unchanged coefficient. Unary compositions are included by this statement. -/
theorem farWeight_unchanged_without_middle (π : IntervalComposition I)
    (t : IncreasingBoundaryTriple n) (H₁ H₂ : TripleArray n R)
    (h : ∀ u, u ≠ t → H₁ u = H₂ u) (hm : t.middle ∉ π.cutSet.cuts) :
    π.nearFarWeight 0 H₁ = π.nearFarWeight 0 H₂ := by
  rw [nearFarWeight_far_only, nearFarWeight_far_only]
  apply Finset.prod_congr rfl
  intro k _
  have ht : π.farTriple k ≠ t := by
    intro hk
    have hi := π.interiorPosition_mem k
    rw [((π.farTriple_eq_iff k t).mp hk).2] at hi
    exact hm ((BoundaryCutSet.mem_interior_iff π.cutSet t.middle).mp hi).1
  rw [h (π.farTriple k) ht]

/-- Compute the ordinary coefficient change by removing exactly its one
changing gate. Every remaining factor is proved equal across the two arrays. -/
theorem farWeight_difference_at_critical (π : IntervalComposition I)
    (t : IncreasingBoundaryTriple n) (H₁ H₂ : TripleArray n R)
    (h : ∀ u, u ≠ t → H₁ u = H₂ u)
    (k : Fin (π.parts - 1)) (hk : π.farTriple k = t) :
    π.nearFarWeight 0 H₂ - π.nearFarWeight 0 H₁ =
      (-(H₂ t - H₁ t) * ⅟ (2 : R)) *
        ∏ j ∈ (Finset.univ.erase k), -H₁ (π.farTriple j) * ⅟ (2 : R) := by
  classical
  have hp : (∏ j ∈ Finset.univ.erase k, -H₂ (π.farTriple j) * ⅟ (2 : R)) =
      ∏ j ∈ Finset.univ.erase k, -H₁ (π.farTriple j) * ⅟ (2 : R) := by
    apply Finset.prod_congr rfl
    intro j hj
    have ht : π.farTriple j ≠ t := by
      intro he
      exact (Finset.mem_erase.mp hj).1 (π.farTriple_injective (he.trans hk.symm))
    rw [h (π.farTriple j) ht]
  rw [nearFarWeight_far_only, nearFarWeight_far_only]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => -H₂ (π.farTriple j) * ⅟ (2 : R))
    (Finset.mem_univ k)]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => -H₁ (π.farTriple j) * ⅟ (2 : R))
    (Finset.mem_univ k)]
  rw [hk, hp]
  ring

/-- The reversed-far coefficient change is calculated separately. Its
changing gate has the opposite sign, and every retained factor is reversed. -/
theorem reversedFarWeight_difference_at_critical (π : IntervalComposition I)
    (t : IncreasingBoundaryTriple n) (H₁ H₂ : TripleArray n R)
    (h : ∀ u, u ≠ t → H₁ u = H₂ u)
    (k : Fin (π.parts - 1)) (hk : π.farTriple k = t) :
    π.nearFarWeight 0 (-H₂) - π.nearFarWeight 0 (-H₁) =
      ((H₂ t - H₁ t) * ⅟ (2 : R)) *
        ∏ j ∈ (Finset.univ.erase k), H₁ (π.farTriple j) * ⅟ (2 : R) := by
  have he := π.farWeight_difference_at_critical t (-H₁) (-H₂)
    (fun u hu => congrArg Neg.neg (h u hu)) k hk
  simpa only [Pi.neg_apply, neg_neg, neg_sub_neg, neg_sub] using he

end
end SM.IntervalComposition

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

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Complete composition sum with scalar weights at actual interior cut
positions and coordinates at actual child intervals, including the unary term. -/
def cutWeightedSum (f : Fin n → R) (X : IntervalArray n R) (I : BoundaryInterval n) : R :=
  ∑ π : IntervalComposition I,
    (∏ k : Fin (π.parts - 1), f (π.interiorPosition k)) *
      ∏ k : Fin π.parts, X (π.part k)

/-- If each cut scalar is the actual far gate, the weighted sum is the
entire source transform on that interval. -/
theorem cutWeightedSum_eq_farTransform (f : Fin n → R) (H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n)
    (h : ∀ π : IntervalComposition I, ∀ k : Fin (π.parts - 1),
      f (π.interiorPosition k) = -H (π.farTriple k) * ⅟ (2 : R)) :
    cutWeightedSum f X I = farTransform H X I := by
  unfold cutWeightedSum farTransform nearFarTransform
  apply Finset.sum_congr rfl
  intro π _
  rw [π.nearFarWeight_far_only]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  exact h π k

namespace IncreasingBoundaryTriple

/-- Evaluate a far gate at fixed critical endpoints and a varying physical
middle position. The value outside the open span is0; all sampled positions
are proved strictly inside before the evaluation rule is used. -/
def fixedFarGate (t : IncreasingBoundaryTriple n) (H : TripleArray n R) (x : Fin n) : R :=
  if hx : t.lower < x ∧ x < t.upper then
    -H ⟨t.lower, x, t.upper, hx.1, hx.2⟩ * ⅟ (2 : R)
  else 0

theorem fixedFarGate_at_interior (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (π : IntervalComposition t.spanInterval) (k : Fin (π.parts - 1)) :
    t.fixedFarGate H (π.interiorPosition k) = -H (π.farTriple k) * ⅟ (2 : R) := by
  have h : t.lower < π.interiorPosition k ∧ π.interiorPosition k < t.upper :=
    ⟨(π.farTriple k).lower_middle, (π.farTriple k).middle_upper⟩
  rw [fixedFarGate, dif_pos h]
  rfl

theorem fixedFarGate_neg (t : IncreasingBoundaryTriple n) (H : TripleArray n R) (x : Fin n) :
    t.fixedFarGate (-H) x = -t.fixedFarGate H x := by
  by_cases hx : t.lower < x ∧ x < t.upper
  · simp only [fixedFarGate, dif_pos hx, Pi.neg_apply, neg_neg, neg_mul]
  · simp only [fixedFarGate, dif_neg hx, neg_zero]

theorem fixedFarGate_weight (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (π : IntervalComposition t.spanInterval) :
    π.nearFarWeight 0 H =
      ∏ k : Fin (π.parts - 1), t.fixedFarGate H (π.interiorPosition k) := by
  rw [π.nearFarWeight_far_only]
  apply Finset.prod_congr rfl
  intro k _
  exact (t.fixedFarGate_at_interior H π k).symm

/-- Express the one-gate response by erasing exactly the physical middle
cut. This is the form needed by the full erased-gap sum bijection. -/
theorem farWeight_difference_physical (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (h : ∀ u, u ≠ t → H₁ u = H₂ u)
    (π : t.MiddleComposition) :
    π.val.nearFarWeight 0 H₂ - π.val.nearFarWeight 0 H₁ =
      (-(H₂ t - H₁ t) * ⅟ (2 : R)) *
        ∏ x ∈ π.val.cutSet.interior.val.erase t.middle, t.fixedFarGate H₁ x := by
  obtain ⟨k, hk, _⟩ := (π.val.existsUnique_farTriple_iff t).mpr ⟨rfl, π.property⟩
  have hm := ((π.val.farTriple_eq_iff k t).mp hk).2
  rw [π.val.farWeight_difference_at_critical t H₁ H₂ h k hk]
  congr 1
  have hp : (∏ j ∈ Finset.univ.erase k, -H₁ (π.val.farTriple j) * ⅟ (2 : R)) =
      ∏ j ∈ Finset.univ.erase k, t.fixedFarGate H₁ (π.val.interiorPosition j) := by
    apply Finset.prod_congr rfl
    intro j _
    exact (t.fixedFarGate_at_interior H₁ π.val j).symm
  rw [hp, π.val.prod_interiorPositions_erase, hm]

end IncreasingBoundaryTriple

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Change of all composition coefficients with the child coordinates held
fixed, summed over the complete raw domain, including the unary composition. -/
def coefficientDifferenceSum (H₁ H₂ : TripleArray n R) (X : IntervalArray n R)
    (I : BoundaryInterval n) : R :=
  ∑ π : IntervalComposition I,
    (π.nearFarWeight 0 H₂ - π.nearFarWeight 0 H₁) *
      ∏ k : Fin π.parts, X (π.part k)

/-- The unary coefficient difference is0, so removing just that composition
gives the exact nonunary coefficient sum in the triangular subtraction. -/
theorem coefficientDifferenceSum_eq_nonunary (H₁ H₂ : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    coefficientDifferenceSum H₁ H₂ X I =
      ∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        (π.val.nearFarWeight 0 H₂ - π.val.nearFarWeight 0 H₁) *
          ∏ k : Fin π.val.parts, X (π.val.part k) := by
  classical
  unfold coefficientDifferenceSum
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (IntervalComposition.single I)]
  rw [(IntervalComposition.single I).nearFarWeight_one 0 H₂ rfl,
    (IntervalComposition.single I).nearFarWeight_one 0 H₁ rfl,
    sub_self, zero_mul, zero_add]
  exact Fintype.sum_equiv (IntervalComposition.nonSingleEquiv I) _ _ (fun _ => rfl)

/-- Only actual middle-cut compositions contribute. Exact erasure and the
full raw splitting bijection factor their entire sum into the two gap sums. -/
theorem coefficientDifferenceSum_span (H₁ H₂ : TripleArray n R) (X : IntervalArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    coefficientDifferenceSum H₁ H₂ X t.spanInterval =
      (-(H₂ t - H₁ t) * ⅟ (2 : R)) *
        (cutWeightedSum (t.fixedFarGate H₁) X t.leftInterval *
         cutWeightedSum (t.fixedFarGate H₁) X t.rightInterval) := by
  classical
  let f : IntervalComposition t.spanInterval → R := fun π =>
    (π.nearFarWeight 0 H₂ - π.nearFarWeight 0 H₁) *
      ∏ k : Fin π.parts, X (π.part k)
  have ha := Fintype.sum_subtype_add_sum_subtype
    (fun π : IntervalComposition t.spanInterval => t.middle ∈ π.cutSet.cuts) f
  have hz : (∑ π : {π : IntervalComposition t.spanInterval // t.middle ∉ π.cutSet.cuts},
      f π.val) = 0 := by
    apply Finset.sum_eq_zero
    intro π _
    change (π.val.nearFarWeight 0 H₂ - π.val.nearFarWeight 0 H₁) *
      (∏ k : Fin π.val.parts, X (π.val.part k)) = 0
    rw [π.val.farWeight_unchanged_without_middle t H₁ H₂ h π.property,
      sub_self, zero_mul]
  rw [hz, add_zero] at ha
  change (∑ π : IntervalComposition t.spanInterval, f π) = _
  rw [← ha]
  change (∑ π : t.MiddleComposition,
    (π.val.nearFarWeight 0 H₂ - π.val.nearFarWeight 0 H₁) *
      ∏ k : Fin π.val.parts, X (π.val.part k)) = _
  simp_rw [t.farWeight_difference_physical H₁ H₂ h]
  calc
    _ = (-(H₂ t - H₁ t) * ⅟ (2 : R)) *
        ∑ π : t.MiddleComposition,
          (∏ x ∈ π.val.cutSet.interior.val.erase t.middle, t.fixedFarGate H₁ x) *
            ∏ k : Fin π.val.parts, X (π.val.part k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro π _
      ring
    _ = _ := by
      rw [t.middle_erased_weighted_composition_sum]
      rfl

/-- Reverse every far sign and compute the response again. The changing
factor has plus delta, and the gap sums use reversed remaining gates. -/
theorem coefficientDifferenceSum_span_reversed (H₁ H₂ : TripleArray n R)
    (X : IntervalArray n R) (t : IncreasingBoundaryTriple n)
    (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    coefficientDifferenceSum (-H₁) (-H₂) X t.spanInterval =
      ((H₂ t - H₁ t) * ⅟ (2 : R)) *
        (cutWeightedSum (t.fixedFarGate (-H₁)) X t.leftInterval *
         cutWeightedSum (t.fixedFarGate (-H₁)) X t.rightInterval) := by
  have he := coefficientDifferenceSum_span (-H₁) (-H₂) X t
    (fun u hu => congrArg Neg.neg (h u hu))
  simpa only [Pi.neg_apply, neg_sub_neg, neg_sub] using he

end
end SM

#print axioms SM.coefficientDifferenceSum
#print axioms SM.coefficientDifferenceSum_eq_nonunary
#print axioms SM.coefficientDifferenceSum_span
#print axioms SM.coefficientDifferenceSum_span_reversed
