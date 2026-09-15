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

#print axioms SM.IntervalComposition.farTriple_eq_iff
#print axioms SM.IntervalComposition.farTriple_injective
#print axioms SM.IntervalComposition.existsUnique_farTriple_iff
#print axioms SM.IntervalComposition.farWeight_unchanged_off_span
#print axioms SM.IntervalComposition.farWeight_unchanged_without_middle
#print axioms SM.IntervalComposition.farWeight_difference_at_critical
#print axioms SM.IntervalComposition.reversedFarWeight_difference_at_critical
