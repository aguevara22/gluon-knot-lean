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

#print axioms SM.IncreasingBoundaryTriple.spanInterval
#print axioms SM.IncreasingBoundaryTriple.joinGapCuts
#print axioms SM.IncreasingBoundaryTriple.splitGapCuts
#print axioms SM.IncreasingBoundaryTriple.split_joinGapCuts
#print axioms SM.IncreasingBoundaryTriple.join_splitGapCuts
#print axioms SM.IncreasingBoundaryTriple.gapCutEquiv
#print axioms SM.IncreasingBoundaryTriple.middleCompositionCutEquiv
#print axioms SM.IncreasingBoundaryTriple.gapCompositionEquiv
#print axioms SM.IncreasingBoundaryTriple.gapCompositionEquiv_left_cuts
#print axioms SM.IncreasingBoundaryTriple.gapCompositionEquiv_right_cuts
#print axioms SM.IncreasingBoundaryTriple.gapCompositionEquiv_symm_cuts
#print axioms SM.IncreasingBoundaryTriple.sum_middle_compositions
