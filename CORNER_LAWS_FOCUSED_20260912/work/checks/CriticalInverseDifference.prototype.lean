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

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Equality of every actual triple inside J is equality of the complete
restricted arrays; no condition is imposed on entries outside J. -/
theorem restrictTripleArray_eq_of_local (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ t : IncreasingBoundaryTriple n, J.left ≤ t.lower → t.upper ≤ J.right → H₁ t = H₂ t) :
    restrictTripleArray J H₁ = restrictTripleArray J H₂ := by
  funext t
  exact h (J.liftTriple t) (J.globalPosition_bounds t.lower).1 (J.globalPosition_bounds t.upper).2

/-- Inverse coordinates depend only on actual triples inside their own
interval. The one-leaf convention is proved separately before using a closed
full local interval at larger arity. -/
theorem farOnlyCoordinates_local (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ t : IncreasingBoundaryTriple n, J.left ≤ t.lower → t.upper ≤ J.right → H₁ t = H₂ t) :
    farOnlyCoordinates H₁ J = farOnlyCoordinates H₂ J := by
  by_cases hj : J.leaves = 1
  · rw [farOnlyCoordinates_leaf H₁ J hj, farOnlyCoordinates_leaf H₂ J hj]
  · have hJ : 2 ≤ J.leaves := by have := J.leaves_pos; omega
    let K := fullBoundaryInterval (by omega : 3 ≤ J.leaves + 1)
    have he := congrArg (fun H : TripleArray (J.leaves + 1) R => farOnlyCoordinates H)
      (restrictTripleArray_eq_of_local J H₁ H₂ h)
    have h₁ := congrFun (farOnlyCoordinates_restrict J H₁) K
    have h₂ := congrFun (farOnlyCoordinates_restrict J H₂) K
    change farOnlyCoordinates H₁ (J.liftInterval K) = farOnlyCoordinates (restrictTripleArray J H₁) K at h₁
    change farOnlyCoordinates H₂ (J.liftInterval K) = farOnlyCoordinates (restrictTripleArray J H₂) K at h₂
    rw [J.lift_fullInterval hJ] at h₁ h₂
    exact h₁.trans ((congrFun he K).trans h₂.symm)

/-- If one critical triple is the only array entry that can differ, every
interval not containing its full span has unchanged inverse coordinate. This
is the locality step in the single-triple wall response, before wall geometry. -/
theorem farOnlyCoordinates_unchanged_off_critical (H₁ H₂ : TripleArray n R)
    (critical : IncreasingBoundaryTriple n)
    (h : ∀ t : IncreasingBoundaryTriple n, t ≠ critical → H₁ t = H₂ t)
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ critical.lower ∧ critical.upper ≤ J.right)) :
    farOnlyCoordinates H₁ J = farOnlyCoordinates H₂ J := by
  apply farOnlyCoordinates_local J H₁ H₂
  intro t hl hr
  apply h t
  intro ht
  subst t
  exact hJ ⟨hl, hr⟩

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Separate the unary coordinate change from all coefficient changes when
every proper child coordinate agrees. This is an identity of the actual full
transforms, over all raw nonunary compositions. -/
theorem farTransform_difference_of_proper_children
    (H₁ H₂ : TripleArray n R) (X₁ X₂ : IntervalArray n R) (I : BoundaryInterval n)
    (hX : ∀ π : IntervalComposition I, 2 ≤ π.parts →
      ∀ k : Fin π.parts, X₁ (π.part k) = X₂ (π.part k)) :
    farTransform H₂ X₂ I - farTransform H₁ X₁ I =
      (X₂ I - X₁ I) +
      ∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        (π.val.nearFarWeight 0 H₂ - π.val.nearFarWeight 0 H₁) *
          ∏ k : Fin π.val.parts, X₁ (π.val.part k) := by
  classical
  change nearFarTransform 0 H₂ X₂ I - nearFarTransform 0 H₁ X₁ I = _
  rw [nearFarTransform_eq_triangular, nearFarTransform_eq_triangular]
  unfold triangularTransform
  have hs : (∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
      π.val.nearFarWeight 0 H₂ * ∏ k : Fin π.val.parts, X₂ (π.val.part k)) =
      ∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        π.val.nearFarWeight 0 H₂ * ∏ k : Fin π.val.parts, X₁ (π.val.part k) := by
    apply Finset.sum_congr rfl
    intro π _
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    exact (hX π.val π.property k).symm
  rw [hs]
  have hd : (∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
      (π.val.nearFarWeight 0 H₂ - π.val.nearFarWeight 0 H₁) *
        ∏ k : Fin π.val.parts, X₁ (π.val.part k)) =
      (∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        π.val.nearFarWeight 0 H₂ * ∏ k : Fin π.val.parts, X₁ (π.val.part k)) -
      (∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        π.val.nearFarWeight 0 H₁ * ∏ k : Fin π.val.parts, X₁ (π.val.part k)) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hd]
  ring

/-- Every proper child of the critical span has unchanged inverse value.
Containing the span would contradict its strictly smaller leaf count. -/
theorem critical_proper_child_coordinates (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u)
    (π : IntervalComposition t.spanInterval) (hp : 2 ≤ π.parts) (k : Fin π.parts) :
    farOnlyCoordinates H₁ (π.part k) = farOnlyCoordinates H₂ (π.part k) := by
  apply farOnlyCoordinates_unchanged_off_critical H₁ H₂ t h
  rintro ⟨hl, hr⟩
  have hc := π.part_leaves_lt hp k
  change (π.part k).left.val ≤ t.lower.val at hl
  change t.upper.val ≤ (π.part k).right.val at hr
  change (π.part k).right.val - (π.part k).left.val < t.upper.val - t.lower.val at hc
  omega

/-- Subtract the two actual inverse equations. Their identical right-hand
side cancels, and the unary coefficient1 gives the negative coefficient sum.
This derives the source coordinate change without assuming a response formula. -/
theorem critical_inverse_difference (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval =
      -(∑ π : {π : IntervalComposition t.spanInterval // 2 ≤ π.parts},
        (π.val.nearFarWeight 0 H₂ - π.val.nearFarWeight 0 H₁) *
          ∏ k : Fin π.val.parts, farOnlyCoordinates H₁ (π.val.part k)) := by
  have he := farTransform_difference_of_proper_children H₁ H₂
    (farOnlyCoordinates H₁) (farOnlyCoordinates H₂) t.spanInterval
    (critical_proper_child_coordinates H₁ H₂ t h)
  rw [farOnlyCoordinates_equation, farOnlyCoordinates_equation, sub_self] at he
  exact eq_neg_of_add_eq_zero_left he.symm

/-- The complete reversed-far output has the same unary coordinate change
and its own separately computed coefficient response. -/
theorem critical_output_difference (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    farOnlyOutput H₂ t.spanInterval - farOnlyOutput H₁ t.spanInterval =
      (farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval) +
      ∑ π : {π : IntervalComposition t.spanInterval // 2 ≤ π.parts},
        (π.val.nearFarWeight 0 (-H₂) - π.val.nearFarWeight 0 (-H₁)) *
          ∏ k : Fin π.val.parts, farOnlyCoordinates H₁ (π.val.part k) :=
  farTransform_difference_of_proper_children (-H₁) (-H₂)
    (farOnlyCoordinates H₁) (farOnlyCoordinates H₂) t.spanInterval
    (critical_proper_child_coordinates H₁ H₂ t h)

end
end SM

#print axioms SM.farTransform_difference_of_proper_children
#print axioms SM.critical_proper_child_coordinates
#print axioms SM.critical_inverse_difference
#print axioms SM.critical_output_difference
