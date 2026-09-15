import SM.UnorderedWallTriples
import SM.RestrictedWordRoot
import SM.GermTurnSigns
import SM.EuclideanPlane
import Mathlib.Data.Sign.Basic
import SM.GermNeighborhood
import SM.CriticalSourceResponse
import SM.FiniteChiStability
import SM.BoundaryTripleSupports
import SM.CriticalContractionPositions
import SM.CriticalContractionBounds
import SM.ContractedGeometricWord
import SM.ContractedIntervals

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/ContractedCompositions.body.lean (prototype UnorderedIntegerSingleTripleResponse, kernel session 17021, receipt
UnorderedIntegerSingleTripleResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Expand every raw cut while preserving the part count, including unary
compositions. The skipped critical interior occurs within one expanded part. -/
def expandComposition (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J) :
    IntervalComposition (t.expandInterval J) where
  parts := π.parts
  parts_pos := π.parts_pos
  cut := fun k => t.expandPosition (π.cut k)
  strict := t.expandPosition_strict.comp π.strict
  first := congrArg t.expandPosition π.first
  last := congrArg t.expandPosition π.last

/-- This exact domain excludes only cuts strictly inside the deleted arc. -/
def SurvivingCuts (t : IncreasingBoundaryTriple n) {I : BoundaryInterval n}
    (π : IntervalComposition I) : Prop :=
  ∀ k : Fin (π.parts + 1), π.cut k ≤ t.lower ∨ t.upper ≤ π.cut k

theorem expandComposition_survives (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J) :
    SurvivingCuts t (expandComposition t π) := by
  intro k
  exact t.expandPosition_survives (π.cut k)

/-- Contract exactly the original surviving cut list. Endpoint identities
show the result is a composition of J, not an arbitrary new interval. -/
def contractComposition (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition (t.expandInterval J))
    (hπ : SurvivingCuts t π) : IntervalComposition J where
  parts := π.parts
  parts_pos := π.parts_pos
  cut := fun k => t.contractPosition (π.cut k) (hπ k)
  strict := by
    intro a b hab
    apply t.expandPosition_strict.lt_iff_lt.mp
    rw [t.expand_contractPosition, t.expand_contractPosition]
    exact π.strict hab
  first := by
    apply t.expandPosition_strict.injective
    rw [t.expand_contractPosition]
    exact π.first
  last := by
    apply t.expandPosition_strict.injective
    rw [t.expand_contractPosition]
    exact π.last

theorem contract_expandComposition (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J) :
    contractComposition t (expandComposition t π) (expandComposition_survives t π) = π := by
  apply eq_of_parts_cut (π := contractComposition t (expandComposition t π)
    (expandComposition_survives t π)) (ρ := π) rfl
  apply heq_of_eq
  funext k
  exact t.contract_expandPosition (π.cut k)

theorem expand_contractComposition (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition (t.expandInterval J))
    (hπ : SurvivingCuts t π) : expandComposition t (contractComposition t π hπ) = π := by
  apply eq_of_parts_cut (π := expandComposition t (contractComposition t π hπ)) (ρ := π) rfl
  apply heq_of_eq
  funext k
  exact t.expand_contractPosition (π.cut k) (hπ k)

/-- Bijection of the complete raw composition types with every original
composition whose cuts survive. No unary or zero-weight term is discarded. -/
def survivingCompositionEquiv (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) :
    IntervalComposition J ≃ {π : IntervalComposition (t.expandInterval J) // SurvivingCuts t π} where
  toFun π := ⟨expandComposition t π, expandComposition_survives t π⟩
  invFun π := contractComposition t π.val π.property
  left_inv := contract_expandComposition t
  right_inv π := Subtype.ext (expand_contractComposition t π.val π.property)

theorem expandComposition_part (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J) (k : Fin π.parts) :
    (expandComposition t π).part k = t.expandInterval (π.part k) := rfl

theorem expandComposition_nearTriple (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J) (k : Fin (π.parts - 1)) :
    (expandComposition t π).nearTriple k = t.expandTriple (π.nearTriple k) := rfl

theorem expandComposition_farTriple (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J) (k : Fin (π.parts - 1)) :
    (expandComposition t π).farTriple k = t.expandTriple (π.farTriple k) := rfl

/-- If one child contains the whole critical arc, each cut lies before its
left endpoint or after its right endpoint. Consecutive cut indices leave
no third possibility. -/
theorem survivingCuts_of_containing_child (t : IncreasingBoundaryTriple n)
    {I : BoundaryInterval n} (π : IntervalComposition I) (k : Fin π.parts)
    (hk : (π.part k).left ≤ t.lower ∧ t.upper ≤ (π.part k).right) :
    SurvivingCuts t π := by
  intro j
  by_cases hj : j.val ≤ k.val
  · left
    exact le_trans (π.strict.monotone (show j ≤ k.castSucc from hj)) hk.1
  · right
    have hs : k.succ ≤ j := by change k.val + 1 ≤ j.val; omega
    exact le_trans hk.2 (π.strict.monotone hs)

/-- Conversely, the child covering the critical left endpoint must reach
the critical right endpoint because its next cut survives the deletion. -/
theorem containing_child_of_survivingCuts (t : IncreasingBoundaryTriple n)
    {I : BoundaryInterval n} (π : IntervalComposition I)
    (hI : I.left ≤ t.lower ∧ t.upper ≤ I.right) (hπ : SurvivingCuts t π) :
    ∃ k : Fin π.parts, (π.part k).left ≤ t.lower ∧ t.upper ≤ (π.part k).right := by
  have hr : t.lower < I.right := lt_of_lt_of_le
    (lt_trans t.lower_middle t.middle_upper) hI.2
  obtain ⟨k, hkl, hkr⟩ := π.exists_halfOpen_part t.lower hI.1 hr
  refine ⟨k, hkl, ?_⟩
  rcases hπ k.succ with h | h
  · exact False.elim ((not_le_of_gt hkr) h)
  · exact h

theorem survivingCuts_iff_containing_child (t : IncreasingBoundaryTriple n)
    {I : BoundaryInterval n} (π : IntervalComposition I)
    (hI : I.left ≤ t.lower ∧ t.upper ≤ I.right) :
    SurvivingCuts t π ↔
      ∃ k : Fin π.parts, (π.part k).left ≤ t.lower ∧ t.upper ≤ (π.part k).right := by
  constructor
  · exact containing_child_of_survivingCuts t π hI
  · rintro ⟨k, hk⟩
    exact survivingCuts_of_containing_child t π k hk

/-- Source propagation correspondence: every contracted composition
corresponds to exactly one original composition with a containing child.
The separate positive-interval uniqueness theorem makes that child unique. -/
def containingCompositionEquiv (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right) :
    IntervalComposition J ≃ {π : IntervalComposition (t.expandInterval J) //
      ∃ k : Fin π.parts, (π.part k).left ≤ t.lower ∧ t.upper ≤ (π.part k).right} where
  toFun π := ⟨expandComposition t π,
    containing_child_of_survivingCuts t (expandComposition t π)
      ((t.expandInterval_contains J).mpr hJ) (expandComposition_survives t π)⟩
  invFun π := contractComposition t π.val
    ((survivingCuts_iff_containing_child t π.val ((t.expandInterval_contains J).mpr hJ)).mpr π.property)
  left_inv π := contract_expandComposition t π
  right_inv π := Subtype.ext (expand_contractComposition t π.val _)

end
end SM.IntervalComposition
