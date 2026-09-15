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
import SM.ContractedCompositions

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/OffLeafContraction.body.lean (prototype UnorderedIntegerSingleTripleResponse, kernel session 17021, receipt
UnorderedIntegerSingleTripleResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

namespace IncreasingBoundaryTriple

/-- Since the distinguished leaf joins adjacent positions, an interval
excluding it lies wholly on one side. There is no partially overlapping case. -/
theorem contractedInterval_side (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) :
    J.right ≤ t.contractedLeaf.left ∨ t.contractedLeaf.right ≤ J.left := by
  change ¬ (J.left.val ≤ t.lower.val ∧ t.lower.val + 1 ≤ J.right.val) at hJ
  change J.right.val ≤ t.lower.val ∨ t.lower.val + 1 ≤ J.left.val
  omega

/-- Outside the distinguished leaf expansion is a translation, hence
preserves the exact number of leaves and the formal unit-array value. -/
theorem expandInterval_leaves_off_leaf (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) :
    (t.expandInterval J).leaves = J.leaves := by
  have hj : J.left.val < J.right.val := J.increasing
  change (t.expandPosition J.right).val - (t.expandPosition J.left).val =
    J.right.val - J.left.val
  rw [expandPosition_val, expandPosition_val]
  rcases t.contractedInterval_side J hJ with h | h
  · have hr : J.right.val ≤ t.lower.val := h
    have hl : J.left.val ≤ t.lower.val := by omega
    rw [if_pos hr, if_pos hl]
  · have hl : t.lower.val + 1 ≤ J.left.val := h
    rw [if_neg (by omega), if_neg (by omega)]
    omega

/-- A subinterval of an interval excluding the leaf still excludes it. -/
theorem subinterval_off_leaf (t : IncreasingBoundaryTriple n)
    (I J : BoundaryInterval t.contractedSize)
    (hI : ¬ (I.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ I.right))
    (hJI : I.left ≤ J.left ∧ J.right ≤ I.right) :
    ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right) := by
  rintro ⟨hl, hr⟩
  exact hI ⟨hJI.1.trans hl, hr.trans hJI.2⟩

end IncreasingBoundaryTriple

namespace IntervalComposition

theorem every_cut_survives_off_leaf (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right))
    (π : IntervalComposition (t.expandInterval J)) : SurvivingCuts t π := by
  intro k
  rcases t.contractedInterval_side J hJ with h | h
  · left
    have he : t.expandPosition J.right ≤ t.lower := by
      rw [← t.expandPosition_lower]
      exact t.expandPosition_strict.monotone h
    exact (π.cut_bounds k).2.trans he
  · right
    have he : t.upper ≤ t.expandPosition J.left := by
      rw [← t.expandPosition_upper]
      exact t.expandPosition_strict.monotone h
    exact he.trans (π.cut_bounds k).1

/-- Away from the leaf every original raw composition survives, so the
correspondence covers the entire composition type, without a subtype filter. -/
def offLeafCompositionEquiv (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) :
    IntervalComposition J ≃ IntervalComposition (t.expandInterval J) where
  toFun := expandComposition t
  invFun π := contractComposition t π (every_cut_survives_off_leaf t J hJ π)
  left_inv := contract_expandComposition t
  right_inv π := expand_contractComposition t π _

end IntervalComposition

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

def contractedTripleArray (t : IncreasingBoundaryTriple n) (H : TripleArray n R) :
    TripleArray t.contractedSize R := fun u => H (t.expandTriple u)

theorem IntervalComposition.expandComposition_weight (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J) (D H : TripleArray n R) :
    (expandComposition t π).nearFarWeight D H =
      π.nearFarWeight (contractedTripleArray t D) (contractedTripleArray t H) := rfl

/-- Complete equation transport on every interval away from the new leaf.
This is proved by the raw composition bijection, retaining all gate factors. -/
theorem nearFarTransform_expanded_off_leaf (t : IncreasingBoundaryTriple n)
    (D H : TripleArray n R) (X : IntervalArray n R)
    (J : BoundaryInterval t.contractedSize)
    (hJ : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) :
    nearFarTransform (contractedTripleArray t D) (contractedTripleArray t H)
      (fun I => X (t.expandInterval I)) J = nearFarTransform D H X (t.expandInterval J) := by
  unfold nearFarTransform
  exact Fintype.sum_equiv (IntervalComposition.offLeafCompositionEquiv t J hJ) _ _ (fun _ => rfl)

theorem boundaryUnitArray_expanded_off_leaf (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) :
    boundaryUnitArray (R := R) (t.expandInterval J) = boundaryUnitArray J := by
  have he := t.expandInterval_leaves_off_leaf J hJ
  have hi := (t.expandInterval J).increasing
  have hj := J.increasing
  change (t.expandInterval J).left.val < (t.expandInterval J).right.val at hi
  change J.left.val < J.right.val at hj
  change (t.expandInterval J).right.val - (t.expandInterval J).left.val =
    J.right.val - J.left.val at he
  have hc : (t.expandInterval J).right.val = (t.expandInterval J).left.val + 1 ↔
      J.right.val = J.left.val + 1 := by omega
  simp only [boundaryUnitArray, hc]

/-- Actual inverse coordinates agree on every unchanged other child.
The induction compares the transported original equation with the unique
contracted equation, using equality only on strictly shorter children. -/
theorem farOnlyCoordinates_expanded_off_leaf (t : IncreasingBoundaryTriple n)
    (H : TripleArray n R) (J : BoundaryInterval t.contractedSize)
    (hJ : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) :
    farOnlyCoordinates H (t.expandInterval J) = farOnlyCoordinates (contractedTripleArray t H) J := by
  have he := nearFarTransform_expanded_off_leaf t 0 H (farOnlyCoordinates H) J hJ
  change nearFarTransform 0 (contractedTripleArray t H)
    (fun I => farOnlyCoordinates H (t.expandInterval I)) J =
      farTransform H (farOnlyCoordinates H) (t.expandInterval J) at he
  rw [farOnlyCoordinates_equation, boundaryUnitArray_expanded_off_leaf t J hJ] at he
  have hq := congrFun (farOnlyCoordinates_equation (contractedTripleArray t H)) J
  change nearFarTransform 0 (contractedTripleArray t H)
    (farOnlyCoordinates (contractedTripleArray t H)) J = boundaryUnitArray J at hq
  rw [nearFarTransform_eq_triangular] at he hq
  unfold triangularTransform at he hq
  have hs : (∑ π : {π : IntervalComposition J // 2 ≤ π.parts},
      π.val.nearFarWeight 0 (contractedTripleArray t H) *
        ∏ k : Fin π.val.parts, farOnlyCoordinates H (t.expandInterval (π.val.part k))) =
      ∑ π : {π : IntervalComposition J // 2 ≤ π.parts},
        π.val.nearFarWeight 0 (contractedTripleArray t H) *
          ∏ k : Fin π.val.parts, farOnlyCoordinates (contractedTripleArray t H) (π.val.part k) := by
    apply Finset.sum_congr rfl
    intro π _
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    exact farOnlyCoordinates_expanded_off_leaf t H (π.val.part k)
      (t.subinterval_off_leaf J (π.val.part k) hJ (π.val.part_bounds k))
  rw [hs] at he
  exact add_right_cancel (he.trans hq.symm)
termination_by J.leaves
decreasing_by exact π.val.part_leaves_lt π.property k

end
end SM
