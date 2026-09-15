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
import SM.OffLeafContraction
import SM.UniqueChangingChild
import SM.ContractedChildResponse
import SM.NonunaryContraction
import SM.ContractionPropagation
import SM.ContractionOutput
import SM.CollinearGateSigns
import SM.BoundaryGateSigns

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/FarOnlyOutputLocality.body.lean (prototype UnorderedIntegerSingleTripleResponse, kernel session 17021, receipt
UnorderedIntegerSingleTripleResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The full reversed-far output on J depends only on the far array inside
J. All coefficient factors and every actual child inverse value are compared
in the complete composition sum, including the unary case. -/
theorem farOnlyOutput_local (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ u : IncreasingBoundaryTriple n, J.left ≤ u.lower → u.upper ≤ J.right → H₁ u = H₂ u) :
    farOnlyOutput H₁ J = farOnlyOutput H₂ J := by
  unfold farOnlyOutput farTransform nearFarTransform
  apply Finset.sum_congr rfl
  intro π _
  have hw : π.nearFarWeight 0 (-H₁) = π.nearFarWeight 0 (-H₂) := by
    unfold IntervalComposition.nearFarWeight
    apply Finset.prod_congr rfl
    intro k _
    simp only [Pi.zero_apply, Pi.neg_apply]
    rw [h (π.farTriple k) le_rfl le_rfl]
  rw [hw]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  apply farOnlyCoordinates_local (π.part k) H₁ H₂
  intro u hl hr
  exact h u (le_trans (π.part_bounds k).1 hl) (le_trans hr (π.part_bounds k).2)

/-- Changing a single far entry leaves every full output coordinate whose
interval excludes the complete critical span unchanged. -/
theorem farOnlyOutput_unchanged_off_critical (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u)
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) :
    farOnlyOutput H₁ J = farOnlyOutput H₂ J := by
  apply farOnlyOutput_local J H₁ H₂
  intro u hl hr
  apply h u
  intro he
  subst u
  exact hJ ⟨hl, hr⟩

end
end SM
