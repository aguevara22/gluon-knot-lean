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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/ContractionOutput.body.lean (prototype UnorderedIntegerSingleTripleResponse, kernel session 17021, receipt
UnorderedIntegerSingleTripleResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- The expansion of complete raw compositions is injective, including unary ones. -/
theorem expandComposition_injective (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) :
    Function.Injective (expandComposition t (J := J)) := by
  intro π ρ he
  exact (survivingCompositionEquiv t J).injective (Subtype.ext he)

theorem mem_range_expandComposition (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) (π : IntervalComposition (t.expandInterval J)) :
    π ∈ Set.range (expandComposition t (J := J)) ↔ SurvivingCuts t π := by
  constructor
  · rintro ⟨ρ, rfl⟩
    exact expandComposition_survives t ρ
  · intro hπ
    exact ⟨contractComposition t π hπ, expand_contractComposition t π hπ⟩

variable {R : Type*} [AddCommMonoid R]

/-- Reindex the entire response sum. Only zero responses outside the surviving
range are discarded; unary and all original zero-weight terms remain included. -/
theorem sum_composition_expansion (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (f : IntervalComposition (t.expandInterval J) → R)
    (hzero : ∀ π, ¬ SurvivingCuts t π → f π = 0) :
    (∑ π : IntervalComposition J, f (expandComposition t π)) =
      ∑ π : IntervalComposition (t.expandInterval J), f π := by
  apply Fintype.sum_of_injective (expandComposition t)
    (expandComposition_injective t J)
  · intro π hπ
    exact hzero π (fun h => hπ ((mem_range_expandComposition t J π).mpr h))
  · intro π
    rfl

end
end SM.IntervalComposition

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- The propagation formula covers every original containing interval through
the actual contraction of its retained endpoints. -/
theorem farOnlyCoordinates_response_containing (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    (I : BoundaryInterval n) (hI : I.left ≤ t.lower ∧ t.upper ≤ I.right) :
    farOnlyCoordinates H₂ I - farOnlyCoordinates H₁ I =
      (farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval) *
        farOnlyCoordinates (contractedTripleArray t H₁)
          (t.contractInterval I (Or.inl hI.1) (Or.inr hI.2)) := by
  let J := t.contractInterval I (Or.inl hI.1) (Or.inr hI.2)
  have he : t.expandInterval J = I := t.expand_contractInterval I _ _
  have hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right :=
    (t.expandInterval_contains J).mp (by simpa only [he] using hI)
  simpa only [he] using farOnlyCoordinates_contraction_propagation t H₁ H₂ hH J hJ

/-- Apply the completed inverse propagation to a complete far transform with
independent coefficient arrays. The parent must properly contain the critical
span so its coefficient formula is unchanged. No response premise is assumed. -/
theorem farTransform_contraction_response (t : IncreasingBoundaryTriple n)
    (H₁ H₂ K₁ K₂ : TripleArray n R)
    (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    (hK : ∀ u, u ≠ t → K₁ u = K₂ u)
    (J : BoundaryInterval t.contractedSize)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)
    (hne : J ≠ t.contractedLeaf) :
    farTransform K₂ (farOnlyCoordinates H₂) (t.expandInterval J) -
      farTransform K₁ (farOnlyCoordinates H₁) (t.expandInterval J) =
      (farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval) *
        farTransform (contractedTripleArray t K₁)
          (farOnlyCoordinates (contractedTripleArray t H₁)) J := by
  classical
  let s := farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval
  have hI : t.expandInterval J ≠ t.spanInterval := by
    intro he
    exact hne (t.expandInterval_injective (he.trans t.expandInterval_contractedLeaf.symm))
  let f (π : IntervalComposition (t.expandInterval J)) :=
    π.nearFarWeight 0 K₁ *
      ((∏ k : Fin π.parts, farOnlyCoordinates H₂ (π.part k)) -
        ∏ k : Fin π.parts, farOnlyCoordinates H₁ (π.part k))
  have hfzero (π : IntervalComposition (t.expandInterval J))
      (hπ : ¬ IntervalComposition.SurvivingCuts t π) : f π = 0 := by
    have hp := nonsurviving_child_product_unchanged t H₁ H₂ hH π hπ
    simp only [f, hp, sub_self, mul_zero]
  have hreindex := IntervalComposition.sum_composition_expansion t J f hfzero
  unfold farTransform nearFarTransform
  rw [← Finset.sum_sub_distrib]
  have hd :
      (∑ π : IntervalComposition (t.expandInterval J),
        ((π.nearFarWeight 0 K₂ * ∏ k : Fin π.parts, farOnlyCoordinates H₂ (π.part k)) -
          (π.nearFarWeight 0 K₁ * ∏ k : Fin π.parts, farOnlyCoordinates H₁ (π.part k)))) =
      ∑ π : IntervalComposition (t.expandInterval J), f π := by
    apply Finset.sum_congr rfl
    intro π _
    rw [← π.farWeight_unchanged_off_span t K₁ K₂ hK hI]
    dsimp only [f]
    ring
  rw [hd, ← hreindex, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π _
  have hp := expanded_child_product_response t H₁ H₂ hH π hJ s
    (fun k hkl hkr => farOnlyCoordinates_contraction_propagation t H₁ H₂ hH
      (π.part k) ⟨hkl, hkr⟩)
  change (IntervalComposition.expandComposition t π).nearFarWeight 0 K₁ *
    ((∏ k : Fin π.parts, farOnlyCoordinates H₂ (t.expandInterval (π.part k))) -
      ∏ k : Fin π.parts, farOnlyCoordinates H₁ (t.expandInterval (π.part k))) = _
  rw [hp]
  change π.nearFarWeight 0 (contractedTripleArray t K₁) *
    (s * ∏ k : Fin π.parts, farOnlyCoordinates (contractedTripleArray t H₁) (π.part k)) = _
  ring

/-- Reversing the far coefficients gives the barred output response on every
properly containing interval, with the same source jump and complete output. -/
theorem farOnlyOutput_contraction_response (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    (J : BoundaryInterval t.contractedSize)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)
    (hne : J ≠ t.contractedLeaf) :
    farOnlyOutput H₂ (t.expandInterval J) - farOnlyOutput H₁ (t.expandInterval J) =
      (farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval) *
        farOnlyOutput (contractedTripleArray t H₁) J := by
  exact farTransform_contraction_response t H₁ H₂ (-H₁) (-H₂) hH
    (fun u hu => congrArg Neg.neg (hH u hu)) J hJ hne

/-- Proper contraction gives the full-output factorization on the exact full
boundary intervals. The arity of the contracted polygon is proved from properness. -/
theorem farOnlyOutput_full_contraction (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    (hn : 3 ≤ n) (hproper : t.spanInterval ≠ fullBoundaryInterval hn) :
    farOnlyOutput H₂ (fullBoundaryInterval hn) - farOnlyOutput H₁ (fullBoundaryInterval hn) =
      (farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval) *
        farOnlyOutput (contractedTripleArray t H₁)
          (fullBoundaryInterval (t.contractedSize_of_proper hn hproper)) := by
  let J := fullBoundaryInterval (t.contractedSize_of_proper hn hproper)
  have he : t.expandInterval J = fullBoundaryInterval hn := t.expandInterval_full hn hproper
  have hc : (fullBoundaryInterval hn).left ≤ t.lower ∧ t.upper ≤ (fullBoundaryInterval hn).right := by
    constructor
    · change 0 ≤ t.lower.val
      omega
    · change t.upper.val ≤ n - 1
      have := t.upper.isLt
      omega
  have hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right :=
    (t.expandInterval_contains J).mp (by simpa only [he] using hc)
  have hne : J ≠ t.contractedLeaf := by
    intro hj
    have hi : t.expandInterval J = t.spanInterval := hj ▸ t.expandInterval_contractedLeaf
    exact hproper (hi.symm.trans he)
  simpa only [he] using farOnlyOutput_contraction_response t H₁ H₂ hH J hJ hne

end
end SM
