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
import SM.FarOnlyOutputLocality
import SM.BoundaryArrayStability
import SM.WallArrayNeighborhood
import SM.WallGapValues
import SM.BoundaryGapGates
import SM.GeometricGapResponse
import SM.ContractedGeometricArray
import SM.GeometricProperResponse
import SM.ProperSpanGermResponse
import SM.FullSpanGermResponse
import SM.CriticalAffineData
import SM.SignedCriticalJump
import SM.SingleTripleTreeResponse
import SM.RestrictedCriticalG1
import SM.IntegerCriticalGaps

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/IntegerSingleTripleResponse.body.lean (prototype UnorderedIntegerSingleTripleResponse, kernel session 17021, receipt
UnorderedIntegerSingleTripleResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
local instance : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)

theorem geometricBoundaryArray_intCast {R : Type*} [CommRing R]
    (P : LabelledTuple n) (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    ((geometricBoundaryArray (R := ℤ) P g t : ℤ) : R) =
      geometricBoundaryArray (R := R) P g t := by
  simp only [geometricBoundaryArray, Int.cast_id]

/-- Recover the exact integer jump from its faithful rational half-jump.
Multiplication by two avoids imposing integer division conventions. -/
theorem integer_jump_of_rat_half (A B d : ℤ)
    (h : ((A : ℚ) - (B : ℚ)) * ⅟ (2 : ℚ) = (d : ℚ)) : A - B = 2 * d := by
  have he : (A : ℚ) - (B : ℚ) = 2 * (d : ℚ) := by
    rw [← h, mul_left_comm, mul_invOf_self, mul_one]
  exact_mod_cast he

namespace WallGerm
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero
attribute [local instance] Classical.propDecidable

/-- Integer single-triple response for every valid affine representation.
The rational response is specialized faithfully; only complete gap outputs,
never the inverse coordinates, are asserted to be integral. -/
theorem single_triple_integer_response_of_affine (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g})
    (hZc : concurrenceTriples w.center = ∅)
    (hchange : w.SignChanges (fun P => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ)))
    (p ω : Plane) (x y z : ℝ) (hω : ω ≠ 0)
    (hx : boundaryWord w.center g t.lower = p + x • ω)
    (hy : boundaryWord w.center g t.middle = p + y • ω)
    (hz : boundaryWord w.center g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (geometricBoundaryArray (R := ℤ) (w.curve sPlus) g t -
          geometricBoundaryArray (R := ℤ) (w.curve sMinus) g t = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn =
          d *
            (if hp : t.spanInterval ≠ fullBoundaryInterval hn then
              (criticalGapUInteger w.center g t hZ t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapUInteger w.center g t hZ t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)) *
                treeCoefficient (contractedWordTuple w.center g t) (contractedWord_G1 w.center g t hZ) 0
                  (t.contractedSize_of_proper hn hp)
            else
              (criticalGapUInteger w.center g t hZ t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapUInteger w.center g t hZ t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)) +
              (criticalGapVInteger w.center g t hZ t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapVInteger w.center g t hZ t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)))) := by
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_tree_response_of_affine (R := ℚ) g hn t hZ hZc hchange
      p ω x y z hω hx hy hz hyx hzy hzx
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  refine ⟨?_, ?_⟩
  · apply integer_jump_of_rat_half
    simpa only [geometricBoundaryArray_intCast] using hr.1
  · apply Int.cast_injective (α := ℚ)
    by_cases hp : t.spanInterval ≠ fullBoundaryInterval hn
    · rw [dif_pos hp] at hr ⊢
      simpa only [Int.cast_sub, Int.cast_mul, criticalGapUInteger_cast] using hr.2
    · rw [dif_neg hp] at hr ⊢
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_add,
        criticalGapUInteger_cast, criticalGapVInteger_cast] using hr.2

end WallGerm
end
end SM
