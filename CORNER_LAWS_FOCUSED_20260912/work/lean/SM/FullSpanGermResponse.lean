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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/FullSpanGermResponse.body.lean (prototype UnorderedIntegerSingleTripleResponse, kernel session 17021, receipt
UnorderedIntegerSingleTripleResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The actual rooted tree coefficients satisfy the full-span response on
both sufficiently close punctured sides of the genuine continuous germ. All
four gap values are evaluated at the wall center. This establishes the displayed
full-span identity; the proper-span contraction branch is separate. -/
theorem full_span_tree_response (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g})
    (hspan : t.spanInterval = fullBoundaryInterval hn)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord w.center g t.lower = p + x • ω)
    (hy : boundaryWord w.center g t.middle = p + y • ω)
    (hz : boundaryWord w.center g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn : R) -
          (treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn : R) =
          ((geometricBoundaryArray (R := R) (w.curve sPlus) g t -
            geometricBoundaryArray (w.curve sMinus) g t) * ⅟ (2 : R)) *
            ((wallGapU (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
              wallGapU (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)) +
             (wallGapV (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
              wallGapV (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z))) := by
  obtain ⟨δ, hδ, hrad, hs⟩ := w.boundary_values_stable_near_center (R := R) g t hZ
  refine ⟨δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hsMinus := hs sMinus hnearMinus
  have hsPlus := hs sPlus hnearPlus
  have hleft : ¬ (t.leftInterval.left ≤ t.lower ∧ t.upper ≤ t.leftInterval.right) := by
    rintro ⟨_, hr⟩
    exact (not_le_of_gt t.middle_upper) hr
  have hright : ¬ (t.rightInterval.left ≤ t.lower ∧ t.upper ≤ t.rightInterval.right) := by
    rintro ⟨hl, _⟩
    exact (not_le_of_gt t.lower_middle) hl
  have hL := hsMinus.2.2 t.leftInterval hleft
  have hR := hsMinus.2.2 t.rightInterval hright
  have hc := geometric_critical_output_response w.center g t
    (geometricBoundaryArray (R := R) (w.curve sMinus) g)
    (geometricBoundaryArray (w.curve sPlus) g) hsMinus.1 hsPlus.1
    p ω x y z hx hy hz hyx hzy hzx
  rw [hspan] at hc
  rw [treeCoefficient_farOnly (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn,
    treeCoefficient_farOnly (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn]
  simpa only [wallGapU, wallGapV, hL, hR] using hc

end
end SM.WallGerm
