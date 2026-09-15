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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/BoundaryGateSigns.body.lean (prototype UnorderedIntegerSingleTripleResponse, kernel session 17021, receipt
UnorderedIntegerSingleTripleResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R]

/-- The actual geometric far-array entry is the reversed-order point sign,
cast through the source integer sign into the allowed coefficient ring. -/
theorem geometricBoundaryArray_pointFarSign (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    geometricBoundaryArray (R := R) P g t =
      ((pointFarSign (boundaryWord P g t.lower) (boundaryWord P g t.middle)
        (boundaryWord P g t.upper) : ℤ) : R) := rfl

/-- The source left-gap identity at actual boundary positions and actual
geometric array entries. The intermediate vertex may be anywhere in the gap. -/
theorem boundary_collinear_left_sign (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzx : z ≠ x) (r : Fin n)
    (hl : t.lower < r) (hr : r < t.middle) :
    geometricBoundaryArray (R := R) P g
        ⟨t.lower, r, t.upper, hl, lt_trans hr t.middle_upper⟩ =
      (((wallLeftEpsilon x y z : ℤ) : R)) *
        geometricBoundaryArray P g ⟨t.lower, r, t.middle, hl, hr⟩ := by
  have hs := affine_collinear_left_gate p ω (boundaryWord P g r) x y z hyx hzx
  rw [← hx, ← hy, ← hz] at hs
  have hc := congrArg (fun s : SignType => ((s : ℤ) : R)) hs
  simpa only [geometricBoundaryArray_pointFarSign, SignType.coe_mul, Int.cast_mul] using hc

/-- The source right-gap identity retains the original physical last
endpoint and the printed orientation of epsilon_R. -/
theorem boundary_collinear_right_sign (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hzy : z ≠ y) (hzx : z ≠ x) (r : Fin n)
    (hl : t.middle < r) (hr : r < t.upper) :
    geometricBoundaryArray (R := R) P g
        ⟨t.lower, r, t.upper, lt_trans t.lower_middle hl, hr⟩ =
      (((wallRightEpsilon x y z : ℤ) : R)) *
        geometricBoundaryArray P g ⟨t.middle, r, t.upper, hl, hr⟩ := by
  have hs := affine_collinear_right_gate p ω (boundaryWord P g r) x y z hzy hzx
  rw [← hx, ← hy, ← hz] at hs
  have hc := congrArg (fun s : SignType => ((s : ℤ) : R)) hs
  simpa only [geometricBoundaryArray_pointFarSign, SignType.coe_mul, Int.cast_mul] using hc

end
end SM
