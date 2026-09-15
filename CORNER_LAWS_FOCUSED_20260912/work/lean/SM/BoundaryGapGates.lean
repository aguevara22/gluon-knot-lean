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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/BoundaryGapGates.body.lean (prototype UnorderedIntegerSingleTripleResponse, kernel session 17021, receipt
UnorderedIntegerSingleTripleResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Every interior cut of the actual left gap samples a noncritical triple
at each pair of endpoints. Thus nearby-array agreement transfers the wall sign
identity to its complete composition gate, even though the nearby points need
not themselves be collinear. -/
theorem boundary_left_gap_gate (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (hH : ∀ u, u ≠ t → H u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzx : z ≠ x)
    (π : IntervalComposition t.leftInterval) (k : Fin (π.parts - 1)) :
    t.fixedFarGate H (π.interiorPosition k) =
      -((((wallLeftEpsilon x y z : ℤ) : R)) * H (π.farTriple k)) * ⅟ (2 : R) := by
  have hl : t.lower < π.interiorPosition k := (π.farTriple k).lower_middle
  have hr : π.interiorPosition k < t.middle := (π.farTriple k).middle_upper
  have hu : π.interiorPosition k < t.upper := lt_trans hr t.middle_upper
  have hwhole : (⟨t.lower, π.interiorPosition k, t.upper, hl, hu⟩ : IncreasingBoundaryTriple n) ≠ t := by
    intro he
    have hm := congrArg IncreasingBoundaryTriple.middle he
    exact (ne_of_lt hr) hm
  have hgap : π.farTriple k ≠ t := by
    intro he
    have hu := congrArg IncreasingBoundaryTriple.upper he
    exact (ne_of_lt t.middle_upper) hu
  have hs : H ⟨t.lower, π.interiorPosition k, t.upper, hl, hu⟩ =
      (((wallLeftEpsilon x y z : ℤ) : R)) * H (π.farTriple k) := by
    rw [hH _ hwhole, hH _ hgap]
    exact boundary_collinear_left_sign P g t p ω x y z hx hy hz hyx hzx
      (π.interiorPosition k) hl hr
  rw [IncreasingBoundaryTriple.fixedFarGate, dif_pos ⟨hl, hu⟩, hs]

/-- The right-gap transfer retains the actual last endpoint and the source's
right epsilon orientation. The local triple differs from the critical triple
already at its first endpoint. -/
theorem boundary_right_gap_gate (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (hH : ∀ u, u ≠ t → H u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hzy : z ≠ y) (hzx : z ≠ x)
    (π : IntervalComposition t.rightInterval) (k : Fin (π.parts - 1)) :
    t.fixedFarGate H (π.interiorPosition k) =
      -((((wallRightEpsilon x y z : ℤ) : R)) * H (π.farTriple k)) * ⅟ (2 : R) := by
  have hl : t.middle < π.interiorPosition k := (π.farTriple k).lower_middle
  have hr : π.interiorPosition k < t.upper := (π.farTriple k).middle_upper
  have hd : t.lower < π.interiorPosition k := lt_trans t.lower_middle hl
  have hwhole : (⟨t.lower, π.interiorPosition k, t.upper, hd, hr⟩ : IncreasingBoundaryTriple n) ≠ t := by
    intro he
    have hm := congrArg IncreasingBoundaryTriple.middle he
    exact (ne_of_gt hl) hm
  have hgap : π.farTriple k ≠ t := by
    intro he
    have hd := congrArg IncreasingBoundaryTriple.lower he
    exact (ne_of_gt t.lower_middle) hd
  have hs : H ⟨t.lower, π.interiorPosition k, t.upper, hd, hr⟩ =
      (((wallRightEpsilon x y z : ℤ) : R)) * H (π.farTriple k) := by
    rw [hH _ hwhole, hH _ hgap]
    exact boundary_collinear_right_sign P g t p ω x y z hx hy hz hzy hzx
      (π.interiorPosition k) hl hr
  rw [IncreasingBoundaryTriple.fixedFarGate, dif_pos ⟨hd, hr⟩, hs]

end
end SM
