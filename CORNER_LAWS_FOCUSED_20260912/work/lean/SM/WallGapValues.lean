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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/WallGapValues.body.lean (prototype UnorderedIntegerSingleTripleResponse, kernel session 17021, receipt
UnorderedIntegerSingleTripleResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The source U switches between the exact unit array E and full B output.
Its consumers require the actual wall epsilon to be either1 or-1. -/
def wallGapU (H : TripleArray n R) (I : BoundaryInterval n) (ε : SignType) : R :=
  if ε = 1 then boundaryUnitArray I else farOnlyOutput H I

/-- The source V interchanges the same two complete interval values. -/
def wallGapV (H : TripleArray n R) (I : BoundaryInterval n) (ε : SignType) : R :=
  if ε = 1 then farOnlyOutput H I else boundaryUnitArray I

/-- Every raw composition is retained. The actual signed far gates identify
the complete weighted sum with source U through the proved inverse equation. -/
theorem cutWeightedSum_signed_inverse (f : Fin n → R) (H : TripleArray n R)
    (I : BoundaryInterval n) (ε : SignType) (hε : ε = 1 ∨ ε = -1)
    (h : ∀ π : IntervalComposition I, ∀ k : Fin (π.parts - 1),
      f (π.interiorPosition k) = -((((ε : ℤ) : R)) * H (π.farTriple k)) * ⅟ (2 : R)) :
    cutWeightedSum f (farOnlyCoordinates H) I = wallGapU H I ε := by
  rcases hε with rfl | rfl
  · rw [wallGapU, if_pos rfl]
    calc
      cutWeightedSum f (farOnlyCoordinates H) I = farTransform H (farOnlyCoordinates H) I := by
        apply cutWeightedSum_eq_farTransform
        intro π k
        simpa using h π k
      _ = boundaryUnitArray I := congrFun (farOnlyCoordinates_equation H) I
  · rw [wallGapU, if_neg (by decide)]
    change cutWeightedSum f (farOnlyCoordinates H) I = farTransform (-H) (farOnlyCoordinates H) I
    apply cutWeightedSum_eq_farTransform
    intro π k
    simpa using h π k

/-- Reversing every far gate interchanges E and B, including the unary gap
whose empty gate product remains1. -/
theorem cutWeightedSum_neg_signed_inverse (f : Fin n → R) (H : TripleArray n R)
    (I : BoundaryInterval n) (ε : SignType) (hε : ε = 1 ∨ ε = -1)
    (h : ∀ π : IntervalComposition I, ∀ k : Fin (π.parts - 1),
      f (π.interiorPosition k) = -((((ε : ℤ) : R)) * H (π.farTriple k)) * ⅟ (2 : R)) :
    cutWeightedSum (-f) (farOnlyCoordinates H) I = wallGapV H I ε := by
  rcases hε with rfl | rfl
  · rw [wallGapV, if_pos rfl]
    change cutWeightedSum (-f) (farOnlyCoordinates H) I = farTransform (-H) (farOnlyCoordinates H) I
    apply cutWeightedSum_eq_farTransform
    intro π k
    simpa using congrArg Neg.neg (h π k)
  · rw [wallGapV, if_neg (by decide)]
    calc
      cutWeightedSum (-f) (farOnlyCoordinates H) I = farTransform H (farOnlyCoordinates H) I := by
        apply cutWeightedSum_eq_farTransform
        intro π k
        simpa using congrArg Neg.neg (h π k)
      _ = boundaryUnitArray I := congrFun (farOnlyCoordinates_equation H) I

end
end SM
