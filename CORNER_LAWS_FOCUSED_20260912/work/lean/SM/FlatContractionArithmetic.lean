import SM.GermTurnSigns
import SM.NamedWallPredicates
import SM.FusionIndices
import SM.DeletionG1
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
import SM.IntegerSingleTripleResponse
import SM.UnorderedCriticalTriple
import SM.UnorderedIntegerSingleTripleResponse
import SM.FlatBoundaryPositions
import SM.FlatAffineSigns
import SM.IncidentFlatGapTuples
import SM.FlatIntegerFactors
import SM.FlatIncidentResponse
import SM.FlatIncidentAllSizes

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/FlatContractionArithmetic.body.lean (prototype FlatSourceResponse, kernel session 25627, receipt
FlatSourceResponse-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section

theorem consecutive_erased_one {n : ℕ} (k : Fin n) (h0 : 0 < k.val) (hLast : k.val + 1 < n) :
    (consecutiveBoundaryTriple k h0 hLast).erasedInteriorCount = 1 := by
  dsimp [IncreasingBoundaryTriple.erasedInteriorCount, consecutiveBoundaryTriple]
  omega

theorem consecutive_contracted_size {q : ℕ} (k : Fin (q + 1))
    (h0 : 0 < k.val) (hLast : k.val + 1 < q + 1) :
    (consecutiveBoundaryTriple k h0 hLast).contractedSize = q := by
  unfold IncreasingBoundaryTriple.contractedSize
  rw [consecutive_erased_one]
  omega

variable {q : ℕ} [NeZero q]

/-- The actual deletion root is the surviving old root, expressed in the
child's cyclic labels. Its natural representative is proved before casting. -/
theorem nonincident_fusionIndex_eq (g j : ZMod (q + 1)) (k : Fin (q + 1))
    (h0 : 0 < k.val) (hLast : k.val + 1 < q + 1)
    (hk : boundaryIndex g k = j) (hroot : ¬ incident j g) :
    fusionIndex j g = ((q - k.val - 1 : ℕ) : ZMod q) := by
  have hj : g ≠ j := fun he => hroot (Or.inr he)
  have he : g + (k.val : ZMod (q + 1)) + 1 = j := hk
  have hq : (q : ZMod (q + 1)) + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using ZMod.natCast_self (q + 1)
  have hc : g - (j + 1) = ((q - k.val - 1 : ℕ) : ZMod (q + 1)) := by
    rw [Nat.cast_sub (by omega : 1 ≤ q - k.val), Nat.cast_sub (by omega : k.val ≤ q), Nat.cast_one]
    linear_combination he - hq
  have hv : (g - (j + 1)).val = q - k.val - 1 := by
    rw [hc, ZMod.val_natCast_of_lt (by omega)]
  rw [fusionIndex, if_neg hj, hv]

theorem nonincident_fusionIndex_cut_relation (g j : ZMod (q + 1)) (k : Fin (q + 1))
    (h0 : 0 < k.val) (hLast : k.val + 1 < q + 1)
    (hk : boundaryIndex g k = j) (hroot : ¬ incident j g) :
    fusionIndex j g + ((k.val + 1 : ℕ) : ZMod q) = 0 := by
  rw [nonincident_fusionIndex_eq g j k h0 hLast hk hroot]
  rw [Nat.cast_sub (by omega : 1 ≤ q - k.val), Nat.cast_sub (by omega : k.val ≤ q),
    Nat.cast_add, Nat.cast_one, ZMod.natCast_self]
  ring

/-- Exact representatives for the cyclic shift across a cut. Both intervals
include their boundary cases; all natural subtractions have proved bounds. -/
theorem zmod_cut_shift_val (k : ℕ) (hk : k < q) (u a : ZMod q)
    (ha : a + ((k + 1 : ℕ) : ZMod q) = 0) :
    (u + a).val = if (u - 1).val < k then (u - 1).val + q - k else (u - 1).val - k := by
  have hv : (u - 1).val < q := ZMod.val_lt _
  have hu : ((u - 1).val : ZMod q) = u - 1 := ZMod.natCast_zmod_val _
  have ha' : a + (k : ZMod q) + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc] using ha
  have he : u + a = ((u - 1).val : ZMod q) - (k : ZMod q) := by
    linear_combination ha' - hu
  by_cases h : (u - 1).val < k
  · rw [if_pos h]
    have hc : u + a = (((u - 1).val + q - k : ℕ) : ZMod q) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]
      exact he
    rw [hc, ZMod.val_natCast_of_lt (by omega)]
  · rw [if_neg h]
    have hc : u + a = (((u - 1).val - k : ℕ) : ZMod q) := by
      rw [Nat.cast_sub (by omega)]
      exact he
    rw [hc, ZMod.val_natCast_of_lt (by omega)]

end
end SM
