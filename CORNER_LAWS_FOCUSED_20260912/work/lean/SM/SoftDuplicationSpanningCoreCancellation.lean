import SM.FiniteChiStability
import Mathlib.Topology.Order.LeftRightNhds
import SM.CrossingCriterion
import SM.ContinuousGeometry
import Mathlib.Topology.Instances.Sign
import Mathlib.Data.Fin.Tuple.Basic
import SM.SinglePointTriple
import SM.CriticalSourceResponse
import SM.InsertionIndices
import SM.RootBoundary
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import SM.InteriorCutSet
import Mathlib.Data.Subtype
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import SM.NearFar
import SM.CompositionCutSet
import SM.ConsecutiveTriples
import SM.FarOnlyOutput
import SM.ConsecutiveCuts
import SM.InteriorCutIndex
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import SM.CompositionSegments
import SM.NearFarTriangular
import SM.SegmentStability
import SM.G1Consequences
import SM.GenericTopology
import SM.CyclicChambers
import SM.SoftDuplicationIndices
import SM.SoftDuplicationCutFibers
import SM.SoftDuplicationPresentations
import SM.OrderedBoundaryTransport
import SM.SoftDuplicationStartingChildren
import SM.SoftDuplicationArrays
import SM.SoftDuplicationSpanningCutPresentations
import SM.CutSetNearFar
import SM.CutSetNearFarNeighbors
import SM.SoftDuplicationSpanningCutNeighbors
import SM.SoftDuplicationStartingGatePositions
import SM.SoftDuplicationSpanningCutGatePositions
import SM.SoftDuplicationSectionTriples
import SM.SoftDuplicationStartingGateProducts
import SM.SoftDuplicationSpanningCutGateProducts
import SM.SoftDuplicationStartingChildFactors
import SM.SoftDuplicationSpanningOneCutChildFactors
import SM.SoftDuplicationSpanningBothChildren
import SM.SoftDuplicationSpanningBothChildFactors

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftDuplicationSpanningCoreCancellation.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The actual left neighbor is strictly below s, so its sign square is covered
by the off-s hypothesis. The far value is evaluated at the actual core far triple. -/
theorem spanning_core_far_square_of_signs (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (H0 : TripleArray n ℚ) (t : Fin n → ℚ)
    (hH : ∀ T, (H0 T) ^ 2 = 1) (ht : ∀ k, k ≠ s → (t k) ^ 2 = 1) :
    (H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) ^ 2 =
      (t (spanningLeftNeighbor s I hI C hL hR hs)) ^ 2 := by
  have hb := spanning_neighbors_bounds s I hI C hL hR hs
  calc
    _ = 1 := hH _
    _ = _ := (ht _ (ne_of_lt hb.2.1)).symm

/-- Split the complete finite gate product at the actual core cut s. Multiplying
its gate (a-h)/2 by (a+h)/2 gives zero from h²=a², and the full exterior is retained. -/
theorem spanning_core_gate_cancellation (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (H0 : TripleArray n ℚ) (t : Fin n → ℚ)
    (hsq : (H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) ^ 2 =
      (t (spanningLeftNeighbor s I hI C hL hR hs)) ^ 2) :
    ((t (spanningLeftNeighbor s I hI C hL hR hs) +
      H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) / 2) *
      cutGateProduct C (coreNear s t) H0 = 0 := by
  let x0 := spanningCoreCut s I hI C hL hR hs
  let a := t (spanningLeftNeighbor s I hI C hL hR hs)
  let h := H0 (C.farAtCut x0)
  let f : {x : Fin n // x ∈ C.interior.val} → ℚ :=
    fun x => (coreNear s t (C.nearAtCut x) - H0 (C.farAtCut x)) / 2
  have hf0 : f x0 = (a - h) / 2 :=
    congrArg (fun v : ℚ => (v - h) / 2)
      (spanning_coreNear_value s I hI C hL hR hs t)
  have hp : cutGateProduct C (coreNear s t) H0 =
      f x0 * ∏ x ∈ Finset.univ.erase x0, f x :=
    (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ x0)).symm
  have hsq' : h ^ 2 = a ^ 2 := hsq
  have hc : ((a + h) / 2) * f x0 = 0 := by
    rw [hf0]
    calc
      _ = (a ^ 2 - h ^ 2) / 4 := by ring
      _ = 0 := by rw [hsq']; ring
  change ((a + h) / 2) * cutGateProduct C (coreNear s t) H0 = 0
  rw [hp, ← mul_assoc, hc, zero_mul]

/-- The same local vanishing retains the complete product of all actual child
values. No gate, exterior or child factor is required to be nonzero. -/
theorem spanning_core_summand_cancellation (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (H0 : TripleArray n ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (hsq : (H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) ^ 2 =
      (t (spanningLeftNeighbor s I hI C hL hR hs)) ^ 2) :
    ((t (spanningLeftNeighbor s I hI C hL hR hs) +
      H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) / 2) *
      C.nearFarSummand (coreNear s t) H0 b0 = 0 := by
  rw [nearFarSummand_eq_cutGateProduct, ← mul_assoc,
    spanning_core_gate_cancellation s I hI C hL hR hs H0 t hsq, zero_mul]

end
end SM.SoftDuplication
