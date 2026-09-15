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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftDuplicationSpanningOneCutChildFactors.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- In the A-only row, the actual right adjacent child receives the starting factor. -/
theorem spanning_zero_right_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingOldEmbedding s)
        (spanningRightChild s I hI C hL hR hs)) =
      ((etaPlus - t (spanningRightNeighbor s I hI C hL hR hs)) / 2) *
        b0 (spanningRightChild s I hI C hL hR hs) := by
  let K := spanningRightChild s I hI C hL hR hs
  have he := spanning_right_child_endpoints s I hI C hL hR hs
  have hb := spanning_neighbors_bounds s I hI C hL hR hs
  have hl : old s K.left = A s := by rw [he.1, old_self]
  have hr : B s < old s K.right := by
    have hk : s.val < K.right.val := hb.2.2.1
    change s.val + 1 < (old s K.right).val
    rw [old_val, if_neg (by omega)]
    omega
  have hc : collapse s
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K).right = K.right :=
    collapse_old s K.right
  rw [ordinaryLift_start s etaMinus etaPlus t b0 _ hl hr,
    collapse_sectionInterval s (startingOldEmbedding s) (collapse_old s), hc]
  simp only [K, spanningRightNeighbor]

/-- Every other old-image child is plain, including the actual left adjacent child. -/
theorem spanning_zero_other_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ spanningRightChild s I hI C hL hR hs) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) = b0 K := by
  have hplain : ¬ intervalContainsBoth s
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) := by
    by_cases hl : s < K.left
    · have ha : A s < old s K.left := by
        rw [← old_self s]
        exact old_strictMono s hl
      exact fun h => (not_le_of_gt ha) h.1
    · have hls : K.left < s := lt_of_le_of_ne (le_of_not_gt hl) (fun he =>
        hne (spanning_right_child_unique s I hI C hL hR hs K hK he))
      have hrs : K.right ≤ s := le_of_not_gt (fun hr => hK.2.2 s hs ⟨hls, hr⟩)
      have ha : old s K.right ≤ A s := by
        rw [← old_self s]
        exact (old_strictMono s).monotone hrs
      exact fun h => (not_le_of_gt (lt_of_le_of_lt ha (A_lt_B s))) h.2
  rw [ordinaryLift_plain s etaMinus etaPlus t b0 _ hplain,
    collapse_sectionInterval s (startingOldEmbedding s) (collapse_old s)]

/-- In the B-only row, the actual left adjacent child receives the ending factor. -/
theorem spanning_one_left_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingTailEmbedding s)
        (spanningLeftChild s I hI C hL hR hs)) =
      ((etaMinus - t (spanningLeftNeighbor s I hI C hL hR hs)) / 2) *
        b0 (spanningLeftChild s I hI C hL hR hs) := by
  let K := spanningLeftChild s I hI C hL hR hs
  have he := spanning_left_child_endpoints s I hI C hL hR hs
  have hb := spanning_neighbors_bounds s I hI C hL hR hs
  have hl : startingTailEmbedding s K.left < A s := by
    rw [startingTail_eq_old s K.left (ne_of_lt hb.2.1), ← old_self s]
    exact old_strictMono s hb.2.1
  have hr : startingTailEmbedding s K.right = B s := by rw [he.2, startingTail_self]
  have hc : collapse s
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) K).left = K.left :=
    collapse_startingTail s K.left
  rw [ordinaryLift_end s etaMinus etaPlus t b0 _ hl hr,
    collapse_sectionInterval s (startingTailEmbedding s) (collapse_startingTail s), hc]
  simp only [K, spanningLeftNeighbor]

/-- Every other tail-image child is plain, including the actual right adjacent child. -/
theorem spanning_one_other_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ spanningLeftChild s I hI C hL hR hs) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) K) = b0 K := by
  have hplain : ¬ intervalContainsBoth s
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) K) := by
    by_cases hr : K.right < s
    · have hb : startingTailEmbedding s K.right < B s := by
        rw [← startingTail_self s]
        exact (startingTailEmbedding s).strictMono hr
      exact fun h => (not_le_of_gt hb) h.2
    · have hsr : s < K.right := lt_of_le_of_ne (le_of_not_gt hr) (fun he =>
        hne (spanning_left_child_unique s I hI C hL hR hs K hK he.symm))
      have hsl : s ≤ K.left := le_of_not_gt (fun hl => hK.2.2 s hs ⟨hl, hsr⟩)
      have hb : B s ≤ startingTailEmbedding s K.left := by
        rw [← startingTail_self s]
        exact (startingTailEmbedding s).monotone hsl
      exact fun h => (not_le_of_gt (lt_of_lt_of_le (A_lt_B s) hb)) h.1
  rw [ordinaryLift_plain s etaMinus etaPlus t b0 _ hplain,
    collapse_sectionInterval s (startingTailEmbedding s) (collapse_startingTail s)]

/-- The complete A-only child product has just the actual right-child multiplier. -/
theorem spanning_zero_child_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∏ J : {J : BoundaryInterval (n + 1) //
        (spanningCutSet s I hI C hL hR hs 0).Consecutive J},
      ordinaryLift s etaMinus etaPlus t b0 J.val) =
      ((etaPlus - t (spanningRightNeighbor s I hI C hL hR hs)) / 2) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := by
  let K0 : {K : BoundaryInterval n // C.Consecutive K} :=
    ⟨spanningRightChild s I hI C hL hR hs, spanning_right_child_consecutive s I hI C hL hR hs⟩
  let m : ℚ := (etaPlus - t (spanningRightNeighbor s I hI C hL hR hs)) / 2
  calc
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        ordinaryLift s etaMinus etaPlus t b0
          (OrderedBoundaryTransport.interval (startingOldEmbedding s) K.val) :=
      (Fintype.prod_equiv (spanningChildrenZeroEquiv s I hI C hL hR hs) _ _ (fun _ => rfl)).symm
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        (if K = K0 then m else 1) * b0 K.val := by
      apply Finset.prod_congr rfl
      intro K hK
      by_cases he : K = K0
      · subst K
        rw [if_pos rfl]
        exact spanning_zero_right_child_factor s I hI C hL hR hs etaMinus etaPlus t b0
      · rw [if_neg he, one_mul]
        exact spanning_zero_other_child_factor s I hI C hL hR hs etaMinus etaPlus t b0
          K.val K.property (fun h => he (Subtype.ext h))
    _ = (∏ K : {K : BoundaryInterval n // C.Consecutive K}, if K = K0 then m else 1) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := Finset.prod_mul_distrib
    _ = _ := by simp [m]

/-- The complete B-only child product has just the actual left-child multiplier. -/
theorem spanning_one_child_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∏ J : {J : BoundaryInterval (n + 1) //
        (spanningCutSet s I hI C hL hR hs 1).Consecutive J},
      ordinaryLift s etaMinus etaPlus t b0 J.val) =
      ((etaMinus - t (spanningLeftNeighbor s I hI C hL hR hs)) / 2) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := by
  let K0 : {K : BoundaryInterval n // C.Consecutive K} :=
    ⟨spanningLeftChild s I hI C hL hR hs, spanning_left_child_consecutive s I hI C hL hR hs⟩
  let m : ℚ := (etaMinus - t (spanningLeftNeighbor s I hI C hL hR hs)) / 2
  calc
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        ordinaryLift s etaMinus etaPlus t b0
          (OrderedBoundaryTransport.interval (startingTailEmbedding s) K.val) :=
      (Fintype.prod_equiv (spanningChildrenOneEquiv s I hI C hL hR hs) _ _ (fun _ => rfl)).symm
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        (if K = K0 then m else 1) * b0 K.val := by
      apply Finset.prod_congr rfl
      intro K hK
      by_cases he : K = K0
      · subst K
        rw [if_pos rfl]
        exact spanning_one_left_child_factor s I hI C hL hR hs etaMinus etaPlus t b0
      · rw [if_neg he, one_mul]
        exact spanning_one_other_child_factor s I hI C hL hR hs etaMinus etaPlus t b0
          K.val K.property (fun h => he (Subtype.ext h))
    _ = (∏ K : {K : BoundaryInterval n // C.Consecutive K}, if K = K0 then m else 1) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := Finset.prod_mul_distrib
    _ = _ := by simp [m]

end
end SM.SoftDuplication
