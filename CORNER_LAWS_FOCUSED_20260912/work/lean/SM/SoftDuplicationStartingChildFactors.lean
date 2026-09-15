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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftDuplicationStartingChildFactors.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- An increasing section of the actual collapse cannot map a genuine core
interval to the duplicate singleton. -/
theorem sectionInterval_not_duplicate (s : Fin n) (e : Fin n ↪o Fin (n + 1))
    (hsec : ∀ k, collapse s (e k) = k) (K : BoundaryInterval n) :
    OrderedBoundaryTransport.interval e K ≠ duplicateInterval s := by
  intro he
  have hc := (collapse_endpoints_eq_iff s (OrderedBoundaryTransport.interval e K)).mpr he
  change collapse s (e K.left) = collapse s (e K.right) at hc
  rw [hsec, hsec] at hc
  exact (ne_of_lt K.increasing) hc

/-- The collapsed image interval is exactly the original core interval. -/
theorem collapse_sectionInterval (s : Fin n) (e : Fin n ↪o Fin (n + 1))
    (hsec : ∀ k, collapse s (e k) = k) (K : BoundaryInterval n)
    (hI : OrderedBoundaryTransport.interval e K ≠ duplicateInterval s) :
    collapseInterval s (OrderedBoundaryTransport.interval e K) hI = K := by
  apply BoundaryInterval.eq_of_endpoints
  · exact hsec K.left
  · exact hsec K.right

/-- The old-mapped first core child receives exactly the source starting factor. -/
theorem starting_zero_first_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) (startingFirstChild s I hI C)) =
      ((etaPlus - t (startingFirstChild s I hI C).right) / 2) *
        b0 (startingFirstChild s I hI C) := by
  have h := starting_first_zero_endpoints s I hI C hL
  rw [ordinaryLift_start s etaMinus etaPlus t b0 _ h.1 h.2.2]
  have hc : collapse s
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) (startingFirstChild s I hI C)).right =
      (startingFirstChild s I hI C).right := collapse_old s _
  rw [hc, collapse_sectionInterval s (startingOldEmbedding s) (collapse_old s)]

/-- Every other old-mapped child is plain and contributes its exact core value. -/
theorem starting_zero_other_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ startingFirstChild s I hI C) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) = b0 K := by
  have hs := starting_otherChild_left_gt s I hI C hL K hK hne
  have ha : A s < old s K.left := by
    rw [← old_self s]
    exact old_strictMono s hs
  have hplain : ¬ intervalContainsBoth s
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) :=
    fun h => (not_le_of_gt ha) h.1
  rw [ordinaryLift_plain s etaMinus etaPlus t b0 _ hplain,
    collapse_sectionInterval s (startingOldEmbedding s) (collapse_old s)]

/-- Each tail-mapped core child starts at or after B, so it is plain.
The section identity is proved for this concrete map, not a caller premise. -/
theorem starting_one_core_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (K : BoundaryInterval n) (hK : C.Consecutive K) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) K) = b0 K := by
  have hs : s ≤ K.left := by
    simpa only [starting_core_left s I hI hL] using (C.bounds K.left hK.1).1
  have hb : B s ≤ startingTailEmbedding s K.left := by
    rw [← startingTail_self s]
    exact (startingTailEmbedding s).monotone hs
  have ha : A s < startingTailEmbedding s K.left := lt_of_lt_of_le (A_lt_B s) hb
  have hplain : ¬ intervalContainsBoth s
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) K) :=
    fun h => (not_le_of_gt ha) h.1
  rw [ordinaryLift_plain s etaMinus etaPlus t b0 _ hplain,
    collapse_sectionInterval s (startingTailEmbedding s) (collapse_startingTail s)]

/-- Row zero's complete child product has precisely one exceptional factor.
Finite-product factorization permits every core child value to be zero. -/
theorem starting_zero_child_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (etaMinus etaPlus : ℚ)
    (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∏ J : {J : BoundaryInterval (n + 1) //
        (startingCutSet s I hI C hL hR 0).Consecutive J},
      ordinaryLift s etaMinus etaPlus t b0 J.val) =
      ((etaPlus - t (startingFirstChild s I hI C).right) / 2) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := by
  let K0 : {K : BoundaryInterval n // C.Consecutive K} :=
    ⟨startingFirstChild s I hI C, startingFirstChild_consecutive s I hI C⟩
  let m : ℚ := (etaPlus - t (startingFirstChild s I hI C).right) / 2
  calc
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        ordinaryLift s etaMinus etaPlus t b0
          (OrderedBoundaryTransport.interval (startingOldEmbedding s) K.val) :=
      (Fintype.prod_equiv (startingChildrenZeroEquiv s I hI C hL hR) _ _ (fun _ => rfl)).symm
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        (if K = K0 then m else 1) * b0 K.val := by
      apply Finset.prod_congr rfl
      intro K hK
      by_cases he : K = K0
      · subst K
        rw [if_pos rfl]
        exact starting_zero_first_child_factor s I hI C hL etaMinus etaPlus t b0
      · rw [if_neg he, one_mul]
        exact starting_zero_other_child_factor s I hI C hL etaMinus etaPlus t b0 K.val K.property
          (fun h => he (Subtype.ext h))
    _ = (∏ K : {K : BoundaryInterval n // C.Consecutive K}, if K = K0 then m else 1) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := Finset.prod_mul_distrib
    _ = _ := by simp [m]

/-- Row one's complete child product is the core product: the additional
actual [A,B] child has value1, and every tail child is transported exactly. -/
theorem starting_one_child_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (etaMinus etaPlus : ℚ)
    (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∏ J : {J : BoundaryInterval (n + 1) //
        (startingCutSet s I hI C hL hR 1).Consecutive J},
      ordinaryLift s etaMinus etaPlus t b0 J.val) =
      ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := by
  calc
    _ = ∏ x : Unit ⊕ {K : BoundaryInterval n // C.Consecutive K},
        ordinaryLift s etaMinus etaPlus t b0
          ((startingChildrenOneEquiv s I hI C hL hR) x).val :=
      (Fintype.prod_equiv (startingChildrenOneEquiv s I hI C hL hR) _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      change (∏ _u : Unit, ordinaryLift s etaMinus etaPlus t b0 (duplicateInterval s)) *
        (∏ K : {K : BoundaryInterval n // C.Consecutive K},
          ordinaryLift s etaMinus etaPlus t b0
            (OrderedBoundaryTransport.interval (startingTailEmbedding s) K.val)) = _
      simp only [ordinaryLift_duplicate, Finset.prod_const_one, one_mul]
      apply Finset.prod_congr rfl
      intro K hK
      exact starting_one_core_child_factor s I hI C hL etaMinus etaPlus t b0 K.val K.property

end
end SM.SoftDuplication
