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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftDuplicationSpanningCutNeighbors.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- A cut at s is strictly interior in a genuinely spanning collapsed interval. -/
theorem spanning_core_cut_interior (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    s ∈ C.interior.val := by
  have hb := span_collapsed_bounds s I hL hR
  exact Finset.mem_erase.mpr ⟨ne_of_lt hb.2,
    Finset.mem_erase.mpr ⟨ne_of_gt hb.1, hs⟩⟩

/-- The actual distinguished interior cut; no neighbor data is a parameter. -/
def spanningCoreCut (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    {k : Fin n // k ∈ C.interior.val} :=
  ⟨s, spanning_core_cut_interior s I hI C hL hR hs⟩

theorem spanningCoreCut_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningCoreCut s I hI C hL hR hs).val = s := rfl

/-- The adjacent children are the existing actual near-interval constructions. -/
def spanningLeftChild (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) : BoundaryInterval n :=
  C.nearLeftInterval (spanningCoreCut s I hI C hL hR hs)

def spanningRightChild (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) : BoundaryInterval n :=
  C.nearRightInterval (spanningCoreCut s I hI C hL hR hs)

def spanningLeftNeighbor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) : Fin n :=
  (spanningLeftChild s I hI C hL hR hs).left

def spanningRightNeighbor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) : Fin n :=
  (spanningRightChild s I hI C hL hR hs).right

theorem spanning_left_child_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    C.Consecutive (spanningLeftChild s I hI C hL hR hs) :=
  C.nearLeftInterval_consecutive (spanningCoreCut s I hI C hL hR hs)

theorem spanning_right_child_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    C.Consecutive (spanningRightChild s I hI C hL hR hs) :=
  C.nearRightInterval_consecutive (spanningCoreCut s I hI C hL hR hs)

theorem spanning_left_child_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningLeftChild s I hI C hL hR hs).left = spanningLeftNeighbor s I hI C hL hR hs ∧
    (spanningLeftChild s I hI C hL hR hs).right = s :=
  ⟨rfl, C.nearAtCut_middle (spanningCoreCut s I hI C hL hR hs)⟩

theorem spanning_right_child_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningRightChild s I hI C hL hR hs).left = s ∧
    (spanningRightChild s I hI C hL hR hs).right = spanningRightNeighbor s I hI C hL hR hs :=
  ⟨C.nearAtCut_middle (spanningCoreCut s I hI C hL hR hs), rfl⟩

/-- Both actual neighboring cuts are in the full core cut set. -/
theorem spanning_neighbors_mem (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    spanningLeftNeighbor s I hI C hL hR hs ∈ C.cuts ∧
      spanningRightNeighbor s I hI C hL hR hs ∈ C.cuts :=
  ⟨(spanning_left_child_consecutive s I hI C hL hR hs).1,
    (spanning_right_child_consecutive s I hI C hL hR hs).2.1⟩

/-- In particular neither neighbor is s; the later t-values are read away from s. -/
theorem spanning_neighbors_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (collapseInterval s I hI).left ≤ spanningLeftNeighbor s I hI C hL hR hs ∧
    spanningLeftNeighbor s I hI C hL hR hs < s ∧
    s < spanningRightNeighbor s I hI C hL hR hs ∧
    spanningRightNeighbor s I hI C hL hR hs ≤ (collapseInterval s I hI).right := by
  let x := spanningCoreCut s I hI C hL hR hs
  have hm : (C.nearAtCut x).middle = s := C.nearAtCut_middle x
  have hc := spanning_neighbors_mem s I hI C hL hR hs
  exact ⟨(C.bounds _ hc.1).1,
    lt_of_lt_of_eq (C.nearAtCut x).lower_middle hm,
    lt_of_eq_of_lt hm.symm (C.nearAtCut x).middle_upper,
    (C.bounds _ hc.2).2⟩

/-- Every actual consecutive child ending at s is the specified left child. -/
theorem spanning_left_child_unique (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (K : BoundaryInterval n) (hK : C.Consecutive K) (hr : K.right = s) :
    K = spanningLeftChild s I hI C hL hR hs :=
  C.consecutive_eq_of_right hK (spanning_left_child_consecutive s I hI C hL hR hs)
    (hr.trans (spanning_left_child_endpoints s I hI C hL hR hs).2.symm)

/-- Every actual consecutive child starting at s is the specified right child. -/
theorem spanning_right_child_unique (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (K : BoundaryInterval n) (hK : C.Consecutive K) (hl : K.left = s) :
    K = spanningRightChild s I hI C hL hR hs :=
  C.consecutive_eq_of_left hK (spanning_right_child_consecutive s I hI C hL hR hs)
    (hl.trans (spanning_right_child_endpoints s I hI C hL hR hs).1.symm)

theorem spanning_children_ne (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    spanningLeftChild s I hI C hL hR hs ≠ spanningRightChild s I hI C hL hR hs := by
  intro he
  have h := congrArg BoundaryInterval.right he
  let x := spanningCoreCut s I hI C hL hR hs
  change (C.nearAtCut x).middle = (C.nearAtCut x).upper at h
  exact (ne_of_lt (C.nearAtCut x).middle_upper) h

/-- The core cut has genuine adjacent parts; this is derived, not a nonunary premise. -/
theorem spanning_core_parts_ge_two (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    2 ≤ C.toComposition.parts := by
  have hb := (C.interiorIndexEquiv.symm (spanningCoreCut s I hI C hL hR hs)).isLt
  omega

theorem spanning_core_near_positions (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    let T := C.nearAtCut (spanningCoreCut s I hI C hL hR hs)
    T.lower = spanningLeftNeighbor s I hI C hL hR hs ∧ T.middle = s ∧
      T.upper = spanningRightNeighbor s I hI C hL hR hs :=
  ⟨rfl, C.nearAtCut_middle (spanningCoreCut s I hI C hL hR hs), rfl⟩

theorem spanning_core_far_positions (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    let T := C.farAtCut (spanningCoreCut s I hI C hL hR hs)
    T.lower = (collapseInterval s I hI).left ∧ T.middle = s ∧
      T.upper = (collapseInterval s I hI).right :=
  ⟨rfl, C.farAtCut_middle (spanningCoreCut s I hI C hL hR hs), rfl⟩

/-- The source a is exactly t at the derived left neighboring cut, with no
hypothesis at the distinguished occurrence or on either rational value. -/
theorem spanning_coreNear_value (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) (t : Fin n → ℚ) :
    coreNear s t (C.nearAtCut (spanningCoreCut s I hI C hL hR hs)) =
      t (spanningLeftNeighbor s I hI C hL hR hs) :=
  coreNear_at_middle s t _ (C.nearAtCut_middle (spanningCoreCut s I hI C hL hR hs))

end
end SM.SoftDuplication
