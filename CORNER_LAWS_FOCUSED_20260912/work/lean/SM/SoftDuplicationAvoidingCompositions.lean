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
import SM.SoftDuplicationSpanningCoreCancellation
import SM.SoftDuplicationSpanningEmptyChildren
import SM.SoftDuplicationSpanningEmptyGates
import SM.SoftDuplicationAvoiding

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftDuplicationAvoidingCompositions.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Collapse every actual cut in an avoiding interval, retaining the part
count. Strictness is derived on the closed parent interval, not supplied. -/
def collapseComposition (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I) :
    IntervalComposition (collapseInterval s I hI) where
  parts := π.parts
  parts_pos := π.parts_pos
  cut := fun k => collapse s (π.cut k)
  strict := by
    intro a b hab
    have bounds (k : Fin (π.parts + 1)) : I.left ≤ π.cut k ∧ π.cut k ≤ I.right := by
      constructor
      · rw [← π.first]
        exact π.strict.monotone (Fin.zero_le k)
      · rw [← π.last]
        exact π.strict.monotone (Fin.le_last k)
    apply lt_of_le_of_ne (collapse_monotone s (π.strict hab).le)
    intro he
    exact (ne_of_lt (π.strict hab))
      (collapse_injective_on_avoiding s I havoid (bounds a) (bounds b) he)
  first := congrArg (collapse s) π.first
  last := congrArg (collapse s) π.last

@[simp] theorem collapseComposition_parts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I) :
    (collapseComposition s I hI havoid π).parts = π.parts := rfl

@[simp] theorem collapseComposition_cut (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin (π.parts + 1)) :
    (collapseComposition s I hI havoid π).cut k = collapse s (π.cut k) := rfl

theorem collapseComposition_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I) :
    (collapseComposition s I hI havoid π).cut 0 = collapse s I.left ∧
    (collapseComposition s I hI havoid π).cut (Fin.last π.parts) = collapse s I.right :=
  ⟨congrArg (collapse s) π.first, congrArg (collapse s) π.last⟩

/-- The direct map has precisely the actual collapsed complete cut set. -/
theorem collapseComposition_cutSet (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I) :
    (collapseComposition s I hI havoid π).cutSet = collapseCuts s I hI π.cutSet := by
  apply BoundaryCutSet.ext
  change Finset.univ.image (fun k => collapse s (π.cut k)) =
    (Finset.univ.image π.cut).image (collapse s)
  rw [Finset.image_image]
  rfl

/-- The direct pointwise collapse is the previously constructed genuine
composition equivalence, proved by the complete cut set, not endpoints. -/
theorem collapseComposition_eq_avoidingCompositionEquiv (s : Fin n)
    (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I) :
    collapseComposition s I hI havoid π = (avoidingCompositionEquiv s I hI havoid) π := by
  apply IntervalComposition.cutSet_injective
  rw [collapseComposition_cutSet]
  change collapseCuts s I hI π.cutSet =
    (collapseCuts s I hI π.cutSet).toComposition.cutSet
  exact (BoundaryCutSet.toComposition_cutSet _).symm

theorem collapseComposition_part_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin π.parts) :
    ((collapseComposition s I hI havoid π).part k).left = collapse s (π.part k).left ∧
    ((collapseComposition s I hI havoid π).part k).right = collapse s (π.part k).right :=
  ⟨rfl, rfl⟩

/-- Every actual part of an avoiding composition remains avoiding. -/
theorem composition_part_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin π.parts) : ¬ ((π.part k).left ≤ A s ∧ B s ≤ (π.part k).right) := by
  intro h
  have hb := π.part_bounds k
  exact havoid ⟨le_trans hb.1 h.1, le_trans h.2 hb.2⟩

/-- The mapped child is the actual collapsed child interval; its distinct
endpoints are derived from the proved child avoidance. -/
theorem collapseComposition_part (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin π.parts) :
    (collapseComposition s I hI havoid π).part k =
      collapseInterval s (π.part k)
        (avoiding_not_duplicate s (π.part k) (composition_part_avoiding s I havoid π k)) := rfl

theorem collapseComposition_nearTriple_positions (s : Fin n)
    (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin (π.parts - 1)) :
    ((collapseComposition s I hI havoid π).nearTriple k).lower =
        collapse s (π.nearTriple k).lower ∧
    ((collapseComposition s I hI havoid π).nearTriple k).middle =
        collapse s (π.nearTriple k).middle ∧
    ((collapseComposition s I hI havoid π).nearTriple k).upper =
        collapse s (π.nearTriple k).upper := ⟨rfl, rfl, rfl⟩

theorem collapseComposition_farTriple_positions (s : Fin n)
    (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin (π.parts - 1)) :
    ((collapseComposition s I hI havoid π).farTriple k).lower =
        collapse s (π.farTriple k).lower ∧
    ((collapseComposition s I hI havoid π).farTriple k).middle =
        collapse s (π.farTriple k).middle ∧
    ((collapseComposition s I hI havoid π).farTriple k).upper =
        collapse s (π.farTriple k).upper := ⟨rfl, rfl, rfl⟩

/-- Every bounded triple in the avoiding interval is a plain triple. -/
theorem triple_plain_of_avoiding_interval (s : Fin n) (I : BoundaryInterval (n + 1))
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (T : IncreasingBoundaryTriple (n + 1)) (hL : I.left ≤ T.lower)
    (hR : T.upper ≤ I.right) : ¬ tripleContainsBoth s T := by
  intro h
  apply havoid
  rcases (triple_contains_both_iff s T).mp h with hu | hl
  · constructor
    · calc
        I.left ≤ T.lower := hL
        _ ≤ T.middle := T.lower_middle.le
        _ = A s := hu.1
    · calc
        B s = T.upper := hu.2.symm
        _ ≤ I.right := hR
  · constructor
    · calc
        I.left ≤ T.lower := hL
        _ = A s := hl.1
    · calc
        B s = T.middle := hl.2.symm
        _ ≤ T.upper := T.middle_upper.le
        _ ≤ I.right := hR

theorem nearTriple_plain_of_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin (π.parts - 1)) : ¬ tripleContainsBoth s (π.nearTriple k) := by
  apply triple_plain_of_avoiding_interval s I havoid
  · change I.left ≤ π.cut ⟨k.val, by have := k.isLt; omega⟩
    rw [← π.first]
    exact π.strict.monotone (Fin.zero_le _)
  · change π.cut ⟨k.val + 2, by have := k.isLt; omega⟩ ≤ I.right
    rw [← π.last]
    exact π.strict.monotone (Fin.le_last _)

theorem farTriple_plain_of_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin (π.parts - 1)) : ¬ tripleContainsBoth s (π.farTriple k) :=
  triple_plain_of_avoiding_interval s I havoid (π.farTriple k) le_rfl le_rfl

/-- Compatibility with any proof of plainness, including the preceding
derived one. Proof irrelevance leaves the actual collapsed positions fixed. -/
theorem collapseComposition_nearTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin (π.parts - 1)) (hplain : ¬ tripleContainsBoth s (π.nearTriple k)) :
    (collapseComposition s I hI havoid π).nearTriple k =
      collapseTriple s (π.nearTriple k) hplain := rfl

theorem collapseComposition_farTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin (π.parts - 1)) (hplain : ¬ tripleContainsBoth s (π.farTriple k)) :
    (collapseComposition s I hI havoid π).farTriple k =
      collapseTriple s (π.farTriple k) hplain := rfl

end
end SM.SoftDuplication
