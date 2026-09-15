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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftDuplicationAvoiding.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

theorem avoiding_not_duplicate (s : Fin n) (I : BoundaryInterval (n + 1))
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) : I ≠ duplicateInterval s := by
  intro he
  subst I
  exact havoid ⟨le_rfl, le_rfl⟩

/-- Collapse is injective on the entire closed vertex interval whenever
that interval does not contain both duplicate occurrences. -/
theorem collapse_injective_on_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    {p q : Fin (n + 1)} (hp : I.left ≤ p ∧ p ≤ I.right)
    (hq : I.left ≤ q ∧ q ≤ I.right) (he : collapse s p = collapse s q) : p = q := by
  rcases lt_trichotomy p q with h | h | h
  · obtain ⟨hpa, hqb⟩ := (collapse_eq_iff_of_lt s p q h).mp he
    exact False.elim (havoid ⟨hpa ▸ hp.1, hqb ▸ hq.2⟩)
  · exact h
  · obtain ⟨hqa, hpb⟩ := (collapse_eq_iff_of_lt s q p h).mp he.symm
    exact False.elim (havoid ⟨hqa ▸ hq.1, hpb ▸ hp.2⟩)

/-- The unique avoiding presentation is the full preimage inside I.
This formula also handles an interval ending at A or starting at B. -/
def avoidingExpandCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI)) :
    BoundaryCutSet I where
  cuts := Finset.univ.filter (fun p => (I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts)
  left_mem := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ⟨⟨le_rfl, I.increasing.le⟩, C.left_mem⟩⟩
  right_mem := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ⟨⟨I.increasing.le, le_rfl⟩, C.right_mem⟩⟩
  bounds := by intro p hp; exact (Finset.mem_filter.mp hp).2.1

theorem mem_avoidingExpandCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (p : Fin (n + 1)) : p ∈ (avoidingExpandCuts s I hI C).cuts ↔
      (I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts := by
  simp only [avoidingExpandCuts, Finset.mem_filter, Finset.mem_univ, true_and]

theorem collapse_avoidingExpandCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI)) :
    collapseCuts s I hI (avoidingExpandCuts s I hI C) = C := by
  apply BoundaryCutSet.ext
  ext k
  constructor
  · intro hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    exact ((mem_avoidingExpandCuts s I hI C p).mp hp).2
  · intro hk
    obtain ⟨p, hpb, hpc⟩ := exists_position_in_interval s I k (C.bounds k hk)
    exact Finset.mem_image.mpr ⟨p,
      (mem_avoidingExpandCuts s I hI C p).mpr ⟨hpb, hpc.symm ▸ hk⟩, hpc⟩

theorem avoidingExpandCuts_collapse (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (T : BoundaryCutSet I) : avoidingExpandCuts s I hI (collapseCuts s I hI T) = T := by
  apply BoundaryCutSet.ext
  ext p
  constructor
  · intro hp
    obtain ⟨hpb, hpc⟩ := (mem_avoidingExpandCuts s I hI _ p).mp hp
    obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hpc
    have hqp := collapse_injective_on_avoiding s I havoid (T.bounds q hq) hpb he
    exact hqp ▸ hq
  · intro hp
    exact (mem_avoidingExpandCuts s I hI _ p).mpr
      ⟨T.bounds p hp, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩

/-- An actual inverse equivalence, not an equality of cut-set cardinalities. -/
def avoidingCutSetEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) :
    BoundaryCutSet I ≃ BoundaryCutSet (collapseInterval s I hI) where
  toFun := collapseCuts s I hI
  invFun := avoidingExpandCuts s I hI
  left_inv := avoidingExpandCuts_collapse s I hI havoid
  right_inv := collapse_avoidingExpandCuts s I hI

/-- All raw compositions, including unary, survive the avoiding collapse. -/
def avoidingCompositionEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) :
    IntervalComposition I ≃ IntervalComposition (collapseInterval s I hI) :=
  ((IntervalComposition.cutSetEquiv I).trans (avoidingCutSetEquiv s I hI havoid)).trans
    (IntervalComposition.cutSetEquiv (collapseInterval s I hI)).symm

/-- The actual local subset of the full-preimage presentation. -/
def avoidingLocalCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI)) :
    CutFiber s I hI C :=
  ⟨(localCuts s I hI (avoidingExpandCuts s I hI C)).val, by
    have h := (localCuts s I hI (avoidingExpandCuts s I hI C)).property
    simpa only [collapse_avoidingExpandCuts] using h⟩

/-- Every admissible local selection gives the same avoiding presentation. -/
theorem expandCuts_eq_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (C : BoundaryCutSet (collapseInterval s I hI)) (Q : CutFiber s I hI C) :
    expandCuts s I hI C Q = avoidingExpandCuts s I hI C := by
  have h := avoidingExpandCuts_collapse s I hI havoid (expandCuts s I hI C Q)
  rw [collapse_expandCuts] at h
  exact h.symm

theorem avoidingCutFiber_unique (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (C : BoundaryCutSet (collapseInterval s I hI)) (Q : CutFiber s I hI C) :
    Q = avoidingLocalCuts s I hI C := by
  apply Subtype.ext
  calc
    Q.val = (localCuts s I hI (expandCuts s I hI C Q)).val :=
      (localCuts_expandCuts_val s I hI C Q).symm
    _ = (localCuts s I hI (avoidingExpandCuts s I hI C)).val := by
      rw [expandCuts_eq_avoiding s I hI havoid C Q]
    _ = (avoidingLocalCuts s I hI C).val := rfl

def avoidingCutFiberEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (C : BoundaryCutSet (collapseInterval s I hI)) : PUnit ≃ CutFiber s I hI C :=
  Equiv.ofBijective (fun _ => avoidingLocalCuts s I hI C) ⟨by
    intro x y _
    exact Subsingleton.elim x y, by
    intro Q
    exact ⟨PUnit.unit, (avoidingCutFiber_unique s I hI havoid C Q).symm⟩⟩

/-- The inner fibre sum has exactly the one full-preimage summand. -/
theorem sum_avoidingCutFiber {R : Type*} [AddCommMonoid R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (C : BoundaryCutSet (collapseInterval s I hI)) (f : BoundaryCutSet I → R) :
    (∑ Q : CutFiber s I hI C, f (expandCuts s I hI C Q)) = f (avoidingExpandCuts s I hI C) := by
  have he := (Fintype.sum_equiv (avoidingCutFiberEquiv s I hI havoid C)
    (fun _ : Unit => f (avoidingExpandCuts s I hI C))
    (fun Q => f (expandCuts s I hI C Q))
    (fun _ : Unit => congrArg f (expandCuts_eq_avoiding s I hI havoid C _).symm)).symm
  simpa using he

local instance avoidingCutSetFintype {m : ℕ} [NeZero m] (I : BoundaryInterval m) :
    Fintype (BoundaryCutSet I) :=
  Fintype.ofEquiv (IntervalComposition I) (IntervalComposition.cutSetEquiv I)

theorem sum_avoidingCuts {R : Type*} [AddCommMonoid R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (f : BoundaryCutSet I → R) :
    (∑ T : BoundaryCutSet I, f T) =
      ∑ C : BoundaryCutSet (collapseInterval s I hI), f (avoidingExpandCuts s I hI C) :=
  Fintype.sum_equiv (avoidingCutSetEquiv s I hI havoid) _ _
    (fun T => congrArg f (avoidingExpandCuts_collapse s I hI havoid T).symm)

end
end SM.SoftDuplication
