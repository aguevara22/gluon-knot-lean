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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftDuplicationCutFibers.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Every core position between the collapsed endpoints has an actual lift
inside the child interval. Clamping a global lift to an endpoint changes
neither its collapsed value nor the interval being considered. -/
theorem exists_position_in_interval (s : Fin n) (I : BoundaryInterval (n + 1))
    (k : Fin n) (hk : collapse s I.left ≤ k ∧ k ≤ collapse s I.right) :
    ∃ p : Fin (n + 1), (I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p = k := by
  let p := old s k
  have hp : collapse s p = k := collapse_old s k
  by_cases hl : I.left ≤ p
  · by_cases hr : p ≤ I.right
    · exact ⟨p, ⟨hl, hr⟩, hp⟩
    · refine ⟨I.right, ⟨I.increasing.le, le_rfl⟩, le_antisymm ?_ hk.2⟩
      rw [← hp]
      exact collapse_monotone s (le_of_lt (lt_of_not_ge hr))
  · refine ⟨I.left, ⟨le_rfl, I.increasing.le⟩, le_antisymm hk.1 ?_⟩
    rw [← hp]
    exact collapse_monotone s (le_of_lt (lt_of_not_ge hl))

/-- Collapse the actual complete cut set, automatically removing the second
copy of s if both A and B occur. The sole degenerate interval is excluded. -/
def collapseCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (T : BoundaryCutSet I) :
    BoundaryCutSet (collapseInterval s I hI) where
  cuts := T.cuts.image (collapse s)
  left_mem := Finset.mem_image.mpr ⟨I.left, T.left_mem, rfl⟩
  right_mem := Finset.mem_image.mpr ⟨I.right, T.right_mem, rfl⟩
  bounds := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨collapse_monotone s (T.bounds p hp).1,
      collapse_monotone s (T.bounds p hp).2⟩

/-- The local fibre consists of selected physical duplicate occurrences.
Only positions inside the interval may be selected. Nonemptiness records
the core cut at s, and endpoint cuts are mandatory, not optional. -/
def CutFiberCondition (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (Q : Finset (Fin (n + 1))) : Prop :=
  (∀ p ∈ Q, collapse s p = s ∧ I.left ≤ p ∧ p ≤ I.right) ∧
  (Q.Nonempty ↔ s ∈ C.cuts) ∧
  (collapse s I.left = s → I.left ∈ Q) ∧
  (collapse s I.right = s → I.right ∈ Q)

abbrev CutFiber (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI)) :=
  {Q : Finset (Fin (n + 1)) // CutFiberCondition s I hI C Q}

/-- Extract precisely those cuts lying over the distinguished occurrence. -/
def localCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (T : BoundaryCutSet I) :
    CutFiber s I hI (collapseCuts s I hI T) :=
  ⟨T.cuts.filter (fun p => collapse s p = s), by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp
      have h := Finset.mem_filter.mp hp
      exact ⟨h.2, T.bounds p h.1⟩
    · constructor
      · rintro ⟨p, hp⟩
        have h := Finset.mem_filter.mp hp
        exact Finset.mem_image.mpr ⟨p, h.1, h.2⟩
      · intro hs
        obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hs
        exact ⟨p, Finset.mem_filter.mpr ⟨hp, he⟩⟩
    · intro hs
      exact Finset.mem_filter.mpr ⟨T.left_mem, hs⟩
    · intro hs
      exact Finset.mem_filter.mpr ⟨T.right_mem, hs⟩⟩

/-- The inverse is an explicit finite-set formula: take every nonduplicate
preimage of the core cuts inside I, then insert exactly Q. -/
def expandCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (Q : CutFiber s I hI C) : BoundaryCutSet I where
  cuts := (Finset.univ.filter (fun p =>
    (I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts ∧ collapse s p ≠ s)) ∪ Q.val
  left_mem := by
    by_cases hs : collapse s I.left = s
    · exact Finset.mem_union_right _ (Q.property.2.2.1 hs)
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨⟨le_rfl, I.increasing.le⟩, C.left_mem, hs⟩⟩
  right_mem := by
    by_cases hs : collapse s I.right = s
    · exact Finset.mem_union_right _ (Q.property.2.2.2 hs)
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨⟨I.increasing.le, le_rfl⟩, C.right_mem, hs⟩⟩
  bounds := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_filter.mp hp).2.1
    · exact (Q.property.1 p hp).2

theorem mem_expandCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (Q : CutFiber s I hI C) (p : Fin (n + 1)) :
    p ∈ (expandCuts s I hI C Q).cuts ↔
      ((I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts ∧ collapse s p ≠ s) ∨
        p ∈ Q.val := by
  simp only [expandCuts, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]

theorem collapse_expandCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (Q : CutFiber s I hI C) : collapseCuts s I hI (expandCuts s I hI C Q) = C := by
  apply BoundaryCutSet.ext
  ext k
  constructor
  · intro hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    rcases (mem_expandCuts s I hI C Q p).mp hp with hp | hp
    · exact hp.2.1
    · have hs := (Q.property.1 p hp).1
      rw [hs]
      exact Q.property.2.1.mp ⟨p, hp⟩
  · intro hk
    by_cases hs : k = s
    · have hsc : s ∈ C.cuts := hs ▸ hk
      obtain ⟨p, hp⟩ := Q.property.2.1.mpr hsc
      exact Finset.mem_image.mpr ⟨p,
        (mem_expandCuts s I hI C Q p).mpr (Or.inr hp),
        ((Q.property.1 p hp).1).trans hs.symm⟩
    · obtain ⟨p, hpb, hpc⟩ := exists_position_in_interval s I k (C.bounds k hk)
      apply Finset.mem_image.mpr
      refine ⟨p, (mem_expandCuts s I hI C Q p).mpr (Or.inl ?_), hpc⟩
      exact ⟨hpb, by simpa only [hpc] using hk, by simpa only [hpc] using hs⟩

theorem localCuts_expandCuts_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (Q : CutFiber s I hI C) :
    (localCuts s I hI (expandCuts s I hI C Q)).val = Q.val := by
  ext p
  change p ∈ (expandCuts s I hI C Q).cuts.filter (fun p => collapse s p = s) ↔ p ∈ Q.val
  constructor
  · intro hp
    obtain ⟨he, hs⟩ := Finset.mem_filter.mp hp
    rcases (mem_expandCuts s I hI C Q p).mp he with he | he
    · exact False.elim (he.2.2 hs)
    · exact he
  · intro hp
    exact Finset.mem_filter.mpr
      ⟨(mem_expandCuts s I hI C Q p).mpr (Or.inr hp), (Q.property.1 p hp).1⟩

theorem expandCuts_collapseCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (T : BoundaryCutSet I) :
    expandCuts s I hI (collapseCuts s I hI T) (localCuts s I hI T) = T := by
  apply BoundaryCutSet.ext
  ext p
  constructor
  · intro hp
    rcases (mem_expandCuts s I hI _ _ p).mp hp with hp | hp
    · obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hp.2.1
      have hqold := (collapse_eq_iff_of_ne s (collapse s p) hp.2.2 q).mp he
      have hpold := (collapse_eq_iff_of_ne s (collapse s p) hp.2.2 p).mp rfl
      exact (hqold.trans hpold.symm) ▸ hq
    · exact (Finset.mem_filter.mp hp).1
  · intro hp
    apply (mem_expandCuts s I hI _ _ p).mpr
    by_cases hs : collapse s p = s
    · exact Or.inr (Finset.mem_filter.mpr ⟨hp, hs⟩)
    · exact Or.inl ⟨T.bounds p hp, Finset.mem_image.mpr ⟨p, hp, rfl⟩, hs⟩

/-- Every actual complete child cut set is exactly a core cut set together
with its admissible local subset of A,B. Both inverse identities use the
explicit finite-set formula; no correspondence is supplied as a premise. -/
def cutFiberEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) :
    BoundaryCutSet I ≃ Σ C : BoundaryCutSet (collapseInterval s I hI), CutFiber s I hI C where
  toFun T := ⟨collapseCuts s I hI T, localCuts s I hI T⟩
  invFun CQ := expandCuts s I hI CQ.1 CQ.2
  left_inv := expandCuts_collapseCuts s I hI
  right_inv := by
    rintro ⟨C, Q⟩
    have hc := collapse_expandCuts s I hI C Q
    apply Sigma.ext hc
    apply (Subtype.heq_iff_coe_eq (by
      intro U
      change CutFiberCondition s I hI (collapseCuts s I hI (expandCuts s I hI C Q)) U ↔
        CutFiberCondition s I hI C U
      rw [hc])).mpr
    exact localCuts_expandCuts_val s I hI C Q

/-- Reindex the original complete composition domain, including the unary
composition, through the actual cut-set equivalence. -/
def compositionCutFiberEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) :
    IntervalComposition I ≃
      Σ C : BoundaryCutSet (collapseInterval s I hI), CutFiber s I hI C :=
  (IntervalComposition.cutSetEquiv I).trans (cutFiberEquiv s I hI)

/-- The local subset contains only the two physical occurrences. -/
theorem cutFiber_subset_pair (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (Q : CutFiber s I hI C) : Q.val ⊆ {A s, B s} := by
  intro p hp
  have h := (collapse_eq_s_iff s p).mp (Q.property.1 p hp).1
  simpa only [Finset.mem_insert, Finset.mem_singleton] using h

/-- No core cut at s forces the sole local presentation to be the empty set. -/
theorem cutFiber_empty_iff (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (Q : CutFiber s I hI C) : Q.val = ∅ ↔ s ∉ C.cuts := by
  rw [← Finset.not_nonempty_iff_eq_empty, Q.property.2.1]

/-- All finite sums may now be reindexed by the actual fibres. This local
instance has the same construction as the separate cut-set transform API. -/
local instance cutSetFintype {m : ℕ} [NeZero m] (I : BoundaryInterval m) :
    Fintype (BoundaryCutSet I) :=
  Fintype.ofEquiv (IntervalComposition I) (IntervalComposition.cutSetEquiv I)

theorem sum_cutFiber {R : Type*} [AddCommMonoid R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (f : BoundaryCutSet I → R) :
    (∑ T : BoundaryCutSet I, f T) =
      ∑ C : BoundaryCutSet (collapseInterval s I hI),
        ∑ Q : CutFiber s I hI C, f (expandCuts s I hI C Q) := by
  calc
    (∑ T : BoundaryCutSet I, f T) =
        ∑ CQ : (Σ C : BoundaryCutSet (collapseInterval s I hI), CutFiber s I hI C),
          f (expandCuts s I hI CQ.1 CQ.2) :=
      Fintype.sum_equiv (cutFiberEquiv s I hI) _ _
        (fun T => congrArg f (expandCuts_collapseCuts s I hI T).symm)
    _ = _ := Fintype.sum_sigma' (fun C Q => f (expandCuts s I hI C Q))

theorem sum_compositionCutFiber {R : Type*} [AddCommMonoid R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (f : IntervalComposition I → R) :
    (∑ π : IntervalComposition I, f π) =
      ∑ C : BoundaryCutSet (collapseInterval s I hI),
        ∑ Q : CutFiber s I hI C, f (expandCuts s I hI C Q).toComposition := by
  calc
    (∑ π : IntervalComposition I, f π) =
        ∑ T : BoundaryCutSet I, f T.toComposition :=
      Fintype.sum_equiv (IntervalComposition.cutSetEquiv I) _ _
        (fun π => congrArg f π.cutSet_toComposition.symm)
    _ = _ := sum_cutFiber s I hI (fun T => f T.toComposition)

end
end SM.SoftDuplication
