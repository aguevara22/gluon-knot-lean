import Mathlib.Data.List.Nodup
import SM.CrossingTransport
import SM.FiniteChiStability
import Mathlib.Topology.Order.LeftRightNhds
import SM.WeakTopology
import SM.WallSegmentStability
import SM.CuspParameters
import Mathlib.Data.Fin.Tuple.Basic
import SM.SinglePointTriple
import SM.CriticalSourceResponse
import Mathlib.Tactic
import SM.SegmentStability
import SM.G1Consequences
import SM.CrossingCriterion
import SM.ContinuousGeometry
import Mathlib.Topology.Instances.Sign
import SM.GenericTopology
import SM.CyclicChambers
import SM.PairVisits
import SM.Traversal
import SM.GaussCyclicGap
import Mathlib.Tactic.NormNum
import SM.BoundaryTripleSupports
import SM.CanonicalTripleSigns
import SM.SoftInsertionIndices
import SM.SoftInsertionSuccessors
import SM.SoftInsertionTuple
import SM.SoftParentEdges
import SM.SoftInheritedParameters
import SM.SoftParentPairStability
import SM.SoftLocalDeterminants
import SM.SoftFamilyG1
import SM.SoftFamilyLocalCrossing
import SM.SoftEdgeAvoidance
import SM.SoftCrossingClassification
import SM.SoftFamilyG2
import SM.SoftCrossingTransport
import SM.SoftParentOrder
import SM.SoftVisitOrder
import SM.SoftGaussLists

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CycleFiltering.body.lean (prototype SoftFamilyAssembly, kernel session 44274, receipt
SoftFamilyAssembly-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace List

variable {α : Type*}

/-- Filtering respects cyclic rotation, even when the retained prefix or
suffix is empty and even when list entries repeat. -/
theorem IsRotated.filter {l l' : List α} (h : l ~r l') (p : α → Bool) :
    l.filter p ~r l'.filter p := by
  obtain ⟨k, hk, rfl⟩ := isRotated_iff_mod.mp h
  rw [rotate_eq_drop_append_take hk, filter_append]
  have hsplit : l.filter p = (l.take k).filter p ++ (l.drop k).filter p := by
    rw [← filter_append, take_append_drop]
  rw [hsplit]
  exact isRotated_append

end List

namespace Cycle

variable {α β : Type*}

/-- Retain exactly the entries satisfying p in their cyclic order. The
quotient construction uses the proved rotation compatibility of List.filter. -/
def filter (p : α → Bool) : Cycle α → Cycle α :=
  Quotient.map' (List.filter p) (fun _ _ h => h.filter p)

@[simp]
theorem filter_coe (p : α → Bool) (l : List α) :
    filter p (l : Cycle α) = (l.filter p : Cycle α) := rfl

@[simp]
theorem filter_nil (p : α → Bool) : filter p (nil : Cycle α) = nil := rfl

@[simp]
theorem mem_filter {p : α → Bool} {a : α} {s : Cycle α} :
    a ∈ s.filter p ↔ a ∈ s ∧ p a :=
  Quotient.inductionOn' s (by simp)

/-- Filtering by a property of the mapped letter commutes with the letter
map. No injectivity is required, so this also applies when two visits carry
the same crossing label. -/
theorem filter_map (p : β → Bool) (f : α → β) (s : Cycle α) :
    (s.map f).filter p = (s.filter (fun a => p (f a))).map f := by
  induction s using Quotient.inductionOn' with
  | _ l =>
    change (((l.map f).filter p : List β) : Cycle β) =
      (((l.filter (fun a => p (f a))).map f : List β) : Cycle β)
    exact congrArg (fun t : List β => (t : Cycle β)) List.filter_map

@[simp]
theorem filter_filter (p q : α → Bool) (s : Cycle α) :
    (s.filter q).filter p = s.filter (fun a => p a && q a) := by
  induction s using Quotient.inductionOn' with
  | _ l =>
    change (((l.filter q).filter p : List α) : Cycle α) =
      ((l.filter (fun a => p a && q a) : List α) : Cycle α)
    exact congrArg (fun t : List α => (t : Cycle α)) List.filter_filter

/-- A filter retaining every occurring entry leaves the cycle unchanged. -/
theorem filter_eq_self (p : α → Bool) (s : Cycle α) :
    (∀ a ∈ s, p a) → s.filter p = s :=
  Quotient.inductionOn' s fun l h =>
    congrArg (fun t : List α => (t : Cycle α)) (List.filter_eq_self.mpr h)

/-- Removing visits cannot introduce repetitions in their cyclic sequence. -/
theorem Nodup.filter {s : Cycle α} (h : s.Nodup) (p : α → Bool) :
    (s.filter p).Nodup := by
  induction s using Quotient.inductionOn' with
  | _ l => exact List.Nodup.filter p h

end Cycle
