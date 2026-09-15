import SM.GaussWord
import SM.SortedCyclicGap
import Mathlib.Tactic
import SM.GaussCyclicGap
import Mathlib.GroupTheory.Perm.Cycle.Basic
import SM.CrossingPair
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Set.Function
import Mathlib.Data.List.Cycle
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import SM.InterlaceSupports
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import SM.TraversalRelabel
import SM.ContinuousGeometry
import SM.EuclideanPlane
import SM.CarrierMarks
import SM.CarrierSuccessor
import SM.CarrierVisitTwin
import SM.CarrierSmoothing
import SM.CarrierSingleSwitch
import SM.CarrierUnchangedComponent
import SM.CarrierSplitList
import SM.CarrierAmbientTransport
import SM.CycleFiltering
import SM.CarrierFilteredCycles
import SM.CarrierTrueCorners
import SM.CarrierCycleList
import SM.CarrierSingleSupport
import SM.CarrierInheritedOrder
import SM.CarrierCurrentCycle
import SM.CarrierInsertOrbits
import SM.CarrierSameArc
import SM.CarrierSortedArcLists
import SM.CarrierMarkedArcLists
import SM.CarrierPendingPairs
import SM.CarrierInheritedInsert
import SM.CarrierIndependentOrder
import SM.CarrierMarkedSegments
import SM.CarrierAffineSegments
import SM.CarrierSegmentGeometry
import SM.CarrierClosedTrace

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierFirstCornerBlock.body.lean (prototype CarrierActualCornerBlock, kernel session 28160, receipt
CarrierActualCornerBlock-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

variable {α : Type*}

/-- Scan the remaining anchored list, with its retained anchor appended at
the end. Finite recursion constructs the first retained entry and all omitted
entries before it, including an empty omitted block and a closing return. -/
theorem first_retained_append_anchor (p : α → Bool) (a : α) (R : List α)
    (ha : p a = true) :
    ∃ (M : List α) (b : α) (B : List α),
      R ++ [a] = M ++ b :: B ∧ (∀ x ∈ M, p x = false) ∧ p b = true := by
  induction R with
  | nil =>
    exact ⟨[], a, [], rfl, by simp, ha⟩
  | cons x R ih =>
    cases hx : p x with
    | false =>
      obtain ⟨M, b, B, hsplit, hM, hb⟩ := ih
      refine ⟨x :: M, b, B, ?_, ?_, hb⟩
      · simpa only [List.cons_append] using congrArg (List.cons x) hsplit
      · intro y hy
        rcases List.mem_cons.mp hy with he | hy
        · subst y
          exact hx
        · exact hM y hy
    | true =>
      exact ⟨[], x, R ++ [a], rfl, by simp, hx⟩

variable [DecidableEq α]

/-- The first retained entry after the anchor is exactly the filtered cyclic
next entry. The proof permits the filtered tail to be empty, in which case
the next entry is the anchor itself. No two-corner premise is used. -/
theorem filter_next_eq_of_first_retained (p : α → Bool) (a : α) (R : List α)
    (ha : p a = true) (M : List α) (b : α) (B : List α)
    (hsplit : R ++ [a] = M ++ b :: B) (hM : ∀ x ∈ M, p x = false)
    (hb : p b = true) :
    ((a :: R).filter p).next a (by simp [ha]) = b := by
  have hMfilter : M.filter p = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simp [hM x hx]
  have hfilter : R.filter p ++ [a] = b :: B.filter p := by
    have hh := congrArg (List.filter p) hsplit
    simpa [List.filter_append, ha, hb, hMfilter] using hh
  by_cases hR : R.filter p = []
  · have hab : a = b := by
      have hh := congrArg List.head? hfilter
      simpa [hR] using hh
    simpa [List.filter_cons, ha, hR] using hab
  · obtain ⟨c, C, hRC⟩ := List.exists_cons_of_ne_nil hR
    have hcb : c = b := by
      have hh := congrArg List.head? hfilter
      simpa [hRC] using hh
    simpa [List.filter_cons, ha, hRC] using hcb

/-- A duplicate-free anchored marked cycle has a constructed first retained
block. Its closed block is a literal prefix of the original closed marked
list, so all intermediate steps remain consecutive original list steps.
The endpoint may equal the anchor, and the intermediate block may be empty. -/
theorem firstCornerBlock (p : α → Bool) (a : α) (R : List α)
    (hN : (a :: R).Nodup) (ha : p a = true) :
    ∃ (M : List α) (b : α) (B : List α),
      R ++ [a] = M ++ b :: B ∧ (∀ x ∈ M, p x = false) ∧ p b = true ∧
      ((a :: R).filter p).next a (by simp [ha]) = b ∧
      (a :: (M ++ [b])) <+: ((a :: R) ++ [a]) ∧ M.Nodup ∧ a ∉ M := by
  obtain ⟨M, b, B, hsplit, hM, hb⟩ := first_retained_append_anchor p a R ha
  refine ⟨M, b, B, hsplit, hM, hb,
    filter_next_eq_of_first_retained p a R ha M b B hsplit hM hb, ?_, ?_, ?_⟩
  · refine ⟨B, ?_⟩
    simpa only [List.cons_append, List.append_assoc, List.singleton_append,
      List.nil_append] using congrArg (List.cons a) hsplit.symm
  · have hclosedN : (R ++ [a]).Nodup := by
      simpa only [List.rotate_cons_succ, List.rotate_zero] using
        (List.nodup_rotate.mpr hN : ((a :: R).rotate 1).Nodup)
    rw [hsplit] at hclosedN
    exact (List.nodup_append.mp hclosedN).1
  · intro ham
    have hh := hM a ham
    simp [ha] at hh

end SM.Carrier
