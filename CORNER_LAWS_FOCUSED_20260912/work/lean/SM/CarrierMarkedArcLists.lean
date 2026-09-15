import SM.GaussWord
import SM.SortedCyclicGap
import Mathlib.Tactic
import SM.GaussCyclicGap
import Mathlib.GroupTheory.Perm.Cycle.Basic
import SM.CrossingPair
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.List.Cycle
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Data.Set.Function
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import SM.InterlaceSupports
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import SM.CarrierMarks
import SM.CarrierSuccessor
import SM.CarrierVisitTwin
import SM.CarrierSmoothing
import SM.CarrierSingleSwitch
import SM.CarrierOrbitRefinement
import SM.CycleFiltering
import SM.CarrierFilteredCycles
import SM.CarrierCycleList
import SM.CarrierSplitList
import SM.CarrierSingleSupport
import SM.CarrierInheritedOrder
import SM.CarrierCurrentCycle
import SM.CarrierAmbientTransport
import SM.CarrierUnchangedComponent
import SM.CarrierInsertOrbits
import SM.CarrierComponentFibers
import SM.CarrierFiberCard
import SM.CarrierSameArc
import SM.CarrierSortedArcLists

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierMarkedArcLists.body.lean (prototype CarrierComponentCount, kernel session 35180, receipt
CarrierComponentCount-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- In any actual rotated complete marked list, the open list from a to b
is exactly the strict physical traversal arc, including wraparound. -/
theorem markList_rotate_left_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k = a :: (A ++ b :: B)) (m : Mark P) :
    m ∈ A ↔ traversalBetween (markPosition hn hP.1 a) (markPosition hn hP.1 m)
      (markPosition hn hP.1 b) := by
  letI := markLinearOrder hn hP
  have hr : (Finset.univ : Finset (Mark P)).sort.rotate k = a :: (A ++ b :: B) := hrot
  exact sorted_rotate_split_mem_iff Finset.univ k a b A B m hr (Finset.mem_univ m)

/-- The other open list is the reverse oriented physical arc, with both
endpoint marks excluded rather than assigned by a non-strict inequality. -/
theorem markList_rotate_right_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k = a :: (A ++ b :: B)) (m : Mark P) :
    m ∈ B ↔ traversalBetween (markPosition hn hP.1 b) (markPosition hn hP.1 m)
      (markPosition hn hP.1 a) := by
  letI := markLinearOrder hn hP
  have hr : (Finset.univ : Finset (Mark P)).sort.rotate k = a :: (A ++ b :: B) := hrot
  exact sorted_rotate_split_reverse_mem_iff Finset.univ k a b A B m hr (Finset.mem_univ m)

/-- Filtering the physical forward arc to one actual component adds precisely
its owner equality. No compatibility with the current successor is assumed. -/
theorem markList_filter_left_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) (q : Component hn hP T)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k = a :: (A ++ b :: B)) (m : Mark P) :
    m ∈ A.filter (fun x => decide (owner hn hP T x = q)) ↔
      traversalBetween (markPosition hn hP.1 a) (markPosition hn hP.1 m)
        (markPosition hn hP.1 b) ∧ owner hn hP T m = q := by
  simp only [List.mem_filter, decide_eq_true_eq,
    markList_rotate_left_iff hn hP k a b A B hrot m]

theorem markList_filter_right_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) (q : Component hn hP T)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k = a :: (A ++ b :: B)) (m : Mark P) :
    m ∈ B.filter (fun x => decide (owner hn hP T x = q)) ↔
      traversalBetween (markPosition hn hP.1 b) (markPosition hn hP.1 m)
        (markPosition hn hP.1 a) ∧ owner hn hP T m = q := by
  simp only [List.mem_filter, decide_eq_true_eq,
    markList_rotate_right_iff hn hP k a b A B hrot m]

/-- Actual independence puts another selected twin pair wholly into one
literal original split-list arc. This connects physical noninterlacement to
list membership, without replacing original arcs by current components. -/
theorem independent_twin_same_slice (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (v w : Visit P) (hvS : v.1 ∈ S) (hwS : w.1 ∈ S) (hvw : v.1 ≠ w.1)
    (k : ℕ) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k =
      Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)) :
    (Sum.inr w ∈ A ∧ Sum.inr (visitTwin w) ∈ A) ∨
      (Sum.inr w ∈ B ∧ Sum.inr (visitTwin w) ∈ B) := by
  rcases independent_twin_one_open_arc hn hP hS v w hvS hwS hvw with ha | hb
  · exact Or.inl
      ⟨(markList_rotate_left_iff hn hP k _ _ A B hrot _).mpr ha.1,
        (markList_rotate_left_iff hn hP k _ _ A B hrot _).mpr ha.2⟩
  · exact Or.inr
      ⟨(markList_rotate_right_iff hn hP k _ _ A B hrot _).mpr hb.1,
        (markList_rotate_right_iff hn hP k _ _ A B hrot _).mpr hb.2⟩

/-- When the other selected pair currently has owner q, the proved original
same-arc property puts both visits in one owner-filtered arc. The current-owner
equalities remain explicit inputs for the later simultaneous induction. -/
theorem independent_twin_same_filtered_slice (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (v w : Visit P) (hvS : v.1 ∈ S) (hwS : w.1 ∈ S) (hvw : v.1 ≠ w.1)
    (T : Finset (Crossing P)) (q : Component hn hP T)
    (hqw : owner hn hP T (Sum.inr w) = q)
    (hqt : owner hn hP T (Sum.inr (visitTwin w)) = q)
    (k : ℕ) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k =
      Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)) :
    (Sum.inr w ∈ A.filter (fun x => decide (owner hn hP T x = q)) ∧
      Sum.inr (visitTwin w) ∈ A.filter (fun x => decide (owner hn hP T x = q))) ∨
    (Sum.inr w ∈ B.filter (fun x => decide (owner hn hP T x = q)) ∧
      Sum.inr (visitTwin w) ∈ B.filter (fun x => decide (owner hn hP T x = q))) := by
  simpa only [List.mem_filter, hqw, hqt, decide_true, and_true] using
    independent_twin_same_slice hn hP hS v w hvS hwS hvw k A B hrot

end
end SM.Carrier
