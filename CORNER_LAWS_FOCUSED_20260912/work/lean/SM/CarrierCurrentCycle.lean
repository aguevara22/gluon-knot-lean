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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierCurrentCycle.body.lean (prototype CarrierComponentCount, kernel session 35180, receipt
CarrierComponentCount-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Any literal representative of an actual inherited component has no repeated marks. -/
theorem componentCycle_list_nodup (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q : Component hn hP T)
    (L : List (Mark P)) (hL : componentCycle hn hP T q = (L : Cycle (Mark P))) :
    L.Nodup := by
  have hN := componentCycle_nodup hn hP T q
  rw [hL] at hN
  exact hN

/-- The representative's membership is exactly its constructed incoming owner. -/
theorem componentCycle_list_mem_iff (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q : Component hn hP T)
    (L : List (Mark P)) (hL : componentCycle hn hP T q = (L : Cycle (Mark P)))
    (m : Mark P) : m ∈ L ↔ owner hn hP T m = q := by
  change m ∈ (L : Cycle (Mark P)) ↔ _
  rw [← hL]
  exact mem_componentCycle hn hP T q m

/-- An explicit inherited-order hypothesis gives equality of the representative's
permutation with the current successor on its own marks, not on the whole ambient type. -/
theorem componentCycle_list_eqOn (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (hI : InheritsMarkOrder hn hP T)
    (q : Component hn hP T) (L : List (Mark P))
    (hL : componentCycle hn hP T q = (L : Cycle (Mark P))) :
    Set.EqOn L.formPerm (smoothingSuccessor hn hP T) {m | m ∈ L} := by
  have hN := componentCycle_list_nodup hn hP T q L hL
  have he : (⟨componentCycle hn hP T q, componentCycle_nodup hn hP T q⟩ :
      {s : Cycle (Mark P) // s.Nodup}) = ⟨(L : Cycle (Mark P)), hN⟩ :=
    Subtype.ext hL
  have hp := congrArg
    (fun s : {s : Cycle (Mark P) // s.Nodup} => s.val.formPerm s.property) he
  change (componentCycle hn hP T q).formPerm (componentCycle_nodup hn hP T q) =
    (L : Cycle (Mark P)).formPerm hN at hp
  have hp' : (componentCycle hn hP T q).formPerm
      (componentCycle_nodup hn hP T q) = L.formPerm :=
    hp.trans (Cycle.formPerm_coe L hN)
  intro m hm
  have hmc : m ∈ componentCycle hn hP T q := by
    rw [hL]
    exact hm
  rw [← hp']
  exact (inheritsMarkOrder_iff_formPerm hn hP T).mp hI q m hmc

/-- Distinct marks in one actual component supply the original rotation and
the owner-filtered literal current split list. Its action equality is derived
from the explicit induction invariant. No representation is supplied as input. -/
theorem componentCycle_current_split_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (hI : InheritsMarkOrder hn hP T)
    (q : Component hn hP T) (a b : Mark P) (hab : a ≠ b)
    (ha : owner hn hP T a = q) (hb : owner hn hP T b = q) :
    ∃ (k : ℕ) (A B : List (Mark P)),
      (markList hn hP).rotate k = a :: (A ++ b :: B) ∧
      let L := a :: (A.filter (fun m => decide (owner hn hP T m = q)) ++
        b :: B.filter (fun m => decide (owner hn hP T m = q)))
      componentCycle hn hP T q = (L : Cycle (Mark P)) ∧ L.Nodup ∧
        (∀ m : Mark P, m ∈ L ↔ owner hn hP T m = q) ∧
        Set.EqOn L.formPerm (smoothingSuccessor hn hP T) {m | m ∈ L} := by
  obtain ⟨k, A, B, hrot⟩ := markList_rotate_split hn hP a b hab
  let L := a :: (A.filter (fun m => decide (owner hn hP T m = q)) ++
    b :: B.filter (fun m => decide (owner hn hP T m = q)))
  have hL : componentCycle hn hP T q = (L : Cycle (Mark P)) :=
    componentCycle_eq_filtered_splitList hn hP T q k a b A B hrot ha hb
  exact ⟨k, A, B, hrot, hL, componentCycle_list_nodup hn hP T q L hL,
    componentCycle_list_mem_iff hn hP T q L hL,
    componentCycle_list_eqOn hn hP T hI q L hL⟩

end
end SM.Carrier
