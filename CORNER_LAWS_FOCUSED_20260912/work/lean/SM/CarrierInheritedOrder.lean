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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierInheritedOrder.body.lean (prototype CarrierComponentCount, kernel session 35180, receipt
CarrierComponentCount-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The current actual successor follows each component's inherited original
cyclic order. This is an explicit invariant, not part of componentCycle's definition. -/
def InheritsMarkOrder (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) : Prop :=
  ∀ (q : Component hn hP T) (a : Mark P) (ha : a ∈ componentCycle hn hP T q),
    (componentCycle hn hP T q).next (componentCycle_nodup hn hP T q) a ha =
      smoothingSuccessor hn hP T a

/-- The next-point invariant is equivalently the actual filtered cycle's
formPerm action on its members. No assertion is made about nonmembers. -/
theorem inheritsMarkOrder_iff_formPerm (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) :
    InheritsMarkOrder hn hP T ↔
      ∀ (q : Component hn hP T) (a : Mark P) (_ha : a ∈ componentCycle hn hP T q),
        (componentCycle hn hP T q).formPerm (componentCycle_nodup hn hP T q) a =
          smoothingSuccessor hn hP T a := by
  constructor
  · intro h q a ha
    rw [Cycle.formPerm_apply_mem_eq_next _ _ a ha]
    exact h q a ha
  · intro h q a ha
    rw [← Cycle.formPerm_apply_mem_eq_next _ _ a ha]
    exact h q a ha

/-- Before any selected reconnection the inherited component cycle is the
original circle, whose next point is the constructed actual successor. -/
theorem inheritsMarkOrder_empty (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) : InheritsMarkOrder hn hP ∅ := by
  rw [inheritsMarkOrder_iff_formPerm]
  intro q a ha
  have he : (⟨componentCycle hn hP ∅ q, componentCycle_nodup hn hP ∅ q⟩ :
      {s : Cycle (Mark P) // s.Nodup}) = ⟨markCycle hn hP, markCycle_nodup hn hP⟩ :=
    Subtype.ext (componentCycle_empty hn hP q)
  have hp := congrArg
    (fun s : {s : Cycle (Mark P) // s.Nodup} => s.val.formPerm s.property) he
  rw [hp, smoothingSuccessor_empty]
  exact Cycle.formPerm_apply_mem_eq_next (markCycle hn hP) (markCycle_nodup hn hP)
    a (mem_markCycle hn hP a)

/-- Filtering the original split list by the left child node set retains
exactly a followed by B, including the case that B is empty. -/
theorem filter_splitList_left {α : Type*} [DecidableEq α]
    (a b : α) (A B : List α) (h : (a :: (A ++ b :: B)).Nodup) :
    (a :: (A ++ b :: B)).filter (fun x => decide (x ∈ a :: B)) = a :: B := by
  obtain ⟨hL, hR, hd⟩ := splitList_child_data a b A B h
  have hA : A.filter (fun x => decide (x ∈ a :: B)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    exact fun hxl => hd hxl (List.mem_cons_of_mem b hx)
  have hB : B.filter (fun x => decide (x ∈ a :: B)) = B := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    exact List.mem_cons_of_mem a hx
  have hb : b ∉ a :: B := fun hb => hd hb List.mem_cons_self
  rw [List.filter_cons, List.filter_append, hA, List.filter_cons, hB]
  simp [hb]

/-- Filtering by the other child retains A followed by b. Its rotation is
b followed by A, so this also treats the singleton child when A is empty. -/
theorem filter_splitList_right {α : Type*} [DecidableEq α]
    (a b : α) (A B : List α) (h : (a :: (A ++ b :: B)).Nodup) :
    (a :: (A ++ b :: B)).filter (fun x => decide (x ∈ b :: A)) = A ++ [b] := by
  obtain ⟨hL, hR, hd⟩ := splitList_child_data a b A B h
  have hA : A.filter (fun x => decide (x ∈ b :: A)) = A := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    exact List.mem_cons_of_mem b hx
  have hB : B.filter (fun x => decide (x ∈ b :: A)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    exact fun hxr => hd (List.mem_cons_of_mem a hx) hxr
  have ha : a ∉ b :: A := fun ha => hd List.mem_cons_self ha
  rw [List.filter_cons, List.filter_append, hA, List.filter_cons, hB]
  simp [ha]

/-- One actual selected crossing has the two literal inherited child cycles.
Their representations, membership filters and permutation product are derived
from a rotation of the complete original marked circle. -/
theorem componentCycle_singleton_splitList (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (v : Visit P) :
    ∃ A B : List (Mark P),
      (Sum.inr v :: B).Nodup ∧ (Sum.inr (visitTwin v) :: A).Nodup ∧
      (Sum.inr v :: B).Disjoint (Sum.inr (visitTwin v) :: A) ∧
      componentCycle hn hP {v.1} (owner hn hP {v.1} (Sum.inr v)) =
        (Sum.inr v :: B : Cycle (Mark P)) ∧
      componentCycle hn hP {v.1} (owner hn hP {v.1} (Sum.inr (visitTwin v))) =
        (Sum.inr (visitTwin v) :: A : Cycle (Mark P)) ∧
      smoothingSuccessor hn hP {v.1} =
        (Sum.inr v :: B).formPerm * (Sum.inr (visitTwin v) :: A).formPerm := by
  classical
  let a : Mark P := Sum.inr v
  let b : Mark P := Sum.inr (visitTwin v)
  have hab : a ≠ b := fun he => (visitTwin_ne v).symm (Sum.inr.inj he)
  obtain ⟨k, A, B, hrot⟩ := markList_rotate_split hn hP a b hab
  have hN : (a :: (A ++ b :: B)).Nodup := by
    rw [← hrot]
    exact List.nodup_rotate.mpr (markList_nodup hn hP)
  obtain ⟨hL, hR, hd⟩ := splitList_child_data a b A B hN
  have hc : markCycle hn hP = (a :: (A ++ b :: B) : Cycle (Mark P)) := by
    rw [← hrot]
    exact (markCycle_rotation hn hP k).symm
  have hp : (a :: (A ++ b :: B)).formPerm = markSuccessor hn hP := by
    rw [← hrot, List.formPerm_rotate _ (markList_nodup hn hP) k]
    exact (markSuccessor_eq_formPerm hn hP).symm
  have hs : smoothingSuccessor hn hP {v.1} =
      (a :: (A ++ b :: B)).formPerm * Equiv.swap a b := by
    simpa only [Finset.insert_empty, smoothingSuccessor_empty, hp] using
      smoothingSuccessor_insert hn hP (∅ : Finset (Crossing P)) v
        (Finset.notMem_empty v.1)
  have hownerL (m : Mark P) : owner hn hP {v.1} m = owner hn hP {v.1} a ↔
      m ∈ a :: B := by
    rw [owner_eq_iff, hs, Equiv.Perm.sameCycle_comm]
    exact splitList_left_sameCycle_iff a b A B hN m
  have hownerR (m : Mark P) : owner hn hP {v.1} m = owner hn hP {v.1} b ↔
      m ∈ b :: A := by
    rw [owner_eq_iff, hs, Equiv.Perm.sameCycle_comm]
    exact splitList_right_sameCycle_iff a b A B hN m
  have hpL : (fun m => decide (owner hn hP {v.1} m = owner hn hP {v.1} a)) =
      (fun m => decide (m ∈ a :: B)) := by
    funext m
    simp only [hownerL m]
  have hpR : (fun m => decide (owner hn hP {v.1} m = owner hn hP {v.1} b)) =
      (fun m => decide (m ∈ b :: A)) := by
    funext m
    simp only [hownerR m]
  have hcL : componentCycle hn hP {v.1} (owner hn hP {v.1} a) =
      (a :: B : Cycle (Mark P)) := by
    rw [componentCycle, hc, Cycle.filter_coe, hpL]
    refine congrArg (fun l : List (Mark P) => (l : Cycle (Mark P)))
      (Eq.trans ?_ (filter_splitList_left a b A B hN))
    apply List.filter_congr
    intro m _
    exact decide_eq_decide.mpr Iff.rfl
  have hcR : componentCycle hn hP {v.1} (owner hn hP {v.1} b) =
      (b :: A : Cycle (Mark P)) := by
    rw [componentCycle, hc, Cycle.filter_coe, hpR]
    refine (congrArg (fun l : List (Mark P) => (l : Cycle (Mark P)))
      (Eq.trans ?_ (filter_splitList_right a b A B hN))).trans
      (Cycle.coe_eq_coe.mpr (List.isRotated_concat b A))
    apply List.filter_congr
    intro m _
    exact decide_eq_decide.mpr Iff.rfl
  exact ⟨A, B, hL, hR, hd, hcL, hcR, hs.trans (splitList_identity a b A B hN)⟩

/-- The inherited-order invariant holds for one actual selected crossing.
Actual owner exhaustion reduces to the two child cycles, and disjointness
makes the full successor product restrict to each child's own formPerm. -/
theorem inheritsMarkOrder_singleton (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (v : Visit P) : InheritsMarkOrder hn hP {v.1} := by
  rw [inheritsMarkOrder_iff_formPerm]
  intro q m hm
  obtain ⟨A, B, hL, hR, hd, hcL, hcR, hs⟩ := componentCycle_singleton_splitList hn hP v
  rcases owner_singleton_exhaust hn hP v q with hq | hq
  · subst q
    have hmL : m ∈ Sum.inr v :: B := by
      rw [hcL] at hm
      exact hm
    have he : (⟨componentCycle hn hP {v.1} (owner hn hP {v.1} (Sum.inr v)),
        componentCycle_nodup hn hP {v.1} (owner hn hP {v.1} (Sum.inr v))⟩ :
        {s : Cycle (Mark P) // s.Nodup}) = ⟨(Sum.inr v :: B : Cycle (Mark P)), hL⟩ :=
      Subtype.ext hcL
    have hp := congrArg
      (fun s : {s : Cycle (Mark P) // s.Nodup} => s.val.formPerm s.property) he
    rw [hp]
    change (Sum.inr v :: B).formPerm m = smoothingSuccessor hn hP {v.1} m
    rw [hs, Equiv.Perm.mul_apply,
      List.formPerm_apply_of_notMem (fun hr => hd hmL hr)]
  · subst q
    have hmR : m ∈ Sum.inr (visitTwin v) :: A := by
      rw [hcR] at hm
      exact hm
    have he : (⟨componentCycle hn hP {v.1} (owner hn hP {v.1} (Sum.inr (visitTwin v))),
        componentCycle_nodup hn hP {v.1} (owner hn hP {v.1} (Sum.inr (visitTwin v)))⟩ :
        {s : Cycle (Mark P) // s.Nodup}) =
        ⟨(Sum.inr (visitTwin v) :: A : Cycle (Mark P)), hR⟩ := Subtype.ext hcR
    have hp := congrArg
      (fun s : {s : Cycle (Mark P) // s.Nodup} => s.val.formPerm s.property) he
    rw [hp]
    change (Sum.inr (visitTwin v) :: A).formPerm m = smoothingSuccessor hn hP {v.1} m
    rw [hs,
      (formPerm_disjoint_of_disjoint (Sum.inr v :: B) (Sum.inr (visitTwin v) :: A) hd).commute.eq,
      Equiv.Perm.mul_apply, List.formPerm_apply_of_notMem (fun hl => hd hl hmR)]

end
end SM.Carrier
