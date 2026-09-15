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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierTrueCorners.body.lean (prototype CarrierActualCornerBlock, kernel session 28160, receipt
CarrierActualCornerBlock-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Source true corners are exactly original vertices and selected crossing
visits. Unselected crossing visits are auxiliary marks of the traced curve. -/
def IsTrueCorner {P : LabelledTuple n} (S : Finset (Crossing P)) : Mark P → Prop
  | Sum.inl _ => True
  | Sum.inr v => v.1 ∈ S

@[simp]
theorem isTrueCorner_vertex {P : LabelledTuple n} (S : Finset (Crossing P))
    (i : ZMod n) : IsTrueCorner S (Sum.inl i) := trivial

@[simp]
theorem isTrueCorner_visit {P : LabelledTuple n} (S : Finset (Crossing P))
    (v : Visit P) : IsTrueCorner S (Sum.inr v) ↔ v.1 ∈ S := Iff.rfl

/-- A component containing no true corner would follow the original successor
throughout its whole owner block. Orbit transport then forces an original
vertex into that block, a contradiction. No independence premise is needed. -/
theorem component_has_trueCorner (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (q : Component hn hP S) :
    ∃ a : Mark P, owner hn hP S a = q ∧ IsTrueCorner S a := by
  by_contra hnoc
  have hnone : ∀ a : Mark P, owner hn hP S a = q → ¬ IsTrueCorner S a := by
    intro a ha hc
    exact hnoc ⟨a, ha, hc⟩
  obtain ⟨m, hm⟩ := owner_surjective hn hP S q
  have he : Set.EqOn (smoothingSuccessor hn hP S) (markSuccessor hn hP)
      {a | owner hn hP S a = q} := by
    intro a ha
    cases a with
    | inl i => exact False.elim (hnone (Sum.inl i) ha (isTrueCorner_vertex S i))
    | inr v =>
        exact smoothingSuccessor_visit_of_not_mem hn hP S v (hnone (Sum.inr v) ha)
  have hc : (smoothingSuccessor hn hP S).SameCycle m (Sum.inl (0 : ZMod n)) :=
    (sameCycle_congr_of_eqOn_bijOn (smoothingSuccessor hn hP S) (markSuccessor hn hP)
      {a | owner hn hP S a = q} (smoothingSuccessor_bijOn_owner hn hP S q) he
      m hm (Sum.inl (0 : ZMod n))).mp (markSuccessor_sameCycle hn hP m (Sum.inl 0))
  have hv : owner hn hP S (Sum.inl (0 : ZMod n)) = q :=
    ((owner_eq_iff hn hP S m (Sum.inl 0)).mpr hc).symm.trans hm
  exact hnone (Sum.inl (0 : ZMod n)) hv (isTrueCorner_vertex S 0)

/-- The actual inherited component cycle restricted to precisely its true
corners. Geometric compression and source regularity are separate theorems. -/
def componentCornerCycle (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : Cycle (Mark P) :=
  (componentCycle hn hP S q).filter (fun a => decide (IsTrueCorner S a))

/-- A literal representative retains exact owner and true-corner membership
in their inherited original cyclic order. -/
theorem componentCornerCycle_eq_filtered_markList (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (q : Component hn hP S) :
    componentCornerCycle hn hP S q =
      (((markList hn hP).filter (fun a => decide (owner hn hP S a = q))).filter
        (fun a => decide (IsTrueCorner S a)) : Cycle (Mark P)) := rfl

@[simp]
theorem mem_componentCornerCycle (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (q : Component hn hP S)
    (a : Mark P) : a ∈ componentCornerCycle hn hP S q ↔
      owner hn hP S a = q ∧ IsTrueCorner S a := by
  simp only [componentCornerCycle, Cycle.mem_filter, mem_componentCycle, decide_eq_true_eq]

theorem componentCornerCycle_nodup (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (q : Component hn hP S) :
    (componentCornerCycle hn hP S q).Nodup :=
  (componentCycle_nodup hn hP S q).filter (fun a => decide (IsTrueCorner S a))

/-- The corner filter is nonempty for every actual component and every
support; corner existence is derived above rather than supplied. -/
theorem componentCornerCycle_nonempty (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (q : Component hn hP S) :
    ∃ a : Mark P, a ∈ componentCornerCycle hn hP S q := by
  obtain ⟨a, ha, hc⟩ := component_has_trueCorner hn hP S q
  exact ⟨a, (mem_componentCornerCycle hn hP S q a).mpr ⟨ha, hc⟩⟩

end
end SM.Carrier
