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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierMarkedSegments.body.lean (prototype CarrierActualCornerBlock, kernel session 28160, receipt
CarrierActualCornerBlock-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The original successor cannot fix a mark: its actual orbit contains the
two distinct original vertex marks zero and one. -/
theorem markSuccessor_ne_self (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (a : Mark P) : markSuccessor hn hP a ≠ a := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  intro ha
  have h0 := (markSuccessor_sameCycle hn hP a (Sum.inl (0 : ZMod n))).eq_of_left ha
  have h1 := (markSuccessor_sameCycle hn hP a (Sum.inl (1 : ZMod n))).eq_of_left ha
  have h01 : (0 : ZMod n) = 1 := Sum.inl.inj (h0.symm.trans h1)
  have hz : (0 : ℕ) = 1 := by
    simpa only [ZMod.val_zero, ZMod.val_one] using congrArg ZMod.val h01
  omega

/-- Consecutive actual marks lie in increasing parameter order on one original
edge, or the second mark is precisely the next original vertex. Shifting the
cyclic cut to the first edge proves the same classification across label zero. -/
theorem markSuccessor_position_cases (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (a : Mark P) :
    ((markPosition hn hP.1 (markSuccessor hn hP a)).1 = (markPosition hn hP.1 a).1 ∧
      (markPosition hn hP.1 a).2.val <
        (markPosition hn hP.1 (markSuccessor hn hP a)).2.val) ∨
      markSuccessor hn hP a = Sum.inl ((markPosition hn hP.1 a).1 + 1) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  let p := markPosition hn hP.1 a
  let r := markPosition hn hP.1 (markSuccessor hn hP a)
  let i := p.1
  let r' := traversalShift i r
  let z : Set.Ico (0 : ℝ) 1 := ⟨0, le_rfl, zero_lt_one⟩
  have hp : traversalShift i p = ((0 : ZMod n), p.2) := by
    simp [traversalShift, i]
  have hv : traversalShift i (markPosition hn hP.1 (Sum.inl (i + 1))) =
      ((1 : ZMod n), z) := by
    apply Prod.ext
    · change (i + 1) - i = 1
      abel
    · apply Subtype.ext
      rfl
  have hgap : ¬ traversalBetween ((0 : ZMod n), p.2) ((1 : ZMod n), z) r' := by
    intro h
    have hshift : traversalBetween (traversalShift i p)
        (traversalShift i (markPosition hn hP.1 (Sum.inl (i + 1))))
        (traversalShift i r) := by
      simpa only [hp, hv] using h
    exact (markSuccessor_no_mark_between hn hP a (Sum.inl (i + 1)))
      ((traversalBetween_shift i p (markPosition hn hP.1 (Sum.inl (i + 1))) r).mp hshift)
  have hk0 : traversalKey ((0 : ZMod n), p.2) = p.2.val := by
    simp [traversalKey]
  have hk1 : traversalKey ((1 : ZMod n), z) = 1 := by
    simp [traversalKey, z, ZMod.val_one]
  have hne : traversalKey r' ≠ p.2.val := by
    intro he
    have hkey : traversalKey (traversalShift i r) =
        traversalKey (traversalShift i p) := by
      rw [hp, hk0]
      exact he
    have hrp : r = p :=
      (traversalShiftEquiv i).injective (traversalKey_injective hkey)
    exact (markSuccessor_ne_self hn hP a) (markPosition_injective hn hP hrp)
  have hlt : p.2.val < traversalKey r' := by
    by_contra h
    have hle := le_of_not_gt h
    have hstrict := lt_of_le_of_ne hle hne
    apply hgap
    exact Or.inr (Or.inr ⟨by simpa only [hk0] using hstrict,
      by simpa only [hk0, hk1] using p.2.property.2⟩)
  have hle : traversalKey r' ≤ 1 := by
    by_contra h
    have hstrict : 1 < traversalKey r' := lt_of_not_ge h
    apply hgap
    exact Or.inl ⟨by simpa only [hk0, hk1] using p.2.property.2,
      by simpa only [hk1] using hstrict⟩
  have hval : r'.1.val ≤ 1 := by
    have hp0 := r'.2.property.1
    have hval' : (r'.1.val : ℝ) ≤ 1 := by
      dsimp only [traversalKey] at hle
      linarith
    exact_mod_cast hval'
  have hcases : r'.1.val = 0 ∨ r'.1.val = 1 := by omega
  rcases hcases with hzero | hone
  · have hr0 : r'.1 = 0 :=
      ZMod.val_injective n (by simpa only [ZMod.val_zero] using hzero)
    have hri : r.1 = p.1 := by
      have he : r.1 - i = 0 := hr0
      exact sub_eq_zero.mp he
    have hk : traversalKey r' = r.2.val := by
      change (r'.1.val : ℝ) + r.2.val = r.2.val
      rw [hr0, ZMod.val_zero, Nat.cast_zero, zero_add]
    exact Or.inl ⟨hri, by simpa only [hk] using hlt⟩
  · have hr1 : r'.1 = 1 :=
      ZMod.val_injective n (hone.trans (ZMod.val_one n).symm)
    have hrt : r.2.val = 0 := by
      have hp0 : 0 ≤ r.2.val := r.2.property.1
      have hk : traversalKey r' = 1 + r.2.val := by
        change (r'.1.val : ℝ) + r.2.val = 1 + r.2.val
        rw [hr1, ZMod.val_one, Nat.cast_one]
      rw [hk] at hle
      linarith
    have hri : r.1 = i + 1 := by
      have he : r.1 - i = 1 := hr1
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp he)
    right
    apply markPosition_injective hn hP
    change r = markPosition hn hP.1 (Sum.inl (i + 1))
    apply Prod.ext
    · exact hri
    · apply Subtype.ext
      exact hrt

/-- The actual original successor endpoint lies a strictly positive parameter
distance ahead on the starting original edge, up to and including parameter
one. Its parameter is derived from the complete marked successor, not supplied. -/
theorem markSuccessor_subsegment_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (a : Mark P) :
    ∃ t : ℝ, (markPosition hn hP.1 a).2.val < t ∧ t ≤ 1 ∧
      traversalEvaluation P (markPosition hn hP.1 (markSuccessor hn hP a)) =
        edgePoint P (markPosition hn hP.1 a).1 t := by
  rcases markSuccessor_position_cases hn hP a with ⟨hi, ht⟩ | hv
  · refine ⟨(markPosition hn hP.1 (markSuccessor hn hP a)).2.val, ht,
      (markPosition hn hP.1 (markSuccessor hn hP a)).2.property.2.le, ?_⟩
    unfold traversalEvaluation
    rw [hi]
  · refine ⟨1, (markPosition hn hP.1 a).2.property.2, le_rfl, ?_⟩
    rw [hv, markPosition_evaluation_vertex]
    exact (edgePoint_one P (markPosition hn hP.1 a).1).symm

end
end SM.Carrier
