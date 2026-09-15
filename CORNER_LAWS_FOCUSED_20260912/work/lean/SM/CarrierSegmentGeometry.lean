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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierSegmentGeometry.body.lean (prototype CarrierActualCornerBlock, kernel session 28160, receipt
CarrierActualCornerBlock-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Every actual smoothed outgoing segment is one positive piece of the
original outgoing edge at the selected slot. Physical twin equality identifies
the starting point, without identifying the distinct incoming marks. -/
theorem smoothingSegment_subsegment_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    let p := markPosition hn hP.1 (selectedMarkPerm S a)
    ∃ t : ℝ, p.2.val < t ∧ t ≤ 1 ∧
      traversalEvaluation P (markPosition hn hP.1 a) = edgePoint P p.1 p.2.val ∧
      traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) =
        edgePoint P p.1 t ∧
      ∀ u : ℝ, smoothingSegment hn hP S a u = edgePoint P p.1 (p.2.val + u * (t - p.2.val)) := by
  dsimp only
  obtain ⟨t, hst, ht1, he⟩ := markSuccessor_subsegment_data hn hP (selectedMarkPerm S a)
  have hstart : traversalEvaluation P (markPosition hn hP.1 a) =
      edgePoint P (markPosition hn hP.1 (selectedMarkPerm S a)).1
        (markPosition hn hP.1 (selectedMarkPerm S a)).2.val :=
    (selectedMarkPerm_evaluation hn hP.1 S a).symm
  have hend : traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) =
      edgePoint P (markPosition hn hP.1 (selectedMarkPerm S a)).1 t := he
  refine ⟨t, hst, ht1, hstart, hend, ?_⟩
  intro u
  unfold smoothingSegment
  rw [hstart, hend, edgePoint_affine]

/-- The exact endpoint displacement is a strictly positive multiple of the
actual original outgoing edge. The scalar is the proved parameter gap. -/
theorem smoothingSegment_positive_direction (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) -
        traversalEvaluation P (markPosition hn hP.1 a) =
        c • edge P (markPosition hn hP.1 (selectedMarkPerm S a)).1 := by
  obtain ⟨t, hst, _, hstart, hend, _⟩ := smoothingSegment_subsegment_data hn hP S a
  refine ⟨t - (markPosition hn hP.1 (selectedMarkPerm S a)).2.val, sub_pos.mpr hst, ?_⟩
  rw [hstart, hend, edgePoint_sub_edgePoint]

theorem smoothingSegment_displacement_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) -
      traversalEvaluation P (markPosition hn hP.1 a) ≠ 0 := by
  obtain ⟨c, hc, he⟩ := smoothingSegment_positive_direction hn hP S a
  rw [he]
  exact smul_ne_zero (ne_of_gt hc)
    ((g1 hn P hP.1).2.1 (markPosition hn hP.1 (selectedMarkPerm S a)).1)

/-- Positive length uses the Euclidean length of the source plane, not the
product-space norm. -/
theorem smoothingSegment_length_pos (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    0 < euclideanLength
      (traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) -
        traversalEvaluation P (markPosition hn hP.1 a)) :=
  euclideanLength_pos (smoothingSegment_displacement_ne_zero hn hP S a)

/-- Parameters in the unit interval stay on the actual original edge segment. -/
theorem smoothingSegment_mem_edgeSegment (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    smoothingSegment hn hP S a u ∈
      edgeSegment P (markPosition hn hP.1 (selectedMarkPerm S a)).1 := by
  obtain ⟨t, hst, ht1, _, _, hformula⟩ := smoothingSegment_subsegment_data hn hP S a
  let s := (markPosition hn hP.1 (selectedMarkPerm S a)).2.val
  have hs0 : 0 ≤ s := (markPosition hn hP.1 (selectedMarkPerm S a)).2.property.1
  have hgap : 0 ≤ t - s := le_of_lt (sub_pos.mpr hst)
  refine ⟨s + u * (t - s), ?_, ?_, hformula u⟩
  · exact add_nonneg hs0 (mul_nonneg hu0 hgap)
  · have hmul := mul_le_mul_of_nonneg_right hu1 hgap
    nlinarith

/-- Each actual segment traverses its positive parameter interval without
repetition. This is local segment injectivity, not injectivity of a carrier. -/
theorem smoothingSegment_injective (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    Function.Injective (smoothingSegment hn hP S a) := by
  intro u v huv
  obtain ⟨t, hst, _, _, _, hformula⟩ := smoothingSegment_subsegment_data hn hP S a
  rw [hformula u, hformula v] at huv
  have hparam := edgePoint_injective
    ((g1 hn P hP.1).2.1 (markPosition hn hP.1 (selectedMarkPerm S a)).1) huv
  exact mul_right_cancel₀ (ne_of_gt (sub_pos.mpr hst)) (add_left_cancel hparam)

/-- No support can produce a fixed actual mark: its outgoing geometric segment
has nonzero displacement. This uses geometry beyond the abstract split model. -/
theorem smoothingSuccessor_ne_self (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    smoothingSuccessor hn hP S a ≠ a := by
  intro he
  have hne := smoothingSegment_displacement_ne_zero hn hP S a
  rw [he, sub_self] at hne
  exact hne rfl

end
end SM.Carrier
