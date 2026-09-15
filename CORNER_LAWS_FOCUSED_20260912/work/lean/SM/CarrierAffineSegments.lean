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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierAffineSegments.body.lean (prototype CarrierActualCornerBlock, kernel session 28160, receipt
CarrierActualCornerBlock-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Difference of two points on the same original oriented edge, with the
parameter difference retained as its exact scalar. -/
theorem edgePoint_sub_edgePoint (P : LabelledTuple n) (i : ZMod n) (s t : ℝ) :
    edgePoint P i t - edgePoint P i s = (t - s) • edge P i := by
  apply Prod.ext <;> simp [edgePoint, smul_eq_mul] <;> ring

/-- Affine interpolation of actual edge points agrees with interpolation of
their parameters. No positivity assumption is needed for this algebraic identity. -/
theorem edgePoint_affine (P : LabelledTuple n) (i : ZMod n) (s t u : ℝ) :
    edgePoint P i s + u • (edgePoint P i t - edgePoint P i s) =
      edgePoint P i (s + u * (t - s)) := by
  apply Prod.ext <;> simp [edgePoint, smul_eq_mul] <;> ring

/-- The actual straight segment from a mark to its smoothed successor.
Its positive original-edge realization is proved in the next packet. -/
def smoothingSegment (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) (u : ℝ) : Plane :=
  traversalEvaluation P (markPosition hn hP.1 a) +
    u • (traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) -
      traversalEvaluation P (markPosition hn hP.1 a))

@[simp]
theorem smoothingSegment_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    smoothingSegment hn hP S a 0 = traversalEvaluation P (markPosition hn hP.1 a) := by
  simp [smoothingSegment]

@[simp]
theorem smoothingSegment_one (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    smoothingSegment hn hP S a 1 =
      traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) := by
  simp [smoothingSegment]

/-- Every constructed segment joins exactly to the next segment, including
the closing join of an actual successor orbit. -/
theorem smoothingSegment_glue (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    smoothingSegment hn hP S a 1 =
      smoothingSegment hn hP S (smoothingSuccessor hn hP S a) 0 := by
  rw [smoothingSegment_one, smoothingSegment_zero]

theorem continuous_smoothingSegment (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    Continuous (smoothingSegment hn hP S a) :=
  continuous_const.add (continuous_id.smul continuous_const)

end
end SM.Carrier
