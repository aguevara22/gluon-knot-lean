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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftVisitOrder.body.lean (prototype SoftFamilyAssembly, kernel session 44274, receipt
SoftFamilyAssembly-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- The explicit finite family of inherited same-edge parameter comparisons.
This is a helper predicate, derived from parent Generic below. -/
def SoftInheritedOrderAt (P : LabelledTuple n) (j : ZMod n) (q : Plane) (ε : ℝ) : Prop :=
  ∀ k l m : ZMod n, IsCrossing P {k, l} → IsCrossing P {k, m} →
    (edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) <
      edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j m) ↔
      edgeParameter P k l < edgeParameter P k m)

/-- One positive radius supplies all pointwise transport and ordering inputs.
No child Generic assumption is required of the caller. -/
theorem soft_small_visit_order_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      Generic (softInsertion P j q ε) ∧ SoftCrossingPersistence P j q ε ∧
        SoftCrossingClassificationAt P j q ε ∧ SoftInheritedOrderAt P j q ε := by
  obtain ⟨δt, hδt, ht⟩ := soft_small_crossing_transport_data hn hP j q hq
  obtain ⟨δo, hδo, ho⟩ := Metric.eventually_nhds_iff.mp
    (soft_all_inherited_orders_persist hn hP j q)
  refine ⟨min δt δo, lt_min hδt hδo, ?_⟩
  intro ε hε hεδ
  obtain ⟨hG, hp, hc⟩ := ht ε hε (lt_of_lt_of_le hεδ (min_le_left _ _))
  refine ⟨hG, hp, hc, ho ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hε] using
    lt_of_lt_of_le hεδ (min_le_right δt δo)

variable {P : LabelledTuple n} {j : ZMod n} {q : Plane} {ε : ℝ}

theorem softInheritedVisit_parameter_lt_iff (hn : 3 ≤ n) (hP : G1 P)
    (hp : SoftCrossingPersistence P j q ε) (hQ : G1 (softInsertion P j q ε))
    (ho : SoftInheritedOrderAt P j q ε) (v w : Visit P) (he : v.2.val = w.2.val) :
    visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
      visitParameter v < visitParameter w := by
  obtain ⟨l, _, hv⟩ := crossing_pair_of_mem v.1 v.2.val v.2.property
  obtain ⟨m, _, hw⟩ := crossing_pair_of_mem w.1 w.2.val w.2.property
  have hvl : IsCrossing P {v.2.val, l} := hv ▸ v.1.property
  have hwm : IsCrossing P {v.2.val, m} := by
    simpa only [hw, ← he] using w.1.property
  rw [softInheritedVisit_parameter hn hp hQ v l hv,
    softInheritedVisit_parameter hn hp hQ w m hw,
    visitParameter_eq_of_support_pair hn hP v l hv,
    visitParameter_eq_of_support_pair hn hP w m hw, ← he]
  exact ho v.2.val l m hvl hwm

/-- Actual traversal keys keep their strict order, using numerical edge order
for different edges and the geometric parameter comparison on a common edge. -/
theorem softInheritedVisit_key_lt_iff (hn : 3 ≤ n) (hP : G1 P)
    (hp : SoftCrossingPersistence P j q ε) (hQ : G1 (softInsertion P j q ε))
    (ho : SoftInheritedOrderAt P j q ε) (v w : Visit P) :
    visitKey (by omega : 3 ≤ n + 1) hQ (softInheritedVisit hp v) <
      visitKey (by omega : 3 ≤ n + 1) hQ (softInheritedVisit hp w) ↔
      visitKey hn hP v < visitKey hn hP w := by
  rw [visitKey_lt_iff, visitKey_lt_iff]
  simp only [softInheritedVisit_edge, softParentEdge_val_lt_iff,
    (softParentEdge_injective j).eq_iff]
  exact or_congr Iff.rfl (and_congr_right
    (softInheritedVisit_parameter_lt_iff hn hP hp hQ ho v w))

theorem softInheritedVisit_key_le_iff (hn : 3 ≤ n) (hP : G1 P)
    (hp : SoftCrossingPersistence P j q ε) (hQ : G1 (softInsertion P j q ε))
    (ho : SoftInheritedOrderAt P j q ε) (v w : Visit P) :
    visitKey (by omega : 3 ≤ n + 1) hQ (softInheritedVisit hp v) ≤
      visitKey (by omega : 3 ≤ n + 1) hQ (softInheritedVisit hp w) ↔
      visitKey hn hP v ≤ visitKey hn hP w := by
  simpa only [not_lt] using not_congr
    (softInheritedVisit_key_lt_iff hn hP hp hQ ho w v)

end
end SM
