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
import SM.CycleFiltering
import SM.SoftGaussDeletion
import SM.SoftNewbornParameters
import SM.SoftNewbornVisitWindows
import SM.SoftParentArc
import SM.SoftNewbornVisits
import SM.GaussNextFromEmptyArc
import SM.SoftGaussGeometry
import SM.SoftAttachmentSigns
import SM.SoftFamilyTurns
import SM.SoftFamilyRegularData
import SM.SoftSourceSectors
import SM.SoftNewbornVertexArc

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftInheritedCrossingData.body.lean (prototype SoftFamilyAssembly, kernel session 44274, receipt
SoftFamilyAssembly-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- Finiteness provides one neighborhood for all ordered inherited pairs.
Both parameter inequalities are strict, and the ordered determinant sign
is compared with that same ordered parent pair. -/
theorem soft_all_inherited_parameters_persist (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : G1 P) (j : ZMod n) (q : Plane) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ∀ k l : ZMod n, IsCrossing P {k, l} →
      (0 < edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) ∧
        edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) < 1) ∧
      (0 < edgeParameter (softInsertion P j q ε) (softParentEdge j l) (softParentEdge j k) ∧
        edgeParameter (softInsertion P j q ε) (softParentEdge j l) (softParentEdge j k) < 1) ∧
      det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l)) ≠ 0 ∧
      SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l))) =
          SignType.sign (det (edge P k) (edge P l)) ∧
      IsCrossing (softInsertion P j q ε) {softParentEdge j k, softParentEdge j l} := by
  apply eventually_all.mpr
  intro k
  apply eventually_all.mpr
  intro l
  by_cases hc : IsCrossing P {k, l}
  · exact (softParent_crossing_parameters_persist hn hP j k l q hc).mono
      (fun _ h _ => h)
  · exact Eventually.of_forall (fun _ h => (hc h).elim)

variable {P : LabelledTuple n} {j : ZMod n} {q : Plane} {ε : ℝ}

/-- The image is the deterministic image of the actual unordered support;
no independent crossing correspondence is chosen. -/
theorem softInheritedCrossing_pair (hp : SoftCrossingPersistence P j q ε)
    {k l : ZMod n} (hc : IsCrossing P {k, l}) :
    softInheritedCrossing hp (⟨{k, l}, hc⟩ : Crossing P) =
      (⟨{softParentEdge j k, softParentEdge j l}, hp k l hc⟩ :
        Crossing (softInsertion P j q ε)) := by
  apply Subtype.ext
  change ({k, l} : Finset (ZMod n)).image (softParentEdge j) = _
  simp only [Finset.image_insert, Finset.image_singleton]

/-- The actual inherited canonical point is the global supporting-line
function. Only this pointwise bridge needs a child G1 proof. -/
theorem softInheritedCrossing_pair_point (hn : 3 ≤ n)
    (hp : SoftCrossingPersistence P j q ε) (hQ : G1 (softInsertion P j q ε))
    {k l : ZMod n} (hc : IsCrossing P {k, l}) :
    crossingPoint (softInheritedCrossing hp (⟨{k, l}, hc⟩ : Crossing P)) =
      softInheritedPoint P j k l q ε := by
  rw [softInheritedCrossing_pair hp hc]
  exact (softInheritedPoint_eq_crossingPoint hn P j k l q ε hQ (hp k l hc)).symm

/-- Both member visits use the same inherited support, with the ordered
support reversed only to select its second actual member edge. -/
theorem softInheritedPair_parameters (hn : 3 ≤ n)
    (hp : SoftCrossingPersistence P j q ε) (hQ : G1 (softInsertion P j q ε))
    {k l : ZMod n} (hc : IsCrossing P {k, l}) :
    visitParameter (softInheritedVisit hp (pairVisit hc)) =
      edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) ∧
    visitParameter (softInheritedVisit hp
      (pairVisit (by simpa only [Finset.pair_comm] using hc : IsCrossing P {l, k}))) =
      edgeParameter (softInsertion P j q ε) (softParentEdge j l) (softParentEdge j k) := by
  constructor
  · exact softInheritedVisit_parameter hn hp hQ (pairVisit hc) l rfl
  · exact softInheritedVisit_parameter hn hp hQ
      (pairVisit (by simpa only [Finset.pair_comm] using hc : IsCrossing P {l, k})) k rfl

/-- The three global functions have the actual parent canonical limits.
This is a limit at zero of supporting-line functions, never an assertion
that the duplicate-vertex child at zero is Generic. -/
theorem softInheritedPair_tendsto (hn : 3 ≤ n) (hP : G1 P)
    (j k l : ZMod n) (q : Plane) (hc : IsCrossing P {k, l}) :
    Tendsto (softInheritedPoint P j k l q) (𝓝 (0 : ℝ))
      (𝓝 (crossingPoint (⟨{k, l}, hc⟩ : Crossing P))) ∧
    Tendsto (fun ε : ℝ => edgeParameter (softInsertion P j q ε)
      (softParentEdge j k) (softParentEdge j l)) (𝓝 (0 : ℝ))
      (𝓝 (visitParameter (pairVisit hc))) ∧
    Tendsto (fun ε : ℝ => edgeParameter (softInsertion P j q ε)
      (softParentEdge j l) (softParentEdge j k)) (𝓝 (0 : ℝ))
      (𝓝 (visitParameter
        (pairVisit (by simpa only [Finset.pair_comm] using hc : IsCrossing P {l, k})))) := by
  refine ⟨softInheritedPoint_tendsto hn hP j k l q hc, ?_, ?_⟩
  · rw [pairVisit_parameter hn hP hc]
    exact softParentParameter_tendsto P j k l q
      (crossing_edgeParameter_det_ne_zero hn hP hc)
  · have hrev : IsCrossing P {l, k} := by simpa only [Finset.pair_comm] using hc
    rw [pairVisit_parameter hn hP hrev]
    exact softParentParameter_tendsto P j l k q
      (crossing_edgeParameter_det_ne_zero hn hP hrev)

/-- All actual inherited geometry holds on one positive interval obtained
from the parent hypotheses. Child Generic and persistence are conclusions,
not hypotheses of this radius theorem. -/
theorem soft_small_inherited_crossing_data (hn : 3 ≤ n) (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ (hQ : Generic (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε),
        ∀ k l : ZMod n, ∀ hc : IsCrossing P {k, l},
          (0 < edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) ∧
            edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) < 1) ∧
          (0 < edgeParameter (softInsertion P j q ε) (softParentEdge j l) (softParentEdge j k) ∧
            edgeParameter (softInsertion P j q ε) (softParentEdge j l) (softParentEdge j k) < 1) ∧
          det (edge (softInsertion P j q ε) (softParentEdge j k))
            (edge (softInsertion P j q ε) (softParentEdge j l)) ≠ 0 ∧
          SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
            (edge (softInsertion P j q ε) (softParentEdge j l))) =
              SignType.sign (det (edge P k) (edge P l)) ∧
          crossingPoint (softInheritedCrossing hp (⟨{k, l}, hc⟩ : Crossing P)) =
            softInheritedPoint P j k l q ε ∧
          visitParameter (softInheritedVisit hp (pairVisit hc)) =
            edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) ∧
          visitParameter (softInheritedVisit hp
            (pairVisit (by simpa only [Finset.pair_comm] using hc : IsCrossing P {l, k}))) =
            edgeParameter (softInsertion P j q ε) (softParentEdge j l) (softParentEdge j k) := by
  obtain ⟨δp, hδp, hpar⟩ := Metric.eventually_nhds_iff.mp
    (soft_all_inherited_parameters_persist hn hP.1 j q)
  obtain ⟨δt, hδt, htransport⟩ := soft_small_crossing_transport_data hn hP j q hq
  refine ⟨min δp δt, lt_min hδp hδt, ?_⟩
  intro ε hε hεδ
  have hεp : dist ε (0 : ℝ) < δp := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hε] using
      (lt_of_lt_of_le hεδ (min_le_left δp δt))
  have hεt : ε < δt := lt_of_lt_of_le hεδ (min_le_right δp δt)
  obtain ⟨hQ, hp, _⟩ := htransport ε hε hεt
  refine ⟨hQ, hp, ?_⟩
  intro k l hc
  have hd := hpar hεp k l hc
  exact ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1,
    softInheritedCrossing_pair_point hn hp hQ.1 hc,
    softInheritedPair_parameters hn hp hQ.1 hc⟩

end
end SM
