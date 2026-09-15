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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftFamilyG2.body.lean (prototype SoftFamilyAssembly, kernel session 44274, receipt
SoftFamilyAssembly-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
open Set Filter Topology
variable {n : ℕ} [NeZero n]

/-- Three distinct closed edges cannot have a common point if one pair is
adjacent: its shared vertex lies on no third edge under G1. -/
theorem g1_no_adjacent_closedTripleMeet (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (i j k : ZMod n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (ha : adjacent i j) : ¬ ClosedTripleMeet P i j k := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  rintro ⟨x, hi, hj, hk⟩
  have hmem : x ∈ edgeSegment P i ∩ edgeSegment P j := ⟨hi, hj⟩
  rcases g1_adjacent_intersection hn hP hij ha with ⟨he, hset⟩ | ⟨he, hset⟩
  · rw [hset] at hmem
    have hx : x = P j := hmem
    have hjnext : j ≠ k + 1 := by
      intro h
      exact hik (add_right_cancel (he.symm.trans h))
    exact (g1_vertex_not_mem_edge hP k j (next_ne_self k).symm hjk hjnext) (hx ▸ hk)
  · rw [hset] at hmem
    have hx : x = P i := hmem
    have hinext : i ≠ k + 1 := by
      intro h
      exact hjk (add_right_cancel (he.symm.trans h))
    exact (g1_vertex_not_mem_edge hP k i (next_ne_self k).symm hik hinext) (hx ▸ hk)

/-- Parent Generic excludes all distinct closed triples, not just the
pairwise remote triples mentioned in the canonical G2 characterization. -/
theorem generic_no_distinct_closedTripleMeet (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (i j k : ZMod n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ¬ ClosedTripleMeet P i j k := by
  classical
  haveI : Fact (1 < n) := ⟨by omega⟩
  by_cases hr1 : remote i j
  · by_cases hr2 : remote j k
    · by_cases hr3 : remote i k
      · exact (g2_iff_no_remote_closed_triples hn hP.1).mp hP.2 i j k hr1 hr2 hr3
      · have ha : adjacent i k := by simpa only [remote, not_not] using hr3
        rintro ⟨x, hi, hj, hk⟩
        exact g1_no_adjacent_closedTripleMeet hn hP.1 i k j hik hjk.symm hij ha
          ⟨x, hi, hk, hj⟩
    · have ha : adjacent j k := by simpa only [remote, not_not] using hr2
      rintro ⟨x, hi, hj, hk⟩
      exact g1_no_adjacent_closedTripleMeet hn hP.1 j k i hjk hik.symm hij.symm ha
        ⟨x, hj, hk, hi⟩
  · have ha : adjacent i j := by simpa only [remote, not_not] using hr1
    exact g1_no_adjacent_closedTripleMeet hn hP.1 i j k hij hjk hik ha

/-- The complete closed segment at every corresponding parent label is
exactly its parent segment at zero, including the return edge. -/
theorem edgeSegment_softInsertion_parent_zero (P : LabelledTuple n) (j k : ZMod n)
    (q : Plane) :
    edgeSegment (softInsertion P j q 0) (softParentEdge j k) = edgeSegment P k := by
  ext x
  simp only [edgeSegment, mem_setOf_eq, edgePoint_softInsertion_parent_zero]

/-- Compact closed-triple persistence on all actual corresponding edges,
simultaneously. No genericity of the inserted zero tuple is assumed. -/
theorem soft_parent_closedTriples_persist (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (j : ZMod n) (q : Plane) :
    ∃ δ > 0, ∀ ε : ℝ, |ε| < δ → ∀ k l m : ZMod n,
      k ≠ l → l ≠ m → k ≠ m →
        ¬ ClosedTripleMeet (softInsertion P j q ε)
          (softParentEdge j k) (softParentEdge j l) (softParentEdge j m) := by
  classical
  have htrip : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ∀ k l m : ZMod n,
      k ≠ l → l ≠ m → k ≠ m →
        ¬ ClosedTripleMeet (softInsertion P j q ε)
          (softParentEdge j k) (softParentEdge j l) (softParentEdge j m) := by
    refine eventually_all.mpr fun k => eventually_all.mpr fun l =>
      eventually_all.mpr fun m => ?_
    by_cases hd : k ≠ l ∧ l ≠ m ∧ k ≠ m
    · have hzero : ¬ ClosedTripleMeet (softInsertion P j q 0)
          (softParentEdge j k) (softParentEdge j l) (softParentEdge j m) := by
        simpa only [ClosedTripleMeet, edgeSegment_softInsertion_parent_zero] using
          generic_no_distinct_closedTripleMeet hn hP k l m hd.1 hd.2.1 hd.2.2
      have he : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
          ¬ ClosedTripleMeet (softInsertion P j q ε)
            (softParentEdge j k) (softParentEdge j l) (softParentEdge j m) :=
        ((continuous_softInsertion P j q).continuousAt :
          ContinuousAt (softInsertion P j q) (0 : ℝ)).eventually
          ((isClosed_closedTripleMeet (softParentEdge j k) (softParentEdge j l)
            (softParentEdge j m)).isOpen_compl.mem_nhds hzero)
      exact he.mono (fun _ h _ _ _ => h)
    · exact Eventually.of_forall (fun _ hkl hlm hkm => (hd ⟨hkl, hlm, hkm⟩).elim)
  obtain ⟨δ, hδ, hmem⟩ := Metric.eventually_nhds_iff.mp htrip
  exact ⟨δ, hδ, fun ε hε => hmem (by simpa only [Real.dist_eq, sub_zero] using hε)⟩

/-- Genericity on one positive interval, proved through compact closed
triples and soft-edge avoidance. No inherited/newborn separation theorem,
child Generic hypothesis or crossing classification is used. -/
theorem softInsertion_small_Generic (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → Generic (softInsertion P j q ε) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  haveI : Fact (1 < n + 1) := ⟨by omega⟩
  obtain ⟨δt, hδt, htrip⟩ := soft_parent_closedTriples_persist hn hP j q
  obtain ⟨δg, hδg, hG1⟩ := softInsertion_small_G1 hP.1 j q hq
  obtain ⟨δs, hδs, hcontacts⟩ := softEdge_only_incident_contacts hn hP.1 j q hq
  refine ⟨min δt (min δg δs), lt_min hδt (lt_min hδg hδs), ?_⟩
  intro ε hε hεδ
  have hεt : |ε| < δt := by
    simpa only [abs_of_pos hε] using lt_of_lt_of_le hεδ (min_le_left δt (min δg δs))
  have hεg : ε < δg := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δt (min δg δs)) (min_le_left δg δs))
  have hεs : ε < δs := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δt (min δg δs)) (min_le_right δg δs))
  have hg := hG1 ε hε hεg
  have havoid := (hcontacts ε hε hεs).2.2
  have hsoft (a : ZMod (n + 1)) (hr : remote (softOldIndex j j) a) :
      Disjoint (edgeSegment (softInsertion P j q ε) (softOldIndex j j))
        (edgeSegment (softInsertion P j q ε) a) := by
    have he := remote_endpoints (softOldIndex j j) a hr
    apply havoid a he.1
    · intro ha
      apply he.2.2.1
      have hp := softOldIndex_next j (j - 1) (prev_ne_self j)
      simp only [sub_add_cancel] at hp
      exact (congrArg (fun b : ZMod (n + 1) => b + 1) ha).trans hp.symm
    · intro ha
      exact he.2.1 (ha.trans (softOldIndex_attachment_next j).symm)
  refine ⟨hg, (g2_iff_no_remote_closed_triples (by omega : 3 ≤ n + 1) hg).mpr ?_⟩
  intro a b c hab hbc hac
  rintro ⟨x, hxa, hxb, hxc⟩
  have has : a ≠ softOldIndex j j := by
    intro he
    subst a
    exact Set.disjoint_left.mp (hsoft b hab) hxa hxb
  have hbs : b ≠ softOldIndex j j := by
    intro he
    subst b
    exact Set.disjoint_left.mp (hsoft a (remote_symm hab)) hxb hxa
  have hcs : c ≠ softOldIndex j j := by
    intro he
    subst c
    exact Set.disjoint_left.mp (hsoft a (remote_symm hac)) hxc hxa
  obtain ⟨k, rfl⟩ := (soft_parent_edges_exhaust j a).resolve_left has
  obtain ⟨l, rfl⟩ := (soft_parent_edges_exhaust j b).resolve_left hbs
  obtain ⟨m, rfl⟩ := (soft_parent_edges_exhaust j c).resolve_left hcs
  have hkl : k ≠ l := by
    intro he
    exact (remote_endpoints _ _ hab).1 ((congrArg (softParentEdge j) he).symm)
  have hlm : l ≠ m := by
    intro he
    exact (remote_endpoints _ _ hbc).1 ((congrArg (softParentEdge j) he).symm)
  have hkm : k ≠ m := by
    intro he
    exact (remote_endpoints _ _ hac).1 ((congrArg (softParentEdge j) he).symm)
  exact htrip ε hεt k l m hkl hlm hkm ⟨x, hxa, hxb, hxc⟩

/-- The G2 conclusion alone is available without any extra caller premise. -/
theorem softInsertion_small_G2 (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → G2 (softInsertion P j q ε) := by
  obtain ⟨δ, hδ, hg⟩ := softInsertion_small_Generic hn hP j q hq
  exact ⟨δ, hδ, fun ε hε hεδ => (hg ε hε hεδ).2⟩

/-- The actual generic-valued map from the positive interval lies in one
labelled chamber and one quotient polygon chamber. The base parameter is
the positive midpoint; the duplicate-vertex zero tuple is never used as a
Generic point. -/
theorem softInsertion_one_chamber (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∃ hmid : Generic (softInsertion P j q (δ / 2)),
      ∀ ε : ℝ, 0 < ε → ε < δ → ∃ hg : Generic (softInsertion P j q ε),
        (⟨softInsertion P j q ε, hg⟩ : GenericTuple (n + 1)) ∈
          labelledChamber ⟨softInsertion P j q (δ / 2), hmid⟩ ∧
        polygonProjection (⟨softInsertion P j q ε, hg⟩ : GenericTuple (n + 1)) ∈
          chamber (polygonProjection ⟨softInsertion P j q (δ / 2), hmid⟩) := by
  obtain ⟨δ, hδ, hgen⟩ := softInsertion_small_Generic hn hP j q hq
  have hm0 : 0 < δ / 2 := by linarith
  have hmδ : δ / 2 < δ := by linarith
  have hmid := hgen (δ / 2) hm0 hmδ
  let H : Ioo (0 : ℝ) δ → GenericTuple (n + 1) := fun t =>
    ⟨softInsertion P j q t.val, hgen t.val t.property.1 t.property.2⟩
  have hH : Continuous H :=
    ((continuous_softInsertion P j q).comp continuous_subtype_val).subtype_mk _
  let mid : Ioo (0 : ℝ) δ := ⟨δ / 2, hm0, hmδ⟩
  have hbase : H mid = (⟨softInsertion P j q (δ / 2), hmid⟩ : GenericTuple (n + 1)) :=
    Subtype.ext rfl
  letI : ConnectedSpace (Ioo (0 : ℝ) δ) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ioo hδ)
  have hrange := isConnected_range hH
  have hproj := isConnected_range (continuous_polygonProjection.comp hH)
  refine ⟨δ, hδ, hmid, ?_⟩
  intro ε hε hεδ
  let t : Ioo (0 : ℝ) δ := ⟨ε, hε, hεδ⟩
  have hm : H t ∈ labelledChamber (H mid) :=
    hrange.subset_connectedComponent (mem_range_self mid) (mem_range_self t)
  have hp : polygonProjection (H t) ∈ chamber (polygonProjection (H mid)) :=
    hproj.subset_connectedComponent (mem_range_self mid) (mem_range_self t)
  refine ⟨hgen ε hε hεδ, ?_, ?_⟩
  · simpa only [hbase, H] using hm
  · simpa only [hbase, H] using hp

end
end SM
