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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftCrossingClassification.body.lean (prototype SoftFamilyAssembly, kernel session 44274, receipt
SoftFamilyAssembly-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- The only formerly adjacent parent pair made remote is incoming/return,
in either order. Every other remote pair was already remote in the parent. -/
theorem softParentEdge_remote_cases (hn : 3 ≤ n) (j k l : ZMod n)
    (hr : remote (softParentEdge j k) (softParentEdge j l)) :
    remote k l ∨ (k = j - 1 ∧ l = j) ∨ (k = j ∧ l = j - 1) := by
  by_cases hp : remote k l
  · exact Or.inl hp
  · have hadj : adjacent k l := by simpa only [remote, not_not] using hp
    have hne : k ≠ l := by
      intro he
      exact (remote_endpoints _ _ hr).1 (congrArg (softParentEdge j) he.symm)
    rcases adjacent_distinct_cases hne hadj with he | he
    · have hlj : l = j := by
        by_contra hlj
        have hnext := (softParentEdge_next_eq_iff j k l).mpr ⟨he.symm, hlj⟩
        exact (remote_endpoints _ _ hr).2.1 hnext.symm
      right; left
      refine ⟨?_, hlj⟩
      rw [hlj] at he
      linear_combination -he
    · have hkj : k = j := by
        by_contra hkj
        have hnext := (softParentEdge_next_eq_iff j l k).mpr ⟨he.symm, hkj⟩
        exact (remote_endpoints _ _ hr).2.2.1 hnext
      right; right
      refine ⟨hkj, ?_⟩
      rw [hkj] at he
      linear_combination -he

/-- Complete enumeration of actual enlarged crossing supports. Every
inherited support is present; the sole possible extra support is the actual
incoming/return pair, and it occurs exactly in the loop sector. -/
theorem soft_crossing_support_classification (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → ∀ s : Finset (ZMod (n + 1)),
      IsCrossing (softInsertion P j q ε) s ↔
        (∃ k l : ZMod n, IsCrossing P {k, l} ∧ s = {softParentEdge j k, softParentEdge j l}) ∨
        (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) ∧
          s = {softOldIndex j (j - 1), softNewIndex j} := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨δr, hδr, hremote⟩ := soft_small_remote_pairs hn hP j q
  obtain ⟨δl, hδl, hlocal⟩ := softFamily_local_crossing hn P hP j q hq
  obtain ⟨δs, hδs, hsoft⟩ := softEdge_only_incident_contacts hn hP j q hq
  refine ⟨min δr (min δl δs), lt_min hδr (lt_min hδl hδs), ?_⟩
  intro ε hε hεδ
  have hεr : |ε| < δr := by
    simpa only [abs_of_pos hε] using lt_of_lt_of_le hεδ (min_le_left δr (min δl δs))
  have hεl : ε < δl := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δr (min δl δs)) (min_le_left δl δs))
  have hεs : ε < δs := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δr (min δl δs)) (min_le_right δl δs))
  have hmiss (a : ZMod (n + 1)) (ha : remote (softOldIndex j j) a) :
      Disjoint (edgeSegment (softInsertion P j q ε) (softOldIndex j j))
        (edgeSegment (softInsertion P j q ε) a) := by
    apply (hsoft ε hε hεs).2.2 a (remote_endpoints _ _ ha).1
    · intro he
      apply (remote_endpoints _ _ ha).2.2.1
      rw [he, ← softOldIndex_next j (j - 1) (prev_ne_self j), sub_add_cancel]
    · intro he
      apply (remote_endpoints _ _ ha).2.1
      rw [he, softOldIndex_attachment_next]
  intro s
  constructor
  · rintro ⟨a, b, hs, hr, hm⟩
    rcases soft_parent_edges_exhaust j a with rfl | ⟨k, rfl⟩
    · obtain ⟨x, hx, hy⟩ := hm
      exact (Set.disjoint_left.mp (hmiss b hr) hx hy).elim
    · rcases soft_parent_edges_exhaust j b with rfl | ⟨l, rfl⟩
      · obtain ⟨x, hx, hy⟩ := hm
        exact (Set.disjoint_left.mp (hmiss _ (remote_symm hr)) hy hx).elim
      · have hc : IsCrossing (softInsertion P j q ε) {softParentEdge j k, softParentEdge j l} :=
          ⟨_, _, rfl, hr, hm⟩
        rcases softParentEdge_remote_cases hn j k l hr with hp | ⟨hk, hl⟩ | ⟨hk, hl⟩
        · exact Or.inl ⟨k, l, (hremote ε hεr k l hp).mp hc, hs⟩
        · subst k; subst l
          have hc' : IsCrossing (softInsertion P j q ε)
              {softOldIndex j (j - 1), softNewIndex j} := by
            simpa only [softParentEdge_of_ne j (j - 1) (prev_ne_self j),
              softParentEdge_at_attachment] using hc
          exact Or.inr ⟨(hlocal ε hε hεl).2.mp hc', by
            simpa only [softParentEdge_of_ne j (j - 1) (prev_ne_self j),
              softParentEdge_at_attachment] using hs⟩
        · subst k; subst l
          have hc' : IsCrossing (softInsertion P j q ε)
              {softOldIndex j (j - 1), softNewIndex j} := by
            simpa only [softParentEdge_of_ne j (j - 1) (prev_ne_self j),
              softParentEdge_at_attachment, Finset.pair_comm] using hc
          exact Or.inr ⟨(hlocal ε hε hεl).2.mp hc', by
            simpa only [softParentEdge_of_ne j (j - 1) (prev_ne_self j),
              softParentEdge_at_attachment, Finset.pair_comm] using hs⟩
  · rintro (⟨k, l, hc, rfl⟩ | ⟨hloop, rfl⟩)
    · exact (hremote ε hεr k l (crossing_pair_remote hc)).mpr hc
    · exact (hlocal ε hε hεl).2.mpr hloop

/-- The newborn support cannot be the image of any actual parent crossing.
Thus the support classification adds exactly one support in the loop sector. -/
theorem soft_newborn_support_not_inherited (hn : 3 ≤ n) (P : LabelledTuple n)
    (j k l : ZMod n) (hc : IsCrossing P {k, l}) :
    ({softParentEdge j k, softParentEdge j l} : Finset (ZMod (n + 1))) ≠
      {softOldIndex j (j - 1), softNewIndex j} := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  intro he
  have himage : ({k, l} : Finset (ZMod n)).image (softParentEdge j) =
      ({j - 1, j} : Finset (ZMod n)).image (softParentEdge j) := by
    simpa only [Finset.image_insert, Finset.image_singleton,
      softParentEdge_of_ne j (j - 1) (prev_ne_self j), softParentEdge_at_attachment] using he
  have hpair := Finset.image_injective (softParentEdge_injective j) himage
  rw [hpair] at hc
  have hr := crossing_pair_remote hc
  exact (remote_endpoints (j - 1) j hr).2.1 (sub_add_cancel j 1).symm

end
end SM
