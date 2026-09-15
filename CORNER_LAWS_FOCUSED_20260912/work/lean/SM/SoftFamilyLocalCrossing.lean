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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftFamilyLocalCrossing.body.lean (prototype SoftFamilyAssembly, kernel session 44274, receipt
SoftFamilyAssembly-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- In the actual enlarged word, the return edge starts two cyclic labels
after the incoming edge, with the soft edge between them. -/
theorem softIncoming_return_difference (hn : 3 ≤ n) (j : ZMod n) :
    softNewIndex j - softOldIndex j (j - 1) = (2 : ZMod (n + 1)) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hnext := softOldIndex_next j (j - 1) (prev_ne_self j)
  simp only [sub_add_cancel] at hnext
  rw [← softOldIndex_attachment_next j, hnext]
  ring

/-- The incoming/return pair is actually remote, including at parent
arity three and at every physical wrap position. -/
theorem softIncoming_return_remote (hn : 3 ≤ n) (j : ZMod n) :
    remote (softOldIndex j (j - 1)) (softNewIndex j) := by
  unfold remote adjacent
  rw [softIncoming_return_difference hn j]
  rintro (hneg | hzero | hpos)
  · have h3 : (3 : ZMod (n + 1)) = 0 := by linear_combination hneg
    have hd : n + 1 ∣ 3 := (ZMod.natCast_eq_zero_iff 3 (n + 1)).mp (by simpa using h3)
    have hle := Nat.le_of_dvd (by decide : 0 < 3) hd
    omega
  · have hd : n + 1 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (n + 1)).mp (by simpa using hzero)
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  · have h1 : (1 : ZMod (n + 1)) = 0 := by linear_combination hpos
    have hd : n + 1 ∣ 1 := (ZMod.natCast_eq_zero_iff 1 (n + 1)).mp (by simpa using h1)
    have hle := Nat.le_of_dvd (by decide : 0 < 1) hd
    omega

/-- Exact translation of the two actual closed edge segments to their
local point-and-direction parameter equations; every real parameter is allowed. -/
theorem softIncoming_return_segment_parameters (hn : 3 ≤ n)
    (P : LabelledTuple n) (j : ZMod n) (q : Plane) (ε : ℝ) :
    (edgeSegment (softInsertion P j q ε) (softOldIndex j (j - 1)) ∩
      edgeSegment (softInsertion P j q ε) (softNewIndex j)).Nonempty ↔
    ∃ s t : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧
      P (j - 1) + s • (P j - P (j - 1)) =
        softLocalPoint (P j) q ε + t • softLocalReturn (P j) (P (j + 1)) q ε := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hin (s : ℝ) :
      edgePoint (softInsertion P j q ε) (softOldIndex j (j - 1)) s =
        P (j - 1) + s • (P j - P (j - 1)) := by
    rw [edgePoint, softInsertion_old,
      edge_softInsertion_old P j (j - 1) q ε (prev_ne_self j)]
    simp only [edge, sub_add_cancel]
  have hout (t : ℝ) :
      edgePoint (softInsertion P j q ε) (softNewIndex j) t =
        softLocalPoint (P j) q ε + t • softLocalReturn (P j) (P (j + 1)) q ε := by
    rw [edgePoint, softInsertion_new, edge_softInsertion_return]
    rfl
  constructor
  · rintro ⟨x, ⟨s, hs0, hs1, hs⟩, ⟨t, ht0, ht1, ht⟩⟩
    refine ⟨s, t, hs0, hs1, ht0, ht1, ?_⟩
    have he := hs.symm.trans ht
    rwa [hin s, hout t] at he
  · rintro ⟨s, t, hs0, hs1, ht0, ht1, he⟩
    refine ⟨edgePoint (softInsertion P j q ε) (softOldIndex j (j - 1)) s,
      ⟨s, hs0, hs1, rfl⟩, ⟨t, ht0, ht1, ?_⟩⟩
    rw [hin s, hout t]
    exact he

/-- Local incoming/return crossing part of lem:soft-generic. The geometric
inputs are only parent G1 and the actual source admissibility predicate.
No genericity of the enlarged tuple or other soft-family claim is assumed.
This theorem concerns this one pair, not an enumeration of all crossings. -/
theorem softFamily_local_crossing (hn : 3 ≤ n) (P : LabelledTuple n) (hP : G1 P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ((edgeSegment (softInsertion P j q ε) (softOldIndex j (j - 1)) ∩
          edgeSegment (softInsertion P j q ε) (softNewIndex j)).Nonempty ↔
        softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) ∧
      (IsCrossing (softInsertion P j q ε) {softOldIndex j (j - 1), softNewIndex j} ↔
        softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hT : det (P j - P (j - 1)) (P (j + 1) - P j) ≠ 0 := by
    simpa only [edge, sub_add_cancel] using g1_turn_nonzero hn hP j
  have hm : det (P j - P (j - 1)) q ≠ 0 := by
    simpa only [edge, sub_add_cancel] using hq.1
  have hp : det q (P (j + 1) - P j) ≠ 0 := hq.2.1
  obtain ⟨δ, hδ, hlocal⟩ := softLocal_small_crossing_sector
    (P j) (P (j - 1)) (P (j + 1)) q hT hm hp
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hsector := (hlocal ε hε hεδ).2.2.1
  have hc :
      (edgeSegment (softInsertion P j q ε) (softOldIndex j (j - 1)) ∩
        edgeSegment (softInsertion P j q ε) (softNewIndex j)).Nonempty ↔
      softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j := by
    rw [softIncoming_return_segment_parameters hn P j q ε]
    simpa only [softAttachmentMinus, softAttachmentPlus, turn_det, edge, sub_add_cancel] using hsector
  exact ⟨hc, (isCrossing_pair (softInsertion P j q ε)
    (softOldIndex j (j - 1)) (softNewIndex j) (softIncoming_return_remote hn j)).trans hc⟩

end
end SM
