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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftAttachmentSigns.body.lean (prototype SoftFamilyAssembly, kernel session 44274, receipt
SoftFamilyAssembly-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Both source attachment chirotopes agree with their parameter-independent
determinant signs for every positive epsilon, with the actual inserted labels. -/
theorem softInsertion_attachment_signs (P : LabelledTuple n) (j : ZMod n)
    (q : Plane) (ε : ℝ) (hε : 0 < ε) :
    chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j j) (softOldIndex j (j - 1)) =
      softAttachmentMinus P j q ∧
    chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j j) (softOldIndex j (j + 1)) =
      softAttachmentPlus P j q := by
  simpa only [chi, softInsertion_new, softInsertion_old, softLocalPoint,
    softAttachmentMinus, softAttachmentPlus, edge, sub_add_cancel] using
    softLocal_attachment_signs (P j) (P (j - 1)) (P (j + 1)) q ε hε

theorem softAttachment_signs_nonzero {P : LabelledTuple n} {j : ZMod n} {q : Plane}
    (hq : SoftAdmissible P j q) :
    softAttachmentMinus P j q ≠ 0 ∧ softAttachmentPlus P j q ≠ 0 := by
  exact ⟨fun hz => (sign_ne_zero.mpr hq.1) (SignType.neg_eq_zero_iff.mp hz),
    fun hz => (sign_ne_zero.mpr hq.2.1) (SignType.neg_eq_zero_iff.mp hz)⟩

/-- The turns at the two ends of the actual soft edge have the source signs.
The size hypothesis is used only to keep the incoming parent edge distinct. -/
theorem softInsertion_attachment_turns (hn : 3 ≤ n) (P : LabelledTuple n) (j : ZMod n)
    (q : Plane) (ε : ℝ) (hε : 0 < ε) :
    turn (softInsertion P j q ε) (softOldIndex j j) = -softAttachmentMinus P j q ∧
    turn (softInsertion P j q ε) (softNewIndex j) = -softAttachmentPlus P j q := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hj : j - 1 ≠ j := by
    intro h
    have h1 : (1 : ZMod n) = 0 := by linear_combination -h
    exact one_ne_zero h1
  have hnext := softOldIndex_next j (j - 1) hj
  rw [sub_add_cancel] at hnext
  have hprev : softOldIndex j j - 1 = softOldIndex j (j - 1) := by
    rw [hnext, add_sub_cancel_right]
  have hnewprev : softNewIndex j - 1 = softOldIndex j j := by
    rw [← softOldIndex_attachment_next, add_sub_cancel_right]
  have hs := softLocal_turn_signs (P j) (P (j - 1)) (P (j + 1)) q ε hε
  constructor
  · rw [turn_det, hprev, edge_softInsertion_old P j (j - 1) q ε hj, edge_softInsertion_soft]
    simpa only [softLocalPoint, add_sub_cancel_left, softAttachmentMinus,
      neg_neg, edge, sub_add_cancel] using hs.1
  · rw [turn_det, hnewprev, edge_softInsertion_soft, edge_softInsertion_return]
    simpa only [softLocalPoint, softLocalReturn, add_sub_cancel_left,
      softAttachmentPlus, neg_neg, edge] using hs.2

/-- All defining clauses of the source soft insertion, expressed directly
on its actual cyclic labels. This is a definition interface, not the later
genericity or crossing theorem. -/
theorem soft_insertion_definition (hn : 3 ≤ n) (P : LabelledTuple n) (j : ZMod n)
    (q : Plane) (ε : ℝ) (hε : 0 < ε) :
    (∀ k : ZMod n, softInsertion P j q ε (softOldIndex j k) = P k) ∧
    softInsertion P j q ε (softNewIndex j) = P j + ε • q ∧
    (∀ k : ZMod n, k ≠ j → edge (softInsertion P j q ε) (softOldIndex j k) = edge P k) ∧
    edge (softInsertion P j q ε) (softOldIndex j j) = ε • q ∧
    edge (softInsertion P j q ε) (softNewIndex j) = edge P j - ε • q ∧
    chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j j) (softOldIndex j (j - 1)) =
      softAttachmentMinus P j q ∧
    chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j j) (softOldIndex j (j + 1)) =
      softAttachmentPlus P j q ∧
    turn (softInsertion P j q ε) (softOldIndex j j) = -softAttachmentMinus P j q ∧
    turn (softInsertion P j q ε) (softNewIndex j) = -softAttachmentPlus P j q := by
  have hs := softInsertion_attachment_signs P j q ε hε
  have ht := softInsertion_attachment_turns hn P j q ε hε
  exact ⟨fun k => softInsertion_old P j k q ε, softInsertion_new P j q ε,
    fun k hk => edge_softInsertion_old P j k q ε hk, edge_softInsertion_soft P j q ε,
    edge_softInsertion_return P j q ε, hs.1, hs.2, ht.1, ht.2⟩

end
end SM
