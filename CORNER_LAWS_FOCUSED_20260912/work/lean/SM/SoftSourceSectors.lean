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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftSourceSectors.body.lean (prototype SoftFamilyAssembly, kernel session 44274, receipt
SoftFamilyAssembly-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section

/-- Exhaustion of the two non-loop source sectors by three-valued nonzero
signs. The nonzero hypotheses exclude the only fixed point of sign negation. -/
theorem signType_nonloop_sectors (a b τ : SignType)
    (ha : a ≠ 0) (hb : b ≠ 0) (hτ : τ ≠ 0) :
    ((a = -τ ∧ b = -τ) ∨ a ≠ b) ↔ ¬ (a = τ ∧ b = τ) := by
  cases a <;> cases b <;> cases τ <;> simp_all

variable {n : ℕ} [NeZero n]

/-- The source's same-sign and mixed cases are precisely the complement
of the loop case for a Generic parent and an admissible inserted vector. -/
theorem soft_nonloop_sectors_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ((softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) ∨
      softAttachmentMinus P j q ≠ softAttachmentPlus P j q) ↔
      ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hτ : turn P j ≠ 0 := by
    rw [turn_det]
    exact sign_ne_zero.mpr (g1_turn_nonzero hn hP j)
  exact signType_nonloop_sectors _ _ _ (softAttachment_signs_nonzero hq).1
    (softAttachment_signs_nonzero hq).2 hτ

theorem soft_attachment_sectors (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) ∨
    (softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) ∨
    softAttachmentMinus P j q ≠ softAttachmentPlus P j q := by
  by_cases hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j
  · exact Or.inl hloop
  · exact Or.inr ((soft_nonloop_sectors_iff hn hP j q hq).mpr hloop)

/-- The actual Gauss-word result with exactly the source's printed non-loop
sector antecedent. The helper transport inputs are derived on a source interval. -/
theorem soft_gaussWord_source_nonloop (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) (ε : ℝ)
    (hp : SoftCrossingPersistence P j q ε) (hQ : Generic (softInsertion P j q ε))
    (hclass : SoftCrossingClassificationAt P j q ε) (ho : SoftInheritedOrderAt P j q ε)
    (hsector : (softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) ∨
      softAttachmentMinus P j q ≠ softAttachmentPlus P j q) :
    (gaussWord hn hP).map (softInheritedCrossing hp) = gaussWord (by omega : 3 ≤ n + 1) hQ :=
  soft_gaussWord_nonloop hn hP hp hQ hclass ho
    ((soft_nonloop_sectors_iff hn hP.1 j q hq).mp hsector)

end
end SM
