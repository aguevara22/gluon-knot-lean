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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftGaussLists.body.lean (prototype SoftFamilyAssembly, kernel session 44274, receipt
SoftFamilyAssembly-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {j : ZMod n} {q : Plane} {ε : ℝ}

/-- Set exhaustion supplies a permutation; ordering is proved separately below. -/
theorem soft_gaussList_inherited_perm (hn : 3 ≤ n) (hP : Generic P)
    (hp : SoftCrossingPersistence P j q ε) (hQ : Generic (softInsertion P j q ε))
    (hclass : SoftCrossingClassificationAt P j q ε) :
    ((gaussList hn hP).map (softInheritedVisit hp)).Perm
      ((gaussList (by omega : 3 ≤ n + 1) hQ).filter
        (fun w => decide (w.1.val ≠ {softOldIndex j (j - 1), softNewIndex j}))) := by
  apply (List.perm_ext_iff_of_nodup
    (List.Nodup.map (softInheritedVisit_injective hp) (gaussList_nodup hn hP))
    ((gaussList_nodup (by omega : 3 ≤ n + 1) hQ).filter _)).mpr
  intro w
  constructor
  · rintro hw
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw
    exact List.mem_filter.mpr ⟨mem_gaussList _ hQ _,
      decide_eq_true (softInheritedCrossing_ne_newborn hn hp v.1)⟩
  · intro hw
    have hne : w.1.val ≠ {softOldIndex j (j - 1), softNewIndex j} := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp hw).2
    obtain ⟨v, rfl⟩ := (softInheritedVisit_range_iff hn hp hclass w).mpr hne
    exact List.mem_map.mpr ⟨v, mem_gaussList hn hP v, rfl⟩

/-- Literal equality of the inherited sorted visit lists, including the
numerical cut and an empty parent list. It uses the actual geometric order. -/
theorem soft_gaussList_inherited (hn : 3 ≤ n) (hP : Generic P)
    (hp : SoftCrossingPersistence P j q ε) (hQ : Generic (softInsertion P j q ε))
    (hclass : SoftCrossingClassificationAt P j q ε)
    (ho : SoftInheritedOrderAt P j q ε) :
    (gaussList hn hP).map (softInheritedVisit hp) =
      (gaussList (by omega : 3 ≤ n + 1) hQ).filter
        (fun w => decide (w.1.val ≠ {softOldIndex j (j - 1), softNewIndex j})) := by
  apply List.Perm.eq_of_pairwise
    (fun x y _ _ hxy hyx => visitKey_injective (by omega : 3 ≤ n + 1) hQ
      (le_antisymm hxy hyx))
    _ ((gaussList_sorted (by omega : 3 ≤ n + 1) hQ).filter _)
    (soft_gaussList_inherited_perm hn hP hp hQ hclass)
  apply List.pairwise_map.mpr
  apply (gaussList_sorted hn hP).imp
  intro v w h
  exact (softInheritedVisit_key_le_iff hn hP.1 hp hQ.1 ho v w).mpr h

/-- In all non-loop sectors every actual child visit is inherited. -/
theorem soft_gaussList_nonloop (hn : 3 ≤ n) (hP : Generic P)
    (hp : SoftCrossingPersistence P j q ε) (hQ : Generic (softInsertion P j q ε))
    (hclass : SoftCrossingClassificationAt P j q ε)
    (ho : SoftInheritedOrderAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)) :
    (gaussList hn hP).map (softInheritedVisit hp) =
      gaussList (by omega : 3 ≤ n + 1) hQ := by
  rw [soft_gaussList_inherited hn hP hp hQ hclass ho]
  apply List.filter_eq_self.mpr
  intro w _
  obtain ⟨v, rfl⟩ := softInheritedVisit_surjective_nonloop hp hclass hnot w
  exact decide_eq_true (softInheritedCrossing_ne_newborn hn hp v.1)

/-- This equality is in the genuine rotation quotient of actual visits. -/
theorem soft_gaussCycle_nonloop (hn : 3 ≤ n) (hP : Generic P)
    (hp : SoftCrossingPersistence P j q ε) (hQ : Generic (softInsertion P j q ε))
    (hclass : SoftCrossingClassificationAt P j q ε)
    (ho : SoftInheritedOrderAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)) :
    (gaussCycle hn hP).map (softInheritedVisit hp) =
      gaussCycle (by omega : 3 ≤ n + 1) hQ := by
  exact congrArg (fun l : List (Visit (softInsertion P j q ε)) =>
    (l : Cycle (Visit (softInsertion P j q ε))))
    (soft_gaussList_nonloop hn hP hp hQ hclass ho hnot)

/-- Crossing pairing is retained when passing from visits to the Gauss word. -/
theorem soft_gaussWord_nonloop (hn : 3 ≤ n) (hP : Generic P)
    (hp : SoftCrossingPersistence P j q ε) (hQ : Generic (softInsertion P j q ε))
    (hclass : SoftCrossingClassificationAt P j q ε)
    (ho : SoftInheritedOrderAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)) :
    (gaussWord hn hP).map (softInheritedCrossing hp) =
      gaussWord (by omega : 3 ≤ n + 1) hQ := by
  have hl := congrArg (List.map Sigma.fst)
    (soft_gaussList_nonloop hn hP hp hQ hclass ho hnot)
  have he : ((gaussList hn hP).map Sigma.fst).map (softInheritedCrossing hp) =
      (gaussList (by omega : 3 ≤ n + 1) hQ).map Sigma.fst := by
    simpa only [List.map_map, Function.comp_def, softInheritedVisit_crossing] using hl
  exact congrArg (fun l : List (Crossing (softInsertion P j q ε)) =>
    (l : Cycle (Crossing (softInsertion P j q ε)))) he

end
end SM
