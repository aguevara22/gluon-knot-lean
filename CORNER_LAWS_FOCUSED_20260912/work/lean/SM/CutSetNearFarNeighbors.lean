import SM.FiniteChiStability
import Mathlib.Topology.Order.LeftRightNhds
import SM.CrossingCriterion
import SM.ContinuousGeometry
import Mathlib.Topology.Instances.Sign
import Mathlib.Data.Fin.Tuple.Basic
import SM.SinglePointTriple
import SM.CriticalSourceResponse
import SM.InsertionIndices
import SM.RootBoundary
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import SM.InteriorCutSet
import Mathlib.Data.Subtype
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import SM.NearFar
import SM.CompositionCutSet
import SM.ConsecutiveTriples
import SM.FarOnlyOutput
import SM.ConsecutiveCuts
import SM.InteriorCutIndex
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import SM.CompositionSegments
import SM.NearFarTriangular
import SM.SegmentStability
import SM.G1Consequences
import SM.GenericTopology
import SM.CyclicChambers
import SM.SoftDuplicationIndices
import SM.SoftDuplicationCutFibers
import SM.SoftDuplicationPresentations
import SM.OrderedBoundaryTransport
import SM.SoftDuplicationStartingChildren
import SM.SoftDuplicationArrays
import SM.SoftDuplicationSpanningCutPresentations
import SM.CutSetNearFar

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CutSetNearFarNeighbors.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.BoundaryCutSet

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- Two consecutive intervals with the same right endpoint have the same
left endpoint: either strict ordering would expose an intervening cut. -/
theorem consecutive_left_unique (S : BoundaryCutSet I) {J K : BoundaryInterval n}
    (hJ : S.Consecutive J) (hK : S.Consecutive K) (hr : J.right = K.right) :
    J.left = K.left := by
  rcases lt_trichotomy J.left K.left with h | h | h
  · exact False.elim (hJ.2.2 K.left hK.1 ⟨h, by rw [hr]; exact K.increasing⟩)
  · exact h
  · exact False.elim (hK.2.2 J.left hJ.1 ⟨h, by rw [← hr]; exact J.increasing⟩)

theorem consecutive_right_unique (S : BoundaryCutSet I) {J K : BoundaryInterval n}
    (hJ : S.Consecutive J) (hK : S.Consecutive K) (hl : J.left = K.left) :
    J.right = K.right := by
  rcases lt_trichotomy J.right K.right with h | h | h
  · exact False.elim (hK.2.2 J.right hJ.2.1 ⟨by rw [← hl]; exact J.increasing, h⟩)
  · exact h
  · exact False.elim (hJ.2.2 K.right hK.2.1 ⟨by rw [hl]; exact K.increasing, h⟩)

/-- The physical child interval ending at this interior cut. -/
def nearLeftInterval (S : BoundaryCutSet I) (x : {x : Fin n // x ∈ S.interior.val}) :
    BoundaryInterval n where
  left := (S.nearAtCut x).lower
  right := (S.nearAtCut x).middle
  increasing := (S.nearAtCut x).lower_middle

/-- The physical child interval beginning at this interior cut. -/
def nearRightInterval (S : BoundaryCutSet I) (x : {x : Fin n // x ∈ S.interior.val}) :
    BoundaryInterval n where
  left := (S.nearAtCut x).middle
  right := (S.nearAtCut x).upper
  increasing := (S.nearAtCut x).middle_upper

theorem nearLeftInterval_consecutive (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) : S.Consecutive (S.nearLeftInterval x) := by
  let k := S.interiorIndexEquiv.symm x
  let l : Fin S.toComposition.parts := ⟨k.val, by have := k.isLt; omega⟩
  have he : S.nearLeftInterval x = S.toComposition.part l := rfl
  rw [he]
  simpa only [S.toComposition_cutSet] using S.toComposition.part_consecutive l

theorem nearRightInterval_consecutive (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) : S.Consecutive (S.nearRightInterval x) := by
  let k := S.interiorIndexEquiv.symm x
  let l : Fin S.toComposition.parts := ⟨k.val + 1, by have := k.isLt; omega⟩
  have he : S.nearRightInterval x = S.toComposition.part l := rfl
  rw [he]
  simpa only [S.toComposition_cutSet] using S.toComposition.part_consecutive l

/-- Any geometric proof that J is the preceding consecutive child identifies
the actual near gate's lower argument. No enumeration correspondence is assumed. -/
theorem nearAtCut_lower_eq_of_consecutive (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) (J : BoundaryInterval n)
    (hJ : S.Consecutive J) (hr : J.right = x.val) :
    (S.nearAtCut x).lower = J.left := by
  apply S.consecutive_left_unique (S.nearLeftInterval_consecutive x) hJ
  exact (S.nearAtCut_middle x).trans hr.symm

theorem nearAtCut_upper_eq_of_consecutive (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) (J : BoundaryInterval n)
    (hJ : S.Consecutive J) (hl : J.left = x.val) :
    (S.nearAtCut x).upper = J.right := by
  apply S.consecutive_right_unique (S.nearRightInterval_consecutive x) hJ
  exact (S.nearAtCut_middle x).trans hl.symm

end
end SM.BoundaryCutSet
