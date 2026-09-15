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
import SM.CutSetNearFarNeighbors
import SM.SoftDuplicationSpanningCutNeighbors
import SM.SoftDuplicationStartingGatePositions
import SM.SoftDuplicationSpanningCutGatePositions
import SM.SoftDuplicationSectionTriples
import SM.SoftDuplicationStartingGateProducts
import SM.SoftDuplicationSpanningCutGateProducts
import SM.SoftDuplicationStartingChildFactors
import SM.SoftDuplicationSpanningOneCutChildFactors
import SM.SoftDuplicationSpanningBothChildren
import SM.SoftDuplicationSpanningBothChildFactors
import SM.SoftDuplicationSpanningCoreCancellation
import SM.SoftDuplicationSpanningEmptyChildren
import SM.SoftDuplicationSpanningEmptyGates
import SM.SoftDuplicationAvoiding
import SM.SoftDuplicationAvoidingCompositions
import SM.SoftDuplicationAvoidingUnit
import SM.SoftDuplicationAvoidingTransform
import SM.SoftDuplicationSpanningEmptyWeights
import SM.SoftDuplicationTransformSetup
import SM.BoundaryTripleSupports
import SM.CanonicalTripleSigns
import SM.SoftInsertionIndices
import SM.SoftInsertionSuccessors
import SM.SoftInsertionTuple
import SM.SoftLocalDeterminants
import SM.SoftFamilyG1
import SM.SoftAttachmentSigns
import SM.SoftFarSignFamily
import SM.SoftParentEdges

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftRootBoundary.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Position of the attachment vertex in the boundary word cut immediately
after the specified parent root. The subtraction is in ZMod n. -/
def softRootPosition (j g : ZMod n) : Fin n :=
  ⟨(j - g - 1).val, ZMod.val_lt _⟩

theorem softRootPosition_index (j g : ZMod n) :
    boundaryIndex g (softRootPosition j g) = j := by
  change g + ((j - g - 1).val : ZMod n) + 1 = j
  rw [ZMod.natCast_zmod_val]
  abel

/-- Moving a specified number of positions in a boundary word moves the
actual cyclic label by that number, including wraparound. -/
theorem softRoot_boundaryIndex_add (g : ZMod n) {a b : Fin n} (d : ℕ)
    (h : b.val = a.val + d) :
    boundaryIndex g b = boundaryIndex g a + (d : ZMod n) := by
  simp only [boundaryIndex, h, Nat.cast_add]
  abel

/-- Successive retained old positions differ by one, except that the step
after the attachment skips the new occurrence and therefore differs by two. -/
theorem softRoot_old_step_val (s : Fin n) (m : ℕ) (hm : m + 1 < n) :
    (SoftDuplication.old s (⟨m + 1, hm⟩ : Fin n)).val =
      (SoftDuplication.old s (⟨m, by omega⟩ : Fin n)).val +
        (if m = s.val then 2 else 1) := by
  simp only [SoftDuplication.old_val]
  split_ifs <;> omega

/-- The actual old-position embedding in every nonsoft-root boundary word.
The proof follows cyclic successors, so no physical-label-zero exception
or freely supplied correspondence is needed. -/
theorem softRootBoundary_old_index (j g : ZMod n) (k : Fin n) :
    boundaryIndex (softParentEdge j g) (SoftDuplication.old (softRootPosition j g) k) =
      softOldIndex j (boundaryIndex g k) := by
  let s := softRootPosition j g
  have hs : boundaryIndex g s = j := softRootPosition_index j g
  have h : ∀ (m : ℕ) (hm : m < n),
      boundaryIndex (softParentEdge j g) (SoftDuplication.old s (⟨m, hm⟩ : Fin n)) =
        softOldIndex j (boundaryIndex g (⟨m, hm⟩ : Fin n)) := by
    intro m
    induction m with
    | zero =>
      intro hm
      have hv : (SoftDuplication.old s (⟨0, hm⟩ : Fin n)).val = 0 := by
        rw [SoftDuplication.old_val]
        simp only [Nat.zero_le, ite_true]
      simp only [boundaryIndex, hv, Nat.cast_zero, add_zero]
      exact softParentEdge_next j g
    | succ m ih =>
      intro hm
      have hm0 : m < n := by omega
      let k0 : Fin n := ⟨m, hm0⟩
      let k1 : Fin n := ⟨m + 1, hm⟩
      have hp : boundaryIndex g k1 = boundaryIndex g k0 + 1 := by
        simpa only [Nat.cast_one] using
          (softRoot_boundaryIndex_add g (a := k0) (b := k1) 1 rfl)
      have hh : boundaryIndex (softParentEdge j g) (SoftDuplication.old s k0) =
          softOldIndex j (boundaryIndex g k0) := ih hm0
      have hstep := softRoot_old_step_val s m hm
      change boundaryIndex (softParentEdge j g) (SoftDuplication.old s k1) =
        softOldIndex j (boundaryIndex g k1)
      by_cases he : m = s.val
      · have hk0 : k0 = s := Fin.ext he
        have hj0 : boundaryIndex g k0 = j := by simpa only [hk0] using hs
        have hc : boundaryIndex (softParentEdge j g) (SoftDuplication.old s k1) =
            boundaryIndex (softParentEdge j g) (SoftDuplication.old s k0) + 2 := by
          apply softRoot_boundaryIndex_add (softParentEdge j g) 2
          simpa only [if_pos he] using hstep
        calc
          boundaryIndex (softParentEdge j g) (SoftDuplication.old s k1) =
              boundaryIndex (softParentEdge j g) (SoftDuplication.old s k0) + 2 := hc
          _ = softOldIndex j (boundaryIndex g k0) + 2 := congrArg (fun x => x + 2) hh
          _ = softOldIndex j (j + 1) := by
            rw [hj0]
            calc
              softOldIndex j j + 2 = (softOldIndex j j + 1) + 1 := by ring
              _ = softNewIndex j + 1 := by rw [softOldIndex_attachment_next]
              _ = softOldIndex j (j + 1) := softNewIndex_next j
          _ = softOldIndex j (boundaryIndex g k1) := by rw [hp, hj0]
      · have hj0 : boundaryIndex g k0 ≠ j := by
          intro hj
          have hk0 : k0 = s := boundaryIndex_injective g (hj.trans hs.symm)
          exact he (congrArg Fin.val hk0)
        have hc : boundaryIndex (softParentEdge j g) (SoftDuplication.old s k1) =
            boundaryIndex (softParentEdge j g) (SoftDuplication.old s k0) + 1 := by
          apply softRoot_boundaryIndex_add (softParentEdge j g) 1
          simpa only [if_neg he] using hstep
        calc
          boundaryIndex (softParentEdge j g) (SoftDuplication.old s k1) =
              boundaryIndex (softParentEdge j g) (SoftDuplication.old s k0) + 1 := hc
          _ = softOldIndex j (boundaryIndex g k0) + 1 := congrArg (fun x => x + 1) hh
          _ = softOldIndex j (boundaryIndex g k0 + 1) :=
            (softOldIndex_next j (boundaryIndex g k0) hj0).symm
          _ = softOldIndex j (boundaryIndex g k1) := congrArg (softOldIndex j) hp.symm
  exact h k.val k.isLt

theorem softRootBoundary_A_index (j g : ZMod n) :
    boundaryIndex (softParentEdge j g) (SoftDuplication.A (softRootPosition j g)) =
      softOldIndex j j := by
  have h := softRootBoundary_old_index j g (softRootPosition j g)
  simpa only [SoftDuplication.old_self, softRootPosition_index] using h

/-- The extra position really is the inserted physical vertex, including
when it is the last position for the return-edge root. -/
theorem softRootBoundary_B_index (j g : ZMod n) :
    boundaryIndex (softParentEdge j g) (SoftDuplication.B (softRootPosition j g)) =
      softNewIndex j := by
  have h : boundaryIndex (softParentEdge j g) (SoftDuplication.B (softRootPosition j g)) =
      boundaryIndex (softParentEdge j g) (SoftDuplication.A (softRootPosition j g)) + 1 := by
    apply softRoot_boundaryIndex_add (softParentEdge j g) 1
    rfl
  rw [h, softRootBoundary_A_index, softOldIndex_attachment_next]

/-- Every retained boundary vertex agrees exactly with the parent word;
this is an equality for the actual soft tuple at every real parameter. -/
theorem softRootBoundary_old_word (P : LabelledTuple n) (j g : ZMod n) (q : Plane)
    (ε : ℝ) (k : Fin n) :
    boundaryWord (softInsertion P j q ε) (softParentEdge j g)
      (SoftDuplication.old (softRootPosition j g) k) = boundaryWord P g k := by
  unfold boundaryWord
  rw [softRootBoundary_old_index, softInsertion_old]

theorem softRootBoundary_new_word (P : LabelledTuple n) (j g : ZMod n) (q : Plane)
    (ε : ℝ) :
    boundaryWord (softInsertion P j q ε) (softParentEdge j g)
      (SoftDuplication.B (softRootPosition j g)) = P j + ε • q := by
  rw [boundaryWord, softRootBoundary_B_index, softInsertion_new]

/-- Cutting after the incoming parent edge puts the attachment first. -/
theorem softRootPosition_incoming (j : ZMod n) :
    (softRootPosition j (j - 1)).val = 0 := by
  have h : j - (j - 1) - 1 = (0 : ZMod n) := by abel
  simp only [softRootPosition, h, ZMod.val_zero]

/-- Cutting after the return edge puts the retained attachment last in the
core word, followed by the new occurrence at the last child position. -/
theorem softRootPosition_return (j : ZMod n) :
    (softRootPosition j j).val = n - 1 := by
  have h : j - j - 1 = (-1 : ZMod n) := by abel
  change (j - j - 1).val = n - 1
  rw [h]
  have hn := last_index_val_succ (n := n)
  omega

/-- Every actual child root except the soft edge has a unique parent root
with these proved label and vertex identities. No correspondence is a
caller premise, and the return root is included by softParentEdge. -/
theorem softRootBoundary_nonsoft (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (ε : ℝ) (a : ZMod (n + 1)) (ha : a ≠ softOldIndex j j) :
    ∃! g : ZMod n, a = softParentEdge j g ∧
      (∀ k : Fin n, boundaryIndex a (SoftDuplication.old (softRootPosition j g) k) =
        softOldIndex j (boundaryIndex g k)) ∧
      boundaryIndex a (SoftDuplication.B (softRootPosition j g)) = softNewIndex j ∧
      (∀ k : Fin n, boundaryWord (softInsertion P j q ε) a
        (SoftDuplication.old (softRootPosition j g) k) = boundaryWord P g k) ∧
      boundaryWord (softInsertion P j q ε) a
        (SoftDuplication.B (softRootPosition j g)) = P j + ε • q := by
  obtain ⟨g, hg⟩ := (soft_parent_edges_exhaust j a).resolve_left ha
  refine ⟨g, ?_, ?_⟩
  · rw [hg]
    exact ⟨rfl, softRootBoundary_old_index j g, softRootBoundary_B_index j g,
      softRootBoundary_old_word P j g q ε, softRootBoundary_new_word P j g q ε⟩
  · intro g' hg'
    exact softParentEdge_injective j (hg'.1.symm.trans hg)

end
end SM
