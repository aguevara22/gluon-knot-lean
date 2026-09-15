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
import SM.SoftRootBoundary
import SM.SoftDuplicationScalars
import SM.SoftGeometricDuplication
import SM.SoftDuplicationNeighbors
import SM.SoftDuplicationSpanningTransform
import SM.SoftDuplicationStartingTransform
import SM.SoftDuplicationEndingChildren
import SM.SoftDuplicationEndingGatePositions
import SM.SoftDuplicationEndingGateProducts
import SM.SoftDuplicationEndingChildFactors
import SM.SoftDuplicationEndingTransform
import SM.SoftDuplicationFullEndpointOutput
import SM.SoftDuplicationOrdinaryIdentification
import SM.SoftAmplitudeGeometric
import SM.SoftAmplitudeSectors
import SM.SoftEdgeAvoidance
import SM.SoftFamilyG2

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftAmplitudeSource.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Intersect the actual geometric amplitude radius with the independently
proved Generic radius and any requested positive upper bound. All nonsoft
corresponding roots share this one positive interval. -/
theorem soft_amplitude_generic_radius (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q)
    (ε0 : ℝ) (hε0 : 0 < ε0) :
    ∃ ε1 : ℝ, 0 < ε1 ∧ ε1 ≤ ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε1 →
      ∃ hQ : Generic (softInsertion P j q ε), ∀ g : ZMod n,
        (treeCoefficient (softInsertion P j q ε) hQ.1 (softParentEdge j g)
          (by omega : 3 ≤ n + 1) : ℚ) =
        softAmplitudeMultiplier P j q * (treeCoefficient P hP.1 g hn : ℚ) := by
  obtain ⟨δA, hδA, hA⟩ := soft_treeCoefficient_uniform hn hP.1 j q hq
  obtain ⟨δG, hδG, hG⟩ := softInsertion_small_Generic hn hP j q hq
  refine ⟨min ε0 (min δA δG), lt_min hε0 (lt_min hδA hδG), min_le_left _ _, ?_⟩
  intro ε hε hε1
  have hεA : ε < δA := lt_of_lt_of_le hε1
    (le_trans (min_le_right ε0 (min δA δG)) (min_le_left δA δG))
  have hεG : ε < δG := lt_of_lt_of_le hε1
    (le_trans (min_le_right ε0 (min δA δG)) (min_le_right δA δG))
  have hQ := hG ε hε hεG
  obtain ⟨hQ1, hcoeff⟩ := hA ε hε hεA
  refine ⟨hQ, ?_⟩
  intro g
  simpa only [softAmplitudeMultiplier] using hcoeff g

/-- Every actual parent root other than the soft edge has a unique core root.
The correspondence is the physical softParentEdge map, whose j entry is the
return edge. Faithful rational casting gives all three integer sector laws. -/
theorem soft_amplitude_nonsoft_root (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q)
    (ε : ℝ) (hQ : Generic (softInsertion P j q ε))
    (hcoeff : ∀ g : ZMod n,
      (treeCoefficient (softInsertion P j q ε) hQ.1 (softParentEdge j g)
        (by omega : 3 ≤ n + 1) : ℚ) =
      softAmplitudeMultiplier P j q * (treeCoefficient P hP.1 g hn : ℚ))
    (a : ZMod (n + 1)) (ha : a ≠ softOldIndex j j) :
    ∃! g : ZMod n,
      a = softParentEdge j g ∧
      (treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) : ℚ) =
        softAmplitudeMultiplier P j q * (treeCoefficient P hP.1 g hn : ℚ) ∧
      ((softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) →
        treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) =
          -(turn P j : ℤ) * treeCoefficient P hP.1 g hn) ∧
      ((softAttachmentMinus P j q ≠ softAttachmentPlus P j q) →
        treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) = 0) ∧
      ((softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) →
        treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) =
          (turn P j : ℤ) * treeCoefficient P hP.1 g hn) := by
  obtain ⟨g, hg⟩ := (soft_parent_edges_exhaust j a).resolve_left ha
  have hval :
      (treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) : ℚ) =
        softAmplitudeMultiplier P j q * (treeCoefficient P hP.1 g hn : ℚ) := by
    rw [hg]
    exact hcoeff g
  refine ⟨g, ⟨hg, hval, ?_, ?_, ?_⟩, ?_⟩
  · intro hsector
    exact softAmplitude_integer_same_sign P j q hsector
      (treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1))
      (treeCoefficient P hP.1 g hn) hval
  · intro hsector
    exact softAmplitude_integer_mixed P j q hq hsector
      (treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1))
      (treeCoefficient P hP.1 g hn) hval
  · intro hsector
    exact softAmplitude_integer_loop P j q hsector
      (treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1))
      (treeCoefficient P hP.1 g hn) hval
  · intro k hk
    exact softParentEdge_injective j (hk.1.symm.trans hg)

/-- The source A-soft law on one radius bounded by the requested ε0, with
actual Generic parent polygons and every nonsoft physical root. Parent
Genericity, root correspondence, the rational law and the three integer
sector laws are conclusions; no residual G1 or supplied correspondence is assumed. -/
theorem soft_amplitude_source (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q)
    (ε0 : ℝ) (hε0 : 0 < ε0) :
    ∃ ε1 : ℝ, 0 < ε1 ∧ ε1 ≤ ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε1 →
      ∃ hQ : Generic (softInsertion P j q ε),
        ∀ a : ZMod (n + 1), a ≠ softOldIndex j j → ∃! g : ZMod n,
          a = softParentEdge j g ∧
          (treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) : ℚ) =
            softAmplitudeMultiplier P j q * (treeCoefficient P hP.1 g hn : ℚ) ∧
          ((softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) →
            treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) =
              -(turn P j : ℤ) * treeCoefficient P hP.1 g hn) ∧
          ((softAttachmentMinus P j q ≠ softAttachmentPlus P j q) →
            treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) = 0) ∧
          ((softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) →
            treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) =
              (turn P j : ℤ) * treeCoefficient P hP.1 g hn) := by
  obtain ⟨ε1, hε1, hε10, hfamilies⟩ := soft_amplitude_generic_radius hn hP j q hq ε0 hε0
  refine ⟨ε1, hε1, hε10, ?_⟩
  intro ε hε hεsmall
  obtain ⟨hQ, hcoeff⟩ := hfamilies ε hε hεsmall
  refine ⟨hQ, ?_⟩
  intro a ha
  exact soft_amplitude_nonsoft_root hn hP j q hq ε hQ hcoeff a ha

end
end SM.SoftDuplication
