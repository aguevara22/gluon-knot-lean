import SM.TreeChamber
import SM.ContactHalfTuples
import SM.FusionIndices
import SM.NamedWallSides
import SM.UnorderedWallTriples
import Mathlib.Tactic
import SM.RestrictedWordRoot
import SM.GermTurnSigns
import SM.EuclideanPlane
import Mathlib.Data.Sign.Basic
import SM.GermNeighborhood
import SM.CriticalSourceResponse
import SM.FiniteChiStability
import SM.BoundaryTripleSupports
import SM.CriticalContractionPositions
import SM.CriticalContractionBounds
import SM.ContractedGeometricWord
import SM.ContractedIntervals
import SM.ContractedCompositions
import SM.OffLeafContraction
import SM.UniqueChangingChild
import SM.ContractedChildResponse
import SM.NonunaryContraction
import SM.ContractionPropagation
import SM.ContractionOutput
import SM.CollinearGateSigns
import SM.BoundaryGateSigns
import SM.FarOnlyOutputLocality
import SM.BoundaryArrayStability
import SM.WallArrayNeighborhood
import SM.WallGapValues
import SM.BoundaryGapGates
import SM.GeometricGapResponse
import SM.ContractedGeometricArray
import SM.GeometricProperResponse
import SM.ProperSpanGermResponse
import SM.FullSpanGermResponse
import SM.CriticalAffineData
import SM.SignedCriticalJump
import SM.SingleTripleTreeResponse
import SM.RestrictedCriticalG1
import SM.IntegerCriticalGaps
import SM.IntegerSingleTripleResponse
import SM.UnorderedCriticalTriple
import SM.FlatBoundaryPositions
import SM.FlatContractionArithmetic
import SM.ContactBoundaryPositions
import SM.ContactRootPartition
import SM.ContactHalfRoots
import SM.ContactContractionLabels
import SM.FlatIntegerFactors
import SM.TupleArityTransport
import SM.ContactGapTuples
import SM.ContactGapWords
import SM.ContactIntegerFactors
import SM.ContactContractionCoefficients
import SM.CuspIntegerFactors
import SM.ContactAffineSigns
import SM.ContactSignedResponse
import SM.ContactSourceResponse
import SM.SilentIntegerFactors
import SM.ExtensionAffineSigns

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/GermTreeEquality.body.lean (prototype TripleSilentTreeLaws, kernel session 2126, receipt
TripleSilentTreeLaws-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- A proved zero jump on a common local radius implies equality at every
independently chosen pair of generic germ-side points. The helper exposes
its local-response premise and transports each side's full chirotope. -/
theorem tree_sides_equal_of_local_zero (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
    (δ : ℝ) (hδ : 0 < δ) (hδr : δ ≤ w.radius)
    (hresponse : ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
      |sMinus.val| < δ → |sPlus.val| < δ →
      treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
        treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn = 0)
    (s t : w.SideParameter) :
    treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn =
      treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn := by
  let q : w.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have hMinus : (w.sideTime false q).val < 0 := by change -(δ / 2) < 0; linarith
  have hPlus : 0 < (w.sideTime true q).val := by change 0 < δ / 2; linarith
  have hMinusNear : |(w.sideTime false q).val| < δ := by
    change |-(δ / 2)| < δ
    rw [abs_neg, abs_of_pos (by linarith : 0 < δ / 2)]
    linarith
  have hPlusNear : |(w.sideTime true q).val| < δ := by
    change |δ / 2| < δ
    rw [abs_of_pos (by linarith : 0 < δ / 2)]
    linarith
  have he : treeCoefficient (w.sideTuple true q).val (w.sideTuple true q).property.1 g hn =
      treeCoefficient (w.sideTuple false q).val (w.sideTuple false q).property.1 g hn :=
    sub_eq_zero.mp (hresponse (w.sideTime false q) (w.sideTime true q) hMinus hPlus hMinusNear hPlusNear)
  have hplusCoeff := treeCoefficient_eq_of_chi (w.sideTuple true q).property.1
    (w.sideTuple true t).property.1
    (fun i j k => generic_family_chi_constant (w.continuous_sideTuple true) q t i j k) g hn
  have hminusCoeff := treeCoefficient_eq_of_chi (w.sideTuple false q).property.1
    (w.sideTuple false s).property.1
    (fun i j k => generic_family_chi_constant (w.continuous_sideTuple false) q s i j k) g hn
  rw [hplusCoeff, hminusCoeff] at he
  exact he

end
end SM.WallGerm
