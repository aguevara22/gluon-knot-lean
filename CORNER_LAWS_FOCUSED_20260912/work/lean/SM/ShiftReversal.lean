import SM.ReversalChambers
import SM.ReversalCrossings
import SM.TurnCountReversal
import SM.RotationReversal
import SM.VisibleRelabel

/-! Proposed repair of source lem:shift. The only additional condition is
explicit and local to the left-count conclusion: every turn must be nonzero.
All other formulas retain their actual tuple/generic/regular domains. This is
not mapped or counted as the unqualified original source theorem. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem shift_reversal_corrected (hn : 3 ≤ n) (P : LabelledTuple n) :
    (∀ i j k, chi (shift 1 P) i j k = chi P (i + 1) (j + 1) (k + 1) ∧
      chi (reversal P) i j k = chi P (2 - i) (2 - j) (2 - k)) ∧
    (∀ i t, edgePoint (shift 1 P) i t = edgePoint P (i + 1) t ∧
      edgePoint (reversal P) i t = edgePoint P (1 - i) (1 - t)) ∧
    (Generic (shift 1 P) ↔ Generic P) ∧ (Generic (reversal P) ↔ Generic P) ∧
    Function.Surjective (genericShift (1 : ZMod n)) ∧
    Function.Surjective (genericReversal (n := n)) ∧
    (∀ Q : GenericTuple n,
      genericShift 1 '' labelledChamber Q = labelledChamber (genericShift 1 Q)) ∧
    (∀ Q : GenericTuple n,
      genericReversal '' labelledChamber Q = labelledChamber (genericReversal Q)) ∧
    (∀ Q : GenericTuple n, polygonProjection (genericShift 1 Q) = polygonProjection Q) ∧
    (∀ Q : GenericPolygon n,
      genericPolygonReversal '' chamber Q = chamber (genericPolygonReversal Q)) ∧
    crossingSet (shift 1 P) = (crossingSet P).image (translateSupport (-1)) ∧
    crossingSet (reversal P) = (crossingSet P).image reverseSupport ∧
    (∀ i, turn (shift 1 P) i = turn P (i + 1) ∧
      turn (reversal P) i = -turn P (2 - i)) ∧
    leftTurns (reversal P) = rightTurns P ∧
    ((∀ i, turn P i ≠ 0) → leftTurns (reversal P) = n - leftTurns P) ∧
    (Regular P → rotationNumber (shift 1 P) = rotationNumber P ∧
      rotationNumber (reversal P) = -rotationNumber P) := by
  exact ⟨fun i j k => ⟨chi_shift 1 P i j k, chi_reversal P i j k⟩,
    fun i t => ⟨edgePoint_shift 1 P i t, edgePoint_reversal P i t⟩,
    generic_shift 1 P, generic_reversal P,
    (genericShiftHomeomorph 1).surjective, genericReversalHomeomorph.surjective,
    genericShift_labelledChamber 1, genericReversal_labelledChamber,
    projection_genericShift 1, genericPolygonReversal_chamber,
    crossingSet_shift P 1, crossingSet_reversal P,
    fun i => ⟨turn_shift 1 P i, turn_reversal P i⟩,
    leftTurns_reversal_eq_right P, leftTurns_reversal_of_nonzero P,
    fun h => ⟨rotationNumber_shift 1 P, rotationNumber_reversal h⟩⟩

end SM
