import TruncationPositiveNext
import FirstChildEvaluatorZero
import DirectGLSSW.TruncationEdgeOrientation
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open Equiv PolygonDrawing MarkedCycleGaps TruncationDirection TruncationEdgeLift Coefficients
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hs : 0 < ε * scale) (hs1 : ε * scale < 1)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
include E in
theorem truncation_positive_crossing_count :
    (positivePolygonEventDiagram q hq).nCrossing =
      (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ).nCrossing :=
  Fintype.card_congr E

include hp hε hε1 hs hs1 hleft hright hpoint in
theorem truncation_positive_normalizedEvaluator
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H) :
    H (positivePolygonEventDiagram q hq) (positivePolygonEventDiagram_nArc_pos q hq) =
      H (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ)
        (positivePolygonEventDiagram_nArc_pos _ hQ) := by
  let Q := truncateCyclicCorner q a p scale ε
  by_cases hz : (positivePolygonEventDiagram q hq).nCrossing = 0
  · have hzQ : (positivePolygonEventDiagram Q hQ).nCrossing = 0 :=
      (truncation_positive_crossing_count q hq a p scale ε hQ E).symm.trans hz
    exact (normalizedEvaluator_eq_one_of_zero_crossings H hH _
      (positivePolygonEventDiagram_nArc_pos q hq) hz (positivePolygonEventDiagram_componentCount q hq)).trans
      (normalizedEvaluator_eq_one_of_zero_crossings H hH _
        (positivePolygonEventDiagram_nArc_pos Q hQ) hzQ (positivePolygonEventDiagram_componentCount Q hQ)).symm
  · letI : Nonempty (PolygonCrossing q) := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hz)
    apply normalizedEvaluator_eq_of_matching_incoming H hH _ _
      (positivePolygonEventDiagram_nArc_pos q hq) (positivePolygonEventDiagram_nArc_pos Q hQ)
      (crossingFin q) (E.trans (crossingFin Q))
      (polygonEventDiagram_isCycleOn q hq) (polygonEventDiagram_isCycleOn Q hQ)
    · exact truncation_positive_incoming_next q hq a p hp scale ε hε hε1 hs hs1 hQ E hleft hright hpoint
    · intro j; rfl
    · intro j
      change (positivePolygonEventDiagram q hq).overBranch (crossingFin q j) =
        (positivePolygonEventDiagram Q hQ).overBranch (crossingFin Q (E j))
      rw [positivePolygonEventDiagram_overBranch q hq j, positivePolygonEventDiagram_overBranch Q hQ (E j)]
      rw [hleft j, hright j]
      have hd := truncateCyclicCorner_edge_determinant_sign_iff
        (by have := hq.size_ge_three; omega) q a p hp scale ε hε hε1 hs hs1 j.val.1 j.val.2
      exact if_congr hd.symm rfl rfl
    · intro j
      rw [positivePolygonEventDiagram_crossingSign, positivePolygonEventDiagram_crossingSign]
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
