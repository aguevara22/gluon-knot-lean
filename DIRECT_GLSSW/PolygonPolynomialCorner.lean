import FramedPolynomialCorner
import PositivePolygonTurns
import FirstChildEvaluatorZero
import PolygonRotationSum

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open Coefficients LowestRowContract PrincipalTurning PermutationOrbits FramedPolynomial

/-- Nonnegative actual planar determinants imply nonnegative principal turns. -/
theorem principalTurn_nonneg_of_turnDet (D : PLLinkDiagram) (e : Fin D.nArc)
    (h : 0 ≤ SmoothingCornerGeometry.turnDet D e) : 0 ≤ turn D e := by
  apply Complex.arg_nonneg_iff.mpr
  rw [Complex.div_im, ← sub_div]
  apply div_nonneg _ (Complex.normSq_nonneg _)
  simpa only [PrincipalTurning.arcVector, SmoothingCornerGeometry.turnDet,
    SmoothingCornerGeometry.arcVector, planarDet, mul_comm] using h

/-- Every component rotation is nonnegative if all actual turns are nonnegative. -/
theorem componentTurnInteger_nonneg_of_turnDet (D : PLLinkDiagram)
    (h : ∀ e : Fin D.nArc, 0 ≤ SmoothingCornerGeometry.turnDet D e)
    (C : diagramComponent D) : 0 ≤ componentTurnInteger D C := by
  have hs : 0 ≤ componentTotalTurn D C :=
    Finset.sum_nonneg (fun e _ => principalTurn_nonneg_of_turnDet D e.val (h e.val))
  rw [componentTotalTurn_eq_integer] at hs
  have hr : (0 : ℝ) ≤ (componentTurnInteger D C : ℝ) :=
    (mul_nonneg_iff_of_pos_right (mul_pos (by norm_num) Real.pi_pos)).mp hs
  exact_mod_cast hr

namespace PolygonDrawingBridge

/-- Actual uniformly-left polygons discharge the sign and rotation premises
of the polynomial-witness coefficient calculation. Only the polynomial witness
remains conditional. The degree uses the existing total rotation integer. -/
theorem positivePolygon_polynomialWitness_corner {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ e : Fin n, 0 < planarDet (cyclicTangent q e)
      (cyclicTangent q (cyclicSuccessor e)))
    (F : Polynomial ℤ)
    (hF : framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
      (positivePolygonEventDiagram_nArc_pos q hq)
      (componentOf (positivePolygonEventDiagram q hq).continuation
        ⟨0,positivePolygonEventDiagram_nArc_pos q hq⟩) = framedVariable * polynomialValue F) :
    (∀ i : ℤ, i < 1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
      |turnInteger (positivePolygonEventDiagram q hq)| →
      coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
        (positivePolygonEventDiagram_nArc_pos q hq)) i 0 = 0) ∧
    coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
      (positivePolygonEventDiagram_nArc_pos q hq))
      (1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
        |turnInteger (positivePolygonEventDiagram q hq)|) 0 = F.eval (-1) := by
  let D := positivePolygonEventDiagram q hq
  let e : Fin D.nArc := ⟨0,positivePolygonEventDiagram_nArc_pos q hq⟩
  let C := componentOf D.continuation e
  have hr := componentTurnInteger_nonneg_of_turnDet D
    (positivePolygonEventDiagram_turn_nonneg_of_uniform_left q hq hleft) C
  have htotal : componentTotalTurn D C = totalTurn D :=
    (positivePolygonEventDiagram_componentTotalTurn q hq e).trans
      (positivePolygonEventDiagram_totalTurn q hq).symm
  have hi : componentTurnInteger D C = turnInteger D := by
    apply (turnInteger_unique D _ _).symm
    rw [← htotal,componentTotalTurn_eq_integer]
  have hc := framedKnotRow_polynomialWitness_prescribed_corner
    Gemini.candidateEvaluator D (positivePolygonEventDiagram_nArc_pos q hq) C F
    (positivePolygonEventDiagram_crossingSign q hq) hr hF
  simpa only [hi] using hc

end PolygonDrawingBridge



end DirectGLSSW.HOMFLY
