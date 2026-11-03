import PhysicalCalculationExists
import GeometricCursorCorner
import GeometricCursorOverStep
import GeometricCursorUnderStep
import GeometricCursorTerminal
import CompleteOverStepWithin
import CompleteUnderStepWithin
import UniformCornerG
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open Coefficients PrincipalTurning PolygonDrawingBridge SmoothingCornerGeometry GeometricSmoothingWeights

/-- The genuine outer strong induction hypothesis on strictly fewer original
polygon crossings, with exactly the source geometric hypotheses. -/
abbrev SmallerPolygonCornerIH {N : ℕ} (q : Fin N → PlanarPoint ℝ) : Prop :=
  ∀ {k : ℕ} (P : Fin k → PlanarPoint ℝ) (hP : CyclicGeneric P)
    (hleftP : ∀ i, 0<planarDet (cyclicTangent P i) (cyclicTangent P (cyclicSuccessor i)))
    (hAuxP : auxiliaryGenericity P hP)
    (hcard : Fintype.card (PolygonCrossing P)<Fintype.card (PolygonCrossing q)),
    let ell := (Finset.univ.filter (fun i : Fin k =>
      0<planarDet (cyclicTangent P ((cyclicSuccessorPerm k)⁻¹ i)) (cyclicTangent P i))).card
    (-1 : ℚ)^ell*GeometricSmoothingWeights.separatingSmoothingSum P hP hAuxP =
      coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram P hP)
        (positivePolygonEventDiagram_nArc_pos P hP))
        (1-((positivePolygonEventDiagram P hP).nCrossing : ℤ)-
          |turnInteger (positivePolygonEventDiagram P hP)|) 0
end DirectGLSSW.HOMFLY.PhysicalCursorComparison
