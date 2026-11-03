import GeminiReversal.HOMFLYReversal
import ReversalContract.Contract

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GeminiReversal

open DirectGLSSW
open DirectGLSSW.GeminiReversalContract
open DirectGLSSW.GeometricSmoothingWeights
open DirectGLSSW.HOMFLY
open DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW.HOMFLY.PrincipalTurning

theorem cyclicGeneric_reversal :
    ∀ {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q),
      CyclicGeneric (reversePolygon q) ∧
      (StrictLeft (reversePolygon q) ↔ StrictRight q) ∧
      (StrictRight (reversePolygon q) ↔ StrictLeft q) :=
  DirectGLSSW.cyclicGeneric_reversal_thm

theorem auxiliaryGenericity_reversal :
    ∀ {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (hAux : auxiliaryGenericity q hq),
      ∃ hqr : CyclicGeneric (reversePolygon q), auxiliaryGenericity (reversePolygon q) hqr :=
  DirectGLSSW.auxiliaryGenericity_reversal_thm

theorem separating_vertex_count :
    ∀ {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (S : Finset (PolygonCrossing q))
      (hS : PolygonNonalternation.polygonNonalternating q hq.g2 S),
      smoothingVertexCount q hq S = n + 2 * S.card :=
  DirectGLSSW.separating_vertex_count_thm

theorem amplitude_reversal :
    ∀ (hRI : GLSSWRootIndependence) {n : ℕ}
      (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q),
      ∃ hqr : CyclicGeneric (reversePolygon q),
        polygonAmplitude (reversePolygon q) hqr = (-1 : ℚ) ^ n * polygonAmplitude q hq :=
  DirectGLSSW.amplitude_reversal_thm

theorem primitive_reversal :
    ∀ (hRI : GLSSWRootIndependence) {n : ℕ}
      (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (hAux : auxiliaryGenericity q hq),
      ∃ (hqr : CyclicGeneric (reversePolygon q))
        (hAuxR : auxiliaryGenericity (reversePolygon q) hqr),
        leftCount (reversePolygon q) = n - leftCount q ∧
        separatingSmoothingSum (reversePolygon q) hqr hAuxR =
          (-1 : ℚ) ^ n * separatingSmoothingSum q hq hAux ∧
        normalizedPrimitive (reversePolygon q) hqr hAuxR = normalizedPrimitive q hq hAux := by
  intro hRI n q hq hAux
  exact ⟨cyclicGeneric_reversePolygon q hq,
    auxiliaryGenericity_reversePolygon q hq hAux,
    leftCount_reversePolygon q hq,
    separatingSmoothingSum_reversePolygon hRI q hq hAux
      (auxiliaryGenericity_reversePolygon q hq hAux),
    normalizedPrimitive_reversePolygon hRI q hq hAux
      (auxiliaryGenericity_reversePolygon q hq hAux)⟩

theorem homfly_reversal :
    ∀ {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q),
      ∃ hqr : CyclicGeneric (reversePolygon q),
        (positivePolygonEventDiagram (reversePolygon q) hqr).nCrossing =
          (positivePolygonEventDiagram q hq).nCrossing ∧
        totalTurn (positivePolygonEventDiagram (reversePolygon q) hqr) =
          - totalTurn (positivePolygonEventDiagram q hq) ∧
        turnInteger (positivePolygonEventDiagram (reversePolygon q) hqr) =
          - turnInteger (positivePolygonEventDiagram q hq) ∧
        Gemini.candidateEvaluator (positivePolygonEventDiagram (reversePolygon q) hqr)
          (positivePolygonEventDiagram_nArc_pos _ hqr) =
          Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
            (positivePolygonEventDiagram_nArc_pos _ hq) ∧
        prescribedCorner (reversePolygon q) hqr = prescribedCorner q hq :=
  DirectGLSSW.homfly_reversal_thm

theorem right_turning_reduction :
    ∀ (hRI : GLSSWRootIndependence) {n : ℕ}
      (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (hAux : auxiliaryGenericity q hq) (hRight : StrictRight q)
      (hLeftIdentity : ∀ (p : Fin n → PlanarPoint ℝ) (hp : CyclicGeneric p)
        (hAuxP : auxiliaryGenericity p hp), StrictLeft p →
          normalizedPrimitive p hp hAuxP = (prescribedCorner p hp : ℚ)),
      normalizedPrimitive q hq hAux = (prescribedCorner q hq : ℚ) :=
  DirectGLSSW.right_turning_reduction_thm

end GeminiReversal
