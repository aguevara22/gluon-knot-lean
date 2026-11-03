import DirectGLSSW.GeometricSmoothingWeights
import FirstChildEvaluatorZero
import ComponentTurning
import Gemini.Solution

/-! Coordinator-owned meaning definitions. No reversal theorem is asserted here.
The worker outputs must use this literal reversed polygon, actual smoothing sum,
and the existing positive polygon diagram and integer rotation. -/
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.GeminiReversalContract
open GeometricSmoothingWeights HOMFLY HOMFLY.PolygonDrawingBridge
  HOMFLY.PrincipalTurning HOMFLY.Coefficients PermutationOrbits
open scoped BigOperators

/-- Reverse the given indexed polygon, including its canonical label origin. -/
def reversePolygon {n : ℕ} (q : Fin n → PlanarPoint ℝ) : Fin n → PlanarPoint ℝ :=
  fun i => q i.rev

/-- Source left-turn count at each original polygon vertex. -/
def leftCount {n : ℕ} (q : Fin n → PlanarPoint ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin n =>
    0 < planarDet (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i))
      (cyclicTangent q i)).card

def StrictLeft {n : ℕ} (q : Fin n → PlanarPoint ℝ) : Prop :=
  ∀ i : Fin n, 0 < planarDet (cyclicTangent q i)
    (cyclicTangent q (cyclicSuccessor i))

def StrictRight {n : ℕ} (q : Fin n → PlanarPoint ℝ) : Prop :=
  ∀ i : Fin n, planarDet (cyclicTangent q i)
    (cyclicTangent q (cyclicSuccessor i)) < 0

/-- Source normalization of the actual separating smoothing primitive. -/
def normalizedPrimitive {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hAux : auxiliaryGenericity q hq) : ℚ :=
  (-1 : ℚ) ^ leftCount q * separatingSmoothingSum q hq hAux

/-- Actual retained daughter vertex counts in all quotient components. -/
def smoothingVertexCount {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (S : Finset (PolygonCrossing q)) : ℕ :=
  ∑ C : Component (smoothingDartPermutation q hq.g2 S),
    Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 S (componentRoot q hq S C))

/-- The prescribed coefficient; this is not the least occupied a degree. -/
def prescribedCorner {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) : ℤ :=
  coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
    (positivePolygonEventDiagram_nArc_pos q hq))
    (1 - ((positivePolygonEventDiagram q hq).nCrossing : ℤ) -
      |turnInteger (positivePolygonEventDiagram q hq)|) 0
end DirectGLSSW.GeminiReversalContract
