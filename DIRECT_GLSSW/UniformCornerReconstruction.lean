import CornerIdentityReduction
import GeneralSharpRetainedCorner

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.UniformCornerReconstruction
open DirectGLSSW GeometricSmoothingWeights DaughterFirstReturn PermutationOrbits
  UniformDaughterSupportLocality UniformSupportReconstruction SmoothingTurnCount
  AuxiliaryCornerAssembly GeneralSharpRetained Coefficients Gemini PolygonUniformity
  PolygonDrawingBridge PrincipalTurning
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Conditional final candidate theorem: all remaining work is the ordinary-polygon gate. -/
theorem candidate_corner_state_sum_of_uniform_identity
    (hRI : GLSSWRootIndependence)
    (hUniform : ∀ {m : ℕ} (p : Fin m → PlanarPoint ℝ) (hp : CyclicGeneric p)
      (hAux : auxiliaryGenericity p hp), PolygonUniform p →
      (-1 : ℚ) ^ leftTurnCount p * separatingSmoothingSum p hp hAux =
        (coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram p hp)
          (positivePolygonEventDiagram_nArc_pos p hp))
          (1 - (positivePolygonEventDiagram p hp).nCrossing -
            |turnInteger (positivePolygonEventDiagram p hp)|) 0 : ℚ))
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    polygonAmplitude q hq =
      (CornerStateSumLocality.cornerStateSum Gemini.candidateEvaluator q hq : ℚ) := by
  let hSkein := Gemini.all_lowerCrossingEvaluatorSkeinIH
  have hnorm : IsNormalizedDescendingSkeinEvaluator Gemini.candidateEvaluator :=
    Gemini.candidateEvaluator_isNormalized hSkein
  have hIso : ∀ (D E : PLLinkDiagram) (hD : 0 < D.nArc) (hE : 0 < E.nArc),
      SignedDiagramIso D E → Gemini.candidateEvaluator D hD = Gemini.candidateEvaluator E hE := by
    intro D E hD hE I
    exact Gemini.candidateEvaluator_signedDiagramIso hSkein D E hD hE I
  have hfactor : ∀ {m : ℕ} (p : Fin m → PlanarPoint ℝ) (hp : CyclicGeneric p)
      (hAuxP : auxiliaryGenericity p hp)
      (S : {S : Finset (PolygonCrossing p) // uniformDaughterSupport p hp S})
      (C : Component (smoothingDartPermutation p hp.g2 S.val)),
      (-1 : ℚ) ^ leftTurnCount (componentPolygon p hp S.val C) *
        separatingSmoothingSum (componentPolygon p hp S.val C)
          (hAuxP S.val S.property.1 (componentRoot p hp S.val C))
          (DaughterNestedWeights.daughter_auxiliaryGenericity p hp S.val S.property.1
            (componentRoot p hp S.val C)
            (componentRoot_retainedCorner p hp S.val C) hAuxP) =
        (coeff (Gemini.candidateEvaluator
          (SharpDaughter.sharpDaughterDiagram p hp S.val C S.property.1)
          (SharpDaughter.arc_count_pos p hp S.val C S.property.1))
          (1 - (SharpDaughter.sharpDaughterDiagram p hp S.val C S.property.1).nCrossing -
            |SharpDaughterRotation.sharpDaughterRotationInteger p hp S.val C S.property.1|) 0 : ℚ) := by
    intro m p hp hAuxP S C
    let root := componentRoot p hp S.val C
    have hNA := S.property.1
    have hroot : retainedCorner p S.val root := componentRoot_retainedCorner p hp S.val C
    have hDaughter : CyclicGeneric (componentPolygon p hp S.val C) :=
      hAuxP S.val hNA root
    have hDaughterAux : auxiliaryGenericity (componentPolygon p hp S.val C) hDaughter := by
      simpa [componentPolygon, root] using
        (DaughterNestedWeights.daughter_auxiliaryGenericity p hp S.val hNA root hroot hAuxP)
    have hComponentUniform : PolygonUniform (componentPolygon p hp S.val C) :=
      ((uniformDaughterSupport_iff_componentPolygon p hp S.val).mp S.property).2 C
    have hOrdinary := hUniform (componentPolygon p hp S.val C) hDaughter hDaughterAux
      hComponentUniform
    have hcorner := GeneralSharpRetained.corner_coefficient p hp S.val root hNA hroot
      hDaughter Gemini.candidateEvaluator hnorm
    have hcorner' :
        (coeff (Gemini.candidateEvaluator
          (SharpDaughter.sharpDaughterDiagram p hp S.val C S.property.1)
          (SharpDaughter.arc_count_pos p hp S.val C S.property.1))
          (1 - (SharpDaughter.sharpDaughterDiagram p hp S.val C S.property.1).nCrossing -
            |SharpDaughterRotation.sharpDaughterRotationInteger p hp S.val C S.property.1|) 0 : ℚ) =
        (coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram
          (componentPolygon p hp S.val C) hDaughter)
          (positivePolygonEventDiagram_nArc_pos _ hDaughter))
          (1 - (positivePolygonEventDiagram (componentPolygon p hp S.val C) hDaughter).nCrossing -
            |turnInteger (positivePolygonEventDiagram (componentPolygon p hp S.val C) hDaughter)|)
          0 : ℚ) := by
      simpa [GeneralSharpRetained.sharpDiagram, GeneralSharpRetained.retainedDiagram,
        componentPolygon, root, componentRoot_sameComponent] using hcorner
    exact hOrdinary.trans hcorner'.symm
  exact AuxiliaryCornerAssembly.polygonAmplitude_eq_cornerStateSum_of_all_daughter_factors
    Gemini.candidateEvaluator hIso hRI hfactor q hq


end DirectGLSSW.HOMFLY.UniformCornerReconstruction
