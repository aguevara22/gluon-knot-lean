import WorkingExactCalculationChart
import WorkingChamberDensity
import ReversalConsumerPrep
import GeminiReversal.Solution
import GeneralSharpRetainedCorner
import PolygonGermAmplitude

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceWorkingReconstruction
open DirectGLSSW.HOMFLY
open DirectGLSSW GeometricSmoothingWeights DaughterFirstReturn PermutationOrbits
  UniformDaughterSupportLocality UniformSupportReconstruction SmoothingTurnCount
  AuxiliaryCornerAssembly GeneralSharpRetained Coefficients Gemini PolygonUniformity
  PolygonDrawingBridge PrincipalTurning
open scoped BigOperators
attribute [local instance] Classical.propDecidable


open Filter Topology Set SourceAuxiliaryWorkingDomain CyclicCarrierClearing

/-- Finite reconstruction on actual auxiliary data, without generic continuation. -/
theorem auxiliary_candidate_corner_identity
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq) :
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
    have hOrdinary := GeminiReversalConsumerPrep.polygon_uniform_identity_of_right_reduction
      hRI _root_.GeminiReversal.right_turning_reduction
      (componentPolygon p hp S.val C) hDaughter hDaughterAux
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
  exact AuxiliaryCornerAssembly.polygonAmplitude_eq_cornerStateSum_of_daughter_factors
    Gemini.candidateEvaluator q hq hAux hRI (hfactor q hq hAux)

/-- Extend an identity on the explicit working locus using its actual chamber
closure and the actual amplitude/state-sum germs. -/
theorem candidate_identity_from_working_chamber
    {n : ℕ} (c : MvPolynomial (Fin n × Fin 2) ℝ)
    (hDense : Dense {r : Fin n → PlanarPoint ℝ |
      MvPolynomial.eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0})
    (hOpen : IsOpen {r : Fin n → PlanarPoint ℝ |
      MvPolynomial.eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0})
    (hIdentity : ∀ (r : Fin n → PlanarPoint ℝ) (hr : CyclicGeneric r),
      MvPolynomial.eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0 →
      polygonAmplitude r hr = (CornerStateSumLocality.cornerStateSum Gemini.candidateEvaluator r hr : ℚ))
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    polygonAmplitude q hq =
      (CornerStateSumLocality.cornerStateSum Gemini.candidateEvaluator q hq : ℚ) := by
  have hA : ∀ᶠ r in 𝓝 q, ∃ hr : CyclicGeneric r,
      polygonAmplitude r hr = polygonAmplitude q hq :=
    PolygonGermStability.eventually_polygonAmplitude_stability (fun r => r)
      (fun v => (continuous_apply v).continuousAt) hq
  have hC := CornerStateSumLocality.eventually_cornerStateSum_eq Gemini.candidateEvaluator
    (Gemini.candidateEvaluator_signedDiagramIso Gemini.all_lowerCrossingEvaluatorSkeinIH) q hq
  have hch := workingAuxiliaryDomain_on_chamber c hDense hOpen q hq
  have hcl := hch.2.2.1 (mem_connectedComponentIn hq)
  obtain ⟨r,hnear,hrwork⟩ := mem_closure_iff_nhds.mp hcl _ (Filter.inter_mem hA hC)
  obtain ⟨hrA,hEqA⟩ := hnear.1
  obtain ⟨hrC,hEqC⟩ := hnear.2
  have hr := (mem_workingAuxiliaryDomain_iff c r).mp hrwork.2
  calc
    polygonAmplitude q hq = polygonAmplitude r hr.1 := hEqA.symm
    _ = (CornerStateSumLocality.cornerStateSum Gemini.candidateEvaluator r hr.1 : ℚ) :=
      hIdentity r hr.1 hr.2
    _ = (CornerStateSumLocality.cornerStateSum Gemini.candidateEvaluator q hq : ℚ) :=
      congrArg (fun z : ℤ => (z : ℚ)) hEqC

/-- The complete generic candidate identity consumes the new exact working
certificate and its chamber density; no sealed final identity is invoked. -/
theorem candidate_corner_identity_via_working_domain
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    polygonAmplitude q hq =
      (CornerStateSumLocality.cornerStateSum Gemini.candidateEvaluator q hq : ℚ) := by
  obtain ⟨c,hc,hDense,hOpen,hChambers,hHistory,hFixed,hChart,hExact⟩ :=
    exists_working_auxiliary_domain_with_exact_calculation_charts hRI q hq
  apply candidate_identity_from_working_chamber c hDense hOpen ?_ q hq
  intro r hr hrc
  have hAux : auxiliaryGenericity r hr :=
    (hHistory r hr hrc n r hr (.nil _)).1
  exact auxiliary_candidate_corner_identity hRI r hr hAux

end DirectGLSSW.SourceWorkingReconstruction



