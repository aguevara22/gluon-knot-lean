import CornerStateSumLocality
import ActualAuxiliaryDensity
import PolygonGermAmplitude

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.GenericCornerIdentityContinuation

open Filter Topology GeometricSmoothingWeights HOMFLY HOMFLY.Coefficients CornerStateSumLocality

/-- Internal assembly of the manuscript's final density argument. The auxiliary
identity remains an explicit proof obligation; this theorem does not establish
that identity or the existence of the normalized evaluator. The conclusion uses
the literal corner-state sum, including its rational cast. -/
theorem polygonAmplitude_eq_cornerStateSum_of_auxiliaryIdentity
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : ∀ (D E : PLLinkDiagram) (hD : 0 < D.nArc) (hE : 0 < E.nArc),
      SignedDiagramIso D E → H D hD = H E hE)
    {n : ℕ}
    (hAuxIdentity : ∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q),
      auxiliaryGenericity q hq →
        polygonAmplitude q hq = (cornerStateSum H q hq : ℚ))
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    polygonAmplitude q hq = (cornerStateSum H q hq : ℚ) := by
  have hA : ∀ᶠ q' in 𝓝 q, ∃ hg : CyclicGeneric q',
      polygonAmplitude q' hg = polygonAmplitude q hq :=
    PolygonGermStability.eventually_polygonAmplitude_stability (fun q' => q')
      (fun v => (continuous_apply v).continuousAt) hq
  have hC := eventually_cornerStateSum_eq H hH q hq
  obtain ⟨q', hnear, hq', hAux', _⟩ :=
    ActualAuxiliaryDensity.exists_auxiliaryGenericity_mem_nhds q hq
      ({q' | ∃ hg : CyclicGeneric q',
          polygonAmplitude q' hg = polygonAmplitude q hq} ∩
        {q' | ∃ hg : CyclicGeneric q',
          cornerStateSum H q' hg = cornerStateSum H q hq})
      (Filter.inter_mem hA hC)
  obtain ⟨hgA, hsameA⟩ := hnear.1
  obtain ⟨hgC, hsameC⟩ := hnear.2
  calc
    polygonAmplitude q hq = polygonAmplitude q' hq' := hsameA.symm
    _ = (cornerStateSum H q' hq' : ℚ) := hAuxIdentity q' hq' hAux'
    _ = (cornerStateSum H q hq : ℚ) := congrArg (fun z : ℤ => (z : ℚ)) hsameC



end DirectGLSSW.GenericCornerIdentityContinuation
