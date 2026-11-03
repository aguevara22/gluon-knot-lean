import AuxiliaryCornerAssembly
import GenericCornerIdentityContinuation

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.AuxiliaryCornerAssembly
open GeometricSmoothingWeights DaughterFirstReturn PermutationOrbits
  UniformDaughterSupportLocality SmoothingTurnCount
  HOMFLY HOMFLY.Coefficients CornerStateSumLocality
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- End-to-end reconstruction and continuation from the precise remaining
all-daughter coefficient gate. This gate is an obligation to discharge, not a
new premise of the approved frozen theorem. -/
theorem polygonAmplitude_eq_cornerStateSum_of_all_daughter_factors
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : ∀ (D E : PLLinkDiagram) (hD : 0 < D.nArc) (hE : 0 < E.nArc),
      SignedDiagramIso D E → H D hD = H E hE)
    (hRI : GLSSWRootIndependence)
    (hfactor : ∀ {m : ℕ} (p : Fin m → PlanarPoint ℝ) (hp : CyclicGeneric p)
      (hAux : auxiliaryGenericity p hp)
      (S : {S : Finset (PolygonCrossing p) // uniformDaughterSupport p hp S})
      (C : Component (smoothingDartPermutation p hp.g2 S.val)),
      (-1 : ℚ)^leftTurnCount (componentPolygon p hp S.val C) *
        separatingSmoothingSum (componentPolygon p hp S.val C)
          (hAux S.val S.property.1 (componentRoot p hp S.val C))
          (DaughterNestedWeights.daughter_auxiliaryGenericity p hp S.val S.property.1
            (componentRoot p hp S.val C) (componentRoot_retainedCorner p hp S.val C) hAux) =
        (coeff (H (SharpDaughter.sharpDaughterDiagram p hp S.val C S.property.1)
          (SharpDaughter.arc_count_pos p hp S.val C S.property.1))
          (1 - (SharpDaughter.sharpDaughterDiagram p hp S.val C S.property.1).nCrossing -
            |SharpDaughterRotation.sharpDaughterRotationInteger p hp S.val C S.property.1|) 0 : ℚ))
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    polygonAmplitude q hq = (cornerStateSum H q hq : ℚ) := by
  apply GenericCornerIdentityContinuation.polygonAmplitude_eq_cornerStateSum_of_auxiliaryIdentity
    H hH (fun p hp hAux =>
      polygonAmplitude_eq_cornerStateSum_of_daughter_factors H p hp hAux hRI
        (hfactor p hp hAux)) q hq

#check @polygonAmplitude_eq_cornerStateSum_of_all_daughter_factors

end DirectGLSSW.AuxiliaryCornerAssembly
