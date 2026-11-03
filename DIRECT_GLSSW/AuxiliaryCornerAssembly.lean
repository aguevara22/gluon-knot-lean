import UniformSupportReconstruction
import SmoothingTurnSigns
import TurnSignLiteralBridge
import CornerStateSumLocality

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.AuxiliaryCornerAssembly
open GeometricSmoothingWeights DaughterFirstReturn PermutationOrbits
  UniformDaughterSupportLocality UniformSupportReconstruction SmoothingTurnCount
  HOMFLY HOMFLY.Coefficients CornerStateSumLocality
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Finite reconstruction with its remaining factor identification made explicit.
The caller must prove the normalized primitive/actual sharp coefficient identity
for every daughter in every literal uniform support. This intermediate does not
assert that factor identity or receive whole-source proof credit. -/
theorem polygonAmplitude_eq_cornerStateSum_of_daughter_factors
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq) (hRI : GLSSWRootIndependence)
    (hfactor : ∀ (S : {S : Finset (PolygonCrossing q) // uniformDaughterSupport q hq S})
      (C : Component (smoothingDartPermutation q hq.g2 S.val)),
      (-1 : ℚ) ^ leftTurnCount (componentPolygon q hq S.val C) *
        separatingSmoothingSum (componentPolygon q hq S.val C)
          (hAux S.val S.property.1 (componentRoot q hq S.val C))
          (DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.val S.property.1
            (componentRoot q hq S.val C) (componentRoot_retainedCorner q hq S.val C) hAux) =
        (coeff (H (SharpDaughter.sharpDaughterDiagram q hq S.val C S.property.1)
          (SharpDaughter.arc_count_pos q hq S.val C S.property.1))
          (1 - (SharpDaughter.sharpDaughterDiagram q hq S.val C S.property.1).nCrossing -
            |SharpDaughterRotation.sharpDaughterRotationInteger q hq S.val C S.property.1|) 0 : ℚ)) :
    polygonAmplitude q hq = (cornerStateSum H q hq : ℚ) := by
  rw [polygonAmplitude_eq_sum_uniformDaughterPrimitives q hq hAux hRI]
  unfold cornerStateSum
  dsimp only
  push_cast
  rw [← leftTurnCount_eq_literal_filter_card q, Finset.mul_sum]
  refine Finset.sum_congr (by ext S; simp only [Finset.mem_univ]) ?_
  intro S _
  let w : Component (smoothingDartPermutation q hq.g2 S.val) → ℚ := fun C =>
    coeff (H (SharpDaughter.sharpDaughterDiagram q hq S.val C S.property.1)
      (SharpDaughter.arc_count_pos q hq S.val C S.property.1))
      (1 - (SharpDaughter.sharpDaughterDiagram q hq S.val C S.property.1).nCrossing -
        |SharpDaughterRotation.sharpDaughterRotationInteger q hq S.val C S.property.1|) 0
  have hf (C : Component (smoothingDartPermutation q hq.g2 S.val)) :
      separatingSmoothingSum (componentPolygon q hq S.val C)
        (hAux S.val S.property.1 (componentRoot q hq S.val C))
        (DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.val S.property.1
          (componentRoot q hq S.val C) (componentRoot_retainedCorner q hq S.val C) hAux) =
      (-1 : ℚ)^leftTurnCount (componentPolygon q hq S.val C) * w C := by
    have hs : ((-1 : ℚ)^leftTurnCount (componentPolygon q hq S.val C)) *
        ((-1 : ℚ)^leftTurnCount (componentPolygon q hq S.val C)) = 1 := by
      rw [← mul_pow]
      norm_num
    have h := congrArg
      (fun x : ℚ => (-1 : ℚ)^leftTurnCount (componentPolygon q hq S.val C) * x)
      (hfactor S C)
    simpa only [← mul_assoc, hs, one_mul] using h
  calc
    componentPrimitiveProduct q hq hAux ⟨S.val, S.property.1⟩ =
        ∏ C : Component (smoothingDartPermutation q hq.g2 S.val),
          (-1 : ℚ)^leftTurnCount (componentPolygon q hq S.val C) * w C := by
      unfold componentPrimitiveProduct
      exact Finset.prod_congr rfl (fun C _ => hf C)
    _ = (-1 : ℚ)^leftTurnCount q * (-1 : ℚ)^S.val.card * ∏ C, w C :=
      product_daughter_signed_weights q hq S.val w
    _ = _ := by simp only [w, mul_assoc]

#check @polygonAmplitude_eq_cornerStateSum_of_daughter_factors

end DirectGLSSW.AuxiliaryCornerAssembly
