import SourceSignedPolygonRotation
import SharpDaughterRotationInteger
import DirectGLSSW.GeometricSmoothingWeights

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceSharpDaughterIdentification
open GeometricSmoothingWeights PermutationOrbits DaughterFirstReturn
open HOMFLY.PolygonDrawingBridge HOMFLY.SharpDaughterRotation SourcePolygonData

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : SeparatingSupport q hq)
    (A : Component (smoothingDartPermutation q hq.g2 S.val))

theorem daughter_size_pos :
    0 < Fintype.card (CornerCoord q hq.g2 S.val (componentRoot q hq S.val A)) := by
  have h := DaughterTurns.daughterVertexCount_ge_three q hq.g2 S.val hq.size_ge_three hq.g1
    (componentRoot q hq S.val A) (componentRoot_retainedCorner q hq S.val A)
  omega

theorem daughter_edges_ne_zero
    (i : Fin (Fintype.card (CornerCoord q hq.g2 S.val (componentRoot q hq S.val A)))) :
    polygonEdgeVector (componentPolygon q hq S.val A) i ≠ 0 :=
  SharpDaughterTurning.sideComplex_ne_zero q hq S.val (componentRoot q hq S.val A)
    (componentRoot_retainedCorner q hq S.val A) i

theorem daughter_adjacent_ratio_slitPlane
    (i : Fin (Fintype.card (CornerCoord q hq.g2 S.val (componentRoot q hq S.val A)))) :
    polygonEdgeVector (componentPolygon q hq S.val A) i /
      polygonEdgeVector (componentPolygon q hq S.val A)
        ((cyclicSuccessorPerm _).symm i) ∈ Complex.slitPlane := by
  have hd := DaughterTurns.daughterTurn_ne_zero q hq.g2 S.val hq.size_ge_three hq.g1
    (componentRoot q hq S.val A) (componentRoot_retainedCorner q hq S.val A) i
  apply Complex.mem_slitPlane_iff.mpr
  right
  rw [Complex.div_im,← sub_div]
  apply div_ne_zero
  · simpa only [polygonEdgeVector, componentPolygon, cyclicTangent,
      daughterSideVector, planarDet, mul_comm] using hd
  · exact mt Complex.normSq_eq_zero.mp (daughter_edges_ne_zero q hq S A _)

/-- The same actual cyclic side vectors and principal angles occur in both sums. -/
theorem daughter_total_turn_literal :
    originalCornerTotalTurn (componentPolygon q hq S.val A) =
      SharpDaughterTurning.cornerTotalTurn q hq S.val (componentRoot q hq S.val A)
        (componentRoot_retainedCorner q hq S.val A) := rfl

/-- Source rotation is available on the actual immersed daughter without daughter G1. -/
theorem source_rotation_eq_sharp :
    signedPolygonRotation (daughter_size_pos q hq S A) (componentPolygon q hq S.val A)
      (daughter_edges_ne_zero q hq S A) (daughter_adjacent_ratio_slitPlane q hq S A) =
      sharpDaughterRotationInteger q hq S.val A S.property := by
  symm
  apply (signedPolygonRotation_total_iff (daughter_size_pos q hq S A)
    (componentPolygon q hq S.val A) (daughter_edges_ne_zero q hq S A)
    (daughter_adjacent_ratio_slitPlane q hq S A) _).mp
  rw [daughter_total_turn_literal]
  exact sharpDaughterRotationInteger_cornerTotalTurn q hq S.val A S.property
    (componentRoot q hq S.val A) (componentRoot_retainedCorner q hq S.val A)
    (componentRoot_sameComponent q hq S.val A)

/-- Every continuous tangent lift of the literal source positional rounding
has the degree used by the sharp-daughter diagram. -/
theorem source_rounding_degree
    (base : Fin (Fintype.card (CornerCoord q hq.g2 S.val (componentRoot q hq S.val A))))
    (δ : HOMFLY.PrincipalTurning.RoundingFraction) (f : ℝ → ℝ) (hf : Continuous f)
    (ha : ∀ t : ℝ, (f t : Real.Angle) =
      ((ImmersedGlobalRounding.curveVelocity (componentPolygon q hq S.val A) base δ t).arg : Real.Angle)) :
    f (Fintype.card (CornerCoord q hq.g2 S.val (componentRoot q hq S.val A))) - f 0 =
      (sharpDaughterRotationInteger q hq S.val A S.property : ℝ) * (2 * Real.pi) := by
  have h := signedPolygonRotation_any_lift (daughter_size_pos q hq S A)
    (componentPolygon q hq S.val A) (daughter_edges_ne_zero q hq S A)
    (daughter_adjacent_ratio_slitPlane q hq S A) base δ f hf ha
  simpa only [source_rotation_eq_sharp] using h

end DirectGLSSW.SourceSharpDaughterIdentification







