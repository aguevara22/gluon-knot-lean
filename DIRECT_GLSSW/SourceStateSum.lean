import SourceSharpDaughterIdentification
import SourceUniformSupportCharacterization
import CornerStateSumLocality

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceStateSum
open scoped BigOperators Classical
open DirectGLSSW.HOMFLY DirectGLSSW.HOMFLY.Coefficients
open DirectGLSSW.GeometricSmoothingWeights DirectGLSSW.PermutationOrbits
open DirectGLSSW.PolygonUniformity DirectGLSSW.UniformSupportReconstruction
open DirectGLSSW.SourceSharpDaughterIdentification
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 10000000 in
/-- The existing finite corner state sum, written with the source's exact
uniform separating supports and prescribed corner coefficient. The same
evaluator `H` appears in every summand. -/
theorem cornerStateSum_eq_source_formula
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    CornerStateSumLocality.cornerStateSum H q hq =
      (-1 : ℤ) ^ OriginalLeftTurnLocality.leftTurnCount q *
      ∑ S : {S : SeparatingSupport q hq //
          ∀ A : Component (smoothingDartPermutation q hq.g2 S.val),
            PolygonUniform (componentPolygon q hq S.val A)},
        (-1 : ℤ) ^ S.1.1.card *
        ∏ A : Component (smoothingDartPermutation q hq.g2 S.1.1),
          coeff
            (H (HOMFLY.SharpDaughter.sharpDaughterDiagram q hq S.1.1 A S.1.2)
              (HOMFLY.SharpDaughter.arc_count_pos q hq S.1.1 A S.1.2))
            (1 - (Fintype.card (PolygonCrossing (componentPolygon q hq S.1.1 A)) : ℤ) -
              |SourcePolygonData.signedPolygonRotation
                (daughter_size_pos q hq S.1 A)
                (componentPolygon q hq S.1.1 A)
                (daughter_edges_ne_zero q hq S.1 A)
                (daughter_adjacent_ratio_slitPlane q hq S.1 A)|) 0 := by
  classical
  let SourceSupports := {S : SeparatingSupport q hq //
      ∀ A : Component (smoothingDartPermutation q hq.g2 S.val),
        PolygonUniform (componentPolygon q hq S.val A)}
  let InternalSupports := {S : Finset (PolygonCrossing q) //
      UniformDaughterSupportLocality.uniformDaughterSupport q hq S}
  let E : SourceSupports ≃ InternalSupports := uniformSupportEquiv q hq
  letI : Fintype InternalSupports := Fintype.ofFinite _
  unfold CornerStateSumLocality.cornerStateSum
  change (-1 : ℤ) ^ OriginalLeftTurnLocality.leftTurnCount q *
      (∑ S : InternalSupports,
        (-1 : ℤ) ^ S.1.card *
          ∏ A : Component (smoothingDartPermutation q hq.g2 S.1),
            coeff (H (HOMFLY.SharpDaughter.sharpDaughterDiagram q hq S.1 A S.2.1)
              (HOMFLY.SharpDaughter.arc_count_pos q hq S.1 A S.2.1))
              (1 - (HOMFLY.SharpDaughter.sharpDaughterDiagram q hq S.1 A S.2.1).nCrossing -
                |HOMFLY.SharpDaughterRotation.sharpDaughterRotationInteger
                  q hq S.1 A S.2.1|) 0) = _
  congr 1
  apply Fintype.sum_equiv E.symm
  intro S
  have hsupport : (E.symm S).1.1 = S.1 := rfl
  simp only [hsupport]
  congr 1
  apply Finset.prod_congr rfl
  intro A hA
  exact (corner_coefficient_identification q hq (E.symm S).1 A H).symm

end DirectGLSSW.SourceStateSum

