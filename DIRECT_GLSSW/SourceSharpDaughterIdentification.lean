import SourceSharpDaughterRotationBridge
import SourceSeparatingSupportCharacterization
import SourceUniformSupportCharacterization
import SharpDaughterSelfCrossingCount
import DirectGLSSW.HOMFLY.HOMFLYSkeinEvaluator

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceSharpDaughterIdentification
open GeometricSmoothingWeights PermutationOrbits DaughterFirstReturn
open HOMFLY HOMFLY.PolygonDrawingBridge HOMFLY.SharpDaughter HOMFLY.SharpDaughterRotation
open SourcePolygonData ActualLocalSupports DaughterLocalCrossingEquiv
open HOMFLY.Coefficients PolygonUniformity UniformDaughterSupportLocality
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : SeparatingSupport q hq)
    (A : Component (smoothingDartPermutation q hq.g2 S.val))

/-- The diagram's crossing number counts exactly the actual daughter's retained self-crossings. -/
theorem sharp_crossing_count_eq_source :
    (sharpDaughterDiagram q hq S.val A S.property).nCrossing =
      Fintype.card (PolygonCrossing (componentPolygon q hq S.val A)) := by
  classical
  let E := localCrossingEquiv q hq S.val S.property (componentRoot q hq S.val A)
    (componentRoot_retainedCorner q hq S.val A)
  let E' : LocalCrossing q (smoothingDartPermutation q hq.g2 S.val) S.val
      (componentOf (smoothingDartPermutation q hq.g2 S.val) (componentRoot q hq S.val A)) ≃
      {c : PolygonCrossing q // c ∉ S.val ∧
        ∀ b : Bool, componentOf (P q hq S.val) (Sum.inr (c,b)) = A} :=
    Equiv.subtypeEquivRight (fun c => by
      change (c ∉ S.val ∧ _ ∧ _) ↔ _
      rw [componentRoot_sameComponent]
      constructor
      · rintro ⟨hc,hf,ht⟩
        exact ⟨hc,fun b => by cases b; exact hf; exact ht⟩
      · rintro ⟨hc,h⟩
        exact ⟨hc,h false,h true⟩)
  rw [sharpDaughterDiagram_selfCrossingCount]
  exact (Fintype.card_congr (E.trans E')).symm

/-- The sharp diagram keeps the same actual oriented dart continuation. -/
theorem sharp_oriented_continuation
    (a : Fin (sharpDaughterDiagram q hq S.val A S.property).nArc) :
    arcEquiv q hq S.val A ((sharpDaughterDiagram q hq S.val A S.property).continuation a) =
      fibrePerm (smoothingDartPermutation q hq.g2 S.val) A (arcEquiv q hq S.val A a) :=
  continuation_conjugacy q hq S.val A S.property a

/-- Source all-left/all-right is the literal frozen retained-corner predicate. -/
theorem source_uniform_eq_frozen_corner_condition :
    PolygonUniform (componentPolygon q hq S.val A) ↔
      daughterUniform q hq S.val (componentRoot q hq S.val A) := Iff.rfl

/-- Any single shared evaluator has identical corner coefficients after the
proved geometric crossing and source rotation identifications. -/
theorem corner_coefficient_identification
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff) :
    coeff (H (sharpDaughterDiagram q hq S.val A S.property)
      (arc_count_pos q hq S.val A S.property))
      (1 - (Fintype.card (PolygonCrossing (componentPolygon q hq S.val A)) : ℤ) -
        |signedPolygonRotation (daughter_size_pos q hq S A) (componentPolygon q hq S.val A)
          (daughter_edges_ne_zero q hq S A) (daughter_adjacent_ratio_slitPlane q hq S A)|) 0 =
    coeff (H (sharpDaughterDiagram q hq S.val A S.property)
      (arc_count_pos q hq S.val A S.property))
      (1 - (sharpDaughterDiagram q hq S.val A S.property).nCrossing -
        |sharpDaughterRotationInteger q hq S.val A S.property|) 0 := by
  rw [source_rotation_eq_sharp, sharp_crossing_count_eq_source]

end DirectGLSSW.SourceSharpDaughterIdentification




