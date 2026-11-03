import ConfigurationDaughterTransport
import DirectGLSSW.TruncationComponentWeights
import ChosenEdgeNormalization

set_option autoImplicit false
namespace DirectGLSSW.ConfigurationSmoothingSums
open CrossingRationalParameters CrossingIncidenceNeighborhood LabelledCrossingContinuity
open ConfigurationEventOrder ConfigurationSmoothingTransport DaughterFirstReturn
open GeometricSmoothingWeights GeometricSmoothingSumTransport PolygonNonalternation
open PermutationOrbits ChosenEdgeNormalization
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P Q : Configuration n)
variable (h : ∀ e f, edgeIntersection Q e f ↔ edgeIntersection P e f)
variable (hP : CyclicGeneric P) (hQ : CyclicGeneric Q)
variable (horder : OrderCompatible P Q h hP.g2 hQ.g2)
variable (hAuxP : auxiliaryGenericity P hP) (hAuxQ : auxiliaryGenericity Q hQ)

/-- Transport the actual component amplitude. The auxiliary rooted equality is
explicit here; the neighborhood wrapper derives it by daughter stability. -/
theorem componentAmplitude_transport (hRI : GLSSWRootIndependence)
    (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
    (hamp : ∀ root : PolygonEvent P,
      polygonAmplitude (daughterVertex Q hQ.g2 (mappedSupport P Q h S) (eventEquiv P Q h root))
        (hAuxQ _ ((nonalternating_iff P Q h hP hQ horder S).mp hS) _) =
      polygonAmplitude (daughterVertex P hP.g2 S root) (hAuxP S hS root))
    (c : Component (smoothingDartPermutation P hP.g2 S)) :
    componentAmplitude Q hQ (mappedSupport P Q h S) hAuxQ
      ((nonalternating_iff P Q h hP hQ horder S).mp hS)
      (componentEquiv P Q h hP hQ horder S c) =
    componentAmplitude P hP S hAuxP hS c := by
  let root := componentRoot P hP S c
  have hcomp : componentOf (smoothingDartPermutation Q hQ.g2 (mappedSupport P Q h S))
      (eventEquiv P Q h root) = componentEquiv P Q h hP hQ horder S c := by
    rw [← componentEquiv_componentOf]
    exact congrArg (componentEquiv P Q h hP hQ horder S) (componentRoot_sameComponent P hP S c)
  rw [TruncationComponentWeights.componentAmplitude_eq_at_root hRI Q hQ
    (mappedSupport P Q h S) hAuxQ _ _ (eventEquiv P Q h root) hcomp]
  exact hamp root

theorem componentAmplitudeProduct_transport (hRI : GLSSWRootIndependence)
    (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
    (hamp : ∀ root : PolygonEvent P,
      polygonAmplitude (daughterVertex Q hQ.g2 (mappedSupport P Q h S) (eventEquiv P Q h root))
        (hAuxQ _ ((nonalternating_iff P Q h hP hQ horder S).mp hS) _) =
      polygonAmplitude (daughterVertex P hP.g2 S root) (hAuxP S hS root)) :
    componentAmplitudeProduct Q hQ (mappedSupport P Q h S) hAuxQ
      ((nonalternating_iff P Q h hP hQ horder S).mp hS) =
    componentAmplitudeProduct P hP S hAuxP hS := by
  symm
  unfold componentAmplitudeProduct
  apply Fintype.prod_equiv (componentEquiv P Q h hP hQ horder S)
  intro c
  exact (componentAmplitude_transport P Q h hP hQ horder hAuxP hAuxQ hRI S hS hamp c).symm

variable (hamp : ∀ (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
    (root : PolygonEvent P),
    polygonAmplitude (daughterVertex Q hQ.g2 (mappedSupport P Q h S) (eventEquiv P Q h root))
      (hAuxQ _ ((nonalternating_iff P Q h hP hQ horder S).mp hS) _) =
    polygonAmplitude (daughterVertex P hP.g2 S root) (hAuxP S hS root))

include hamp in
/-- The full separating primitive preserves its exact support signs and actual
component products under rooted daughter-amplitude transport. -/
theorem separatingSmoothingSum_transport (hRI : GLSSWRootIndependence) :
    separatingSmoothingSum Q hQ hAuxQ = separatingSmoothingSum P hP hAuxP := by
  symm
  let E := separatingSupportEquiv P hP Q hQ (labelEquiv P Q h)
    (nonalternating_iff P Q h hP hQ horder)
  unfold separatingSmoothingSum
  apply Fintype.sum_equiv E
  intro S
  have hc : (E S).val.card = S.val.card := Finset.card_map _
  rw [hc]
  congr 1
  exact (componentAmplitudeProduct_transport P Q h hP hQ horder hAuxP hAuxQ hRI
    S.val S.property (hamp S.val S.property)).symm

/-- Exact crossing labels restrict to crossings of the same chosen edge. -/
def edgeChordEquiv (e : Fin n) : EdgeChord P e ≃ EdgeChord Q e where
  toFun c := ⟨labelEquiv P Q h c.val,c.property⟩
  invFun c := ⟨(labelEquiv P Q h).symm c.val,c.property⟩
  left_inv c := Subtype.ext ((labelEquiv P Q h).symm_apply_apply c.val)
  right_inv c := Subtype.ext ((labelEquiv P Q h).apply_symm_apply c.val)

theorem edgeChordSupport_image (e : Fin n) (T : Finset (EdgeChord P e)) :
    (T.map (edgeChordEquiv P Q h e).toEmbedding).image Subtype.val =
      mappedSupport P Q h (T.image Subtype.val) := by
  simp only [mappedSupport,Finset.map_eq_image,Finset.image_image]
  rfl

include horder in
theorem edgeChordSupport_nonalternating_iff (e : Fin n) (T : Finset (EdgeChord P e)) :
    polygonNonalternating P hP.g2 (T.image Subtype.val) ↔
    polygonNonalternating Q hQ.g2
      ((T.map (edgeChordEquiv P Q h e).toEmbedding).image Subtype.val) := by
  rw [edgeChordSupport_image]
  exact nonalternating_iff P Q h hP hQ horder (T.image Subtype.val)

/-- Nonempty separating supports on the chosen edge correspond bijectively. -/
def chosenEdgeSupportEquiv (e : Fin n) :
    ChosenEdgeSeparatingSupport P hP e ≃ ChosenEdgeSeparatingSupport Q hQ e :=
  Equiv.subtypeEquiv (edgeChordEquiv P Q h e).finsetCongr (fun T =>
    and_congr Finset.map_nonempty.symm
      (edgeChordSupport_nonalternating_iff P Q h hP hQ horder e T))

theorem chosenEdgeSupportEquiv_card (e : Fin n) (T : ChosenEdgeSeparatingSupport P hP e) :
    (chosenEdgeSupportEquiv P Q h hP hQ horder e T).val.card = T.val.card :=
  Finset.card_map _

theorem chosenEdgeSupportEquiv_image (e : Fin n) (T : ChosenEdgeSeparatingSupport P hP e) :
    (chosenEdgeSupportEquiv P Q h hP hQ horder e T).val.image Subtype.val =
      mappedSupport P Q h (T.val.image Subtype.val) :=
  edgeChordSupport_image P Q h e T.val

include hamp in
/-- Transport the actual mixed-edge right-hand side at the unchanged edge label. -/
theorem chosenEdgeSmoothingSum_transport (hRI : GLSSWRootIndependence) (e : Fin n) :
    chosenEdgeSmoothingSum Q hQ e hAuxQ = chosenEdgeSmoothingSum P hP e hAuxP := by
  symm
  unfold chosenEdgeSmoothingSum
  apply Fintype.sum_equiv (chosenEdgeSupportEquiv P Q h hP hQ horder e)
  intro T
  rw [chosenEdgeSupportEquiv_card]
  apply congrArg (fun x : ℚ => (-1 : ℚ)^(T.val.card+1)*x)
  have hi := chosenEdgeSupportEquiv_image P Q h hP hQ horder e T
  simpa only [← hi] using
    (componentAmplitudeProduct_transport P Q h hP hQ horder hAuxP hAuxQ hRI
      (T.val.image Subtype.val) T.property.2 (hamp (T.val.image Subtype.val) T.property.2)).symm











end
end DirectGLSSW.ConfigurationSmoothingSums
