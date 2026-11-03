import ConfigurationSmoothingSums
import ConfigurationDaughterStability

set_option autoImplicit false
namespace DirectGLSSW.ConfigurationSmoothingNeighborhood
open CrossingRationalParameters CrossingIncidenceNeighborhood LabelledCrossingContinuity
open ConfigurationEventOrder ConfigurationSmoothingTransport DaughterFirstReturn
open GeometricSmoothingWeights PolygonNonalternation ChosenEdgeNormalization
open ConfigurationDaughterStability ConfigurationSmoothingSums
noncomputable section

/-- On the original auxiliary domain, one actual coordinate neighborhood keeps
both the separating primitive and every chosen-edge smoothing sum constant.
Only root independence and original G1–G2/auxiliary genericity are assumed.
The crossing correspondence, event order and all daughter equalities are derived. -/
theorem exists_smoothingSums_neighborhood (hRI : GLSSWRootIndependence) {n : ℕ}
    (P : Configuration n) (hP : CyclicGeneric P) (hAux : auxiliaryGenericity P hP) :
    ∃ η : ℝ, 0 < η ∧ ∀ Q : Configuration n, CoordClose η Q P →
      ∃ hQ : CyclicGeneric Q, ∃ hAuxQ : auxiliaryGenericity Q hQ,
        separatingSmoothingSum Q hQ hAuxQ = separatingSmoothingSum P hP hAux ∧
        ∀ e : Fin n, chosenEdgeSmoothingSum Q hQ e hAuxQ =
          chosenEdgeSmoothingSum P hP e hAux := by
  obtain ⟨η,hη,hBox,hall⟩ := exists_configuration_daughter_stability P hP hAux
  refine ⟨η,hη,?_⟩
  intro Q hnear
  let q : Box P η := ⟨Q,hnear⟩
  obtain ⟨hQ,horder,hAuxQ,hstable⟩ := hall q
  have hamp : ∀ (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
      (root : PolygonEvent P),
      polygonAmplitude (daughterVertex Q hQ.g2 (mappedSupport P Q (hBox Q hnear).1 S)
        (eventEquiv P Q (hBox Q hnear).1 root))
        (hAuxQ _ ((nonalternating_iff P Q (hBox Q hnear).1 hP hQ horder S).mp hS) _) =
      polygonAmplitude (daughterVertex P hP.g2 S root) (hAux S hS root) :=
    fun S hS root => (hstable S hS root).2
  refine ⟨hQ,hAuxQ,?_,?_⟩
  · exact separatingSmoothingSum_transport P Q (hBox Q hnear).1 hP hQ horder hAux hAuxQ hamp hRI
  · intro e
    exact chosenEdgeSmoothingSum_transport P Q (hBox Q hnear).1 hP hQ horder hAux hAuxQ hamp hRI e


end
end DirectGLSSW.ConfigurationSmoothingNeighborhood
