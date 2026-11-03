import MixedEdgeDensityRecursion
import ActualAuxiliaryDensity
import NonuniformPrimitive

set_option autoImplicit false
namespace DirectGLSSW.SourceMixedEdgeFormula
open GeometricSmoothingWeights ChosenEdgeNormalization PermutationOrbits
open MixedEdgeDensityRecursion Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Literal source sum: actual nonempty separating crossing supports on e,
actual oriented smoothing components, and the exact (-1)^(|T|+1) sign. -/
theorem mixed_edge_formula (hRI : GLSSWRootIndependence) {n : ℕ}
    (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P) (e : Fin n)
    (hturn : planarDet (cyclicTangent P e) (cyclicTangent P (cyclicSuccessor e)) *
      planarDet (cyclicTangent P (cyclicVertexIndex e (n-2))) (cyclicTangent P e) < 0)
    (hAux : auxiliaryGenericity P hP) :
    polygonAmplitude P hP = ∑ T : ChosenEdgeSeparatingSupport P hP e,
      (-1 : ℚ)^((T.val.image Subtype.val).card+1) *
        ∏ c : Component (smoothingDartPermutation P hP.g2 (T.val.image Subtype.val)),
          polygonAmplitude (componentPolygon P hP (T.val.image Subtype.val) c)
            (hAux _ T.property.2 (componentRoot P hP _ c)) := by
  simpa only [chosenEdgeSmoothingSum, chosenEdgeSupport_image_card,
    componentAmplitudeProduct, componentAmplitude] using
    mixed_edge_recursion_auxiliary hRI P hP e hturn hAux

/-- In the auxiliary formula domain an uncrossed chosen edge leaves an empty sum. -/
theorem uncrossed_amplitude_zero_auxiliary (hRI : GLSSWRootIndependence) {n : ℕ}
    (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P) (e : Fin n)
    (hturn : planarDet (cyclicTangent P e) (cyclicTangent P (cyclicSuccessor e)) *
      planarDet (cyclicTangent P (cyclicVertexIndex e (n-2))) (cyclicTangent P e) < 0)
    (hAux : auxiliaryGenericity P hP) (hno : ∀ c : EdgeChord P e, False) :
    polygonAmplitude P hP = 0 := by
  haveI : IsEmpty (ChosenEdgeSeparatingSupport P hP e) := ⟨fun T => by
    obtain ⟨c,hc⟩ := T.property.1
    exact hno c⟩
  rw [mixed_edge_formula hRI P hP e hturn hAux]
  exact Finset.sum_eq_zero (fun T _ => isEmptyElim T)

/-- The uncrossed-edge consequence extends to every original generic polygon;
all daughter-genericity and crossing-label transport are produced by density. -/
theorem uncrossed_amplitude_zero (hRI : GLSSWRootIndependence) {n : ℕ}
    (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P) (e : Fin n)
    (hturn : planarDet (cyclicTangent P e) (cyclicTangent P (cyclicSuccessor e)) *
      planarDet (cyclicTangent P (cyclicVertexIndex e (n-2))) (cyclicTangent P e) < 0)
    (hno : ∀ c : EdgeChord P e, False) : polygonAmplitude P hP = 0 := by
  obtain ⟨δ,hδ,hlocal⟩ := exists_configurationNeighborhood_cyclicGeneric_and_signs_amplitude P hP
  obtain ⟨η,hη,hturnlocal⟩ := exists_endpoint_turn_negative_radius P e hturn
  obtain ⟨Q,hQdist,hQ,hAux,E,hlabels,_⟩ :=
    ActualAuxiliaryDensity.exists_auxiliaryGenericity_dist_lt P hP (min δ η) (lt_min hδ hη)
  have hQbox : CrossingIncidenceNeighborhood.CoordClose (min δ η) Q P := by
    rw [dist_pi_lt_iff (lt_min hδ hη)] at hQdist
    intro i
    simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff] using hQdist i
  have hd : CrossingIncidenceNeighborhood.CoordClose δ Q P := fun i =>
    ⟨lt_of_lt_of_le (hQbox i).1 (min_le_left _ _), lt_of_lt_of_le (hQbox i).2 (min_le_left _ _)⟩
  have ht : CrossingIncidenceNeighborhood.CoordClose η Q P := fun i =>
    ⟨lt_of_lt_of_le (hQbox i).1 (min_le_right _ _), lt_of_lt_of_le (hQbox i).2 (min_le_right _ _)⟩
  obtain ⟨hQ',_,hamp⟩ := hlocal Q hd
  have hnQ : ∀ c : EdgeChord Q e, False := by
    intro c
    apply hno ⟨E.symm c.val, ?_⟩
    have hl := hlabels (E.symm c.val)
    rw [E.apply_symm_apply] at hl
    simpa only [hl] using c.property
  rw [← hamp]
  exact uncrossed_amplitude_zero_auxiliary hRI Q hQ e (hturnlocal Q ht) hAux hnQ




end
end DirectGLSSW.SourceMixedEdgeFormula
