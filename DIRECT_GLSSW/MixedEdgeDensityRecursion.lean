import ConfigurationSmoothingNeighborhood
import GenericSecantDensity
import NormalizedMixedEdgeRecursion

set_option autoImplicit false
namespace DirectGLSSW.MixedEdgeDensityRecursion
open CrossingRationalParameters CrossingIncidenceNeighborhood LabelledCrossingContinuity
open ConfigurationSmoothingNeighborhood ChosenEdgeNormalization GeometricSmoothingWeights
open FixedEndpointSecantDensity ExtendedReturnArcGeometry InteriorEdgeEvents
open CapCriticalTimes CapCriticalEventGeometry NormalizedMixedEdgeRecursion
open EdgeAffineNormalization
open Filter Topology
noncomputable section

/-- The endpoint-turn product is a continuous polynomial in the actual vertices. -/
theorem exists_endpoint_turn_negative_radius {n : ℕ} (P : Configuration n) (e : Fin n)
    (ht : planarDet (cyclicTangent P e) (cyclicTangent P (cyclicSuccessor e)) *
      planarDet (cyclicTangent P (cyclicVertexIndex e (n-2))) (cyclicTangent P e) < 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ Q : Configuration n, CoordClose η Q P →
      planarDet (cyclicTangent Q e) (cyclicTangent Q (cyclicSuccessor e)) *
        planarDet (cyclicTangent Q (cyclicVertexIndex e (n-2))) (cyclicTangent Q e) < 0 := by
  have hc := (continuous_denominator e (cyclicSuccessor e)).mul
    (continuous_denominator (cyclicVertexIndex e (n-2)) e)
  have hev : ∀ᶠ Q in 𝓝 P,
      planarDet (cyclicTangent Q e) (cyclicTangent Q (cyclicSuccessor e)) *
        planarDet (cyclicTangent Q (cyclicVertexIndex e (n-2))) (cyclicTangent Q e) < 0 :=
    hc.continuousAt.eventually (Iio_mem_nhds ht)
  exact exists_coordBox_subset P _ hev

/-- Fixed-endpoint regular secant density, transported back to the original
vertex labels. The chosen endpoints and its actual closing-edge geometry stay fixed. -/
theorem exists_near_regular_chosen_extension {n : ℕ} (hn : 3 ≤ n)
    (P : Configuration n) (e : Fin n)
    (hU : (P (cyclicSuccessor e)).2 = 0) (hV : (P e).2 = 0)
    (hleft : (P (cyclicSuccessor e)).1 < (P e).1) (η : ℝ) (hη : 0 < η) :
    ∃ Q : Configuration n, ∃ ε : ℝ,
      Q (cyclicSuccessor e) = P (cyclicSuccessor e) ∧ Q e = P e ∧ CoordClose η Q P ∧
      0 < ε ∧ ε < geometricRadius hn (Q ∘ cyclicVertexEquiv e) ∧
      Set.InjOn (criticalRoot (extendedArc hn (Q ∘ cyclicVertexEquiv e) ε))
        ↑(criticalPairs (extendedArc hn (Q ∘ cyclicVertexEquiv e) ε) n) := by
  let R := P ∘ cyclicVertexEquiv e
  have hR0 : (R (zeroIndex hn)).2 = 0 := by simpa only [R,opened_zero] using hU
  have hRn : (R (lastIndex hn)).2 = 0 := by simpa only [R,opened_last] using hV
  have hRleft : (R (zeroIndex hn)).1 < (R (lastIndex hn)).1 := by
    simpa only [R,opened_zero,opened_last] using hleft
  obtain ⟨O,ε,hO0,hOn,hnear,_,hε,hbound,hroots⟩ :=
    exists_near_with_extendedArc_injective hn R hR0 hRn hRleft η hη
  let Q := O ∘ (cyclicVertexEquiv e).symm
  have hQopen : Q ∘ cyclicVertexEquiv e = O := by
    funext i
    simp only [Q,Function.comp_apply,Equiv.symm_apply_apply]
  have hQ0 : Q (cyclicSuccessor e) = P (cyclicSuccessor e) := by
    have hx := congrFun hQopen (zeroIndex hn)
    simp only [opened_zero] at hx
    exact hx.trans (hO0.trans (by simp only [R,opened_zero]))
  have hQn : Q e = P e := by
    have hx := congrFun hQopen (lastIndex hn)
    simp only [opened_last] at hx
    exact hx.trans (hOn.trans (by simp only [R,opened_last]))
  have hQnear : CoordClose η Q P := by
    intro i
    have hi := hnear ((cyclicVertexEquiv e).symm i)
    simpa only [R,Function.comp_apply,Equiv.apply_symm_apply] using hi
  refine ⟨Q,ε,hQ0,hQn,hQnear,hε,?_,?_⟩
  · simpa only [hQopen] using hbound
  · simpa only [hQopen] using hroots

/-- The mixed-edge recursion on the original auxiliary domain, in horizontal
coordinates. Secant exclusions, epsilon, and critical-root injectivity are all
derived by approximation within the proved amplitude/smoothing neighborhoods. -/
theorem normalized_mixed_edge_recursion_auxiliary (hRI : GLSSWRootIndependence) {n : ℕ}
    (P : Configuration n) (hP : CyclicGeneric P) (e : Fin n)
    (hU : (P (cyclicSuccessor e)).2 = 0) (hV : (P e).2 = 0)
    (hleft : (P (cyclicSuccessor e)).1 < (P e).1)
    (hturn : planarDet (cyclicTangent P e) (cyclicTangent P (cyclicSuccessor e)) *
      planarDet (cyclicTangent P (cyclicVertexIndex e (n-2))) (cyclicTangent P e) < 0)
    (hAux : auxiliaryGenericity P hP) :
    polygonAmplitude P hP = chosenEdgeSmoothingSum P hP e hAux := by
  obtain ⟨η,hη,hS⟩ := exists_smoothingSums_neighborhood hRI P hP hAux
  obtain ⟨δ,hδ,hA⟩ := exists_configurationNeighborhood_cyclicGeneric_and_signs_amplitude P hP
  obtain ⟨γ,hγ,hT⟩ := exists_endpoint_turn_negative_radius P e hturn
  obtain ⟨Q,ε,hQ0,hQn,hnear,hε,hbound,hroots⟩ :=
    exists_near_regular_chosen_extension hP.size_ge_three P e hU hV hleft
      (min η (min δ γ)) (lt_min hη (lt_min hδ hγ))
  have hnearη : CoordClose η Q P := by
    intro i
    exact ⟨lt_of_lt_of_le (hnear i).1 (min_le_left _ _),lt_of_lt_of_le (hnear i).2 (min_le_left _ _)⟩
  have hnearδ : CoordClose δ Q P := by
    intro i
    exact ⟨lt_of_lt_of_le (hnear i).1 ((min_le_right _ _).trans (min_le_left _ _)),
      lt_of_lt_of_le (hnear i).2 ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hnearγ : CoordClose γ Q P := by
    intro i
    exact ⟨lt_of_lt_of_le (hnear i).1 ((min_le_right _ _).trans (min_le_right _ _)),
      lt_of_lt_of_le (hnear i).2 ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨hQ,hAuxQ,_,hsum⟩ := hS Q hnearη
  obtain ⟨hQ',_,hamp⟩ := hA Q hnearδ
  have hQU : (Q (cyclicSuccessor e)).2 = 0 := by rw [hQ0]; exact hU
  have hQV : (Q e).2 = 0 := by rw [hQn]; exact hV
  have hQleft : (Q (cyclicSuccessor e)).1 < (Q e).1 := by rw [hQ0,hQn]; exact hleft
  rw [← hamp,← hsum e]
  rw [chosenEdgeSmoothingSum_eq_horizontal Q hQ e (hQV.trans hQU.symm) hQleft]
  exact normalized_mixed_edge_recursion hRI Q hQ e hQU hQV hQleft (hT Q hnearγ)
    ε hε hbound hroots hAuxQ

/-- Source ep:mixed-edge-formula for every actual opposite-turn edge on the
original auxiliary domain, in arbitrary coordinates. No secant/extension premise remains. -/
theorem mixed_edge_recursion_auxiliary (hRI : GLSSWRootIndependence) {n : ℕ}
    (P : Configuration n) (hP : CyclicGeneric P) (e : Fin n)
    (hturn : planarDet (cyclicTangent P e) (cyclicTangent P (cyclicSuccessor e)) *
      planarDet (cyclicTangent P (cyclicVertexIndex e (n-2))) (cyclicTangent P e) < 0)
    (hAux : auxiliaryGenericity P hP) :
    polygonAmplitude P hP = chosenEdgeSmoothingSum P hP e hAux := by
  apply (normalizedPolygon_mixed_edge_iff P hP e hRI hAux).mpr
  obtain ⟨hV,hU,hleft⟩ := normalizedPolygon_leftward P hP e
  exact normalized_mixed_edge_recursion_auxiliary hRI (normalizedPolygon P e)
    (normalizedPolygon_generic P hP e) e hU hV hleft
    ((normalizedPolygon_endpoint_turn_product_neg_iff P hP e).mpr hturn)
    (normalization_auxiliaryGenericity (P (cyclicSuccessor e)) (P e)
      (chosen_endpoints_ne P hP e) P hP hAux)





end
end DirectGLSSW.MixedEdgeDensityRecursion
