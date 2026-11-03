import LabelledCrossingContinuity
import DirectGLSSW.ConfigurationNeighborhood

set_option autoImplicit false
namespace DirectGLSSW.ConfigurationCrossingStability
open CrossingRationalParameters CrossingIncidenceNeighborhood LabelledCrossingContinuity
noncomputable section

/-- A uniform neighborhood of the original G1–G2 polygon preserves every actual
edge-pair incidence and keeps every original crossing denominator nonzero. -/
theorem exists_stableBox {n : ℕ} (P : Configuration n) (hP : CyclicGeneric P) :
    ∃ η : ℝ, 0 < η ∧ StableBox P η ∧
      ∀ Q, CoordClose η Q P → CyclicGeneric Q := by
  obtain ⟨ηI,hηI,hI⟩ := exists_incidence_box_of_g1 P hP
  obtain ⟨ηG,hηG,hG⟩ := exists_configurationNeighborhood_cyclicGeneric_and_signs_amplitude P hP
  let η := min ηI ηG
  have hη : 0 < η := lt_min hηI hηG
  have hsmallI : ∀ Q, CoordClose η Q P → CoordClose ηI Q P := by
    intro Q hQ i
    exact ⟨lt_of_lt_of_le (hQ i).1 (min_le_left _ _),
      lt_of_lt_of_le (hQ i).2 (min_le_left _ _)⟩
  have hsmallG : ∀ Q, CoordClose η Q P → CoordClose ηG Q P := by
    intro Q hQ i
    exact ⟨lt_of_lt_of_le (hQ i).1 (min_le_right _ _),
      lt_of_lt_of_le (hQ i).2 (min_le_right _ _)⟩
  have hgeneric : ∀ Q, CoordClose η Q P → CyclicGeneric Q := by
    intro Q hQ
    obtain ⟨hQg,_,_⟩ := hG Q (hsmallG Q hQ)
    exact hQg
  refine ⟨η,hη,?_,hgeneric⟩
  intro Q hQ
  have hIQ := hI Q (hsmallI Q hQ)
  exact ⟨hIQ.1 (hgeneric Q hQ).g1,hIQ.2⟩

/-- Unpackaged incidence statement on every labelled edge pair. -/
theorem exists_configuration_edgeIntersection_iff {n : ℕ}
    (P : Configuration n) (hP : CyclicGeneric P) :
    ∃ η : ℝ, 0 < η ∧ ∀ Q, CoordClose η Q P →
      ∀ e f : Fin n, edgeIntersection Q e f ↔ edgeIntersection P e f := by
  obtain ⟨η,hη,hBox,_⟩ := exists_stableBox P hP
  exact ⟨η,hη,fun Q hQ => (hBox Q hQ).1⟩

/-- The exact actual crossing parameters and points, labelled by original edge pairs,
are continuous on one uniform coordinate box; no order or daughter hypothesis occurs. -/
theorem exists_configuration_crossing_stability {n : ℕ}
    (P : Configuration n) (hP : CyclicGeneric P) :
    ∃ η : ℝ, 0 < η ∧ ∃ hBox : StableBox P η,
      (∀ Q, CoordClose η Q P → CyclicGeneric Q) ∧
      ∀ c : PolygonCrossing P,
        Continuous (fun Q : Box P η => crossingParameterLeft Q.val (boxCrossing P η hBox Q c)) ∧
        Continuous (fun Q : Box P η => crossingParameterRight Q.val (boxCrossing P η hBox Q c)) ∧
        Continuous (fun Q : Box P η => crossingPoint Q.val (boxCrossing P η hBox Q c)) := by
  obtain ⟨η,hη,hBox,hgeneric⟩ := exists_stableBox P hP
  exact ⟨η,hη,hBox,hgeneric,fun c => ⟨continuous_box_leftParameter P η hBox c,
    continuous_box_rightParameter P η hBox c,continuous_box_crossingPoint P η hBox c⟩⟩




end
end DirectGLSSW.ConfigurationCrossingStability
