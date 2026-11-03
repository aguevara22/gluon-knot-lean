import DaughterCoordinateStability

set_option autoImplicit false
namespace DirectGLSSW.ConfigurationDaughterStability
open CrossingRationalParameters CrossingIncidenceNeighborhood LabelledCrossingContinuity
open ConfigurationEventOrder ConfigurationSmoothingTransport ConfigurationDaughterTransport
open DaughterCoordinateStability DaughterFirstReturn GeometricSmoothingWeights TruncationPointListAdapter
open Filter Topology
noncomputable section

/-- Concrete conclusions for one fixed original retained label word: its nearby
actual coordinates are generic, preserve every triple sign, and keep its rooted
amplitude. This package is proved below, never assumed by the final theorem. -/
def WordStable {n : ℕ} (P : Configuration n) (hP : CyclicGeneric P)
    (hAux : auxiliaryGenericity P hP) (η : ℝ) (hBox : StableBox P η)
    (Q : Box P η) (S : Finset (PolygonCrossing P))
    (hS : PolygonNonalternation.polygonNonalternating P hP.g2 S) (root : PolygonEvent P) : Prop :=
  ∃ hR : CyclicGeneric (mappedDaughterVertex P hP η hBox S root Q),
    (∀ i k j, i ≠ k → k ≠ j → i ≠ j →
      scalarSignValue (planarDet
        (mappedDaughterVertex P hP η hBox S root Q k-mappedDaughterVertex P hP η hBox S root Q j)
        (mappedDaughterVertex P hP η hBox S root Q i-mappedDaughterVertex P hP η hBox S root Q j)) =
      scalarSignValue (planarDet
        (baseWordVertex P hP S root k-baseWordVertex P hP S root j)
        (baseWordVertex P hP S root i-baseWordVertex P hP S root j))) ∧
    polygonAmplitude (mappedDaughterVertex P hP η hBox S root Q) hR =
      polygonAmplitude (daughterVertex P hP.g2 S root) (hAux S hS root)

/-- Pull the finite simultaneous daughter neighborhood back from the original
stable box and choose one smaller ambient coordinate radius. -/
theorem exists_wordStableBox {n : ℕ} (P : Configuration n) (hP : CyclicGeneric P)
    (hAux : auxiliaryGenericity P hP) :
    ∃ η : ℝ, 0 < η ∧ ∃ hBox : StableBox P η,
      ∀ Q : Box P η, ∃ hQ : CyclicGeneric Q.val,
        OrderCompatible P Q.val (hBox Q.val Q.property).1 hP.g2 hQ.g2 ∧
        ∀ (S : Finset (PolygonCrossing P)) (root : PolygonEvent P)
          (hS : PolygonNonalternation.polygonNonalternating P hP.g2 S),
          WordStable P hP hAux η hBox Q S hS root := by
  obtain ⟨ηB,hηB,hB,horderB⟩ := exists_configuration_event_orderIso P hP
  have hev := eventually_all_daughters_stable P hP hAux ηB hηB hB
  rw [nhds_subtype_eq_comap] at hev
  obtain ⟨U,hU,hsub⟩ := Filter.mem_comap.mp hev
  obtain ⟨δ,hδ,hδU⟩ := exists_coordBox_subset P U hU
  let η := min ηB δ
  have hη : 0 < η := lt_min hηB hδ
  have hsmallB : ∀ Q, CoordClose η Q P → CoordClose ηB Q P := by
    intro Q hQ i
    exact ⟨lt_of_lt_of_le (hQ i).1 (min_le_left _ _),lt_of_lt_of_le (hQ i).2 (min_le_left _ _)⟩
  have hsmallδ : ∀ Q, CoordClose η Q P → CoordClose δ Q P := by
    intro Q hQ i
    exact ⟨lt_of_lt_of_le (hQ i).1 (min_le_right _ _),lt_of_lt_of_le (hQ i).2 (min_le_right _ _)⟩
  have hBox : StableBox P η := fun Q hQ => hB Q (hsmallB Q hQ)
  refine ⟨η,hη,hBox,?_⟩
  intro Q
  let QB : Box P ηB := ⟨Q.val,hsmallB Q.val Q.property⟩
  obtain ⟨hQ,horder⟩ := horderB Q.val QB.property
  refine ⟨hQ,horder,?_⟩
  intro S root hS
  have hgood := hsub (show QB ∈ Subtype.val ⁻¹' U from hδU Q.val (hsmallδ Q.val Q.property))
  exact hgood S root hS

/-- The actual nearby auxiliaryGenericity quantifier follows by surjectivity of
both real crossing-support labels and real event-root labels. -/
theorem auxiliaryGenericity_of_wordStable {n : ℕ} (P : Configuration n) (hP : CyclicGeneric P)
    (hAux : auxiliaryGenericity P hP) (η : ℝ) (hBox : StableBox P η)
    (Q : Box P η) (hQ : CyclicGeneric Q.val)
    (horder : OrderCompatible P Q.val (hBox Q.val Q.property).1 hP.g2 hQ.g2)
    (hstable : ∀ (S : Finset (PolygonCrossing P)) (root : PolygonEvent P)
      (hS : PolygonNonalternation.polygonNonalternating P hP.g2 S),
      WordStable P hP hAux η hBox Q S hS root) : auxiliaryGenericity Q.val hQ := by
  intro T hT r
  obtain ⟨S,hSmap⟩ := (labelEquiv P Q.val (hBox Q.val Q.property).1).finsetCongr.surjective T
  change mappedSupport P Q.val (hBox Q.val Q.property).1 S = T at hSmap
  obtain ⟨root,hr⟩ := (eventEquiv P Q.val (hBox Q.val Q.property).1).surjective r
  subst T
  subst r
  have hS := (nonalternating_iff P Q.val (hBox Q.val Q.property).1 hP hQ horder S).mpr hT
  obtain ⟨hR,_,_⟩ := hstable S root hS
  exact cyclicGeneric_of_pointList_eq _ _ hR
    (daughterPointList_eq_ofFn P hP η hBox Q hQ horder S root).symm

/-- Root-preserving daughter amplitude equality needs no root-independence
assumption; both amplitudes use the exact transported starting root. -/
theorem actual_daughter_amplitude_eq {n : ℕ} (P : Configuration n) (hP : CyclicGeneric P)
    (hAux : auxiliaryGenericity P hP) (η : ℝ) (hBox : StableBox P η)
    (Q : Box P η) (hQ : CyclicGeneric Q.val)
    (horder : OrderCompatible P Q.val (hBox Q.val Q.property).1 hP.g2 hQ.g2)
    (hAuxQ : auxiliaryGenericity Q.val hQ)
    (S : Finset (PolygonCrossing P)) (hS : PolygonNonalternation.polygonNonalternating P hP.g2 S)
    (root : PolygonEvent P) (hstable : WordStable P hP hAux η hBox Q S hS root) :
    polygonAmplitude
      (daughterVertex Q.val hQ.g2 (mappedSupport P Q.val (hBox Q.val Q.property).1 S)
        (eventEquiv P Q.val (hBox Q.val Q.property).1 root))
      (hAuxQ _ ((nonalternating_iff P Q.val (hBox Q.val Q.property).1 hP hQ horder S).mp hS) _) =
    polygonAmplitude (daughterVertex P hP.g2 S root) (hAux S hS root) := by
  obtain ⟨hR,_,ha⟩ := hstable
  exact (polygonAmplitude_eq_of_pointList_eq _ _ _ hR
    (daughterPointList_eq_ofFn P hP η hBox Q hQ horder S root)).trans ha

/-- One neighborhood simultaneously preserves actual auxiliary genericity, all
rooted daughter amplitudes, and all fixed-word triple signs. Original hAux stays
explicit; this theorem does not remove it or transfer the full recurrence. -/
theorem exists_configuration_daughter_stability {n : ℕ} (P : Configuration n) (hP : CyclicGeneric P)
    (hAux : auxiliaryGenericity P hP) :
    ∃ η : ℝ, 0 < η ∧ ∃ hBox : StableBox P η,
      ∀ Q : Box P η, ∃ hQ : CyclicGeneric Q.val,
        ∃ horder : OrderCompatible P Q.val (hBox Q.val Q.property).1 hP.g2 hQ.g2,
        ∃ hAuxQ : auxiliaryGenericity Q.val hQ,
          ∀ (S : Finset (PolygonCrossing P))
            (hS : PolygonNonalternation.polygonNonalternating P hP.g2 S) (root : PolygonEvent P),
            WordStable P hP hAux η hBox Q S hS root ∧
            polygonAmplitude
              (daughterVertex Q.val hQ.g2 (mappedSupport P Q.val (hBox Q.val Q.property).1 S)
                (eventEquiv P Q.val (hBox Q.val Q.property).1 root))
              (hAuxQ _ ((nonalternating_iff P Q.val (hBox Q.val Q.property).1 hP hQ horder S).mp hS) _) =
            polygonAmplitude (daughterVertex P hP.g2 S root) (hAux S hS root) := by
  obtain ⟨η,hη,hBox,hall⟩ := exists_wordStableBox P hP hAux
  refine ⟨η,hη,hBox,?_⟩
  intro Q
  obtain ⟨hQ,horder,hstable⟩ := hall Q
  have hAuxQ := auxiliaryGenericity_of_wordStable P hP hAux η hBox Q hQ horder hstable
  refine ⟨hQ,horder,hAuxQ,?_⟩
  intro S hS root
  exact ⟨hstable S root hS,actual_daughter_amplitude_eq P hP hAux η hBox Q hQ horder
    hAuxQ S hS root (hstable S root hS)⟩






end
end DirectGLSSW.ConfigurationDaughterStability
