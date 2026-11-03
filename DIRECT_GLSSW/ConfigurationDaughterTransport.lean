import ConfigurationSmoothingTransport

set_option autoImplicit false
namespace DirectGLSSW.ConfigurationDaughterTransport
open CrossingRationalParameters CrossingIncidenceNeighborhood LabelledCrossingContinuity
open ConfigurationEventOrder ConfigurationSmoothingTransport DaughterFirstReturn
noncomputable section

/-- Every fixed original event label has a continuous actual point on the stable
box: original vertices by evaluation, crossings by their proved rational formula. -/
theorem continuous_box_eventPoint {n : ℕ} (P : Configuration n) (η : ℝ)
    (hBox : StableBox P η) (x : PolygonEvent P) :
    Continuous (fun Q : Box P η =>
      polygonEventPoint Q.val (eventEquiv P Q.val (hBox Q.val Q.property).1 x)) := by
  cases x with
  | inl a => exact (continuous_apply a).comp continuous_subtype_val
  | inr v => exact continuous_box_crossingPoint P η hBox v.1

/-- Coordinates of the fixed original retained word, indexed by its original
finite length. Neither the index type nor the word changes with Q. -/
def mappedDaughterVertex {n : ℕ} (P : Configuration n) (hP : CyclicGeneric P)
    (η : ℝ) (hBox : StableBox P η) (S : Finset (PolygonCrossing P)) (root : PolygonEvent P)
    (Q : Box P η) (i : Fin (retainedLabelWord P hP S root).length) : PlanarPoint ℝ :=
  polygonEventPoint Q.val (eventEquiv P Q.val (hBox Q.val Q.property).1
    ((retainedLabelWord P hP S root)[i.val]))

theorem continuous_mappedDaughterVertex {n : ℕ} (P : Configuration n) (hP : CyclicGeneric P)
    (η : ℝ) (hBox : StableBox P η) (S : Finset (PolygonCrossing P)) (root : PolygonEvent P) :
    Continuous (mappedDaughterVertex P hP η hBox S root) := by
  apply continuous_pi
  intro i
  exact continuous_box_eventPoint P η hBox ((retainedLabelWord P hP S root)[i.val])

theorem ofFn_mappedDaughterVertex {n : ℕ} (P : Configuration n) (hP : CyclicGeneric P)
    (η : ℝ) (hBox : StableBox P η) (S : Finset (PolygonCrossing P)) (root : PolygonEvent P)
    (Q : Box P η) :
    List.ofFn (mappedDaughterVertex P hP η hBox S root Q) =
      (retainedLabelWord P hP S root).map
        (fun x => polygonEventPoint Q.val (eventEquiv P Q.val (hBox Q.val Q.property).1 x)) := by
  simpa only [mappedDaughterVertex] using
    (List.ofFn_getElem_eq_map (retainedLabelWord P hP S root)
      (fun x => polygonEventPoint Q.val (eventEquiv P Q.val (hBox Q.val Q.property).1 x)))

/-- Exact daughter coordinates for any configuration carrying the proved order
transport. This intermediate lemma has the order witness explicit. -/
theorem daughterPointList_eq_ofFn {n : ℕ} (P : Configuration n) (hP : CyclicGeneric P)
    (η : ℝ) (hBox : StableBox P η) (Q : Box P η) (hQ : CyclicGeneric Q.val)
    (horder : OrderCompatible P Q.val (hBox Q.val Q.property).1 hP.g2 hQ.g2)
    (S : Finset (PolygonCrossing P)) (root : PolygonEvent P) :
    daughterPointList Q.val hQ.g2 (mappedSupport P Q.val (hBox Q.val Q.property).1 S)
        (eventEquiv P Q.val (hBox Q.val Q.property).1 root) =
      List.ofFn (mappedDaughterVertex P hP η hBox S root Q) := by
  rw [ofFn_mappedDaughterVertex]
  exact daughterPointList_eq_mappedWord P Q.val (hBox Q.val Q.property).1 hP hQ horder S root

/-- Local smoothing/daughter transport on the full original G1–G2 domain.
All supports and roots are quantified after choosing one radius. Actual event
order, the daughter-word equality, and continuity are conclusions, not premises. -/
theorem exists_configuration_daughter_transport {n : ℕ} (P : Configuration n) (hP : CyclicGeneric P) :
    ∃ η : ℝ, 0 < η ∧ ∃ hBox : StableBox P η,
      (∀ S root, Continuous (mappedDaughterVertex P hP η hBox S root)) ∧
      ∀ Q : Box P η, ∃ hQ : CyclicGeneric Q.val,
        OrderCompatible P Q.val (hBox Q.val Q.property).1 hP.g2 hQ.g2 ∧
        (∀ S : Finset (PolygonCrossing P),
          PolygonNonalternation.polygonNonalternating P hP.g2 S ↔
          PolygonNonalternation.polygonNonalternating Q.val hQ.g2
            (mappedSupport P Q.val (hBox Q.val Q.property).1 S)) ∧
        (∀ (S : Finset (PolygonCrossing P)) (x : PolygonEvent P),
          eventEquiv P Q.val (hBox Q.val Q.property).1 (smoothingPairing P S x) =
          smoothingPairing Q.val (mappedSupport P Q.val (hBox Q.val Q.property).1 S)
            (eventEquiv P Q.val (hBox Q.val Q.property).1 x)) ∧
        (∀ (S : Finset (PolygonCrossing P)) (x : PolygonEvent P),
          eventEquiv P Q.val (hBox Q.val Q.property).1 (smoothingDartPermutation P hP.g2 S x) =
          smoothingDartPermutation Q.val hQ.g2 (mappedSupport P Q.val (hBox Q.val Q.property).1 S)
            (eventEquiv P Q.val (hBox Q.val Q.property).1 x)) ∧
        (∀ (S : Finset (PolygonCrossing P)) (x : PolygonEvent P),
          retainedCorner Q.val (mappedSupport P Q.val (hBox Q.val Q.property).1 S)
            (eventEquiv P Q.val (hBox Q.val Q.property).1 x) ↔ retainedCorner P S x) ∧
        ∀ (S : Finset (PolygonCrossing P)) (root : PolygonEvent P),
          daughterPointList Q.val hQ.g2 (mappedSupport P Q.val (hBox Q.val Q.property).1 S)
            (eventEquiv P Q.val (hBox Q.val Q.property).1 root) =
          List.ofFn (mappedDaughterVertex P hP η hBox S root Q) := by
  obtain ⟨η,hη,hBox,hall⟩ := exists_configuration_event_orderIso P hP
  refine ⟨η,hη,hBox,fun S root => continuous_mappedDaughterVertex P hP η hBox S root,?_⟩
  intro Q
  obtain ⟨hQ,horder⟩ := hall Q.val Q.property
  refine ⟨hQ,horder,?_,?_,?_,?_,?_⟩
  · exact nonalternating_iff P Q.val (hBox Q.val Q.property).1 hP hQ horder
  · exact eventEquiv_pairing P Q.val (hBox Q.val Q.property).1
  · exact eventEquiv_dart P Q.val (hBox Q.val Q.property).1 hP hQ horder
  · exact eventEquiv_retained P Q.val (hBox Q.val Q.property).1
  · exact daughterPointList_eq_ofFn P hP η hBox Q hQ horder







end
end DirectGLSSW.ConfigurationDaughterTransport
