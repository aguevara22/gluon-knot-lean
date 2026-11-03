import ActualCarrierTransport

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActualCarrierTransport
open DaughterFirstReturn AuxiliaryCarrierChart LocalDaughterTransport LocalCrossingTransport
open CarrierFamilyDensity CarrierWitnessEvaluation

 theorem cast_cyclic_predecessor {a b : ℕ} (h : a = b) (i : Fin a) :
    (cyclicSuccessorPerm b)⁻¹ (Fin.cast h i) =
      Fin.cast h ((cyclicSuccessorPerm a)⁻¹ i) := by
  subst b
  rfl

variable {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
  (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
  (E : PolygonCrossing q ≃ PolygonCrossing q')
  (hlabels : ∀ c, (E c).val = c.val)
  (S : Finset (PolygonCrossing q))
  (hdart : ∀ x, polygonEventMapEquiv E (smoothingDartPermutation q hq.g2 S x) =
    smoothingDartPermutation q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E x))
  (L : Fin n → CarrierLine)
  (hinc : ∀ e, lineValue (L e) (q' e) = 0 ∧
      lineValue (L e) (q' (cyclicSuccessor e)) = 0)
  (root : PolygonEvent q) (hroot : retainedCorner q S root)
  (hden : ∀ i : Fin (Fintype.card (CornerCoord q hq.g2 S root)),
    lineDenominator
      (L (daughterCarrier q hq.g2 S root ((cyclicSuccessorPerm _)⁻¹ i)))
      (L (daughterCarrier q hq.g2 S root i)) ≠ 0)

include hlabels hinc hroot hden in
 theorem mapped_daughter_intersection
    (i : Fin (Fintype.card (CornerCoord q hq.g2 S root))) :
    daughterVertex q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root)
      (Fin.cast (daughterCard_eq q q' hq.g2 hq'.g2 E S hdart root) i) =
    lineIntersection
      (L (daughterCarrier q hq.g2 S root ((cyclicSuccessorPerm _)⁻¹ i)))
      (L (daughterCarrier q hq.g2 S root i)) := by
  have hc := daughterCarrier_cast_eq q q' hq hq' E hlabels S hdart root
  have hr := (polygonEventMapEquiv_retained q q' E S root).mpr hroot
  have hp := cast_cyclic_predecessor
    (daughterCard_eq q q' hq.g2 hq'.g2 E S hdart root) i
  have hd : lineDenominator
      (L (daughterCarrier q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root)
        ((cyclicSuccessorPerm _)⁻¹
          (Fin.cast (daughterCard_eq q q' hq.g2 hq'.g2 E S hdart root) i))))
      (L (daughterCarrier q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root)
          (Fin.cast (daughterCard_eq q q' hq.g2 hq'.g2 E S hdart root) i))) ≠ 0 := by
    rw [hp, hc, hc]
    exact hden i
  have ht := daughter_intersection_of_incidence q q' hq' E S L hinc
    (polygonEventMapEquiv E root) hr
    (Fin.cast (daughterCard_eq q q' hq.g2 hq'.g2 E S hdart root) i) hd
  rw [hp, hc, hc] at ht
  exact ht

include hlabels hinc hroot hden hdart in
 theorem mapped_daughter_noncollinear
    (hnum : allDaughterFamilyNumeratorsNonzero q hq.g2 S L) :
    cyclicNoncollinear
      (daughterVertex q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root)) := by
  let hcard := daughterCard_eq q q' hq.g2 hq'.g2 E S hdart root
  intro a b c hab hbc hac
  obtain ⟨a, rfl⟩ := (finCongr hcard).surjective a
  obtain ⟨b, rfl⟩ := (finCongr hcard).surjective b
  obtain ⟨c, rfl⟩ := (finCongr hcard).surjective c
  have hab' : a ≠ b := fun h => hab (congrArg (finCongr hcard) h)
  have hbc' : b ≠ c := fun h => hbc (congrArg (finCongr hcard) h)
  have hac' : a ≠ c := fun h => hac (congrArg (finCongr hcard) h)
  have ha := mapped_daughter_intersection q q' hq hq' E hlabels S hdart L hinc root hroot hden a
  have hb := mapped_daughter_intersection q q' hq hq' E hlabels S hdart L hinc root hroot hden b
  have hc := mapped_daughter_intersection q q' hq hq' E hlabels S hdart L hinc root hroot hden c
  change planarDet
    (daughterVertex q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root) (Fin.cast hcard b) -
      daughterVertex q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root) (Fin.cast hcard c))
    (daughterVertex q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root) (Fin.cast hcard a) -
      daughterVertex q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root) (Fin.cast hcard c)) ≠ 0
  rw [ha, hb, hc]
  intro hz
  apply hnum root hroot c b a hbc'.symm hab'.symm hac'.symm
  exact (carrierTripleNumerator_zero_iff _ _ _ _ _ _ (hden c) (hden b) (hden a)).mpr hz



end DirectGLSSW.ActualCarrierTransport
