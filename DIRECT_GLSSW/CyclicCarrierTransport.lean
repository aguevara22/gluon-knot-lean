import CyclicCarrierFamily

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart DaughterFirstReturn LocalDaughterTransport ActualCarrierTransport LocalCrossingTransport

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
    lineDenominator (L (daughterCarrier q hq.g2 S root ((cyclicSuccessorPerm _)⁻¹ i)))
      (L (daughterCarrier q hq.g2 S root i)) ≠ 0)

include hlabels hinc hroot hden hdart in
theorem mapped_daughter_outer
    (hnum : cycleSecantExclusions (daughterCarrier q hq.g2 S root) L)
    (l : Fin 4 → Fin (Fintype.card
      (CornerCoord q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root))))
    (hl : Function.Injective l) :
    OriginalOuterProperness.outerNumerator
      (daughterVertex q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root) ∘ l) ≠ 0 := by
  let hcard := daughterCard_eq q q' hq.g2 hq'.g2 E S hdart root
  let l' := (finCongr hcard).symm ∘ l
  have hl' : Function.Injective l' := (finCongr hcard).symm.injective.comp hl
  have hc := (cycleSecantExclusions_iff _ L hden).mp hnum
  have he : daughterVertex q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root) ∘ l =
      reconstructPolygon (L ∘ daughterCarrier q hq.g2 S root) ∘ l' := by
    funext i
    have hi := mapped_daughter_intersection q q' hq hq' E hlabels S hdart L hinc root hroot hden (l' i)
    change daughterVertex q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root)
      ((finCongr hcard) (l' i)) = _ at hi
    simpa only [l', Function.comp_def, Equiv.apply_symm_apply, reconstructPolygon] using hi
  rw [he]
  exact hc.1 l' hl'

include hlabels hinc hroot hden hdart in
theorem mapped_daughter_secant
    (hnum : cycleSecantExclusions (daughterCarrier q hq.g2 S root) L)
    (l : Fin 6 → Fin (Fintype.card
      (CornerCoord q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root))))
    (hl : Function.Injective l) :
    OriginalSecantProperness.secantNumerator
      (daughterVertex q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root) ∘ l) ≠ 0 := by
  let hcard := daughterCard_eq q q' hq.g2 hq'.g2 E S hdart root
  let l' := (finCongr hcard).symm ∘ l
  have hl' : Function.Injective l' := (finCongr hcard).symm.injective.comp hl
  have hc := (cycleSecantExclusions_iff _ L hden).mp hnum
  have he : daughterVertex q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root) ∘ l =
      reconstructPolygon (L ∘ daughterCarrier q hq.g2 S root) ∘ l' := by
    funext i
    have hi := mapped_daughter_intersection q q' hq hq' E hlabels S hdart L hinc root hroot hden (l' i)
    change daughterVertex q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root)
      ((finCongr hcard) (l' i)) = _ at hi
    simpa only [l', Function.comp_def, Equiv.apply_symm_apply, reconstructPolygon] using hi
  rw [he]
  exact hc.2 l' hl'

end DirectGLSSW.CyclicCarrierClearing



