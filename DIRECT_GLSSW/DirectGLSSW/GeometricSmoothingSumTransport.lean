import DirectGLSSW.GeometricSmoothingWeights
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace DirectGLSSW.GeometricSmoothingSumTransport
open scoped BigOperators
open DirectGLSSW.GeometricSmoothingWeights

noncomputable instance separatingSupportFintype {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    Fintype (SeparatingSupport q hq) := by
  classical
  unfold SeparatingSupport
  infer_instance

noncomputable def separatingSupportEquiv {n m : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (r : Fin m → PlanarPoint ℝ) (hr : CyclicGeneric r)
    (E : PolygonCrossing q ≃ PolygonCrossing r)
    (hSupport : ∀ S : Finset (PolygonCrossing q),
      PolygonNonalternation.polygonNonalternating q hq.g2 S ↔
        PolygonNonalternation.polygonNonalternating r hr.g2
          (S.map E.toEmbedding)) :
    SeparatingSupport q hq ≃ SeparatingSupport r hr :=
  E.finsetCongr.subtypeEquiv hSupport

theorem separatingSupportEquiv_apply {n m : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (r : Fin m → PlanarPoint ℝ) (hr : CyclicGeneric r)
    (E : PolygonCrossing q ≃ PolygonCrossing r)
    (hSupport : ∀ S : Finset (PolygonCrossing q),
      PolygonNonalternation.polygonNonalternating q hq.g2 S ↔
        PolygonNonalternation.polygonNonalternating r hr.g2
          (S.map E.toEmbedding))
    (S : SeparatingSupport q hq) :
    (separatingSupportEquiv q hq r hr E hSupport S).val =
      S.val.map E.toEmbedding := rfl

theorem separatingSupportEquiv_card {n m : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (r : Fin m → PlanarPoint ℝ) (hr : CyclicGeneric r)
    (E : PolygonCrossing q ≃ PolygonCrossing r)
    (hSupport : ∀ S : Finset (PolygonCrossing q),
      PolygonNonalternation.polygonNonalternating q hq.g2 S ↔
        PolygonNonalternation.polygonNonalternating r hr.g2
          (S.map E.toEmbedding)) :
    Fintype.card (SeparatingSupport q hq) = Fintype.card (SeparatingSupport r hr) :=
  Fintype.card_congr (separatingSupportEquiv q hq r hr E hSupport)

set_option maxHeartbeats 800000 in
theorem separatingSmoothingSum_transport_neg {n m : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (r : Fin m → PlanarPoint ℝ) (hr : CyclicGeneric r)
    (E : PolygonCrossing q ≃ PolygonCrossing r)
    (hSupport : ∀ S : Finset (PolygonCrossing q),
      PolygonNonalternation.polygonNonalternating q hq.g2 S ↔
        PolygonNonalternation.polygonNonalternating r hr.g2
          (S.map E.toEmbedding))
    (hAuxQ : auxiliaryGenericity q hq)
    (hAuxR : auxiliaryGenericity r hr)
    (hProducts : ∀ S : Finset (PolygonCrossing q),
      ∀ hS : PolygonNonalternation.polygonNonalternating q hq.g2 S,
        componentAmplitudeProduct r hr (S.map E.toEmbedding) hAuxR
            ((hSupport S).mp hS) =
          -componentAmplitudeProduct q hq S hAuxQ hS) :
    separatingSmoothingSum r hr hAuxR =
      -separatingSmoothingSum q hq hAuxQ := by
  let e := separatingSupportEquiv q hq r hr E hSupport
  calc
    separatingSmoothingSum r hr hAuxR =
        ∑ S : SeparatingSupport q hq,
          (-1 : ℚ) ^ (e S).val.card *
            componentAmplitudeProduct r hr (e S).val hAuxR (e S).property := by
      unfold separatingSmoothingSum
      exact (Fintype.sum_equiv e
        (fun S => (-1 : ℚ) ^ (e S).val.card *
          componentAmplitudeProduct r hr (e S).val hAuxR (e S).property)
        (fun T => (-1 : ℚ) ^ T.val.card *
          componentAmplitudeProduct r hr T.val hAuxR T.property)
        (by intro S; rfl)).symm
    _ = -(∑ S : SeparatingSupport q hq,
        (-1 : ℚ) ^ S.val.card *
          componentAmplitudeProduct q hq S.val hAuxQ S.property) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro S _
      have hmap : (e S).val = S.val.map E.toEmbedding := rfl
      have hcard : (e S).val.card = S.val.card := by
        rw [hmap, Finset.card_map]
      have himage : e S = ⟨S.val.map E.toEmbedding,
          (hSupport S.val).mp S.property⟩ := Subtype.ext hmap
      rw [himage, Finset.card_map, hProducts S.val S.property]
      ring
    _ = -separatingSmoothingSum q hq hAuxQ := rfl

end DirectGLSSW.GeometricSmoothingSumTransport
