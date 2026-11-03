import DirectGLSSW.TruncationDaughterAmplitude
import DirectGLSSW.TruncationCommonDaughterScale
import DirectGLSSW.TruncationFixedScaleCrossings
import DirectGLSSW.TruncationCommonRadius

set_option autoImplicit false

namespace DirectGLSSW.TruncationDaughterUniform

open DaughterFirstReturn TruncationDirection TruncationEdgeLift PolygonNonalternation

theorem exists_leftCorner_truncation_all_affected_amplitudes
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hturn : 0 < planarDet (q a - q p) (q (cyclicSuccessor a) - q a))
    (hAux : ∀ S : Finset (PolygonCrossing q), polygonNonalternating q hq.g2 S →
      CyclicGeneric (daughterVertex q hq.g2 S (Sum.inl a))) :
    ∃ scale : ℝ, 0 < scale ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ε < 1 ∧ ε * scale < 1 ∧
          ∃ ht : CyclicGeneric (truncateCyclicCorner q a p scale ε),
            polygonAmplitude (truncateCyclicCorner q a p scale ε) ht =
              -polygonAmplitude q hq ∧
            ∃ E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε),
              (∀ c : PolygonCrossing q,
                (E c).val = (edgeLift a c.val.1, edgeLift a c.val.2)) ∧
              (∀ c : PolygonCrossing q,
                crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c) ∧
              (∀ S : Finset (PolygonCrossing q),
                polygonNonalternating q hq.g2 S ↔
                  polygonNonalternating (truncateCyclicCorner q a p scale ε) ht.g2 (S.map E.toEmbedding)) ∧
              (∀ (S : Finset (PolygonCrossing q)) (hS : polygonNonalternating q hq.g2 S),
                ∃ hNew : CyclicGeneric (daughterVertex (truncateCyclicCorner q a p scale ε)
                  ht.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)),
                  polygonAmplitude (daughterVertex (truncateCyclicCorner q a p scale ε)
                    ht.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)) hNew =
                  -polygonAmplitude (daughterVertex q hq.g2 S (Sum.inl a)) (hAux S hS))
 := by
  classical
  obtain ⟨scale, hscale, havoid, _⟩ :=
    TruncationCommonDaughterScale.exists_positive_turn_scale_avoiding_all_daughter_vertex_lines q a p hturn
  have havoidParent (x : Fin n) (hx : x ≠ a) :
      planarDet (scale • (q (cyclicSuccessor a) - q a) - (q p - q a)) (q x - q a) ≠ 0 := by
    apply havoid (Sum.inl x)
    exact fun h => hx (cyclicNoncollinear_injective hq.size_ge_three q hq.g1 h)
  obtain ⟨δP, hδP, hparent⟩ :=
    TruncationFixedScaleCrossings.exists_fixedScale_leftCorner_truncation_amplitude_crossings
      hRI q hq a p hp hturn scale hscale havoidParent
  let Supports := {S : Finset (PolygonCrossing q) // polygonNonalternating q hq.g2 S}
  have hlocal (s : Supports) :=
    TruncationDaughterAmplitude.exists_affected_daughter_truncation_amplitude
      hRI q hq a p hp hturn scale hscale havoid s.val (hAux s.val s.property)
  choose δD hδD hdaughter using hlocal
  obtain ⟨δ, hδ, hδparent, hδdaughter⟩ :=
    TruncationCommonRadius.exists_positive_common_lower_bound_with_parent δP hδP δD hδD
  refine ⟨scale, hscale, δ, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨hε1, hεscale1, ht, hamp, E, hlabels, hpoint⟩ :=
    hparent ε hε (lt_of_lt_of_le hεδ hδparent)
  have hleft (c : PolygonCrossing q) : (E c).val.1 = edgeLift a c.val.1 :=
    congrArg Prod.fst (hlabels c)
  have hright (c : PolygonCrossing q) : (E c).val.2 = edgeLift a c.val.2 :=
    congrArg Prod.snd (hlabels c)
  refine ⟨hε1, hεscale1, ht, hamp, E, hlabels, hpoint, ?_, ?_⟩
  · exact TruncationSmoothingComponents.truncation_polygonNonalternating_iff
      hq.size_ge_three q a p hp scale ε hε hε1 (mul_pos hε hscale) hεscale1
      hq ht E hleft hright hpoint
  · intro S hS
    exact hdaughter ⟨S, hS⟩ ε hε
      (lt_of_lt_of_le hεδ (hδdaughter ⟨S, hS⟩)) ht E hleft hright hpoint

end DirectGLSSW.TruncationDaughterUniform
