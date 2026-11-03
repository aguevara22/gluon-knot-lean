import DirectGLSSW.TruncationDaughterAmplitude
import DirectGLSSW.TruncationFixedScaleCrossings
import DirectGLSSW.TruncationCommonRadius
import DirectGLSSW.TruncationComponentWeights
import ExposedCornerScale

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceTruncationSupport

open DaughterFirstReturn GeometricSmoothingWeights PermutationOrbits
open TruncationDirection TruncationEdgeLift PolygonNonalternation TruncationDaughterEvents
open DirectGLSSW.TruncationCommonRadius DirectGLSSW.ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable

/-- Fixed-scale form of the daughter-uniform truncation producer. The scale
is supplied so geometric support and finite daughter exclusions use the same
literal short edge. -/
theorem exists_leftCorner_truncation_all_affected_amplitudes_at_scale
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hturn : 0 < planarDet (q a-q p) (q (cyclicSuccessor a)-q a))
    (scale : ℝ) (hscale : 0 < scale)
    (havoid : ∀ e : PolygonEvent q, polygonEventPoint q e ≠ q a →
      planarDet (scale • (q (cyclicSuccessor a)-q a)-(q p-q a))
        (polygonEventPoint q e-q a) ≠ 0)
    (hAux : ∀ S : Finset (PolygonCrossing q), polygonNonalternating q hq.g2 S →
      CyclicGeneric (daughterVertex q hq.g2 S (Sum.inl a))) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ε < 1 ∧ ε*scale < 1 ∧
          ∃ ht : CyclicGeneric (truncateCyclicCorner q a p scale ε),
            polygonAmplitude (truncateCyclicCorner q a p scale ε) ht =
              -polygonAmplitude q hq ∧
            ∃ E : PolygonCrossing q ≃
              PolygonCrossing (truncateCyclicCorner q a p scale ε),
              (∀ c : PolygonCrossing q,
                (E c).val = (edgeLift a c.val.1,edgeLift a c.val.2)) ∧
              (∀ c : PolygonCrossing q,
                crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
                  crossingPoint q c) ∧
              (∀ S : Finset (PolygonCrossing q),
                polygonNonalternating q hq.g2 S ↔
                  polygonNonalternating (truncateCyclicCorner q a p scale ε)
                    ht.g2 (S.map E.toEmbedding)) ∧
              (∀ (S : Finset (PolygonCrossing q)) (hS : polygonNonalternating q hq.g2 S),
                ∃ hNew : CyclicGeneric (daughterVertex (truncateCyclicCorner q a p scale ε)
                  ht.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)),
                  polygonAmplitude (daughterVertex (truncateCyclicCorner q a p scale ε)
                    ht.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)) hNew =
                  -polygonAmplitude (daughterVertex q hq.g2 S (Sum.inl a))
                    (hAux S hS)) := by
  classical
  have havoidParent (x : Fin n) (hx : x ≠ a) :
      planarDet (scale • (q (cyclicSuccessor a)-q a)-(q p-q a)) (q x-q a) ≠ 0 := by
    apply havoid (Sum.inl x)
    exact fun h => hx (cyclicNoncollinear_injective hq.size_ge_three q hq.g1 h)
  obtain ⟨δP,hδP,hparent⟩ :=
    TruncationFixedScaleCrossings.exists_fixedScale_leftCorner_truncation_amplitude_crossings
      hRI q hq a p hp hturn scale hscale havoidParent
  let Supports := {S : Finset (PolygonCrossing q) // polygonNonalternating q hq.g2 S}
  have hlocal (s : Supports) :=
    TruncationDaughterAmplitude.exists_affected_daughter_truncation_amplitude
      hRI q hq a p hp hturn scale hscale havoid s.val (hAux s.val s.property)
  choose δD hδD hdaughter using hlocal
  obtain ⟨δ,hδ,hδparent,hδdaughter⟩ :=
    TruncationCommonRadius.exists_positive_common_lower_bound_with_parent δP hδP δD hδD
  refine ⟨δ,hδ,?_⟩
  intro ε hε hεδ
  obtain ⟨hε1,hεscale1,ht,hamp,E,hlabels,hpoint⟩ :=
    hparent ε hε (lt_of_lt_of_le hεδ hδparent)
  have hleft (c : PolygonCrossing q) : (E c).val.1 = edgeLift a c.val.1 :=
    congrArg Prod.fst (hlabels c)
  have hright (c : PolygonCrossing q) : (E c).val.2 = edgeLift a c.val.2 :=
    congrArg Prod.snd (hlabels c)
  refine ⟨hε1,hεscale1,ht,hamp,E,hlabels,hpoint,?_ ,?_⟩
  · exact TruncationSmoothingComponents.truncation_polygonNonalternating_iff
      hq.size_ge_three q a p hp scale ε hε hε1 (mul_pos hε hscale) hεscale1
      hq ht E hleft hright hpoint
  · intro S hS
    exact hdaughter ⟨S,hS⟩ ε hε
      (lt_of_lt_of_le hεδ (hδdaughter ⟨S,hS⟩)) ht E hleft hright hpoint

/-- The source exposed-corner truncation, with its one selected scale used for
both the full crossing/daughter transport and global support of the short edge. -/
theorem exists_exposed_corner_truncation_with_support_data
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq)
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hturn : 0 < planarDet (q a-q p) (q (cyclicSuccessor a)-q a))
    (v : PlanarPoint ℝ)
    (hexposed : ∀ i : Fin n, i ≠ a → 0 < planarDet v (q i-q a)) :
    ∃ scale : ℝ, 0 < scale ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ε < 1 ∧ ε*scale < 1 ∧
        ∃ ht : CyclicGeneric (truncateCyclicCorner q a p scale ε),
        ∃ hAuxt : auxiliaryGenericity (truncateCyclicCorner q a p scale ε) ht,
          polygonAmplitude (truncateCyclicCorner q a p scale ε) ht = -polygonAmplitude q hq ∧
          separatingSmoothingSum (truncateCyclicCorner q a p scale ε) ht hAuxt =
            -separatingSmoothingSum q hq hAux ∧
          (-1 : ℚ)^(n+1)*polygonAmplitude (truncateCyclicCorner q a p scale ε) ht =
            (-1 : ℚ)^n*polygonAmplitude q hq ∧
          (-1 : ℚ)^(n+1)*separatingSmoothingSum
              (truncateCyclicCorner q a p scale ε) ht hAuxt =
            (-1 : ℚ)^n*separatingSmoothingSum q hq hAux ∧
          LeftExposed (truncateCyclicCorner q a p scale ε) a.castSucc ∧
          ∃ E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε),
            (∀ c : PolygonCrossing q,
              (E c).val = (edgeLift a c.val.1,edgeLift a c.val.2)) ∧
            (∀ c : PolygonCrossing q,
              crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c) ∧
            (∀ S : Finset (PolygonCrossing q),
              polygonNonalternating q hq.g2 S ↔
                polygonNonalternating (truncateCyclicCorner q a p scale ε) ht.g2
                  (S.map E.toEmbedding)) ∧
            (∀ (S : Finset (PolygonCrossing q)) (hS : polygonNonalternating q hq.g2 S),
              ∃ hNew : CyclicGeneric (daughterVertex (truncateCyclicCorner q a p scale ε)
                ht.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)),
                polygonAmplitude (daughterVertex (truncateCyclicCorner q a p scale ε)
                  ht.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)) hNew =
                -polygonAmplitude (daughterVertex q hq.g2 S (Sum.inl a))
                  (hAux S hS (Sum.inl a))) := by
  classical
  obtain ⟨scale,hscale,hsupport,havoid⟩ :=
    exists_exposed_corner_generic_support_scale q hq a p hp hturn v hexposed
  obtain ⟨δL,hδL,hleft⟩ :=
    exists_small_truncation_leftExposed q a p scale (fun i hi => hsupport i hi)
  obtain ⟨δA,hδA,hgood⟩ :=
    exists_leftCorner_truncation_all_affected_amplitudes_at_scale
      hRI q hq a p hp hturn scale hscale havoid (fun S hS => hAux S hS (Sum.inl a))
  let δ := min δA δL
  have hδ : 0 < δ := lt_min hδA hδL
  have hδA' : δ ≤ δA := min_le_left δA δL
  have hδL' : δ ≤ δL := min_le_right δA δL
  refine ⟨scale,hscale,δ,hδ,?_⟩
  intro ε hε hεδ
  obtain ⟨hε1,hεscale1,ht,hamp,E,hlabels,hpoint,hsep,hAffected⟩ :=
    hgood ε hε (lt_of_lt_of_le hεδ hδA')
  have hleftEdge : LeftExposed (truncateCyclicCorner q a p scale ε) a.castSucc :=
    hleft ε hε (lt_of_lt_of_le hεδ hδL')
  have hleft (c : PolygonCrossing q) : (E c).val.1 = edgeLift a c.val.1 :=
    congrArg Prod.fst (hlabels c)
  have hright (c : PolygonCrossing q) : (E c).val.2 = edgeLift a c.val.2 :=
    congrArg Prod.snd (hlabels c)
  have hAuxt : auxiliaryGenericity (truncateCyclicCorner q a p scale ε) ht :=
    TruncationDaughterGenericity.auxiliaryGenericity_transport q hq a p hp scale ε
      hε hε1 (mul_pos hε hscale) hεscale1 ht E hleft hright hpoint hAux
      (fun S hS => (hAffected S hS).choose)
  have hsum : separatingSmoothingSum (truncateCyclicCorner q a p scale ε) ht hAuxt =
      -separatingSmoothingSum q hq hAux := by
    apply GeometricSmoothingSumTransport.separatingSmoothingSum_transport_neg
      q hq (truncateCyclicCorner q a p scale ε) ht E hsep hAux hAuxt
    intro S hS
    exact TruncationComponentWeights.componentAmplitudeProduct_truncation
      hRI q hq a p hp scale ε hε hε1 (mul_pos hε hscale) hεscale1 ht E hleft hright hpoint
      hAux hAuxt S hS ((hsep S).mp hS) (hAffected S hS)
  have hAmpParity : (-1 : ℚ)^(n+1)*polygonAmplitude
      (truncateCyclicCorner q a p scale ε) ht = (-1 : ℚ)^n*polygonAmplitude q hq := by
    rw [hamp,pow_succ]
    ring
  have hSumParity : (-1 : ℚ)^(n+1)*separatingSmoothingSum
      (truncateCyclicCorner q a p scale ε) ht hAuxt =
      (-1 : ℚ)^n*separatingSmoothingSum q hq hAux := by
    rw [hsum,pow_succ]
    ring
  exact ⟨hε1,hεscale1,ht,hAuxt,hamp,hsum,hAmpParity,hSumParity,hleftEdge,
    E,hlabels,hpoint,hsep,hAffected⟩




end DirectGLSSW.SourceTruncationSupport
