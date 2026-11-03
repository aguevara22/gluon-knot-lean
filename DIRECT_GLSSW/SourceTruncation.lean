import DirectGLSSW.TruncationSeparatingSum
import DirectGLSSW.TruncationComponentWeights

set_option autoImplicit false

namespace DirectGLSSW.SourceTruncation

open DaughterFirstReturn GeometricSmoothingWeights PermutationOrbits
open TruncationDirection TruncationEdgeLift PolygonNonalternation TruncationDaughterEvents
attribute [local instance] Classical.propDecidable

/-- Actual short-corner replacement, retaining its crossing and smoothing-support
correspondence alongside the amplitude and alternating-sum signs. -/
theorem exists_exposed_corner_truncation_data
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq)
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hturn : 0 < planarDet (q a - q p) (q (cyclicSuccessor a) - q a)) :
    ∃ scale : ℝ, 0 < scale ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ε < 1 ∧ ε * scale < 1 ∧
        ∃ ht : CyclicGeneric (truncateCyclicCorner q a p scale ε),
        ∃ hAuxt : auxiliaryGenericity (truncateCyclicCorner q a p scale ε) ht,
          polygonAmplitude (truncateCyclicCorner q a p scale ε) ht = -polygonAmplitude q hq ∧
          separatingSmoothingSum (truncateCyclicCorner q a p scale ε) ht hAuxt =
            -separatingSmoothingSum q hq hAux ∧
          (-1 : ℚ) ^ (n + 1) * polygonAmplitude (truncateCyclicCorner q a p scale ε) ht =
            (-1 : ℚ) ^ n * polygonAmplitude q hq ∧
          (-1 : ℚ) ^ (n + 1) * separatingSmoothingSum (truncateCyclicCorner q a p scale ε) ht hAuxt =
            (-1 : ℚ) ^ n * separatingSmoothingSum q hq hAux ∧
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
                  -polygonAmplitude (daughterVertex q hq.g2 S (Sum.inl a)) (hAux S hS (Sum.inl a))) := by
  classical
  obtain ⟨scale, hscale, δ, hδ, hgood⟩ :=
    TruncationDaughterUniform.exists_leftCorner_truncation_all_affected_amplitudes
      hRI q hq a p hp hturn (fun S hS => hAux S hS (Sum.inl a))
  refine ⟨scale, hscale, δ, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨hε1, hεscale1, ht, hamp, E, hlabels, hpoint, hsep, hAffected⟩ := hgood ε hε hεδ
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
  have hAmpParity : (-1 : ℚ) ^ (n + 1) * polygonAmplitude (truncateCyclicCorner q a p scale ε) ht =
      (-1 : ℚ) ^ n * polygonAmplitude q hq := by
    rw [hamp, pow_succ]
    ring
  have hSumParity : (-1 : ℚ) ^ (n + 1) * separatingSmoothingSum
      (truncateCyclicCorner q a p scale ε) ht hAuxt =
      (-1 : ℚ) ^ n * separatingSmoothingSum q hq hAux := by
    rw [hsum, pow_succ]
    ring
  exact ⟨hε1, hεscale1, ht, hAuxt, hamp, hsum, hAmpParity, hSumParity,
    E, hlabels, hpoint, hsep, hAffected⟩

/-- For each actual support, the support-preserving component equivalence changes
exactly the component containing the replaced corner. -/
theorem component_amplitude_changes_at_corner_only
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq)
    (a p : Fin n) (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (hAuxQ : auxiliaryGenericity (truncateCyclicCorner q a p scale ε) hQ)
    (S : Finset (PolygonCrossing q)) (hS : polygonNonalternating q hq.g2 S)
    (hSQ : polygonNonalternating (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding))
    (hAffected : ∃ hB : CyclicGeneric (daughterVertex (truncateCyclicCorner q a p scale ε)
      hQ.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)),
      polygonAmplitude (daughterVertex (truncateCyclicCorner q a p scale ε)
        hQ.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)) hB =
      -polygonAmplitude (daughterVertex q hq.g2 S (Sum.inl a)) (hAux S hS (Sum.inl a)))
    (c : Component (smoothingDartPermutation q hq.g2 S)) :
    componentAmplitude (truncateCyclicCorner q a p scale ε) hQ (S.map E.toEmbedding)
      hAuxQ hSQ (TruncationDaughterEvents.truncationDartComponentEquiv hq.size_ge_three
        q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S c) =
      if c = componentOf (smoothingDartPermutation q hq.g2 S) (Sum.inl a)
      then -componentAmplitude q hq S hAux hS c
      else componentAmplitude q hq S hAux hS c :=
  TruncationComponentWeights.componentAmplitude_truncation hRI q hq a p hp scale ε
    hε hε1 hscale hscale1 hQ E hleft hright hpoint hAux hAuxQ S hS hSQ hAffected c

/-- The actual component equivalence sends the old corner component to the new one. -/
theorem truncation_component_equiv_tracks_corner
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (S : Finset (PolygonCrossing q)) :
    TruncationDaughterEvents.truncationDartComponentEquiv hq.size_ge_three
      q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S
      (componentOf (smoothingDartPermutation q hq.g2 S) (Sum.inl a)) =
    componentOf (smoothingDartPermutation (truncateCyclicCorner q a p scale ε)
      hQ.g2 (S.map E.toEmbedding)) (Sum.inl a.castSucc) :=
  TruncationDaughterEvents.truncationDartComponentEquiv_extra hq.size_ge_three
    q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S

end DirectGLSSW.SourceTruncation
