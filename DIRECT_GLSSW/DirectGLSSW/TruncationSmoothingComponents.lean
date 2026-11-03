import DirectGLSSW.TruncationSmoothingPairing
import DirectGLSSW.OrderedPointInsertion
import DirectGLSSW.PermutationInsertion
import DirectGLSSW.PolygonNonalternation

set_option autoImplicit false

namespace DirectGLSSW.TruncationSmoothingComponents

open TruncationDirection TruncationEdgeLift TruncationEventOrder PermutationOrbits
attribute [local instance] Classical.propDecidable

theorem truncationPolygonEventSuccessor_map {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c) (x : PolygonEvent q) :
    polygonEventSuccessor (truncateCyclicCorner q a p scale ε) hQ.g2 (truncationPolygonEventMap q a p scale ε E x) =
      if polygonEventSuccessor q hq.g2 x = Sum.inl a then Sum.inl a.castSucc
      else truncationPolygonEventMap q a p scale ε E (polygonEventSuccessor q hq.g2 x) := by
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  letI : LinearOrder (Fin (n + 1) ⊕ CrossingVisit (truncateCyclicCorner q a p scale ε)) :=
    polygonEventOrder (truncateCyclicCorner q a p scale ε) hQ.g2
  letI := polygonEventOrder q hq.g2
  letI := polygonEventOrder (truncateCyclicCorner q a p scale ε) hQ.g2
  let F := truncationPolygonEventOrderIso hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint
  have hb : orderedCyclicSuccessor (PolygonEvent (truncateCyclicCorner q a p scale ε))
      (Sum.inl a.castSucc) = (F (Sum.inl a)).val :=
    truncationPolygonEventSuccessor_extra hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint
  have hs := OrderedPointInsertion.orderedCyclicSuccessor_orderIso_complement
    (Sum.inl a) (Sum.inl a.castSucc) F hb x
  have hval (z : PolygonEvent q) : (F z).val =
      truncationPolygonEventMap q a p scale ε E z := rfl
  simp only [hval] at hs
  by_cases hx : polygonEventSuccessor q hq.g2 x = Sum.inl a
  · rw [if_pos hx]
    have hx' : orderedCyclicSuccessor (Fin n ⊕ CrossingVisit q) x = Sum.inl a := hx
    simpa only [if_pos hx'] using hs
  · rw [if_neg hx]
    have hx' : orderedCyclicSuccessor (Fin n ⊕ CrossingVisit q) x ≠ Sum.inl a := hx
    simpa only [if_neg hx'] using hs

theorem truncationIncomingPermutation_extra {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c) (S : Finset (PolygonCrossing q)) :
    smoothingIncomingPermutation (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc) = truncationPolygonEventMap q a p scale ε E (Sum.inl a) := by
  change polygonEventSuccessor (truncateCyclicCorner q a p scale ε) hQ.g2
    (Sum.inl a.castSucc) = _
  exact truncationPolygonEventSuccessor_extra hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint

theorem truncationIncomingPermutation_map {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c) (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    smoothingIncomingPermutation (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding) (truncationPolygonEventMap q a p scale ε E x) =
      if smoothingIncomingPermutation q hq.g2 S x = Sum.inl a then Sum.inl a.castSucc
      else truncationPolygonEventMap q a p scale ε E (smoothingIncomingPermutation q hq.g2 S x) := by
  rw [smoothingIncomingPermutation_apply,
    TruncationSmoothingPairing.truncationPolygonEventMap_pairing]
  exact truncationPolygonEventSuccessor_map hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint (smoothingPairing q S x)

noncomputable def truncationIncomingComponentEquiv {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c) (S : Finset (PolygonCrossing q)) :
    Component (smoothingIncomingPermutation q hq.g2 S) ≃ Component (smoothingIncomingPermutation (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding)) := PermutationInsertion.insertedComponentEquiv (smoothingIncomingPermutation q hq.g2 S) (smoothingIncomingPermutation (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding)) (Sum.inl a) (Sum.inl a.castSucc)
    (truncationPolygonEventEquiv q a p scale ε E) (truncationIncomingPermutation_extra hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S) (truncationIncomingPermutation_map hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S)

theorem truncationIncomingComponentEquiv_componentOf {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c) (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    truncationIncomingComponentEquiv hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S (componentOf (smoothingIncomingPermutation q hq.g2 S) x) = componentOf (smoothingIncomingPermutation (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding)) (truncationPolygonEventMap q a p scale ε E x) := rfl

theorem truncationIncomingComponentEquiv_extra {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c) (S : Finset (PolygonCrossing q)) :
    truncationIncomingComponentEquiv hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S (componentOf (smoothingIncomingPermutation q hq.g2 S) (Sum.inl a)) =
      componentOf (smoothingIncomingPermutation (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding)) (Sum.inl a.castSucc) := PermutationInsertion.insertedComponentEquiv_extra (smoothingIncomingPermutation q hq.g2 S) (smoothingIncomingPermutation (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding)) (Sum.inl a) (Sum.inl a.castSucc)
    (truncationPolygonEventEquiv q a p scale ε E) (truncationIncomingPermutation_extra hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S) (truncationIncomingPermutation_map hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S)

theorem truncationIncoming_sameCycle_iff {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c) (S : Finset (PolygonCrossing q)) (x y : PolygonEvent q) :
    (smoothingIncomingPermutation (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding)).SameCycle (truncationPolygonEventMap q a p scale ε E x) (truncationPolygonEventMap q a p scale ε E y) ↔ (smoothingIncomingPermutation q hq.g2 S).SameCycle x y := PermutationInsertion.inserted_sameCycle_iff (smoothingIncomingPermutation q hq.g2 S) (smoothingIncomingPermutation (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding)) (Sum.inl a) (Sum.inl a.castSucc)
    (truncationPolygonEventEquiv q a p scale ε E) (truncationIncomingPermutation_extra hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S) (truncationIncomingPermutation_map hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S) x y

theorem truncationExtra_sameCycle_iff {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c) (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    (smoothingIncomingPermutation (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding)).SameCycle (Sum.inl a.castSucc) (truncationPolygonEventMap q a p scale ε E x) ↔
      (smoothingIncomingPermutation q hq.g2 S).SameCycle (Sum.inl a) x := PermutationInsertion.extra_sameCycle_iff (smoothingIncomingPermutation q hq.g2 S) (smoothingIncomingPermutation (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding)) (Sum.inl a) (Sum.inl a.castSucc)
    (truncationPolygonEventEquiv q a p scale ε E) (truncationIncomingPermutation_extra hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S) (truncationIncomingPermutation_map hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S) x

theorem truncationIncoming_componentCount {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c) (S : Finset (PolygonCrossing q)) :
    componentCount (smoothingIncomingPermutation q hq.g2 S) = componentCount (smoothingIncomingPermutation (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding)) := Fintype.card_congr (truncationIncomingComponentEquiv hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S)

theorem truncation_polygonNonalternating_iff {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c) (S : Finset (PolygonCrossing q)) :
    PolygonNonalternation.polygonNonalternating q hq.g2 S ↔
      PolygonNonalternation.polygonNonalternating (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding) := by
  rw [PolygonNonalternation.polygonNonalternating_iff_incoming_count q hq.g2 hn,
    PolygonNonalternation.polygonNonalternating_iff_incoming_count (truncateCyclicCorner q a p scale ε) hQ.g2 (by omega),
    Finset.card_map, truncationIncoming_componentCount hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S]

noncomputable def truncationSeparatingSupportEquiv {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c) :
    {S : Finset (PolygonCrossing q) // PolygonNonalternation.polygonNonalternating q hq.g2 S} ≃
    {T : Finset (PolygonCrossing (truncateCyclicCorner q a p scale ε)) //
      PolygonNonalternation.polygonNonalternating (truncateCyclicCorner q a p scale ε) hQ.g2 T} := E.finsetCongr.subtypeEquiv (truncation_polygonNonalternating_iff hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint)

theorem truncationSeparatingSupportEquiv_apply {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c)
    (S : {S : Finset (PolygonCrossing q) // PolygonNonalternation.polygonNonalternating q hq.g2 S}) :
    (truncationSeparatingSupportEquiv hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S).val = S.val.map E.toEmbedding := rfl

end DirectGLSSW.TruncationSmoothingComponents
