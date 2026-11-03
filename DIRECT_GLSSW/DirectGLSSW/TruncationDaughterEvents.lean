import DirectGLSSW.TruncationSmoothingComponents
import DirectGLSSW.DaughterFirstReturn

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DirectGLSSW.TruncationDaughterEvents

open DirectGLSSW
open TruncationDirection TruncationEdgeLift TruncationEventOrder
open TruncationSmoothingComponents TruncationSmoothingPairing DaughterFirstReturn PermutationOrbits
attribute [local instance] Classical.propDecidable

theorem truncationDartPermutation_extra {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (S : Finset (PolygonCrossing q)) :
    smoothingDartPermutation (truncateCyclicCorner q a p scale ε) hQ.g2
        (S.map E.toEmbedding) (Sum.inl a.castSucc) =
      truncationPolygonEventMap q a p scale ε E (Sum.inl a) := by
  change smoothingPairing (truncateCyclicCorner q a p scale ε) (S.map E.toEmbedding)
    (polygonEventSuccessor (truncateCyclicCorner q a p scale ε) hQ.g2 (Sum.inl a.castSucc)) = _
  rw [truncationPolygonEventSuccessor_extra hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint]
  rw [truncationPolygonEventMap_pairing]
  simp [smoothingPairing, smoothingPairingMap]

theorem truncationDartPermutation_map {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    smoothingDartPermutation (truncateCyclicCorner q a p scale ε) hQ.g2
        (S.map E.toEmbedding) (truncationPolygonEventMap q a p scale ε E x) =
      if smoothingDartPermutation q hq.g2 S x = Sum.inl a then
        Sum.inl a.castSucc
      else truncationPolygonEventMap q a p scale ε E
        (smoothingDartPermutation q hq.g2 S x) := by
  let Q := truncateCyclicCorner q a p scale ε
  let F := truncationPolygonEventMap q a p scale ε E
  let A : PolygonEvent q := Sum.inl a
  let B : PolygonEvent Q := Sum.inl a.castSucc
  change smoothingPairing Q (S.map E.toEmbedding) (polygonEventSuccessor Q hQ.g2 (F x)) = _
  rw [truncationPolygonEventSuccessor_map hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint]
  by_cases hs : polygonEventSuccessor q hq.g2 x = A
  · have hpairA : smoothingPairing q S A = A := by
      simp [A, smoothingPairing, smoothingPairingMap]
    have hold : smoothingDartPermutation q hq.g2 S x = A := by
      simp [smoothingDartPermutation, hs, hpairA]
    rw [if_pos hs]
    rw [if_pos hold]
    simp [B, smoothingPairing, smoothingPairingMap]
  · have hpairA : smoothingPairing q S A = A := by
      simp [A, smoothingPairing, smoothingPairingMap]
    have hA : smoothingPairing q S (polygonEventSuccessor q hq.g2 x) ≠ A := by
      intro hy
      have heq : polygonEventSuccessor q hq.g2 x = A :=
        (smoothingPairing q S).injective (hy.trans hpairA.symm)
      exact hs heq
    have hold : smoothingDartPermutation q hq.g2 S x ≠ A := by
      simpa [smoothingDartPermutation] using hA
    rw [if_neg hs]
    rw [if_neg hold]
    rw [truncationPolygonEventMap_pairing]
    rfl

theorem truncationRetainedCorner_map_iff {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    retainedCorner (truncateCyclicCorner q a p scale ε) (S.map E.toEmbedding)
      (truncationPolygonEventMap q a p scale ε E x) ↔ retainedCorner q S x := by
  cases x with
  | inl e => simp [retainedCorner, truncationPolygonEventMap]
  | inr v =>
      rcases v with ⟨c, b⟩
      change E c ∈ S.map E.toEmbedding ↔ c ∈ S
      rw [Finset.mem_map]
      constructor
      · rintro ⟨d, hd, hde⟩
        have hdc : d = c := E.injective hde
        simpa [hdc] using hd
      · intro hc
        exact ⟨c, hc, rfl⟩

theorem truncationRetainedCorner_extra {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (S : Finset (PolygonCrossing q)) :
    retainedCorner (truncateCyclicCorner q a p scale ε) (S.map E.toEmbedding)
      (Sum.inl a.castSucc) := by
  simp [retainedCorner]

theorem truncationPolygonEventPoint_oldAnchor {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (S : Finset (PolygonCrossing q)) (e : Fin n) :
    polygonEventPoint (truncateCyclicCorner q a p scale ε)
      (truncationPolygonEventMap q a p scale ε E (Sum.inl e)) =
      if e = a then
        truncateCyclicCorner q a p scale ε ⟨a.val + 1, by omega⟩
      else q e := by
  by_cases he : e = a
  · subst e
    have hlift : edgeLift a a = (⟨a.val + 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp [edgeLift]
    simp [truncationPolygonEventMap, polygonEventPoint, hlift]
  · have hcollapse : ShortEdgeCyclicAdapter.collapseFin a (edgeLift a e) ≠ a := by
      rw [collapseFin_edgeLift]
      exact he
    simp only [truncationPolygonEventMap, polygonEventPoint]
    rw [truncateCyclicCorner_of_collapse_ne q a p scale ε (edgeLift a e) hcollapse]
    rw [collapseFin_edgeLift]
    simp [he]

theorem truncationPolygonEventPoint_visit {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (S : Finset (PolygonCrossing q)) (v : CrossingVisit q) :
    polygonEventPoint (truncateCyclicCorner q a p scale ε)
      (truncationPolygonEventMap q a p scale ε E (Sum.inr v)) =
      crossingVisitPoint q v := by
  simp [truncationPolygonEventMap, polygonEventPoint,
    crossingVisit_mapEquiv_point E hpoint v]

theorem truncationPolygonEventPoint_extra {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (S : Finset (PolygonCrossing q)) :
    polygonEventPoint (truncateCyclicCorner q a p scale ε) (Sum.inl a.castSucc) =
      q a + ε • (q p - q a) := by
  simpa [polygonEventPoint] using truncateCyclicCorner_anchor q a p scale ε

noncomputable def truncationDartComponentEquiv {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (S : Finset (PolygonCrossing q)) :
    Component (smoothingDartPermutation q hq.g2 S) ≃
      Component (smoothingDartPermutation (truncateCyclicCorner q a p scale ε) hQ.g2
        (S.map E.toEmbedding)) := by
  let Q := truncateCyclicCorner q a p scale ε
  let F := truncationPolygonEventEquiv q a p scale ε E
  let A : PolygonEvent q := Sum.inl a
  let B : PolygonEvent Q := Sum.inl a.castSucc
  have hb : smoothingDartPermutation Q hQ.g2 (S.map E.toEmbedding) B = (F A).val := by
    simpa [F, Q, truncationPolygonEventEquiv_apply_val] using
      truncationDartPermutation_extra hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S
  have hs : ∀ x, smoothingDartPermutation Q hQ.g2 (S.map E.toEmbedding) (F x).val =
      if smoothingDartPermutation q hq.g2 S x = A then B
      else (F (smoothingDartPermutation q hq.g2 S x)).val := by
    intro x
    simpa [F, Q, A, B, truncationPolygonEventEquiv_apply_val] using
      truncationDartPermutation_map hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S x
  exact PermutationInsertion.insertedComponentEquiv
    (smoothingDartPermutation q hq.g2 S)
    (smoothingDartPermutation Q hQ.g2 (S.map E.toEmbedding)) A B F hb hs

theorem truncationDartComponentEquiv_componentOf {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    truncationDartComponentEquiv hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S
        (componentOf (smoothingDartPermutation q hq.g2 S) x) =
      componentOf (smoothingDartPermutation (truncateCyclicCorner q a p scale ε) hQ.g2
        (S.map E.toEmbedding)) (truncationPolygonEventMap q a p scale ε E x) := by
  let Q := truncateCyclicCorner q a p scale ε
  let F := truncationPolygonEventEquiv q a p scale ε E
  have hb := by
    simpa [F, Q, truncationPolygonEventEquiv_apply_val] using
      truncationDartPermutation_extra hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S
  have hs : ∀ y, smoothingDartPermutation Q hQ.g2 (S.map E.toEmbedding) (F y).val =
      if smoothingDartPermutation q hq.g2 S y = Sum.inl a then Sum.inl a.castSucc
      else (F (smoothingDartPermutation q hq.g2 S y)).val := by
    intro y
    simpa [F, Q, truncationPolygonEventEquiv_apply_val] using
      truncationDartPermutation_map hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S y
  have hresult := PermutationInsertion.insertedComponentEquiv_componentOf
    (smoothingDartPermutation q hq.g2 S)
    (smoothingDartPermutation Q hQ.g2 (S.map E.toEmbedding)) (Sum.inl a) (Sum.inl a.castSucc)
    F hb hs x
  simpa [truncationDartComponentEquiv, Q, F, truncationPolygonEventEquiv_apply_val] using hresult

theorem truncationDartComponentEquiv_extra {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (S : Finset (PolygonCrossing q)) :
    truncationDartComponentEquiv hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S
        (componentOf (smoothingDartPermutation q hq.g2 S) (Sum.inl a)) =
      componentOf (smoothingDartPermutation (truncateCyclicCorner q a p scale ε) hQ.g2
        (S.map E.toEmbedding)) (Sum.inl a.castSucc) := by
  calc
    truncationDartComponentEquiv hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S
        (componentOf (smoothingDartPermutation q hq.g2 S) (Sum.inl a)) =
      componentOf (smoothingDartPermutation (truncateCyclicCorner q a p scale ε) hQ.g2
        (S.map E.toEmbedding)) (truncationPolygonEventMap q a p scale ε E (Sum.inl a)) :=
          truncationDartComponentEquiv_componentOf hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S (Sum.inl a)
    _ = componentOf (smoothingDartPermutation (truncateCyclicCorner q a p scale ε) hQ.g2
        (S.map E.toEmbedding))
          (smoothingDartPermutation (truncateCyclicCorner q a p scale ε) hQ.g2
            (S.map E.toEmbedding) (Sum.inl a.castSucc)) := by
          rw [truncationDartPermutation_extra hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S]
    _ = componentOf (smoothingDartPermutation (truncateCyclicCorner q a p scale ε) hQ.g2
        (S.map E.toEmbedding)) (Sum.inl a.castSucc) := componentOf_apply _ _


end DirectGLSSW.TruncationDaughterEvents
