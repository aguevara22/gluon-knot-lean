import DirectGLSSW.TruncationDaughterEvents
import DirectGLSSW.PermutationInsertionWords
import DirectGLSSW.DaughterPointListFilter

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DirectGLSSW.TruncationDaughterPointTransport

open DirectGLSSW
open TruncationDirection TruncationEdgeLift TruncationEventOrder
open TruncationDaughterEvents DaughterFirstReturn PermutationOrbits PermutationInsertion
open DaughterPointListFilter TruncationSmoothingComponents
attribute [local instance] Classical.propDecidable

theorem truncationDaughterPointList_unaffected {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q)
    (hx : ¬ (smoothingDartPermutation q hq.g2 S).SameCycle x (Sum.inl a)) :
    daughterPointList (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding)
        (truncationPolygonEventMap q a p scale ε E x) =
      daughterPointList q hq.g2 S x := by
  let Q := truncateCyclicCorner q a p scale ε
  let Dq := smoothingDartPermutation q hq.g2 S
  let DQ := smoothingDartPermutation Q hQ.g2 (S.map E.toEmbedding)
  let A : PolygonEvent q := Sum.inl a
  let B : PolygonEvent Q := Sum.inl a.castSucc
  let F := truncationPolygonEventMap q a p scale ε E
  let Fe := truncationPolygonEventEquiv q a p scale ε E
  have hb : DQ B = (Fe A).val := by
    simpa [DQ, Fe, Q, A, B, truncationPolygonEventEquiv_apply_val] using
      truncationDartPermutation_extra hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S
  have hstep : ∀ z, DQ (Fe z).val = if Dq z = A then B else (Fe (Dq z)).val := by
    intro z
    simpa [DQ, Dq, Fe, Q, A, B, truncationPolygonEventEquiv_apply_val] using
      truncationDartPermutation_map hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S z
  have hword : orbitWord DQ (F x) =
      (orbitWord Dq x).map (fun z => (Fe z).val) := by
    simpa [F, Fe, Q, truncationPolygonEventEquiv_apply_val] using
      PermutationInsertion.unaffected_orbitWord Dq DQ A B Fe hb hstep x hx
  have hret (z : PolygonEvent q) :
      decide (retainedCorner Q (S.map E.toEmbedding) (F z)) = decide (retainedCorner q S z) := by
    have hi := truncationRetainedCorner_map_iff hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S z
    simp [F, Q, hi]
  have hretFe : (fun z => decide (retainedCorner Q (S.map E.toEmbedding) (Fe z).val)) =
      (fun z => decide (retainedCorner q S z)) := by
    funext z
    simpa [Fe, F, Q, truncationPolygonEventEquiv_apply_val] using hret z
  have hpointMap (z : PolygonEvent q) (hz : z ∈ orbitWord Dq x) :
      polygonEventPoint Q (F z) = polygonEventPoint q z := by
    have hzA : z ≠ A := by
      intro heq
      apply hx
      exact (PermutationOrbits.mem_orbitWord_iff Dq x A).mp (heq ▸ hz)
    cases z with
    | inl e =>
        have hea : e ≠ a := by
          intro he
          apply hzA
          exact congrArg Sum.inl he
        simpa [F, Q, hea] using
          truncationPolygonEventPoint_oldAnchor hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S e
    | inr v =>
        simpa [F, Q] using
          truncationPolygonEventPoint_visit hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S v
  rw [daughterPointList_eq_filtered_orbitWord_map q hq.g2 S x,
      daughterPointList_eq_filtered_orbitWord_map Q hQ.g2 (S.map E.toEmbedding) (F x)]
  rw [hword]
  rw [← DaughterPointListFilter.map_filter_comp
    (fun z => (Fe z).val)
    (fun y => decide (retainedCorner Q (S.map E.toEmbedding) y))
    (orbitWord Dq x)]
  rw [hretFe, List.map_map]
  apply List.map_congr_left
  intro z hz
  simpa only [truncationPolygonEventEquiv_apply_val] using
    hpointMap z (List.mem_filter.mp hz).1

theorem truncationDaughterPointList_affected {n : ℕ}
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
    daughterPointList (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding)
        (Sum.inl a.castSucc) =
      (q a + ε • (q p - q a)) ::
        (q a + (ε * scale) • (q (cyclicSuccessor a) - q a)) ::
          (daughterPointList q hq.g2 S (Sum.inl a)).tail := by
  let Q := truncateCyclicCorner q a p scale ε
  let Dq := smoothingDartPermutation q hq.g2 S
  let DQ := smoothingDartPermutation Q hQ.g2 (S.map E.toEmbedding)
  let A : PolygonEvent q := Sum.inl a
  let B : PolygonEvent Q := Sum.inl a.castSucc
  let F := truncationPolygonEventMap q a p scale ε E
  let Fe := truncationPolygonEventEquiv q a p scale ε E
  have hb : DQ B = (Fe A).val := by
    simpa [DQ, Fe, Q, A, B, truncationPolygonEventEquiv_apply_val] using
      truncationDartPermutation_extra hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S
  have hstep : ∀ z, DQ (Fe z).val = if Dq z = A then B else (Fe (Dq z)).val := by
    intro z
    simpa [DQ, Dq, Fe, Q, A, B, truncationPolygonEventEquiv_apply_val] using
      truncationDartPermutation_map hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S z
  have hword := PermutationInsertion.inserted_orbitWord Dq DQ A B Fe hb hstep
  have hwordRoot : orbitWord Dq A = A :: (orbitWord Dq A).tail := by
    have hnword : orbitWord Dq A ≠ [] := orbitWord_nonempty Dq A
    have hhead : (orbitWord Dq A).head hnword = A := by
      rw [List.head_eq_getElem_zero]
      simp [PermutationOrbits.orbitWord, PermutationOrbits.orbitEnumeration_zero]
    calc
      orbitWord Dq A = (orbitWord Dq A).head hnword :: (orbitWord Dq A).tail :=
        (List.head_cons_tail (orbitWord Dq A) hnword).symm
      _ = A :: (orbitWord Dq A).tail := by rw [hhead]
  have hA_tail : A ∉ (orbitWord Dq A).tail := by
    have hnodup := orbitWord_nodup Dq A
    rw [hwordRoot] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hretA : retainedCorner q S A := by simp [A, retainedCorner]
  have hretB : retainedCorner Q (S.map E.toEmbedding) B := by
    simpa [Q, B] using truncationRetainedCorner_extra hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S
  have hretMap (z : PolygonEvent q) :
      decide (retainedCorner Q (S.map E.toEmbedding) (F z)) = decide (retainedCorner q S z) := by
    have hi := truncationRetainedCorner_map_iff hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S z
    simp [F, Q, hi]
  have hretFe : (fun z => decide (retainedCorner Q (S.map E.toEmbedding) (Fe z).val)) =
      (fun z => decide (retainedCorner q S z)) := by
    funext z
    simpa [Fe, F, Q, truncationPolygonEventEquiv_apply_val] using hretMap z
  have hFA : (Fe A).val = F A := by rfl
  have hfiltered :
      (orbitWord DQ B).filter (fun z => decide (retainedCorner Q (S.map E.toEmbedding) z)) =
        B :: F A :: ((orbitWord Dq A).tail.filter
          (fun z => decide (retainedCorner q S z))).map (fun z => (Fe z).val) := by
    rw [hword]
    rw [hwordRoot]
    simp only [List.map_cons, List.filter_cons]
    have hretFA : retainedCorner Q (S.map E.toEmbedding) (F A) :=
      (truncationRetainedCorner_map_iff hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S A).mpr hretA
    rw [if_pos (by simpa [B] using hretB), if_pos (by simpa [F, A] using hretFA)]
    have hfilterTail :
        (List.map (fun z => (Fe z).val) ((orbitWord Dq A).tail)).filter
          (fun z => decide (retainedCorner Q (S.map E.toEmbedding) z)) =
        List.map (fun z => (Fe z).val)
          (((orbitWord Dq A).tail).filter (fun z => decide (retainedCorner q S z))) := by
      calc
        _ = List.map (fun z => (Fe z).val)
            (((orbitWord Dq A).tail).filter
              (fun z => decide (retainedCorner Q (S.map E.toEmbedding) (Fe z).val))) :=
                (DaughterPointListFilter.map_filter_comp
                  (fun z => (Fe z).val)
                  (fun y => decide (retainedCorner Q (S.map E.toEmbedding) y))
                  ((orbitWord Dq A).tail)).symm
        _ = _ := by rw [hretFe]
    simp only [truncationPolygonEventEquiv_apply_val, List.tail_cons]
    rw [hfilterTail, hFA]
  have hpointMap (z : PolygonEvent q) (hz : z ∈ (orbitWord Dq A).tail) :
      polygonEventPoint Q (F z) = polygonEventPoint q z := by
    have hzA : z ≠ A := by
      intro heq
      apply hA_tail
      simpa [heq] using hz
    cases z with
    | inl e =>
        have hea : e ≠ a := by
          intro he
          apply hzA
          exact congrArg Sum.inl he
        simpa [F, Q, hea] using
          truncationPolygonEventPoint_oldAnchor hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S e
    | inr v =>
        simpa [F, Q] using
          truncationPolygonEventPoint_visit hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S v
  have htailMap :
      (((orbitWord Dq A).tail.filter (fun z => decide (retainedCorner q S z))).map
        (fun z => (Fe z).val)).map (polygonEventPoint Q) =
      ((orbitWord Dq A).tail.filter (fun z => decide (retainedCorner q S z))).map
        (polygonEventPoint q) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro z hz
    simpa only [truncationPolygonEventEquiv_apply_val] using
      hpointMap z (List.mem_filter.mp hz).1
  have hOldTail :
      (daughterPointList q hq.g2 S A).tail =
        ((orbitWord Dq A).tail.filter (fun z => decide (retainedCorner q S z))).map
          (polygonEventPoint q) := by
    rw [daughterPointList_eq_filtered_orbitWord_map q hq.g2 S A, hwordRoot]
    simp [hretA]
  have hpointB : polygonEventPoint Q B = q a + ε • (q p - q a) := by
    simpa [Q, B] using
      truncationPolygonEventPoint_extra hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S
  have hpointFA : polygonEventPoint Q (F A) =
      q a + (ε * scale) • (q (cyclicSuccessor a) - q a) := by
    have h := truncationPolygonEventPoint_oldAnchor hn q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S a
    simpa [F, Q, A, truncateCyclicCorner_new] using h
  rw [daughterPointList_eq_filtered_orbitWord_map Q hQ.g2 (S.map E.toEmbedding) B, hfiltered]
  simp only [List.map_cons]
  rw [hpointB, hpointFA, htailMap, ← hOldTail]

end DirectGLSSW.TruncationDaughterPointTransport
