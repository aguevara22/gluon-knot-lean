import DirectGLSSW.ShortEdgeGenericityRadius
import DirectGLSSW.ShortEdgeSignStability

namespace DirectGLSSW.ShortEdgeGenericity

open DirectGLSSW

private theorem exists_scalarSignValue_local_radius (f : ℝ → ℝ)
    (hf : Continuous f) (hf0 : f 0 ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      scalarSignValue (f t) = scalarSignValue (f 0) := by
  by_cases hpos : 0 < f 0
  · let S : Set ℝ := {x | 0 < f x}
    have hopen : IsOpen S := isOpen_Ioi.preimage hf
    have hmem : 0 ∈ S := hpos
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
    refine ⟨δ, hδ, ?_⟩
    intro t ht
    have hft : 0 < f t := hball (by simpa [Metric.mem_ball, Real.dist_eq] using ht)
    simp [scalarSignValue, ne_of_gt hpos, ne_of_gt hft, not_lt_of_ge (le_of_lt hpos),
      not_lt_of_ge (le_of_lt hft)]
  · have hneg : f 0 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hf0
    let S : Set ℝ := {x | f x < 0}
    have hopen : IsOpen S := isOpen_Iio.preimage hf
    have hmem : 0 ∈ S := hneg
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
    refine ⟨δ, hδ, ?_⟩
    intro t ht
    have hft : f t < 0 := hball (by simpa [Metric.mem_ball, Real.dist_eq] using ht)
    simp [scalarSignValue, ne_of_lt hneg, ne_of_lt hft, hneg, hft]

theorem exists_local_cyclicGeneric_and_orderedSign_stability {n : ℕ}
    (Q : ℝ → Fin n → PlanarPoint ℝ)
    (hQ : ∀ v : Fin n, Continuous (fun t : ℝ => Q t v))
    (h0 : CyclicGeneric (Q 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      CyclicGeneric (Q t) ∧
        ∀ i k j : Fin n, i ≠ k → k ≠ j → i ≠ j →
          scalarSignValue (planarDet (Q t k - Q t j) (Q t i - Q t j)) =
            scalarSignValue (planarDet (Q 0 k - Q 0 j) (Q 0 i - Q 0 j)) := by
  classical
  let triples : Finset (Fin n × Fin n × Fin n) := Finset.univ
  let SignStable (tr : Fin n × Fin n × Fin n) (t : ℝ) : Prop :=
    tr.1 ≠ tr.2.1 → tr.2.1 ≠ tr.2.2 → tr.1 ≠ tr.2.2 →
      scalarSignValue
        (planarDet (Q t tr.2.1 - Q t tr.2.2) (Q t tr.1 - Q t tr.2.2)) =
      scalarSignValue
        (planarDet (Q 0 tr.2.1 - Q 0 tr.2.2) (Q 0 tr.1 - Q 0 tr.2.2))
  have hsignlocal : ∀ tr, tr ∈ triples →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → SignStable tr t := by
    intro tr _
    by_cases hdist : tr.1 ≠ tr.2.1 ∧ tr.2.1 ≠ tr.2.2 ∧ tr.1 ≠ tr.2.2
    · let f : ℝ → ℝ := fun t =>
        planarDet (Q t tr.2.1 - Q t tr.2.2) (Q t tr.1 - Q t tr.2.2)
      have hf : Continuous f := by
        dsimp [f]
        continuity
      have hf0 : f 0 ≠ 0 := h0.g1 tr.1 tr.2.1 tr.2.2 hdist.1 hdist.2.1 hdist.2.2
      obtain ⟨δ, hδ, hgood⟩ := exists_scalarSignValue_local_radius f hf hf0
      refine ⟨δ, hδ, ?_⟩
      intro t ht _ _ _
      exact hgood t ht
    · refine ⟨1, by norm_num, ?_⟩
      intro t _ h1 h2 h3
      exact False.elim (hdist ⟨h1, h2, h3⟩)
  have hsignposlocal : ∀ tr, tr ∈ triples →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → SignStable tr ε := by
    intro tr htr
    obtain ⟨δ, hδ, hg⟩ := hsignlocal tr htr
    exact ⟨δ, hδ, fun ε hε hεδ => hg ε (by simpa [abs_of_pos hε] using hεδ)⟩
  have hsignneglocal : ∀ tr, tr ∈ triples →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → SignStable tr (-ε) := by
    intro tr htr
    obtain ⟨δ, hδ, hg⟩ := hsignlocal tr htr
    exact ⟨δ, hδ, fun ε hε hεδ => hg (-ε) (by simpa [abs_of_pos hε] using hεδ)⟩
  obtain ⟨δsignPos, hδsignPos, hsignPos⟩ :=
    ShortEdgeSignStability.exists_finset_common_radius triples SignStable hsignposlocal
  obtain ⟨δsignNeg, hδsignNeg, hsignNeg⟩ :=
    ShortEdgeSignStability.exists_finset_common_radius triples (fun tr ε => SignStable tr (-ε)) hsignneglocal
  let NoClosed (tr : Fin n × Fin n × Fin n) (t : ℝ) : Prop :=
    SeparatedTriple tr.1 tr.2.1 tr.2.2 →
      ¬ ∃ x : PlanarPoint ℝ,
        edgeClosed (Q t) tr.1 x ∧ edgeClosed (Q t) tr.2.1 x ∧
          edgeClosed (Q t) tr.2.2 x
  have hclosedlocal : ∀ tr, tr ∈ triples →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → NoClosed tr t := by
    intro tr _
    by_cases hsep : SeparatedTriple tr.1 tr.2.1 tr.2.2
    · have hzero : ¬ ∃ x : PlanarPoint ℝ,
          edgeClosed (Q 0) tr.1 x ∧ edgeClosed (Q 0) tr.2.1 x ∧
            edgeClosed (Q 0) tr.2.2 x :=
        by
          intro hx
          rcases hx with ⟨x, hx⟩
          exact cyclic_no_three_closed_edges (Q 0) h0 tr.1 tr.2.1 tr.2.2 x
            hsep.1 hsep.2.1 hsep.2.2.1 hx
      obtain ⟨δ, hδ, hgood⟩ :=
        exists_no_three_closed_radius Q tr.1 tr.2.1 tr.2.2 hQ hzero
      refine ⟨δ, hδ, ?_⟩
      intro t ht _
      exact hgood t ht
    · refine ⟨1, by norm_num, ?_⟩
      intro t _ h
      exact False.elim (hsep h)
  have hclosedposlocal : ∀ tr, tr ∈ triples →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → NoClosed tr ε := by
    intro tr htr
    obtain ⟨δ, hδ, hg⟩ := hclosedlocal tr htr
    exact ⟨δ, hδ, fun ε hε hεδ => hg ε (by simpa [abs_of_pos hε] using hεδ)⟩
  have hclosedneglocal : ∀ tr, tr ∈ triples →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → NoClosed tr (-ε) := by
    intro tr htr
    obtain ⟨δ, hδ, hg⟩ := hclosedlocal tr htr
    exact ⟨δ, hδ, fun ε hε hεδ => hg (-ε) (by simpa [abs_of_pos hε] using hεδ)⟩
  obtain ⟨δclosedPos, hδclosedPos, hclosedPos⟩ :=
    ShortEdgeSignStability.exists_finset_common_radius triples NoClosed hclosedposlocal
  obtain ⟨δclosedNeg, hδclosedNeg, hclosedNeg⟩ :=
    ShortEdgeSignStability.exists_finset_common_radius triples (fun tr ε => NoClosed tr (-ε)) hclosedneglocal
  let δ := min (min δsignPos δsignNeg) (min δclosedPos δclosedNeg)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have hδsignPos' : δ ≤ δsignPos := by dsimp [δ]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδsignNeg' : δ ≤ δsignNeg := by dsimp [δ]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδclosedPos' : δ ≤ δclosedPos := by dsimp [δ]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδclosedNeg' : δ ≤ δclosedNeg := by dsimp [δ]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have htSignAbsPos : |t| < δsignPos := lt_of_lt_of_le ht hδsignPos'
  have htSignAbsNeg : |t| < δsignNeg := lt_of_lt_of_le ht hδsignNeg'
  have htClosedAbsPos : |t| < δclosedPos := lt_of_lt_of_le ht hδclosedPos'
  have htClosedAbsNeg : |t| < δclosedNeg := lt_of_lt_of_le ht hδclosedNeg'
  have hsign' : ∀ i k j : Fin n, i ≠ k → k ≠ j → i ≠ j →
      scalarSignValue (planarDet (Q t k - Q t j) (Q t i - Q t j)) =
        scalarSignValue (planarDet (Q 0 k - Q 0 j) (Q 0 i - Q 0 j)) := by
    intro i k j hik hkj hij
    by_cases ht0 : t = 0
    · simp [ht0]
    · by_cases htp : 0 < t
      · have habs : |t| = t := abs_of_pos htp
        exact hsignPos t htp (by simpa [habs] using htSignAbsPos) (i, k, j)
          (Finset.mem_univ _) hik hkj hij
      · have htn : t < 0 := lt_of_le_of_ne (le_of_not_gt htp) ht0
        have habs : |t| = -t := abs_of_neg htn
        have hpos : 0 < -t := neg_pos.mpr htn
        simpa using hsignNeg (-t) hpos (by simpa [habs] using htSignAbsNeg)
          (i, k, j) (Finset.mem_univ _) hik hkj hij
  have hG1 : cyclicNoncollinear (Q t) := by
    intro i k j hik hkj hij
    have hbase : planarDet (Q 0 k - Q 0 j) (Q 0 i - Q 0 j) ≠ 0 :=
      h0.g1 i k j hik hkj hij
    have hs0 : scalarSignValue
        (planarDet (Q 0 k - Q 0 j) (Q 0 i - Q 0 j)) ≠ 0 := by
      rw [scalarSignValue_eq_nonzeroScalarSign _ hbase]
      cases nonzeroScalarSign (planarDet (Q 0 k - Q 0 j) (Q 0 i - Q 0 j)) hbase <;>
        simp [Sign.value]
    intro hdet
    have hs := hsign' i k j hik hkj hij
    rw [hdet, scalarSignValue] at hs
    exact hs0 (by simpa using hs.symm)
  have hG2 : cyclicNoTripleIntersections (Q t) := by
    intro e f g x hef hfg heg hbad
    by_cases htzero : t = 0
    · subst t
      exact h0.g2 e f g x hef hfg heg hbad
    rcases hbad with ⟨he, hf, hg⟩
    have hnonadj : ∀ i j : Fin n,
        edgeInterior (Q t) i x → edgeInterior (Q t) j x → cyclicSuccessor i ≠ j := by
      intro i j hi hj hij
      subst j
      exact cyclic_adjacent_interiors_disjoint h0.size_ge_three (Q t) hG1 i x hi hj
    have hsep : SeparatedTriple e f g :=
      ⟨hef, hfg, heg, hnonadj e f he hf, hnonadj f e hf he,
        hnonadj f g hf hg, hnonadj g f hg hf, hnonadj e g he hg,
        hnonadj g e hg he⟩
    have hclosed' (i : Fin n) (x : PlanarPoint ℝ)
        (hi : edgeInterior (Q t) i x) : edgeClosed (Q t) i x := by
      obtain ⟨s, hs0, hs1, hxs⟩ := hi
      exact ⟨s, le_of_lt hs0, le_of_lt hs1, hxs⟩
    have hbad' : ∃ y : PlanarPoint ℝ,
        edgeClosed (Q t) e y ∧ edgeClosed (Q t) f y ∧ edgeClosed (Q t) g y :=
      ⟨x, hclosed' e x he, hclosed' f x hf, hclosed' g x hg⟩
    by_cases htp : 0 < t
    · exact hclosedPos t htp (by simpa [abs_of_pos htp] using htClosedAbsPos)
        (e, f, g) (Finset.mem_univ _) hsep hbad'
    · have htn : t < 0 := lt_of_le_of_ne (le_of_not_gt htp) htzero
      have hpos : 0 < -t := neg_pos.mpr htn
      have hclosedNeg' := hclosedNeg (-t) hpos
        (by simpa [abs_of_neg htn] using htClosedAbsNeg)
        (e, f, g) (Finset.mem_univ _) hsep
      apply hclosedNeg'
      simpa [neg_neg] using hbad'
  exact ⟨⟨h0.size_ge_three, hG1, hG2⟩, hsign'⟩

end DirectGLSSW.ShortEdgeGenericity
