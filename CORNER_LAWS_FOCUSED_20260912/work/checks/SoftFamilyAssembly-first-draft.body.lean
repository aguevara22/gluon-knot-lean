namespace SM

noncomputable section
open Filter Topology
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Candidate assembly of all four clauses of source lem:soft-generic.
The global limiting functions are explicitly identified with the actual
canonical crossing data on the same positive interval. Every local premise
is derived from the parent Generic/admissibility assumptions. -/
theorem soft_family_generic_source (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    Tendsto (fun ε : ℝ => edge (softInsertion P j q ε) (softNewIndex j))
      (𝓝 (0 : ℝ)) (𝓝 (edge P j)) ∧
    (∀ k l : ZMod n, ∀ hc : IsCrossing P {k, l},
      Tendsto (softInheritedPoint P j k l q) (𝓝 (0 : ℝ))
        (𝓝 (crossingPoint (⟨{k, l}, hc⟩ : Crossing P))) ∧
      Tendsto (fun ε : ℝ => edgeParameter (softInsertion P j q ε)
        (softParentEdge j k) (softParentEdge j l)) (𝓝 (0 : ℝ))
        (𝓝 (visitParameter (pairVisit hc))) ∧
      Tendsto (fun ε : ℝ => edgeParameter (softInsertion P j q ε)
        (softParentEdge j l) (softParentEdge j k)) (𝓝 (0 : ℝ))
        (𝓝 (visitParameter
          (pairVisit (by simpa only [Finset.pair_comm] using hc : IsCrossing P {l, k}))))) ∧
    Tendsto (softNewbornIncomingParameter P j q) (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) ∧
    Tendsto (softNewbornReturnParameter P j q) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
    Tendsto (softNewbornPoint P j q) (𝓝 (0 : ℝ)) (𝓝 (P j)) ∧
    ∃ δ > 0, ∃ B : GenericTuple (n + 1),
      ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hQ : Generic (softInsertion P j q ε),
      ∃ hp : SoftCrossingPersistence P j q ε,
      ∃ hclass : SoftCrossingClassificationAt P j q ε,
        /- Clause (i): actual Generic, one chamber and all soft-edge contacts. -/
        ((⟨softInsertion P j q ε, hQ⟩ : GenericTuple (n + 1)) ∈ labelledChamber B ∧
          polygonProjection (⟨softInsertion P j q ε, hQ⟩ : GenericTuple (n + 1)) ∈
            chamber (polygonProjection B) ∧
          edgeSegment (softInsertion P j q ε) (softOldIndex j j) ∩
            edgeSegment (softInsertion P j q ε) (softOldIndex j (j - 1)) = {P j} ∧
          edgeSegment (softInsertion P j q ε) (softOldIndex j j) ∩
            edgeSegment (softInsertion P j q ε) (softNewIndex j) = {P j + ε • q} ∧
          (∀ a : ZMod (n + 1), a ≠ softOldIndex j j → a ≠ softOldIndex j (j - 1) →
            a ≠ softNewIndex j →
            Disjoint (edgeSegment (softInsertion P j q ε) (softOldIndex j j))
              (edgeSegment (softInsertion P j q ε) a))) ∧
        /- Clause (ii): unchanged directions, both new directions and all turns/signs. -/
        ((∀ k : ZMod n, k ≠ j → edge (softInsertion P j q ε) (softOldIndex j k) = edge P k) ∧
          edge (softInsertion P j q ε) (softOldIndex j j) = ε • q ∧
          edge (softInsertion P j q ε) (softNewIndex j) = edge P j - ε • q ∧
          (∀ k : ZMod n, k ≠ j → turn (softInsertion P j q ε) (softOldIndex j k) = turn P k) ∧
          turn (softInsertion P j q ε) (softOldIndex j j) = -softAttachmentMinus P j q ∧
          turn (softInsertion P j q ε) (softNewIndex j) = -softAttachmentPlus P j q ∧
          SignType.sign (det (edge P (j - 1)) (edge (softInsertion P j q ε) (softNewIndex j))) =
            turn P j ∧
          SignType.sign (det (edge (softInsertion P j q ε) (softNewIndex j)) (edge P (j - 1))) =
            -turn P j) ∧
        /- Clause (iii): persistence is hp; limits above refer to these exact data. -/
        (∀ k l : ZMod n, ∀ hc : IsCrossing P {k, l},
          (0 < edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) ∧
            edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) < 1) ∧
          (0 < edgeParameter (softInsertion P j q ε) (softParentEdge j l) (softParentEdge j k) ∧
            edgeParameter (softInsertion P j q ε) (softParentEdge j l) (softParentEdge j k) < 1) ∧
          det (edge (softInsertion P j q ε) (softParentEdge j k))
            (edge (softInsertion P j q ε) (softParentEdge j l)) ≠ 0 ∧
          SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
            (edge (softInsertion P j q ε) (softParentEdge j l))) =
              SignType.sign (det (edge P k) (edge P l)) ∧
          crossingPoint (softInheritedCrossing hp (⟨{k, l}, hc⟩ : Crossing P)) =
            softInheritedPoint P j k l q ε ∧
          visitParameter (softInheritedVisit hp (pairVisit hc)) =
            edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) ∧
          visitParameter (softInheritedVisit hp
            (pairVisit (by simpa only [Finset.pair_comm] using hc : IsCrossing P {l, k}))) =
            edgeParameter (softInsertion P j q ε) (softParentEdge j l) (softParentEdge j k)) ∧
        (∀ v w : Visit P, v.2.val = w.2.val →
          (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
            visitParameter v < visitParameter w)) ∧
        /- Clause (iv), the printed same-sign and mixed sectors. -/
        (((softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) ∨
          softAttachmentMinus P j q ≠ softAttachmentPlus P j q) →
          Function.Bijective (softInheritedCrossing hp) ∧
          (gaussWord hn hP).map (softInheritedCrossing hp) = gaussWord (by omega : 3 ≤ n + 1) hQ) ∧
        /- Clause (iv), the loop sector, with exact uniqueness and the oriented arc. -/
        (∀ hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j,
          (∀ d : Crossing (softInsertion P j q ε),
            (∃ c : Crossing P, softInheritedCrossing hp c = d) ↔ d ≠ softNewbornCrossing hclass hloop) ∧
          (softNewbornCrossing hclass hloop).val = {softOldIndex j (j - 1), softNewIndex j} ∧
          crossingPoint (softNewbornCrossing hclass hloop) = softNewbornPoint P j q ε ∧
          visitParameter (softNewbornIncomingVisit hclass hloop) = softNewbornIncomingParameter P j q ε ∧
          visitParameter (softNewbornReturnVisit hclass hloop) = softNewbornReturnParameter P j q ε ∧
          (0 < visitParameter (softNewbornIncomingVisit hclass hloop) ∧
            visitParameter (softNewbornIncomingVisit hclass hloop) < 1) ∧
          (0 < visitParameter (softNewbornReturnVisit hclass hloop) ∧
            visitParameter (softNewbornReturnVisit hclass hloop) < 1) ∧
          traversalEvaluation (softInsertion P j q ε) (softAttachmentVertexPosition j) = P j ∧
          traversalEvaluation (softInsertion P j q ε) (softInsertedVertexPosition j) = P j + ε • q ∧
          traversalBetween
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
            (softAttachmentVertexPosition j)
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop)) ∧
          traversalBetween
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
            (softInsertedVertexPosition j)
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop)) ∧
          traversalBetween
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
            (softAttachmentVertexPosition j) (softInsertedVertexPosition j) ∧
          traversalBetween (softAttachmentVertexPosition j) (softInsertedVertexPosition j)
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop)) ∧
          (∀ w : Visit (softInsertion P j q ε),
            ¬ traversalBetween
              (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
              (visitPosition (by omega : 3 ≤ n + 1) hQ.1 w)
              (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop))) ∧
          nextGaussVisit (by omega : 3 ≤ n + 1) hQ (softNewbornIncomingVisit hclass hloop) =
            softNewbornReturnVisit hclass hloop ∧
          (gaussCycle hn hP).map (softInheritedVisit hp) =
            (gaussCycle (by omega : 3 ≤ n + 1) hQ).filter
              (fun w => decide (w.1 ≠ softNewbornCrossing hclass hloop)) ∧
          (gaussWord hn hP).map (softInheritedCrossing hp) =
            (gaussWord (by omega : 3 ≤ n + 1) hQ).filter
              (fun c => decide (c ≠ softNewbornCrossing hclass hloop))) := by
  have hnewlimits := softNewborn_limits hn hP.1 j q
  refine ⟨softInsertion_return_tendsto P j q,
    fun k l hc => softInheritedPair_tendsto hn hP.1 j k l q hc,
    hnewlimits.1, hnewlimits.2.1, hnewlimits.2.2, ?_⟩
  obtain ⟨δr, hδr, B, hregular⟩ := (soft_family_regular_data hn hP j q hq).2
  obtain ⟨δi, hδi, hinherited⟩ := soft_small_inherited_crossing_data hn hP j q hq
  obtain ⟨δg, hδg, hgauss⟩ := soft_small_gauss_geometry hn hP j q hq
  obtain ⟨δo, hδo, horders⟩ := soft_small_visit_order_data hn hP j q hq
  refine ⟨min δr (min δi (min δg δo)), lt_min hδr (lt_min hδi (lt_min hδg hδo)), B, ?_⟩
  intro ε hε hεδ
  have hεr : ε < δr := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεi : ε < δi := lt_of_lt_of_le hεδ
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεg : ε < δg := lt_of_lt_of_le hεδ
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hεo : ε < δo := lt_of_lt_of_le hεδ
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  obtain ⟨hQr, hchL, hchQ, hcIn, hcRet, havoid, hEold, hSoft, hRet,
    hTold, hTin, hTret, hsgnIn, hsgnRet⟩ := hregular ε hε hεr
  obtain ⟨hQi, hpi, hdata⟩ := hinherited ε hε hεi
  obtain ⟨hQ, hp, hclass, hnonloop, hloopdata⟩ := hgauss ε hε hεg
  obtain ⟨hQo, hpo, hco, ho⟩ := horders ε hε hεo
  refine ⟨hQ, hp, hclass, ⟨hchL, hchQ, hcIn, hcRet, havoid⟩,
    ⟨hEold, hSoft, hRet, hTold, hTin, hTret, hsgnIn, hsgnRet⟩,
    hdata, ?_, ?_, ?_⟩
  · intro v w he
    exact softInheritedVisit_parameter_lt_iff hn hP.1 hp hQ.1 ho v w he
  · intro hsector
    have hnot := (soft_nonloop_sectors_iff hn hP.1 j q hq).mp hsector
    exact ⟨⟨softInheritedCrossing_injective hp,
      softInheritedCrossing_surjective_nonloop hp hclass hnot⟩, hnonloop hnot⟩
  · intro hloop
    obtain ⟨hi, hb, _, _, _, _, hgap, hnext, hcycle, hword⟩ := hloopdata hloop
    have hc : IsCrossing (softInsertion P j q ε) {softOldIndex j (j - 1), softNewIndex j} :=
      (softNewbornCrossing hclass hloop).property
    have hd := crossing_edgeParameter_det_ne_zero (by omega : 3 ≤ n + 1) hQ.1 hc
    have hpoint := softNewborn_crossing_data P j q ε hd hc
    have hpar := softNewbornVisits_parameters hclass hloop hd
    have hv := softNewbornVisits_vertex_arc hn hQ.1 hclass hloop
    exact ⟨softInheritedCrossing_range_loop hn hp hclass hloop,
      softNewbornCrossing_support hclass hloop, hpoint.2.2, hpar.1, hpar.2,
      hi, hb, softAttachmentVertexPosition_evaluation P j q ε,
      softInsertedVertexPosition_evaluation P j q ε,
      hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hgap, hnext, hcycle, hword⟩

end
end SM
