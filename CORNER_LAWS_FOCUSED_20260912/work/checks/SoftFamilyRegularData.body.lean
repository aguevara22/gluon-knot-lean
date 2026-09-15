namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- Clauses (i) and (ii) of the source soft-family lemma share one positive
interval. The chamber base is fixed before the radius is shrunk; its positive
parameter is never replaced by the degenerate parameter zero. -/
theorem soft_family_regular_data (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    Tendsto (fun ε : ℝ => edge (softInsertion P j q ε) (softNewIndex j))
      (𝓝 (0 : ℝ)) (𝓝 (edge P j)) ∧
    ∃ δ > 0, ∃ B : GenericTuple (n + 1),
      ∀ ε : ℝ, 0 < ε → ε < δ → ∃ hQ : Generic (softInsertion P j q ε),
        (⟨softInsertion P j q ε, hQ⟩ : GenericTuple (n + 1)) ∈ labelledChamber B ∧
        polygonProjection (⟨softInsertion P j q ε, hQ⟩ : GenericTuple (n + 1)) ∈
          chamber (polygonProjection B) ∧
        edgeSegment (softInsertion P j q ε) (softOldIndex j j) ∩
          edgeSegment (softInsertion P j q ε) (softOldIndex j (j - 1)) = {P j} ∧
        edgeSegment (softInsertion P j q ε) (softOldIndex j j) ∩
          edgeSegment (softInsertion P j q ε) (softNewIndex j) = {P j + ε • q} ∧
        (∀ a : ZMod (n + 1), a ≠ softOldIndex j j → a ≠ softOldIndex j (j - 1) →
          a ≠ softNewIndex j →
          Disjoint (edgeSegment (softInsertion P j q ε) (softOldIndex j j))
            (edgeSegment (softInsertion P j q ε) a)) ∧
        (∀ k : ZMod n, k ≠ j → edge (softInsertion P j q ε) (softOldIndex j k) = edge P k) ∧
        edge (softInsertion P j q ε) (softOldIndex j j) = ε • q ∧
        edge (softInsertion P j q ε) (softNewIndex j) = edge P j - ε • q ∧
        (∀ k : ZMod n, k ≠ j → turn (softInsertion P j q ε) (softOldIndex j k) = turn P k) ∧
        turn (softInsertion P j q ε) (softOldIndex j j) = -softAttachmentMinus P j q ∧
        turn (softInsertion P j q ε) (softNewIndex j) = -softAttachmentPlus P j q ∧
        SignType.sign (det (edge P (j - 1)) (edge (softInsertion P j q ε) (softNewIndex j))) =
          turn P j ∧
        SignType.sign (det (edge (softInsertion P j q ε) (softNewIndex j)) (edge P (j - 1))) =
          -turn P j := by
  refine ⟨softInsertion_return_tendsto P j q, ?_⟩
  obtain ⟨δc, hδc, hmid, hchamber⟩ := softInsertion_one_chamber hn hP j q hq
  obtain ⟨δe, hδe, hcontacts⟩ := softEdge_only_incident_contacts hn hP.1 j q hq
  obtain ⟨δt, hδt, hturns⟩ := softInsertion_small_turns hn hP.1 j q
  refine ⟨min δc (min δe δt), lt_min hδc (lt_min hδe hδt),
    ⟨softInsertion P j q (δc / 2), hmid⟩, ?_⟩
  intro ε hε hεδ
  have hεc : ε < δc := lt_of_lt_of_le hεδ (min_le_left δc (min δe δt))
  have hεe : ε < δe := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δc (min δe δt)) (min_le_left δe δt))
  have hεt : ε < δt := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δc (min δe δt)) (min_le_right δe δt))
  obtain ⟨hQ, hc, hp⟩ := hchamber ε hε hεc
  have he := hcontacts ε hε hεe
  have ht := hturns ε hε hεt
  exact ⟨hQ, hc, hp, he.1, he.2.1, he.2.2,
    fun k hk => edge_softInsertion_old P j k q ε hk,
    edge_softInsertion_soft P j q ε, edge_softInsertion_return P j q ε,
    ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩

end
end SM
