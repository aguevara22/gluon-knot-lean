namespace SM

open Set Filter Topology

variable {n : ℕ}

/-- A generic tuple can be chosen in the actual visible chamber of any weak
representative while preserving every initially nonzero ordered chirotope.
No genericity or restriction on the number of zero triples is imposed on P. -/
theorem visible_chamber_generic_preserving_nonzero_chi
    (hn : 3 ≤ n) (P : WeakTuple n) :
    ∃ Q : GenericTuple n,
      (⟨Q.val, generic_implies_weak hn Q.property⟩ : WeakTuple n) ∈
        labelledVisibleChamber P ∧
      ∀ i j k : ZMod n, chi P.val i j k ≠ 0 →
        chi Q.val i j k = chi P.val i j k := by
  haveI : NeZero n := ⟨by omega⟩
  have hPmem : P.val ∈ Subtype.val '' labelledVisibleChamber P :=
    ⟨P, mem_connectedComponent, rfl⟩
  have hch : Subtype.val '' labelledVisibleChamber P ∈ 𝓝 P.val :=
    (weak_visible_components P).1.mem_nhds hPmem
  have hboth :
      {Q : LabelledTuple n | Q ∈ Subtype.val '' labelledVisibleChamber P ∧
        ∀ i j k : ZMod n, chi P.val i j k ≠ 0 →
          chi Q i j k = chi P.val i j k} ∈ 𝓝 P.val :=
    hch.and (finite_nonzero_chi_persists (P := P.val))
  obtain ⟨U, hsub, hU, hPU⟩ := mem_nhds_iff.mp hboth
  obtain ⟨q, hqU, hqG⟩ := generic_in_nonempty_open hn U hU ⟨P.val, hPU⟩
  have hdata := hsub hqU
  obtain ⟨W, hW, hWq⟩ := hdata.1
  have hW_eq : W = (⟨q, generic_implies_weak hn hqG⟩ : WeakTuple n) :=
    Subtype.ext hWq
  refine ⟨⟨q, hqG⟩, ?_, hdata.2⟩
  exact hW_eq ▸ hW

end SM
