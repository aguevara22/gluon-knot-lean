import SM.CuspRelabel

namespace SM

variable {n : ℕ} [NeZero n]

def TwoStepAdjacent (hn : 3 ≤ n) (P : GenericTuple n) (f : ZMod n)
    (h : IsCrossing P.val {f, f + 2}) : Prop :=
  GaussVisitsAdjacent hn P.property (twoStepFirstVisit h) (twoStepLastVisit h)

theorem twoStep_adjacent_shift (hn : 3 ≤ n) (r : ZMod n)
    {P : LabelledTuple n} (hP : Generic P) {f : ZMod n}
    (h : IsCrossing P {f, f + 2})
    (h' : IsCrossing (shift r P) {f - r, (f - r) + 2}) :
    GaussVisitsAdjacent hn ((generic_shift r P).mpr hP)
      (twoStepFirstVisit h') (twoStepLastVisit h') ↔
    GaussVisitsAdjacent hn hP (twoStepFirstVisit h) (twoStepLastVisit h) := by
  have hh := gaussVisitsAdjacent_shift hn hP r (twoStepFirstVisit h) (twoStepLastVisit h)
  rw [visitShift_twoStepFirst r h h', visitShift_twoStepLast r h h'] at hh
  exact hh

namespace WallGerm

variable (g : WallGerm n)

theorem cuspEmptyAt_relabel_of_cusp (r : ZMod n) {j : ZMod n} (h : g.CuspAt j) :
    (g.relabel r).CuspEmptyAt (j - r) ↔ g.CuspEmptyAt j := by
  obtain ⟨b, hc, _⟩ := g.cusp_case_existsUnique h
  have h' := (g.cuspAt_relabel r j).mpr h
  have hc' := (g.cuspCase_relabel r j b).mpr hc
  rw [(g.relabel r).cuspEmptyAt_iff_at h' hc' g.sideBase,
    g.cuspEmptyAt_iff_at h hc g.sideBase]
  change TwoStepAdjacent _ ((g.relabel r).sideTuple
      ((g.relabel r).cuspLoopSide b (j - r)) g.sideBase) (cuspFirst b (j - r)) _ ↔
    TwoStepAdjacent _ (g.sideTuple (g.cuspLoopSide b j) g.sideBase) (cuspFirst b j) _
  simp only [g.cuspLoopSide_relabel, cuspFirst_sub, g.sideTuple_relabel]
  apply twoStep_adjacent_shift (by have hn := h.1; omega) r
    (g.sideTuple (g.cuspLoopSide b j) g.sideBase).property
    (g.cusp_loop_crossing h hc g.sideBase)

theorem cuspEmptyAt_relabel (r j : ZMod n) :
    (g.relabel r).CuspEmptyAt (j - r) ↔ g.CuspEmptyAt j := by
  by_cases h : g.CuspAt j
  · exact g.cuspEmptyAt_relabel_of_cusp r h
  · constructor
    · rintro ⟨h', _⟩
      exact (h ((g.cuspAt_relabel r j).mp h')).elim
    · rintro ⟨h', _⟩
      exact (h h').elim

end WallGerm
end SM
