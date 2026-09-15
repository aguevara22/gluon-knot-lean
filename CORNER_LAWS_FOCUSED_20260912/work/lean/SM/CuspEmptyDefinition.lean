import SM.GaussAdjacencyTransport
import SM.CuspEmptyEdge

/-! The source empty-cusp predicate uses the actual two newborn visits.
Transport proves independence of the loop-side point and the unique central
case, rather than assuming this for the chosen base parameter. -/

namespace SM

variable {n : ℕ} [NeZero n] {P Q : LabelledTuple n} {f : ZMod n}

theorem visitTransport_twoStepFirst
    (h : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hP : IsCrossing P {f, f + 2}) (hQ : IsCrossing Q {f, f + 2}) :
    visitTransport h (twoStepFirstVisit hP) = twoStepFirstVisit hQ := visit_ext rfl rfl

theorem visitTransport_twoStepLast
    (h : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hP : IsCrossing P {f, f + 2}) (hQ : IsCrossing Q {f, f + 2}) :
    visitTransport h (twoStepLastVisit hP) = twoStepLastVisit hQ := visit_ext rfl rfl

namespace WallGerm

variable (g : WallGerm n)

theorem cusp_empty_parameter_iff {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (s t : g.SideParameter) :
    GaussVisitsAdjacent (by have hn := h.1; omega)
      (g.sideTuple (g.cuspLoopSide b j) s).property
      (twoStepFirstVisit (g.cusp_loop_crossing h hc s))
      (twoStepLastVisit (g.cusp_loop_crossing h hc s)) ↔
    GaussVisitsAdjacent (by have hn := h.1; omega)
      (g.sideTuple (g.cuspLoopSide b j) t).property
      (twoStepFirstVisit (g.cusp_loop_crossing h hc t))
      (twoStepLastVisit (g.cusp_loop_crossing h hc t)) := by
  have hh := generic_family_gaussVisitsAdjacent (by have hn := h.1; omega)
    (g.continuous_sideTuple (g.cuspLoopSide b j)) s t
    (twoStepFirstVisit (g.cusp_loop_crossing h hc s))
    (twoStepLastVisit (g.cusp_loop_crossing h hc s))
  have hfirst : visitTransport (generic_family_crossing_constant
      (by have hn := h.1; omega) (g.continuous_sideTuple (g.cuspLoopSide b j)) s t)
      (twoStepFirstVisit (g.cusp_loop_crossing h hc s)) =
      twoStepFirstVisit (g.cusp_loop_crossing h hc t) := visit_ext rfl rfl
  have hlast : visitTransport (generic_family_crossing_constant
      (by have hn := h.1; omega) (g.continuous_sideTuple (g.cuspLoopSide b j)) s t)
      (twoStepLastVisit (g.cusp_loop_crossing h hc s)) =
      twoStepLastVisit (g.cusp_loop_crossing h hc t) := visit_ext rfl rfl
  rw [hfirst, hlast] at hh
  exact hh.symm

def CuspEmptyAt (j : ZMod n) : Prop :=
  ∃ h : g.CuspAt j, ∃ b : Bool, ∃ hc : CuspCase g.center j b,
    GaussVisitsAdjacent (by have hn := h.1; omega)
      (g.sideTuple (g.cuspLoopSide b j) g.sideBase).property
      (twoStepFirstVisit (g.cusp_loop_crossing h hc g.sideBase))
      (twoStepLastVisit (g.cusp_loop_crossing h hc g.sideBase))

theorem cuspEmptyAt_iff_at {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (s : g.SideParameter) :
    g.CuspEmptyAt j ↔
    GaussVisitsAdjacent (by have hn := h.1; omega)
      (g.sideTuple (g.cuspLoopSide b j) s).property
      (twoStepFirstVisit (g.cusp_loop_crossing h hc s))
      (twoStepLastVisit (g.cusp_loop_crossing h hc s)) := by
  constructor
  · rintro ⟨h', b', hc', ha⟩
    obtain ⟨c, _, huniq⟩ := g.cusp_case_existsUnique h
    have hb : b' = b := (huniq b' hc').trans (huniq b hc).symm
    subst b'
    exact (g.cusp_empty_parameter_iff h hc g.sideBase s).mp ha
  · intro ha
    exact ⟨h, b, hc, (g.cusp_empty_parameter_iff h hc g.sideBase s).mpr ha⟩

theorem cuspEmptyAt_middle_edge {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (he : g.CuspEmptyAt j) :
    ∀ side : Bool, ∀ t : g.SideParameter, ∀ c : Crossing (g.sideTuple side t).val,
      cuspCorner₁ b j ∉ c.val :=
  g.cusp_empty_middle_edge h hc g.sideBase ((g.cuspEmptyAt_iff_at h hc g.sideBase).mp he)

end WallGerm
end SM
