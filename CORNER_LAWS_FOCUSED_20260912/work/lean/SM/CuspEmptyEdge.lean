import SM.CuspSideGeometry
import SM.ThreeEdgeEmptyArc
import SM.ThreeEdgeClosedArc

/-! The source empty-cusp consequence for the actual newborn visits:
cyclic adjacency makes the middle edge crossing-free on both entire sides. -/

namespace SM.WallGerm

variable {n : ℕ} [NeZero n] (g : WallGerm n)

theorem cusp_empty_middle_edge {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (s : g.SideParameter)
    (ha : GaussVisitsAdjacent (by have hn := h.1; omega)
      (g.sideTuple (g.cuspLoopSide b j) s).property
      (twoStepFirstVisit (g.cusp_loop_crossing h hc s))
      (twoStepLastVisit (g.cusp_loop_crossing h hc s))) :
    ∀ side : Bool, ∀ t : g.SideParameter, ∀ c : Crossing (g.sideTuple side t).val,
      cuspCorner₁ b j ∉ c.val := by
  haveI : Fact (1 < n) := ⟨by have hn := h.1; omega⟩
  have hn : 3 ≤ n := by have hn := h.1; omega
  have hempty := twoStep_middle_edge_no_crossing hn
    (g.sideTuple (g.cuspLoopSide b j) s).property (g.cusp_loop_crossing h hc s) ha
  intro side t c hinc
  have hnot : cuspCorner₁ b j ∉ ({cuspFirst b j, cuspLast b j} : Finset (ZMod n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, cuspCorner₁, cuspLast]
    rintro (he | he)
    · exact next_ne_self (cuspFirst b j) he
    · have hz : (1 : ZMod n) = 0 := by linear_combination -he
      exact one_ne_zero hz
  have hneq : c.val ≠ {cuspFirst b j, cuspLast b j} := fun he => hnot (he ▸ hinc)
  have hx : IsCrossing (g.sideTuple (g.cuspLoopSide b j) s).val c.val :=
    (g.cusp_other_crossings_sides h hc side (g.cuspLoopSide b j) t s c.val hneq).mp c.property
  exact hempty ⟨c.val, hx⟩ hinc

theorem cusp_loop_arc_vertices {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (s : g.SideParameter) (i : ZMod n) :
    twoStepClosedArc (by have hn := h.1; omega)
      (g.sideTuple (g.cuspLoopSide b j) s).property.1 (g.cusp_loop_crossing h hc s) (traversalVertex i) ↔
      i = cuspCorner₁ b j ∨ i = cuspCorner₂ b j := by
  exact twoStepClosedArc_vertex_iff (by have hn := h.1; omega)
    (g.sideTuple (g.cuspLoopSide b j) s).property.1 (g.cusp_loop_crossing h hc s) i

end SM.WallGerm
