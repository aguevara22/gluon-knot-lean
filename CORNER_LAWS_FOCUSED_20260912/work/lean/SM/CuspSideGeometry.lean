import SM.CuspSideCrossings

/-! All crossing supports and needle signs on independently chosen points
of the actual loop and no-loop sides. The geometric source centre stays singular. -/

namespace SM.WallGerm

variable {n : ℕ} [NeZero n] (g : WallGerm n)

theorem cusp_other_crossings_sides {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (a c : Bool) (s t : g.SideParameter)
    (pair : Finset (ZMod n)) (hne : pair ≠ {cuspFirst b j, cuspLast b j}) :
    IsCrossing (g.sideTuple a s).val pair ↔ IsCrossing (g.sideTuple c t).val pair := by
  obtain ⟨δ, hδ, hδr, hlocal⟩ := g.cusp_local_control h hc
  let t₀ : g.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have ht₀ : t₀.val < δ := by dsimp [t₀]; linarith
  have hl (side : Bool) : CuspLocalControl g.center (g.sideTuple side t₀).val b j := by
    apply hlocal (g.sideTime side t₀)
    have habs : |(g.sideTime side t₀).val| = t₀.val := by
      cases side <;> simp [sideTime, abs_of_pos t₀.property.1]
    rw [habs]
    exact ht₀
  have hh := cusp_other_crossings_equal h.1 h.2.1 (hl a).2.2.1 (hl c).2.2.1
    (g.sideTuple a t₀).property.1 (g.sideTuple c t₀).property.1 pair hne
  exact (generic_family_crossing_constant (by have hn := h.1; omega)
    (g.continuous_sideTuple a) s t₀ pair).trans
    (hh.trans (generic_family_crossing_constant (by have hn := h.1; omega)
      (g.continuous_sideTuple c) t₀ t pair))

theorem cusp_side_needle_patterns {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (side : Bool) (s : g.SideParameter) :
    (IsCrossing (g.sideTuple side s).val {cuspFirst b j, cuspLast b j} →
      turn (g.sideTuple side s).val (cuspCorner₁ b j) = turn (g.sideTuple side s).val j ∧
      turn (g.sideTuple side s).val (cuspCorner₂ b j) = turn (g.sideTuple side s).val j) ∧
    (¬ IsCrossing (g.sideTuple side s).val {cuspFirst b j, cuspLast b j} →
      turn (g.sideTuple side s).val (cuspCorner₁ b j) = -turn (g.sideTuple side s).val (cuspCorner₂ b j)) := by
  obtain ⟨δ, hδ, hδr, hlocal⟩ := g.cusp_local_control h hc
  let t₀ : g.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have ht₀ : t₀.val < δ := by dsimp [t₀]; linarith
  have habs : |(g.sideTime side t₀).val| = t₀.val := by
    cases side <;> simp [sideTime, abs_of_pos t₀.property.1]
  have hl := hlocal (g.sideTime side t₀) (by rw [habs]; exact ht₀)
  rw [generic_family_crossing_constant (by have hn := h.1; omega)
      (g.continuous_sideTuple side) s t₀,
    g.side_turn_constant side s t₀ (cuspCorner₁ b j),
    g.side_turn_constant side s t₀ (cuspCorner₂ b j), g.side_turn_constant side s t₀ j]
  exact (hl.2.2.2 (g.sideTuple side t₀).property.1).2

theorem cusp_loop_needle_patterns {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (s t : g.SideParameter) :
    (turn (g.sideTuple (g.cuspLoopSide b j) s).val (cuspCorner₁ b j) =
        turn (g.sideTuple (g.cuspLoopSide b j) s).val j ∧
      turn (g.sideTuple (g.cuspLoopSide b j) s).val (cuspCorner₂ b j) =
        turn (g.sideTuple (g.cuspLoopSide b j) s).val j) ∧
    turn (g.sideTuple (!(g.cuspLoopSide b j)) t).val (cuspCorner₁ b j) =
      -turn (g.sideTuple (!(g.cuspLoopSide b j)) t).val (cuspCorner₂ b j) :=
  ⟨(g.cusp_side_needle_patterns h hc _ s).1 (g.cusp_loop_crossing h hc s),
    (g.cusp_side_needle_patterns h hc _ t).2 (g.cusp_no_loop_crossing h hc t)⟩

end SM.WallGerm
