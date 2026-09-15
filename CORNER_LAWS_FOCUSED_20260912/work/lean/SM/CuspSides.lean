import SM.CuspArcData
import SM.CuspRotation

/-! All four clauses of source lem:cusp-sides. The case is derived, the
determinant has one common local radius, and all side comparisons permit
independent parameters. The general cusp is allowed to be threaded. -/

namespace SM

variable {n : ℕ} [NeZero n]

structure CuspSidesData (g : WallGerm n) (j : ZMod n) (h : g.CuspAt j)
    (b : Bool) (hc : CuspCase g.center j b) : Prop where
  case_unique : ∀ b' : Bool, CuspCase g.center j b' → b' = b
  remote_pair : remote (cuspFirst b j) (cuspLast b j)
  delta_neighborhood : ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧
    ∀ t : g.Parameter, |t.val| < δ → cuspDelta (g.curve t) b j ≠ 0 ∧
      SignType.sign (cuspDelta (g.curve t) b j) = SignType.sign (cuspDelta g.center b j)
  side_laws : ∀ side : Bool, ∀ s : g.SideParameter,
    (IsCrossing (g.sideTuple side s).val {cuspFirst b j, cuspLast b j} ↔ side = g.cuspLoopSide b j) ∧
    (IsCrossing (g.sideTuple side s).val {cuspFirst b j, cuspLast b j} ↔
      turn (g.sideTuple side s).val j = -SignType.sign (cuspDelta g.center b j)) ∧
    ((¬ IsCrossing (g.sideTuple side s).val {cuspFirst b j, cuspLast b j}) ↔
      turn (g.sideTuple side s).val j = SignType.sign (cuspDelta g.center b j))
  other_crossings : ∀ a c : Bool, ∀ s t : g.SideParameter,
    ∀ pair : Finset (ZMod n), pair ≠ {cuspFirst b j, cuspLast b j} →
      (IsCrossing (g.sideTuple a s).val pair ↔ IsCrossing (g.sideTuple c t).val pair)
  needle_turns : ∀ s t : g.SideParameter,
    (turn (g.sideTuple (g.cuspLoopSide b j) s).val (cuspCorner₁ b j) =
        turn (g.sideTuple (g.cuspLoopSide b j) s).val j ∧
      turn (g.sideTuple (g.cuspLoopSide b j) s).val (cuspCorner₂ b j) =
        turn (g.sideTuple (g.cuspLoopSide b j) s).val j) ∧
    turn (g.sideTuple (!(g.cuspLoopSide b j)) t).val (cuspCorner₁ b j) =
      -turn (g.sideTuple (!(g.cuspLoopSide b j)) t).val (cuspCorner₂ b j)
  loop_arc : ∀ s : g.SideParameter, CuspArcData (by have hn := h.1; omega)
    (g.sideTuple (g.cuspLoopSide b j) s).property (g.cusp_loop_crossing h hc s)
  empty_middle_edge : ∀ s : g.SideParameter,
    GaussVisitsAdjacent (by have hn := h.1; omega)
      (g.sideTuple (g.cuspLoopSide b j) s).property
      (twoStepFirstVisit (g.cusp_loop_crossing h hc s))
      (twoStepLastVisit (g.cusp_loop_crossing h hc s)) →
    ∀ side : Bool, ∀ t : g.SideParameter, ∀ c : Crossing (g.sideTuple side t).val,
      cuspCorner₁ b j ∉ c.val
  rotation_jump : ∀ s t : g.SideParameter,
    rotationNumber (g.sideTuple (g.cuspLoopSide b j) s).val -
      rotationNumber (g.sideTuple (!(g.cuspLoopSide b j)) t).val =
        (turn (g.sideTuple (g.cuspLoopSide b j) s).val j : ℝ) ∧
    (turn (g.sideTuple (g.cuspLoopSide b j) s).val j = -1 ∨
      turn (g.sideTuple (g.cuspLoopSide b j) s).val j = 1)

theorem cusp_sides (g : WallGerm n) {j : ZMod n} (h : g.CuspAt j) :
    ∃ b : Bool, ∃ hc : CuspCase g.center j b, CuspSidesData g j h b hc := by
  obtain ⟨b, hc, hu⟩ := g.cusp_case_existsUnique h
  refine ⟨b, hc, ?_⟩
  refine {
    case_unique := hu
    remote_pair := cusp_newborn_remote h.1 b j
    delta_neighborhood := ?_
    side_laws := ?_
    other_crossings := g.cusp_other_crossings_sides h hc
    needle_turns := g.cusp_loop_needle_patterns h hc
    loop_arc := fun s => cusp_arc_data (by have hn := h.1; omega)
      (g.sideTuple (g.cuspLoopSide b j) s).property (g.cusp_loop_crossing h hc s)
    empty_middle_edge := g.cusp_empty_middle_edge h hc
    rotation_jump := g.cusp_rotation_jump h hc }
  · obtain ⟨δ, hδ, hδr, hd, _⟩ := g.cusp_local_geometry h hc
    exact ⟨δ, hδ, hδr, hd⟩
  · intro side s
    exact ⟨g.cusp_side_crossing_iff_loop h hc side s,
      g.cusp_side_crossing_iff_turn h hc side s, g.cusp_side_no_crossing_iff_turn h hc side s⟩

end SM
