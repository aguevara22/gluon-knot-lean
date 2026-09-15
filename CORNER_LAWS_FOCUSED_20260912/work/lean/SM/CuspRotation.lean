import SM.CuspTurnLimits

/-! The signed cusp rotation law for arbitrary independent side parameters.
Integrality and connectedness give side constancy; actual principal-angle
limits give the jump. No rotation value of the singular centre is assigned. -/

namespace SM.WallGerm

open Filter Topology

variable {n : ℕ} [NeZero n] (g : WallGerm n)

theorem cusp_rotation_side_formula {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (side : Bool) (s : g.SideParameter) :
    rotationNumber (g.sideTuple side s).val =
      ((∑ i ∈ Finset.univ.erase j, principalTurn g.center i) +
        (turn (g.sideTuple side s).val j : ℝ) * Real.pi) / (2 * Real.pi) := by
  have hlim := (g.cusp_principalTurnSum_limit h hc side s).div_const (2 * Real.pi)
  have hconst : Tendsto (fun _ : ℕ => rotationNumber (g.sideTuple side s).val) atTop
      (𝓝 (((∑ i ∈ Finset.univ.erase j, principalTurn g.center i) +
        (turn (g.sideTuple side s).val j : ℝ) * Real.pi) / (2 * Real.pi))) := by
    apply hlim.congr'
    exact Filter.Eventually.of_forall (fun m => g.side_rotation_constant
      (by have hn := h.1; omega) side (g.sideApproach m) s)
  exact tendsto_nhds_unique tendsto_const_nhds hconst

theorem cusp_rotation_jump {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (s t : g.SideParameter) :
    rotationNumber (g.sideTuple (g.cuspLoopSide b j) s).val -
      rotationNumber (g.sideTuple (!(g.cuspLoopSide b j)) t).val =
        (turn (g.sideTuple (g.cuspLoopSide b j) s).val j : ℝ) ∧
    (turn (g.sideTuple (g.cuspLoopSide b j) s).val j = -1 ∨
      turn (g.sideTuple (g.cuspLoopSide b j) s).val j = 1) := by
  have ht := g.cusp_loop_turns h hc s t
  refine ⟨?_, ht.2.2.2⟩
  have hcast : (turn (g.sideTuple (g.cuspLoopSide b j) s).val j : ℝ) =
      -(turn (g.sideTuple (!(g.cuspLoopSide b j)) t).val j : ℝ) := by
    rw [ht.2.2.1, SignType.coe_neg]
  rw [g.cusp_rotation_side_formula h hc, g.cusp_rotation_side_formula h hc]
  rw [← sub_div, div_eq_iff (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))]
  rw [hcast]
  ring

end SM.WallGerm
