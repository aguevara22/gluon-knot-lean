import SM.CuspSideCrossings
import SM.GermApproach
import SM.PrincipalAngleBranchLimit

/-! The actual principal-turn limits on either connected cusp side.
Only the singular corner has different one-sided limits. -/

namespace SM.WallGerm

open Filter Topology

variable {n : ℕ} [NeZero n] (g : WallGerm n)

theorem side_rotation_constant (hn : 3 ≤ n) (b : Bool) (s t : g.SideParameter) :
    rotationNumber (g.sideTuple b s).val = rotationNumber (g.sideTuple b t).val :=
  rotationNumber_family_constant (continuous_subtype_val.comp (g.continuous_sideTuple b))
    (fun u => generic_regular hn (g.sideTuple b u).property) s t

theorem cusp_other_turn_limit {j : ZMod n} (h : g.CuspAt j) (side : Bool)
    {i : ZMod n} (hi : i ≠ j) :
    Tendsto (fun m => principalTurn (g.sideTuple side (g.sideApproach m)).val i) atTop
      (𝓝 (principalTurn g.center i)) := by
  have he (k : ZMod n) : Continuous (fun P : LabelledTuple n => edge P k) :=
    (continuous_apply (k + 1)).sub (continuous_apply k)
  exact (continuousAt_principalAngle (he (i - 1)).continuousAt (he i).continuousAt
    (cusp_other_turn_regular h.1 h.2.1 hi)).tendsto.comp (g.sideTuple_approach_tendsto side)

theorem cusp_singular_turn_limit {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (side : Bool) (s : g.SideParameter) :
    Tendsto (fun m => principalTurn (g.sideTuple side (g.sideApproach m)).val j) atTop
      (𝓝 ((turn (g.sideTuple side s).val j : ℝ) * Real.pi)) := by
  haveI : Fact (1 < n) := ⟨by have hn := h.1; omega⟩
  have hr := cusp_rotor_negative_real h.1 h.2.1 hc
  have ht : turn (g.sideTuple side s).val j ≠ 0 := by
    rw [turn_det]
    exact sign_ne_zero.mpr (g1_turn_nonzero (by have hn := h.1; omega)
      (g.sideTuple side s).property.1 j)
  apply tendsto_principalAngle_at_antiparallel (g.sideEdge_approach_tendsto side (j - 1))
    (g.sideEdge_approach_tendsto side j) hr.1 hr.2 ht
  intro m
  rw [← turn_det]
  exact g.side_turn_constant side (g.sideApproach m) s j

theorem cusp_principalTurnSum_limit {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) (side : Bool) (s : g.SideParameter) :
    Tendsto (fun m => ∑ i : ZMod n, principalTurn (g.sideTuple side (g.sideApproach m)).val i)
      atTop (𝓝 ((∑ i ∈ Finset.univ.erase j, principalTurn g.center i) +
        (turn (g.sideTuple side s).val j : ℝ) * Real.pi)) := by
  classical
  have hsum := tendsto_finsetSum (Finset.univ.erase j)
    (fun i hi => g.cusp_other_turn_limit h side (Finset.mem_erase.mp hi).1)
  have ht := hsum.add (g.cusp_singular_turn_limit h hc side s)
  simpa only [Finset.sum_erase_add _ _ (Finset.mem_univ j)] using ht

end SM.WallGerm
