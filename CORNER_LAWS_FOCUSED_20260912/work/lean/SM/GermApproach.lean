import SM.GermDefinition
import Mathlib.Analysis.SpecificLimits.Basic

/-! Explicit points approaching the centre through either genuine half interval.
The construction needs only the positive radius and continuity of the germ. -/

namespace SM.WallGerm

open Filter Topology

variable {n : ℕ} (g : WallGerm n)

noncomputable def sideApproach (m : ℕ) : g.SideParameter :=
  ⟨g.radius / ((m : ℝ) + 2), by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    constructor
    · exact div_pos g.radius_pos (by linarith)
    · apply (div_lt_iff₀ (by linarith : 0 < (m : ℝ) + 2)).mpr
      nlinarith [g.radius_pos]⟩

theorem sideApproach_tendsto :
    Tendsto (fun m => (g.sideApproach m).val) atTop (𝓝 0) := by
  have ht := (tendsto_add_atTop_iff_nat 2).2
    (tendsto_const_div_atTop_nhds_zero_nat g.radius)
  simpa only [sideApproach, Nat.cast_add, Nat.cast_ofNat] using ht

theorem sideTime_approach_tendsto (b : Bool) :
    Tendsto (fun m => g.sideTime b (g.sideApproach m)) atTop (𝓝 g.zeroParameter) := by
  rw [tendsto_subtype_rng]
  cases b
  · simpa only [sideTime, Bool.false_eq_true, ↓reduceIte, zeroParameter, neg_zero]
      using g.sideApproach_tendsto.neg
  · exact g.sideApproach_tendsto

theorem sideTuple_approach_tendsto (b : Bool) :
    Tendsto (fun m => (g.sideTuple b (g.sideApproach m)).val) atTop (𝓝 g.center) :=
  g.continuous_curve.continuousAt.tendsto.comp (g.sideTime_approach_tendsto b)

theorem sideEdge_approach_tendsto (b : Bool) (i : ZMod n) :
    Tendsto (fun m => edge (g.sideTuple b (g.sideApproach m)).val i) atTop
      (𝓝 (edge g.center i)) :=
  ((continuous_apply (i + 1)).tendsto g.center |>.comp (g.sideTuple_approach_tendsto b)).sub
    ((continuous_apply i).tendsto g.center |>.comp (g.sideTuple_approach_tendsto b))

end SM.WallGerm
