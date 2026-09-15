import SM.G1CrossingStability
import SM.GermDefinition
import SM.GermNeighborhood

/-! A G1 centre fixes every actual crossing support on each entire connected
generic side. The centre need not satisfy G2. -/

namespace SM.WallGerm

variable {n : ℕ} [NeZero n]

theorem g1_center_side_crossings (hn : 3 ≤ n) (g : WallGerm n) (hG1 : G1 g.center) :
    ∀ b : Bool, ∀ t : g.SideParameter, ∀ s : Finset (ZMod n),
      IsCrossing (g.sideTuple b t).val s ↔ IsCrossing g.center s := by
  have hnear := g.continuous_curve.continuousAt.eventually (g1_crossings_locally_constant hn hG1)
  obtain ⟨δ, hδ, hδr, hlocal⟩ := (g.eventually_center_iff_radius _).mp hnear
  let t₀ : g.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have ht₀ : t₀.val < δ := by dsimp [t₀]; linarith
  intro b t s
  have habs : |(g.sideTime b t₀).val| = t₀.val := by
    cases b <;> simp [sideTime, abs_of_pos t₀.property.1]
  have hc := (hlocal (g.sideTime b t₀) (by rw [habs]; exact ht₀)).2 s
  exact (generic_family_crossing_constant hn (g.continuous_sideTuple b) t t₀ s).trans hc

theorem g1_center_side_parameter_order (hn : 3 ≤ n) (g : WallGerm n) (hG1 : G1 g.center)
    (b : Bool) (i j k : ZMod n)
    (hij : IsCrossing g.center {i, j}) (hik : IsCrossing g.center {i, k})
    (s t : g.SideParameter) :
    (edgeParameter (g.sideTuple b s).val i j < edgeParameter (g.sideTuple b s).val i k ↔
      edgeParameter (g.sideTuple b t).val i j < edgeParameter (g.sideTuple b t).val i k) := by
  have hc := g.g1_center_side_crossings hn hG1 b g.sideBase
  exact generic_family_crossingOrder_constant hn (g.continuous_sideTuple b) g.sideBase i j k
    ((hc _).mpr hij) ((hc _).mpr hik) s t

end SM.WallGerm
