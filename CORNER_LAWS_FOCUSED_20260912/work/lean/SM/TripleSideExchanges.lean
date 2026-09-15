import SM.TripleExchanges
import SM.GermG1Crossings

/-! The three order reversals are fixed on both connected generic sides,
with independently chosen positive and negative evaluation parameters. -/

namespace SM.WallGerm

variable {n : ℕ} [NeZero n]

theorem g1_parameter_signChange_sides (hn : 3 ≤ n) (g : WallGerm n)
    (hG1 : G1 g.center) (i j k : ZMod n)
    (hij : IsCrossing g.center {i, j}) (hik : IsCrossing g.center {i, k})
    (hsc : g.SignChanges (fun P => edgeParameter P i j - edgeParameter P i k))
    (s t : g.SideParameter) :
    (edgeParameter (g.sideTuple true s).val i j < edgeParameter (g.sideTuple true s).val i k ↔
      edgeParameter (g.sideTuple false t).val i k < edgeParameter (g.sideTuple false t).val i j) ∧
    (edgeParameter (g.sideTuple true s).val i k < edgeParameter (g.sideTuple true s).val i j ↔
      edgeParameter (g.sideTuple false t).val i j < edgeParameter (g.sideTuple false t).val i k) := by
  obtain ⟨δ, hδ, hδr, hlocal⟩ := hsc
  let t₀ : g.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have ht₀ : t₀.val < δ := by dsimp [t₀]; linarith
  have hswap := opposite_difference_orders (hlocal t₀ ht₀)
  exact ⟨(g.g1_center_side_parameter_order hn hG1 true i j k hij hik s t₀).trans
      (hswap.1.trans (g.g1_center_side_parameter_order hn hG1 false i k j hik hij t₀ t)),
    (g.g1_center_side_parameter_order hn hG1 true i k j hik hij s t₀).trans
      (hswap.2.trans (g.g1_center_side_parameter_order hn hG1 false i j k hij hik t₀ t))⟩

theorem triple_order_exchanges (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) (s t : g.SideParameter) :
    TriangleOrderExchanges (g.sideTuple true s).val (g.sideTuple false t).val e f k := by
  have hG1 : G1 g.center := (g.pointZeros_empty_iff).mp h.1
  have hc := uniqueTriple_crossings h.2.1
  exact ⟨g.g1_parameter_signChange_sides hn hG1 e f k hc.1 hc.2.1 h.2.2.1 s t,
    g.g1_parameter_signChange_sides hn hG1 f e k (isCrossing_pair_reverse hc.1) hc.2.2
      h.2.2.2.1 s t,
    g.g1_parameter_signChange_sides hn hG1 k e f (isCrossing_pair_reverse hc.2.1)
      (isCrossing_pair_reverse hc.2.2) h.2.2.2.2 s t⟩

theorem triple_other_orders_sides (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) (b : Bool) (s : g.SideParameter) :
    TripleUnchangedOrders g.center (g.sideTuple b s).val e f k := by
  have hG1 : G1 g.center := (g.pointZeros_empty_iff).mp h.1
  have hnear := g.continuous_curve.continuousAt.eventually
    (uniqueTriple_other_orders_persist hn hG1 h.2.1)
  obtain ⟨δ, hδ, hδr, hlocal⟩ := (g.eventually_center_iff_radius _).mp hnear
  let t₀ : g.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have ht₀ : t₀.val < δ := by dsimp [t₀]; linarith
  have habs : |(g.sideTime b t₀).val| = t₀.val := by
    cases b <;> simp [sideTime, abs_of_pos t₀.property.1]
  have ho := hlocal (g.sideTime b t₀) (by rw [habs]; exact ht₀)
  intro i j l hij hil hnot
  exact (g.g1_center_side_parameter_order hn hG1 b i j l hij hil s t₀).trans
    (ho i j l hij hil hnot)

end SM.WallGerm
