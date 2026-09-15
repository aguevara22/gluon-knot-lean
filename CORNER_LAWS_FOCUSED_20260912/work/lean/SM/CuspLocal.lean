import SM.CuspOtherCrossings
import SM.GermNeighborhood

/-! One common positive germ radius for the cusp finite-segment crossing
test, both needle patterns and all other actual crossing-support comparisons.
Loop-side existence, the traversal arc and rotation are separate obligations. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n]

def CuspLocalControl (C Q : LabelledTuple n) (b : Bool) (j : ZMod n) : Prop :=
  cuspDelta Q b j ≠ 0 ∧
  SignType.sign (cuspDelta Q b j) = SignType.sign (cuspDelta C b j) ∧
  CuspCrossingControl C b j Q ∧
  (G1 Q →
    (IsCrossing Q {cuspFirst b j, cuspLast b j} ↔ turn Q j = -SignType.sign (cuspDelta C b j)) ∧
    (IsCrossing Q {cuspFirst b j, cuspLast b j} →
      turn Q (cuspCorner₁ b j) = turn Q j ∧ turn Q (cuspCorner₂ b j) = turn Q j) ∧
    (¬ IsCrossing Q {cuspFirst b j, cuspLast b j} →
      turn Q (cuspCorner₁ b j) = -turn Q (cuspCorner₂ b j)))

theorem cusp_local_control_persists (hn : 4 ≤ n) {P : LabelledTuple n} {j : ZMod n}
    (hz : pointZeroTriples P = {turnSupport j}) {b : Bool} (hc : CuspCase P j b) :
    ∀ᶠ Q in 𝓝 P, CuspLocalControl P Q b j := by
  filter_upwards [cusp_newborn_persists hn hz hc, cusp_needle_patterns hn hz hc,
    cusp_crossing_control_persists hn hz hc] with Q ht hn hc
  exact ⟨ht.1, ht.2.1, hc, fun hG => ⟨ht.2.2 hG, hn hG⟩⟩

namespace WallGerm

theorem cusp_local_control (g : WallGerm n) {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter, |t.val| < δ →
      CuspLocalControl g.center (g.curve t) b j := by
  exact (g.eventually_center_iff_radius _).mp
    (g.continuous_curve.continuousAt.eventually (cusp_local_control_persists h.1 h.2.1 hc))

theorem cusp_local_geometry (g : WallGerm n) {j : ZMod n} (h : g.CuspAt j)
    {b : Bool} (hc : CuspCase g.center j b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧
      (∀ t : g.Parameter, |t.val| < δ → cuspDelta (g.curve t) b j ≠ 0 ∧
        SignType.sign (cuspDelta (g.curve t) b j) = SignType.sign (cuspDelta g.center b j)) ∧
      (∀ t : g.Parameter, |t.val| < δ → t.val ≠ 0 →
        (IsCrossing (g.curve t) {cuspFirst b j, cuspLast b j} ↔
          turn (g.curve t) j = -SignType.sign (cuspDelta g.center b j)) ∧
        (IsCrossing (g.curve t) {cuspFirst b j, cuspLast b j} →
          turn (g.curve t) (cuspCorner₁ b j) = turn (g.curve t) j ∧
          turn (g.curve t) (cuspCorner₂ b j) = turn (g.curve t) j) ∧
        (¬ IsCrossing (g.curve t) {cuspFirst b j, cuspLast b j} →
          turn (g.curve t) (cuspCorner₁ b j) = -turn (g.curve t) (cuspCorner₂ b j))) ∧
      (∀ s t : g.Parameter, |s.val| < δ → |t.val| < δ → s.val ≠ 0 → t.val ≠ 0 →
        ∀ c : Finset (ZMod n), c ≠ {cuspFirst b j, cuspLast b j} →
          (IsCrossing (g.curve s) c ↔ IsCrossing (g.curve t) c)) := by
  obtain ⟨δ, hδ, hδr, hlocal⟩ := g.cusp_local_control h hc
  refine ⟨δ, hδ, hδr, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨(hlocal t ht).1, (hlocal t ht).2.1⟩
  · intro t ht hnt
    exact (hlocal t ht).2.2.2 (g.generic_punctured t hnt).1
  · intro s t hs ht hns hnt c hc
    exact cusp_other_crossings_equal h.1 h.2.1 (hlocal s hs).2.2.1 (hlocal t ht).2.2.1
      (g.generic_punctured s hns).1 (g.generic_punctured t hnt).1 c hc

end WallGerm
end SM
