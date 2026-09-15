import SM.DeletionGeneric
import SM.GenericCurveChamber

/-! Actual nearby deletions lie in the central deletion's genuine labelled and
cyclic-quotient chambers. This proves the chamber part of flat-sides (iii),
but does not assert the still separate crossing/visit fusion correspondence. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem flat_deletion_chamber (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter, |t.val| < δ →
      ∃ ht : Generic (deleteVertex (g.curve t) j),
        (⟨deleteVertex (g.curve t) j, ht⟩ : GenericTuple n) ∈
          labelledChamber ⟨deleteVertex g.center j, generic_deleteVertex hn hz hb hc⟩ ∧
        polygonProjection ⟨deleteVertex (g.curve t) j, ht⟩ ∈
          chamber (polygonProjection
            ⟨deleteVertex g.center j, generic_deleteVertex hn hz hb hc⟩) := by
  exact generic_curve_local_chamber hn g (fun t => deleteVertex (g.curve t) j)
    ((continuous_deleteVertex j).comp g.continuous_curve) (generic_deleteVertex hn hz hb hc)

end SM
