import SM.FlatCarriersDefs
import SM.CornerStateSum

/-! Source thm:C-S3 (reference/SM/sm-4-knotlaws.tex:153-159, frame SM15): the flat law, "At a simple flat wall at `j`,
with `n ≥ 4`, `C(P_right) − C(P_left) = C(P(0) ∖ j)`." Main declaration: `SM.thm_C_S3` (the fixed target name of
work/lean/axiom-policy.json).

Notation (accepted rows def:germ, def:walls, lem:flat-sides, def:flat-carriers, def:C): a simple flat wall germ at
`j` on `n + 1 ≥ 4` vertices is `g : WallGerm (n + 1)` with `hz : g.pointZeros = {turnSupport j}`, `hb : StrictBetween
(g.center (j−1)) (g.center j) (g.center (j+1))`, `hc : g.concurrences = ∅`, `hsc : g.SignChanges (turn · j)` — the
hypotheses of lem:flat-sides (SM/FlatSides.lean), the parent size written `n + 1` with `3 ≤ n` as there; the right
side is the side with `τ_j = −1` (`IsRightSide g j b t`), the left side the one with `τ_j = +1` (`IsLeftSide`,
def:walls (F)); `P_right`, `P_left` are the polygons `g.sideTuple b t` on those sides for sufficiently small
side parameters `t < δ` ("after shrinking the interval"); `P(0) ∖ j` is `deleteVertex g.center j`, generic by
lem:flat-sides (iii) (`generic_deleteVertex`); `C` is `cornerStateSum` (def:C). -/

namespace SM

/-- thm:C-S3 as printed. -/
structure CS3Data : Prop where
  /-- eq. ccf:flat-law: `C(P_right) − C(P_left) = C(P(0) ∖ j)` at a simple flat wall, for the polygons of the two
  sides at all sufficiently small side parameters. -/
  flat_law : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (_hsc : g.SignChanges (fun P => (turn P j : ℝ))),
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧
      ∀ (bR bL : Bool) (tR tL : g.SideParameter), tR.val < δ → tL.val < δ →
        IsRightSide g j bR tR → IsLeftSide g j bL tL →
        cornerStateSum (flat_hn1 hn) (g.sideTuple bR tR).property -
            cornerStateSum (flat_hn1 hn) (g.sideTuple bL tL).property =
          cornerStateSum hn (generic_deleteVertex hn hz hb hc)

theorem thm_C_S3 : CS3Data := by
  sorry

end SM
