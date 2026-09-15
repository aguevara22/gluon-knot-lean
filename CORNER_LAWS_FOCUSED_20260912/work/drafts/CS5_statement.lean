import SM.CornerStateSum
import SM.CuspSides

/-! Source thm:C-S5 (reference/SM/sm-4-knotlaws.tex:910-913, frame SM15): empty-cusp zero, "At a simple empty cusp,
`C(P_no) = 0`." Main declaration: `SM.thm_C_S5` (the fixed target name of work/lean/axiom-policy.json).

Notation (accepted rows def:germ, def:walls, lem:cusp-sides, def:C; SM/CuspDefinition.lean, CuspSideCrossings.lean,
CuspSides.lean, CornerStateSum.lean): a simple cusp wall germ at `j` is `g : WallGerm n` with `h : g.CuspAt j`
(def:walls (K): `n ≥ 4`, `Z_pt = {{j−1, j, j+1}}`, `Z_c = ∅`, `μ_j(0)` outside the closed segment
`[μ_{j−1}(0), μ_{j+1}(0)]`, `τ_j` changes sign); its case `b` (`CuspCase g.center j b`: A when `μ_{j+1}(0)` lies between
`μ_{j−1}(0)` and `μ_j(0)`, B when `μ_{j−1}(0)` lies between `μ_j(0)` and `μ_{j+1}(0)`) fixes the newborn pair
`{cuspFirst b j, cuspLast b j}`; the loop side is `g.cuspLoopSide b j` (the side on which the newborn pair is a
crossing, lem:cusp-sides (i)) and the no-loop side `P_no` is the other side, `g.sideTuple (!(g.cuspLoopSide b j)) t`
for every side parameter `t`; "the cusp is empty if on the loop side the two visits of the newborn crossing are
cyclically adjacent in the Gauss word" is `WallGerm.EmptyCusp` (`GaussVisitsAdjacent` of the two visits
`twoStepFirstVisit`/`twoStepLastVisit` of the newborn crossing, at every loop-side parameter); `C` is
`cornerStateSum` (def:C). -/

namespace SM

variable {n : ℕ} [NeZero n]

/-- def:walls (K): "The cusp is *empty* if on the loop side the two visits of the newborn crossing are
cyclically adjacent in the Gauss word." -/
def WallGerm.EmptyCusp (g : WallGerm n) {j : ZMod n} (h : g.CuspAt j) {b : Bool}
    (hc : CuspCase g.center j b) : Prop :=
  ∀ s : g.SideParameter,
    GaussVisitsAdjacent (by have := h.1; omega) (g.sideTuple (g.cuspLoopSide b j) s).property
      (twoStepFirstVisit (g.cusp_loop_crossing h hc s)) (twoStepLastVisit (g.cusp_loop_crossing h hc s))

/-- thm:C-S5 as printed. -/
structure CS5Data : Prop where
  /-- "At a simple empty cusp, `C(P_no) = 0`": for every simple cusp wall germ, in its case, if the cusp is
  empty then the corner state sum vanishes at every polygon of the no-loop side. -/
  empty_cusp_zero : ∀ (n : ℕ) [NeZero n] (g : WallGerm n) (j : ZMod n) (h : g.CuspAt j) (b : Bool)
    (hc : CuspCase g.center j b), g.EmptyCusp h hc →
    ∀ t : g.SideParameter,
      cornerStateSum (by have := h.1; omega) (g.sideTuple (!(g.cuspLoopSide b j)) t).property = 0

theorem thm_C_S5 : CS5Data := by
  sorry

end SM
