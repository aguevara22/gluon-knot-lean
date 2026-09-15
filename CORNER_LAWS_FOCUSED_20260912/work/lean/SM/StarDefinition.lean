import SM.StarPolygons
import SM.BowTie

/-! Source def:star (reference/SM/sm-5-transport.tex:5, frame SM15): the stars `K_r`, `K_{-r}`
and the bow-tie `K_0`. Main declaration: `SM.star_definition`. Notation: for `r ≥ 1` and
`N = 2r + 1`, `unitPoint N k = u_k = (cos (2πk/N), sin (2πk/N))` for `k : ZMod N`;
`star r : LabelledTuple N` is `K_r` with `K_r t = u_{r(t-1)}` for the label `t : ZMod N` (the
source label `N` is the residue `0`); `starNeg r = K_{-r} = reversal (star r)` (`P̄_i = μ_{2-i}`,
def:shift); `bowTie : LabelledTuple 4` is `K_0 = ((0,0), (2,2), (0,2), (2,0))` at the labels
`1, 2, 3, 4` (`(4 : ZMod 4) = 0`). -/

namespace SM

/-- def:star as printed on SM15. -/
def StarDefinitionData : Prop :=
  (∀ r : ℕ, 1 ≤ r → ∀ k : ZMod (2 * r + 1),
    unitPoint (2 * r + 1) k =
      (Real.cos (2 * Real.pi * (k.val : ℝ) / ((2 * r + 1 : ℕ) : ℝ)),
        Real.sin (2 * Real.pi * (k.val : ℝ) / ((2 * r + 1 : ℕ) : ℝ)))) ∧
  (∀ r : ℕ, 1 ≤ r → ∀ t : ZMod (2 * r + 1),
    star r t = unitPoint (2 * r + 1) ((r : ZMod (2 * r + 1)) * (t - 1))) ∧
  (∀ r : ℕ, 1 ≤ r → starNeg r = reversal (star r)) ∧
  (bowTie 1 = (0, 0) ∧ bowTie 2 = (2, 2) ∧ bowTie 3 = (0, 2) ∧ bowTie 4 = (2, 0))

theorem star_definition : StarDefinitionData := by
  refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    bowTie_apply_one, bowTie_apply_two, bowTie_apply_three, ?_⟩
  have h4 : (4 : ZMod 4) = 0 := by decide
  rw [h4]
  exact bowTie_apply_zero

end SM
