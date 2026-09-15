import SM.CuspSourceResponse
import SM.InducedRootsDefinition

/-! Source thm:A-S4 (reference/SM/sm-2-amplitude.tex:460, frame SM15): the cusp law for the
tree coefficient `A_g`. Main declaration: `SM.WallGerm.cusp_law_treeCoefficient`.

Notation. `w : WallGerm (n + 1)` (the source's polygon has `n + 1 ≥ 4` vertices);
`w.CuspAt j` is "simple cusp wall at `j`" (def:walls (K): `4 ≤ n + 1`, `Z_pt = {{j-1, j, j+1}}`,
`Z_c = ∅`, `μ_j(0)` outside the closed segment `[μ_{j-1}(0), μ_{j+1}(0)]`, `τ_j` changes sign);
`CuspCase w.center j true` is "`μ_{j+1}(0)` lies between `μ_{j-1}(0)` and `μ_j(0)`" (newborn
pair `{j-1, j+1} = {cuspFirst true j, cuspLast true j}`) and `CuspCase w.center j false` is
"`μ_{j-1}(0)` lies between `μ_j(0)` and `μ_{j+1}(0)`" (newborn pair `{j-2, j}`);
`w.cuspLoopSide b j : Bool` is the side (`true` = positive parameters, `false` = negative
parameters) on which the newborn pair is a crossing, i.e. `P_loop`, and `!w.cuspLoopSide b j`
is `P_no`; `w.sideTuple side s` is the polygon at the point `s` of that side;
`rotationNumber = rot` (def:regular, lem:rot); `deleteVertex w.center j = Q = P(0) ∖ j`;
`deletionRoot j g = D_j(g)` (def:induced-roots); `treeCoefficient = A_g` (def:treesum).
The proof is the previous executor's kernel-checked candidate lane (prototype
CuspSourceResponse), ported verbatim. -/

namespace SM.WallGerm

variable {n : ℕ} [NeZero n]

/-- thm:A-S4 (cusp law for `A_g`), as printed on SM15: at a simple cusp wall at `j` with
`n ≥ 4` whose deletion `Q = P(0) ∖ j` satisfies (G1): the centre is in exactly one of the two
cusp cases `b`; the newborn pair `{cuspFirst b j, cuspLast b j}` is a crossing at every point
of the loop side and at no point of the no-loop side; `κ = rot(P_loop) - rot(P_no) ∈ {-1, 1}`;
and for every root `g`, `A_g(P_loop) - A_g(P_no) = -κ A_{D_j(g)}(Q)`, at every point of the
loop side and every point of the no-loop side. -/
theorem cusp_law_treeCoefficient (w : WallGerm (n + 1)) (j : ZMod (n + 1)) (hf : w.CuspAt j)
    (hQ : G1 (deleteVertex w.center j)) :
    ∃ b : Bool, CuspCase w.center j b ∧ (∀ b' : Bool, CuspCase w.center j b' → b' = b) ∧
      (∀ s : w.SideParameter,
        IsCrossing (w.sideTuple (w.cuspLoopSide b j) s).val {cuspFirst b j, cuspLast b j} ∧
        ¬ IsCrossing (w.sideTuple (!(w.cuspLoopSide b j)) s).val {cuspFirst b j, cuspLast b j}) ∧
      ∃ κ : ℤ, (κ = -1 ∨ κ = 1) ∧
        ∀ s t : w.SideParameter,
          (rotationNumber (w.sideTuple (w.cuspLoopSide b j) s).val -
            rotationNumber (w.sideTuple (!(w.cuspLoopSide b j)) t).val = (κ : ℝ)) ∧
          ∀ g : ZMod (n + 1),
            treeCoefficient (w.sideTuple (w.cuspLoopSide b j) s).val
                (w.sideTuple (w.cuspLoopSide b j) s).property.1 g (by have := hf.1; omega) -
              treeCoefficient (w.sideTuple (!(w.cuspLoopSide b j)) t).val
                (w.sideTuple (!(w.cuspLoopSide b j)) t).property.1 g (by have := hf.1; omega) =
              -κ * treeCoefficient (deleteVertex w.center j) hQ (deletionRoot j g)
                (by have := hf.1; omega) := by
  obtain ⟨b, hb, huniq, κ, hκ, hlaw⟩ := w.cusp_tree_law j hf
  refine ⟨b, hb, huniq, ?_, κ, hκ, hlaw⟩
  intro s
  constructor
  · exact (w.cusp_side_crossing_iff_loop hf hb (w.cuspLoopSide b j) s).mpr rfl
  · intro hc
    have h := (w.cusp_side_crossing_iff_loop hf hb (!(w.cuspLoopSide b j)) s).mp hc
    exact Bool.not_ne_self _ h

end SM.WallGerm
