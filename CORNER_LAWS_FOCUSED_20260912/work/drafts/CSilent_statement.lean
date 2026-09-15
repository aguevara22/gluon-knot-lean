import SM.CornerStateSum
import SM.NamedWallPredicates

/-! Source prop:C-silent (reference/SM/sm-4-knotlaws.tex:101-105, frame SM15): silence, "At a simple
exterior-extension wall (E) or a simple pure cut (C), `C(P₊) = C(P₋)`." Main declaration: `SM.prop_C_silent`
(the fixed target name of work/lean/axiom-policy.json).

Notation (accepted rows def:germ, def:walls, def:C; SM/WallGerm.lean, GermDefinition.lean,
NamedWallPredicates.lean, CornerStateSum.lean): a wall germ is `g : WallGerm n` (a continuous curve of labelled
`n`-tuples on `(−radius, radius)`, generic off the centre, not generic at the centre); "a simple
exterior-extension wall (E) at `(M; a)`" is `g.ExtensionAt M a` (def:walls (E): `M ∉ {a−1, a, a+1, a+2}`,
`Z_pt = {{a, a+1, M}}`, `Z_c = ∅`, `μ_M(0)` on the line of `E_a(0)` outside the closed segment, `χ_{a,a+1,M}`
changes sign); "a simple pure cut (C) at `{i, j, k}`" is `g.PureCutAt i j k` (no two of `i, j, k` consecutive,
`Z_pt = {{i, j, k}}`, `Z_c = ∅`, `χ_{ijk}` changes sign); the two sides `P₊`, `P₋` of the wall are the generic
polygons `g.sideTuple true t` (parameter `+t`) and `g.sideTuple false t` (parameter `−t`) for side parameters
`t ∈ (0, radius)` — the statement is read at every pair of side points (each side lies in one chamber, on which
`C` is constant by the accepted prop:C-chamber); `C` is `cornerStateSum` (def:C). -/

namespace SM

/-- prop:C-silent as printed: at a simple silent wall the corner state sums of the two sides agree. -/
structure CSilentData : Prop where
  /-- (E): "At a simple exterior-extension wall … `C(P₊) = C(P₋)`." -/
  extension : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n), g.ExtensionAt M a →
    ∀ tp tm : g.SideParameter,
      cornerStateSum hn (g.sideTuple true tp).property = cornerStateSum hn (g.sideTuple false tm).property
  /-- (C): "… or a simple pure cut, `C(P₊) = C(P₋)`." -/
  cut : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (i j k : ZMod n), g.PureCutAt i j k →
    ∀ tp tm : g.SideParameter,
      cornerStateSum hn (g.sideTuple true tp).property = cornerStateSum hn (g.sideTuple false tm).property

theorem prop_C_silent : CSilentData := by
  sorry

end SM
