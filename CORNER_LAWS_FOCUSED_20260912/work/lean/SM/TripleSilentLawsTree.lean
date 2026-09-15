import SM.TripleSilentTreeLaws

/-! Source thm:A-R3E (reference/SM/sm-2-amplitude.tex:593, frame SM15): the triple law and
silence for the tree coefficient `A_g`. Main declaration:
`SM.WallGerm.triple_and_silent_laws_treeCoefficient`.

Notation. `w : WallGerm n`; `w.TripleAt e f k` is "simple triple wall at `{e, f, k}`" (def:walls
(T)); `w.ExtensionAt M a` is "simple exterior-extension wall at `(M; a)`" (def:walls (E));
`w.PureCutAt i j k` is "simple pure cut at `{i, j, k}`" (def:walls (C)); `P_+` / `P_-` are the
punctured sides of positive / negative parameters, `w.sideTuple true t` / `w.sideTuple false s`
their polygons at the points `t`, `s`; `TreeDataEqual P Q hP hQ g hn` (module SM.TreeChamber,
used by the accepted prop:A-chamber) says that for the root `g` every ordinary and root
composition weight `V^±(π)`, every open sum `b_{[i,j]}` and the tree coefficient `A_g` of `P`
and of `Q` agree; `treeCoefficient = A_g` (def:treesum). The proof is the previous executor's
kernel-checked candidate lane (prototype TripleSilentTreeLaws), ported verbatim. -/

namespace SM.WallGerm

variable {n : ℕ} [NeZero n]

/-- thm:A-R3E (triple law and silence for `A_g`), as printed on SM15.
(i) At a simple triple wall, every composition weight, every `b_{[i,j]}` and `A_g` are identical
on the two sides, for every root `g` (at every point of each side).
(ii) At a simple exterior-extension wall or a simple pure cut, `A_g(P_+) = A_g(P_-)` for every
root `g` (at every point of each side). -/
theorem triple_and_silent_laws_treeCoefficient (hn : 3 ≤ n) :
    (∀ (w : WallGerm n) (e f k : ZMod n), w.TripleAt e f k →
      ∀ (g : ZMod n) (s t : w.SideParameter),
        TreeDataEqual (w.sideTuple true t).val (w.sideTuple false s).val
          (w.sideTuple true t).property.1 (w.sideTuple false s).property.1 g hn) ∧
    (∀ (w : WallGerm n) (M a : ZMod n), w.ExtensionAt M a →
      ∀ (g : ZMod n) (s t : w.SideParameter),
        treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn =
          treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn) ∧
    (∀ (w : WallGerm n) (i j k : ZMod n), w.PureCutAt i j k →
      ∀ (g : ZMod n) (s t : w.SideParameter),
        treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn =
          treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn) :=
  tree_triple_and_silent_laws hn

end SM.WallGerm
