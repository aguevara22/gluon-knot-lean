# Nonincident flat contraction: tuple correspondence

2026-09-11. **DERIVATION / UNCHECKED IMPLEMENTATION PLAN**, same-model technical assistance only. No stronger fidelity approval, source acceptance, kernel, build, or existing Lean-file edit. Progress remains 39/192 (20.3%).

Let parent arity be N = q + 1 ≥ 4, let g be nonincident to j, and choose the actual boundary position k of j. The reviewed boundary lemmas give `0 < k.val` and `k.val + 1 < N`. Put `t := consecutiveBoundaryTriple k ...`, `Q := deleteVertex P j`, and `a := fusionIndex j g`.

First prove `t.erasedInteriorCount = 1` and `hsize : t.contractedSize = q`. These follow by substituting lower/middle/upper values k - 1, k, k + 1 and using the strict bounds. Unlike the incident-gap reparameterization, these equalities involve the variable k and should not be assumed definitionally true.

Use `e := ZMod.ringEquivCongr hsize` to express the exact typed target:

```lean
contractedVertexIndex g t i = deletionIndex j (e i + a)
```

Equation (1), for every `i : ZMod t.contractedSize`. Equivalently, the contracted tuple reindexed to child arity q equals `shift a Q`:

```lean
(fun u : ZMod q => contractedWordTuple P g t (e.symm u)) = shift a Q
```

Equation (2). The proof must establish (1) for all labels; physical root endpoints alone do not imply (2).

Here is a complete arithmetic route. Let `v := (e i - 1).val`; `ringEquivCongr_val` and preservation of subtraction and 1 identify it with the contracted local position. The `expandPosition_val` formula, after erasure = 1, gives v when v < k.val and v + 1 otherwise. The original boundary equation is `j = g + ↑k.val + 1`. From it and the nonincident definition of `fusionIndex`, derive `a.val = N - k.val - 2`; this lies between 0 and q - 2.

Since `e i` is v + 1 modulo q, `e i + a` is v - k.val modulo q. Its natural representative is `v + q - k.val` when v < k.val, and `v - k.val` otherwise. Each representative lies in [0,q), so prove these representative formulas by exhibiting the corresponding natural cast and applying `ZMod.val_natCast_of_lt`; there is no need for an unrestricted natural-subtraction identity.

In the first case, the deletion label is `j + 1 + ↑(v + q - k.val)`. Substitute the boundary equation for j and cancel k.val; since q + 1 = N is zero modulo N, the result is `g + ↑v + 1`, the unshifted expansion label. In the second case it is `j + 1 + ↑(v - k.val)`, which becomes `g + ↑v + 2`, the expansion label after deleting k. Justify each natural cast subtraction with its established bound. These two cases prove (1), including local label 0.

Applying P to (1) proves (2). A general arity-transport lemma for the reindexed tuple, its G1 proof, and its root coefficient can be proved by equality induction on `hsize`; it should not be an assumed invariance principle. Once the arity is identified, use `treeCoefficient_shift Q hQ a a (by omega)` and simplify `a - a` to 0. This carries local root 0 to exactly `fusionIndex j g`, with `hQ := g1_deleteVertex hz` on the source singleton turn-support domain.

Relevant inspected APIs: `expandPosition_val`, `contractedVertexIndex`, `contractedWordTuple`, `deletionIndex`, `fusionIndex`, `ZMod.ringEquivCongr`, `ZMod.ringEquivCongr_val`, `ZMod.val_natCast_of_lt`, `g1_deleteVertex`, and `treeCoefficient_shift`. This supplies the geometric correspondence required by the nonincident paragraph of `thm:A-S3`; scalar and side-order assembly remain separate.
