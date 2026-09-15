# Source coefficient domain, 2026-09-11

Same-model technical advice by `/root/review_contraction_candidates`; **not stronger statement-fidelity approval**. No Lean kernel was run, and no existing body or map was edited. Checklist remains **39/192 (20.3%)**.

The integer source equality should be obtained from **integer gap outputs**, not integer inverse coordinates. On a two-leaf interval, the inverse equation has the unary coordinate plus one gate contribution. Both child coordinates are one and the unit-array right side is zero, so the inverse coordinate is half the geometric far sign. Over the rationals it can therefore be one-half or minus one-half. Neither the source nor the current proof needs integrality of the raw inverse array.

## Minimal cast bridge to prove

The following are recommended definitions/lemma statements, **not newly kernel-checked declarations**. For any interval J assume only
`hG : 2 ≤ J.leaves → G1 (restrictedWordTuple P g J)`.
For the actual wall gaps, obtain this premise from `critical_closed_gaps_G1`; do not require global G1 of the nongeneric center.

Define integers independent of the coefficient ring:

- `integerGapE J`: one when the endpoints are adjacent, otherwise zero.
- `integerGapB P g J hG`: one if `J.leaves = 1`; otherwise the integer `treeCoefficient` of `restrictedWordTuple P g J`, rooted at zero, using `hG` and the derived arity of at least three.
- `integerGapU` and `integerGapV`: the same epsilon branches as `wallGapU` and `wallGapV`, using these integer E/B values.

Prove the following exact cast identities for every commutative R with invertible two:

```lean
(integerGapE J : R) = boundaryUnitArray (R := R) J
(integerGapB P g J hG : R) =
  farOnlyOutput (geometricBoundaryArray (R := R) P g) J
(integerGapU P g J hG ε : R) =
  wallGapU (geometricBoundaryArray (R := R) P g) J ε
(integerGapV P g J hG ε : R) =
  wallGapV (geometricBoundaryArray (R := R) P g) J ε
```

Justification is already available: the E identity is the identical zero/one definition. For B, split on one leaf. `farOnly_leaf_values` proves the formal value one. Otherwise positive interval length gives at least two leaves, and `farOnlyOutput_restricted_tree` gives exactly the cast of the defined integer tree coefficient. It uses only local G1. The U/V identities follow by splitting the same epsilon condition and using the two cast identities. These cast lemmas can hold for every `SignType` epsilon because both definitions use the same default branch; the source application separately proves the epsilon is nonzero.

This proves integer origin using specific, ring-independent integers. A bare existential cast witness in an arbitrary R would obscure that content, especially in positive characteristic or a trivial ring. No assertion about integrality of individual inverse coordinates or summands is involved.

## Recover the integer-amplitude theorem

1. Instantiate the existing aggregate at **R = ℚ**, retaining its fixed integer sign d and its common punctured radius. This is a faithful coefficient domain with invertible two; ℤ itself is not an allowed coefficient ring for the inverse construction.
2. Rewrite all center U/V factors using the cast lemmas. The original and contracted `treeCoefficient` terms already come from integers. In the proper branch, keep the proved contracted arity/G1 and physical-root identification; in the full branch construct no contracted polygon.
3. Use preservation of subtraction, addition, and multiplication by the integer cast to express both sides as casts of the corresponding integer source expressions. Injectivity of the embedding from ℤ into ℚ then yields the exact integer equality. Arbitrary-R equality alone must not be cancelled through a possibly noninjective cast.

The existing rational half-jump equation retains the source meaning of d. If a wholly integer scalar clause is preferred, additionally export the equivalent statement that the positive critical integer sign minus the negative critical integer sign equals twice d. This follows directly from opposite fixed signs; it avoids integer division. Keep the proved alternative that d is minus one or one.

Both arbitrary-affine and constructed-affine aggregate versions can receive this integer corollary. No proof of integrality of the full inverse array, and no new geometric premise, is needed.

Sources inspected: `reference/SM/sm-2-amplitude.tex`, `lem:farout` and `thm:single-triple`; `work/checks/RestrictedCriticalG1.body.lean` (`critical_closed_gaps_G1`); `work/lean/SM/FarOnlyOutput.lean` (leaf equations); `work/lean/SM/RestrictedWordRoot.lean` (`farOnlyOutput_restricted_tree`). Their source bindings are respectively `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf`, `be36ad6817db31270a9ea436505688e2d2e65f00a8c839449bdcfdd268b2df60`, `d773b636e2dc37babf11ae3df6b1eb813f5bc2812ad10f5e9bb76faf7d133aa4`, and `a2d45634865602373437222b5e190794f31375624fa3021745ae6a0043551e8e`.
