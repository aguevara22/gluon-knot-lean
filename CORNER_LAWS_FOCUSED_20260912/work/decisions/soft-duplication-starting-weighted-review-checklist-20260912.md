# Starting weighted-row review checklist

Prepared by `/root/review_contraction_candidates`, another agent of the same currently available model. This is technical/source-comparison preparation for future consumers, not a proof or stronger-model statement-fidelity approval. The reviewer authored the frozen Indices, Arrays and OrderedBoundaryTransport dependencies. No Lean/kernel/build/audit run or frozen-file change was made. Source acceptance increment 0; stronger fidelity approval false; canonical integration false.

Scope: SM2 starting paragraph 1280–1302 and ordinary table 1254–1265. This checklist incorporates root’s proposed more general near/child parameter `t` and independent far parameter `u`; the source ordinary and root cases are later specializations.

Fix an actual parent interval `I` with `I.left=A s`, `B s<I.right`, its proved nonduplicate witness `hI`, and `J=collapseInterval s I hI`. For each actual `C : BoundaryCutSet J`, let `X=(startingFirstChild s I hI C).right`, `Y0=J.right`, and `S0,S1=startingCutSet ... 0,1`. `X` is the first boundary after s and may equal Y0; it is not necessarily an interior cut or the immediate core successor.

## 1. All actual cuts and triple entries

- Require exact interior-cut bijections, not just cardinalities: row0 is the old image of every core interior cut; row1 is their image plus B, disjointly indexed by Unit plus core interior cuts. Derive B’s strict interior bounds from A<B<I.right. Core interior x satisfies s<x<Y0, hence old(x)=tail(x)>B.
- Row0 inherited near and far triples are old images. Row1 inherited near triples are **tail images**, but its inherited far triples are **old images**: the top interval still starts at A. Using a tail image for row1 far data would change the left endpoint to B.
- Verify every lower, middle and upper position using actual consecutive children and `nearAtCut_lower_eq_of_consecutive`/`nearAtCut_upper_eq_of_consecutive`; prove the whole triple equality before evaluating arrays. SectionTriples6 supplies the resulting old/tail evaluations without a caller-provided section or array identity.
- The new B gate must be the actual near triple `(A,B,old X)` and actual far triple `(A,B,I.right)`. Derive this from the literal duplicate child and mapped first core child; collapse of the third positions gives X and Y0. No assumption that X is interior is valid.

## 2. Complete gate products and both weighted rows

Use arbitrary rational D0,H0,b0, exceptional near/child data t, exceptional far data u, and etaMinus,etaPlus. Set D1=`tripleLift s D0 t`, H1=`tripleLift s H0 u`, and b1=`ordinaryLift s etaMinus etaPlus t b0`. Let G(C) be exactly the full core gate product in `BoundaryCutSet.nearFarSummand`, B(C) its full child product, and W(C)=G(C)*B(C).

1. Actual gate reindexing should yield G(S0)=G(C) and G(S1)=((t(X)-u(Y0))/2)*G(C). The extra factor follows from the new B gate entries, with the canonical minus-far convention. (1)
2. The frozen child products give B(S0)=((etaPlus-t(X))/2)*B(C) and B(S1)=B(C). The latter includes the explicit singleton child value 1. (2)
3. Multiply the complete gate and child products and rearrange in the commutative rational ring: W(S0)=((etaPlus-t(X))/2)*W(C) and W(S1)=((t(X)-u(Y0))/2)*W(C). Both are complete summands, not isolated gate identities. (3)
4. Add by distributivity, then add the numerators with their common denominator: W(S0)+W(S1)=((etaPlus-u(Y0))/2)*W(C). Cancellation of t(X) is justified because the **near array and child table use the same t**; u remains arbitrary. No assumption t=u or sign-square identity is required for this general result. (4)
5. Use the proved two-row fiber enumeration (`sum_startingRows`) and the complete cut-fiber sum. Since etaPlus and Y0 are independent of C, pull the multiplier through the full finite core sum. Translate both complete cut-set sums to actual nearFarTransform using the established canonical equivalence. (5)

All product arguments must retain zero values and empty gate products. Use product equivalences and distributivity, never division by an existing gate, b0 entry, or exterior product. No caller-supplied gate/child correspondence, b0-solution premise, or restricted family of compositions should remain on the generic transform theorem.

## 3. Ordinary versus root specialization

- Ordinary: use D0=`coreNear s t`, H0=H and u=t. The resulting multiplier is `(etaPlus-t(Y0))/2`. Only after proving the complete generic transform identity set b0 to the actual ordinary inverse for (D0,H), and apply its proved defining equation.
- Root: use far core array -H and u=-t while retaining **the same ordinary b0** obtained from (D0,H). Negating the lifted far array must negate both its core and exceptional entries. The multiplier becomes `(etaPlus+t(Y0))/2`, multiplying the exact core transform with negated far signs. Do not replace b0 by an inverse for (D0,-H).
- Do not infer equality of individual auxiliary and geometric open sums. Source1217–1221 explicitly attributes the near-data freedom to the complete transform.

## 4. Unary, one-leaf and endpoint checks

- A unary core composition has X=Y0 and no inherited gates, even when J has many leaves. Row0’s gate product is 1; row1 has only the B gate. Under the ordinary specialization that gate is 0; under the root specialization it is t(Y0). The child b0(J) need not be 1. Exclude no unary composition with a parts>=2 or nonempty-interior premise.
- A **one-leaf interval** is a different condition. For the final ordinary E equation: if J has at least two leaves, its core E entry is zero; if J has one leaf, Y0 is the actual immediate core successor of s, so source neighbor data derives t(Y0)=etaPlus and kills the multiplier. Prove this from actual interval lengths/labels rather than identifying the generally selected X with that successor.
- For the later full-root starting case, derive s=0 from the full interval’s left endpoint; then Y0 is the last core position and the cyclic predecessor of s. Actual neighbor data gives t(Y0)=etaMinus, producing the printed k=(etaMinus+etaPlus)/2. This specialization is not part of the current gate helper scope.
- Retain arbitrary distinguished s and source n>=3. Any impossibility of a starting interval when s is last must follow from its endpoint bounds. Ending and strict-spanning cases are separate obligations, not consequences of the starting result.

## Bound files read

- `reference/SM/sm-2-amplitude.tex`: `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf`
- `work/decisions/soft-duplication-starting-gates-plan-20260912.md`: `85fe053a0d3565e8bc2b880089436efdb8860a7ca56b698d56fd981bf4834ebb`
- `work/checks/SoftDuplicationStartingChildren.body.lean`: `7dbdf490200a1ed0064d6e0357317e50c79c6b34946971659cdbfb2bab4c8857`
- `work/checks/SoftDuplicationStartingChildFactors.body.lean`: `2fded724e258908c416e1f4446ec0aafe60479d0a277bce7af089640d345732d`
- `work/checks/SoftDuplicationSectionTriples.body.lean`: `1df5f0f4648a76504970a6eb8fd490b69ed834e4405f7a61e1708ce9bc502b1a`
- `work/checks/CutSetNearFar.body.lean`: `acafef61406c9f460db333b9614da2ec644bc848f4827b0ed256c26c048417c2`
- `work/checks/CutSetNearFarNeighbors.body.lean`: `37fa18e71ce48f08a0073c12847ceb00232b26523ff883327750f0d5918cbbed`
