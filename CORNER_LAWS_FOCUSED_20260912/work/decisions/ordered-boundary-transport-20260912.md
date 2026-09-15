# Ordered boundary transport: candidate proof scope

Authored by `/root/review_contraction_candidates`, following architecture proposed by `/root`; same available model. This is implementation, not an independent review or stronger statement-fidelity approval. No Lean/kernel/build/audit was run by this agent. Root owns compilation and nonauthor review. No frozen proof, source, canonical module or acceptance map was edited.

The candidate has 27 declarations in `SM.OrderedBoundaryTransport`, with canonical imports `SM.NearFar` and `SM.CompositionCutSet` only. Its ordered prototype body list contains just `work/checks/OrderedBoundaryTransport.body.lean`. First drafts and exact import/source/body/prototype hashes are recorded in `OrderedBoundaryTransport-draft-dependency-bindings.json`.

## Definitions and exact identities

For any `e : Fin n ↪o Fin m`, `interval e I` maps both endpoints; `triple e T` maps all three positions. Strictness is obtained from `e.strictMono`, not assumed separately. Neither size has a positivity premise; an actual source interval already supplies distinct endpoints.

`composition e π` retains `π.parts`, `π.parts_pos`, and the full index type `Fin (π.parts + 1)`. Its cut map is exactly `fun k => e (π.cut k)`. Thus the part, near-triple and far-triple identities are definitional, including their proof fields. The endpoint identities follow by applying `e` to the original first/last equations.

`cutSet e S` is the complete `Finset.image e S.cuts`, including both endpoints. Every image cut lies between the image endpoints by monotonicity. `composition_cutSet` is the finite-image composition identity. Finset image injectivity and the canonical exact cut-set encoding prove injectivity of both cut-set and composition transport. `cutSet_toComposition` proves compatibility with the canonical sorted composition by applying its cut-set injectivity theorem. It does not identify endpoints alone with an entire tuple or cut list.

## Weight and summand proofs

`nearFarWeight_pullback` is the unconditional weight identity for `pullbackTripleArray`. `nearFarWeight_transport` needs equalities only at each actual mapped near/far triple used by the given composition. The proof applies finite-product congruence, substitutes the exact triple identities, then substitutes the two pointwise entry equalities. The half factor stays identical in the same arbitrary commutative ring with invertible 2.

`childProduct_transport` compares every actual mapped child interval under the explicit pointwise child-coordinate equality. `summand_transport` combines these two proved product identities to transport the complete raw transform summand. `summand_pullback` specializes it to exact pullback arrays without extra hypotheses. No factor is divided out, so zeros and rings with zero divisors are retained. A unary composition still has one child and zero cut gates; the same finite-product proof covers its empty gate product.

## Scope and remaining work

This supplies generic algebra/composition transport for the plain and selected-cut duplication cases in source A-soft (SM2 formal-duplication proof, lines 1223–1402). It does not assert that an embedding preserves numeric leaf counts, unit arrays, or all possible target cut sets. In particular, no bijection onto every composition of the image interval and no whole-transform or duplication law are claimed. The concrete duplication proof must derive the actual pulled-back array and child-coordinate equalities and handle the other cut-set fibers separately.

Exact declaration print list:

- `SM.OrderedBoundaryTransport.interval`
- `SM.OrderedBoundaryTransport.interval_left`
- `SM.OrderedBoundaryTransport.interval_right`
- `SM.OrderedBoundaryTransport.interval_injective`
- `SM.OrderedBoundaryTransport.triple`
- `SM.OrderedBoundaryTransport.triple_positions`
- `SM.OrderedBoundaryTransport.triple_injective`
- `SM.OrderedBoundaryTransport.composition`
- `SM.OrderedBoundaryTransport.composition_parts`
- `SM.OrderedBoundaryTransport.composition_cut`
- `SM.OrderedBoundaryTransport.composition_endpoints`
- `SM.OrderedBoundaryTransport.composition_part`
- `SM.OrderedBoundaryTransport.composition_nearTriple`
- `SM.OrderedBoundaryTransport.composition_farTriple`
- `SM.OrderedBoundaryTransport.cutSet`
- `SM.OrderedBoundaryTransport.cutSet_cuts`
- `SM.OrderedBoundaryTransport.cutSet_injective`
- `SM.OrderedBoundaryTransport.composition_cutSet`
- `SM.OrderedBoundaryTransport.composition_injective`
- `SM.OrderedBoundaryTransport.cutSet_toComposition`
- `SM.OrderedBoundaryTransport.pullbackTripleArray`
- `SM.OrderedBoundaryTransport.pullbackIntervalArray`
- `SM.OrderedBoundaryTransport.nearFarWeight_pullback`
- `SM.OrderedBoundaryTransport.nearFarWeight_transport`
- `SM.OrderedBoundaryTransport.childProduct_transport`
- `SM.OrderedBoundaryTransport.summand_transport`
- `SM.OrderedBoundaryTransport.summand_pullback`
