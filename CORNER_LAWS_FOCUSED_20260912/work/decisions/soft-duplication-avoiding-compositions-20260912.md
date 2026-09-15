# Direct avoiding composition transport

Authored by `/root/review_contraction_candidates` following the bounded architecture proposed by `/root`. This is same-model implementation, not an independent review or stronger statement-fidelity approval. No Lean/kernel/build/audit run; no frozen/canonical/reference or acceptance edits. Root owns compilation and nonauthor review.

The body has 16 declarations in `SM.SoftDuplication`. It retains the frozen avoiding domain: arbitrary `[NeZero n]`, `s : Fin n`, actual child interval `I`, its nonduplicate proof `hI`, and `havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)`. The latter already proves the former via `avoiding_not_duplicate`; no extra correspondence or size premise is introduced. The source triangle case is included.

## Construction and proof steps

`collapseComposition` keeps `π.parts` and sends every cut `k` to `collapse s (π.cut k)`. Every original cut lies between the original first and last cuts by monotonicity of the strict cut map. Collapse monotonicity gives weak order on two selected cuts. Equality would contradict the proved injectivity of collapse on this same avoiding interval and then the original strict cut order. This proves strictness without a global order embedding or a supplied correspondence.

`collapseComposition_cutSet` is the exact finite-image composition identity. `collapseComposition_eq_avoidingCompositionEquiv` then compares complete cut sets using canonical composition injectivity and the canonical sorting inverse; endpoint equality is not treated as composition equality. Since parts are unchanged, unary compositions and all indexed factors remain available to later algebra.

The body exposes exact cut and endpoint equations, actual child endpoints, and all three positions of every actual near and far triple. `composition_part_avoiding` uses canonical `part_bounds`: if both duplicate occurrences were in a child, they would be in the parent. Thus `collapseComposition_part` identifies the actual mapped child with `collapseInterval` whose nondegeneracy is derived from that child avoidance. This is not leaf-count or unit-array preservation.

`triple_plain_of_avoiding_interval` proves that a triple bounded by I cannot contain both A and B: either allowed exceptional placement forces I.left ≤ A and B ≤ I.right, contradicting havoid. The near specialization derives its bounds from the actual extreme selected cuts. The far specialization uses the exact parent endpoints. The two collapseTriple compatibility theorems accept any proof of this plainness; the preceding two declarations supply it from the actual source domain, and proof irrelevance means no chosen proof changes the positions.

## Dependencies and scope

The ordered prototype embeds Indices, CutFibers, Avoiding, Arrays, then this new body, each exactly once. It imports their canonical import union plus `SM.CompositionSegments`. Exact body/prototype/source/receipt bindings and initial snapshots are in `SoftDuplicationAvoidingCompositions-draft-dependency-bindings.json`.

This addresses the direct composition, child and triple identification in source A-soft's avoiding-interval paragraph (SM2 lines1273–1277). It proves no weight or array identity, numerical leaf count, boundaryUnitArray value, complete transform equality, inverse equation or soft amplitude law. Root separately handles numeric/unit lemmas and weighted assembly. No source acceptance is granted.

Exact declaration print list:

- `SM.SoftDuplication.collapseComposition`
- `SM.SoftDuplication.collapseComposition_parts`
- `SM.SoftDuplication.collapseComposition_cut`
- `SM.SoftDuplication.collapseComposition_endpoints`
- `SM.SoftDuplication.collapseComposition_cutSet`
- `SM.SoftDuplication.collapseComposition_eq_avoidingCompositionEquiv`
- `SM.SoftDuplication.collapseComposition_part_endpoints`
- `SM.SoftDuplication.composition_part_avoiding`
- `SM.SoftDuplication.collapseComposition_part`
- `SM.SoftDuplication.collapseComposition_nearTriple_positions`
- `SM.SoftDuplication.collapseComposition_farTriple_positions`
- `SM.SoftDuplication.triple_plain_of_avoiding_interval`
- `SM.SoftDuplication.nearTriple_plain_of_avoiding`
- `SM.SoftDuplication.farTriple_plain_of_avoiding`
- `SM.SoftDuplication.collapseComposition_nearTriple`
- `SM.SoftDuplication.collapseComposition_farTriple`
