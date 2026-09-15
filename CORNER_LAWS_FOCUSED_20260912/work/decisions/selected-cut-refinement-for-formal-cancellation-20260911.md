# Fixed selected-cut factorization for formal cancellation

Implementation by review_contraction_candidates, another agent of the same currently available model. This is authored proof work, not independent self-review or stronger-model fidelity approval. Root owns review and all Lean/kernel runs. No kernel/build/audit was run here; frozen files and accepted state were not edited.

Read the full source `reference/SM/sm-2-amplitude.tex:845–984` and `formal-cancellation-after-line-gap.md`. The smallest missing combinatorial bridge is a fixed-selected-cut specialization of the existing refinement bijection. It needs no new sorting or concatenation algorithm: NestedCutSets already proves exact inverse flattening/restriction, and RefinedChildren already proves equality of every actual fine child interval and the complete product of their coordinates.

New body/prototype: `work/checks/SelectedCutRefinement.body.lean` and `.prototype.lean`. They contain thirteen declarations in `SM.IntervalComposition` and import `SM.NearFarFactorization` plus `Mathlib.Tactic`. Exact initial body/prototype copies are preserved as `SelectedCutRefinement-first-draft.*`. These are unchecked candidates until root supplies its own kernel result.

API, in dependency order:

1. `refiningCompositionEquiv π`: fine raw compositions containing all cuts of π are equivalent to canonical `RefiningCutSet π`.
2. `nestedRefiningCompositionEquiv π`: every independent family of raw compositions of the actual parts of π is equivalent to those fine compositions.
3. `nestedRefiningCompositionEquiv_val`: its fine composition is exactly the ordered composition of `flattenCutSets`.
4. `selectedComposition_interior S`: adjoining the endpoints to any `InteriorCutSet S` and sorting gives a composition whose exact interior set is S.
5. `selectedComposition_refines_iff S ρ`: refinement containment of that composition is equivalent to `S.val ⊆ ρ.cutSet.interior.val`; the global endpoints impose no extra selection.
6. `prod_interior_positions π b`: the product indexed by all interior cut indices equals the product over the actual physical interior cut set.
7. `prod_inner_positions π T b`: the product over every recovered inner cut equals the physical product over `T.interior \ π.interior`. This follows from the canonical unmarked-cut equivalence and position identities, not an assumed equality of products.
8. `positionCutSummand b X ρ`: product of b at every actual interior position, multiplied by X at every actual child interval of ρ.
9. `prod_refinement_gap_summands π T b X`: all recovered gap summands multiply to the unselected physical-cut product times the complete fine child product.
10. `prod_nested_gap_summands π σ b X`: the same termwise equality for any actual independently chosen gap family σ, using canonical exact recovery after flattening.
11. `sum_refining_cut_products π b X`: sum over every fine raw composition containing π's cuts equals the product, over actual gaps of π, of the independent raw gap-composition sums.
12. `sum_refining_selected_cut_products π a b X`: restores the fixed product of arbitrary selected-cut weights a.
13. `sum_refining_constant_selected_factor π q b X`: the selected product is `q ^ π.cutSet.interior.val.card`, giving the source's desired cardinal exponent after π is constructed from S.

The last three theorems hold over any commutative semiring. Earlier product identities need only a commutative monoid. They preserve actual child interval arguments, all raw compositions including unary ones, empty inner-cut domains, a unary outer composition (empty S), and one-leaf gaps. No disjointness, geometric genericity, nonzero weight, or coefficient identity is assumed. For a nonempty source S, instantiate the same theorems with its sorted outer composition; no separate size hypothesis is needed for the combinatorial identity.

To apply the final theorem to the printed top-coefficient formula:

- Choose π as `(BoundaryCutSet.ofInterior S).toComposition` and q as `-eta/2`. The exact cut-set lemma identifies its selected interior set with S.
- Define b at each strict interior physical position x of I as the constant top cut factor `-eta*H0(I.left,x,I.right)/2`. Values of b outside I's strict interior are immaterial; they may be defined as zero. Every unselected silent top cut therefore has b=0. Terms containing one vanish, so the unrestricted refinement sum already implements exclusion of all other silent cuts.
- Use the separately proved actual gap-sign identity to identify b at every interior position of each actual gap with the corresponding gap far-factor `-(eta*epsilon_gap)*H0(gap.left,x,gap.right)/2`. Then each positional gap sum is the full canonical `farTransform` on that gap, with X fixed at c0. Empty cut products remain one, so the same rewrite covers one-leaf gaps.
- What remains is genuine polynomial algebra: prove coefficient extraction from the formal top transform equals the left-hand refining sum, using injectivity of the physical top-cut variable map and the fact each raw cut occurs once. This candidate does not assume or prove that extraction statement. Root must also discharge the gap-sign specialization, vanishing factors, inverse uniqueness/induction, full-root output cancellation, and the later unrestricted polynomial substitution/continuation corollary.

The implementation deliberately uses a positional weight b because top coefficients have fixed global endpoints, whereas the gap transform has each gap's own endpoints. Treating the canonical preserved **near** triples as preserved gap **far** triples would be wrong. Only the middle-position identity is used here; the endpoint change is left to the actual geometric sign identity.

SHA-256 bindings:

| File | SHA-256 |
|---|---|
| `work/checks/SelectedCutRefinement.body.lean` | `14813200d24d78c3da98cdc7508400e3b82251cfed19f4dddbf4f81cfe190b18` |
| `work/checks/SelectedCutRefinement.prototype.lean` | `2ada5f1b4a38f717fef32c16c3007bd6caaff29b05cdb82af0aa500df3b1c140` |
| `work/checks/SelectedCutRefinement-first-draft.body.lean` | `14813200d24d78c3da98cdc7508400e3b82251cfed19f4dddbf4f81cfe190b18` |
| `work/checks/SelectedCutRefinement-first-draft.prototype.lean` | `2ada5f1b4a38f717fef32c16c3007bd6caaff29b05cdb82af0aa500df3b1c140` |
| `work/lean/SM/NestedCutSets.lean` | `1d2532f7a0928ad105e901bf534dced931244866bc875eecc59f47b338970945` |
| `work/lean/SM/RefinedChildren.lean` | `c201df125ee9221a73c9ce58a195fcec98e55c7c1b78de5616e1bdf94e5ea3d3` |
| `work/lean/SM/RefinedInterior.lean` | `b3df53fad5a7616efc35bf277faad08a2295b4dab5a3fcdde259752af61980b0` |
| `work/lean/SM/RefinedOuter.lean` | `afd60b4ad330b24f5a273b20512c54ef58b2f36e0f7a9c59f82f13de70afe1d0` |
| `work/lean/SM/RefinedWeights.lean` | `328abc14a9737341c01603980d66fc7ef58e05b1c5fc672d6ea8419fe034a6b6` |
| `work/lean/SM/MarkedCutIndex.lean` | `8a6cb69376fa533591a4e6efe819bc91a0138ea24630106598e3da58d1135de5` |
| `work/lean/SM/MarkedRefinement.lean` | `e0755615095571245f94fab25e6690ca61a79a9a0df664f3332da03d4a612144` |
| `work/lean/SM/InteriorCutSet.lean` | `4eaf17d0deef9554cbbfbd3464a3a0f1c54de03ac419932b14a595cc35aca326` |
| `work/lean/SM/NearFarFactorization.lean` | `5ba746897c43bb5382e4a409feba3c77acfca9bbbadcd6a5e708b94263d92628` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Candidate only. Source acceptance and stronger statement/definition fidelity remain pending; accepted progress remains 39/192 (20.3%), targets 0/8.
