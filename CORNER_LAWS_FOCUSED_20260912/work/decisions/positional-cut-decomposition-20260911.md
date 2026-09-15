# Positional decomposition through the actual near/far transform

Authored implementation by review_contraction_candidates, another agent of the same currently available model. Root owns nonauthor review and all kernels. This is not a self-review, stronger fidelity approval, or source acceptance. No kernel/build/audit was run and no frozen file/map was changed.

Eight new candidate declarations in PositionalCutDecomposition:

- `SM.positional_cut_half_add`: the factor `(2*b - (-(2*a))) * invOf 2` equals `a+b` by ring algebra and the actual inverse-of-two identity.
- `SM.IntervalComposition.nearFarWeight_position_add`, `_position_near`, `_position_far`: exact full composition-weight identities, since both canonical triples have the same actual middle position. Setting one positional function to zero gives the two single-array identities.
- `SM.nearFarTransform_position_add`, `SM.nearTransform_position`, `SM.farTransform_position`: sum these exact weights with the untouched product over all actual child intervals.
- `SM.positionCutSum_add_decomposition`: use canonical `nearFar_factorization_coordinate` with `D(t)=2*b(t.middle)` and `H(t)=-(2*a(t.middle))`; rewrite all three transforms and convert the selected interior-index product to the actual physical-cut Finset product using frozen `prod_interior_positions`.

The final identity holds for arbitrary a,b on Fin n, arbitrary interval array X, every actual interval I and any CommRing with invertible two. It contains all raw outer and inner compositions, hence unary terms, empty marked sets, empty inner cuts and one-leaf gaps. Zero weights are allowed. There are no geometric hypotheses, coefficient identities or restricted refinement premises.

This supplies an exact polynomial decomposition when R is the unrestricted silent-variable polynomial ring. It does not yet identify the chosen a,b with formal geometric arrays, prove a vanishing gap factor, or establish formal cancellation. Those are root's separate assembly obligations.

The prototype imports SM.NearFarFactorization and Mathlib.Tactic and embeds the exact frozen SelectedCutRefinement body. Exact initial files are preserved as PositionalCutDecomposition-first-draft.body/prototype.lean. Root must run and review this candidate before treating it as checked.

SHA-256:

- `work/checks/PositionalCutDecomposition.body.lean`: `b2d4791ce6ad2a41846ce999b0cc99cecda860dc545064640d526559f7c04fcb`
- `work/checks/PositionalCutDecomposition.prototype.lean`: `e708eca3ae9fc7f6e8fcc04454593956db93cb7b62fa7d84be68e97aa4056d13`
- `work/checks/SelectedCutRefinement.body.lean`: `14813200d24d78c3da98cdc7508400e3b82251cfed19f4dddbf4f81cfe190b18`
- `work/lean/SM/NearFarFactorization.lean`: `5ba746897c43bb5382e4a409feba3c77acfca9bbbadcd6a5e708b94263d92628`
- `reference/SM/sm-2-amplitude.tex`: `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf`

Acceptance unchanged: 39/192 (20.3%); targets 0/8.
