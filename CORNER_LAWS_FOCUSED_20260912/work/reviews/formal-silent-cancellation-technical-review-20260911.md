# Full formal silent cancellation candidate: technical review

Independent technical/source comparison of root-authored FormalSilentCancellation by another agent of the **same currently available model**. This is **not the stronger-model statement-fidelity approval requested by the user** and does not accept the source claim. I authored the FiniteLineGaps, SelectedCutRefinement, original PositionalCutDecomposition and SilentGapTransform dependencies; root's nonauthor construction reviews are bound below. This report reviews the final assembly and its source statement, not those authored helper proofs. No kernel/build/audit or frozen-file/map edit was performed.

Compared all four declarations and the complete final theorem type with source `pf:formal-cancellation`, `reference/SM/sm-2-amplitude.tex:845–936`, including both stated conclusions and every geometric restriction needed by the printed proof. No mathematical defect, hidden gap premise or source-domain narrowing was found in the final candidate.

The formal input is exactly `silentFarArray (geometricBoundaryArray (R := ℚ) P g)`. Its polynomial variables are indexed by the subtype of **all and only** zero increasing-boundary-triple entries of that actual rational geometric far array. Each index retains the full triple; proof witnesses do not duplicate a variable. Every nonzero entry remains its constant-polynomial image. The ambient algebra is the unrestricted multivariate polynomial ring over ℚ, with no quotient, realizability relation, or hypothesis about independence of determinant differentials.

`map_geometricBoundaryArray` is valid because each actual geometric value is an integer-cast SignType value. Every ring map preserves that integer cast, including at zero; this is not an assertion that arbitrary maps reflect zero. The geometric split theorem uses this exact constant inclusion to rewrite the formal array as the geometric array in the polynomial coefficient ring plus its independent variable part. The support theorem proves that this perturbation vanishes at every initially nonzero rational entry. Both facts are proved from the explicit definitions rather than supplied to the final theorem as premises.

`formal_silent_cancellation` has exactly the source geometric scope: source n≥3, WeakGeneric on the actual polygon, and every fixed physical root g. It assumes neither G1 nor a single-zero condition, a regular perturbation, selected-gap data, a coefficient certificate or realizability of formal assignments. The two conclusions are:

- Equality of the **entire** formal inverse-coordinate array with `constantFarCoordinates H0`, whose definition is coordinatewise C(farOnlyCoordinates H0). Thus every interval coordinate, including leaves and unary terms, equals its fixed c0 value. It is not merely an equality after zero evaluation.
- Equality of the complete `farOnlyOutput` of the formal array at `fullBoundaryInterval hn` with C of the original rational output there. Since farOnlyOutput H is the actual F(-H) applied to the actual inverse coordinates of H, this is precisely the printed reversed-far output with c already proved constant. No unsupported reversed-output claim on arbitrary open intervals is included.

The proof first applies the already checked supported-perturbation results over the polynomial ring with the actual proved variable support. Constant-array inverse naturality identifies its resulting base inverse with C(c0). Complete output naturality identifies the base polynomial-ring output with C of the rational output. The local inverse-of-two instance is the previously proved transport through C, re-enabled as a local instance; the final theorem adds no caller premise of polynomial invertibility.

The dependency chain discharges each substantive source step: exact selected-cut/child decomposition; all rationally silent outer cuts imply actual collinear selected endpoints; an actual nonleaf positive gap kills each forward nonunary contribution; a nonleaf negative gap is used only at the physical full root for the reversed output; and any selected nonsilent cut kills the perturbation product directly. The public supported-coordinate/output results leave no gap hypothesis. Uniqueness of the actual triangular inverse replaces the printed interval induction after all fixed-child forward equations have been proved, so constancy is not used circularly.

The implementation uses an **exact full positional decomposition**, specialized from canonical near/far factorization, instead of separately exporting the printed coefficient-bracket identity `pf:coefficient-factor`. All selected sets and independent gap compositions are present in that unrestricted-ring identity, including empty marks, unary inner terms, one-leaf gaps and further silent zero factors. The two stated source conclusions follow by termwise vanishing in this decomposition. No separate theorem explicitly bearing the coefficient-extraction formula is delivered by this group; it is an alternative complete proof of the lemma's conclusions, not an assumed coefficient identity.

Root first10250 exited0. All 21/21 receipt-bound hashes match and all nineteen bodies are embedded exactly once. All four requested traces contain only propext, Classical.choice and Quot.sound; there is no error, sorryAx, native_decide or Lean.ofReduceBool marker. Successful receipts establish checked evidence only, not the stronger fidelity approval.

This review is limited to `pf:formal-cancellation`. The following `cor:polyform`, its exact gate-variable substitution and its continuation/open-neighborhood argument are not established by this theorem. Stronger statement/definition fidelity, controlled canonical integration/checker and source acceptance remain pending.

SHA-256 bindings:

| File | SHA-256 |
|---|---|
| `work/checks/FormalSilentCancellation.body.lean` | `5cd1e816bc173404929919a02d98943d2c15bc2fcbbbc440c45d99667ae1f27e` |
| `work/checks/FormalSilentCancellation.prototype.lean` | `49707f97d6b09646c2f58260afce3330f451cd0c5aa78f8fb7cd73bc14fd609d` |
| `work/checks/FormalSilentCancellation-first-kernel.log` | `ceeb8b5a7ed4839255a0fa0f40735e9bc3741dd46dfed5d03cb8d48e075d5d8d` |
| `work/checks/FormalSilentCancellation-prototype-result.json` | `895c7c6dd387715a5caf124833633ad5618e1201ea435a53bf4be2202f6b3dac` |
| `work/checks/SilentFarPolynomial.body.lean` | `46ce117365d9aa9b3f262c215a50a73bde1f4c4939fd2eeb9aed64051a876fe0` |
| `work/checks/NearFarRingMaps.body.lean` | `7a5aaadbc1a8041a39f316fb825632afd3493d892e0722fc32defd8fc64c8f16` |
| `work/checks/SilentSupportedPerturbation.body.lean` | `fd4b2656d0073ce518f0460d28bace8528c87723b40682d533fb3f539b6c20ba` |
| `work/checks/SilentGapTransform.body.lean` | `cd5fa17cde20c28806f14f5c790a90da41cc1b1a1d599f0cf88d29fd410b4295` |
| `work/checks/TopFarDecomposition.body.lean` | `2cc1eb1027a60fd62c29ba50c6e933c3ea3c84ec524b550fda66a3be4cdf4231` |
| `work/reviews/silent-supported-perturbation-technical-review-20260911.md` | `ee59f270a5e0eebb0942e4ddff0bcf23fa21893bc3cbe3944d57418dac4d47eb` |
| `work/reviews/silent-far-polynomial-technical-review-20260911.md` | `8440ec15c6e6862a45522cd9bd2228ce5327b31ffaa837393b463889e671912f` |
| `work/reviews/finite-line-gaps-technical-review-20260911.md` | `e9c3e5eac643bbd0a9554a6ce386d57b1f89d84e30c3b4b41dd50546079fae23` |
| `work/reviews/selected-cut-refinement-technical-review-20260911.md` | `fdc5706133aabcdd77ca0c7419269866b257b8c77377f9cc2336904738af1c13` |
| `work/reviews/positional-cut-decomposition-core-review-20260912.md` | `5fd3bb4bf8bdff142159fbe4e01d0b81485e85efe886f5cc9447c13af94301e0` |
| `work/reviews/silent-gap-transform-technical-review-20260912.md` | `27442075ebc86ed020cf224d9be7f94f654cae1763db90fb33fdef1498a00ae0` |
| `work/lean/SM/NearFar.lean` | `3d243e1d12636a02743e0f8dc37e3eecc7d46306fbd3cfca5170fd223ad6fa60` |
| `work/lean/SM/FarOnlyOutput.lean` | `d773b636e2dc37babf11ae3df6b1eb813f5bc2812ad10f5e9bb76faf7d133aa4` |
| `work/lean/SM/NearFarTriangular.lean` | `851c9d30affbb3d38893bdc72249173f4b830d552768ba04e971e1ee848663b2` |
| `work/lean/SM/WeakGeneric.lean` | `1a72ebddb4ddb4d72a89f14a5fede9badc3dbed095a972f6dd1b85db30789b22` |
| `work/lean/SM/RootBoundary.lean` | `604906b750e1ab198a2db3fc3cc011ab325493a91404a0b52ffe4583dd403f1a` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Accepted progress remains 39/192 (20.3%); final target acceptance 0/8.
