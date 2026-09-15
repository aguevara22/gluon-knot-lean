# Proper geometric germ: technical review, 2026-09-11

Reviewer: `/root/review_contraction_candidates`, a separate agent without authorship of these candidates, using the **same currently available model** as the authoring agent. This is independent technical evidence only, **NOT the stronger statement-fidelity approval requested by the user**. Original source acceptance remains pending. No Lean kernel, build, or checker was run by this reviewer.

Reported startup/completion checklist: **39/192 (20.3%)**, targets 0/8; the original shift-scope obstruction remains recorded. This report changes no acceptance status.

## Finding

No algebraic, geometric-indexing, or neighborhood-quantifier defect found in `GeometricProperResponse.body.lean` or `ProperSpanGermResponse.body.lean`. Together they assemble the proper-span response with explicit affine data and the actual critical half-difference, corresponding to `reference/SM/sm-2-amplitude.tex:229–266, 271–311, 319–366`. They do not yet supply the normalized sign-change conclusion or construct the affine data from the original hypotheses.

- **Critical scalar and orientation.** `geometric_proper_output_response` uses the second array minus the first array, multiplied by the inverse of two. In the germ theorem these are respectively the positive and negative punctured values. `geometricBoundaryArray` reads the source's reversed-order sign, and `pointFarSign` uses precisely the same determinant order. The scalar therefore has the printed orientation. The dependency `critical_inverse_source_jump` subtracts the actual inverse equations: the changing ordinary far gate contributes the negative half-difference, and solving for the unary inverse difference changes that sign to positive. `CoefficientResponse` removes only the zero unary coefficient difference, erases the critical gate exactly once, and uses the complete two-gap composition bijection. No critical-response formula or nonzero scalar is assumed.

- **Exact epsilon and E/B choices.** `wallLeftEpsilon` and `wallRightEpsilon` are the signs of the printed left and right ratios. The supplied three scalar inequalities make their numerators and denominator nonzero; `wall_epsilons_one_or_neg_one` excludes the zero branch. `wallGapU` chooses `boundaryUnitArray` for positive epsilon and the complete `farOnlyOutput` for negative epsilon; `wallGapV` makes the opposite choice. `WallGapValues` proves these identifications by the actual inverse equation and sign reversal of every remaining gate. Thus the ordinary critical source uses U, while V belongs to the separately computed critical barred response and is correctly absent from the proper-span formula. Unary gaps retain the empty gate product and E/B value one.

- **Wall geometry is used only at the center.** `BoundaryGapGates` checks that each sampled whole-span or local-gap triple differs from the critical triple before applying array agreement with the center. The left sign identity uses the common first endpoint; the right identity uses the common last endpoint and the printed right ratio. Nearby polygons are never assumed collinear. These identities are valid even for zero determinants, but the wall-support and stability lemmas ensure the sampled noncritical determinants here are nonzero and unchanged. No zero critical gate is evaluated as an ordinary gap coefficient.

- **Center gap values.** The intermediate geometric theorem expresses U using `H₁`. In `proper_span_tree_response`, the two gap intervals provably exclude the full critical span, respectively by strict middle/upper and lower/middle inequalities. The common-neighborhood theorem therefore equates their entire B outputs at the negative punctured point with their center values. E is the unit array and already independent of H. The final simplification of `wallGapU` consequently moves both complete gap factors to the center. Although the full center array has a zero critical entry, gap locality proves that neither gap value depends on it.

- **Actual contracted polygon and physical root.** `expandTriple_ne_critical` proves that every contracted triple avoids the deleted middle position. Therefore pulling back `H₁` gives exactly the pullback of the center array, not an array retaining any punctured critical value. `geometricBoundaryArray_contractedWord` identifies this pullback with the actual contracted tuple's boundary determinants. Its surviving vertices remain in their original order and include both arc endpoints. `contractedWord_G1` follows from the unique zero support and exclusion of its middle vertex; `contractedSize_of_proper` supplies at least three vertices. `contracted_output_tree` applies the existing far-only/tree-coefficient equivalence to that Q. Its label zero is the original physical root: `contractedWord_physical_root` proves equality of the actual directed closing edge with the original edge at g, not merely an abstract label correspondence. The germ theorem evaluates this tuple at `w.center` throughout.

- **Independent sufficiently close punctured points.** `WallGerm` is an actual continuous curve on its open real parameter interval, with genericity at every nonzero parameter. `finite_nonzero_chi_persists` preserves all nonzero signs on one neighborhood; the exact unordered-support correspondence supplies every off-critical entry. `boundary_values_stable_near_center` then obtains a single positive radius no larger than the germ radius through `eventually_center_iff_radius`. That radius is chosen before either punctured point. The conclusion quantifies independently over every negative `sMinus` and positive `sPlus` with their separate absolute values below it; it does not require opposite or equal magnitudes. Positivity leaves nonempty portions of both sides. Each actual tree coefficient uses G1 from its own punctured genericity proof. The Lean variable named `δ` here denotes the neighborhood radius, not the critical jump scalar.

## Scope still outstanding

These candidates leave affine coordinates and their pairwise inequalities as explicit inputs. Their existence from the source wall data, including the source's nonzero direction choice, is not established here. The geometric helper itself does not need a nonzero-direction premise: the determinant-rescaling proof only requires the nonzero scalar ratios. This is a weaker hypothesis, not an additional source restriction.

Neither theorem assumes that the critical sign changes or that the concurrence-zero set is empty. It instead proves the more general actual-half-difference identity on its stated data. It therefore does **not** yet show that the jump scalar is one of the two source signs, or provide the final source theorem with its sign-change hypothesis and affine-data choices discharged. The exceptional full-span response and the remaining wall laws are also outside this review. These are explicit scope limits, not defects in the stated helper conclusions.

The inspected proof path uses established critical-source algebra, contraction/output helpers, determinant identities, finite sign stability, and continuity. No circular use of the proper-germ conclusion was found. Neither target body contains `axiom`, `sorry`, `admit`, `native_decide`, or `unsafe`. The root log reports only `propext`, `Classical.choice`, and `Quot.sound` for both declarations; this reviewer has not independently reproduced kernel elaboration or audited every transitive compiled import.

## Hash and receipt binding

Python SHA-256 verification matched **all 25/25 recorded hashes** in `ProperSpanGermResponse-prototype-result.json`. Both target bodies and every recorded dependency body occur exactly once, byte-for-byte, in the combined prototype. The receipt records **root session 50436, exit 0, first run passed**, and zero source-claim acceptance increment; the log prints the two expected theorem signatures and axiom lists.

| File, relative to focused handoff root | SHA-256 |
|---|---|
| `work/checks/GeometricProperResponse.body.lean` | `a774179b0e4ff1955f3cfa06059e02754fe938bd1204006ec7cf225b397d895a` |
| `work/checks/ProperSpanGermResponse.body.lean` | `2818b513ce2539d8efcd4d1f3df7b465d37fa46a23ce05ee2fb4e130adfe755f` |
| `work/checks/ProperSpanGermResponse.prototype.lean` | `148f8d92bf884788a5bcc16e6999e009bffc830e9b0bcaae3cea9ff8336b3b72` |
| `work/checks/ProperSpanGermResponse-first-kernel.log` | `5ad330efe1d89d29f2509bb0e5c11027c06ca67e93af184214cec177b9df00d0` |
| `work/checks/ProperSpanGermResponse-prototype-result.json` | `ee4714dbdaaa9346add7739312d4de126f9935d9ce5bdc2b7e6546d20b436635` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

New dependency bodies inspected: `CollinearGateSigns`, `BoundaryGateSigns`, `BoundaryGapGates`, `WallGapValues`, `GeometricGapResponse`, `FarOnlyOutputLocality`, `BoundaryArrayStability`, `WallArrayNeighborhood`, and `ContractedGeometricArray` (all under `work/checks/`, suffix `.body.lean`). Their exact bindings are in the hashed receipt above. Shared contraction/output dependency hashes match the earlier receipts. The fourteen canonical-source hashes in `contraction-candidates-technical-review-20260911.md` were rechecked and still match. Prior review hashes are `daff29fbdc79ee5e132a54d58255fc0d3fe04377cccd99e5045aecd901edec24` for that report and `d1f569f0dadbd0df2d86bc2439a1020cd6ae0b20f6ad7f7e93b154d73ecab47d` for `contraction-output-technical-review-20260911.md`.

Additional canonical sources inspected at their relevant definitions and proofs:

```text
154f456d16f796f6d52fabb1f2979b04b9b62dff8421cc2d785def4a2797b705  work/lean/SM/CriticalSourceResponse.lean
709865501de144f8640efc7a55717e168a735385cbdca7fa02b2ba410769640f  work/lean/SM/CoefficientResponse.lean
3fdfd8603154185a6f82e7aafb86ceb0e7297ede7f4b9c6ce91033784ca55651  work/lean/SM/FixedEndpointGate.lean
6cd04237f5c6358f97c53f8f0222844d27cbe967d798d29181f2e518d696d1c2  work/lean/SM/GapSplitProducts.lean
fca24dab7111c6b6f404b075ab4e1b8c20d2fb48083565b6ba89758ebf684f9b  work/lean/SM/WallGerm.lean
b5b30d800215dde4ff3a11d04b16a261501f6736224807df97a434a2aed0ca5a  work/lean/SM/GermNeighborhood.lean
7160db9c4ac930a64c65ce44b9e9a41d4f139a3442a49604b3c96f9a347cadc9  work/lean/SM/FiniteChiStability.lean
d66da53bd155faf33a26116324dfe2211e01ac75a8b9f2ccbf028630ee1e6417  work/lean/SM/Generic.lean
5930e77bd3eb05d371b5226c226d9caa464f99d0be48038b1154d02c623dc2c8  work/lean/SM/SinglePointTriple.lean
33e64bb519d61fdb2d9e7613cd42af12831246e5774276ca5e2e21f63ea2c23a  work/lean/SM/ZeroTriples.lean
```

These hashes bind the reviewed source bytes and root receipts, not every imported `.olean` artifact. Only this report was created; no Lean body, canonical source, map, or status file was edited.
