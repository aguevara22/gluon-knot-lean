# Triple tree data and silent algebra: technical review

2026-09-11. Reviewer: another agent of the same currently available model, independently reviewing seven root-authored declarations. This is **not the stronger-model statement-fidelity approval requested by the user**, and is not source acceptance. No Lean/kernel/build was run and no frozen body, canonical file or acceptance map was edited.

**Finding:** no defect found in `TripleTreeData` (2), `SilentIntegerFactors` (4), or `GermTreeEquality` (1). The triple theorem covers source `thm:A-R3E(i)`; the other five declarations are explicitly algebraic/local-response helpers for part (ii), not standalone proofs that every silent wall has zero jump. Comparison used `sm-2-amplitude.tex`, lines 588–652, and the actual germ/sides definition in `sm-1-polygons.tex`.

`g1_center_side_chi` assumes only G1 at the centre, not full genericity of that nongeneric point. Finite persistence supplies one common neighbourhood for every nonzero central chirotope. The three repeated-label cases are separately reduced to zero, while G1 supplies nonvanishing for each distinct triple. The chosen positive parameter δ/2 lies within the common radius; either sign of that parameter is covered. Continuous generic-side chirotope constancy then extends the central values to every point on each entire side. No crossing-order assertion or generic-centre premise enters this proof.

`triple_wall_tree_data` derives the required G1 from the actual `TripleAt` condition `pointZeros = ∅`. Its result `TreeDataEqual` expands to equality of both ordinary and root composition weights for **every** boundary interval and **every** interval composition, equality of **every** open sum, and equality of the complete rooted tree coefficient. Leaves and unary compositions are not excluded. The root and the positive/negative side parameters are arbitrary and independent. `tree_data_eq_of_chi` derives these equalities from the actual near/far signs and the complete recursive expressions. This covers all quantities stated in source part (i), without assuming their equality or depending on crossing-visit order.

The first two silent factor lemmas use a positive epsilon on a specified nonleaf gap: its U factor is precisely the unit array E, whose value there is zero. The other factor may have any `SignType` value; no coefficient is divided out or assumed nonzero. The third lemma handles two nonleaf gaps and the explicit disjunction that at least one epsilon is positive. It proves only the U product vanishes, which is exactly what the proper-span response needs.

The fourth factor lemma requires opposite epsilon pairs (+,−) or (−,+) and both gaps nonleaf. In each case the U product has a zero E factor on one side, and the V product has a zero E factor on the other. It proves both products vanish, as required by the **full-span** response. Merely proving one positive epsilon would not suffice for that branch; the candidate does not make that mistake. The nonleaf hypotheses preserve the formal-leaf value one. B remains the complete integer gap output with derived G1, and these lemmas do not assert integrality of inverse coordinates. Their kernel `decide` only checks the closed finite inequality of the two `SignType` values.

`tree_sides_equal_of_local_zero` exposes its full premise: one δ with positive value, δ≤radius, and zero jump for every sufficiently close independently chosen negative/positive parameter pair. It constructs δ/2 explicitly, applies that proved premise, and converts the integer zero difference to equality. It transports the positive and negative coefficients separately using **all** chirotope values along their continuous generic side families. The resulting s and t range independently over the full positive side-parameter interval; `sideTime false` reads the actual negative parameter. Positivity makes the local premise usable, so the argument is not vacuous. The helper does not itself assume or establish the geometric silent-wall response, and it does not assert constancy of open sums at a point-triple wall.

Verified receipts: `TripleTreeData` first root **97775**, exit **0**, **3/3** files; `SilentIntegerFactors` first **44434**, exit **0**, **8/8**; `GermTreeEquality` second **29206**, exit **0**, **3/3**. Every bound body is embedded once in its prototype. All seven successful traces contain only `propext`, `Classical.choice`, `Quot.sound`, with no `error:`, `sorryAx`, `native_decide` or `Lean.ofReduceBool` marker in the successful logs.

The preserved first `GermTreeEquality` run **44970** failed at two missing `PreconnectedSpace` instances. Its body is byte-for-byte identical to the passing body. The sole prototype change replaces `import SM.WallGerm` with `import SM.GermSides`; that canonical module proves `ConnectedSpace` for the actual open side interval using `isConnected_Ioo`. This is an import repair, not a new premise or an assumed connectedness axiom. The first failed log is preserved separately and is not counted as passing evidence.

| Bound file | SHA-256 |
| --- | --- |
| `work/checks/TripleTreeData.body.lean` | `34f289b190ef8c9a35d1277fab4ef45d261b11c8021b618f517dd6e304aa0cc4` |
| `work/checks/TripleTreeData.prototype.lean` | `c723a675a066d4b43f739c3b15b455b4cebed758bde3563544ad26063c5c773f` |
| `work/checks/TripleTreeData-first-kernel.log` | `35f712f375d0d32197cc058f0f3d1858449477e57ae1d6210c2c5390812f23d3` |
| `work/checks/TripleTreeData-prototype-result.json` | `e7802fb9eb6de777a6c7644fccf5c8d8832b7a13e53a8cb4f3b12c0356fcfbff` |
| `work/checks/SilentIntegerFactors.body.lean` | `52225243bc48a9a04c37f1fe92c52f28819033adc222a2d41a43fde9e6be3552` |
| `work/checks/SilentIntegerFactors.prototype.lean` | `9e79c4e82b95c6409922dd48c02c52cc1b014cadc1a032b8b26975daf3b71206` |
| `work/checks/SilentIntegerFactors-first-kernel.log` | `4edbb16a70ed66eeabee9e350a86e1684fa034f84142c25aec371f4239d85353` |
| `work/checks/SilentIntegerFactors-prototype-result.json` | `b24921635ecd5fe0ea6743a0fd38ddc3d54b21ea2f7b7d1e0524e4901435c303` |
| `work/checks/GermTreeEquality.body.lean` (also preserved first body) | `23ae56adbfd3faec1538d1ba80c8471b33b31d62afb85d5d77e6ef8daeb9bc0d` |
| `work/checks/GermTreeEquality.prototype.lean` | `faa7842204112735aa13778153264a042ccadd8941ddea060b9438b599a8fae2` |
| `work/checks/GermTreeEquality-second-kernel.log` | `3ed27eb4f685d1842aa4cd5cff8d04d88d6a609673358ef8a4d7ed5c68900090` |
| `work/checks/GermTreeEquality-prototype-result.json` | `f486a7d2c247f068cb235185bfd3c8a4722cffd325180e0c1de24f7bff83cae4` |
| `work/checks/GermTreeEquality-first.prototype.lean` | `8668fa122c4a61e0d32ef1f4c0e6fdf2ffa51f30c7d952f5aec53756fb6e8f6b` |
| `work/checks/GermTreeEquality-first-kernel.log` | `ab73e731920d14ddc8976b0c0c8e0996b54a93606c3207d5b9d81289e60e7ed4` |
| `work/lean/SM/TreeChamber.lean` | `a9a657675002c2f2ca28cbcc790de3f235e3561a28c44209b6341df8baa88961` |
| `work/lean/SM/FiniteChiStability.lean` | `7160db9c4ac930a64c65ce44b9e9a41d4f139a3442a49604b3c96f9a347cadc9` |
| `work/lean/SM/GermNeighborhood.lean` | `b5b30d800215dde4ff3a11d04b16a261501f6736224807df97a434a2aed0ca5a` |
| `work/lean/SM/GermSides.lean` | `a95418d15b11a300c5e6a88cbb43ecd9877b5fd061dab754e2efc19eac625d0a` |
| `work/lean/SM/TreeCoefficient.lean` | `d070e70dfbb61e036641f0d5fac4adae83fd1cadfe22f3ce2ffd8c8e1de9ab06` |
| `work/checks/IntegerCriticalGaps.body.lean` | `0ad1c8c46a927d04c736b49f06a092028463264675fd2a2a0d85420f638cba05` |
| `work/checks/FlatIntegerFactors.body.lean` | `b441262771ca2212a4200a18b0dc3f8334cde9180f3085769ccccbeabdbf696d` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |

Receipt hashes bind the remaining verified evidence entries. Passing checks and hashes do not themselves establish source fidelity. Stronger statement-fidelity approval remains pending; acceptance is unchanged at **39/192 (20.3%)**, targets **0/8**.
