# Tree path gluing: technical review

2026-09-11. Reviewer: another agent of the same currently available model, independently reviewing four root-authored declarations. This is **not the stronger-model statement-fidelity approval requested by the user** or source-claim acceptance. No Lean/kernel/build, proof edit, canonical edit or acceptance-map change was performed. The reviewer authored the dependency `WeakCenterSilent`; root separately reviewed that dependency in `weak-center-silent-technical-review-20260911.md`. This report does not represent an independent review of that self-authored dependency.

**Finding:** no mathematical or domain defect found. The final declaration proves equality of the original integer tree coefficients at generic endpoints of any actual continuous path in the weak locus, for each fixed arbitrary physical root. It discharges the path-density, local agreement and event-classification premises used by the earlier helpers.

`WallGerm.silent_tree_parameter_value` unfolds the actual `Silent` predicate as an exterior-extension or pure-cut wall. The corresponding proved full-side theorem gives exactly the cross-side equality required by `tree_parameter_eq_positive_of_sides_equal`, for independent side parameters and the same root. Thus the cross-side premise is proved at this application; no local-zero-response assumption is passed in by the caller. The full punctured germ domain is retained.

`tree_path_pair_near_silent_event` uses the actual centre equality to show that the event parameter is nongeneric. Every generic parameter in the open ball of germ radius is consequently different from that event parameter. Its real difference from the event lies in the germ domain and is nonzero. The full shifted-path premise identifies the corresponding entire curve tuple, using `shifted_curve_eq_path`; equality of the resulting `GenericTuple` values then transports the dependent coefficient. Both generic parameters therefore have the value at the same genuine positive-side reference `sideBase`, proving pairwise equality throughout that open ball. Neither continuity of p nor an ambient density assertion is needed for this local germ argument.

`tree_path_constant_of_silent_germs` defines the dense domain to be the **actual generic path parameters**, and f to be their actual rooted integer coefficients. It proves density from the given shifted punctured-generic germs. At every parameter, generic and nongeneric cases respectively supply the local generic persistence neighbourhood or the just-proved silent-event neighbourhood. These establish all local-pair premises before applying `dense_local_pairs_constant` on the connected unit interval. The event hypothesis is explicit in this intermediate lemma; no generic interval segment or zero jump is merely presumed. Finiteness of events is not needed by this valid local-to-global argument.

`tree_coefficient_eq_along_weak_path` constructs a relative-general-position path with one derived positive Euclidean tolerance and weak membership at every parameter. Its actual `event` field supplies the centre equality, the full shifted-curve identity and simplicity at each nongeneric point. Transporting weak membership to the actual germ centre permits `silent_of_simple_weak_center` to derive E/C classification. The event premise of the preceding gluing theorem is therefore discharged. Finally, the exact endpoint identities of the constructed path give whole `GenericTuple` equalities; applying the coefficient function transfers the result back to both original endpoints, including their G1 proof witnesses.

The final theorem assumes only n≥3, an actual continuous original path, its pointwise weak membership, generic endpoints and an arbitrary root. It adds no caller-supplied regularity, perturbation, event certificate, silent response, R identity or root-independence premise. It proves the path argument of source `thm:A-continuation` (lines 656–692). The remaining source steps—joining generic points within a visible component, choosing a generic representative in every component, and constructing and proving uniqueness of the extension—are not claimed by these four helpers. All coefficient evaluations here occur on generic tuples; no gate is evaluated at a silent zero.

Verified successful receipt: second root **5804**, exit **0**, **63/63** bound hashes match; the exact body occurs once in its prototype. All four successful traces contain only `propext`, `Classical.choice`, `Quot.sound`; no `error:`, `sorryAx`, `native_decide` or `Lean.ofReduceBool` marker occurs in the successful log. The preserved first run **91465** was an invalid import environment. The entire body is byte-identical to the first body; the exact prototype diff adds only `import SM.SilentCenter`, supplying the actual `Silent` definition. Failed-run traces, including any unresolved/self-name artifact, are not used as successful evidence.

| Bound file | SHA-256 |
| --- | --- |
| `work/checks/TreePathGluing.body.lean` | `326e810eb8199deadf18bef44c54d99b960d1b5fb0774a5d9a99fbafaabf4269` |
| `work/checks/TreePathGluing.prototype.lean` | `c3cc33e30ccdb148c11ee2523f84d438cab9ed6a069b13456312c94bdf400a4d` |
| `work/checks/TreePathGluing-second-kernel.log` | `83177fd4782da8f1774365fc31560b3e04544027d4170cb2f9965342bdbdc0b6` |
| `work/checks/TreePathGluing-prototype-result.json` | `5fb4ab05bcabd7943e37403eda420b36030ab22c4ae54d17a7006c02da00e641` |
| `work/checks/TreePathGluing-first.body.lean` | `326e810eb8199deadf18bef44c54d99b960d1b5fb0774a5d9a99fbafaabf4269` |
| `work/checks/TreePathGluing-first.prototype.lean` | `9d84ab98043a08e377e486af81ab37596abaed96e9957cc5c3633debcee451c5` |
| `work/checks/TreePathGluing-first-kernel.log` | `9648403ed9e961efc29c56454aade27657e3a8a3165aad51b4b135ade47918f3` |
| `work/checks/TreePathLocal.body.lean` | `8e092c2403ebcc45dc96d7df151fccf60c423d9930f3d186ff960a744f656f87` |
| `work/checks/DenseLocalPairs.body.lean` | `11f2384626f702549dd37b874ba665a326f9613c768fcc5dbfe15b3ba1f48cdc` |
| `work/checks/GermPathGeometry.body.lean` | `14149417adc4b8a116d6ba9e8bce6f8d1ba9f9c00acd0a57edbe6cc760003e41` |
| `work/checks/WeakPathTolerance.body.lean` | `7fcea08ceee8dbba853a89a8d7f0da76ffd265b3700e607f2833ab0a78b283c5` |
| `work/checks/WeakCenterSilent.body.lean` | `71fb7d0b8cea85738641274219121ed0c5f29c78f852df43f2c586b159d2c561` |
| `work/checks/ExtensionTreeResponse.body.lean` | `269dbcdda2e731c4f84b40b79966e45e5f9299588f801993d222c85aab327716` |
| `work/checks/PureCutTreeResponse.body.lean` | `9fc9c04cdc1d68c85753c66bec09d2f3ab17b2df766ecac4d984772afcf5872f` |
| `work/lean/SM/RelativeGeneralPosition.lean` | `1b0a8d1802d97de912b73baa08b718cf18732c75d42eba564d4f49dd1f3f5d3b` |
| `work/lean/SM/SilentCenter.lean` | `20fa33f369f6c9f588fb7c94d1828532f12b9c03c08daaae3524b547f5673d5d` |
| `work/lean/SM/WallGerm.lean` | `fca24dab7111c6b6f404b075ab4e1b8c20d2fb48083565b6ba89758ebf684f9b` |
| `work/reviews/weak-center-silent-technical-review-20260911.md` | `266a29f84ae07d56aeca52cc142c1aa358ace3dc1ef3141a530085f303fab2c5` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

The receipt binds the remaining embedded dependencies. Passing evidence does not establish stronger statement fidelity. Acceptance remains **39/192 (20.3%)**, targets **0/8**.
