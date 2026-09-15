# Triple and silent tree laws: aggregate technical review

2026-09-11. Reviewer: another agent of the same currently available model, independently reviewing the root-authored `SM.tree_triple_and_silent_laws`. This is **not the stronger-model statement-fidelity approval requested by the user** and does not accept `thm:A-R3E`. I authored some geometry dependencies, whose independent review is recorded by the root agent; this report reviews the final aggregate and its application of the separately reviewed responses. No Lean/kernel/build or frozen/canonical/map edit was performed.

**Finding:** no defect or omitted clause found in this candidate aggregate for source `thm:A-R3E` (`sm-2-amplitude.tex`, lines 588–652). It assembles all three required assertions without adding a local-radius or geometric premise to callers. It is not the final corner theorem or an R/BRIDGE identity.

The first conjunct assumes only the actual `TripleAt` predicate and supplies `TreeDataEqual` for every physical root and every independently chosen positive/negative side pair. The canonical predicate expands to equality of both ordinary and root weights for **every boundary interval and every composition**, equality of all open sums, and equality of the complete rooted output. Thus it includes formal leaves and unary compositions, not just a selected root sum. The supporting theorem derives G1 at the centre from the empty point-zero set, establishes all chirotopes on both sides from finite central persistence and same-side constancy, and then uses the actual gate/tree formulas. Crossing-visit order is not assumed unchanged.

The second and third conjuncts use exactly `ExtensionAt` and `PureCutAt`, respectively. They conclude only complete tree-output equality, correctly preserving the source's warning that the individual open sums need not remain unchanged at these point-triple walls. The extension theorem covers both exterior scalar ranges and all three exhaustive physical root cases. The pure-cut theorem derives physical distinctness and the gap/properness facts from the actual nonconsecutive singleton support and handles all affine orders, including a critical point at either boundary endpoint separately.

Every branch retains ambient `3 ≤ n`; any larger lower bound used internally is derived from its actual wall predicate. No root exclusion, caller-supplied affine data, child-genericity condition, zero-response assumption, nonzero amplitude assumption or chosen side witness appears in the aggregate. Both side parameters range independently over the entire `(0, radius)` domain: the positive tuple is evaluated at t and the negative tuple at −s. This is the source's full side interpretation, with no remaining closeness restriction. The two silence proofs derive their local zero responses before applying the explicit transport helper; the aggregate does not smuggle in its own conclusion as a premise.

The three conjunct proofs directly apply the separately reviewed `triple_wall_tree_data`, `extension_tree_silent` and `pure_cut_tree_silent` with the same root and parameters. Their detailed proof/source comparisons are recorded in `silent-algebra-and-triple-technical-review-20260911.md`, `extension-tree-response-technical-review-20260911.md` and `pure-cut-tree-response-technical-review-20260911.md`. No untranslated assertion within the two printed clauses was identified in this limited review. Stronger statement-fidelity approval and source acceptance remain pending.

Receipt records first root session **2126**, exit **0**. I recomputed all **57/57** manifest hashes without mismatch and checked that every bound body occurs exactly once in the prototype. The log prints the expected aggregate theorem with only `propext`, `Classical.choice`, `Quot.sound`; it contains no `error:`, `sorryAx`, `native_decide` or `Lean.ofReduceBool` marker. Passing checks and hashes do not themselves establish statement fidelity.

| Bound file | SHA-256 |
| --- | --- |
| `work/checks/TripleSilentTreeLaws.body.lean` | `d44fe4500b259ad724d6d71ff1c9f7f69c355ca978fc483414bde5d80ff7fe9f` |
| `work/checks/TripleSilentTreeLaws.prototype.lean` | `29b3e054fb4e3846c06b7814884597ad30355f596bb9734166430c7428b726df` |
| `work/checks/TripleSilentTreeLaws-first-kernel.log` | `99f4156e9639935bc0e39b4f6c2d9d7e232ad87601e5c5b13f9f8f4f6fe1916d` |
| `work/checks/TripleSilentTreeLaws-prototype-result.json` | `9f3f8416b2d8595355f7a73b7ce98c120417657863ecd9f320ffcce635182ebe` |
| `work/checks/TripleTreeData.body.lean` | `34f289b190ef8c9a35d1277fab4ef45d261b11c8021b618f517dd6e304aa0cc4` |
| `work/checks/ExtensionTreeResponse.body.lean` | `269dbcdda2e731c4f84b40b79966e45e5f9299588f801993d222c85aab327716` |
| `work/checks/PureCutTreeResponse.body.lean` | `9fc9c04cdc1d68c85753c66bec09d2f3ab17b2df766ecac4d984772afcf5872f` |
| `work/lean/SM/TreeChamber.lean` | `a9a657675002c2f2ca28cbcc790de3f235e3561a28c44209b6341df8baa88961` |
| `work/lean/SM/NamedWallPredicates.lean` | `828a9c5dc91455d6d171a01c0ece96901708dd9720f3a379563850b0a61e7513` |
| `work/lean/SM/WallGerm.lean` | `fca24dab7111c6b6f404b075ab4e1b8c20d2fb48083565b6ba89758ebf684f9b` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |

The receipt hash binds the remaining verified evidence entries. Acceptance remains **39/192 (20.3%)**, targets **0/8**; this review changes neither count.
