# Positional decomposition: review of two proof repairs only

Reviewer: review_contraction_candidates, another agent of the **same currently available model**. I authored the original eight-declaration PositionalCutDecomposition construction and its SelectedCutRefinement dependency. Root authored the two repairs reviewed here. This is therefore **only a nonauthor technical review of those two repairs**, not an independent review of my original mathematical construction. Root is responsible for that separate construction/source review. This is not the stronger-model fidelity approval requested by the user and does not accept a source claim. I ran no kernel/build/audit and edited no proof body.

Read root's exact first43011 failure log and compared the preserved first-failed body/prototype with the passing versions. The only changes are inside `nearFarWeight_position_near` and `nearFarWeight_position_far`; all eight theorem statements and the remainder of the body are unchanged.

For the near-only proof, function extensionality proves that the synthetic array sending every triple to `-(2*0)` equals the actual zero TripleArray. Rewriting that complete array equality in `nearFarWeight_position_add` at a=0 gives the correct near-only weight. Simplifying `0+b` then yields the intended product.

For the far-only proof, function extensionality proves that the synthetic array sending every triple to `2*0` equals the actual zero TripleArray. Rewriting in the general identity at b=0 gives the correct far-only weight, and simplifying `a+0` yields the intended product. These are proved function equalities; neither inserts an assumption or changes a sign, factor, cut index, child interval, scalar domain or unary case. Both preserve the original construction and resolve precisely the Pi.zero transport errors reported in the failed run.

Root second64127 exited0. All 4/4 receipt-bound hashes match; both embedded bodies occur exactly once in the prototype. All eight traces use only standard foundations (propext, Classical.choice, Quot.sound, sometimes a subset), with no error, sorryAx, native_decide or Lean.ofReduceBool marker. These are inspected root receipts, not a reviewer kernel run. First43011 remains failed evidence.

SHA-256 bindings:

| File | SHA-256 |
|---|---|
| `work/checks/PositionalCutDecomposition.body.lean` | `ed59789e73793bd8b885ab65bd9096abe7065de2b7cd4386f19de6ff26a82b6d` |
| `work/checks/PositionalCutDecomposition.prototype.lean` | `5b179f40dba6858a80146a652d0658715067eacbb183a3397869420b24a191d2` |
| `work/checks/PositionalCutDecomposition-second-kernel.log` | `6bcb68dccb6d1fb76fef022b3f1187befc026f1fbebf33f8bbee4f86eb797a9a` |
| `work/checks/PositionalCutDecomposition-prototype-result.json` | `9b640c1217703f93148374b3f9940a8373810c62ae558ba312d7450c2661284e` |
| `work/checks/PositionalCutDecomposition-first-failed.body.lean` | `b2d4791ce6ad2a41846ce999b0cc99cecda860dc545064640d526559f7c04fcb` |
| `work/checks/PositionalCutDecomposition-first-failed.prototype.lean` | `e708eca3ae9fc7f6e8fcc04454593956db93cb7b62fa7d84be68e97aa4056d13` |
| `work/checks/PositionalCutDecomposition-first-kernel.log` | `57a1250ce4bd45a5f25bb8ed4ca2913e3bb85fe17a878ec678fac9461d00411e` |
| `work/checks/SelectedCutRefinement.body.lean` | `14813200d24d78c3da98cdc7508400e3b82251cfed19f4dddbf4f81cfe190b18` |

Scope is limited to the two repaired proofs. Stronger fidelity and source acceptance remain pending; accepted progress remains 39/192 (20.3%), targets 0/8.
