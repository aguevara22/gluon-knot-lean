# Contact root partition — technical review

2026-09-11. Independent review by another agent of the **same currently available model**. This is **not stronger-model statement-fidelity approval** and supplies no original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8. Root authored the reviewed body; this reviewer ran no Lean kernel or build.

Reviewed all six declarations in `ContactRootPartition.body.lean` against the half-map rows in `reference/SM/sm-2-amplitude.tex` lines 387–394 and the root exhaustion in the `thm:A-S7` proof. No mathematical or domain defect was found.

- `contact_relative_offset_val` gives the exact representative after moving the origin from M to a. Put u = (g-M).val and d = (a-M).val. If u < d, the representative is u+n-d; otherwise it is u-d. Each branch proves its natural subtraction bound, its residue bound below n, and its cast equality before applying `val_natCast_of_lt`. It includes u=d, d=0, and wraparound; it does not use an invalid unrestricted cast/subtraction identity.
- `firstHalf_inherited_root_iff` identifies precisely u < d. The first-half vertices read M through a and have size d+1. The excluded child label -1 is its closing edge at a. Every earlier child edge, including the edge starting at M and the edge ending at a, is retained. The proof uses the actual cyclic-range offset and its proved successor formula; the converse obtains an actual child label and excludes -1 by the strict inequality.
- `secondHalfEdgeIndex_range_iff` gives the exact consecutive edge-label range based at a. `secondHalf_inherited_root_iff` removes its opening child label 0 and proves exactly d < u. Positivity of the nonzero child representative and the explicit offset formula rule out the wrapped branch. Conversely, the strict bound constructs a child label with the original root and proves it is nonzero. In particular the final child label is retained, so the original edge ending at M is included.
- `contact_root_cases` applies natural trichotomy. Equality u=d is converted through the exact casts to g=a; the other branches supply the actual inherited child labels. `contact_root_cases_disjoint` proves all three pairwise exclusions using the two strict inequalities. Child-label uniqueness also follows from the existing injectivity of the index maps; no ambiguous duplicate root slot is introduced.

The six theorems are combinatorial and require only n nonzero. They impose no geometric genericity, separation, affine coordinates or extra source arity. In the source contact domain, `ContactSeparated` and the source size condition give both nontrivial halves; the broader combinatorial statements do not narrow that domain. The resulting rows are exactly the contacted edge a, the original M-to-a arc with roots M through a-1, and the original a+1-to-M arc with roots a+1 through M-1. This file establishes the partition of labels; directed endpoint preservation is reviewed separately in `contact-half-roots-technical-review-20260911.md`.

## Evidence and repair

All **3/3** receipt hashes match current bytes; the body is embedded verbatim exactly once in the prototype. Root's second session **71853** exited 0, with all six traces using only `propext` and `Quot.sound`. The passing log has no `error:`, `sorryAx`, `native_decide`, or `Lean.ofReduceBool`.

First session **15257** is preserved with an unresolved arithmetic goal and a subtraction-cancellation type mismatch, followed by three affected `sorryAx` traces. All six statement texts before `:= by` are byte-for-byte unchanged. The proof repairs specify M,a,g in two offset rewrites and use `sub_left_injective` for the common-subtrahend equality g-M = a-M. They change neither the offset formula nor the partition domain.

Principal SHA-256 bindings, relative to the focused root:

| File | SHA-256 |
|---|---|
| `work/checks/ContactRootPartition.body.lean` | `efecdb4cbb8581ed5fd9a922eaeb66ecfa44d2d2fcd6ae041a2e3f43c4b1504a` |
| `work/checks/ContactRootPartition.prototype.lean` | `b25eb4d681c5158f81125d1c960d36d71bfabe9840449ec0accedabfd08e52dd` |
| `work/checks/ContactRootPartition-second-kernel.log` | `3eb911e9006c119d4ce07f6be1b93a88bfffa8e0ebe1a482736f299811d93b24` |
| `work/checks/ContactRootPartition-prototype-result.json` | `e719987c56dd1e42b64ef0d3d1271d6ed13b9c8343a738ddb983b044749fbe2e` |
| `work/checks/ContactRootPartition-first.body.lean` | `e864660a057f144ba58f1ab25361134afe6436e6a0cd6c08d94f740852310921` |
| `work/checks/ContactRootPartition-first.prototype.lean` | `c985c4fb61616dd4242b4edcc7d5f1c2117baf971d18cb98fc2ecc71879ae993` |
| `work/checks/ContactRootPartition-first-kernel.log` | `82bfe674324676fbb97cc1a148ca3e7087e558c0cec2a76bd5f124b2dfd9971f` |
| `work/lean/SM/ContactHalfSizes.lean` | `801a5afe127b3640e922847d052696e88e2998c4e92bbc8af4b851291c1c1140` |
| `work/lean/SM/ContactHalfIndices.lean` | `137e1b2a30581d4ce11cee87a7b59c60b7cad24f039ee6a822f30559e2446323` |
| `work/lean/SM/ContactHalfSupport.lean` | `f94f82e56972e033764bdb061aac053a963a836d6351b4797576674691469ca8` |
| `work/lean/SM/CyclicRangeIndices.lean` | `f45ef2301f77291c3be946076128fac7b337881fa1b2013f5400372bdbe3541d` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Hash agreement and successful checks identify artifacts without establishing source fidelity. No proof, frozen evidence, canonical/source file, map or acceptance status was edited.
