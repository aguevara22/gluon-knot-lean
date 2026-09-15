# Full silent line-gap candidate: technical review

Independent comparison of root-authored SilentLineGap's two final declarations by another agent of the **same currently available model**. This is **not the stronger-model statement-fidelity approval requested by the user**, and does not accept the source claim. I authored the separate FiniteLineGaps abstract order helpers; root independently reviewed those in `finite-line-gaps-technical-review-20260911.md`. My review of the final assembly is therefore not independent authorship review of that dependency. No Lean kernel/build was run and no frozen proof, source, canonical module, or map was edited.

Compared both complete theorem types and their proofs with both conclusions and the full argument of `reference/SM/sm-2-amplitude.tex:795–842` (`pf:line-gap`). No mathematical defect, unproved assembly premise, or extra source-domain restriction was found.

- `silent_line_gap` retains every root `g`, WeakGeneric on the actual polygon, source polygon size `3≤n`, at least three selected vertices (`2≤k`), and the actual strictly increasing map `Fin(k+1) → Fin n`. It accepts arbitrary real affine coordinates representing all those points. Distinct coordinates and a nonzero endpoint difference are **derived** from weak vertex/index injectivity; no G1, regular perturbation, sign convention, or restriction to only one collinear triple is added.
- With boundary word length `n`, the source's `N` is `n-1`; Lean gap `j:Fin k` is printed gap `j+1`. The output is exactly epsilon `+1` and natural-position difference at least two for some open selected gap. The second conclusion additionally requires precisely `r_0=0` and `r_k=n-1`, then gives epsilon `-1` and the same nontrivial-gap inequality. No full-word premise is attached to the positive assertion, and no negative assertion is claimed on a mere subinterval.
- The proof normalizes arbitrary input coordinates by their actual endpoint difference and changes the affine origin/direction pointwise. This covers both positive and negative original endpoint differences. Exact epsilon equivalences use the source ratio itself, not an unnormalized difference whose sign could disagree.
- Its leaf predicate is the concrete position equation `r(j+1)=r(j)+1`. Every no-interior-point condition, consecutive-leaf exclusion, physical-root closing exclusion and first/last nonleaf condition supplied to the abstract order theorem is derived from WeakGeneric and the actual selected point equations. The only closing edge used is `g → g+1`, from the last boundary point to the first. In particular, there is no caller-supplied finite-order oracle or assumed combinatorial separation.
- For any returned nonleaf gap, strict monotonicity proves the next natural position is strictly larger. Since their difference cannot be one, elementary natural arithmetic gives a difference at least two. Thus the helper's abstract nonleaf conclusion is converted to the exact printed leaf count, including the minimal selected size `k=2`; no truncation of natural subtraction hides a reversed position.
- `silent_line_gap_of_collinear` supplies the additional source-facing route from actual zero determinants. It constructs the endpoint-direction dot-product coordinates, proves their injection and endpoint values zero/one, and applies the first theorem to the proved affine representation. The determinant condition is a concrete expression of membership in the selected affine line because the actual endpoints are distinct. This wrapper does not replace the first theorem's arbitrary-coordinate coverage.

The positive abstract helper follows the source maximum/second-maximum argument. The negative helper uses the closing-edge exclusion and the derived first/last nonleaf conditions to keep the maximum and its next decreasing step inside the open list; a second successive decreasing leaf then contradicts the actual turn condition. This is a finite-list reformulation of the printed cyclic argument, with all additional helper premises discharged by the final proof. Root's nonauthor review of the three abstract helpers is explicitly bound below.

Root second23877 exited0. All 8/8 receipt-bound hashes match; each of the six embedded bodies occurs exactly once in the final prototype. Both final traces contain only `propext`, `Classical.choice`, and `Quot.sound`; there are no error, sorryAx, native_decide, or Lean.ofReduceBool markers. The first10149 failure is preserved. Comparing both bodies and prototypes shows exactly one proof-line repair: the implicit index of `Fin.castSucc_lt_succ` is inferred from an explicit result type. Both theorem statements are unchanged.

This completes this review of the candidate's two `pf:line-gap` clauses only. The subsequent formal-cancellation lemma, polynomial claims and final corner targets are not proved or accepted by these statements. Stronger statement/definition fidelity, controlled integration and source acceptance remain separate and pending.

SHA-256 bindings (relative to the focused root):

| File | SHA-256 |
|---|---|
| `work/checks/SilentLineGap.body.lean` | `466edcf63484a6e2f4d41a038164383d6d0e216c325c964ad41b27cfa433f5a7` |
| `work/checks/SilentLineGap.prototype.lean` | `dba7fc69a3ec6f73d4e8f436fb6f48f00b4e0782a5a64eb73e66f196705de5c7` |
| `work/checks/SilentLineGap-second-kernel.log` | `cde9179e2770705e5a66d5adefd6e2bdc641b2b7f8a1bd54d11b345892a6381b` |
| `work/checks/SilentLineGap-prototype-result.json` | `695911f691576f830c64010e2b33eced7a99c606a891864a7abd65a4724fa268` |
| `work/checks/SilentLineGap-first-failed.body.lean` | `95e3b2f4b430092ec8b64fe582d2141d7445ccfbaa2ffd3af4be690ddd668b07` |
| `work/checks/SilentLineGap-first-failed.prototype.lean` | `9f58e1d0853f2e3413b77cc3f1080865cc9f426ceccaebd23162ab74723c1c46` |
| `work/checks/SilentLineGap-first-kernel.log` | `a13920cb7d7568f23060f0432c9e874ccaad0622cdd49964cb69943814e5ae2f` |
| `work/checks/FiniteLineGaps.body.lean` | `9d7d3e76bb2e142b2e675922d663fa116ab03ba6e3908fd8ec809e8b980ed2bd` |
| `work/checks/FiniteLineGaps-prototype-result.json` | `ab121e54b1f25b6cfd95358d34978af99b0f5204aca2c61d37f474f20d384f93` |
| `work/reviews/finite-line-gaps-technical-review-20260911.md` | `e9c3e5eac643bbd0a9554a6ce386d57b1f89d84e30c3b4b41dd50546079fae23` |
| `work/checks/WeakLineGeometry.body.lean` | `33fa407bf8a5c37dd2c9459d56e50cb3c48faa85f48076f679a2197694135dc3` |
| `work/checks/WeakLineSelections.body.lean` | `a91324f0380378fd48fcecea0bb1642f52dcdcc9fbfd45c626d43209cc6782c5` |
| `work/checks/LineCoordinateNormalization.body.lean` | `95806b56f50651011b05d31989e3ce43076c9a129ac9a7de6f0f08d903c37797` |
| `work/checks/WeakSelectedLineCoordinates.body.lean` | `a711895a3661f741753269d46d480168b15840561b488d7a8ebd78c17b431d3b` |
| `work/reviews/weak-line-geometry-and-selections-technical-review-20260911.md` | `37b0b80802924ba2d39f71b68b1870114f05424764734f18302fec95e5ccf64a` |
| `work/reviews/line-coordinate-normalization-technical-review-20260911.md` | `e5d17671f8cb44b3aef304a43f29edceddacf348868fae6d537bb4b40aba6a6d` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |
| `work/lean/SM/WeakGeneric.lean` | `1a72ebddb4ddb4d72a89f14a5fede9badc3dbed095a972f6dd1b85db30789b22` |
| `work/lean/SM/RootBoundary.lean` | `604906b750e1ab198a2db3fc3cc011ab325493a91404a0b52ffe4583dd403f1a` |

Accepted progress remains 39/192 (20.3%); target acceptance 0/8.
