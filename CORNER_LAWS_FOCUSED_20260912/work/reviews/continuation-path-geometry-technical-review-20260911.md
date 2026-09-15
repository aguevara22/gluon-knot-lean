# Continuation path geometry: technical review

2026-09-11. Reviewer: another agent of the same currently available model, independently reviewing four root-authored declarations in `GermPathGeometry` and `WeakPathTolerance`. This is **not the stronger-model statement-fidelity approval requested by the user** or acceptance of `thm:A-continuation`. No Lean/kernel/build, proof edit, canonical edit or acceptance-map change was performed.

**Finding:** no mathematical or domain defect found. The helpers prove actual path-parameter density from shifted punctured-generic germs, an actual Euclidean tolerance for a compact path range, and a constructed relative-general-position path that remains weakly generic. They do not yet prove local tree-value agreement or the source continuation theorem.

`WallGerm.shifted_curve_eq_path` retains the exact pointwise shifted-path premise for **every** germ parameter. For a path parameter u within the germ radius of t, it substitutes the actual difference u−t; the absolute-value bound puts that difference in the germ domain. The real identity t+(u−t)=u, transported by subtype extensionality, identifies the entire labelled tuple at u. This is not merely equality at the centre or at two endpoints. In particular, the premise also fixes the central tuple when u=t.

`generic_path_dense_of_germs` assumes that each nongeneric path parameter has such an actual shifted `WallGerm`. At an already generic parameter, closure membership is immediate. Otherwise, for any positive neighbourhood radius, it chooses a positive q smaller than both that radius and the germ radius, using half their minimum. The shifted-path premise supplies the genuine path parameter t+q, and punctured genericity makes its tuple generic. The real distance to t is exactly q. Thus density is established in the actual interval parameter space, without appealing to ambient density or asserting the nongeneric event set empty.

The two-sided shifted-germ premise cannot hold at a nongeneric interval endpoint: one sign of a sufficiently small shift would leave the interval. This is consistent with the intended application, since `RelativeGeneralPositionPath` has generic endpoint collars. The helper covers endpoints via the generic branch, without discarding either endpoint from its density conclusion. Continuity of an arbitrary p is not an omitted hypothesis: the stated local germ data alone suffice for this density argument.

`euclidean_path_open_tolerance` sends the compact unit-interval path range into the actual Euclidean space of all 2n real coordinates. The continuous inverse coordinate map takes the open set S back to an open set containing that compact range. The compact thickening lemma supplies one positive radius whose entire thickening remains there. For every parameter, the original coordinate tuple is a witness that a uniformly close perturbed coordinate tuple lies in this thickening. Applying the inverse identity returns actual membership in S. The proof uses precisely the Euclidean distance occurring in the result, not the default product maximum metric. No separation distance or closeness bound is supplied by the caller; continuity of the perturbed function is unnecessary for this membership-only conclusion.

`weak_relative_general_position` applies that tolerance to the proved open weak locus. It derives regularity pointwise from the nonzero-turn clause of `WeakGeneric`, then calls the existing proved `relative_general_position` construction with the generated positive tolerance and the given generic endpoints. The resulting object is an actual `RelativeGeneralPositionPath`; its structure retains continuity, the fixed endpoints, the exact coordinate closeness, finite nongeneric events, generic endpoint collars, and actual shifted simple wall germs. Its `close` field supplies the tolerance premise, proving weak membership at **every** perturbed parameter. No caller-supplied replacement path, regularity hypothesis or event-exclusion certificate has been added.

The wrapper was checked against the concrete canonical structure and construction, rather than treating its name as a path-existence oracle. This review does not repeat the full historical proof audit of the canonical relative-general-position construction. Compared with the path perturbation step of source `thm:A-continuation`, these helpers supply the stated geometry. The later application must still establish the tree-value local-pair hypotheses and complete the chamber/gluing argument.

Verified receipts: `GermPathGeometry` second root **54231**, exit **0**, **3/3** hashes; `WeakPathTolerance` first **1291**, exit **0**, **3/3** hashes. Each body occurs exactly once in its prototype. All four successful traces list only `propext`, `Classical.choice`, `Quot.sound`; no `error:`, `sorryAx`, `native_decide` or `Lean.ofReduceBool` marker appears in the successful logs. The preserved germ first run **32126** failed only the radius-bound arithmetic. The exact diff adds `w.radius_pos` to that tactic's arguments; both theorem types are byte-identical to the first types. No caller premise was added.

| Bound file | SHA-256 |
| --- | --- |
| `work/checks/GermPathGeometry.body.lean` | `14149417adc4b8a116d6ba9e8bce6f8d1ba9f9c00acd0a57edbe6cc760003e41` |
| `work/checks/GermPathGeometry.prototype.lean` | `50a36c22da0adf213d05d4162b11c550128188589a3df9eb413ee89d3177579f` |
| `work/checks/GermPathGeometry-second-kernel.log` | `c9a256a0905d41bdf5252c9dd8d6203ca87220ce973263011066429d74aa054e` |
| `work/checks/GermPathGeometry-prototype-result.json` | `6eac8fb079d229a7dd397cf0fca94ee8f542bbaf66b40d682c7b9dd703963b03` |
| `work/checks/GermPathGeometry-first.body.lean` | `bf3fa8d51c042df2f7b259fe46d0e663c7103ce7e2d3d70046ccd358361cd44c` |
| `work/checks/GermPathGeometry-first.prototype.lean` | `2ac151e04c60db1593f9c511f1ccafd02a17161ed56359b7c046372b72e29b8a` |
| `work/checks/GermPathGeometry-first-kernel.log` | `2520d41780a423c26797d94182fac9c598965c9b3e9f9d2b55185c38d3471f5b` |
| `work/checks/WeakPathTolerance.body.lean` | `7fcea08ceee8dbba853a89a8d7f0da76ffd265b3700e607f2833ab0a78b283c5` |
| `work/checks/WeakPathTolerance.prototype.lean` | `662d5268cff26e777eda039ac12c283283ba3bbf7544ad3f9b936bc5d4b94a7b` |
| `work/checks/WeakPathTolerance-first-kernel.log` | `8651d029eba9e994045f66382c999bcb159ad33506926f27bcfae61f4d046200` |
| `work/checks/WeakPathTolerance-prototype-result.json` | `97a4c5efab3443e99f7a36098308b692e6aa1077b8749fa9caa79be640ac6809` |
| `work/lean/SM/WallGerm.lean` | `fca24dab7111c6b6f404b075ab4e1b8c20d2fb48083565b6ba89758ebf684f9b` |
| `work/lean/SM/RelativeGeneralPosition.lean` | `1b0a8d1802d97de912b73baa08b718cf18732c75d42eba564d4f49dd1f3f5d3b` |
| `work/lean/SM/EuclideanTuple.lean` | `acf79a23b262961b245ec4333627f06d02af2cbe74e9c3385ea237a98f016e69` |
| `work/lean/SM/NonFlatCenter.lean` | `79297e5edc3912d5dbaab3583f6e5dbb29f20935f183ace13dcc8c4feeea907b` |
| `work/lean/SM/WeakOpen.lean` | `d529ddd96240311708fe3a840c9fb4cf2692764943435b77dae59e5c56b79bd5` |
| `work/lean/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean` | `b26622a0d6f360634ded7777e87d60a923ede57399a7089b29012ca45d44d4a9` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Passing evidence does not establish stronger statement fidelity. Acceptance remains **39/192 (20.3%)**, targets **0/8**.
