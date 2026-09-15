# Final cusp response — technical review

2026-09-11. Independent technical/source comparison by another agent of the **same currently available model**. This is **not the stronger-model statement-fidelity approval requested by the user**, and supplies no original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8.

Reviewed the two frozen declarations in `CuspSourceResponse.body.lean` against `thm:A-S4`, `reference/SM/sm-2-amplitude.tex` lines 455–520, and the actual cusp-side conventions and rotation proof in `sm-1-polygons.tex` lines 1024–1070 and 1198–1226. No mathematical defect, omitted root/arity case, or unproved normalization premise was found in this bounded comparison. The prior signed-response review covers its tree-response input. This reviewer authored the affine and generic orientation helpers; those were checked/reviewed by root as nonauthor and are not independently re-reviewed by their author here.

## Actual sides and rotation

`CuspCase` is the source's two central betweenness cases: case true has B strictly between A and M; case false has A strictly between M and B. `cusp_case_existsUnique` derives the unique Boolean from actual `CuspAt`, using its singleton zero support, source arity bound and exterior condition. The final theorem therefore does not ask the caller to choose or prove a case.

`cuspLoopSide` is selected by the **actual crossing** of the source newborn pair on the positive-time side at `sideBase`. The inspected `cusp_side_crossing_iff_loop` proves that this side, and only this side, has that crossing at every positive distance parameter. `cusp_loop_turns` identifies its turn with minus the sign of the actual central determinant and the opposite side's turn with plus that sign. These facts follow from local crossing control and constancy on the connected generic sides, not from an assumed tree response or a merely named Boolean. No empty-loop, unthreadedness or R premise enters.

The used `cusp_rotation_jump` is an existing proved theorem about the actual `rotationNumber`, defined as the sum of principal turns divided by 2π. Its proof uses principal-angle limits: other corners have the same center limits; the singular corner has the side turn sign times π. Integrality and connected-side continuity give rotation constancy, and uniqueness of the resulting limit identifies each side value. Subtracting cancels the common other-corner sum and gives the loop-side turn. This rotation argument has no tree-coefficient dependency. It neither assigns rotation to the singular center nor assumes differentiability.

## Two declarations and exact sign

`cusp_loop_tree_response` is the auxiliary result with a supplied, genuine central case. It returns the loop turn's two sign possibilities, its equality to the actual real rotation difference, and the integer tree response with minus that turn as multiplier. The cases are correct:

- If the loop turn is -1, the opposite turn is +1. Applying the negative-minus-positive coefficient theorem in that order gives the deletion coefficient; minus the loop turn is +1.
- If the loop turn is +1, the opposite turn is -1. The coefficient theorem is applied in the opposite order, and negating that integer equality gives minus the deletion coefficient; minus the loop turn is -1.

The calls pass actual `sideTime` parameters and their proved nonzero values. Numerical simplification and explicit unfolding of `sideTuple` identify their coefficients with the generic side tuples in the target. No sample is assumed to be symmetric or close to zero.

`cusp_tree_law` derives the unique central case, then defines **one integer κ** as the loop-side turn at `sideBase`, before quantifying any s, t or g. The rotation theorem supplies κ = -1 or κ = 1. `side_turn_constant` identifies every loop-side turn with that fixed base turn. `SignType.intCast_cast` identifies the real cast of κ with the same real sign in the rotation equation; κ is thus the **actual** rotation jump, not an unrelated integer sign witness.

For every independent pair s,t in the full interval `(0, radius)`, the theorem proves the actual loop-minus-no-loop rotation difference equals the real cast of κ, and for every physical root g the tree-coefficient difference is **-κ times the center deletion coefficient at `fusionIndex j g`**. These parameters cover arbitrary punctured representatives on the two named sides. There is no remaining proximity restriction or root-dependent κ. The output is in the integers, with exactly the source's scalar sign and no extra normalization factor.

The geometric premise is only `CuspAt`; it retains source parent arity at least four, the precise zero/concurrence conditions, exteriority and turn sign change. The n+1 parameterization covers every source size, including four, and the deletion has at least three vertices. Its G1, explicitly assumed in the printed theorem, is proved from singleton zero support by `g1_deleteVertex`. The actual cyclic deletion tuple and physical induced root are preserved by the earlier complete tuple and endpoint identifications; the argument assumes neither root independence nor a root transport theorem. The final two statements add no hypothetical response, rotation, emptiness or case oracle.

This matches the printed rooted cusp equation and its κ clause at the level of the inspected candidate statement and dependencies. It does **not** accept `thm:A-S4`, approve the entire source-to-formalization chain, or resolve the separate original shift-scope issue; stronger fidelity approval remains pending.

## Frozen receipt and repair

All **53/53** files in `CuspSourceResponse-prototype-result.json` match current SHA-256 values, and every listed body appears verbatim exactly once in the passing prototype. Root's second session **68098** exited 0. Both declarations print only `propext`, `Classical.choice`, and `Quot.sound`; the passing log contains no `error:`, `sorryAx`, `native_decide`, or `Lean.ofReduceBool`. This reviewer ran no Lean kernel or build.

First session **64876** is preserved with two type-comparison errors and downstream `sorryAx` traces. Both statement texts before `:= by` are byte-for-byte unchanged. The only repairs separate numerical sign simplification from `simpa only [sideTuple]` (and `neg_sub` in the reversed case), exposing the same raw curve/side-tuple identity. No definition, premise, side choice, coefficient or conclusion was changed.

Principal SHA-256 bindings, relative to the focused root:

| File | SHA-256 |
|---|---|
| `work/checks/CuspSourceResponse.body.lean` | `5bbd396809164ae91a05de4ce015c4c3c9c5e7cbf4d3e9742b4f196bd7e4426b` |
| `work/checks/CuspSourceResponse.prototype.lean` | `9f4eda2f252f695341403946d98ddcb23161fcdec70e5b3ea783bcac04392779` |
| `work/checks/CuspSourceResponse-second-kernel.log` | `a09fa92f9d4970e1b57cabadec020d33e174787012fedb46326929de41116e98` |
| `work/checks/CuspSourceResponse-prototype-result.json` | `6d62740907d68d7e67b23d0f6ef1884340b1bee6f1c986220c47cfc56ca5ac79` |
| `work/checks/CuspSourceResponse-first.body.lean` | `ffa54cdbd7ca724a218a0f1bed6f84da1d251ceb6a5f342c4f1d5bcb00e83629` |
| `work/checks/CuspSourceResponse-first.prototype.lean` | `113f8808b451d15fd0f2485eb9e777991bc4c4f90087fc25bf149c7e15258f6e` |
| `work/checks/CuspSourceResponse-first-kernel.log` | `21e39e470b071a5078a76ba80a8cbc8c44b772afbcd010031160b03773c5730c` |
| `work/lean/SM/CuspDefinition.lean` | `af2d8abcea1c4ac66b975b22e5d79d4c1e95a44e271923bb8323ab4a1a105bda` |
| `work/lean/SM/CuspSideCrossings.lean` | `1cadd1e929e21a591533a027bb0060476f4ce3306602158126ec0f3706480431` |
| `work/lean/SM/CuspTurnLimits.lean` | `054533981e64eec2da9ef807c6b1c77562e93a7cb37fb342d30c4d562345cc96` |
| `work/lean/SM/CuspRotation.lean` | `779e47f7ba8d751a0d8cfabbef6160b254db300abbf5a38e19e52f1634beb959` |
| `work/lean/SM/GermTurnSigns.lean` | `9bb2bc056bbddb1f7961f9392a9753759e62bff6fd023a89182f90c06a51ad85` |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Hashes and successful kernel evidence bind the inspected artifacts; they do not establish source fidelity. No frozen body, canonical/source file, map or acceptance status was edited.
