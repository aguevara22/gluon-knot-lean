# Exterior-extension tree response: technical review

2026-09-11. Reviewer: another agent of the same currently available model, independently reviewing five root-authored declarations. This is **not the stronger-model statement-fidelity approval requested by the user**, and not source acceptance. I authored the extension affine signs and the reused contact boundary/sign/support dependencies; this review checks their application, with their independent proof review supplied by the root agent. No Lean/kernel/build or frozen/canonical/map edit was performed.

**Finding:** no mathematical or domain defect found in the three root-case near responses, the all-roots near response, or `extension_tree_silent`. They cover the exterior-extension portion of source `thm:A-R3E(ii)`, including both exterior ranges and every physical root, with arbitrary independent full-side parameters in the final statement.

The caller gives only an actual `WallGerm`, `3 ≤ n`, and `ExtensionAt M a`. This retains the source remoteness condition, sole point-zero support, empty concurrence set, a point on the actual edge line but outside the **closed** segment, and the actual sign change. The affine scalar and nonzero direction B−A are constructed from those hypotheses through `extension_exterior_affine`; no interior contact, `VertexEdgeAt`, `CuspAt`, `FlatAt` or chosen affine data is assumed. The resulting scalar is strictly below zero or above one, and all three coordinate inequalities required by the single-triple theorem are proved.

The reused `contact…Triple` and support/order lemmas are label-based consequences of `ContactSeparated`. Their application here does not require a contact point inside the segment. The sign-change transport likewise needs only the exact cyclic critical label order and the supplied sign-change observable. This is why the same three root cuts remain valid for exterior geometry.

| Root case | Source specialization actually used |
| --- | --- |
| g=a | Cut B,X,A with coordinates (1,r,0), full span and two nonleaf gaps. For r<0 the epsilons are (+,−); for r>1 they are (−,+). Thus each of the U and V products contains a zero nonleaf E factor. Both terms of the full-span sum vanish. |
| `(g-M).val < contactDistance M a` | Cut A,B,X with coordinates (0,1,r). The right gap is nonleaf, and its epsilon is positive in both exterior ranges. Its U factor is zero. The span is proper, so this zero product annihilates the actual contracted coefficient. |
| `contactDistance M a < (g-M).val` | Cut X,A,B with coordinates (r,0,1). The left gap is nonleaf and its epsilon is positive in both ranges. Its U factor is zero; the proper-span formula gives zero output jump. |

The nonleaf counts and proper/full facts come from the exact cut positions and separation bounds. They are not extra geometric hypotheses. The all-roots proof first separates g=a, then the first strict inequality. In the remaining case equality of the representatives would imply g=a by `ZMod.val_injective` and subtraction injectivity, so the second strict inequality follows. This includes the inherited endpoint roots and the cyclic seam; no contact-adjacent edge is omitted. The source remoteness condition excludes the consecutive flat/cusp configurations rather than silently extending this silence assertion to them.

The proper branches keep the single-triple theorem's actual contracted tuple and derived G1/arity witnesses. Since the multiplier is zero, no named-half tuple equality, half genericity premise, root invariance or nonzero coefficient cancellation is needed. The full branch explicitly kills both U and V products. All factors are the proved integer outputs; inverse coordinates are not claimed to be integral.

Every near statement supplies one positive common radius before quantifying over independent negative and positive parameters. The final theorem applies the already reviewed `tree_sides_equal_of_local_zero` to the **proved** near response, obtaining equality for arbitrary s and t in the full side interval by separate chirotope transport along each continuous generic side. It has no remaining local-radius premise and asserts only equality of the complete tree coefficient, not of open sums or composition weights at this point-triple wall.

Receipt records first root session **63236**, exit **0**. All **53/53** manifest hashes match; every bound body occurs exactly once in the prototype. The five expected declarations have only `propext`, `Classical.choice`, `Quot.sound` in their traces; the successful log contains no `error:`, `sorryAx`, `native_decide` or `Lean.ofReduceBool` marker. This is evidence for the frozen candidate, not stronger source approval.

| Bound file | SHA-256 |
| --- | --- |
| `work/checks/ExtensionTreeResponse.body.lean` | `269dbcdda2e731c4f84b40b79966e45e5f9299588f801993d222c85aab327716` |
| `work/checks/ExtensionTreeResponse.prototype.lean` | `10761d1a6ce9580b17734b45b88245a4b911ab36be29e90e8e0150bb5b1e2741` |
| `work/checks/ExtensionTreeResponse-first-kernel.log` | `31c4228ab2324ad0ebd63ee3e996df4470d97d4296dd75c22847426850aecd0a` |
| `work/checks/ExtensionTreeResponse-prototype-result.json` | `33db1eb18a381d66745bba437978ebf4694a927dcaa557d67411eaab67f359fe` |
| `work/checks/ExtensionAffineSigns.body.lean` | `02971d5e80a6f6e46f17ac15f2d2b18be1b0d7c47bed8ed501fec86baf011c5a` |
| `work/checks/ContactBoundaryPositions.body.lean` | `61d797a366cb8db5312ac0739037da47361b87eed4ed50e786ee3b72b7c2c4b7` |
| `work/checks/ContactIntegerFactors.body.lean` | `406f96eee710116768518910df04615235b4ee4842106b1d4d847dfd3fcb27e7` |
| `work/checks/ContactAffineSigns.body.lean` | `eb17b5a65fb80e38549b9c7be114cb000caf8469e6dc3a43265105e5ab525b47` |
| `work/checks/SilentIntegerFactors.body.lean` | `52225243bc48a9a04c37f1fe92c52f28819033adc222a2d41a43fde9e6be3552` |
| `work/checks/GermTreeEquality.body.lean` | `23ae56adbfd3faec1538d1ba80c8471b33b31d62afb85d5d77e6ef8daeb9bc0d` |
| `work/checks/IntegerSingleTripleResponse.body.lean` | `227462b1bbe0456ce83377b04e35bc6d78ef8aed641200b783f83f9779d4d130` |
| `work/lean/SM/NamedWallPredicates.lean` | `828a9c5dc91455d6d171a01c0ece96901708dd9720f3a379563850b0a61e7513` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

The receipt binds the remaining verified files. Source comparison covers the exterior argument at lines 607–632 and the proper/full formulas of `thm:single-triple`. Stronger statement-fidelity approval remains pending; acceptance is unchanged at **39/192 (20.3%)**, targets **0/8**.
