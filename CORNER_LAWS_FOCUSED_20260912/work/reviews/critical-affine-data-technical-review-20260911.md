# Critical affine data: technical review, 2026-09-11

Reviewer: `/root/review_contraction_candidates`, a separate agent without authorship of the candidate, using the **same currently available model** as the authoring agent. This is independent technical evidence only, **NOT the stronger statement-fidelity approval requested by the user**. No original source claim is accepted. No Lean kernel, build, or checker was run; the ongoing `SignedCriticalJump` candidate was not inspected.

Reported startup/completion checklist: **39/192 (20.3%)**, targets 0/8; the original shift-scope obstruction remains recorded.

## Finding

No defect found in `distinct_collinear_affine_data` or `critical_boundary_affine_data`. They explicitly construct the affine data requested in `reference/SM/sm-2-amplitude.tex:239–240`, including a nonzero direction and three pairwise distinct scalar coordinates.

1. **Actual construction from the determinant.** The first theorem chooses base point a, direction from a to c, and endpoint coordinates zero and one. Its middle coordinate is the dot product of the direction with the vector from a to b, divided by the direction's squared Euclidean length. The hypothesis that c differs from a proves the direction nonzero. `scalar_of_det_zero` applies after `det_swap` changes the supplied zero determinant to the required order; no sign or nonzero determinant is assumed.

2. **The quotient is justified.** `Plane` is concretely the real coordinate plane, and `planeDot` is its ordinary coordinate dot product. `planeDot_self_pos` proves the denominator strictly positive from the nonzero direction. In `scalar_of_det_zero`, the vanishing determinant yields each of the two coordinate identities after multiplication by that denominator; the proof divides only after establishing positivity. It thereby proves the middle displacement equals the constructed scalar multiple. This is an explicit coordinate proof, not an assumed collinearity or linear-dependence interface.

3. **Every required inequality is proved.** If the middle coordinate were zero, the affine identity would make b equal a, contradicting `hba`. If it were one, the same identity and the endpoint identity would make c equal b, contradicting `hcb`. The two endpoint coordinates differ because one differs from zero. These prove exactly the three output inequalities, as well as the separately established nonzero direction. No interval bound on the middle scalar is imposed: it may lie outside the endpoint coordinates, as the source's signed epsilon cases require.

4. **The boundary application uses actual points.** `critical_boundary_affine_data` obtains the actual `PointZeroTriple` from the singleton `pointZeroTriples` equality. Membership of the three root-read boundary labels in that support gives their zero chirotope; `sign_eq_zero_iff` gives the determinant equation on the actual boundary-word point differences. The wrapper then applies the constructed point theorem with all three physical point inequalities explicitly supplied.

5. **Arity three is preserved.** The wrapper has no arity-at-least-four premise and never infers physical distinctness merely from distinct labels or singleton support. An increasing triple ensures three distinct labels, while the three separate hypotheses concern their geometric point values. Thus the stated theorem applies at arity three when the source's physical distinctness condition holds. It does not use the invalid implication that singleton zero support alone makes all vertices distinct at that arity.

## Limits and evidence

This review concerns only the affine-data construction and its boundary wrapper. It does not prove sign-change normalization, choose a critical increasing triple from an unordered input, assemble the complete wall theorem, or approve final statement fidelity. The explicit physical inequalities match the source's distinct-wall-point requirement; callers must still provide them.

No proof admission, custom axiom, unsafe computation, or circular invocation was found. The word “admit” appears only in the English docstring describing existence of coordinates, not as a Lean tactic. The root log prints both expected signatures and only `propext`, `Classical.choice`, and `Quot.sound` as their axiom dependencies. This is inspection of root evidence, not an independent kernel run or a complete audit of compiled imports.

Python SHA-256 checks matched **all 4/4 recorded hashes** in `CriticalAffineData-prototype-result.json`. The target body and its `BoundaryTripleSupports` dependency each occur exactly once, byte-for-byte, in the prototype. The receipt records **root session 2001, exit 0, first run passed**, with zero source-claim acceptance increment.

| File, relative to focused handoff root | SHA-256 |
|---|---|
| `work/checks/CriticalAffineData.body.lean` | `eac6a342f4efb6e55da13322feab4e3f685e63828440ccc820297813971b5be1` |
| `work/checks/CriticalAffineData.prototype.lean` | `16e353f1eb27ab97eff49754618ab316539c458e31879f826ec9ad4bc0213756` |
| `work/checks/CriticalAffineData-first-kernel.log` | `dc73783d17db2811e99a3c5ebf61445d48fa00bc475471d38d138734d934ab0b` |
| `work/checks/CriticalAffineData-prototype-result.json` | `58dab6647c5d18a65dcacb41a15c1ff84af06685543fc1923b17657b933a741d` |
| `work/checks/BoundaryTripleSupports.body.lean` | `60199670494951bea511f187f7f894fd63fd4d074237e5b0442602e2c4f02e42` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Relevant canonical definitions and proofs inspected, with source-byte bindings:

```text
30a5956221225bc9811a792b5a67c6c5967fb6dda0b4cb14be997051b32b7a4f  work/lean/SM/EuclideanPlane.lean
e0225bc712162273f43269ed764ac4849ae8fcd8798245a367d4262858fbf575  work/lean/SM/Chirotope.lean
d0b5d37591c252d66e1a3f060cea1e3d58625fedd6c5491cf4c1cf6d2b8c149d  work/lean/SM/Polygon.lean
5930e77bd3eb05d371b5226c226d9caa464f99d0be48038b1154d02c623dc2c8  work/lean/SM/SinglePointTriple.lean
33e64bb519d61fdb2d9e7613cd42af12831246e5774276ca5e2e21f63ea2c23a  work/lean/SM/ZeroTriples.lean
```

Only this report was created. No Lean body, canonical source, map, or status file was edited.
