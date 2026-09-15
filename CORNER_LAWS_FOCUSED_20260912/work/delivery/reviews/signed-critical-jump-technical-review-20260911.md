# Signed critical jump: technical review, 2026-09-11

Reviewer: `/root/review_contraction_candidates`, a separate agent without authorship of the candidate, using the **same currently available model** as the authoring agent. This is independent technical evidence only, **NOT the stronger statement-fidelity approval requested by the user**. Original source acceptance remains pending. No Lean kernel, build, or checker was run, and the assembling single-triple candidate was not inspected.

Reported startup/completion checklist: **39/192 (20.3%)**, targets 0/8; the original shift-scope obstruction remains recorded.

## Finding

No defect found in the four declarations of `work/checks/SignedCriticalJump.body.lean`. They derive the fixed integer sign required by `reference/SM/sm-2-amplitude.tex:232–237` from the local sign-change definition at `reference/SM/sm-1-polygons.tex:666–667`, using the actual connected generic sides.

1. **Exact half-difference and casts.** `sign_half_difference` first proves an equality in the integers from the hypothesis that the two `SignType` values are opposite. After substituting that hypothesis, the three sign cases reduce to closed integer equalities and use kernel `decide`. The proof casts that integer equality to the arbitrary commutative coefficient ring with `Int.cast_sub`, `Int.cast_mul`, and the natural-number cast rule. It then reassociates multiplication and cancels only the explicitly invertible two. It does not divide by a sign or require a nontrivial ring. The lemma correctly includes the zero/opposite-zero case; the later sign-change argument, not this arithmetic lemma, excludes zero.

2. **Source local predicate.** `WallGerm.SignChanges` states existence of a positive radius, bounded by the germ radius, for which the product of the real-valued function at paired positive and negative times is negative. `signChanges_iff_real` gives the actual real-time formulation, and `signChanges_iff_local` shows the radius bound adds no restriction: a witness can be shrunk. This matches the source's local definition, with no derivative, transversality, or independent-parameter assumption hidden in the premise.

3. **From one local pair to both full sides.** `side_chi_signChanges_opposite` chooses half the witness radius, which is a valid strictly positive side parameter inside the germ. The negative-product sign lemma yields opposite nonzero chirotopes at that pair. `generic_family_chi_constant` then transports each value independently along its entire side. Its source proof composes continuity of chirotopes on the generic locus with the actual continuous side map and uses preconnectedness of the real open interval. `continuous_generic_chi` proves continuity using G1's nonzero determinants, with repeated-label cases handled as constant zero. No combinatorial replacement for a connected side or additional constancy axiom is used.

4. **All actual negative and positive parameters.** `chi_signChanges_parameters` converts an arbitrary positive point of the germ interval to its positive-distance side parameter. It converts an arbitrary negative point to the negation of its coordinate; the original interval's lower bound proves the new coordinate is below the germ radius. Equality of the original and side evaluations is proved in the interval subtype, including the double negation on the negative side. The positive reference value is fixed at `sideBase`, half the full germ radius. Although that base point may lie outside the local sign-change radius, connected-side constancy justifies transporting to it. No global extension of the curve, equal-magnitude pairing, or omitted near-zero condition is needed.

5. **One fixed integer sign.** `boundary_half_jump_signed` chooses the integer cast of the critical chirotope at that fixed positive base point *before* quantifying over the two evaluation parameters. Sign change proves that reference value nonzero; the two nonzero `SignType` cases prove its integer cast is minus one or one. Every independent negative/positive pair has those same opposite signs. Applying the exact cast lemma gives the required half-jump in the coefficient ring. The integer sign remains normalized even in a coefficient ring whose cast identifies values; no unjustified nonzero conclusion in the ring is asserted.

6. **Orientation and domain.** The sign-change premise and the geometric array both use the reversed boundary triple: upper, middle, lower. The subtraction is the positive-side array minus the negative-side array, so the resulting integer is the positive-side sign with the source orientation. Both parameters range over the entire actual open germ interval subject only to their indicated signs. This is justified by global genericity on each punctured side in `WallGerm`. There is no arity-four restriction or assumed wall-response formula. If an integration layer encodes the original unordered critical support with another ordering, it must still supply the corresponding sign-change premise; this helper's premise is explicit.

## Failure repair and limits

The first-run log records an unsolved contradictory finite sign case in `sign_half_difference`, followed by `sorryAx` in the failed declaration and its dependent jump theorem. Those outputs are failed evidence, not proofs. The preserved body diff changes only that proof-local case step: it substitutes the opposite-sign hypothesis before case analysis. All four theorem headers are byte-for-byte unchanged. The final body contains no `axiom`, `sorry`, `admit`, `native_decide`, or `unsafe` token, and its only `decide` use checks the three closed integer identities. The passing log reports no `sorryAx`: the arithmetic lemma uses only `propext` and `Quot.sound`, and the other declarations additionally use `Classical.choice`.

This review supports the stated normalization helpers. It does not approve the complete wall theorem, geometric application, statement-fidelity status, or every transitive compiled import. The kernel evidence was inspected but not independently rerun.

## Hash and receipt binding

Python SHA-256 checks matched **all 3/3 hashes** in `SignedCriticalJump-prototype-result.json`; the target body occurs exactly once, byte-for-byte, in the prototype. The receipt records **root second session 61164, exit 0**, preserved failed session 57122, and zero source-claim acceptance increment. The logs print the four expected theorem signatures.

| File, relative to focused handoff root | SHA-256 |
|---|---|
| `work/checks/SignedCriticalJump.body.lean` | `98e8e750a50f6c3ead9740ebcfba4ea05cceda3624a0c7f6ec81e7a485c31ffc` |
| `work/checks/SignedCriticalJump.prototype.lean` | `ae571bf82ef0fc96f3eb001129666d40e10e4cbf98a3fc5ba0840f7356dc71e7` |
| `work/checks/SignedCriticalJump-second-kernel.log` | `5f2a0428d8b316524d183866250fc2229523342b1240c979a92cede50e43230d` |
| `work/checks/SignedCriticalJump-prototype-result.json` | `b45f5af2057369405ddde0680db6f30c3c14e34096b3f771228f3186919bc501` |
| `work/checks/SignedCriticalJump-first.body.lean` | `8e1f449ba5a13484385696f60f988130c73f1f7f129963e2a95c64aa0ac0a081` |
| `work/checks/SignedCriticalJump-first.prototype.lean` | `8f56e90ea6ca28736397a2a9b2aed25edb6130320ca9e96f191e50aeab958599` |
| `work/checks/SignedCriticalJump-first-kernel.log` | `8590e9097482748bea920f306ed5487ab8ea1f35031f600c7ecb2525fc599b99` |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Relevant canonical definitions and proofs inspected, with source-byte bindings:

```text
18a9abb6b32839d22aabfdba3e45d533ff515aef021adc6efb5337854be0d91a  work/lean/SM/GermSignChange.lean
9bb2bc056bbddb1f7961f9392a9753759e62bff6fd023a89182f90c06a51ad85  work/lean/SM/GermTurnSigns.lean
cabb36d739563036aeee39c1a7bc0cf925a6259c5f90a22ecd61c9e2e737d44a  work/lean/SM/ChamberPaths.lean
595dbb81227c5e368a9aaa696d6a609338961899c3c948590ab6a6f94d70ecc9  work/lean/SM/Chambers.lean
fca24dab7111c6b6f404b075ab4e1b8c20d2fb48083565b6ba89758ebf684f9b  work/lean/SM/WallGerm.lean
3d243e1d12636a02743e0f8dc37e3eecc7d46306fbd3cfca5170fd223ad6fa60  work/lean/SM/NearFar.lean
e0225bc712162273f43269ed764ac4849ae8fcd8798245a367d4262858fbf575  work/lean/SM/Chirotope.lean
```

Only this report was created. No Lean body, canonical source, map, or status file was edited.
