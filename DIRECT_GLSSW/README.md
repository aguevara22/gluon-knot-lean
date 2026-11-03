# Direct GLSSW sewing proof

This separate Lean project contains the exact 1,589-source release verified on 20 October 2026. It does not import the repository's wall-law formalization.

The central theorem is [`DirectGLSSW.joint_normalized_homfly_corner_identity`](ArmstrongFrozen/Frozen/JointNormalizedHomflyCornerIdentity.lean). It establishes:

- Normalized HOMFLY existence and uniqueness, agreement with every based descending traversal, and invariance under `SignedDiagramIso` and `SignedRegularDeletion`, unconditionally.
- For the same evaluator, the corner identity for every finite real G1–G2 polygon, assuming `GLSSWRootIndependence`.

**GLSSW root independence is an explicit hypothesis, not a theorem proved by this package.** The construction of HOMFLY is independent of it. The proof subtracts separating sewings, proves that the resulting primitive vanishes on mixed-turn polygons, identifies the uniform primitive with the prescribed HOMFLY coefficient, and reconstructs the amplitude by finite inversion and local continuation.

The package also contains a uniquely characterized locally constant extension, `PrimitiveContinuation.fullPrimitive`, of the auxiliary finite primitive sum. The final theorem does not depend on this extension or identify it with manuscript primitive values at nongeneric daughters. Supplementary modules remain included because the release audit certifies the complete selected source inventory.

## Build and verify

With Elan and Python 3.11 or newer available, run from the repository root:

```sh
cd DIRECT_GLSSW
lake exe cache get
lake build JointReversalApplication
python3 check_release.py
lake env lean -j 2 ../ci/direct_glssw/FrozenProofConsumption.lean
```

The project pins Lean **4.19.0** and Mathlib revision **`c44e0c8ee63ca166450922a373c7409c5d26b00b`** in its own toolchain and Lake manifests. Run Lake in this directory to select these pins. Dependency sources, toolchain binaries, and build caches are not bundled.

`check_release.py` requires the build to have succeeded. It verifies the source inventory and hashes, rejects `sorry`, `admit`, `axiom`, and `unsafe` in code, and checks all 3,382 named exports in Lean's checked environment. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed in their axiom dependencies. Receipts are written beneath `.lake/release-audit/`.

The additional proof-consumption probe checks 16 selected direct proof connections and five results in the final theorem's transitive proof-term closure. These supplement the semantic review; they do not individually test every source-graph edge.

For a quick integrity check without Lean, run from the repository root:

```sh
python3 ci/direct_glssw/check_snapshot.py
```

This compares the relocated files with the original build and audit receipts; it is not a fresh kernel verification. The [Direct GLSSW workflow](../.github/workflows/direct-glssw.yml) performs the full build, export audit, and dependency probe on GitHub-hosted runners and uploads new receipts.

## Verification evidence

The [bundled evidence](evidence/README.md) distinguishes historical checks from new CI runs:

- **20 October 2026:** fresh GCP build of all 1,589 modules in 23:30.10; audit of 3,382 exports with zero forbidden source tokens and only the three standard axioms above. The exact Lean sources, checker, and dependency pins are unchanged here.
- **20 October 2026:** independent final source, definition, binder, and dependency review passed with zero excess premises.
- **24 October 2026, Gemini:** semantic review passed with zero reported mathematical defects. Its kernel and overall verdicts are **INCONCLUSIVE** because a fresh build was not run in that audit session; it verified the source hashes against the prior cloud receipts. The original verdict is included without upgrading it.

These records concern the cited snapshot. GitHub workflow runs report the status of subsequent builds.

## Source and attribution

The source manuscript is [*Marked polygon currents and the HOMFLY corner: A direct sewing argument for the GLSSW state sum*](reference/direct_glssw_corner_proof.tex), dated 13 September 2026. Its supplied author field is blank; this directory does not assign authorship or grant a new license to it.

The formalization was developed with Codex and Gemini. Lean, Mathlib, and other pinned dependencies retain their upstream licenses. Historical receipt paths identify the original verification environment; they are not dependencies on that machine.
