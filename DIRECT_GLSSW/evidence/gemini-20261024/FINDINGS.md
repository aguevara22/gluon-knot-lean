# Audit Findings (`audit/FINDINGS.md`)

## Summary of Defects vs. Informational Findings

- **Mathematical / Semantic Defects (`FAIL` items)**: **`0`**
  - Zero `EXCESS` or `RULED` binders in the frozen theorem `DirectGLSSW.joint_normalized_homfly_corner_identity`.
  - Zero weakened definitions, degenerate defaults, or unguarded division-by-zero / zero-sign fallbacks on the G1–G2 polygon domain.
  - Zero daughter G1 hypotheses in the public daughter diagram $K_Q$ (`SharpDaughter.sharpDaughterDiagram`) or rotation number $r(Q)$ (`SharpDaughterRotation.sharpDaughterRotationInteger`).
  - Zero uses of `PrimitiveContinuation.fullPrimitive` in the import or proof-term closure of the frozen theorem.
  - Zero forbidden tokens (`sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `extern`, `native_decide`, `Quot.mk`) or metaprogramming/notation overrides (`elab`, `macro`, `macro_rules`, `syntax`, `notation`, `local_notation`) across all `1,589` Lean files.

---

## Detailed Findings Log

### [INF-01] `GLSSWRootIndependence` Is an Explicit Theorem Hypothesis (As Permitted by Contract)
- **Severity**: Informational (Permitted by Audit Contract)
- **Locations**:
  - Manuscript: `project/reference/direct_glssw_corner_proof.tex:85–93`
  - Lean definition: `project/DirectGLSSW/RootedAmplitude.lean:32–35`
  - Frozen statement: `project/ArmstrongFrozen/Frozen/JointNormalizedHomflyCornerIdentity.lean:36`
- **Description**:
  The frozen theorem proves the existence, uniqueness, and invariance of the normalized HOMFLY evaluator `H` **unconditionally** (outside and before `GLSSWRootIndependence`), and proves the polygon corner identity under the sole additional hypothesis `GLSSWRootIndependence`. Our definition audit (`audit/DEFINITIONS.md` §2.2) confirmed that `GLSSWRootIndependence` is a pure statement of root-independence of the finite GLSSW spinor recursion (`rootedSpinorAmplitude`) on `CyclicGeneric` (G1–G2) polygons, with no dependence on HOMFLY, daughters, or knot theory.

### [INF-02] Targeted Scope of `probes/FrozenProofConsumption.lean` and `114` Unreached Supplemental Modules
- **Severity**: Informational
- **Locations**:
  - `probes/FrozenProofConsumption.lean:1–127`
  - `context/IMPLEMENTATION_BINDING_AMENDMENT.json:1–504`
- **Description**:
  Out of `1,589` Lean modules in `project/`, `1,475` modules lie in the transitive `import` closure of `ArmstrongFrozen/Frozen/JointNormalizedHomflyCornerIdentity.lean`, while `114` modules are supplemental or historical exports (including `PrimitiveContinuation.lean`, `OneSegmentContract.lean`, `DirectGLSSW/PolygonAmplitudePathConstancy.lean`, `GeminiChamber/*`, `Immersed*.lean`, and the top-level build target `JointReversalApplication.lean`). The bundled probe `probes/FrozenProofConsumption.lean` checks `16` direct producer-to-consumer proof-term edges and `5` closure targets in the `36,209`-declaration proof-term closure of `DirectGLSSW.joint_normalized_homfly_corner_identity` (specifically covering the `7` bindings in `IMPLEMENTATION_BINDING_AMENDMENT.json`), rather than testing all `314` AND edges of `context/GRAPH_SNAPSHOT.json` individually. Our independent source audit traced the complete proof spine (`audit/DEPENDENCIES.md` §2–3) and confirmed all `100` source proof obligations and `26` definitions on the selected Whitney route (`un:terminal-frame#whitney-route`) are faithfully proved and wired.

### [INF-03] Fresh Cloud Kernel Execution Blocked by Workspace Sandbox (`REMOTE_CHECKS.md`)
- **Severity**: Operational / Verification Environment Constraint
- **Locations**:
  - `REMOTE_CHECKS.md`
  - `audit/BUILD.md` §4
- **Description**:
  Local Lean compilation (`lake`, `lean`, `elan`) on the user's laptop is prohibited by `AGENTS.md`. Inside the current agent execution sandbox, invoking `/Users/aguevaragonzalez/.local/bin/gcp-orphan-check` failed with exit code `127` (`operation not permitted`) and `/Users/aguevaragonzalez/Library/Mobile Documents/com~apple~CloudDocs/augusst knot campaign/phase19/state/gcp_spend_ledger.txt` was inaccessible outside the sandbox boundary. Per `REMOTE_CHECKS.md`, `kernel_verdict` in `audit/VERDICT.json` is recorded as `"INCONCLUSIVE"` (and `overall_verdict` as `"INCONCLUSIVE"` solely due to the absence of a fresh in-session cloud run), while `semantic_verdict` is `"PASS"`. We cryptographically verified that all `1,589` `.lean` files in `project/` and all project metadata files match the exact SHA-256 hashes recorded in the bundled 2026-10-20 cloud build receipt (`PASS_FRESH_PROJECT_BUILD`), portable axiom audit receipt (`PASS_SOURCE_AND_EXPORT_AXIOMS`, `3,382` exports using only `[propext, Quot.sound, Classical.choice]`), and proof-consumption receipt (`FROZEN_PROOF_TERM_CLOSURE_OK visited=36209 targets=5`) with `0` mismatches.
