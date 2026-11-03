# Verification records

These are archived records for the exact source snapshot in `DIRECT_GLSSW`. Historical paths and timestamps are preserved; references to the old workspace are provenance, not paths needed to build this package.

| Record | Scope |
|---|---|
| [Build result](20261020/build/RESULT.json), [log](20261020/build/build.log), [timing](20261020/build/TIME.txt) | Fresh GCP project build, 1,589 modules; pinned dependency cache reused |
| [Export audit](20261020/audit/portable/RESULT.json), [source hashes](20261020/audit/portable/SOURCE_AUDIT.json), [axiom log](20261020/audit/portable/axioms.log) | 3,382 exports; source inventory, hashes and forbidden-token check; standard axioms only |
| [Proof-consumption result](20261020/audit/PROOF_CONSUMPTION.json), [log](20261020/audit/proof-consumption.log) | 16 direct edges and five transitive targets; [probe source](../../ci/direct_glssw/FrozenProofConsumption.lean) |
| [Final semantic review](20261020/FINAL_SEMANTIC_MANIFEST.json) | Source theorem, definitions, binders and dependency use; zero excess premises |
| [Source graph](context/GRAPH_SNAPSHOT.json), [binding amendment](context/IMPLEMENTATION_BINDING_AMENDMENT.json) | Selected Whitney route and implementation bindings |
| [Gemini verdict](gemini-20261024/VERDICT.json), [report](gemini-20261024/REPORT.md), [findings](gemini-20261024/FINDINGS.md) | Semantic PASS; kernel and overall INCONCLUSIVE because no fresh build ran in that session |

The root-level `ci/direct_glssw/check_snapshot.py` verifies that the package files match the recorded build and audit inputs. The full kernel audit remains `python3 check_release.py` after the pinned Lake build. A new CI run provides a new verification record; copying the package does not itself rerun Lean.
