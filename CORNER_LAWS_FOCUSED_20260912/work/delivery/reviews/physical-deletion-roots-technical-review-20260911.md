# Physical deletion roots — technical review

2026-09-11. Independent review by another agent of the **same currently available model**, **not stronger-model statement-fidelity approval** and not original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8.

## Findings

No defect was found in the seven declarations in `PhysicalDeletionRoots.body.lean` relative to the **deletion portion only** of `def:induced-roots`, `reference/SM/sm-2-amplitude.tex` lines 380–386.

- `incident j g` is exactly `g = j - 1 ∨ g = j`. The fused child root has label `-1` because `deleteVertex` reads surviving vertices starting at the old successor of j. `fusionIndex_eq_last_iff_incident` proves precisely which parent roots map there; `fusionIndex_surjective` supplies every child root via its retained starting label. Neither uses geometric assumptions.
- `fusionIndex_nonincident_labels` identifies the two endpoint **labels in order** as g and g + 1. It first excludes both incident labels, then uses the inverse relation for `deletionIndex` and its successor formula away from the fused root. Thus it does not silently apply that successor formula across the deletion seam.
- `fusionIndex_incident_labels` identifies the two fused endpoint labels as j - 1 and j + 1. It reduces the child root to -1, uses its successor 0, and applies the proved last/first deletion-index formulas. This is the source fused predecessor-to-successor edge with the correct orientation.
- `fusionIndex_unique_nonincident_root` constructs the nonfused child root with those ordered endpoints. Any other such label has the same image under the injective `deletionIndex`, hence is equal. This is uniqueness of the induced **label**, not a claim that coincident point coordinates can never make different geometric segments equal.
- `fusionIndex_physical_deletion_root` evaluates the label identities through the actual tuple `deleteVertex P j`. Its two implications cover every parent root and give the literal ordered point pairs appearing in the source definition. `fusionIndex_nonincident_edgePoint` additionally preserves the entire parametrized edge for every real parameter: both its initial point and its endpoint difference agree. Equality of vectors alone is not substituted for equality of physical endpoint pairs.

The existing `fusionIndex` is therefore supplied with direct endpoint evidence for its intended interpretation as the source deletion-root map. The proofs concern arbitrary labelled tuples of parent arity n + 1 with positive child arity n; this broad domain adds no restriction to simple flat/cusp walls. No nondegeneracy, G1, amplitude, wall response, or inferred point separation is assumed. The relevant existing definitions and inverse-index proofs were inspected in `FusionIndices`, `DeletionIndices`, `DeletedTuple`, `DeletionInteriors`, and `Polygon`. Their dependency direction is index construction → endpoint transport, with no circular use of the claimed wall law.

The separate half-map definition and the flat equation are **not established by these seven declarations**. This review does not extend to either claim.

## Receipt and hash evidence

Root's first session **15649** exited 0. All **3/3** receipt hashes match the current files, and the body occurs verbatim exactly once in the prototype, which imports `SM.FusionIndices`. The passing log prints all seven declarations; their axiom traces contain only `propext`, `Quot.sound`, and, for the geometric statements, `Classical.choice`. No error, `sorryAx`, `native_decide`, or `Lean.ofReduceBool` occurs in that log. This reviewer ran no Lean kernel or build.

SHA-256 bindings (paths relative to the focused root):

| File | SHA-256 |
|---|---|
| `work/checks/PhysicalDeletionRoots.body.lean` | `0ddba4bd177561cab24e9fb98d5aac8ba07c978bf37367e2880ed5c39cdc5ffb` |
| `work/checks/PhysicalDeletionRoots.prototype.lean` | `a508b45b54b837150a1d52ca2fcef9f5191f22a1c43fcea8135286c9837be72f` |
| `work/checks/PhysicalDeletionRoots-first-kernel.log` | `b15a7fa7e62c6a2042424a3abbc0aef0faeb2f72de5754217caa4613fb165941` |
| `work/checks/PhysicalDeletionRoots-prototype-result.json` | `352b23d3f61f909e41a28fa773e79627d4b4a8a0b682e5196958310995842d82` |
| `work/lean/SM/FusionIndices.lean` | `6ea253ca0032b57388319e838d7aac9d985ad1144589261a6606ac32dc9f468f` |
| `work/lean/SM/DeletionIndices.lean` | `15078436d16d1d233a3005ebdd5027156dd36200236a5a7928eef9e4071cec58` |
| `work/lean/SM/DeletedTuple.lean` | `b2e591d11b1f25d82511de7979be131fb2158e7bf3a62a0e3e962f1e2cca634c` |
| `work/lean/SM/DeletionInteriors.lean` | `ea1a88c5ec8367505114f541379f72b5b78a20690b3257d1b44ffb05c1ddfc8c` |
| `work/lean/SM/Polygon.lean` | `d0b5d37591c252d66e1a3f060cea1e3d58625fedd6c5491cf4c1cf6d2b8c149d` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Hashes and recorded successful checks bind the inspected artifacts; they do not supply stronger fidelity approval. No frozen Lean body, canonical file, acceptance map, or status was edited.
