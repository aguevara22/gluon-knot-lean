# Visible generic tuple preserving the nonzero chirotope

Authored by the same currently available model as the root agent. This is an untested implementation candidate, not independent review or stronger-model statement-fidelity approval. No Lean kernel, build, or audit was run. Root owns compilation and independent review. No frozen, canonical, source, or acceptance file was edited.

The only new declaration is `SM.visible_chamber_generic_preserving_nonzero_chi`. Its caller supplies exactly `hn : 3 ≤ n` and `P : WeakTuple n`. It returns `Q : GenericTuple n`, membership of Q's proved weak representative in the actual `labelledVisibleChamber P`, and equality of every ordered chi entry initially nonzero at P. There is no G1 premise at P, single-zero premise, or density oracle.

Proof steps: (1) P belongs to its own connected component. The canonical `weak_visible_components` theorem therefore makes the ambient image of that actual component a neighborhood of P. (2) The canonical `finite_nonzero_chi_persists` theorem supplies a single neighborhood preserving all initially nonzero ordered signs; it uses continuity away from zero and finite intersection over the three labels and is valid at arbitrary P. (3) Intersect the two neighborhoods, extract a nonempty open subset containing P with `mem_nhds_iff`, and apply `generic_in_nonempty_open hn`. This produces actual full Generic, including G2. (4) Unpack the component-image witness and use subtype extensionality to identify it with the weak representative obtained from `generic_implies_weak`. The same chosen tuple retains all sign equalities.

This implements the generic-witness step of `cor:polyform`, source lines 975–981. The proof uses an open neighborhood instead of explicitly constructing a ball; both enforce the exact chamber and sign requirements needed by the source argument. It makes no polynomial-evaluation or cancellation claim.

The prototype imports only the three canonical modules `SM.WeakOpen`, `SM.GenericDensity`, and `SM.FiniteChiStability`. It embeds the body exactly once and requests its type and axiom trace. Exact first drafts were preserved before any possible repair.

## Candidate hashes

- `work/checks/VisibleGenericSignPersistence.body.lean`: `7caaaa02bddf3cfe88062877b9bc6f322b8d5b445870c23be02d5859ded84084`
- `work/checks/VisibleGenericSignPersistence.prototype.lean`: `e48c11900330122d2f2ebe6367da9285693eccf94aa9013bb01ca10bbde277a9`
- `work/checks/VisibleGenericSignPersistence-first-draft.body.lean`: `7caaaa02bddf3cfe88062877b9bc6f322b8d5b445870c23be02d5859ded84084`
- `work/checks/VisibleGenericSignPersistence-first-draft.prototype.lean`: `e48c11900330122d2f2ebe6367da9285693eccf94aa9013bb01ca10bbde277a9`

## Canonical and source hashes

- `work/lean/SM/WeakOpen.lean`: `d529ddd96240311708fe3a840c9fb4cf2692764943435b77dae59e5c56b79bd5`
- `work/lean/SM/GenericDensity.lean`: `6b6880d31118c202d47ca340811b3006e4ef565e7d6dfe666b5ac7f115ae39c1`
- `work/lean/SM/FiniteChiStability.lean`: `7160db9c4ac930a64c65ce44b9e9a41d4f139a3442a49604b3c96f9a347cadc9`
- `work/lean/SM/WeakGeneric.lean`: `1a72ebddb4ddb4d72a89f14a5fede9badc3dbed095a972f6dd1b85db30789b22`
- `work/lean/SM/Chambers.lean`: `595dbb81227c5e368a9aaa696d6a609338961899c3c948590ab6a6f94d70ecc9`
- `reference/SM/sm-2-amplitude.tex`: `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf`
