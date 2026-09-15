You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proofs. Your job is a
DEFINITION-fidelity review of one definition row against one printed source definition.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source definition, verbatim (frame SM15):
   work/reviews/def-induced-roots-source-excerpt-lines-385-398.tex.txt
   = reference/SM/sm-2-amplitude.tex lines 385-398 (def:induced-roots). For notation read
   reference/SM/sm-0-legend.tex, reference/SM/sm-1-polygons.tex (def:polygon: vertices, edges
   E_g = [μ_g, μ_{g+1}], roots; def:walls (F),(K),(V) at lines ~737-775; def:deletion-halves near
   line 1254: P∖j, the halves λ₁, λ₂ at a vertex-edge wall) and reference/SM/sm-2-amplitude.tex
   (def:root lines 10-27; the theorems thm:A-S3, thm:A-S4, thm:A-S7 at lines 400-560 CONSUME this
   definition and may be read only to understand how D_j and H are meant to be used).
2. The Lean row under review with every proof replaced by `sorry`:
   work/reviews/def-induced-roots-reviewer-input-statement.lean.txt
   Main declaration `SM.induced_roots_definition : InducedRootsDefinitionData`; the definitions
   `SM.deletionRoot` (= D_j), `SM.halfRoots` (= H) and the property bundles `DeletionRootData`,
   `HalfRootsData` are in that file.
3. The Lean definition modules under work/lean/SM/ that these refer to (read definitions and
   docstrings; helper proofs are not under review): Polygon (incident, edge, adjacent),
   DeletionIndices, DeletedTuple (deleteVertex), FusionIndices (fusionIndex), DeletionInteriors,
   ContactIndices (ContactSeparated, contactSupport), ContactHalfSizes (contactDistance,
   firstHalfSize, secondHalfSize), CyclicRangeIndices, ContactHalfIndices (firstHalfIndex,
   secondHalfIndex, secondHalfEdgeIndex), ContactHalfTuples (firstHalf, secondHalf),
   DeletionHalvesDefinition (the ACCEPTED row def:deletion-halves: DeletionData, HalvesData),
   NamedWallPredicates (FlatAt, VertexEdgeAt), CuspDefinition (CuspAt), WallGerm,
   ContactRootPartition, ContactHalfRoots, PhysicalDeletionRoots. Follow any further definition.
   Do NOT open work/lean/SM/InducedRootsDefinition.lean (it contains the proofs).

YOUR TASK. The source defines two maps: D_j on roots (two cases: g ∈ {j-1, j} ↦ the fused edge
[μ_{j-1}, μ_{j+1}] of P∖j; otherwise ↦ the edge of P∖j with the same endpoints as E_g) and H on
roots at a vertex-edge wall (three cases: g = a ↦ (d₁, d₂); g ∈ {M, …, a-1} ↦ (E_g in λ₁, d₂);
g ∈ {a+1, …, M-1} ↦ (d₁, E_g in λ₂), with d₁ = [μ_a, μ_M] the closing edge of λ₁ and
d₂ = [μ_M, μ_{a+1}] the opening edge of λ₂). Decide whether the Lean definitions
`deletionRoot`/`halfRoots` denote exactly these maps and whether the property bundles
`DeletionRootData`/`HalfRootsData`, as asserted by `InducedRootsDefinitionData`, characterise them
as printed: (a) are the case conditions the printed ones (incident j g ↔ g ∈ {j-1, j}; the two
cyclic arcs expressed through (g - M).val and contactDistance M a = (a - M).val; g = a)? (b) is
"the fused edge" the edge -1 of deleteVertex P j with endpoints μ_{j-1}, μ_{j+1}? (c) is "the
edge of P∖j with the same endpoints as E_g" pinned down (same two vertices, unique)? (d) are d₁,
d₂ the printed edges of the halves, and "E_g in λ₁ / λ₂" the inherited edge with the same parent
label / endpoints? (e) is the domain right: the deletion map is stated for every P with n+1 ≥ 4
vertices and every j (the source scopes it to flat/cusp walls at j — say whether stating it more
generally is acceptable for a definition), the half map for every simple vertex-edge wall
(VertexEdgeAt)? (f) is anything vacuous, missing, or stronger/weaker than the printed text?
Expand every local Lean definition down to accepted primitives. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys:
  "verdict": "faithful" | "not faithful",
  "reason": clause-by-clause comparison (cite source lines 385-398 and statement-file lines),
  "discrepancies": [strings], "stronger_than_source": [strings], "weaker_than_source": [strings],
  "supporting_definitions_inspected": [Lean names], "reviewer_files_read": [relative paths]
