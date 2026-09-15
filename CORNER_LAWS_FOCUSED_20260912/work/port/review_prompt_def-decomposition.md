You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the row and must not read its proof. Your job is a DEFINITION-fidelity review of one
definition row against one printed source definition.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source definition, verbatim (frame SM15):
   work/reviews/def-decomposition-source-excerpt-lines-9-12.tex.txt
   = reference/SM/sm-3-statesum.tex lines 9-12 (def:decomposition). For notation read
   reference/SM/sm-0-legend.tex, reference/SM/sm-1-polygons.tex (def:crossings ~138, def:gauss ~249,
   def:interlace ~259: crossings interlace, the interlacement graph G_P, Ind(G_P)), and the first
   lines of reference/SM/sm-3-statesum.tex (1-30) for context ("P is generic throughout").
2. The Lean row with the proof replaced by `sorry`:
   work/reviews/def-decomposition-reviewer-input-statement.lean.txt (main declaration
   `SM.decomposition_definition`; definitions `SM.IsDecomposition`, `SM.decompositions`).
3. The Lean definition modules under work/lean/SM/ (definitions and docstrings): InterlaceSupports
   (interlacementGraph, independentSupports, crossingSupportShift, supportNeighbors),
   Interlacement (Interlaces), InterlaceDefinition (the ACCEPTED row def:interlace,
   SM.interlacement_definition), Crossings (Crossing, IsCrossing), Generic, Polygon, Chambers /
   GenericTopology (generic_shift), CrossingEquiv (crossingShiftEquiv). Do NOT open
   work/lean/SM/DecompositionDefinition.lean (it contains the proof).

YOUR TASK. The source: "A decomposition of P is an independent set S ∈ Ind(G_P) of crossings
(Definition def:interlace): no two crossings of S interlace." Check: (a) that `IsDecomposition hn hP
S` denotes exactly "S is an independent set of the interlacement graph G_P" and that
`decompositions hn hP` is Ind(G_P); (b) that the conjuncts are the printed characterisations (S ∈
Ind(G_P); independent set of G_P; no two distinct crossings of S interlace) and that `Interlaces`
and `interlacementGraph` are the accepted def:interlace objects; (c) the domain: P generic with the
standing n ≥ 3 (sm-3 line 3: "P is generic throughout this section"); (d) whether the extra
conjuncts (∅ is a decomposition; descent under cyclic relabelling) are true consequences and
harmless; (e) vacuity or anything missing. Expand definitions to primitives. Default to "not
faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys:
  "verdict": "faithful" | "not faithful", "reason": string (cite source lines 9-12 and statement-file
  lines), "discrepancies": [strings], "stronger_than_source": [strings], "weaker_than_source":
  [strings], "supporting_definitions_inspected": [Lean names], "reviewer_files_read": [relative paths]
