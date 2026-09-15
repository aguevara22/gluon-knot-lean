You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the row you are reviewing and you must not read its proofs. Your job is a
DEFINITION-fidelity review of one definition row against one printed source definition.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source definition, verbatim (frame SM15):
   work/reviews/def-soft-source-excerpt-lines-996-1015.tex.txt
   = reference/SM/sm-2-amplitude.tex lines 996-1015 (def:soft). For notation read
   reference/SM/sm-0-legend.tex (conventions: det, indices mod n, ℓ_i), reference/SM/sm-1-polygons.tex
   (def:polygon: vertices μ_i, edges E_i = [μ_i, μ_{i+1}], edge vectors ℓ_i = μ_{i+1} − μ_i; def:chirotope:
   χ_{ijk}, turns τ_i; def:generic), and reference/SM/sm-2-amplitude.tex lines 1017-1052
   (lem:soft-generic) and 1157-1169 (thm:A-soft), which CONSUME this definition — read them only to
   understand how the notation P_ε, χ_±, "admissible", soft edge, return edge is used.
2. The Lean row under review with every proof replaced by `sorry`:
   work/reviews/def-soft-reviewer-input-statement.lean.txt
   Main declaration `SM.softInsertion_definition : SoftInsertionDefinitionData`; the property bundle
   `SoftInsertionData` is in that file.
3. The Lean definition modules under work/lean/SM/ that these refer to (definitions and docstrings;
   helper proofs are not under review): SoftInsertionTuple (softInsertion, SoftAdmissible,
   softAttachmentMinus, softAttachmentPlus), SoftInsertionIndices (softNewPosition, softNewIndex,
   softOldIndex), SoftInsertionSuccessors, CanonicalTripleSigns (canonicalPosition, canonical_label),
   RootBoundary (boundaryIndex), Polygon (LabelledTuple, edge, det), Chirotope (chi, turn),
   EuclideanPlane, Generic. Follow any further definition (e.g. Fin.insertNth from Mathlib: you may
   look up its meaning in .lake/packages/mathlib if needed). Do NOT open
   work/lean/SM/SoftInsertionDefinition.lean (it contains the proofs).

YOUR TASK. The source defines, for P with (G1), a vertex j and q ≠ 0, the (n+1)-gon
P_ε = (μ_1, …, μ_j, μ_j + εq, μ_{j+1}, …, μ_n), ε > 0, with μ_* inserted immediately after μ_j; its
edges ℓ_{j−1}, the soft edge εq, the return edge ℓ_j − εq, the others unchanged; the attachment
signs χ_− = χ_{*,j,j−1}(P_ε) = −sgn det(ℓ_{j−1}, q) and χ_+ = χ_{*,j,j+1}(P_ε) = −sgn det(q, ℓ_j)
for every ε > 0; and admissibility of q. Decide whether the Lean definitions denote exactly these
objects and whether `SoftInsertionData` characterises them as printed: (a) is `softInsertion P j q ε`
the printed tuple (which labels carry the old vertices, where the new vertex sits, cyclic order
"immediately after μ_j", no vertex lost or duplicated)? Expand softNewPosition/softNewIndex/
softOldIndex/canonicalPosition/Fin.insertNth to check. (b) are the soft edge and return edge the
printed edges (indices and vectors) and are the other edges unchanged? (c) are χ_−, χ_+ the printed
chirotope entries of P_ε at the printed index triples AND the printed determinant formulas, with the
printed signs? (d) is SoftAdmissible exactly the three printed determinant conditions? (e) domain:
the data is stated for every P, j, q and ε > 0 (the source says P with (G1), q ≠ 0): is stating it
more generally acceptable for a definition? (f) anything vacuous, missing, stronger or weaker?
Expand every local Lean definition down to primitives. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys:
  "verdict": "faithful" | "not faithful", "reason": clause-by-clause comparison (cite source lines
  996-1015 and statement-file lines), "discrepancies": [strings], "stronger_than_source": [strings],
  "weaker_than_source": [strings], "supporting_definitions_inspected": [Lean names],
  "reviewer_files_read": [relative paths]
