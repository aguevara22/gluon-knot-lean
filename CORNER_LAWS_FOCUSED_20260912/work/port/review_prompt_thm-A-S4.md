You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE theorem against ONE printed source statement.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source statement, verbatim (frame SM15):
   work/reviews/thm-A-S4-source-excerpt-lines-460-470.tex.txt
   = reference/SM/sm-2-amplitude.tex lines 460-470 (thm:A-S4). For notation read
   reference/SM/sm-0-legend.tex, reference/SM/sm-1-polygons.tex (def:polygon, def:chirotope (τ_j),
   def:crossings (X(P), crossing pairs), def:regular and lem:rot (rot), def:germ ~680-700 (wall germ,
   sides), def:walls ~737-775 ((K) cusp wall: newborn pair, loop side P_loop, no-loop side P_no),
   def:deletion-halves ~1254 (P∖j)), reference/SM/sm-2-amplitude.tex (def:root, def:gates,
   def:treesum lines 10-100; def:induced-roots lines 385-398 (D_j); the proof of thm:A-S4 at lines
   471-523 only to disambiguate notation).
2. The Lean statement with its proof replaced by `sorry`:
   work/reviews/thm-A-S4-reviewer-input-statement.lean.txt (main declaration
   `SM.WallGerm.cusp_law_treeCoefficient`).
3. The Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are
   not under review): WallGerm, GermSides (sideTuple, sideBase), GermSignChange, CuspDefinition
   (CuspAt, CuspCase, cuspFirst, cuspLast), CuspSideCrossings (cuspLoopSide), StrictBetween,
   TurnSupports, ZeroTriples, WallCenterClassification (pointZeros, concurrences), Polygon,
   Chirotope (turn), Generic (G1), Crossings (IsCrossing), RotationNumber / RegularLocus /
   PrincipalAngles (rotationNumber), DeletedTuple (deleteVertex), DeletionIndices, FusionIndices,
   InducedRootsDefinition (deletionRoot; definitions and docstrings only — this pending definition
   row def:induced-roots is reviewed separately), TreeCoefficient, Gates, FiniteCompositions,
   RootBoundary. Do NOT open work/lean/SM/CuspLawTree.lean (it contains the proof).

GLOSSARY (source -> Lean), to be verified, not assumed:
  polygon with n ≥ 4 vertices : `WallGerm (n + 1)` with `4 ≤ n + 1` inside `CuspAt`;
  "simple cusp wall at j" : `w.CuspAt j`; the two placements of def:walls (K) : `CuspCase w.center j
  true/false`; the newborn pair : `{cuspFirst b j, cuspLast b j}`; P_loop / P_no : the punctured side
  `w.cuspLoopSide b j` (Bool: true = positive parameters, false = negative) / its negation, with
  `w.sideTuple side s` the polygon at the point s of that side; rot : `rotationNumber`;
  Q = P(0)∖j : `deleteVertex w.center j`; D_j(g) : `deletionRoot j g`; A_g : `treeCoefficient`.

YOUR TASK. Compare clause by clause: (a) hypotheses: "simple cusp wall at j with n ≥ 4" = `CuspAt`
(check def:walls (K) word by word: Z_pt, Z_c, μ_j(0) outside the closed segment, τ_j changes sign),
and "whose deletion Q satisfies (G1)" = `hQ`; nothing added, nothing dropped. (b) the sides: is
P_loop really "the side on which the newborn pair is a crossing" (check CuspCase ↔ the printed
betweenness conditions, cuspFirst/cuspLast ↔ the printed newborn pairs {j-1, j+1} and {j-2, j}, and
the crossing conjunct), and P_no the other side; could anything be vacuous? (c) κ =
rot(P_loop) − rot(P_no) ∈ {-1, 1}: the real rotation numbers of the side polygons, the integer κ.
(d) the identity A_g(P_loop) − A_g(P_no) = −κ A_{D_j(g)}(Q) for every root g at every point of each
side; the sign and the order of the difference. (e) expand deletionRoot, deleteVertex,
rotationNumber, treeCoefficient, IsCrossing to primitives. Say where the Lean type is stronger or
weaker. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys:
  "verdict": "faithful" | "not faithful", "reason": string (clause-by-clause, cite line numbers),
  "discrepancies": [strings], "stronger_than_source": [strings], "weaker_than_source": [strings],
  "supporting_definitions_inspected": [Lean names], "reviewer_files_read": [relative paths]
