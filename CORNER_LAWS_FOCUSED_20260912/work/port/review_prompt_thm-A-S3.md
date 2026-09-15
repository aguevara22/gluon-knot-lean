You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE theorem against ONE printed source statement.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source statement, verbatim (frame SM15):
   work/reviews/thm-A-S3-source-excerpt-lines-400-409.tex.txt
   = reference/SM/sm-2-amplitude.tex lines 400-409 (thm:A-S3). For notation read
   reference/SM/sm-0-legend.tex, reference/SM/sm-1-polygons.tex (def:polygon, def:chirotope
   (turn τ_j), def:germ ~680-700 (wall germ, sides), def:walls ~737-775 ((F) flat wall, right/left
   sides), def:deletion-halves ~1254 (P∖j)), reference/SM/sm-2-amplitude.tex (def:root, def:gates,
   def:treesum lines 10-100; def:induced-roots lines 385-398 (D_j); the proof of thm:A-S3 at lines
   410-449 only to disambiguate notation).
2. The Lean statement with its proof replaced by `sorry`:
   work/reviews/thm-A-S3-reviewer-input-statement.lean.txt (main declaration
   `SM.WallGerm.flat_law_treeCoefficient`).
3. The Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are
   not under review): WallGerm, GermSides, GermSignChange, NamedWallPredicates (FlatAt),
   NamedWallSides (FlatRightSide, FlatLeftSide), TurnSupports (turnSupport), ZeroTriples,
   WallCenterClassification (pointZeros, concurrences, StrictBetween), Polygon, Chirotope (turn),
   Generic (G1), DeletedTuple (deleteVertex), DeletionIndices, FusionIndices,
   InducedRootsDefinition (deletionRoot; you may read its definitions and docstrings — this row
   is the pending definition row def:induced-roots and is being reviewed separately),
   TreeCoefficient (treeCoefficient), Gates, FiniteCompositions, RootBoundary, DeletionG1.
   Do NOT open work/lean/SM/FlatLawTree.lean (it contains the proof).

GLOSSARY (source -> Lean), to be verified, not assumed:
  polygon with n ≥ 4 vertices : `WallGerm (n + 1)` with `4 ≤ n + 1` inside `FlatAt`;
  "simple flat wall at j" : `w.FlatAt j`; τ_j : `turn P j`; P(0) : `w.center`;
  the sides P_right (τ_j = -1) and P_left (τ_j = +1): the side b ∈ {true = positive parameters,
    false = negative parameters} with `FlatRightSide j b` / `FlatLeftSide j (!b)`;
  A_g(P) : `treeCoefficient P hP g hn`; P(0)∖j : `deleteVertex w.center j`;
  D_j(g) : `deletionRoot j g` (def:induced-roots).

YOUR TASK. Compare clause by clause: (a) hypotheses: is "simple flat wall at j with n ≥ 4" exactly
`FlatAt`, nothing more, nothing less? (b) the sides: does the ∃! conjunct plus the universal
quantification over parameters with `turn = -1` (right) and `turn = 1` (left) capture "P_right is
the side with τ_j = -1" and "P_left" (the chamber values of A_g)? Is anything vacuous — could the
implication be vacuously true because no parameter has turn -1, or because both sides have the
same turn? (c) conclusion: A_g(P_right) − A_g(P_left) = A_{D_j(g)}(P(0)∖j) for every root g, with
the printed sides in the printed order and the printed deletion root; the G1 of P(0)∖j needed to
define the right-hand side. (d) definitions: expand `deletionRoot`, `deleteVertex`, `FlatAt`,
`FlatRightSide`, `treeCoefficient` to primitives and check they denote the source objects. Say
where the Lean type is stronger or weaker. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys:
  "verdict": "faithful" | "not faithful", "reason": string (clause-by-clause, cite line numbers),
  "discrepancies": [strings], "stronger_than_source": [strings], "weaker_than_source": [strings],
  "supporting_definitions_inspected": [Lean names], "reviewer_files_read": [relative paths]
