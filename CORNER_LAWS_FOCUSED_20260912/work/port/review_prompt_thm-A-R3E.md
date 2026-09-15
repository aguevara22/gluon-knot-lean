You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE theorem against ONE printed source statement.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source statement, verbatim (frame SM15):
   work/reviews/thm-A-R3E-source-excerpt-lines-593-601.tex.txt
   = reference/SM/sm-2-amplitude.tex lines 593-601 (thm:A-R3E). For notation read
   reference/SM/sm-0-legend.tex, reference/SM/sm-1-polygons.tex (def:polygon, def:chirotope,
   def:crossings, def:germ ~680-700 (wall germ, sides P_±), lem:triple-sides ~697, def:walls
   ~737-775 ((T) triple wall, (E) exterior extension, (C) pure cut)), reference/SM/sm-2-amplitude.tex
   (def:root, def:gates, def:treesum lines 10-100 — composition weights V^±(π), open sums b_{[i,j]},
   A_g; prop:A-chamber lines 121-135; the proof of thm:A-R3E at lines 602-660 only to disambiguate
   notation).
2. The Lean statement with its proof replaced by `sorry`:
   work/reviews/thm-A-R3E-reviewer-input-statement.lean.txt (main declaration
   `SM.WallGerm.triple_and_silent_laws_treeCoefficient`).
3. The Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are
   not under review): WallGerm, GermSides (sideTuple), GermSignChange, NamedWallPredicates
   (TripleAt, ExtensionAt, PureCutAt, ContactSeparated via ContactIndices, NoConsecutive),
   WallCenterClassification (pointZeros, concurrences), ZeroTriples, EdgeParameters /
   CrossingParameters (edgeParameter, if referenced by TripleAt), TreeChamber (TreeDataEqual),
   TreeCoefficient (treeCoefficient, openTreeSum), Gates (ordinaryWeight, rootWeight, near/far signs),
   FiniteCompositions, RootBoundary, Polygon, Chirotope, Generic (G1), Segment (edgeInterior,
   edgeSegment, edgePoint). Do NOT open work/lean/SM/TripleSilentLawsTree.lean (it contains the proof).

GLOSSARY (source -> Lean), to be verified, not assumed:
  "simple triple wall at {e,f,g}" : `w.TripleAt e f k`; "simple exterior-extension wall at (M;a)" :
  `w.ExtensionAt M a`; "simple pure cut at {i,j,k}" : `w.PureCutAt i j k`; P_+ / P_- : sides of
  positive / negative parameters, `w.sideTuple true t` / `w.sideTuple false s`; "every composition
  weight, every b_{[i,j]} and A_g are identical on the two sides" : `TreeDataEqual`; A_g :
  `treeCoefficient`; standing n ≥ 3 : `hn`.

YOUR TASK. Compare clause by clause: (a) each of the three wall hypotheses against def:walls (T),
(E), (C) word by word (in particular (T): Z_pt = ∅, Z_c = {{e,f,g}}, and on each of the three edges
the difference of the two crossing parameters of the other two edges changes sign; (E): M ∉
{a-1,a,a+1,a+2}, Z_pt = {{a,a+1,M}}, Z_c = ∅, μ_M(0) on the line of E_a(0) outside the closed segment,
χ_{a,a+1,M} changes sign; (C): no two of i,j,k consecutive mod n, Z_pt = {{i,j,k}}, Z_c = ∅, χ_{ijk}
changes sign); nothing added, nothing dropped. (b) clause (i): does TreeDataEqual cover "every
composition weight, every b_{[i,j]} and A_g" (ordinary and root weights of every composition of
every interval, every open sum, the coefficient) for the root g, with the two sides in either
order; (c) clause (ii): A_g(P_+) = A_g(P_-) for every root; (d) quantifiers: every wall germ of size
n ≥ 3, every root, every point of each side; vacuity checks; (e) expand the definitions to
primitives. Say where the Lean type is stronger or weaker; default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys:
  "verdict": "faithful" | "not faithful", "reason": string (clause-by-clause, cite line numbers),
  "discrepancies": [strings], "stronger_than_source": [strings], "weaker_than_source": [strings],
  "supporting_definitions_inspected": [Lean names], "reviewer_files_read": [relative paths]
