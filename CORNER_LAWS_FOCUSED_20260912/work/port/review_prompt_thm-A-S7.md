You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE theorem against ONE printed source statement.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source statement, verbatim (frame SM15):
   work/reviews/thm-A-S7-source-excerpt-lines-525-535.tex.txt
   = reference/SM/sm-2-amplitude.tex lines 525-535 (thm:A-S7). For notation read
   reference/SM/sm-0-legend.tex, reference/SM/sm-1-polygons.tex (def:polygon, def:chirotope (χ),
   def:germ ~680-700 (wall germ, sides P_±), def:walls ~737-775 ((V) vertex-edge wall, bigon and
   sliding types, contact sign s = χ_{a,a+1,M}(P_-)), def:deletion-halves ~1254 (the halves
   λ₁, λ₂ at a vertex-edge wall)), reference/SM/sm-2-amplitude.tex (def:root, def:gates,
   def:treesum lines 10-100; def:induced-roots lines 385-398 (the half map H); the proof of
   thm:A-S7 at lines 536-592 only to disambiguate notation).
2. The Lean statement with its proof replaced by `sorry`:
   work/reviews/thm-A-S7-reviewer-input-statement.lean.txt (main declaration
   `SM.WallGerm.vertex_edge_law_treeCoefficient`).
3. The Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are
   not under review): WallGerm, GermSides (sideTuple, sideBase), GermSignChange,
   NamedWallPredicates (VertexEdgeAt, BigonAt, SlidingAt), NamedWallSides (contactSign),
   ContactIndices (ContactSeparated, contactSupport), ContactHalfSizes, CyclicRangeIndices,
   ContactHalfIndices, ContactHalfTuples (firstHalf, secondHalf), DeletionHalvesDefinition (the
   ACCEPTED row def:deletion-halves), ContactRootPartition, ContactHalfRoots,
   InducedRootsDefinition (halfRoots; definitions and docstrings only — that pending definition row
   is reviewed separately), ZeroTriples, WallCenterClassification, Polygon, Chirotope, Generic (G1),
   Segment (edgeInterior), TreeCoefficient, Gates, FiniteCompositions, RootBoundary.
   Do NOT open work/lean/SM/VertexEdgeLawTree.lean (it contains the proof).

GLOSSARY (source -> Lean), to be verified, not assumed:
  "simple vertex-edge wall at (M; a)" : `w.VertexEdgeAt M a`; bigon / sliding : `BigonAt` / `SlidingAt`;
  P_+ / P_- : the sides of positive / negative parameters, `w.sideTuple true t` / `w.sideTuple false s`;
  s = χ_{a,a+1,M}(P_-) : `w.contactSign M a` (as an integer via the SignType cast);
  λ₁, λ₂ : `firstHalf w.center M a`, `secondHalf w.center M a`; H(g) = (h₁, h₂) : `halfRoots M a g`;
  A_g : `treeCoefficient`; the standing n ≥ 3 : `hn`.

YOUR TASK. Compare clause by clause: (a) hypotheses: is "simple vertex-edge wall at (M; a), of bigon
or sliding type" exactly `VertexEdgeAt` (check def:walls (V) word by word, and that bigon/sliding
exhaust the type as the source's "of bigon or sliding type" intends); nothing added or dropped?
(b) s: is `contactSign` the printed χ_{a,a+1,M}(P_-), and does the constancy conjunct pin it to the
whole negative side? (c) the halves and the roots: are λ₁, λ₂ the printed halves (at the wall
centre P(0), as def:deletion-halves defines them) and (h₁, h₂) = H(g) as def:induced-roots defines
it; are the G1 facts and the size facts the right prerequisites for A to be defined? (d) the
identity A_g(P_+) − A_g(P_-) = s·A_{h₁}(λ₁)·A_{h₂}(λ₂) for every physical root g at every point of
each side, with the printed sign and order. (e) expand halfRoots, firstHalf, secondHalf, contactSign,
VertexEdgeAt, treeCoefficient to primitives. Say where the Lean type is stronger or weaker;
default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys:
  "verdict": "faithful" | "not faithful", "reason": string (clause-by-clause, cite line numbers),
  "discrepancies": [strings], "stronger_than_source": [strings], "weaker_than_source": [strings],
  "supporting_definitions_inspected": [Lean names], "reviewer_files_read": [relative paths]
