You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE proposition against ONE printed source statement.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source statement, verbatim (frame SM15):
   work/reviews/prop-A-reversal-source-excerpt-lines-1508-1519.tex.txt
   = reference/SM/sm-2-amplitude.tex lines 1508-1519 (prop:A-reversal). For notation read
   reference/SM/sm-0-legend.tex (indices mod n, det), reference/SM/sm-1-polygons.tex (def:polygon
   incl. the shift σ: (σP)_i = μ_{i+1}, roots carried g ↦ g−1; def:generic (G1); def:shift near line
   398: reversal P̄_i = μ_{2−i}), reference/SM/sm-2-amplitude.tex (def:root lines 10-27: a root is an
   edge index, the shift carries the root g of P to the root g−1 of σP; def:gates, def:treesum lines
   29-81; the proof of prop:A-reversal at lines 1520-1560 only to disambiguate notation).
2. The Lean statement with its proof replaced by `sorry`:
   work/reviews/prop-A-reversal-reviewer-input-statement.lean.txt (main declaration
   `SM.treeCoefficient_reversal_shift_law`).
3. The Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are
   not under review): Polygon (LabelledTuple, shift, edge, det), Reversal (reversal), Generic (G1),
   GenericReversal (g1_reversal_forward statement), Generic/G1Consequences (g1_shift_forward
   statement), TreeCoefficient (treeCoefficient, rootedTreeRec, openTreeRec, fullBoundaryInterval),
   Gates, FiniteCompositions, RootBoundary (boundaryIndex, boundaryWord, BoundaryInterval,
   IntervalComposition), Chirotope (chi). Do NOT open work/lean/SM/ReversalShiftLaw.lean or
   work/lean/SM/TreeReversal.lean (they contain the proofs).

GLOSSARY (source -> Lean), to be verified, not assumed:
  polygon satisfying (G1) : `P : LabelledTuple n`, `hP : G1 P`, standing n ≥ 3 : `hn`;
  root g : `g : ZMod n` (edge index); σP : `shift 1 P`; P̄ with P̄_i = μ_{2−i} : `reversal P`;
  g^∨ = 1 − g : `1 - g`; A_g(P) : `treeCoefficient P hP g hn : ℤ`; (−1)^n : `(-1) ^ n` in ℤ.

YOUR TASK. Compare clause by clause: (i) `A_g(σP) = A_{g+1}(P)`: check `shift 1 P` is σP with the
printed vertex relabelling (μ_{i+1} at i), that the Lean has the root g on σP and g+1 on P as
printed (and not the reverse), and that the (G1) proof for σP is supplied without extra hypotheses;
(ii) `A_{g^∨}(P̄) = (−1)^n A_g(P)` with `P̄_i = μ_{2−i}` and `g^∨ = 1 − g`: check the conjunct
`∀ i, reversal P i = P (2 - i)` records the printed definition of P̄, the root `1 - g` is g^∨, the
sign `(-1)^n` uses the source's n (the number of vertices), and both sides are the printed tree
coefficients (expand treeCoefficient to def:treesum: boundary word a_k = μ_{g+k+1}, compositions,
V^± gates, the open-sum recursion, the rooted sum). Check "for every polygon satisfying (G1) and
every root g" and "all indices read modulo n" (ZMod n). Say where the Lean type is stronger or
weaker; is anything vacuous? Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys:
  "verdict": "faithful" | "not faithful", "reason": string (clause-by-clause, cite line numbers),
  "discrepancies": [strings], "stronger_than_source": [strings], "weaker_than_source": [strings],
  "supporting_definitions_inspected": [Lean names], "reviewer_files_read": [relative paths]
