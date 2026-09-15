You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE theorem against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/thm-root-indep-proof-source-excerpt-lines-53-56.tex.txt
   (= reference/SM/sm-6-comparison.tex 53-56, thm:root-indep-proof). Context, read ONLY to fix
   notation: reference/SM/sm-2-amplitude.tex 10-27 (def:root: a root of a polygon is one of its
   edges, an edge index g ∈ ℤ/n on a representative) and 66-82 (def:treesum: the tree coefficient
   A_g(P) of a polygon satisfying (G1) at the root g); reference/SM/sm-1-polygons.tex 27-62
   (def:polygon: labelled tuples and polygons as cyclic orbits), 100-125 (def:generic: (G1), (G2),
   generic polygon). The proof of the theorem (sm-6-comparison.tex 57-104) may be skimmed ONLY to
   confirm what "generic polygon" and "edges g, h" range over.
2. The Lean statement with the proof replaced by `sorry`:
   work/reviews/thm-root-indep-proof-reviewer-input-statement.lean.txt (main declaration
   SM.root_independence). Its docstring maps notation — verify it, do not trust it.
3. Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are not
   under review): TreeCoefficient (treeCoefficient and the definitions it is built from; accepted
   row def:treesum, declaration SM.treesumData) with the modules it imports that define open sums,
   gates and interval compositions (definitions only), RootBoundary (accepted row def:root),
   Generic (G1, G2, Generic; accepted row def:generic), Polygon (LabelledTuple, shift, edge;
   accepted row def:polygon), Chirotope (chi, turn). Do NOT open work/lean/SM/RootIndependence.lean
   (it contains the proof) and do not open any other module under work/lean/SM whose name contains
   RootIndep.

YOUR TASK: compare the printed sentence "For every generic polygon P and any two of its edges g, h,
A_g(P) = A_h(P)" with the Lean statement. Check: (a) "generic polygon P" — the Lean quantifies over
labelled tuples P : LabelledTuple n with Generic P for every n ≥ 3 (with a [NeZero n] instance);
does stating it on labelled representatives cover the printed polygons (cyclic orbits), and is the
range of n (3 ≤ n) the printed one (a polygon has at least three vertices; check def:polygon)?
(b) "any two of its edges g, h" — edge indices g h : ZMod n (def:root); (c) "A_g(P)" — the Lean
treeCoefficient P hP.1 g hn takes the (G1) witness hP.1 (the first component of Generic P) and the
arity witness hn; does treeCoefficient denote the printed A_g (compare with def:treesum and the
accepted row def:treesum), and does the value depend on the proof arguments? (d) is anything
hidden in the hypotheses: is Generic P stronger or weaker than the printed "generic" (def:generic:
(G1) and (G2)); is the theorem vacuous for some n? Expand definitions to primitives; say where the
Lean is STRONGER or WEAKER; any printed sub-clause without a Lean counterpart is a discrepancy.
Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
