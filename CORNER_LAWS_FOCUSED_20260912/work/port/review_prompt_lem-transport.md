You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE lemma against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/lem-transport-source-excerpt-lines-299-306.tex.txt
   (= reference/SM/sm-5-transport.tex 299-306, lem:transport). Context, read ONLY to fix notation:
   reference/SM/sm-5-transport.tex 150-159 (thm:mycyclic) and 307-316 (the proof of lem:transport,
   which names the three ingredients: thm:mycyclic, thm:relgp, lem:children);
   reference/SM/sm-1-polygons.tex 27-62 (def:polygon: labelled tuples, edges, the cyclic shift σ),
   100-125 (def:generic), 386-406 (def:regular: the regular locus ℛ_n; def:shift), 407-421 (lem:rot),
   539-546 (def:admissible: fibres), 680-736 (def:germ: wall germs, sides, simple germs), 737-800
   (def:walls: the named walls (F) flat, (C) cusp, (V) vertex–edge, (T) triple, (E) extension, (C)
   pure cut — note the printed lemma's "(C)" is the pure cut, the cusp being excluded), 1269-1280
   (lem:children: deletions and halves), 1412-1422 (thm:relgp: piecewise-affine paths, simple wall
   germs, "no cusp occurs"); the definition of deletion and halves (search
   reference/SM/sm-1-polygons.tex for def:deletion-halves).
2. The Lean statement with the proof replaced by `sorry`:
   work/reviews/lem-transport-reviewer-input-statement.lean.txt (main declaration
   SM.transport_lemma). Its module docstring maps notation — verify it, do not trust it.
3. Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are not
   under review): Polygon (LabelledTuple, shift, edge), Generic (Generic), RegularLocus and
   RegularDefinition (Regular; accepted row def:regular), RotationNumber (rotationNumber),
   Admissible (Admissible), WallGerm (WallGerm: radius, curve, Parameter, center, generic_punctured,
   nongeneric_center), GermDefinition (accepted row def:germ), WallCenterKinds (WallKind, HasWallKind,
   Simple), NamedWallPredicates (FlatAt, VertexEdgeAt, BigonAt, SlidingAt, TripleAt, ExtensionAt,
   PureCutAt), CuspDefinition (CuspAt), NamedWallsDefinition (accepted row def:walls),
   RegularWallKinds (RegularWallKind, HasRegularWallKind), DeletedTuple (deleteVertex),
   ContactHalfSizes and ContactHalfTuples (firstHalfSize, secondHalfSize, firstHalf, secondHalf),
   Children (accepted row lem:children — statement only), RelativeGeneralPosition (accepted row
   thm:relgp — the structure RelativeGeneralPositionPath and the statement only), UniformMesh and
   UniformMeshCells (uniformMeshPoint, uniformMeshCell), MycyclicTheorem (row thm:mycyclic under
   review: the bundle MycyclicData — statement only). Mathlib's unitInterval, Continuous, Set.Finite
   may be looked up in .lake/packages/mathlib (read-only). Do NOT open work/lean/SM/TransportLemma.lean
   (it contains the proof).

YOUR TASK: compare the printed sentence with the Lean conclusion, under the printed hypotheses
"P, Z generic labelled tuples in the same fibre (n, r)". Domain: the Lean writes the vertex count as
n + 1 with 3 ≤ n + 1 (every n ≥ 3 has this form — say whether anything is lost), takes Generic P,
Generic Z, rotationNumber P = r = rotationNumber Z, and does NOT assume (n, r) admissible (it follows
from lem:fibres; say whether "in the same fibre (n, r)" requires more). Conclusion, clause by clause:
"there are k ∈ ℤ/n, with k = 0 unless (n, r) = (4, 0)" (∃ k, ((n+1, r) ≠ (4, 0) → k = 0)); "a
piecewise-affine path in ℛ_n from P to σ^k Z" (path : unitInterval → LabelledTuple (n+1), Continuous,
path 0 = P, path 1 = shift k Z, ∀ t Regular (path t), and affine `a + t • b` on each closed cell of a
uniform mesh of [0, 1] — is that "piecewise-affine", and is shift k Z the printed σ^k Z?); "generic
except at finitely many parameters" ({t | ¬ Generic (path t)}.Finite); "at each of which it is a
simple wall germ of type (F), (V), (T), (E) or (C)" (for each nongeneric t: a WallGerm g with
g.center = path t, whose curve is the path near t (the shifted-parameter clause), g.Simple, and the
five-way disjunction FlatAt / VertexEdgeAt / TripleAt / ExtensionAt / PureCutAt — check against
def:germ and def:walls that these predicates are the printed types and that "simple" is rendered;
note the printed (V) covers both branches (bigon and sliding) and that the cusp is excluded as
printed); "at each (F) the deletion is generic" (Generic (deleteVertex (path t) j) for the flat
vertex j); "at each (V) both halves are generic" (Generic (firstHalf (path t) M a) ∧ Generic
(secondHalf (path t) M a) — check def:deletion-halves against firstHalf/secondHalf and the index
convention (M; a)); "all with fewer than n vertices" (the deletion has n vertices by its type,
LabelledTuple n from LabelledTuple (n+1); the halves have firstHalfSize M a < n + 1 and
secondHalfSize M a < n + 1). Expand definitions to primitives; say where the Lean is STRONGER or
WEAKER; any printed sub-clause without a Lean counterpart is a discrepancy. Default to "not
faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
