You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE corollary against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cor-A-lawful-source-excerpt-lines-105-116.tex.txt
   (= reference/SM/sm-6-comparison.tex 105-116, cor:A-lawful). Context, read ONLY to fix notation
   (each law is "the" law of the cited accepted row, so read its printed statement): sm-6 53-56
   (thm:root-indep-proof), sm-6 5-13 (lem:A-small-values), reference/SM/sm-2-amplitude.tex 66-82
   (def:treesum, in particular "The main text's A(P) is A_n(P), rooted at the last edge E_n"),
   121-135 (prop:A-chamber), 401-415 (thm:A-S3 flat law: P_right, P_left, the deletion P(0)∖j),
   460-480 (thm:A-S4 cusp law: P_loop, P_no, κ), 525-545 (thm:A-S7 vertex–edge law: P_±, s, the
   halves λ₁ λ₂), 593-610 (thm:A-R3E triple law and silence), 1157-1175 (thm:A-soft: the soft
   theorem A_g(P_ε) = ((χ_- + χ_+)/2) A_g(P) in every sector, the roots it covers), 1508-1525
   (prop:A-reversal: shift and reversal), reference/SM/sm-5-transport.tex 5-15 (def:star: K_1, K_{-1}
   the counterclockwise and clockwise triangles), reference/SM/sm-1-polygons.tex 27-62 (def:polygon:
   polygons as cyclic orbits), 206-211 (def:chamber), 680-736 (def:germ: wall germs and sides),
   737-800 (def:walls), 1254-1268 (def:deletion-halves).
2. The Lean statement with the proof replaced by `sorry`:
   work/reviews/cor-A-lawful-reviewer-input-statement.lean.txt (definition `amplitude`, bundle
   `ALawfulData`, main declaration SM.A_lawful). Its module docstring maps notation — verify it, do
   not trust it.
3. Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are not
   under review): TreeCoefficient (treeCoefficient; accepted row def:treesum), Generic, Polygon
   (LabelledTuple, shift), Reversal (reversal; accepted row def:shift), Chambers and CyclicChambers
   (GenericTuple, GenericPolygon, polygonProjection, labelledChamber, chamber; accepted row
   def:chamber), TreeChamber (accepted row prop:A-chamber — statement only), WallGerm (WallGerm,
   Parameter, SideParameter, sideTuple, curve, center), GermDefinition and NamedWallsDefinition
   (accepted rows def:germ, def:walls), NamedWallPredicates (FlatAt, VertexEdgeAt, TripleAt,
   ExtensionAt, PureCutAt), CuspDefinition (CuspAt, CuspCase, cuspLoopSide, cuspFirst, cuspLast),
   NamedWallSides (contactSign, FlatRightSide, FlatLeftSide), DeletedTuple (deleteVertex),
   InducedRootsDefinition (deletionRoot, halfRoots; accepted row def:induced-roots), ContactHalfTuples
   and ContactHalfSizes (firstHalf, secondHalf, sizes), FlatLawTree, CuspLawTree, VertexEdgeLawTree,
   TripleSilentLawsTree, SoftTheoremTree, ReversalShiftLaw (accepted law rows — statements only, to
   compare the side conventions), SoftInsertionTuple and SoftInsertionDefinition (softInsertion,
   SoftAdmissible, softAttachmentMinus/Plus), SoftAmplitudeSectors (softAmplitudeMultiplier),
   StarPolygons and StarDefinition (star, starNeg; accepted row def:star), StarGenericLaw (statement
   only), SmallValuesLemma (statement only), RootIndependence (statement of SM.root_independence
   only — do not read its proof body). Do NOT open work/lean/SM/ALawful.lean (it contains the proof).

YOUR TASK: compare the printed corollary with the bundle. (i) "A(P) := A_g(P) (any g) is well
defined on generic polygons": `amplitude` is the tree coefficient at the root 0 (the main text's
A_n); check the fields root_independent (any root gives the same value), shift_invariant and
descends (a function on the polygon space GenericPolygon n exists with the right values) — is
"well defined on generic polygons" fully rendered? (ii) "chamber constancy and silence
(prop:A-chamber, thm:A-R3E(ii))": chamber_constant (labelled chambers and chambers of the polygon
space) and silent (extension and pure-cut walls). (iii) the flat law "A(P_right) − A(P_left) =
A(P(0)∖j)": field flat_law — the sides named by the turn at j as in the accepted thm:A-S3 row, the
deletion generic (extra, from lem:children), the value of A on the deletion. (iv) the cusp law
"A(P_loop) − A(P_no) = −κ A(P(0)∖j) when the deletion satisfies (G1)": field cusp_law — the loop
side and κ as in the accepted thm:A-S4 row; the right-hand side is stated at every induced root
D_j(g) of the (G1) deletion, and as −κ·A(deletion) when the deletion is generic. Judge this reading:
for a deletion that satisfies only (G1), A(P(0)∖j) is not root-independent in general, so the
per-root form is the meaningful one — is the printed sentence rendered faithfully, weakened, or
strengthened? (v) the vertex–edge law "A(P_+) − A(P_-) = s A(λ₁) A(λ₂)": field vertex_edge_law (sides
P_± = positive/negative parameters, s = contactSign, halves generic as extra information). (vi) the
triple law "A(P_+) = A(P_-)": field triple_law. (vii) the soft theorem "A(P_ε) = ((χ_- + χ_+)/2) A(P)
in every sector": field soft_theorem (for all small ε; softAmplitudeMultiplier = (χ_- + χ_+)/2; the
identity in ℚ). (viii) reversal "A(P̄) = (−1)^n A(P)": field reversal_law. (ix) "A(K_1) = −1,
A(K_{−1}) = +1 on the counterclockwise and clockwise triangles": field triangles with K_1 = star 1,
K_{−1} = starNeg 1 = reversal (star 1). Expand definitions to primitives; say where the Lean is
STRONGER or WEAKER; any printed clause without a Lean counterpart is a discrepancy. Default to "not
faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
