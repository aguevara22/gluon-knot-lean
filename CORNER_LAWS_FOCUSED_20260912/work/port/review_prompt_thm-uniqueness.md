You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE theorem against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/thm-uniqueness-source-excerpt-lines-201-218.tex.txt
   (= reference/SM/sm-6-comparison.tex 201-218, thm:uniqueness: hypotheses (a)-(f) and the
   conclusion F(P) = A(P)). Context, read ONLY to fix notation: sm-6 105-116 (cor:A-lawful: A(P) and
   the laws it satisfies — each hypothesis of thm:uniqueness is "the" law of the corresponding
   accepted row read for F), sm-6 261-298 (the remark after the proof: "what the theorem does not
   assume"), reference/SM/sm-2-amplitude.tex 66-82 (def:treesum: A(P) = A_n(P) rooted at the last
   edge), 401-410 (thm:A-S3: P_right, P_left, P(0)∖j), 525-534 (thm:A-S7: P_±, s, λ₁, λ₂), 593-601
   (thm:A-R3E: triple law and silence), 1157-1169 (thm:A-soft: the soft theorem, "for all
   sufficiently small ε"), 996-1015 (def:soft: admissible vector, soft insertion, χ_±),
   reference/SM/sm-5-transport.tex 5-15 (def:star: K_1, K_{-1}), reference/SM/sm-1-polygons.tex 27-62
   (def:polygon: polygons as cyclic orbits; the formalization remark), 100-108 (def:generic),
   206-211 (def:chamber), 680-736 (def:germ), 737-800 (def:walls: simple walls of types (F), (C)
   cusp, (V), (T), (E), (C) cut), 1254-1267 (def:deletion-halves).
2. The Lean statement with the proof replaced by `sorry`:
   work/reviews/thm-uniqueness-reviewer-input-statement.lean.txt (structure UniquenessHypotheses,
   main declaration SM.uniqueness). Its module docstring maps notation — verify it, do not trust it.
3. Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are not
   under review): Chambers and CyclicChambers (GenericTuple, GenericPolygon, polygonProjection,
   chamber, labelledChamber, genericCyclicSetoid; accepted row def:chamber), Polygon (LabelledTuple,
   shift), Generic, ALawful (the definition `amplitude` and the statement of `A_lawful : ALawfulData`
   only — not its proof; row cor:A-lawful, under review in parallel), TreeCoefficient
   (treeCoefficient; accepted row def:treesum), WallGerm (WallGerm, Parameter, SideParameter,
   sideTuple, curve, center), GermDefinition and NamedWallsDefinition (accepted rows def:germ,
   def:walls), NamedWallPredicates (FlatAt, VertexEdgeAt, BigonAt, SlidingAt, TripleAt, ExtensionAt,
   PureCutAt), NamedWallSides (contactSign), DeletedTuple (deleteVertex), ContactHalfTuples and
   ContactHalfSizes (firstHalf, secondHalf, sizes), FlatLawTree, VertexEdgeLawTree,
   TripleSilentLawsTree, SoftTheoremTree (accepted law rows — statements only, to compare side
   conventions), SoftInsertionTuple and SoftInsertionDefinition (softInsertion, SoftAdmissible,
   softAttachmentMinus/Plus), SoftAmplitudeSectors (softAmplitudeMultiplier), StarPolygons and
   StarDefinition (star, starNeg; accepted row def:star), StarGenericLaw (statement only). Do NOT open
   work/lean/SM/Uniqueness.lean (it contains the proof).

YOUR TASK: compare the printed theorem with the Lean statement. Domain: "F a function assigning an
integer to every generic polygon of every arity n ≥ 3" is `F : ∀ (n : ℕ) [NeZero n], GenericPolygon n
→ ℤ`, a function on the space of generic polygons (cyclic orbits) — say whether this is exactly the
printed object (in particular that F is a function of the polygon, not of a labelling, and that the
[NeZero n] instance and the arities n < 3, on which F is unconstrained, are harmless); a generic
labelled tuple P presents the polygon `polygonProjection ⟨P, hP⟩`. Hypotheses, one field each: (a)
`chamber` (constant on chambers of the polygon space) and `silent` (unchanged across simple silent
walls of types (E) ExtensionAt and (C) PureCutAt — is "simple silent walls (types (E) and (C))"
exactly these two predicates, and is "unchanged across" the equality of the two side values for all
side parameters?); (b) `flat`: "F(P_right) − F(P_left) = F(P(0)∖j) at every simple flat wall" — sides
named by the turn at j as in thm:A-S3, the deletion with any genericity witness (the source's
deletion at a simple flat wall is generic by lem:children; does taking hdel as a hypothesis weaken
or strengthen?); (c) `vertex_edge`: "F(P_+) − F(P_-) = s F(λ₁) F(λ₂) at every simple vertex–edge wall,
both branches" — VertexEdgeAt covers bigon and sliding; s = contactSign; halves with genericity
witnesses; (d) `triple`; (e) `soft`: "F(P_ε) = ((χ_- + χ_+)/2) F(P) for all small ε, at every soft
insertion of an admissible vector into a generic polygon" — ∃ δ > 0, ∀ ε < δ, for every genericity
witness of P_ε, the identity in ℚ with softAmplitudeMultiplier = (χ_- + χ_+)/2; (f) `triangles`:
F(K_1) = −1, F(K_{-1}) = +1 with K_1 = star 1, K_{-1} = starNeg 1 as polygons. Conclusion: "F(P) = A(P)
for every generic polygon P" — `F n (polygonProjection ⟨P, hP⟩) = amplitude P hP.1 hn` for every n ≥ 3
and generic labelled P, where amplitude is the tree coefficient at the root 0 (the main text's
A_n; cor:A-lawful makes it root-independent) — is this the printed A(P)? Expand definitions to
primitives; say where the Lean is STRONGER or WEAKER (a weaker hypothesis on F or a stronger
conclusion makes the theorem stronger; a stronger hypothesis on F makes it weaker — classify each);
any printed clause without a Lean counterpart is a discrepancy. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
