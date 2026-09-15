You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row of the CV lane against ONE printed source statement of the paper "CV"
(reference/R/CV/, frozen): CV:cor:groupedknot (row 158), Lean declaration `CV.groupedknot : CV.GroupedKnotData hn hG hS q`.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cv-cor-groupedknot-source-excerpt-lines-263-298.tex.txt (= reference/R/CV/d6_vertexedge.tex
   263-298, cor:groupedknot "…" — read every sentence: the label union W of the pieces on a carrier L, retaining all of W, the
   partition into the pieces, the tree 𝓣 of clean marked joins, the product formula, the single-piece case, the knot diagram D(W), the
   grouped polynomial P_{S,L} and grouped writhe w_{S,L}, the underlying curve, no triple points, the parenthetical about the no-piece
   case). Context, ONLY to fix notation: d6_vertexedge.tex 299-360 (its proof — skim for the objects), 56-74 (lem:pieceintrinsic, accepted
   as CV.pieceintrinsic), 117-141 (lem:homflyrows, accepted), reference/R/CV/d1_setup.tex 514-530 (def:pieces), 565-610 (def:piecediagram,
   lem:piececurve — accepted rows 142/143), 908-930 (def:X1: P_{S,L} = ∏_{H on L} P_H, w_{S,L} = Σ|H| — accepted), reference/SM/sm-3-statesum.tex
   1362-1437 (marked diagrams and clean marked joins, mp:join), 1624-1636 (mp:blocks, accepted as SM.blocks: the record partitioned into
   interlacement blocks, realized by a finite succession of clean marked joins, product formula), 352-370 (def:gauss-record).
2. The Lean statement with the row proof replaced by `sorry`: work/reviews/cv-cor-groupedknot-reviewer-input-statement.lean.txt (module
   CV/GroupedKnot.lean: the definitions carrierDiagram (D(W)), IsPieceLeafFamily, the record-level lemmas' STATEMENTS (arcBetween_iff_visitBetween,
   liftRestrictRecordIso, adj_iff_geometricInterlaces, blockEquiv — proof material, not under review), the bundle GroupedKnotData with fields
   label_union, retain_all, partition, tree, product, single, knot_diagram, grouped_polynomial, grouped_writhe, underlying_curve,
   no_triple_points, no_piece and the theorem CV.groupedknot are UNDER REVIEW). Its module docstring maps the notation and lists readings —
   verify, do not trust. Do NOT open work/lean/CV/GroupedKnot.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/CV/PieceCurve.lean (pieceDiagram, pieceHomfly,
   pieceWrithe, pieceCurve — accepted), CV/PieceIntrinsic.lean (IsCarrierRestriction, carrierRestriction — accepted), CV/X1.lean (groupedPoly,
   groupedWrithe — accepted), CV/Carriers.lean (Piece, pieceLabels, piecesOn, pieceOwner), CV/HomflyRows.lean (statement), CV/Axioms.lean
   (CV.ax_homfly, gausscode_polynomial), SM/GeoPositiveLift.lean (geoPositiveLift, geoCarrierShadow — the actual positive diagram of a carrier),
   SM/FlatCarriersDefs.lean (GeoComponent, geoCarrierCrossings), SM/MarkedProducts.lean ONLY the definitions MarkedDiagram, IsCleanMarkedJoin,
   JoinForest, BlockSupply, Record.restrictCrossings and the bundle BlocksData (accepted mp:blocks), SM/LinkRecord.lean (Record, RecordIso),
   SM/LinkDiagramRecord.lean (Diagram.record), SM/LinkDiagram.lean (Diagram, writhe, componentCount, Generic / no_triple), SM/LinkInterfaces.lean
   (homfly). You MAY read work/AUTHOR_NOTES.md entries "CV-DOM decided" (readings (i)-(iii)), "F4", "D9" (design-decision record
   work/reports/design-decision-diagram-record-20260913.md: clean marked joins at record level) and "CV:lem:pieceintrinsic ACCEPTED".

DISCLOSED READINGS of the unit (judge each): (a) D(W) = carrierDiagram = geoPositiveLift of the carrier L itself (W is the whole
self-crossing set of L, so nothing is erased; reading (ii)); (b) "≅" between D(W) and the tree's result is a named record isomorphism with
an actual clean-marked-join diagram (F4, D9), not link equivalence; the tree 𝓣 is existential (mp:blocks' realizes), structured by
JoinForest rather than an explicit tree type; (c) tree / product quantify over every record-isomorphic leaf family IsPieceLeafFamily (the
printed ∏ P_{H_i} with leaves the piece diagrams is the canonical instance; stronger); (d) "k ≥ 1" = (piecesOn q).Nonempty on the fields
that need it; underlying_curve / no_triple_points hold unconditionally; (e) the parenthetical no-piece case is a field proved from def:X1's
empty conventions; (f) hn : 3 ≤ n per reading (iii).

YOUR TASK: decide whether the definitions + bundle render exactly the printed corollary, sentence by sentence; every printed clause must
have a field and every field a printed clause (or a labelled consequence). Expand definitions to primitives; say where the Lean is
STRONGER or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
