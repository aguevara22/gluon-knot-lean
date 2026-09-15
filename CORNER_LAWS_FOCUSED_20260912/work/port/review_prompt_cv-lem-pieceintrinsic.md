You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row of the CV lane against ONE printed source statement of the paper "CV"
(reference/R/CV/, frozen): CV:lem:pieceintrinsic (row 156), Lean declaration `CV.pieceintrinsic : CV.PieceIntrinsicData …`.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cv-lem-pieceintrinsic-source-excerpt-lines-56-74.tex.txt (= reference/R/CV/d6_vertexedge.tex
   56-74, lem:pieceintrinsic "carrier restriction is the intrinsic piece diagram"). Context, ONLY to fix notation: d6_vertexedge.tex
   75-116 (its proof — skim for the objects), 117-141 (lem:homflyrows), 263-330 (cor:groupedknot, the consumer), reference/R/CV/d1_setup.tex
   355-361 (def:smoothing), 362-383 (lem:carriers, esp. (iii)-(iv)), 450-459 (lem:carrierword), 514-530 (def:pieces), 565-590
   (def:piecediagram — the divide convention and D_P(H)), 592-610 (lem:piececurve: the carrier C_H, Step 5 erasures), the record
   definition CV:def:record (grep 'label{def:record}' in reference/R/CV/*.tex) and ax:gausscode (reference/R/CV/d10_axioms.tex, grep
   'label{ax:gausscode}' — accepted as the polynomial consequence CV.gausscode_polynomial, executor decision F4), reference/SM/sm-3-statesum.tex
   352-370 (def:gauss-record, named record isomorphisms).
2. The Lean statement with the row proofs replaced by `sorry`: work/reviews/cv-lem-pieceintrinsic-reviewer-input-statement.lean.txt
   (module CV/PieceIntrinsic.lean: the definitions IsCarrierRestriction, carrierRestriction, pieceVisit, restrictionVisit,
   carrierRestriction_recordIso (statement), the bundle PieceIntrinsicData with fields carried, restriction, intrinsic, record_iso,
   same_link, polynomial, writhe, and the theorems CV.pieceintrinsic (printed Generic binder) / CV.pieceintrinsic_of_diagrammatic are
   UNDER REVIEW; §1-§5 helper lemmas' proofs are not). Its module docstring maps the printed notation and lists readings R1-R6 —
   verify them, do not trust them. Do NOT open work/lean/CV/PieceIntrinsic.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/CV/PieceCurve.lean (accepted rows 142/143:
   StepInvariant, pieceSupport, pieceCarrier, pieceCurve, pieceShadow, pieceDiagram, pieceHomfly, pieceWrithe; bundles PieceDiagramData,
   PieceCurveData as statements), CV/Carriers.lean (Piece, pieceLabels, pieceOwner — CV:def:pieces), CV/CarriersLemma.lean and
   CV/CarrierWord.lean (statements), CV/Setup.lean (Generic, Diagrammatic, Generic.diagrammatic), CV/Events.lean (Ind), CV/Axioms.lean
   (AxHomflyData, CV.ax_homfly, CV.gausscode_polynomial — accepted), CV/RecordHomfly.lean, SM/FlatCarriersDefs.lean (GeoComponent,
   geoOwner, geoCarrierCrossings), SM/GeoPositiveLift.lean (geoPositiveLift, geoCarrierShadow, geoCarrierCrossingEquiv),
   SM/LinkRecord.lean (Record, RecordIso), SM/LinkDiagramRecord.lean (Diagram.record, twin, nextVisit, overBit), SM/LinkDiagram.lean
   (Diagram, writhe, sign), SM/LinkInterfaces.lean (homfly). You MAY read work/AUTHOR_NOTES.md entries "CV-DOM decided" (readings
   (i)-(iii)), "F4" (CV:ax:gausscode replaced by its polynomial consequence) and "U7c rows reviewed" / "CV:lem:piececurve ACCEPTED"
   (2026-09-14).

DISCLOSED READINGS of the unit (judge each): R1 (substantive) — "D_L(H), the diagram obtained from L by retaining exactly the crossings
of H … and erasing all others" is rendered as the FAMILY of positive lifts of carriers q of S ∪ K with K an admissible erased set
(StepInvariant S H K: K ⊆ U(S), K ∩ H = ∅, S ∪ K independent) and q retaining exactly H (IsCarrierRestriction K q); every member lies
inside L; pieceDiagram is a member; every field is stated for every member (the text fixes neither the erasure order nor the terminal
set; "intrinsic" = independence from them; fixing a single D_L(H) would make the row a tautology); R2 D_P(H) = pieceDiagram (row 142);
R3 "the identity map on the visits of H" = pieceVisit (ι.Φ v) = restrictionVisit v (occurrences named by their parent visits); R4
"they present the same oriented link (Axiom ax:gausscode)" read in the F4 polynomial form (CV.gausscode_polynomial); R5 the printed
Generic binder via hG.diagrammatic hn, hn : 3 ≤ n per reading (iii).

YOUR TASK: decide whether the definitions + bundle render exactly the printed lemma: the binder (P generic, S ∈ Ind, H a residual piece
carried by the carrier L by lem:carriers (iv)); the objects D_L(H) (R1 — is the family reading faithful or a widening; is "obtained from
L by retaining exactly the crossings of H … each resolved by the divide convention … erasing all others" what IsCarrierRestriction +
carrierRestriction say?) and D_P(H) (R2); the standing sentence "a crossing lies on a carrier means both traversal preimages belong to
it" (carried field?); the conclusion "the identity map on the visits of H is a record isomorphism from the record of D_L(H) to the
record of D_P(H)" (record_iso with R3 — is the isomorphism the identity on visits, and is 'record isomorphism' CV:def:record's / def:gauss-record's
RecordIso?); "Consequently they present the same oriented link (Axiom ax:gausscode)" (same_link, R4); "P_{D_L(H)} = P_H"
(polynomial) and "w(D_L(H)) = |H|" (writhe). Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; label
non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
