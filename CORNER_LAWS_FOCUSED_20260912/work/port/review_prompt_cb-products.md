You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row against ONE printed source statement (frame SM15):
cb:products (row 102), Lean declaration `SM.cb_products : SM.CbProductsData hn hP hS`.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cb-products-source-excerpt-lines-4638-4650.tex.txt (= reference/SM/sm-3-statesum.tex
   4638-4650, lem:cb:products "Actual block diagrams and the carrier product": every block H has one owner and admits an actual
   positive carrier diagram D_H with exactly its restricted named cyclic record; P_H is independent of the further smoothings used to
   produce it; for every original carrier A, P_A = ∏_{H owned by A} P_H and m_A = Σ_{H owned by A} |H|; with no owned blocks the actual
   diagram has value 1 and m_A = 0). Context, ONLY to fix notation: sm-3:4651-4696 (its proof — skim for the objects), 4623-4637
   (def:cb:blocks, accepted as SM.cb_blocks_definition — its vocabulary U(S), blocks, owner, D_A, P_A), 4697-4759 (cb:singleton, the
   consumer: which shape it needs), 1624-1687 (mp:blocks, accepted as SM.blocks: "restricted named cyclic record", clean marked joins,
   the product formula), 1215-1229 (rp:record-polynomial: P depends only on the named record), 1306-1320 (lc:presentations), 352-370
   (def:gauss-record), 325-351 (def:positive-lift), the SM lem:carriers (grep 'label{lem:carriers}' in sm-3; clauses (iii),(iv)).
2. The Lean statement with the row proof replaced by `sorry`: work/reviews/cb-products-reviewer-input-statement.lean.txt (module
   SM/CBProducts.lean: the bundle CbProductsData lives in SM/CBBlocks.lean (see 3) — the row theorem SM.cb_products is the declaration
   under review; the module's chain lemmas (namespace SM.CB: gaussRecord, positiveLiftRecordIso, gaussRecord_adj_iff, gaussRecord_restrict_iso,
   restrictCrossings_iso_of_recordIso, exists_blockGraphEquiv, exists_blockCarrier, greedy_independent, greedy_step …) are proof
   material, NOT under review; you may read their statements only to understand the definitions they pin). Do NOT open
   work/lean/SM/CBProducts.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/CBBlocks.lean (accepted row 101: the
   definitions cg, someVisit, crossingOwner, blockOwner, blocksOwnedBy, carrierPoly, IsBlockCarrierDiagram, blockRecordCrossings,
   blockRecord, recordPolynomial, blockPoly and BOTH bundles CbBlocksDefinitionData / CbProductsData with their field docstrings — the
   bundle CbProductsData IS the statement under review), the accepted SM Carrier lane (grep under work/lean/SM/: Generic, IsDecomposition,
   Component, owner, carrierCrossings, carrierCrossingCount, positiveLift and its properties as statements), CV/Carriers.lean (Piece,
   pieceLabels, piecesOn, pieceOwner), CV/CarriersLemma.lean (statement), CV/CarrierBridges.lean + SM/FlatCarriersDefs.lean
   (generic_crossingGeometry, geoComponentEquivGeneric, geoCarrierCrossings_eq_generic — statements), SM/LinkRecord.lean (Record,
   RecordIso, Record.restrictCrossings — the accepted mp:blocks restriction), SM/LinkDiagramRecord.lean (Diagram.record, IsRealizable),
   SM/LinkDiagram.lean, SM/LocalPolynomial.lean (P), SM/MarkedProducts.lean ONLY the definitions BlockSupply / Record.restrictCrossings
   and the bundle BlocksData (accepted mp:blocks) if cited. You MAY read work/AUTHOR_NOTES.md entry "cb lane (cb:blocks 101, cb:products
   102): design panel decided" (2026-09-14) for the recorded readings R-1..R-12 and the entry "cb:blocks ACCEPTED".

DISCLOSED READINGS (judge each): R-4 "actual positive carrier diagram D_H" = positiveLift of a carrier q of an independent refinement
T ⊇ S with carrierCrossings T q = pieceLabels H (IsBlockCarrierDiagram; the printed proof's S_H also has U(S_H) = H, which no clause
needs); R-5 "its restricted named cyclic record" = Record.restrictCrossings (the accepted mp:blocks restriction) of the record of the
OWNER's actual diagram D_{A_H} to the chords whose geometric crossing is a label of H (blockRecord); the printed proof's "the original
record restricted to H" is RecordIso to it; R-6 P_H := recordPolynomial (blockRecord H) (= SM.P of a Classical.choose'n realization, 0
if none) pinned by polynomial_independent and block_diagram — "P_H, the polynomial of D_H" is this common value; R-7 stronger conjuncts:
polynomial_independent asserts for EVERY block carrier diagram D of H both RecordIso D.record (blockRecord H) and SM.P D = P_H; one_owner
asserts ∃! plus equality with blockOwner H; R-9 eq. cb:greedy-step and "the enlarged support is independent" are companion lemmas
(greedy_step, greedy_independent), not fields; the printed proof sentence "the self-crossings of a carrier are exactly its owned
undominated crossings" is a companion lemma; R-11 the proof (not the statement) uses CV:lem:piececurve / def:piecediagram (accepted);
axioms of the row: propext, Classical.choice, Quot.sound, SM.lp_lm (through the accepted SM.blocks product law).

YOUR TASK: decide whether the bundle CbProductsData renders exactly the printed lemma, sentence by sentence: "Every block H has one
owner" (one_owner); "and admits an actual positive carrier diagram D_H with exactly its restricted named cyclic record" (block_diagram —
is IsBlockCarrierDiagram + RecordIso to blockRecord the printed sentence? is blockRecord the printed "restricted named cyclic record"?);
"Its polynomial P_H is independent of the further smoothings used to produce it" (polynomial_independent — is quantifying over every
block carrier diagram the printed independence?); "For every original carrier A, P_A = ∏_{H owned by A} P_H" (owned_by: which blocks are
owned by A; product: P_A = carrierPoly = P (positiveLift A) vs ∏ blockPoly); "m_A = Σ_{H owned by A} |H|" (count: m_A =
carrierCrossingCount); "With no owned blocks the actual diagram has value 1 and m_A = 0" (no_blocks). Every printed clause must have a
field and every field a printed clause (or a labelled consequence). Expand definitions to primitives; say where the Lean is STRONGER or
WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
