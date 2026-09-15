You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE definition row against ONE printed source definition (frame SM15):
cb:blocks (row 101), Lean declaration `SM.cb_blocks_definition : SM.CbBlocksDefinitionData hn hP hS`.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cb-blocks-source-excerpt-lines-4623-4637.tex.txt (= reference/SM/sm-3-statesum.tex
   4623-4637, def:cb:blocks "Undominated blocks and their owners"). Context, ONLY to fix notation: sm-3:4638-4696 (cb:products, the
   consumer, and its proof — "The self-crossings of a carrier are exactly its owned undominated crossings"), 4697-4759 (cb:singleton),
   the SM carrier definitions the row cites: grep in reference/SM/sm-3-statesum.tex and sm-1-polygons.tex for def:smoothing /
   def:flat-carriers / lem:carriers ("Lemma lem:carriers" — locate the SM lemma with clauses (iii),(iv): an undominated crossing has both
   visits on one carrier), def:interlace (sm-1:259-268), lp:core (1041-1063: P = H⁺ on positive diagrams), def:positive-lift (325-351:
   the actual positive diagram of a polygon, D_A), def:gauss (sm-1:240-268).
2. The Lean statement with the row proof replaced by `sorry`: work/reviews/cb-blocks-reviewer-input-statement.lean.txt (module
   SM/CBBlocks.lean: the definitions in namespace SM.CB — cg, mem_Ind, someVisit, crossingOwner, blockOwner, blocksOwnedBy,
   carrierPoly, IsBlockCarrierDiagram, blockRecordCrossings, blockRecord, recordPolynomial, blockPoly — and the bundle
   CbBlocksDefinitionData are UNDER REVIEW as the row's statement; the bundle CbProductsData (row 102) is NOT under review; helper
   lemmas' proofs are not). Its module docstring maps the printed notation — verify, do not trust. Do NOT open work/lean/SM/CBBlocks.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): the accepted SM Carrier lane — grep under
   work/lean/SM/ for the definitions the statement uses: Generic, IsDecomposition / independentSupports, interlacementGraph,
   Interlaces, supportUnselected, supportNeighbors, Component, owner, carrierCrossings, carrierCrossingCount, positiveLift (the actual
   positive diagram of a carrier — its componentCount, IsPositive, sign, writhe lemmas as statements), cornerHomfly (def:C), P (SM/LocalPolynomial),
   homfly (SM/LinkInterfaces); the accepted CV geo objects it bridges to: work/lean/CV/Carriers.lean (Piece, pieceLabels, piecesOn,
   pieceOwner, residualGraph, U, N — CV:def:pieces), CV/Events.lean (Ind, N, U), CV/CarrierBridges.lean and SM/FlatCarriersDefs.lean
   (generic_crossingGeometry, geoComponentEquivGeneric, geoCarrierCrossings_eq_generic, U_eq_generic, N_eq_generic,
   geometricInterlacementGraph_eq_generic — definitions and statements), SM/LinkRecord.lean (Record, RecordIso, Record.restrictCrossings),
   SM/LinkDiagramRecord.lean (Diagram.record), SM/MarkedProducts.lean ONLY the definitions Record.restrictCrossings / BlockSupply if
   cited. You MAY read work/AUTHOR_NOTES.md entry "cb lane (cb:blocks 101, cb:products 102): design panel decided" (2026-09-14) for the
   recorded readings R-1..R-12, and the CV-DOM decision entry ("CV-DOM decided", readings (i)-(iii)).

DISCLOSED READINGS (judge each): R-1 SM "block" = the accepted CV.Piece (generic_crossingGeometry hn hP) S — the same printed object
"connected components of G_P[U(S)]" — with the bridging conjuncts (CV.U = supportUnselected, CV.N = supportNeighbors,
geometricInterlacementGraph = interlacementGraph) inside the fields they serve; R-2 the owner of an undominated crossing is DEFINED
through a fixed visit (someVisit) and pinned by the field crossing_owner (both visits on one carrier — by lem:carriers (iii));
R-3 two lanes (SM Carrier lane for carriers/owner/D_A/m_A; the geo layer for blocks) joined by the accepted equivalence
geoComponentEquivGeneric; R-6 P_H := recordPolynomial (blockRecord H) is row 102's device (its fields pin it) — check only what row
101's bundle says about D_A and P_A; R-8 hn : 3 ≤ n and [NeZero n] are bundle parameters; hS : IsDecomposition renders "independent
support".

YOUR TASK: decide whether the definitions + bundle pin down exactly the printed definition, sentence by sentence: "Fix a generic
polygon P, its interlacement graph G_P, and an independent support S" (binder); "For a vertex set T write N_G(T) for the union of
its graph neighbourhoods" (neighbourhood); "U(S) = V(G_P) \ (S ∪ N(S))" (undominated); "The connected components of G_P[U(S)] are
called its blocks" (blocks, blocks_partition — is a partition clause printed or a consequence?); "An undominated crossing has both
visits on one carrier by Lemma lem:carriers; that carrier is its owner" (undominated_one_carrier, crossing_owner); "Write D_A for the
actual positive diagram of a carrier A, and P_A = P_{D_A}" (actual_positive_diagram — is positiveLift the printed actual positive
diagram, and are its listed properties (one component, every crossing positive, sign +1, writhe = number of self-crossings) printed
or consequences?; carrier_polynomial); "These polynomials equal the corresponding H_A^+ by Theorem lp:core" (equals_Hplus — a
consequence field as printed). Every printed clause must have a field and every field a printed clause (or a labelled consequence).
Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
