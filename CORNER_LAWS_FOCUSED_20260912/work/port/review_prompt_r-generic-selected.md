You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the statement you are
reviewing and you must not read its proof. Your job is a statement-fidelity review of ONE row against its printed source:
R:generic_selected (row 174; a package obligation of the R lane with a FIXED name `RProof.generic_selected` and a FIXED bundle
statement `RowShape @GenericSelectedData`, whose bundle `GenericSelectedData` was accepted earlier in the R lane), module
RProof/GenericSelected.lean.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. Printed source, verbatim: work/reviews/r-generic-selected-source-excerpt-R_GENERIC_SELECTED_COUPLE_PROOF.md.txt
   (= reference/R/RA/R_GENERIC_SELECTED_COUPLE_PROOF.md, whole file: "R local complement — generic selected complementary couple",
   statement (GSC): T_E(b) = T_P(b) + T_P(ac) for the selected b/ac complementary couple at a simple RIII wall in the generic graph
   orbit with an exterior independent support Q, full availability), read with R_ASSEMBLY_SPEC.md and EXECUTION.json at the
   handoff root (the obligation's place in the R assembly) and, for notation only, reference/R/RA/R_ATTACHMENT_WARRANTS.md (R-LOC,
   R-PAR), R_GENERIC_ORBIT_ACTUAL_TABLE.md, R_GENERIC_NONSELECTED_SELECTOR_PROOF.md, and the CV definitions in reference/R/CV/.
2. The Lean statement: work/reviews/r-generic-selected-reviewer-input-statement.lean.txt (RProof/GenericSelected.lean with the proof
   replaced by sorry: the row theorem in the FIXED shape) and, for the fixed bundle `GenericSelectedData` and `RowShape`,
   work/reviews/r-ledgers-reviewer-input.lean.txt (RProof/RALedgers.lean stripped: RowShape, gsc_moves, gsc_Ledger, gsc_ledger,
   gsc_generic_selected_of_moves — statements only) and the accepted RProof/X1Rows.lean where GenericSelectedData is defined
   (grep `structure GenericSelectedData`).
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/RProof/X1Rows*.lean, RProof/RALedgers.lean,
   RProof/GenericTransport.lean (GT_Endpoint, the wall transport), work/lean/CV/ (Event, Punctured, carrierDiagram, geoPositiveLift,
   GeoComponent, X1, Omega1, groupedWrithe, carrierR, weight — grep for the names you meet), work/lean/SM/BigonDeletion.lean
   (BigonData, exists_rii_deletion: the R-II deletion the proof constructs), SM/Smoothing.lean (smoothDiagram), and Mathlib.
4. Disclosed readings: work/AUTHOR_NOTES.md entries of 2026-09-15 titled "CV/R tail … design panel judged", "Moves toolkit …"
   (D-RM-1..4), "Row 174: the bigon site landed", "Rows 174/176: record transports closed", "Row 174: the site inputs",
   "Rows 174/176 all units back", "Row 174 wave 1 assembled" and the acceptance entry; for the fixed bundle also
   work/drafts/rlane2/NOTES_FINAL.md §7 (the accepted statement panel's clause map of GenericSelectedData — you MAY read this one
   draft file).

KERNEL FACTS (reported by the executor; re-check with `cd work/lean && lake env lean` on a scratch file importing
RProof.GenericSelected if you wish): the row theorem has no hypothesis beyond the fixed binders; axioms exactly [propext,
Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]
(the last three via CV.carrierSlotFloor = thm:carrierfloor) — all registered.

YOUR TASK. The row theorem's statement must be the FIXED accepted bundle form `RowShape @GenericSelectedData` — verify it is
byte-identical to the shape the accepted consumers use (cv_R_of_rows (h174 : RowShape @GenericSelectedData) in RALedgers, and the
sibling rows 168/170/172/173/175 after substituting only the theorem and bundle names) and compare GenericSelectedData's fields with
the printed (GSC) statement and its presuppositions (the couple b/ac, the sides P and E, the complete X1 terms T_ν(J) with absent
rows zero, the opposite coorientation by −1); is anything STRONGER or WEAKER than the print; label non-blocking notes. Default to
"not faithful" if in doubt. The proof route (an R-II deletion witness built by exists_bigonData_of_triangle on the switched carrier
diagram, the wall record transport, the carrier structure across the wall, the smoothing identification) is NOT under review — only
the statement.
