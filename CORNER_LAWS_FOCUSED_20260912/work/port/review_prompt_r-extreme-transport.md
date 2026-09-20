You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the statement you are
reviewing and you must not read its proof. Your job is a statement-fidelity review of ONE row against its printed source:
R:extreme_transport (row 176; a package obligation of the R lane with a FIXED name `RProof.extreme_transport` and a FIXED bundle
statement `RowShape @ExtremeTransportData`, whose bundle `ExtremeTransportData` was accepted earlier in the R lane), module
RProof/ExtremeTransport.lean.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. Printed source, verbatim: work/reviews/r-extreme-transport-source-excerpt-R_EXTREME_SINGLETON_TRANSPORT_PROOF.md.txt
   (= reference/R/RA/R_EXTREME_SINGLETON_TRANSPORT_PROOF.md, whole file: the extreme singleton transport row —
   the affected carrier's X1 term is transported across the wall by an R-II port of the switched positive lift and the oriented
   smoothing splits it into two clean outer carriers with the writhe / rotation / one-dissent ledgers (13)-(14)), read with R_ASSEMBLY_SPEC.md and EXECUTION.json at the
   handoff root (the obligation's place in the R assembly) and, for notation only, reference/R/RA/R_ATTACHMENT_WARRANTS.md (R-LOC,
   R-PAR), R_GENERIC_ORBIT_ACTUAL_TABLE.md, R_GENERIC_NONSELECTED_SELECTOR_PROOF.md, and the CV definitions in reference/R/CV/.
2. The Lean statement: work/reviews/r-extreme-transport-reviewer-input-statement.lean.txt (RProof/ExtremeTransport.lean with the proof
   replaced by sorry: the row theorem in the FIXED shape) and, for the fixed bundle `ExtremeTransportData` and `RowShape`,
   work/reviews/r-ledgers-reviewer-input.lean.txt (RProof/RALedgers.lean stripped: RowShape, est_PortData, est_port_relation, est_row_H, est_row, est_ledger,
   est_extreme_transport_of — statements only) and the accepted RProof/X1Rows.lean where ExtremeTransportData is defined
   (grep `structure ExtremeTransportData`).
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/RProof/X1Rows*.lean, RProof/RALedgers.lean,
   RProof/GenericTransport.lean (GT_Endpoint, the wall transport), work/lean/CV/ (Event, Punctured, carrierDiagram, geoPositiveLift,
   GeoComponent, X1, Omega1, groupedWrithe, carrierR, weight — grep for the names you meet), work/lean/SM/BigonDeletion.lean
   (BigonData, exists_rii_deletion: the R-II deletion the proof constructs), SM/Smoothing.lean (smoothDiagram), and Mathlib.
4. Disclosed readings: work/AUTHOR_NOTES.md entries of 2026-09-15 titled "CV/R tail … design panel judged", "Moves toolkit …"
   (D-RM-1..4), "Row 176: the j-corner site landed" (D-RM-5: the library's literal port field is unrealisable and the row closes
   through a weak-port replay), "Rows 174/176: record transports closed", "Rows 174/176 all units back" (D-RM-6: the rot / alt
   fields need wind ≠ 0; the row closes through a wind = 0 split), "Row 176 wave 1 assembled", and the acceptance entry — these
   concern the PROOF ROUTE and the library interface structures, not the row statement; for the fixed bundle also
   work/drafts/rlane2/NOTES_FINAL.md §7 (the accepted statement panel's clause map of ExtremeTransportData — you MAY read this one
   draft file).

KERNEL FACTS (reported by the executor; re-check with `cd work/lean && lake env lean` on a scratch file importing
RProof.ExtremeTransport if you wish): the row theorem has no hypothesis beyond the fixed binders; axioms exactly [propext,
Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]
(the last three via CV.carrierSlotFloor = thm:carrierfloor) — all registered.

YOUR TASK. The row theorem's statement must be the FIXED accepted bundle form `RowShape @ExtremeTransportData` — verify it is
byte-identical to the shape the accepted consumers use (cv_R_of_rows (h176 : RowShape @ExtremeTransportData) in RALedgers, and the
sibling rows 168/170/172/173/174/175 after substituting only the theorem and bundle names) and compare ExtremeTransportData's fields
with the printed statement of R_EXTREME_SINGLETON_TRANSPORT_PROOF.md and its presuppositions (the extreme singleton, the two sides,
the affected carrier, the complete X1 terms with absent rows zero, the sign conventions); is anything STRONGER or WEAKER than the
print; label non-blocking notes. Default to "not faithful" if in doubt. The proof route (the weak R-II port built from an actual
R-II deletion, the wall record transport, the smoothing into two components, the outer-carrier identification, the curl removal, the
wind = 0 split) is NOT under review — only the statement.
