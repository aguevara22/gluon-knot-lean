You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the statement you are
reviewing and you must not read its proof. Your job is a statement-fidelity review of ONE row against its printed source:
R:extreme_selected (row 177; a package obligation of the R lane with a FIXED name `RProof.extreme_selected` and a FIXED bundle
statement `RowShape @ExtremeSelectedData`, whose bundle `ExtremeSelectedData` was accepted earlier in the R lane), module
RProof/ExtremeSelected.lean.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. Printed source, verbatim: work/reviews/r-extreme-selected-source-excerpt-R_EXTREME_SELECTED_COUPLE_PROOF.md.txt
   (= reference/R/RA/R_EXTREME_SELECTED_COUPLE_PROOF.md, whole file: the extreme selected complementary couple row —
   the selected complementary couple identity at a simple RIII wall in the extreme orbit: the switched-RIII transport of the contact
   diagram, the R-II after smoothing, the three-way carrier split with the outer polynomials f_A, f_B, f_C and the ledger), read with R_ASSEMBLY_SPEC.md and EXECUTION.json at the
   handoff root (the obligation's place in the R assembly) and, for notation only, reference/R/RA/R_ATTACHMENT_WARRANTS.md (R-LOC,
   R-PAR), R_GENERIC_ORBIT_ACTUAL_TABLE.md, R_GENERIC_NONSELECTED_SELECTOR_PROOF.md, and the CV definitions in reference/R/CV/.
2. The Lean statement: work/reviews/r-extreme-selected-reviewer-input-statement.lean.txt (RProof/ExtremeSelected.lean with the proof
   replaced by sorry: the row theorem in the FIXED shape) and, for the fixed bundle `ExtremeSelectedData` and `RowShape`,
   work/reviews/r-ledgers-reviewer-input.lean.txt (RProof/RALedgers.lean stripped: RowShape, esc_MoveData, esc_FullSplitData, esc_interface, esc_couple, esc_ledger,
   esc_extreme_selected_of — statements only) and the accepted RProof/X1Rows.lean where ExtremeSelectedData is defined
   (grep `structure ExtremeSelectedData`).
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/RProof/X1Rows*.lean, RProof/RALedgers.lean,
   RProof/GenericTransport.lean (GT_Endpoint, the wall transport), work/lean/CV/ (Event, Punctured, carrierDiagram, geoPositiveLift,
   GeoComponent, X1, Omega1, groupedWrithe, carrierR, weight — grep for the names you meet), work/lean/SM/BigonDeletion.lean
   (BigonData, exists_rii_deletion: the R-II deletion the proof constructs), SM/Smoothing.lean (smoothDiagram), and Mathlib.
4. Disclosed readings: work/AUTHOR_NOTES.md entries "CV/R tail … design panel judged" (D-CVT-1..6, FR-R-174..177), "Moves toolkit …"
   (D-RM-1..4), the 2026-09-15 audits A-177-1 / A-177-2 and the 2026-09-19 entries "D-AUTH-20260919", "Row 177: the non-kink question is
   RESOLVED …" and the acceptance entry — these concern the PROOF ROUTE (the trans-free copy of the accepted RIII transport, the
   weak-form replays, the kink case handled by a flat subdivision instead of the printed bigon move), not the row statement; for the fixed bundle also
   work/drafts/rlane2/NOTES_FINAL.md §7 (the accepted statement panel's clause map of ExtremeSelectedData — you MAY read this one
   draft file).

KERNEL FACTS (reported by the executor; re-check with `cd work/lean && lake env lean` on a scratch file importing
RProof.ExtremeSelected if you wish): the row theorem has no hypothesis beyond the fixed binders; axioms exactly [propext,
Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]
(the last three via CV.carrierSlotFloor = thm:carrierfloor) — all registered.

YOUR TASK. The row theorem's statement must be the FIXED accepted bundle form `RowShape @ExtremeSelectedData` — verify it is
byte-identical to the shape the accepted consumers use (cv_R_of_rows (h176 : RowShape @ExtremeSelectedData) in RALedgers, and the
sibling rows 168/170/172/173/174/175/176 after substituting only the theorem and bundle names) and compare ExtremeSelectedData's fields
with the printed statement of R_EXTREME_SELECTED_COUPLE_PROOF.md and its presuppositions (the extreme orbit K3/empty complement,
the selected couple, the two sides, the complete X1 terms with absent rows zero, the sign table); is anything STRONGER or WEAKER than the
print; label non-blocking notes. Default to "not faithful" if in doubt. The proof route (the switched G11 transport on a trans-free copy of the
accepted configuration type, the value-form R-II after smoothing incl. the kink case by subdivision, the carrier split, the outer
polynomials) is NOT under review — only the statement.
