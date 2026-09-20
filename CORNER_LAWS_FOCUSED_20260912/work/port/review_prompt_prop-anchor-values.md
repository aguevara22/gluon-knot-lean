You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the statement you
are reviewing and you must not read its proof. Your job is a statement-fidelity review of ONE row against ONE printed source
statement (frame SM15): prop:anchor-values (row 122), Lean declaration `SM.prop_anchor_values : SM.AnchorValuesData` (module
SM/AnchorValuesRow.lean; the structures AnchorValuesHypotheses / AnchorValuesData in SM/AnchorValues.lean; the descent of the
corner state sum C to the polygon quotient, `cornerPolygon`, in SM/CornerPolygon.lean).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/prop-anchor-values-source-excerpt-lines-461-476.tex.txt (= reference/SM/
   sm-5-transport.tex 461-476, Proposition prop:anchor-values). Context ONLY to fix notation: sm-5:477-505 (its proof), the
   transport chapter's accepted rows (def:anchors and the anchor types ZeroAnchor / LoopAnchor / LoopAnchorZero, thm:A-soft,
   the uniqueness hypotheses UniquenessHypotheses.chamber / .soft, thm:uniqueness — grep in reference/SM/sm-5-transport.tex and
   find their Lean modules through work/lean/lean-declarations.json), def:soft and lem:soft-generic (reference/SM/
   sm-4-knotlaws.tex, grep "def:soft"), def:C (sm-3, grep "def:C") and the accepted thm:C-soft (sm-4:984-991, SM/CSoft.lean's
   statement CSoftData in SM/CornerChainStatements.lean).
2. The Lean statements: work/reviews/prop-anchor-values-reviewer-input-statement.lean.txt (the row module, proof withheld),
   work/reviews/anchor-values-statements-reviewer-input.lean.txt (SM/AnchorValues.lean with proofs replaced by sorry:
   AnchorValuesHypotheses F, AnchorValuesData with its nine fields and docstrings, the av_ helper statements — proof route, not
   under review — and anchor_values_of), work/reviews/corner-polygon-reviewer-input.lean.txt (cornerPolygonSum / cornerPolygon:
   the descent of cornerStateSum to GenericPolygon by cornerStateSum_genericShift). Docstrings quote the source — verify them.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/AnchorsDefinition.lean (def:anchors:
   ZeroAnchor, LoopAnchor, LoopAnchorZero, Admissible / MinimalAdmissible, the anchor parameters), SM/Uniqueness.lean
   (UniquenessHypotheses, amplitude, GenericPolygon), SM/CornerStateSum.lean (cornerStateSum, cornerStateSum_genericShift),
   SM/SoftGenericLemma.lean, SM/SoftAmplitudeSectors.lean, SM/SoftParentEdges.lean (softParentEdge, softOldIndex), SM/CChamber.lean,
   and Mathlib.
4. Disclosed readings: work/AUTHOR_NOTES.md entries "Comparison lane (rows 122 prop:anchor-values, 127 thm:comparison, 128
   cor:C-inherits): design panel judged …" of 2026-09-15 (decisions D-CM-1..5 and the fidelity risks FR-CM-1..17) and "Comparison
   lane fully proved …" (the two extra readings FR-CM-3′: AnchorValuesData quantifies over every ZeroAnchor / LoopAnchor /
   LoopAnchorZero WITHOUT def:anchors' case conditions — a proved generalisation; FR-CM-9′ on the cusp law, not this row).

KERNEL FACTS (reported by the executor; re-check with `cd work/lean && lake env lean` on a scratch file importing
SM.AnchorValuesRow if you wish — the machine is loaded, batch your checks): `SM.prop_anchor_values : AnchorValuesData` with no
hypothesis; axioms exactly [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm,
SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact] — all registered (inherited from SM.thm_C_soft, row 112).

YOUR TASK: compare the printed proposition clause by clause with the nine fields of AnchorValuesData over
AnchorValuesHypotheses F (= UniquenessHypotheses.chamber / .soft verbatim — is that exactly the printed standing hypothesis on
F?): the zero / loop / loop-zero anchor values at the anchor's own parameter (zero, loop, loopZero); the (L) / (L₀) turn clauses
(loop_turn, loopZero_turn — the latter asserts BOTH readings of "orientation sign of the parent triangle": the common turn sign
and the rotation number, FR-CM-3 / D-CM-1 — is asserting both faithful or stronger?); C_hypotheses : AnchorValuesHypotheses
cornerPolygon (C descended to the polygon quotient — is the descent the printed "C" of the proposition?); the A_g clauses at
every root ≠ soft edge with ∃! parent root (A_zero / A_loop / A_loopZero). Judge FR-CM-3′ (quantification over every anchor
without def:anchors' case conditions Admissible m r / MinimalAdmissible (m+1) r ∧ 2 ≤ |r| / (m+1, r) = (4, 0) — a generalisation:
is it faithful as a strengthening, or does it change the proposition?). Expand definitions to primitives. Say where the Lean is
STRONGER or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason" (clause-by-clause, cite source
and statement-file line numbers), "discrepancies", "stronger_than_source", "weaker_than_source" (arrays of strings),
"supporting_definitions_inspected" (Lean names), "reviewer_files_read" (relative paths).
