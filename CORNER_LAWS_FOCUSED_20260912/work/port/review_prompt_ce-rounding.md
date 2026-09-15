You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row against ONE printed source statement (frame SM15):
ce:rounding (row 89), Lean declaration `SM.ce_rounding : SM.CeRoundingData` (module SM/CeRounding.lean).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/ce-rounding-source-excerpt-lines-3029-3058.tex.txt (= reference/SM/sm-3-statesum.tex
   3029-3058, Lemma ce:rounding "Ordinary rounding of the exact cusp germs": the hypotheses 3031-3046 (a smooth oriented spatial
   embedding L of finitely many parameter circles; projection p = (x, z); only failures of regularity finitely many isolated cusps;
   other coincidences finitely many transverse double points; no triple points, no cusps on another branch, distinct y heights at
   double points; the exact germ ce:exact-germ at every cusp, u increasing or decreasing), and the conclusion 3047-3056). Context, ONLY
   to fix notation and to see which objects the statement names: sm-3:3059-3169 (its proof — skim: the positive chart, the cutoff, the
   one-cusp replacement, the family, the contact computation 3132-3169 which is commentary), 3170-3209 (ce:smoothing-record, row 90,
   the consumer — accepted as SM.ce_smoothing_record: how the family D_ε and the smoothing are used), 341-343 (def:transverse-front,
   accepted), 1825-1841 (ng:front-domain) if needed.
2. The Lean statement: work/reviews/ce-rounding-reviewer-input-statement.lean.txt — the module SM/CeRounding.lean with EVERY theorem
   proof replaced by `sorry`; the definitions are shown in full and ARE under review (periodicBump, GermData, chart, CuspChoice,
   Choices, core, coreLoop are CONSTRUCTION material used only inside the proof — they are not part of the statement; the statement
   is CuspRoundingWitness (extends the accepted CuspRoundingFamily) and the bundle CeRoundingData with the row theorem
   ce_rounding : CeRoundingData). It compiles. Its module docstring maps notation — verify it, do not trust it. Do NOT open
   work/lean/SM/CeRounding.lean or anything under work/drafts/cerounding/.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/CeSmoothingRecord.lean (row 90,
   ACCEPTED 2026-09-14: the shared spatial-link vocabulary SpatialLink, CuspedProjection (with not_isCusp_of_isDouble as a theorem),
   RegularGenericProjection, HeightMarking, CleanCuspSmoothing (with the field `collar`), CuspRoundingFamily and its lemmas —
   definitions and docstrings), SM/TransverseFront.lean (Space, xOf/yOf/zOf/xzOf, SameT), SM/FrontSmooth.lean (SmoothLoop, Param,
   SameParam), SM/FrontRecordBridge.lean (IsDoubleOf, occSetOf, crossSignOf), SM/Polygon.lean (Plane, det), SM/LinkMoves.lean (IsDisc),
   and Mathlib (Real.smoothTransition, ContDiff, HasDerivAt, deriv, Set.Ioo/Icc, Function.Periodic).

DISCLOSED FIDELITY RISKS recorded by the executor BEFORE the row was stated (work/AUTHOR_NOTES.md entry "Ce:rounding lane (row 89)" of
2026-09-14 ~09:05Z — you MAY read it, together with the entries on row 90 ce:smoothing-record and decision D-1): CE-R1 (FR-1/GAP-1:
RegularGenericProjection is "the diagram" as in def:transverse-front; no polygonal Diagram / HeightMarking is delivered by the row;
consumers take the marking as a hypothesis); CE-R2 (the library's SpatialFamily indexes the slices by all of ℝ, jointly C^∞ on ℝ × ℝ
and embedded everywhere, while the printed family is 0 ≤ λ ≤ 1 with embeddedness outside [0,1] not claimed — met by the time clamp
μ = Real.smoothTransition λ, so on [0,1] the family is the printed one reparametrized); CE-R3 ("no cusps on another branch" derived
from transverse, no field; heights_distinct kept as the printed field though redundant); CE-R4 (the construction's constants differ
from the printed ones — invisible in the statement); CE-R5 ("cleanly smooths the cusps" = the accepted CleanCuspSmoothing WITH the
collar field, decision D-1); CE-R6 (CuspRoundingWitness extends the accepted CuspRoundingFamily by intervals_disjoint_circle, U and
clean_in; row 90 quantifies over the parent, delivered via toCuspRoundingFamily); CE-R7 (fields 2-6 of CeRoundingData are projections
of the witness; the theorem content is exists_family and const_of_no_cusps); CE-R8 (readings: "spatial embedding" = injective
immersion of compact circles; orientation = parameter direction; ExactCuspGerm on an OPEN interval with y' ≠ 0; the printed 0 < c is
never used); CE-R9 (the two disclaimers and the contact computation are commentary; nothing Legendrian/transverse/sl is stated);
CE-R11 (non-vacuity: the kernel-checked module work/lean/SM/CeRoundingNonVacuity.lean — which you MAY read — shows the round circle at
height 0 is a CuspedProjection and a RegularGenericProjection with a constant CleanCuspSmoothing and constant CuspRoundingFamily);
CE-R12 (= row 90's K-5): IsDisc is a CONVEX compact disc for the clean cusp neighbourhood, an unprinted restriction inherited from the
accepted vocabulary; CE-R13: no standalone CUSPED witness was kernel-checked (the row's own proof constructs the per-cusp fields for
every cusp); CE-R7 addendum: bundle fields 2-6 quantify over any c (the printed 0 < c is not demanded).

YOUR TASK: compare the printed lemma clause by clause with the hypotheses (CuspedProjection: which printed hypothesis is which field;
is "finitely many isolated cusps" / "finitely many transverse double points" / "no triple points" / "no cusps on another branch" /
"distinct heights" / the exact germ with A ≠ 0 and u increasing or decreasing each rendered, added or dropped?) and the conclusion
(3047-3056: "a jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings with L_0 = L, fixed outside disjoint cusp
parameter intervals, such that for every λ > 0 its xz projection is an ordinary finite regular generic diagram. It cleanly smooths the
cusps, creates no crossing, and retains every original crossing with its oriented decorated data. All original parameter circles,
component labels and traversal orientations are retained. With no cusps take the constant family." — plus the disclaimer sentence
3055-3056 which asserts nothing) versus CuspRoundingWitness and the fields of CeRoundingData, expanding every definition to primitives (through the accepted
row-90 vocabulary). Every printed clause must have a field and every field a printed clause or a disclosed extra; CE-R2 (the ℝ-indexed
family) and CE-R6 (the witness extension) must be judged explicitly: faithful renderings or class changes? Say where the Lean is
STRONGER or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
