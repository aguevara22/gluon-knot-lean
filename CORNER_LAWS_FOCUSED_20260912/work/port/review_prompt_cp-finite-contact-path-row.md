You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the
statement you are reviewing and you must not read its proof. Your job is a statement-fidelity review of ONE row
against ONE printed source statement (frame SM15): cp:finite-contact-path (row 91), Lean declaration
`SM.cp_finite_contact_path : SM.ContactPathData` (module SM/ContactPath.lean). The row is now claimed as PROVED: the
2026-09-14 review accepted the conditional theorem `cp_finite_contact_path_of_descent : AmbientIsotopyDescent →
ContactPathData` (work/reviews/cp-finite-contact-path-conditional.json, which you MAY read), and on the author's
decision of 2026-09-15 the clause `AmbientIsotopyDescent` is now the registered literature axiom
`SM.lit_homfly_descent` (second declaration of lit:homfly; under a separate interface review).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cp-finite-contact-path-source-excerpt-lines-3210-3233.tex.txt
   (= reference/SM/sm-3-statesum.tex 3210-3233). Context, ONLY to fix notation and to see which objects the proof uses:
   sm-3:3234-3327 (its proof), 3029-3058 (ce:rounding, accepted), 3170-3209 (ce:smoothing-record, accepted), 341-343
   (def:transverse-front), 905-935 (lit:homfly's registry text) and blueprint/AXIOM_REGISTRY.md section lit:homfly.
2. The Lean statement: work/reviews/cp-finite-contact-path-row-reviewer-input-statement.lean.txt (the row module with
   the proof withheld) and work/reviews/cp-finite-contact-path-reviewer-input-statement.lean.txt (the statements
   module: `ContactPathData` with one field per printed clause, `AmbientIsotopyDescent` and its companions, the
   conditional theorem with proof withheld); work/reviews/lit-homfly-descent-reviewer-input-statement.lean.txt (the
   axiom). Do NOT open work/drafts/ or the proofs in work/lean/SM/ContactPathOfDescent.lean (lines > 270).
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/CeSmoothingRecord.lean
   (SpatialLink, CuspedProjection, RegularGenericProjection, HeightMarking, CleanCuspSmoothing, SpatialFamily,
   CuspRoundingFamily), work/lean/SM/CeRounding.lean lines 1-200, SM/TransverseFront.lean, SM/FrontSmooth.lean,
   SM/FrontRecordBridge.lean, SM/LinkInterfaces.lean, SM/LinkMoves.lean (definitions), SM/LinkDiagram.lean,
   SM/LocalPolynomial.lean (P), SM/PolynomialBlock.lean (P_eq_homfly — statement), and Mathlib.
4. Disclosed readings you MAY read: work/AUTHOR_NOTES.md entries "Row 91 cp:finite-contact-path PROVED MODULO the
   descent clause" (FR-CP-1..FR-CP-10, D-CP-1), "D-GAP2" and "D-GAP2-2b" (FR-LHD-1..4).

KERNEL FACTS (reported by the executor; you may re-check with `cd work/lean && lake env lean` on a scratch file
importing SM.ContactPath — compiling takes ~1 min): `SM.cp_finite_contact_path` depends on the axioms propext,
Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness — all registered in
lean/axiom-policy.json; the row has NO hypothesis.

YOUR TASK: (A) compare the printed hypotheses (C finite nonempty union of oriented circles; L a smooth embedding with
nonvanishing derivative; F regular except at finitely many cusps each with the exact germ cp:exact-cusp; only finitely
many transverse double points, none at a cusp, distinct y values; the supplied jointly smooth family G_t from L to T;
D_T ordinary finite regular generic) and the conclusion ("every clean ordinary cusp smoothing S(F), with smaller y over
at the unchanged crossings, has P_{S(F)} = P_{D_T}", display cp:endpoint-polynomial) with `ContactPathData`, expanding
every definition to primitives through the accepted row-89/90 vocabulary; is P_{D_T} read faithfully (D_T read with T's
own heights, FR-CP-6); is the quantification over readings faithful (FR-CP-1); is the ℝ-indexed family a faithful
rendering of "a supplied jointly smooth family G_t" (FR-CP-5)? (B) confirm that the row theorem's type is exactly
`ContactPathData` with no extra hypothesis and that the sentence the proof needed beyond the frozen interfaces is now
exactly the registered axiom (nothing else was added). Say where the Lean is STRONGER or WEAKER; label non-blocking
notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason" (clause-by-clause, cite
source and statement-file line numbers), "discrepancies", "stronger_than_source", "weaker_than_source" (arrays of
strings), "supporting_definitions_inspected" (Lean names), "reviewer_files_read" (relative paths).
