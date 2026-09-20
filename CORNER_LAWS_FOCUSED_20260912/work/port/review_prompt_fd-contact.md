You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the statement
you are reviewing and you must not read its proof. Your job is a statement-fidelity review of ONE row against ONE
printed source statement (frame SM15): fd:contact (row 94, a theorem), Lean declaration `SM.fd_contact : SM.FdContactData`
(module SM/FdContactUnits.lean; the structure FdContactData in SM/FdContactStatements.lean).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/fd-contact-source-excerpt-lines-3404-3423.tex.txt (= reference/SM/
   sm-3-statesum.tex 3404-3423, Theorem fd:contact "The contact dictionary and finite-diagram representative bound":
   the front-page over rule and crossing sign; display fd:front-writhe sl(T) = Σ sgn det_xz(u_O, u_U) for a generic positive
   transverse front; display fd:representative-bound sl(T) ≤ −max deg_a P_T − 1 for an individual smooth positive transverse
   knot whose specified xz projection D_T is an ordinary finite regular generic diagram; the two closing sentences).
   Context ONLY to fix notation: sm-3:3424-3492 (its proof — which rows it consumes), 341-343 (def:transverse-front),
   2820-2824 and 3012-3022 (fd:framed-linking, rem:sl-convention), 3341-3365 (src:contact), 3210-3233 (cp:finite-contact-
   path, the endpoint reading), and blueprint/AXIOM_REGISTRY.md §src:contact.
2. The Lean statement: work/reviews/fd-contact-row-reviewer-input-statement.lean.txt (the row module with every proof
   replaced by sorry) and work/reviews/fd-contact-statements-reviewer-input.lean.txt (SM/FdContactStatements.lean with
   proofs stripped: FdContactData with its three fields and docstrings, the CV bundles, the unit Props U_* and the assembly
   statement — the unit Props describe the PROOF ROUTE and are not under review; you may use them only to see that no
   hypothesis is smuggled into the row). The self-linking number: work/reviews/src-contact-reviewer-input-statement.lean.txt
   (SM.slCircle, SM.sl, TransverseKnot.circle/spatial — definitions).
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/TransverseFront.lean
   (TransverseKnot, front, SmoothKnotDiagram.IsDouble/isOver/crossSign/vel/writhe, yOf, det), SM/CeSmoothingRecord.lean
   (SpatialLink, HeightMarking, projLoop), SM/LinkingCalculus.lean (selfLinking — grep), SM/LocalPolynomial.lean (P),
   SM/AdegDefinition.lean (degAZ), SM/LinkDiagram.lean (Diagram), and Mathlib.
4. Disclosed readings: work/AUTHOR_NOTES.md entries "Contact lane (src:contact, SM.sl, rows 94 …)" (D-SC-1..6, FR-SC-1..11,
   FR-FC-1..7) and "src:contact DECLARED …" of 2026-09-15.

KERNEL FACTS (reported by the executor; re-check with `cd work/lean && lake env lean` on a scratch file importing
SM.FdContactUnits if you wish): `SM.fd_contact : SM.FdContactData` with no hypothesis; axioms exactly [propext,
Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word,
SM.src_contact] — all registered literature interfaces (the printed status line says "consumes Literature inputs
src:contact and lit:homfly"; ng:finite-word enters through fd:ng-bound, lp:lm through lp:core).

YOUR TASK: compare the printed statement clause by clause with FdContactData: sentence 1 "In the xz front page the
smaller-y branch is over, and its crossing sign is sgn det_xz(u_O, u_U)" ↔ over_rule_sign (∀ K s t, IsDouble → (isOver s t
↔ yOf K.T s < yOf K.T t) ∧ crossSign s t = sign (det (vel s) (vel t))) — definitional on def:transverse-front's class;
display fd:front-writhe "for a generic positive transverse front, sl(T) = Σ_q sgn det_xz(u_O(q), u_U(q))" ↔ front_writhe
(∀ K : TransverseKnot, sl K = ↑K.front.writhe — is SmoothKnotDiagram.writhe exactly that sum? is "generic positive transverse
front" = the fronts of TransverseKnot?); display fd:representative-bound "Let T be an individual smooth positive transverse
knot whose specified xz projection D_T is an ordinary finite regular generic diagram. With P_T the original campaign
polynomial of this actual diagram, sl(T) ≤ −max deg_a P_T − 1" ↔ representative_bound (∀ K X, Nonempty (K.spatial.HeightMarking
K.spatial.projLoop X) → sl K ≤ ((−degAZ (P X) − 1 : ℤ) : ℝ)): is TransverseKnot exactly "an individual smooth positive
transverse knot whose specified xz projection is an ordinary finite regular generic diagram"; is the polygonal reading of D_T
through HeightMarking of K.spatial (FR-1, FR-FC-1: quantified over every reading; over = smaller y) faithful; is P X "the
original campaign polynomial of this actual diagram"; is degAZ max deg_a; casts. Are the two closing sentences correctly
treated as commentary? Say where the Lean is STRONGER or WEAKER (sl real-valued; readings; class). Default to "not
faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason" (clause-by-clause, cite
source and statement-file line numbers), "discrepancies", "stronger_than_source", "weaker_than_source" (arrays of
strings), "supporting_definitions_inspected" (Lean names), "reviewer_files_read" (relative paths).
