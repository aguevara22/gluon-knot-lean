You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statements you are reviewing and you must not read their proofs. Your job is a
statement-fidelity review of ONE row (named in your task) against ONE printed source statement (frame SM15):
row 81 ng:circle — Lean declaration `SM.ng_circle : SM.NgCircleClauses`, or
row 82 ng:cusp-skein — Lean declaration `SM.ng_cusp_skein : SM.NgCuspSkeinClauses`
(both in the module SM/FrontRowsW2.lean, the front certificate rows lane).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: row 81 = work/reviews/ng-circle-source-excerpt-lines-2046-2051.tex.txt (= reference/SM/sm-3-statesum.tex
   2046-2051, Lemma ng:circle "Standard front circles": "Deleting a separated standard front circle with nonempty remainder preserves B.
   A single standard front circle, and any union of such circles, has B = 0."); row 82 = work/reviews/ng-cusp-skein-source-excerpt-lines-
   2076-2083.tex.txt (= sm-3 2076-2083, Lemma ng:cusp-skein "Cusp-skein inequality": "For either principal direction of an oriented
   cusp-skein interchange, B of the earlier branch is at least the minimum of B of the other principal branch and B of the unique
   compatible smoothing. The smoothing has one fewer singularity; the principal branches have the same singularity count."). Context, ONLY
   to fix notation and to see which objects the statements name: sm-3:1825-1841 (ng:front-domain: fronts, D(F), w(F), s(F), the rounding
   S(F)), 1843-1920 (ng:smoothing-record and the definition of the certificate B = w − D … − max-degree quantity — read how B is defined
   in the source: the accepted def rows of this block), 1921-1949 (ng:commutation: the section computes on Rutherford's front WORDS — the
   printed second sentence says every front is represented by a finite elementary front word), 2052-2075 and 2084-2170 (the proofs of the
   two rows and the cusp-skein templates: which word patterns are the "standard front circle", "separated", "cusp-skein interchange",
   "principal direction", "compatible smoothing"), and blueprint/AXIOM_REGISTRY.md section ng:finite-word (the accepted literature
   interface SM.ng_finite_word: standard circle base and the finite elementary word).
2. The Lean statement: work/reviews/ng-circle-cusp-skein-reviewer-input-statement.lean.txt — the module SM/FrontRowsW2.lean with EVERY
   theorem proof replaced by `sorry` (936 theorems); the definitions are shown in full. The STATEMENT PART for your row is: lines 55-82
   (SmoothFront.NonsingularDeformation — not used by rows 81/82; NgCircleClauses with fields circleDeletion_B, single_B, union_B;
   NgCuspSkeinClauses with fields earlier_branch, unique_smoothing, smoothing_s, principal_s) and the row theorems near the end (grep
   `theorem ng_circle` / `theorem ng_cusp_skein`); everything else in the file is the lane's infrastructure (namespaces SM.FrontRows.U1..U8R),
   shown only because definitions are not withheld — do not review it. It compiles. Do NOT open work/lean/SM/FrontRowsW2.lean or anything
   under work/drafts/frontrows/.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/FrontWords.lean (Word, Letter, the move
   patterns: IsCircleDeletion 463, IsCuspSkeinStep 475, IsCuspSkein 483 = either principal direction, the other patterns), SM/FrontWordsBase.lean
   (OWord = closed oriented words; sCountSyn; IsStandardCircleBase), SM/FrontRealize*.lean (SM.realize : OWord → PLFront, the standard
   realization of a word as a PL front — FrontRealizeGeometry / Base / Deform / Standard / Correspondence / Slots), SM/FrontPL.lean (PLFront:
   the PL front class with downCount D, writhe w, sCount s, defect B = the certificate, IsStandardCircles 513, the identity rounding and the
   accepted polynomial P of the rounded diagram), SM/FrontInterfaces.lean (PLFront-level statements of the accepted rows 73-75 and the axiom
   SM.ng_finite_word), SM/FrontSmooth.lean (SmoothFront, the accepted def ng:front-domain — the smooth class), SM/LocalPolynomial.lean (P),
   SM/PolynomialBlock.lean (degAZ etc. — statements only). Do NOT open other work/ files.

DISCLOSED FIDELITY RISKS recorded by the executor BEFORE the rows were stated (work/AUTHOR_NOTES.md entries "Front certificate rows" /
"frontrows" of 2026-09-14 — you MAY read them, and work/drafts/frontrows/PLAN_FINAL.md §1 (readings) and §7 (FR-8..FR-17)):
FR-1 / FR-5 (accepted earlier): the front block is formalised on the PL front class PLFront and on closed oriented WORDS through the standard
realization SM.realize — the document's own computational framework (the section computes on Rutherford's words; the moves exist only as
word patterns); D, w, s, B are read on the realization. FR-8 (class narrowing of the certificate rows): rows 77-82 are stated on
realizations of closed oriented words, the printed rows are on fronts; justified by the printed text and CLOSED by the printed second
sentence of ng:commutation ("every front is represented by a finite elementary front word"), kept as the field `represent` of row 76 on the
smooth class (row 76 is a separate row, in progress) — judge whether stating rows 81/82 on words is faithful given that reading.
FR-11 (row 81 sentence 2): "a single standard front circle, and any union of such circles, has B = 0" is stated on PLFront with the geometric
predicate IsStandardCircles (the smallest accepted class carrying the geometric notion; not the smooth class); sentence 1 on words
(IsCircleDeletion with the "nonempty remainder" built into the pattern — check). FR-12 ("unique"): the definite article "the unique
compatible smoothing" is rendered as the field unique_smoothing (any two compatible smoothings have equal letters); "either principal
direction" = IsCuspSkein is the symmetric disjunction of the two IsCuspSkeinStep directions; right-cusp templates ("by relabeling",
sm-3:2164-2166) are outside the row, as in the accepted interface. FR-13: every polynomial clause reaches the literature interface SM.lp_lm
through P, as PLFront.defect itself does. FR-15: no block-rectangle move discs (design). Also: "singularity count" = sCount (cusps +
crossings) on the realization; "one fewer singularity" = (realize C).sCount + 1 = (realize A).sCount.

YOUR TASK (for YOUR row): compare the printed lemma clause by clause with the Lean fields, expanding every definition to primitives (what is
a "separated standard front circle with nonempty remainder" as the word pattern IsCircleDeletion? does `defect` on realizations render B?
what is IsStandardCircles and does it capture "a single standard front circle, and any union of such circles"; is F.Γ.c = 1 "single"? for
row 82: is the inequality direction right ("B of the earlier branch is at least the minimum …"), is "the earlier branch" A, "the other
principal branch" A′ and "the compatible smoothing" C in IsCuspSkein A A′ C, in both principal directions? are the two count sentences
rendered by smoothing_s and principal_s?). Every printed clause must have a field and every field a printed clause or a disclosed extra.
Judge the class reading (words/realizations, FR-8; PLFront for 81's second sentence, FR-11) explicitly: faithful given the disclosed
design, or a blocking class change? Say where the Lean is STRONGER or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
