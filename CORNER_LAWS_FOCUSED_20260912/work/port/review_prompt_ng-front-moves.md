You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statements you are reviewing and you must not read their proofs. Your job is a
statement-fidelity review of ONE row (named in your task) against ONE printed source statement (frame SM15):
row 77 ng:front-I — `SM.ng_front_I : SM.NgFrontIClauses` (field typeI_B), or
row 79 ng:front-III — `SM.ng_front_III : SM.NgFrontIIIClauses` (fields typeIII_D, typeIII_w, typeIII_d, typeIII_B), or
row 80 ng:deletions — `SM.ng_deletions : SM.NgDeletionsClauses` (fields zigzag_s, zigzag_B, crossedCusp_s, crossedCusp_B)
(all in the module SM/FrontRowsW3.lean, the front certificate rows lane's wave-3 delta module).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: row 77 = work/reviews/ng-front-i-source-excerpt-lines-1950-1953.tex.txt (= reference/SM/sm-3-statesum.tex
   1950-1953, Lemma ng:front-I "Front type I"); row 79 = work/reviews/ng-front-iii-source-excerpt-lines-1990-1993.tex.txt (= sm-3
   1990-1993, Lemma ng:front-III "Front type III"); row 80 = work/reviews/ng-deletions-source-excerpt-lines-2008-2013.tex.txt (= sm-3
   2008-2013, Lemma ng:deletions "Zigzag and crossed-cusp deletion"). Context, ONLY to fix notation and to see which objects the
   statements name: sm-3:1825-1841 (ng:front-domain: D, w, s, the rounding), 1843-1920 (the certificate B = D − w − d − 1 and the front
   WORDS with their moves: which letter patterns are the front type-I, type-II, type-III moves, the zigzag deletion and the crossed-cusp
   shortcut), 1921-1949 (ng:commutation, accepted row 76: the words framework), 1954-1971 / 1994-2007 / 2014-2045 (the printed proofs of
   the three rows — skim for the moves' geometry: an RI / RIII move of the realizations, the deletion's effect on s and B), and
   blueprint/AXIOM_REGISTRY.md section ng:finite-word (the accepted interface: the elementary moves and deletions of front words).
2. The Lean statement: work/reviews/ng-front-moves-reviewer-input-statement.lean.txt — the module SM/FrontRowsW3.lean with EVERY theorem
   proof replaced by `sorry` (989 theorems); definitions shown in full. The STATEMENT PART for your row: the structures NgFrontIClauses
   (line 52), NgFrontIIIClauses (63), NgDeletionsClauses (71) — note NgFrontIIClauses and NgLocalFrontBoundClauses are declared here for a
   later module and are NOT under review — and the row theorems ng_front_I (≈6451), ng_front_III (≈6456), ng_deletions (≈6462). The
   leaves typeIII_site (≈1220), typeI_move (≈6405), crossedCusp_move (≈6416) and everything in namespaces SM.FrontRows.U5 / U6 are the
   PROOF construction (polygonal RIII / RI / deletion moves between the standard realizations), shown only because definitions are not
   withheld; do not review them. It compiles. Do NOT open work/lean/SM/FrontRowsW3.lean or anything under work/drafts/frontrows/.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/FrontWords.lean (Word, Letter, the move
   patterns IsTypeI, IsTypeII, IsTypeIII, IsZigzagDeletion, IsCrossedCuspShortcut — read them and compare with the printed patterns of
   the section; also IsComm, IsCircleDeletion, IsCuspSkein for orientation), SM/FrontWordsBase.lean and SM/FrontWords.lean (OWord = closed
   oriented words, sCount), SM/FrontRealize*.lean (SM.realize : OWord → PLFront, the standard realization), SM/FrontPL.lean (PLFront:
   downCount D, writhe w, sCount s, defect B, diagram, the identity rounding), SM/LocalPolynomial.lean (P), SM/LinkLaurentRing.lean
   (degAZ, line ~446: the a-degree with the convention degAZ 0 = 0), SM/FrontRowsW2.lean lines 1-100 (the lane's header and statement
   part, for the conventions) — do NOT read its proofs. Do NOT open other work/ files.

DISCLOSED FIDELITY RISKS recorded by the executor BEFORE the rows were stated (work/AUTHOR_NOTES.md entry "Front certificate rows 76-83"
of 2026-09-14 ~07:27Z and the later frontrows entries — you MAY read them; also work/drafts/frontrows/PLAN_FINAL.md §1 and §7): FR-1/FR-5
(accepted): the front block on the PL class and on closed oriented WORDS through the standard realization SM.realize; D, w, s, B read on
the realization; FR-8 (class narrowing): rows 77-82 are stated on realizations of closed oriented words, the printed rows on fronts — the
moves exist in the source only as word patterns, and the narrowing is CLOSED by the accepted row 76's field represent (every front is
represented by a word); FR-6: deletion directions only for types I/II (equalities, so the creation direction is the same statement);
the deletion rows (zigzag, crossed cusp) are stated in the DELETION direction W → W′ with s decreasing and B not increasing — check the
inequality direction against the printed sentence; FR-13: every polynomial clause reaches the literature interface SM.lp_lm through P, as
PLFront.defect itself does; FR-15 (design): no block-rectangle move discs; the realizations of W and W′ are compared through a polygonal
move (RI / RIII) plus a record isomorphism — proof material, not statement; FR-1/FR-16: d = degAZ (P (realize W).diagram) on the identity
rounding; degAZ 0 = 0 is inert since P of a diagram is nonzero (lp:core).

YOUR TASK (for YOUR row): compare the printed lemma clause by clause with the Lean fields, expanding every definition to primitives (the
word pattern of the move/deletion: is it exactly the printed letter pattern with the printed index shifts? for row 77: does the printed
lemma assert only "preserves B", or also D, w, d — and does the field set match; for row 79: D, w, d and B preserved; for row 80: the
printed effect on s ("two fewer singularities" / "one fewer") and on B (preserved? not increased? — read the exact printed wording and check
the direction of ≤), for both the zigzag deletion and the crossed-cusp shortcut). Every printed clause must have a field and every field a
printed clause or a disclosed extra. Judge the class reading (words/realizations, FR-8) explicitly: faithful given the disclosed design, or
a blocking class change? Say where the Lean is STRONGER or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
