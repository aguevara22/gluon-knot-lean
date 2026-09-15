You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row against ONE printed source statement (frame SM15):
ng:commutation (row 76), Lean declaration `SM.ng_commutation : SM.NgCommutationClauses` (module SM/FrontRowsW2S.lean; fields comm_D,
comm_w, comm_d, comm_B, deform_D, deform_w, deform_d, deform_B, represent).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/ng-commutation-source-excerpt-lines-1921-1927.tex.txt (= reference/SM/sm-3-statesum.tex
   1921-1927, Lemma ng:commutation "Commutations and nonsingular deformation": "Disjoint-gadget commutations and deformations through
   fronts without a singular event preserve D, w, d, and hence B. Every supplied finite front can be represented by a finite elementary
   front word."). Context, ONLY to fix notation and to see which objects the statement names: sm-3:1825-1841 (ng:front-domain: fronts F,
   D(F) downward cusps, w(F) writhe, s(F), the rounding S(F)), 1843-1920 (ng:smoothing-record and the certificate B = D − w − d − 1 with
   d = deg_a P_{S(F)} — the accepted definition rows; how the section sets up Rutherford's front words and their disjoint-gadget
   commutations), 1928-1949 (the printed proof: which commutation patterns, what "deformation without a singular event" means, and how the
   word representing a front is produced — vertical cuts of a perturbed front), and blueprint/AXIOM_REGISTRY.md section ng:finite-word (the
   accepted interface: finite elementary words, standard circle base).
2. The Lean statement: work/reviews/ng-commutation-reviewer-input-statement.lean.txt — the module SM/FrontRowsW2S.lean with EVERY theorem
   proof replaced by `sorry` (518 theorems); definitions shown in full. The STATEMENT PART is the structure `NgCommutationClauses` (near line
   3761) and the theorem `ng_commutation` (near line 3783); the leaf `represent` (near 3749, proof withheld) is the ninth clause's content;
   the structure `SmoothFront.NonsingularDeformation` lives in the imported module SM/FrontRowsW2.lean (lines 55-65 of its ported file —
   read it there). Everything else in the file (namespace SM.FrontRows.U8R: the sweep construction — cuts, events, letters, the word, Φ,
   the traversal) is the proof of `represent`, shown only because definitions are not withheld; do not review it. It compiles. Do NOT
   open work/lean/SM/FrontRowsW2S.lean or anything under work/drafts/frontrows/.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/FrontRowsW2.lean lines 1-100 (the header and
   the statement part: SmoothFront.NonsingularDeformation; the module is the lane's shared infrastructure — you may grep it for
   definitions but need not read its proofs), work/lean/SM/FrontWords.lean (Word, Letter, IsCommStep / IsComm 412-…: the disjoint-gadget
   commutation patterns; read them and compare with the printed "disjoint-gadget commutations"), SM/FrontWordsBase.lean (OWord = closed
   oriented words, sCountSyn), SM/FrontRealize*.lean (SM.realize : OWord → PLFront, the standard realization), SM/FrontPL.lean (PLFront:
   downCount D, writhe w, sCount s, defect B, diagram, the identity rounding), SM/FrontSmooth.lean (SmoothFront — the accepted def
   ng:front-domain: downCount, writhe, sCount, IsRounding S, defect S, Marking; Param, cusps, crossings), SM/LinkRecord.lean and
   SM/LinkDiagramRecord.lean (Record, RecordIso, Diagram.record — the named record of a diagram), SM/LocalPolynomial.lean (P),
   SM/PolynomialBlock.lean (degAZ — statement only). Do NOT open other work/ files.

DISCLOSED FIDELITY RISKS recorded by the executor BEFORE the row was stated (work/AUTHOR_NOTES.md entry "Front certificate rows 76-83" of
2026-09-14 ~07:27Z and the later frontrows entries — you MAY read them; also work/drafts/frontrows/PLAN_FINAL.md §1 (readings) and §7
(FR-8..FR-17)): FR-1/FR-5 (accepted): the front block is formalised on the PL front class and on closed oriented words through SM.realize,
D, w, s, B read on the realization; FR-8: sentence 1's COMMUTATION clause is stated on realizations of closed oriented words (comm_D/w/d/B
with IsComm — the commutation exists in the source only as a word pattern), while its DEFORMATION clause and sentence 2 are stated on
the smooth class SmoothFront (deform_D/w/d/B, represent) — the class narrowing of the word rows is CLOSED by sentence 2 (every front is
represented by a word) kept as the field represent; FR-9: "deformations through fronts without a singular event" = SmoothFront.
NonsingularDeformation — a jointly C^∞ family of fronts of the class on [0,1] × ℝ with constant component count c (a reviewer may prefer
C^k or smoothness on a neighbourhood of [0,1]: the chosen hypothesis is stronger, so the clause is slightly weaker than the most liberal
reading); FR-10: "represented by a finite elementary front word" = equal D, w, s and a named-record isomorphism (RecordIso) of every
rounding S(F) with the realization's diagram (across the smooth/PL boundary only the invariants and the record can be stated; the record
reading is what every consumer uses); FR-13: d = degAZ (P ·) reaches the literature interface lp_lm through P; FR-1/FR-16: d of a PL
realization is read on its identity rounding (F.diagram), d of a smooth front on any rounding S with F.IsRounding S (deform_d quantifies
over roundings of both fronts).

YOUR TASK: compare the printed lemma clause by clause with the nine fields: "disjoint-gadget commutations … preserve D, w, d, and hence B"
(comm_D, comm_w, comm_d, comm_B on IsComm — expand IsComm/IsCommStep: are these exactly the disjoint-gadget commutations of the section,
i.e. two adjacent letters acting on disjoint sets of strands swapped, with the index shifts the source uses? is "and hence B" rendered as
an equality of defects?), "deformations through fronts without a singular event preserve D, w, d, and hence B" (deform_D/w/d/B on
NonsingularDeformation — expand its fields: path, endpoints, constant c, joint smoothness; does "without a singular event" mean exactly
"through fronts of the class" — every intermediate front is a front of ng:front-domain — as rendered, or something more/less?), "Every
supplied finite front can be represented by a finite elementary front word" (represent — is the reading FR-10 faithful: equal D, w, s and
a record isomorphism of every rounding with the realization's diagram; is "finite elementary front word" = OWord (closed oriented word
over the letters); "supplied finite front" = SmoothFront of the accepted class?). Every printed clause must have a field and every field a
printed clause or a disclosed extra. Judge the class readings (FR-8, FR-9, FR-10) explicitly: faithful given the disclosed design, or a
blocking class change? Say where the Lean is STRONGER or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
