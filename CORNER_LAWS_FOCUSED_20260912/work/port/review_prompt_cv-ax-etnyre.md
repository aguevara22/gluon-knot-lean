You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the statement
you are reviewing and you must not read its proof. Your job is a statement-fidelity review of ONE row against ONE
printed source statement: CV:ax:etnyre (row 161), Lean declaration `CV.ax_etnyre : CV.AxEtnyreData` (module
CV/AxEtnyre.lean). In the CV document the row is an "axiom" environment; in this package every CV ax:* row is a THEOREM
derived from the SM side (pattern of the accepted CV.ax_homfly; here from the literature interface SM.src_contact).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cv-ax-etnyre-source-excerpt-lines-387-397.tex.txt (= reference/R/CV/
   d10_axioms.tex 387-397: "Let T be a front diagram of a transverse knot with no downward vertical tangency. Then sl(T)
   equals the writhe of T." + the "Why it is not proved here" paragraph + "Used in: thm:carrierfloor(C)"). Context ONLY
   to fix notation: d10_axioms.tex 399-425 (ax:slbound), reference/R/CV/d3_floor.tex 930-990 (the consumer's transverse
   lift), reference/SM/sm-3-statesum.tex 341-343 (def:transverse-front), 2820-2824 and 3012-3022 (the SM self-linking
   number and rem:sl-convention), 3341-3365 (src:contact), 3404-3411 (fd:contact's display fd:front-writhe).
2. The Lean statement: work/reviews/cv-ax-etnyre-reviewer-input-statement.lean.txt (the row module, proof withheld) and
   the structure `CV.AxEtnyreData` with its docstring in work/lean/SM/FdContactStatements.lean (read the CV block only;
   the theorems ax_etnyre_of / ax_slbound_of there are library derivations, not the row's proof). The self-linking number
   `SM.sl` and `SM.slCircle`: work/reviews/src-contact-reviewer-input-statement.lean.txt (definitions).
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/TransverseFront.lean
   (TransverseKnot, front, SmoothKnotDiagram.vel/isOver/crossSign/writhe, front_vertical_up), SM/LinkingCalculus.lean
   (selfLinking — grep), and Mathlib.
4. Disclosed readings: work/AUTHOR_NOTES.md entry "Contact lane …" of 2026-09-15 (D-SC-4, FR-FC-4: the hypothesis "no
   downward vertical tangency" kept explicitly though redundant on the class; CV's sl read as SM's sl; D-F10 (iii)
   superseded) and the earlier entry containing D-F10 (grep "D-F10").

KERNEL FACTS (reported by the executor; re-check with `cd work/lean && lake env lean` on a scratch file importing
CV.AxEtnyre if you wish): `CV.ax_etnyre : CV.AxEtnyreData` with no hypothesis; axioms [propext, Classical.choice,
Quot.sound, SM.src_contact].

YOUR TASK: compare the printed statement with the field `self_linking_eq_writhe : ∀ D K, K.front = D → (∀ t, (D.vel t).1
= 0 → 0 < (D.vel t).2) → SM.sl K = ↑D.writhe`: "a front diagram of a transverse knot" (D with K.front = D, K a
TransverseKnot of def:transverse-front — is the class right: the CV text's transverse knots with a front diagram vs
SM's knots with a generic front?), "with no downward vertical tangency" (the explicit hypothesis: vertical velocity
points up — is this the printed condition?), "sl(T)" (SM.sl K, the document's framed self-linking number; the CV text
never defines sl — is reading it as SM's number faithful, given the CV text says it "presupposes the contact-geometric
definition of sl"?), "equals the writhe of T" (↑D.writhe with the accepted over = smaller y / sign det_xz conventions —
the CV writhe convention: check d10/d3 for CV's own sign convention if stated). Is the Lean STRONGER or WEAKER than
printed? Is the "Why it is not proved here" paragraph correctly treated as commentary? Default to "not faithful" if in
doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason" (clause-by-clause, cite
source and statement-file line numbers), "discrepancies", "stronger_than_source", "weaker_than_source" (arrays of
strings), "supporting_definitions_inspected" (Lean names), "reviewer_files_read" (relative paths).
