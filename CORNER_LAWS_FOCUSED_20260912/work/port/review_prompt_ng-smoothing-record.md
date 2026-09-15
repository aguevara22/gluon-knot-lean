You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE lemma row against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/ng-smoothing-record-source-excerpt-lines-1843-1849.tex.txt (= reference/SM/
   sm-3-statesum.tex 1843-1849, ng:smoothing-record "independence of the rounding"). Context, ONLY to fix notation:
   sm-3-statesum.tex 1850-1875 (its printed proof and the paragraph on the polynomial's inputs), 1825-1841
   (ng:front-domain: the front class and the rounding S(F) — its Lean rendering is the row ng:front-domain, module
   SM/FrontSmooth.lean, under round-2 review; you may read work/reviews/ng-front-domain-reviewer-input-statement.lean.txt
   for its definitions: SmoothFront, Marking, GeomRounding, Rounding, IsRounding — definitions and docstrings only),
   352-370 (def:gauss-record: the named record and named record isomorphisms), 1215-1229 (rp:record-polynomial,
   accepted). You MAY read the executor's fidelity risks FR-1..FR-4 and the row-73 repair entries in work/AUTHOR_NOTES.md
   (2026-09-14: "Front block: representation adopted", "ng:front-domain repaired and re-ported").
2. The Lean statement with the row proof replaced by `sorry`: work/reviews/ng-smoothing-record-reviewer-input-statement.lean.txt
   (module SM/FrontRecordBridge.lean: module docstring — verify, do not trust; definitions IsDoubleOf / occSetOf /
   slopeOf / crossSignOf of a loop family and the helper lemmas are library material (proofs not under review);
   `Rounding.iso` (the RecordIso between two roundings' diagrams) is used by the bundle's fields; the bundle
   `SmoothingRecordData` (7 fields) and theorem `SM.ng_smoothing_record` at the end). Do NOT open
   work/lean/SM/FrontRecordBridge.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/FrontSmooth.lean is OFF
   LIMITS except through the reviewer-input copy named in 1; work/lean/SM/LinkRecord.lean (Record, RecordIso with e, Φ
   and the preserved data), LinkDiagramRecord.lean (Diagram.record, nextVisit, twin, VisitBetween, RecordIso.visitBetween_iff
   statement), LinkDiagram.lean (Diagram, componentCount, compOf, overBit, sign), LocalPolynomial.lean (P),
   PolynomialBlock.lean END (the accepted rp:record-polynomial / lc:presentations bundles — statements only).

YOUR TASK: decide whether the bundle pins down exactly the printed lemma. Clauses: "Let F be a front on the domain of
ng:front-domain. Any two ordinary diagrams S(F) obtained by the cusp replacement of that definition" (∀ F : SmoothFront,
S S' : Diagram with F.IsRounding S, F.IsRounding S'); "have the same full named record" (full_named_record: Nonempty
(RecordIso S.record S'.record)); "the same component circles, including crossing-free ones" (component_circles: both have
F.c components and the iso's circle bijection e is respected by Φ — is "including crossing-free ones" rendered by the
component count / e on all circles?); "and the same crossing occurrences, cyclic orders, over/under bits and signs"
(crossing_occurrences: |visits| = |F.Occ| on both and Φ commutes with twin — is that "same crossing occurrences"?;
cyclic_orders: Φ commutes with nextVisit and preserves VisitBetween; over_under_bits; signs); "Consequently P_{S(F)} does
not depend on the choice of rounding" (polynomial: P S = P S'). Are the fields stated for the specific iso `ρ.iso ρ'`
of two given roundings faithful to "the same … record" (an existence statement)? Is anything printed missing or anything
in Lean stronger (e.g. the count conjuncts)? Expand definitions to primitives; default to "not faithful" if in doubt;
label non-blocking discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
