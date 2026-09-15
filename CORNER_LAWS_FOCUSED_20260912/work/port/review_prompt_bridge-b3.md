You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row of the Bridge lane, Bridge:B3 (Lemma B3), against its printed
source, the frozen bridge specification reference/BRIDGE/BRIDGE.md (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/bridge-b3-source-excerpt-lines-493-636.md.txt (= BRIDGE.md
   493-636: Lemma B3 — "The three parameter-difference sign changes in SM type T, together with its central
   conditions, imply CV transversality for the zero set (3)" — with the quoted CV parameter factorization
   and dictionary identities and its proof; the STATEMENT is line 495). Context: work/reviews/bridge-s0-
   context-lines-5-101.md.txt (BRIDGE.md §0), work/reviews/bridge-b1-source-excerpt-lines-159-446.md.txt and
   bridge-b2-source-excerpt-lines-448-491.md.txt (Lemmas B1, B2 — the germ, the event and its zero set (3),
   rows under separate review), reference/R/CV/d1_setup.tex 42-218 (CV def:guarded, incl. the parameter
   factorization 198-207), 1072-1097 (def:event: SignChanges, Transversal), reference/R/CV/d8a_dictionary.tex
   429-435 (G3 = −G4 identity) and the SM wall-germ definitions the excerpt cites (follow its `sm-…tex:line`
   citations only: def:germ, def:walls, type T, parameter-difference sign changes).
2. The Lean statement with the row proofs replaced by `sorry`:
   work/reviews/bridge-b3-reviewer-input-statement.lean.txt (module Bridge/B3.lean: helper lemmas with proofs
   (not under review), `theorem Bridge.B3` and `Bridge.B3_unsorted`). The header maps notation — verify it. Do
   NOT open work/lean/Bridge/B3.lean. You MAY read work/lean/Bridge/B1.lean's DEFINITIONS `Bridge.eventOfTriple`
   and the statements of `Bridge.B2`, `exists_sorted_tripleAt` (rows 179-180; do not review their proofs).
3. Lean definition modules (definitions and docstrings): work/lean/CV/Events.lean (CV.Event, Parameter,
   SideParameter, sideCurve, zeroSet, SignChanges, Transversal — accepted row 148), work/lean/CV/Setup.lean
   (Member, G3, G4, Crosses, crossParam — accepted rows 129-133), and under work/lean/SM/: the wall-germ
   modules (`WallGerm`, `TripleAt`, `SignChanges`, `edgeParameter` — grep NamedWallPredicates.lean,
   GermSignChange.lean, UnorderedWallTriples.lean, TripleOrder.lean; definitions only).

YOUR TASK: compare the printed Lemma B3 with `Bridge.B3 (hn : 3 ≤ n) (g : WallGerm n) (h : g.TripleAt e f k)
(hef : rep e < rep f) (hfk : rep f < rep k) : (eventOfTriple hn g h).Transversal` (and the unsorted
version). Check: "the three parameter-difference sign changes in SM type T, together with its central
conditions" = `TripleAt` (read its definition: pointZeros = ∅, concurrences = {{e,f,k}}, the three sign
changes — on which edges are the parameter differences measured?); "CV transversality for the zero set (3)"
= `Event.Transversal` (every member of `zeroSet` satisfies `SignChanges` of its evaluation — read def:event's
printed "transversal" and the Lean rendering); is `Event.SignChanges` for `eventOfTriple` the same notion as
SM's germ sign change (the header claims `Iff.rfl`)? Does the Lean assert anything beyond the printed lemma
(e.g. about members outside the zero set) or less? Expand definitions to primitives; say where the Lean is
STRONGER or WEAKER. Default to "not faithful" if in doubt; label non-blocking discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
