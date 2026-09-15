You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statements you are reviewing and you must not read their proofs. Your job is a
statement-fidelity review of ONE row of the CV lane against ONE printed source statement of the paper "CV"
(reference/R/CV/, frozen). The row is named in your task.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: CV:lem:carrierword → work/reviews/cv-lem-carrierword-source-excerpt-lines-450-470.tex.txt
   (= reference/R/CV/d1_setup.tex 450-470: the statement 450-459 and the beginning of the proof); CV:selector_A →
   work/reviews/cv-selector-A-source-excerpt-lines-1000-1030.tex.txt (= reference/R/CV/d6_vertexedge.tex 1000-1030;
   the row is clause (A) of lem:selectorid at 1017-1020: "Under the guards of Definition def:generic(A), every carrier of
   every support has at least three corners" — clause (B) is a DIFFERENT row, not under review). Context, ONLY to fix
   notation: d1_setup.tex 355-361 (def:smoothing), 362-383 (lem:carriers), 471-486 (the rest of carrierword's proof),
   487-513 (def:wind: corners), 220-238 (def:generic), 592-620 (lem:piececurve Step 5 — the consumer of carrierword's
   refinement reading), reference/SM/sm-1-polygons.tex 240-268 (SM def:gauss: Gauss words). You MAY read the executor's
   CV-DOM decision in work/AUTHOR_NOTES.md (entry "CV-DOM decided: F2 mechanism = (C) on the accepted geo layer",
   2026-09-14) — in particular its documented reading (i): lem:carrierword's printed generality over "a closed curve C with
   finitely many transverse double points" is realised on the carriers of a diagrammatic polygon P and on daughter carriers
   via the refinement clause (S ⊆ S′ both independent ⇒ every carrier of S′ lies in one carrier of S with the induced
   order), the only instances the CV text consumes — judge whether that reading is faithful.
2. The Lean statements with the row proofs replaced by `sorry`: CV:lem:carrierword →
   work/reviews/cv-lem-carrierword-reviewer-input-statement.lean.txt (module CV/CarrierWord.lean: bundle CarrierWordData,
   theorem CV.carrierword; definitions carrierGaussList etc. under review; helper lemmas' proofs not under review);
   CV:selector_A → work/reviews/cv-selector-A-reviewer-input-statement.lean.txt (module CV/SelectorA.lean: bundle
   SelectorAData with the single field three_corners, theorem CV.selector_A). Do NOT open work/lean/CV/CarrierWord.lean or
   work/lean/CV/SelectorA.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/CV/Carriers.lean (accepted
   CV:def:smoothing / def:wind / def:pieces), CV/CarriersLemma.lean (CV:lem:carriers — statement only), CV/Setup.lean
   (Diagrammatic, Generic), CV/Events.lean (Ind), SM/FlatCarriersDefs.lean (GeoComponent, geoOwner, geoComponentMarkList,
   geoComponentCornerList, geoCornerCount, geoMarkSuccessor, geoSmoothingSuccessor, TracedSuccessor — definitions),
   SM/GeoCarrierCount.lean (GeoInheritsMarkOrder — definition), SM/GeometricVisits.lean (geometricGaussList), SM/GaussVisits.lean.

YOUR TASK: for YOUR row only, decide whether the bundle renders exactly the printed statement on its printed binder.
carrierword: read the printed statement 450-459 sentence by sentence (the closed curve C, its double points, the
smoothing, "the Gauss word of each carrier is the restriction of C's word in the inherited cyclic order", the refinement
clause or whatever the text says) and compare with the fields smoothing_preserves_order, carrier_word, refinement — is
reading (i) (carriers of P; daughter carriers) faithful or a narrowing; is the binder hD : Diagrammatic P printed?
selector_A: is three_corners exactly "under the guards of def:generic(A), every carrier of every support has at least
three corners" (binder hG : Generic P; ∀ S ∈ Ind, ∀ carrier, 3 ≤ geoCornerCount; the local ∀ hn : 3 ≤ n)? Expand
definitions to primitives; say where the Lean is STRONGER or WEAKER; default to "not faithful" if in doubt; label
non-blocking discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).

ROUND 2 (CV:lem:carrierword only; the statement is UNCHANGED). Round 1 returned 2 faithful / 1 not faithful and two
refuters not refuted. The dissent's sole item: the wording "no domain change" in the executor's CV-DOM note is inaccurate
for this row — the Lean binder `hD : Diagrammatic P` (with the smoothed curves reached as iterated carriers through the
field `refinement`) is a NARROWING of the printed binder "a closed curve C with a traversal circle Γ_C and finitely many
transverse double points" (d1:450-453; the generality serves the induction on smoothed curves, d1:481-484). The executor
has recorded that ruling (work/AUTHOR_NOTES.md, entry "Four accepts, one split verdict, one library decision",
2026-09-14 ~04:22Z, which you MAY read): reading (i) is a narrowing of the printed binder to diagrammatic polygons and
their iterated carriers; the frozen source defines smoothing only for polygons (def:smoothing d1:355-360) and never
defines a general class of closed curves; every consumer instance (lem:carriers, lem:piececurve Steps 1/5) is
polygon-derived; the library has no type of general closed curves. YOUR ROUND-2 TASK: with the narrowing disclosed as
such, decide whether the bundle is a faithful rendering of the printed lemma on the class of curves the frozen source
itself defines and uses (polygons and their iterated smoothings), or whether the narrowing is a blocking defect (e.g. a
printed consumer or the printed proof needs an instance the Lean class does not contain). Default to "not faithful" if
in doubt; do not defer to the executor's ruling.
