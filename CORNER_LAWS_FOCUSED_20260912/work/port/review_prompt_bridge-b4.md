You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE bridge obligation row against its frozen source text: Bridge:B4 (checklist row 182),
Lean declaration `Bridge.B4 : Bridge.B4Data` (module Bridge/B4.lean).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The frozen source, verbatim: work/reviews/bridge-b4-source-excerpt-lines-637-700.md.txt (= reference/BRIDGE/BRIDGE.md 637-700: "B4.
   Pointwise dictionary and side values", Lemma B4 and the beginning of its proof) and work/reviews/bridge-b4-source-displays-lines-1355-1445.md.txt
   (= BRIDGE.md 1355-1445: display (17) — the pointwise identity of the two state sums on SM-generic labelled representatives — and
   display (18) — the side values on the two punctured sides of a triple germ — with the sentence at 1441 "These are equalities of values
   on corresponding sides. They do not assert equality of a quotient SM chamber with a labelled CV chamber …"). Context, ONLY to fix
   notation: reference/BRIDGE/BRIDGE.md 90-130 (the two generic loci and what B1 transfers), 493-636 (Lemma B3, accepted as Bridge.B3),
   1446-1480 (how (18) is consumed to prove hyp:R), and the accepted Bridge rows' Lean modules work/lean/Bridge/B1.lean, Bridge/B3.lean
   (statements and docstrings: Bridge.eventOfTriple, WallGerm, TripleAt, sideTuple, sideBase, sideChamber, Bridge.sm_R's shape).
2. The Lean statement with the row proofs replaced by `sorry`: work/reviews/bridge-b4-reviewer-input-statement.lean.txt (module
   Bridge/B4.lean: the bundle Bridge.B4Data with fields pointwise, sides and the theorems Bridge.B4_of_cb (the row under the explicit
   hypothesis that cb:products holds — a proof device) and Bridge.B4 are UNDER REVIEW). Its module docstring maps the notation and lists
   the unit's readings — verify, do not trust. Do NOT open work/lean/Bridge/B4.lean or work/lean/SM/GeoCarrierAgreement.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/CornerStateSum.lean (SM.cornerStateSum,
   cornerCoefficient, cornerHomfly — def:C, accepted), SM/CChamber.lean (SM.prop_C_chamber — statement), SM/WallGerms.lean or wherever
   WallGerm / TripleAt / sideTuple / sideBase are defined (grep under work/lean/SM and work/lean/Bridge), CV/X1.lean (CV.X1 and its accepted
   bundle), CV/Setup.lean (CV.Generic, CV.chamber, CV.generic_of_sm if there), CV/ChamberInvRow.lean (CV.chamberinv_ii — statement),
   CV/CarrierBridges.lean (generic_crossingGeometry, CV.generic_of_sm — the SM-generic ⇒ CV-generic bridge, statements), CV/Events.lean
   (CV.Event, sideChamber), CV/TripleEvents.lean, SM/CBBlocks.lean (CbProductsData — the cb:products bundle that B4_of_cb assumes; row 102
   is implemented and under review), Bridge/B1.lean, Bridge/B3.lean. You MAY read work/AUTHOR_NOTES.md entries "CV-DOM decided" (rulings
   R6/R7 on the shape of Bridge.B4) and "cb lane …", and work/drafts/cvdom/DECISION_FINAL.md §7 (ruling R7: `structure Bridge.B4Data : Prop`
   with `pointwise` = (17) on SM-generic labelled representatives and `sides` = (18) on the sides of Bridge.eventOfTriple).

DISCLOSED READINGS of the unit (judge each): (a) `pointwise : ∀ n [NeZero n] (hn : 3 ≤ n) (P) (hP : SM.Generic P), CV.X1 hn P (CV.generic_of_sm hn hP)
= SM.cornerStateSum hn hP` — display (17) with CV's X₁ read at the SM-generic representative through the accepted SM-generic ⇒ CV-generic
bridge; (b) `sides`: for every wall germ g with a triple at (e,f,k), side b, side parameter t, and every CV-generic Q in the side chamber
(eventOfTriple hn g h).sideChamber b, the SM side value cornerStateSum of g.sideTuple b t equals CV.X1 hn Q hQ — display (18) as
"equalities of values on corresponding sides", quantifying Q with its own genericity proof and the SM value at an arbitrary side
parameter t (no quotient chamber object, as BRIDGE.md 1441 insists); (c) the proof route (not statement matter): pointwise via the
agreement of the geo layer with the SM Carrier lane and cb:products' product formula (P_A = ∏ P_H identifies cornerHomfly with the
grouped polynomial), sides via SM.prop_C_chamber + pointwise + CV.chamberinv_ii; (d) B4_of_cb isolates cb:products as one hypothesis;
Bridge.B4 discharges it with SM.cb_products.

YOUR TASK: decide whether B4Data renders exactly Lemma B4 / displays (17) and (18): the class of representatives ("every SM-generic labelled
representative"), the two state sums (SM's C and CV's X₁ — is CV.X1 at CV.generic_of_sm the printed X₁ of the same labelled polygon?),
the side statement (which polygons, which chambers, which parameters; is "on either punctured side of a triple germ, this equality
identifies the SM side value with the value of X₁ on the corresponding CV side" rendered exactly — neither a quotient-chamber equality
nor weaker than (18)?), hypotheses added or dropped (hn, NeZero, the triple data). Expand definitions to primitives; say where the Lean is
STRONGER or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
