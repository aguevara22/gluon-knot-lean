# RESUME_FOR_NEXT_AGENT.md — how to pick this formalization up (written 2026-09-14 20:57 UTC / 4:57pm ET by the pod executor (the executor first wrote 18:50 by mistake; corrected after the second-agent check))

## 0. State in one paragraph
Focused package "Corner state sum: wall laws and soft theorem" (frame SM15). Claims verified **109/132** (82.6%); checklist **168/192**
rows accepted (0 implemented-awaiting-review, 24 pending); final targets **4/8** (prop:C-chamber, prop:C-silent, thm:C-S3, thm:C-S5
accepted). work/lean: 665 library modules (628 SM, 28 CV, 5 RProof, 4 Bridge; a bare `find` also lists the checker's Supplemental.lean and
Supplemental/Audit.lean = 667 files), ~248k lines, zero `sorry`, only the four registered literature axioms (SM.lit_homfly, SM.lp_lm,
SM.lp_lm_uniqueness, SM.ng_finite_word) beyond propext/Classical.choice/Quot.sound. Last development receipt:
work/checks/dev-check-FINAL-20260914.json (= stage-development.json; passed, 168 mapped, 36 079 audited). The stage check
`python3 tools/check_lean.py work/lean --all` is **INCOMPLETE** (24 unaccepted rows; log work/checks/stage-all-attempt-1806.log). The 24:
22 claim rows behind GAP-2 (see §7), lem:gauss-two-discs (row 57, deferred), src:contact (unused interface). Every accepted row has an
independent review record in work/reviews/<slug>.json: the 128 rows accepted in this run (author executor-pod-…-20260913) by the AI
workflow (3 lenses + 2 adversarial refuters, proof withheld); the 40 rows accepted before this run by their 2026-09-10/11/12 reviews (39 of them
carry a `countersignature_20260913` field; lem:shift, reviewed by the 2026-09-12 cold-start session, does not). FINAL_REVIEW.md (root) is completed.
No construction is in flight. The reachable ceiling without a decision on GAP-2 has been reached.

## 1. Read in this order
1. START_HERE.md, then the package CLAUDE.md (rules that override everything), SETUP.md.
2. This file.
3. work/STATUS.md — its top header ("CURRENT STATE", written ~18:00Z) still carries the 17:55Z figures (106/132, 165/192, three rows
   then under review); the final figures are in the "FINAL checkpoint 2026-09-14 18:20Z" at the END of the file. The dated checkpoints
   are chronological.
4. work/AUTHOR_NOTES.md — the complete decision log (~5 100 lines, dated entries). Read at least the last ~65 entries of 2026-09-14
   (from "GAP-2 statement memo received", ~07:51Z, line ~4229, onward) and search for the decision ids you meet: D-F6..D-F16, D-1, D-2, D-ER1, D-G11, D-CP-1, D-FR1..D-FR5, and
   the fidelity-risk families FR-*, CE-R*, K-*, R-*, FR-LC/CM/TN/GF/ER/HR/NB/CP-*.
5. FINAL_REVIEW.md (root): the checklist template (first 51 lines) and the appended "Completed fidelity review — 2026-09-14": per-row
   status, disclosed readings, the GAP-2 paragraph, remaining gaps, process. work/FINAL_REVIEW_DRAFT.md is the same text with the
   generated tables (regenerate with `python3 work/delivery/tools/gen_final_review_tables.py --write`).
6. work/delivery/README.md — the delivery package (pins, declaration map, reviews, receipts, progress history, refresh.sh).
7. /workspace/repos/lean/reassessment_rule.md (Mark's rule: audit after two substantive attempts or 60 min without a newly accepted
   claim) and /workspace/repos/lean/CLAUDE.md (machine notes: tmux `side`, the venv, keys never printed; the "Discord only for milestones"
   convention comes from Mark's global ~/.claude/CLAUDE.md, not from that file).

## 2. Environment and the two hard operational rules
- Fresh machine: `bash setup.sh` (installs elan, the pinned toolchain v4.34.0-rc2, Mathlib cache; ends with the checker line). On the pod
  used so far: `source /workspace/envs/lean/env.sh` in EVERY shell (python venv + elan + caches on the volume); `work/lean/.lake` is a
  symlink to a local-disk cache (not in the handover tarball — rebuilt by setup.sh / `lake build`).
- ONE `lake build` or checker at a time. Before any build: `pgrep -f '^python3 tools/check_lea[n]'` (this exact pattern — a pattern that
  appears literally elsewhere in your own command line kills your own shell; two shells died that way). Start the checker as
  `nohup python3 tools/check_lean.py work/lean > work/checks/checker-run-<HHMM>.log 2>&1 &` and poll the log; it takes 4-6 minutes.
- Subagents never `lake build` and never write under work/lean; they compile drafts with
  `cd work/lean && lake env lean ../drafts/<lane>/<file>.lean` (uses the built oleans; safe while the checker runs).
- Report `python3 tools/progress.py --once` every ≤15 minutes while active (a background heartbeat loop was used; restart one).

## 3. Package rules recap (they override everything; see CLAUDE.md, AUTONOMOUS_EXECUTION.md, ACCEPT_CYCLE.md)
No `sorry` in work/lean (the checker rejects sorryAx; "not even the string in a docstring of a new port" is the executor's stricter
practice — 57 library modules, 30 of them row modules of accepted rows, still say "sorry-free"/"no sorry" in their headers, cf.
STATUS.md item 6), and no `#print`/`#eval`
directives; never delete, rename or
rewrite an ACCEPTED declaration (extend the library; docstring-only edits of UNACCEPTED library modules are allowed and were recorded);
reference/, provenance/, blueprint/ are frozen; a statement believed false gets a kernel-checked counterexample under work/repairs/ and
stays unaccepted; decide locally and record in AUTHOR_NOTES (nobody to ask); an incomplete stage is reported as incomplete; independent
review means an agent that did not write the statement and did not see the proof, disclosed in the review file. Fixed target names are
enforced by the checker (work/lean/axiom-policy.json; tools/check_lean.py hard-codes hyp:R → SM.hyp_R).

## 4. The accept cycle, exactly as practised (all scripts in work/port/)
1. Port the finished draft verbatim: one header line `-- Ported HH:MMZ 2026-MM-DD from work/drafts/<lane>/<file> (…) by <who>; body verbatim.`
   then the draft; check `grep -c -i sorry` = 0 and no `#print`/`#eval`; run the namespace-aware clash scan (an inline python used in
   AUTHOR_NOTES ~09:26Z: collect fully-qualified `theorem/def/structure…` names with namespace tracking and intersect with all of
   work/lean; two clashes were caught this way and renamed in the unaccepted draft).
2. `cd work/lean && lake build <Module>` (checker idle!).
3. `python3 work/port/map_row.py implement <row-id> <Decl> <Module>` (declaration name must match the fixed name if the row has one).
4. Checker (nohup, see §2) → when passed, copy work/checks/stage-development.json to work/checks/dev-check-<name>-implemented.json.
5. Reviewer input: `python3 work/port/strip_proofs.py work/lean/<Module>.lean work/reviews/<slug>-reviewer-input-statement.lean.txt`
   (replaces EVERY theorem proof by sorry, keeps definitions; compile-check the result with `lake env lean` on a /tmp copy).
   Source excerpt: `sed -n A,Bp reference/…/file.tex > work/reviews/<slug>-source-excerpt-lines-A-B.tex.txt` (the lemma environment).
6. Brief: work/port/review_prompt_<slug>.md — copy the nearest existing brief (e.g. review_prompt_fd-generic-front.md for a smooth-analysis
   row, review_prompt_ng-front-moves.md for a multi-row words brief, review_prompt_r-generic-transport.md for an R row, review_prompt_hyp-R.md
   for a definition row). It lists: the printed excerpt + context lines, the statement file, the definition modules allowed, the disclosed
   fidelity risks (which MUST already be in AUTHOR_NOTES before the row was stated), the clause-by-clause task, the JSON output keys.
7. Review: a Workflow with 3 lens reviewers (literal / definitions / strength) then 2 adversarial refuters (each sees the three reviews);
   schemas REVIEW_SCHEMA {verdict, reason, discrepancies, stronger_than_source, weaker_than_source, supporting_definitions_inspected,
   reviewer_files_read} and REFUTE_SCHEMA {refuted, argument, files_read}. Save the result as
   /workspace/scratch/lean_results/<slug>-round1.output in the shape {"result": {"reviews": [...], "refuters": [...]}}.
8. `python3 work/port/summarize_review.py <output> <slug>` (writes work/reviews/<slug>-review-workflow-raw.json; prints ALL CLEAR or
   ATTENTION NEEDED — non-blocking discrepancies always print ATTENTION; read them). Acceptance requires all three verdicts `faithful`
   and no refutation; a split verdict → fix the disclosure or the statement and run round 2 (done this run for cv-events — brief
   review_prompt_cv-events-round2.md —, ng:front-domain and CV:lem:carriers).
9. `python3 work/port/write_review_and_accept.py <row-id> <slug> <Decl> <Module> <source-file> '<locator text>' reviews/<excerpt>
   reviews/<statement-file> 0 literal,definitions,strength "<kernel text>" "<notes text>" allow-doc-notes` — asserts the verdicts, binds
   the hashes of every file the reviewers read, requires the row's statement hash to be in work/checks/declaration-audit.json (i.e. the
   checker ran after mapping), sets the row accepted. Avoid apostrophes inside the quoted texts (shell quoting bit once).
10. Checker again (the receipt must bind the accepted state) → copy to dev-check-<name>-accepted.json; AUTHOR_NOTES entry; STATUS
    checkpoint + tarball to /workspace/scratch/lean_results/ every ~1-2 hours; Discord only at milestones.

## 5. The lane pattern for large rows (what produced the 3k-40k-line proofs)
Design panel Workflow (2 architects with different emphases + a judge) → work/drafts/<lane>/PLAN_FINAL.md, Statements_FINAL.lean (the
frozen row statement), Skeleton_FINAL.lean (definitions + assembly PROVED, leaves `sorry`) → record the panel's fidelity risks in
AUTHOR_NOTES BEFORE the row is stated → prover Workflow: N units on byte-identical copies U_<unit>.lean (statements frozen; helpers
prefixed; false leaves reported, never changed) + an assembler (diff audit, contiguous hunks, `#print axioms`, clash scan, docstring
without the word sorry) → port → §4. Sizes achieved: 1.3k-15k lines per ported module (largest: SM/FrontRowsW2 14.7k, SM/FrontRowsW3 13.3k,
RProof/GenericTransport 11.2k; the certificate-rows lane W2+W2S+W3+W3b ≈ 39.9k in total) in 1-3 hours wall time per lane. Lessons: (a) two
lanes had a FALSE
internal leaf (an unused or repairable construction lemma) — the assembler replaced it with a true form without touching any statement;
(b) skeleton section variables: Lean includes a `variable` only if the statement mentions it — two leaves were unprovable until
`include hG in`; (c) Mathlib lemmas outside the skeleton's import closure must be re-proved or the import added (recorded per lane);
(d) no forward references — units sometimes relocate a block verbatim, the merger must reproduce the order; (e) very large lanes are
ported INCREMENTALLY as sorry-free modules (D-FR1: SM/FrontRowsW2 → W2S → W3 → W3b, each importing the previous); (f) unused false leaves
are removed at port (D-FR2); (g) `strip_proofs.py` splits at the first ` :=`/` where` at bracket depth 0, skips `let x :=`, and treats a
column-0 line as a block end unless it is a proof continuation (`by`, `fun`, `·`, …).

## 6. Where things are in work/lean (accepted unless marked)
SM/*: the SM15 foundations, the polygon/chamber/wall layer (WallGerm, NamedWallPredicates, CornerStateSum, CChamber, CSilent, CS3, CS5…),
the link-diagram layer (LinkDiagram, LinkMoves, LinkRecord*, LocalPolynomial, PolynomialBlock, LinkInterfaces = the literature axioms),
the front block (FrontSmooth, FrontPL, FrontWords*, FrontRealize*, FrontInterfaces incl. SM.ng_finite_word, FrontRowsW2/W2S/W3/W3b,
NgBound), the fd block (ParameterAvoidance, ContactMotions incl. the proved smooth dependence, TransverseNeighborhood, GenericFront,
LinkingCalculus + RegularPoleCount + LinkingCalculusRow), the ce block (CeSmoothingRecord, CeRounding, CeRoundingNonVacuity), Rounding,
Curl, HypR. CV/*: the CV lane (Events, X1, Carriers, Rounding, Curl, ChamberInv*, PieceCurve, GroupedKnot, …). RProof/*: Cores, X1Rows,
X1Rows2, GenericTransport (claims rows 166-173; the definition row CV:ax:R also lives in RProof/X1Rows). Bridge/B1 (rows Bridge:B1 AND
Bridge:B2 — there is no B2.lean), B3, B4. UNMAPPED conditional library (never map while their clause is open):
SM/ContactPathOfDescent.lean (row 91 modulo SM.AmbientIsotopyDescent), Bridge/SmR.lean (SM.sm_R_of_cv_R : CV.hyp_R → SM.hyp_R; Bridge.sm_R
:= SM.sm_R_of_cv_R RProof.cv_R once R:cv_theorem exists), RProof/X1Rows3.lean (row 173 modulo G11 — superseded by GenericTransport, kept as
its imported library), SM/LinkingCalculus.lean (the conditional bundle LinkingCalculusDataOf; the row bundle is LinkingCalculusRow).

## 7. Open work — what remains and what it would take
- **GAP-2** (22 claim rows): cp:finite-contact-path (91) needs "an ambient isotopy of links ⇒ equal HOMFLY of their diagrams". The frozen
  interface SM.lit_homfly states descent over LinkEquiv (planar isotopy + Reidemeister moves between polygonal diagrams; design D2);
  passing from a smooth spatial isotopy to a move sequence is Reidemeister's theorem, declared out of scope, no sixth axiom. Row 91 is
  PROVED modulo the single Prop SM.AmbientIsotopyDescent (SM/ContactPathOfDescent.lean; its statement independently reviewed clean:
  work/reviews/cp-finite-contact-path-conditional.json). Behind it: 94 fd:contact → 99 cf:thm-carrierfloor → 100 thm:floor → 103
  cb:singleton → 105 lem:corner-values → 112 thm:C-soft → 122, 127 thm:comparison, 128 cor:C-inherits → 184 SM:corner_laws_and_soft;
  110 thm:C-S7; 155 CV:thm:carrierfloor, 161/162 CV:ax:etnyre/slbound (D-F10), 165 CV:singleton_D_i → 175; 174/175/176/177 → 178 R:cv_theorem →
  183 Bridge:theorem. Options recorded for Mark in work/drafts/gap2/CPRow91_PLAN.md §7: (α) a policy change on the frozen interface
  (spatial descent clause; small code, re-review of every consumer), (β) prove Reidemeister's theorem for smooth isotopies (multi-thousand
  lines), or (α') the printed split AmbientIsotopyDescentLit ∧ IsotopyExtension (the second is provable analysis, ~3-5k lines). Statement
  drafts for the blocked rows: work/drafts/gap2/Gap2Statements.lean + GAP2_STATEMENTS_MEMO.md (D-F11: statement-only bundles are ported only
  after review and never mapped).
- **Row 57 lem:gauss-two-discs**: deferred — INFEASIBLE now (12-20k lines; PL Jordan–Schoenflies; work/drafts/pldiscs/PLDISCS_FEASIBILITY.md).
  Its non-GAP-2 consumer 104 was proved without it (D-ER1).
- **src:contact**: the fifth literature interface, never declared (its consumers fd:contact and CV:ax:etnyre are GAP-2-blocked).
- Cosmetic backlog (docstring citation nits inside ACCEPTED modules, listed in the review files, STATUS.md item 6 and FINAL_REVIEW §5;
  FINAL_REVIEW §7 lists tool-vs-notes inconsistencies instead, e.g. the lane size "≈26.8k" that is really ≈39.9k) — only at a layer
  rebuild, since accepted declarations are never touched.

## 8. Inventory of tools and evidence
tools/claims.py (--pending-only, --json, --next), tools/progress.py (--once), tools/check_lean.py (development / --stage / --all),
setup.sh, verify_bundle.py. work/port/: map_row.py, strip_proofs.py, summarize_review.py, write_review_and_accept.py, review_prompt_*.md
(one per reviewed row/group), make_lane_modules.py (the previous executor's prototype flow; not used since 09-13). work/reviews/: <slug>.json
(review records), *-reviewer-input-statement.lean.txt, *-source-excerpt-*.txt, *-review-workflow-raw.json. work/checks/: dev-check-*.json
(every receipt, all passed), stage-development.json (current), stage-1.json (passed=false), stage-all-attempt-1806.log, checker-run-*.log;
declaration-audit.json and lean-check.log are ~0.85 GB each and are NOT in the handover tarball (the audit is gzipped in
work/delivery/receipts/, and both are regenerated by any checker run). work/drafts/<lane>/: PLAN_FINAL.md, Statements_FINAL.lean,
Skeleton_*.lean, unit files, *_REPORT.md, assembly/merge reports — the provenance of every ported module. work/delivery/: the package
(README.md, refresh.sh, pins, declaration-map, reviews, receipts, progress, tools/gen_final_review_tables.py). Checkpoint tarballs:
/workspace/scratch/lean_results/RESULT_20260914_*.tgz (the final: RESULT_20260914_1820Z_FINAL.tgz). Memory of the executing Claude session:
/root/.claude/projects/-workspace-repos-lean/memory/*.md (copied into the handover tarball LEAN_HANDOVER_20260914_2115Z.tgz — in
/workspace/repos/lean/ and /workspace/scratch/lean_results/, built 20:58 UTC — under handover_extras/memory/, next to
handover_extras/reassessment_rule.md and repos-lean-CLAUDE.md).

## 9. If you resume
Restart the 15-minute heartbeat; run the development checker once (`python3 tools/check_lean.py work/lean`) to confirm the receipt still
matches; then either (i) wait for Mark's GAP-2 decision and, if (α)/(α'), start with IsotopyExtension (work/drafts/gap2/CPRow91_PLAN.md §7,
the SpatialFamily ambient-extension analysis of sm-3:3264-3313) as a lane, or (ii) open the row-57 lane only if its 12-20k-line cost is
explicitly accepted. Apply the reassessment rule to every branch; record audits in AUTHOR_NOTES.

Verified against the repository by a second agent, 2026-09-14 21:15 UTC / 5:15pm ET: every path and script above exists; the counts 109/132, 168/192, 4/8, 24 = 22 GAP-2 + row 57 + src:contact, ~248k lines, 168 mapped / 36 079 audited; the §4 argument lists (write_review_and_accept.py sys.argv[1:13] + optional allow-doc-notes, map_row.py implement, strip_proofs.py); the §7 chain against claims.py/DEPENDENCIES.json; and check_lean.py line 104 (hyp:R → SM.hyp_R) all check out. Corrections made in place: module-count wording (665 library + 2 Supplemental = 667 files), review provenance (128 this-run / 40 inherited + countersignature), STATUS.md header currency, AUTHOR_NOTES size and entry count, Bridge/B2 (no such file; row in Bridge/B1.lean), RProof row numbers 166-173, 175 → 178, cosmetic-backlog pointer (STATUS item 6 / FINAL_REVIEW §5), zip → tarball, lane sizes, round-2 count, Discord-rule attribution, docstring-sorry practice vs checker rule. Not verified: wall-clock claims (checker 4-6 min, lanes 1-3 h, "two shells died"). Note: this file's mtime before this note was 20:57 UTC / 4:57pm ET although the header says 18:50 UTC.
