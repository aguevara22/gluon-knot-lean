# RESUME_FOR_NEXT_AGENT.md — how to pick this formalization up

**Rewritten 2026-09-16 01:55 UTC / 9:55pm ET (2026-09-15) by the synthesizer agent (Claude Code, tmux `side`, Mark's RunPod home pod).
This text SUPERSEDES the 2026-09-14 20:57 UTC version (kept in the 2026-09-14 handover archive and, as a backup of this rewrite, in the
synthesizer's scratchpad). The operational sections §2-§5 and most of §8 are the 2026-09-14 text, re-verified where marked; §0, §1, §6, §7,
§9 are new. The complete register of open items — every leaf, disclosure, debt and decision with file:line pointers — is
`OPEN_ITEMS_20260916.md` at the package root; this file tells you how to work, that one tells you what is open.**

*Repair pass 02:24Z UTC 2026-09-16 / 10:24pm ET (2026-09-15): locator and count corrections from two adversarial critics applied here (§1 items 2-3, §2, §3, §6, §7, §8)
and in OPEN_ITEMS (its end note "Critic items rejected" lists what was corrected).*

## 0. State in one paragraph (2026-09-16 00:59Z, the executor's "Session closed" entry, re-verified against the receipts)
Focused package "Corner state sum: wall laws and soft theorem" (frame SM15). Claims verified **124/132** (93.9%); checklist **184/192** rows
accepted (0 implemented-awaiting-review, 8 pending); final targets **5/8** (prop:C-chamber, prop:C-silent, thm:C-S3, thm:C-S5, thm:C-soft
accepted; thm:C-S7, Bridge:theorem, SM:corner_laws_and_soft open). work/lean: 697 `.lean` files (648 SM, 32 CV, 11 RProof, 4 Bridge, 2
Supplemental), 295 911 lines, zero `sorry`, six literature axiom constants for the FIVE registry interfaces — SM.lit_homfly,
SM.lit_homfly_descent (the author-authorised SECOND declaration of lit:homfly, D-GAP2, 2026-09-15), SM.lp_lm, SM.lp_lm_uniqueness,
SM.ng_finite_word, SM.src_contact (declared 2026-09-15) — beyond propext/Classical.choice/Quot.sound ("the nine registered axioms"). Last
development receipt: work/checks/dev-check-FINAL-20260916.json (passed, 184 mapped, 41 658 audited, no unregistered axiom, no sorryAx; 100
receipts in work/checks, all passed). The stage check `python3 tools/check_lean.py work/lean --all` and `--stage 1` are **INCOMPLETE by
design** — "unaccepted rows: Bridge:theorem, R:cv_theorem, R:extreme_selected, SM:corner_laws_and_soft, cor:C-inherits, lem:gauss-two-discs,
thm:C-S7, thm:comparison" (log work/checks/stage-all-check-20260916-0032.log). The 8: row 57 deferred by the author; the corner branch 110 →
127/128 → 184 stopped by audit A-110-1 (110 kernel-proved modulo five named Props, ≈ 8-12k lines); the R branch 177 → 178 → 183 stopped by
audit A-177-2 (177 proved modulo two named leaves, ≈ 1.0-2.5k lines, one route open; 178/183 one-liners STAGED). GAP-2 is closed by the
author's decision, not by a proof. Sixteen rows were accepted on 2026-09-15/16 (91, src:contact, 161, 94, 162, 99, 100, 155, 165, 175, 103,
105, 112, 122, 174, 176), all by the AI review workflow (3 lenses + 2 refuters, proof withheld). FINAL_REVIEW.md (root, 1276 lines) was
regenerated 00:56Z; verify_bundle.py PASS; work/delivery refreshed 00:59Z. **No construction is in flight. Both stopped branches wait for the
author (OPEN_ITEMS §G-01, §G-02). No checkpoint tarball of the 2026-09-15/16 state exists — build one first (§9).**

## 1. Read in this order
1. START_HERE.md, then the package CLAUDE.md (rules that override everything), SETUP.md.
2. This file, then **OPEN_ITEMS_20260916.md** (root): §A the eight rows and their named leaves with resume commands, §B the two new axioms and
   the verifier relaxation, §C library-interface findings (false-as-stated fields closed by weak replays), §D every reviewer note on the 16
   new rows, §E documentation debts, §F tooling caveats (audited-count scope, pgrep trick, heredocs, heartbeat, archives; §F-20 = the index of the
   2026-09-15/16 decision ids D-GAP2-n / D-FL-n / D-SC-n / D-CC-n / D-CVT-n / D-CM-n / D-RM-n that the lane entries carry inline), §G the
   author's decisions.
3. work/STATUS.md — the TOP block (00:57Z 2026-09-16) is current; it stacks five "# STATUS" headers (2026-09-15 18:40Z … 14:00Z) above the
   2026-09-14 text, and only its fifth bullet (L11) keeps a pre-conclusion phrase ("no branch currently past its bound") — the FINAL bullet
   wins. (The sentence "177 (Wave 3c assembler, bound 02:15Z), 178 -> 183 after 177" that FINAL_REVIEW §7 L1190-1194 attributes to STATUS
   is NOT in STATUS — it is AN L6417; FR §7 was written against the 00:33Z header, before the 00:57Z rewrite; OPEN_ITEMS §E-09.)
4. work/AUTHOR_NOTES.md — the decision log (6479 lines). The 2026-09-15/16 entries are L5144-6479 (headings: `grep -n '^## '
   work/AUTHOR_NOTES.md | awk -F: '$1>=5144'`). Read at least: D-GAP2 (L5144-5203), the lane design entries (floor L5218, contact L5295,
   corner L5396, CV/R tail L5474, comparison L5691 — each records decisions D-* and fidelity readings FR-* BEFORE the statements were
   stated), the audits A-110-1 (L6079, concluded L6300), A-177-1 (L6171, success L6216), A-177-2 (L6330, concluded L6419), D-RM-1..7
   (L5664, L5868, L5930, L5999, L6070, L6255, L6377), and the closing entries L6442-6479.
5. FINAL_REVIEW.md (root): §1-§3 status tables (§3 = the eight pending rows with reasons and §3.1/§3.4 the two stopped branches), §4.3 the
   axioms and which rows carry them, §5 the honest gap list (14 items), §6 process and audits, §7 verified inconsistencies. The 2026-09-14
   text of record is work/FINAL_REVIEW_DRAFT.md; the 2026-09-15 addendum draft is work/delivery/FINAL_REVIEW_ADDENDUM_DRAFT_20260915.md.
6. work/delivery/README.md — the delivery package (its prose still describes the 2026-09-14 state; the copies/receipts are 00:59Z 2026-09-16).
7. /workspace/repos/lean/reassessment_rule.md (Mark's rule: audit after two substantive attempts or 60 min without a newly accepted claim;
   memory note /root/.claude/projects/-workspace-repos-lean/memory/lean-reassessment-rule.md) and /workspace/repos/lean/CLAUDE.md (machine
   notes: tmux `side`, the venv, keys never printed; "Discord only for milestones" comes from Mark's global ~/.claude/CLAUDE.md).
8. For the stopped branches: work/drafts/corner/port/CS7_STATE.md + W3_ASSEMBLY_REPORT.md (§3, §6, §7) for row 110;
   work/drafts/moves/W3C_ASSEMBLY_REPORT.md (§3, §6, §7, §8) for row 177; work/drafts/cvtail/port/R178_183/ for the staged 178/183;
   work/drafts/comparison/port/PORT_REPORT.md L130-143 for the 127/128 one-liners.

## 2. Environment and the two hard operational rules (2026-09-14 text, re-verified 2026-09-16)
- Fresh machine: `bash setup.sh` (installs elan, the pinned toolchain v4.34.0-rc2, Mathlib cache; ends with the checker line). On the pod
  used so far: `source /workspace/envs/lean/env.sh` in EVERY shell (python venv + elan + caches on the volume; the file sets ELAN_HOME, PATH
  and LEAN_PROJ, no keys); `work/lean/.lake` is a symlink to `/root/lean-lake` (local disk, not in any archive — rebuilt by setup.sh / `lake build`).
- ONE `lake build` or checker at a time (AUTHOR_NOTES L3893-3894). Before any build: `pgrep -f '^python3 tools/check_lea[n]'` (this exact
  pattern — a pattern that appears literally elsewhere in your own command line matches and kills your own shell; AUTHOR_NOTES L3929-3931).
  Start the checker as `nohup python3 tools/check_lean.py work/lean > work/checks/checker-run-<HHMM>.log 2>&1 &` and poll the log; it takes
  4-6 minutes idle.
- Subagents never `lake build` and never write under work/lean; they compile drafts with
  `cd work/lean && lake env lean ../drafts/<lane>/<file>.lean` (uses the built oleans; safe while the checker runs). `#print axioms` only in
  a scratch copy compiled with `lake env lean <abs path>` from work/lean — never inside work/lean (the checker rejects `#print`/`#eval`).
- Under ≈ 25 concurrent agents a 3000-line draft compiles in many minutes, not seconds (latency, not correctness; AUTHOR_NOTES L5610-5611).
- Report `python3 tools/progress.py --once` every ≤15 minutes while active (CLAUDE.md rule 6; EXECUTION.json progress_interval_seconds 900).
  `python3 tools/progress.py --watch` (pid 77461, log work/progress-watch.log) was still running at 01:32Z and at 02:17Z 2026-09-16 (pgrep at the repair pass; re-verify); the executor's
  14-minute in-session timer died with its session (no system crontab on the pod). Restart your own reminder; keep or kill the watcher
  deliberately (`pgrep -f 'progress.py --watc[h]'`).
- When appending to work/AUTHOR_NOTES.md or writing Lean text from bash, use a QUOTED heredoc (`cat >> file <<'EOF'`): Lean names carry
  backticks, and an unquoted heredoc executes them as command substitution.

## 3. Package rules recap (they override everything; see CLAUDE.md, AUTONOMOUS_EXECUTION.md, ACCEPT_CYCLE.md) — 2026-09-14 text
No `sorry` in work/lean (the checker rejects sorryAx; "not even the string in a docstring of a new port" is the executor's stricter
practice — 55 library modules at register time (`grep -rliE 'sorry-free|no sorry' work/lean --include=*.lean | wc -l`; STATUS.md
2026-09-14 item 6 counted 57, 30 of them row modules of accepted rows) still say "sorry-free"/"no sorry" in their headers, cf. OPEN_ITEMS §E-11), and no `#print`/`#eval` directives; never delete, rename or rewrite an ACCEPTED declaration
(extend the library; docstring-only edits of UNACCEPTED library modules are allowed and were recorded; the 2026-09-15 22:40Z header fix in an
accepted module was comment-only and is the one precedent — OPEN_ITEMS §G-05); reference/, provenance/, blueprint/ are frozen; a statement
believed false gets a kernel-checked counterexample under work/repairs/ and stays unaccepted (the 2026-09-15/16 false-as-stated findings were
all DRAFT sub-leaves or LIBRARY interface fields, never row statements — they were restated in drafts or bypassed by weak replays, OPEN_ITEMS
§C); decide locally and record in AUTHOR_NOTES (nobody to ask, except that the AUTHOR now exists as a decision-giver through Mark: D-GAP2
was received that way); an incomplete stage is reported as incomplete; independent review means an agent that did not write the statement
and did not see the proof, disclosed in the review file. Fixed target names are enforced by the checker (work/lean/axiom-policy.json;
tools/check_lean.py:104 hard-codes hyp:R → SM.hyp_R). D-F11: a row theorem with an undischarged premise is never mapped — its `_of` form is
ported as library and the row waits (this is why the eight pending rows have `module ""` in work/lean/lean-declarations.json).

## 4. The accept cycle, exactly as practised (all scripts in work/port/) — 2026-09-14 text, unchanged in 2026-09-15/16
1. Port the finished draft verbatim: one header line `-- Ported HH:MMZ 2026-MM-DD from work/drafts/<lane>/<file> (…) by <who>; body verbatim.`
   then the draft; check `grep -c -i sorry` = 0 and no `#print`/`#eval`; run the namespace-aware clash scan (an inline python used in
   AUTHOR_NOTES ~09:26Z 2026-09-14: collect fully-qualified `theorem/def/structure…` names with namespace tracking and intersect with all of
   work/lean; the lane-specific tools work/drafts/corner/port/tools/port_clash_scan.py and work/drafts/moves/clash_scan_W3.py do the same).
2. `cd work/lean && lake build <Module>` (checker idle!).
3. `python3 work/port/map_row.py implement <row-id> <Decl> <Module>` (declaration name must match the fixed name if the row has one).
4. Checker (nohup, see §2) → when passed, copy work/checks/stage-development.json to work/checks/dev-check-<name>-implemented.json.
5. Reviewer input: `python3 work/port/strip_proofs.py work/lean/<Module>.lean work/reviews/<slug>-reviewer-input-statement.lean.txt`
   (replaces EVERY theorem proof by sorry, keeps definitions; compile-check the result with `lake env lean` on a scratch copy).
   Source excerpt: `sed -n A,Bp reference/…/file.tex > work/reviews/<slug>-source-excerpt-lines-A-B.tex.txt` (the lemma environment).
   Record the file's OWN sha256 as `source_sha256` (two 2026-09-15 records carry the whole tex file's hash instead, OPEN_ITEMS §E-04).
6. Brief: work/port/review_prompt_<slug>.md — copy the nearest existing brief (review_prompt_r-extreme-transport.md for an R row,
   review_prompt_prop-anchor-values.md for a comparison/corner row, review_prompt_lit-homfly-descent.md for an interface,
   review_prompt_fd-generic-front.md for a smooth-analysis row, review_prompt_hyp-R.md for a definition row) and FIX its locators
   (OPEN_ITEMS §E-15 lists the errors found). It lists: the printed excerpt + context lines, the statement file, the definition modules
   allowed, the disclosed fidelity risks (which MUST already be in AUTHOR_NOTES before the row was stated), the clause-by-clause task, the
   JSON output keys.
7. Review: a Workflow with 3 lens reviewers (literal / definitions / strength) then 2 adversarial refuters (each sees the three reviews);
   schemas REVIEW_SCHEMA {verdict, reason, discrepancies, stronger_than_source, weaker_than_source, supporting_definitions_inspected,
   reviewer_files_read} and REFUTE_SCHEMA {refuted, argument, files_read}. Save the result as
   /workspace/scratch/lean_results/<slug>-round1.output in the shape {"result": {"reviews": [...], "refuters": [...]}}.
8. `python3 work/port/summarize_review.py <output> <slug>` (writes work/reviews/<slug>-review-workflow-raw.json; prints ALL CLEAR or
   ATTENTION NEEDED — non-blocking discrepancies always print ATTENTION; read them). Acceptance requires all three verdicts `faithful`
   and no refutation; a split verdict → fix the disclosure or the statement and run round 2 (done 2026-09-14 for cv-events,
   ng:front-domain and CV:lem:carriers; no round 2 was needed on 2026-09-15/16).
9. `python3 work/port/write_review_and_accept.py <row-id> <slug> <Decl> <Module> <source-file> '<locator text>' reviews/<excerpt>
   reviews/<statement-file> 0 literal,definitions,strength "<kernel text>" "<notes text>" allow-doc-notes` — asserts the verdicts, binds
   the hashes of every file the reviewers read (`reviewer_files_read`), requires the row's statement hash to be in
   work/checks/declaration-audit.json (i.e. the checker ran after mapping), sets the row accepted. Avoid apostrophes inside the quoted texts.
10. Checker again (the receipt must bind the accepted state) → copy to dev-check-<name>-accepted.json; AUTHOR_NOTES entry; STATUS
    checkpoint + tarball to /workspace/scratch/lean_results/ every ~1-2 hours (NOT done on 2026-09-15/16 — see §9); Discord only at milestones.
    After any acceptance also: `python3 tools/check_lean.py work/lean --all`, `--stage 1`, `python3 verify_bundle.py`,
    `bash work/delivery/refresh.sh`, and `python3 work/port/refresh_manifest.py FINAL_REVIEW.md` after editing any manifested root file.

## 5. The lane pattern for large rows (what produced the 3k-40k-line proofs) — 2026-09-14 text plus the 2026-09-15 lessons
Design panel Workflow (2 architects with different emphases + a judge) → work/drafts/<lane>/PLAN_FINAL.md, Statements_FINAL.lean (the
frozen row statement), Skeleton_FINAL.lean (definitions + assembly PROVED, leaves `sorry`) → record the panel's fidelity risks in
AUTHOR_NOTES BEFORE the row is stated → prover Workflow: N units on byte-identical copies U_<unit>.lean (statements frozen; helpers
prefixed; false leaves reported, never changed) + an assembler (diff audit, contiguous hunks, `#print axioms`, clash scan, docstring
without the word sorry) → port → §4. Sizes achieved: 1.3k-15k lines per ported module (largest: SM/FrontRowsW2 14.7k, SM/FrontRowsW3 13.3k,
SM/CornerChainUnits 11.8k, RProof/GenericTransport 11.2k, RProof/ExtremeTransportUnits 9.0k, RProof/GenericSelectedUnits 7.3k,
SM/BigonDeletion 5.4k) in 1-3.5 hours wall time per lane. Lessons: (a) several lanes had a FALSE internal leaf or interface field (D-FL-4,
D-RM-5/6/7, the corner RET finding, the 177 kink statements) — the assembler replaced it with a true/weak form without touching any row
statement, and the accepted library kept its literal field where it was accepted (OPEN_ITEMS §C); (b) skeleton section variables: Lean
includes a `variable` only if the statement mentions it — `include hG in`; (c) Mathlib lemmas outside the skeleton's import closure must be
re-proved or the import added; (d) no forward references — the merger must reproduce the order; (e) very large lanes are ported
INCREMENTALLY as sorry-free modules (D-FR1); (f) unused false leaves are removed at port (D-FR2); (g) `strip_proofs.py` splits at the first
` :=`/` where` at bracket depth 0, skips `let x :=`, and treats a column-0 line as a block end unless it is a proof continuation;
(h) 2026-09-15: state each Reidemeister move as an explicit interface Prop first, prove the ledger from it, realise the move last
(D-CVT-4) — and expect the interface to need a WEAK replay when the literal Prop cannot be inhabited (D-RM-5); (i) a shared constructor
(SM/BigonDeletion.lean, one RII deletion for all sites) beat four per-row realisations (D-RM-1..4); (j) apply the reassessment rule per
branch: three of the five 2026-09-15 lanes closed inside their first bounded window, the two that did not (110, 177) were stopped by
recorded audits rather than by a fourth attempt; (k) keep merge scripts and probes under work/drafts/<lane>/, not in the session scratchpad
(the corner assembler's assemble.py and the reviewers' probe scripts are gone).

## 6. Where things are in work/lean (accepted unless marked)
SM/*: the SM15 foundations, the polygon/chamber/wall layer (WallGerm, NamedWallPredicates, CornerStateSum, CChamber, CSilent, CS3, CS5…),
the link-diagram layer (LinkDiagram, LinkMoves, LinkRecord*, LocalPolynomial, PolynomialBlock, LinkInterfaces = lit:homfly / lp:lm /
lp:lm-uniqueness), the front block (FrontSmooth, FrontPL, FrontWords*, FrontRealize*, FrontInterfaces incl. SM.ng_finite_word,
FrontRowsW2/W2S/W3/W3b, NgBound), the fd block (ParameterAvoidance, ContactMotions, TransverseNeighborhood, GenericFront, LinkingCalculus +
RegularPoleCount + LinkingCalculusRow), the ce block (CeSmoothingRecord, CeRounding, CeRoundingNonVacuity), Rounding, Curl, HypR.
**New 2026-09-15/16 (accepted rows in bold):** SM/LitHomflyDescent.lean (the axiom), SM/ContactPath.lean (**91**), SM/SrcContact.lean (the
axiom, **src:contact**), SM/FdContactStatements.lean + FdContactUnits.lean + FdContact*.lean (**94**; CV rows **161** CV/AxEtnyre.lean and
**162** CV/AxSlbound.lean), SM/CarrierFloor.lean + CarrierFloorRows.lean (**99**, **100**), CV/CarrierFloor.lean (**155**; also the library
interface CV.CarrierSlotFloor read by 165/174/176/177), CV/SingletonDi.lean (**165**), RProof/RALedgers.lean (library: RowShape, the RA
ledgers gsc_/est_/esc_, cv_R_of_rows, sm_R_of_rows — byte-unchanged since its port), RProof/ExtremePairZero.lean (**175**),
SM/CornerChainStatements.lean + CornerChainUnits.lean + the row modules SM/CBSingleton.lean (`SM.CBSingleton` per lean-declarations.json —
capital B; no CbSingleton.lean exists) / CornerValues.lean / CSoft.lean (**103**, **105**, **112**; the CS7Data
statement of row 110 lives in CornerChainStatements), SM/CS7Sliding.lean (library for 110, no row), SM/BigonDeletion.lean (the shared RII
deletion constructor), SM/CornerPolygon.lean + AnchorValues.lean + AnchorValuesRow.lean (**122**), SM/CuspDeletionGeneric.lean +
Comparison.lean + CInherits.lean (library for 127/128: thm_comparison_of, cor_C_inherits_of, the FINAL CInheritsData),
RProof/GenericSelectedUnits.lean + GenericSelected.lean (**174**), RProof/ExtremeTransportUnits.lean + ExtremeTransport.lean (**176**).
CV/*: the CV lane (Events, X1, Carriers, Rounding, Curl, ChamberInv*, PieceCurve, GroupedKnot, …). RProof/*: Cores, X1Rows, X1Rows2,
GenericTransport (rows 166-173; CV:ax:R in RProof/X1Rows). Bridge/B1 (rows Bridge:B1 AND Bridge:B2 — there is no B2.lean), B3, B4.
**UNMAPPED conditional library (never map while their premise is open; D-F11):** SM/ContactPathOfDescent.lean (now consumed by 91),
Bridge/SmR.lean (SM.sm_R_of_cv_R; its header line still says "blocked by GAP-2"), RProof/X1Rows3.lean, SM/LinkingCalculus.lean,
RProof/RALedgers.lean, SM/Comparison.lean, SM/CInherits.lean, SM/FdContactStatements.lean (`_of` forms), SM/CarrierFloor.lean (`_of_bound`
forms), SM/CornerChainUnits.lean, SM/CS7Sliding.lean, SM/BigonDeletion.lean — these are OUTSIDE the checker's audited count unless a mapped
module imports them (OPEN_ITEMS §F-01). **Do not exist (verified):** SM/CS7.lean, SM/CS7Units.lean, SM/ComparisonRows.lean,
RProof/ExtremeSelected.lean, RProof/GenericTransportSw*.lean, RProof/CvR.lean, Bridge/SmRRow.lean — they are the modules the pending rows
would occupy.

## 7. Open work — what remains and what it would take (details and pointers: OPEN_ITEMS_20260916.md §A, §G)
- **Row 110 thm:C-S7** (SM.thm_C_S7 : CS7Data): `thm_C_S7 := thm_C_S7_of_floor thm_floor` typechecks in work/drafts/corner/W3_Assembled.lean
  (8958 lines, 0 errors) with sorryAx through the two branch leaves; sorry-free glue reduces them to FIVE Props — sliding S1 w3_SlidingRet
  (line 4705; FALSE as stated on the leg-M side, must be restated on RET's corrected s7r_SlidingTransport', 500-700 lines) and S3
  w3_SlidingCarriers (4730; 1,300-2,050); bigon B1 w3_BigonFSector (8824; 2,300-3,600 incl. F's three boxes), B2 w3_BigonReturnedRows
  (8841; 3,500-5,400 incl. SITE's hrec/clearance), B3 w3_BigonOneNewborn (8859; 400-700). S2 is proved. ≈ 8-12k lines, 2-3 waves. Audit
  A-110-1 stopped construction; **the author decides** (§G-01). Then 127/128 are one-liners (SM/ComparisonRows.lean, one-liners in
  work/drafts/comparison/port/PORT_REPORT.md) and 184 needs also 183 and the CInheritsData re-typing (OPEN_ITEMS §A-21/A-22).
- **Row 177 R:extreme_selected** (RProof.extreme_selected : RowShape @ExtremeSelectedData): work/drafts/moves/W3C_Assembled.lean (16 945
  lines, 0 errors); the operative chain w3ck_extreme_selected has exactly two sorryAx sources — w3cx_outer_residue_data (decl 16425: parity
  #mixedSet = 2Λ + KNOT's identification, 0.7-1.3k, route known) and w3cs_not_kink_site_data (decl 13745: 0.3-0.6k, route OPEN, may need
  an event hypothesis — an author question); on closure RProof.extreme_selected carries all nine registered axioms incl. the descent axiom
  and src_contact (W3C_AXIOMS.log:2; OPEN_ITEMS §B-04) — plus two skeleton statement edits at port and the ≈ 7.8k mechanical port of the trans-free
  G11_ConfigSw copy (or the author's cheaper edit dropping G11_Config.trans, §G-03). Audit A-177-2 stopped construction; **the author
  decides** (§G-02). Then 178 (RProof.cv_R) and 183 (Bridge.sm_R, a TARGET) are the staged one-liners in work/drafts/cvtail/port/R178_183/.
- **Row 57 lem:gauss-two-discs:** deferred by the author (12-20k lines).
- **Author decisions pending besides the two windows:** confirm/revert the verify_bundle.py relaxation (§G-06); the registry sub-entry
  (§G-07); bundled vs literal descent axiom (§G-08); the false-as-stated accepted fields est_PortData.port/rot/alt (§G-04); comment-only edits
  in accepted modules (§G-05); human spot-check of the AI-only reviews (§G-10).
- **Executor-doable now (no decision needed):** build the missing 2026-09-15/16 tarball (§9); the documentation items of OPEN_ITEMS §E marked
  executor (AN entries for FR-SC-11 and row 174's σ, review-brief locators, STATUS top block, delivery README prose, the table generator);
  fix `source_sha256` in the two row-91 records (§E-04).

## 8. Inventory of tools and evidence (2026-09-14 text, updated)
tools/claims.py (--pending-only, --json, --next), tools/progress.py (--once, --watch), tools/check_lean.py (development / --stage / --all),
setup.sh, verify_bundle.py (line 100 relaxed 2026-09-15, D-GAP2-2b: label-part comparison of literature keys). work/port/: map_row.py,
strip_proofs.py, summarize_review.py, write_review_and_accept.py, refresh_manifest.py, review_prompt_*.md (one per reviewed row/group),
make_lane_modules.py (2026-09-13 prototype, unused). work/reviews/: <slug>.json (review records — 17 new on 2026-09-15/16),
*-reviewer-input-statement.lean.txt, *-source-excerpt-*.txt, *-review-workflow-raw.json (frozen; never regenerate an accepted row's inputs).
work/checks/: dev-check-*.json (100 receipts, all passed; current dev-check-FINAL-20260916.json), stage-development.json,
stage-1.json (the `{"passed": false, "stage": 1, "state": "checking"}` placeholder of the 00:33Z --all run), stage-all-check-20260916-0032.log,
checker-run-*.log, port-comparison-chain.log; declaration-audit.json (197 723 lines) and lean-check.log are regenerated by every checker run
and are NOT in any archive (the audit is gzipped in work/delivery/receipts/). work/drafts/<lane>/: PLAN_FINAL.md, Statements_FINAL.lean,
Skeleton_*.lean, unit files, *_REPORT.md, assembly/merge reports — the provenance of every ported module; new lanes 2026-09-15: gap2 (row 91
plan), floor, contact, corner (incl. port/CS7_STATE.md, W3_*.lean, W3_*_REPORT.md), cvtail (incl. port/R178_183/), comparison (incl.
port/PORT_REPORT.md), moves (incl. W3_A1_Assembled.lean, W3B/W3C_Assembled.lean — sha256 prefixes b8c7b7d1 / cbedf6d6 / dbcd1037, OPEN_ITEMS §A-15 —,
W3C_ASSEMBLY_REPORT.md, assemble_W3C*.py and check_W3_*.py (run them from work/drafts/moves/: relative filenames, W3C_Assembled.lean is
overwritten), clash_scan_W3.py, W3C_AXIOMS.log, port/ (R174 and R176 only, no R177), Site_174/176.lean, R174_*.lean, R176W2_*.lean), rlane2 (NOTES_FINAL.md). work/delivery/: README.md
(prose still 2026-09-14), refresh.sh, pins, declaration-map, reviews, receipts, progress, FINAL_REVIEW_ADDENDUM_DRAFT_20260915.md,
tools/gen_final_review_tables.py (stale, OPEN_ITEMS §E-17). work/repairs/: ShiftZeroTurn.lean, index.json (unchanged). Package root: the stray file '=3' was deleted 13:50Z 2026-09-15 on the
author's instruction (D-GAP2 item 4, AN L5180; MANIFEST line refreshed, verify_bundle PASS — OPEN_ITEMS §E-28). Checkpoint tarballs:
/workspace/scratch/lean_results/RESULT_2026091{3,4}_*.tgz (32 files; last: RESULT_20260914_1820Z_FINAL.tgz) and the handover
LEAN_HANDOVER_20260914_2115Z.tgz in /workspace/repos/lean/ and /workspace/scratch/lean_results/ (excludes work/lean/.lake,
work/checks/declaration-audit.json, lean-check.log; adds handover_extras/ with the project CLAUDE.md, reassessment_rule.md and memory files;
env.sh excluded). **Nothing of 2026-09-15/16 is archived.** Memory of the executing Claude sessions:
/root/.claude/projects/-workspace-repos-lean/memory/*.md.

## 9. If you resume
1. `source /workspace/envs/lean/env.sh`; `pgrep -f '^python3 tools/check_lea[n]'` (expect nothing); `python3 tools/progress.py --once`
   (expect 124/132); restart your ≤15-minute heartbeat.
2. **Build the missing archive first:** `cd /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME && tar czf
   /workspace/repos/lean/LEAN_HANDOVER_20260916_<HHMM>Z.tgz --exclude=CORNER_LAWS_FOCUSED_20260912/work/lean/.lake
   --exclude=CORNER_LAWS_FOCUSED_20260912/work/checks/declaration-audit.json --exclude=CORNER_LAWS_FOCUSED_20260912/work/checks/lean-check.log
   CORNER_LAWS_FOCUSED_20260912` and copy it to /workspace/scratch/lean_results/; record the sha256 and time in AUTHOR_NOTES.
3. Run the development checker once (`nohup python3 tools/check_lean.py work/lean > work/checks/checker-run-<HHMM>.log 2>&1 &`) and confirm
   the receipt still says 184 mapped / 41 658 audited.
4. Then either (i) wait for the author's answers to OPEN_ITEMS §G-01/§G-02 (and §G-03 before any 177 port), doing the executor-only
   documentation items of §E meanwhile; or (ii) if a window is opened, record the new audit window in AUTHOR_NOTES (rule §F-06: it is a new
   window on a branch with a stagnation history), then follow OPEN_ITEMS §A-02/§A-15 in the recorded order of attack; or (iii) open the
   row-57 lane only if its 12-20k-line cost is explicitly accepted. Apply the reassessment rule to every branch; record audits in
   AUTHOR_NOTES; report an incomplete stage as incomplete.

---
*Historical note kept from the 2026-09-14 version:* "Verified against the repository by a second agent, 2026-09-14 21:15 UTC / 5:15pm ET:
every path and script above exists; the counts 109/132, 168/192, 4/8, 24 = 22 GAP-2 + row 57 + src:contact, ~248k lines, 168 mapped /
36 079 audited; the §4 argument lists (write_review_and_accept.py sys.argv[1:13] + optional allow-doc-notes, map_row.py implement,
strip_proofs.py); the §7 chain against claims.py/DEPENDENCIES.json; and check_lean.py line 104 (hyp:R → SM.hyp_R) all check out." Those
2026-09-14 counts are superseded by §0 above; the script signatures and the check_lean.py:104 fact were re-verified on 2026-09-16 by grep.
Not verified in this rewrite: wall-clock claims (checker 4-6 min, lanes 1-3.5 h), and the contents of Bridge/SmR.lean beyond its
declaration list.
