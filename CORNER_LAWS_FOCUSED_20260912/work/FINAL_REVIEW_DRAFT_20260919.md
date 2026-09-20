# Final fidelity review

The execution lead assigns an independent reviewer locally. This is a concrete
review of implemented Lean declarations against supplied source, not an author
approval request. Record the review and candidate hashes in work/reviews/.

- The definitions denote the source objects: actual polygons, their connected-
  component chambers, continuous wall germs, independent supports, carriers,
  local polynomials and the full state sum. No empty domain or hidden assertion
  of the desired theorem is substituted for these definitions.
- Each source/Lean pair preserves its quantifiers, hypotheses and conclusions.
  Expand local helper definitions when assessing meaning. Hashes detect changes
  in those definitions; they do not decide mathematical equivalence.
- The permitted literature declarations have exactly their printed meanings.
  No extra axiom, sorryAx or native_decide axiom enters a theorem. In particular,
  an axiom with an allowed name but a stronger type is not an allowed input.
- The conditional comparison theorem exposes its R parameter. The proved CV R
  theorem, the resulting SM R theorem and each unconditional final theorem have
  no extra R, lawful-quantity, corner-law or equivalent proof assumption. Inspect
  parameters explicitly; axiom output alone cannot establish this.
- R covers the entire printed simple, transversal, forced-bundle domain. The
  proof includes every availability case and both graph orbits. It does not
  import an R-dependent result to prove R. B1–B4 compare the actual SM15 and CV
  conventions and scalar values, with no assumed equality of their generic loci.

For the focused `SM.corner_laws_and_soft`, check every clause separately:

| Clause | Source comparison required |
|---|---|
| Chamber constancy and silence | `prop:C-chamber`, `prop:C-silent` |
| Flat deletion jump | `thm:C-S3`, including the actual deletion and side sign |
| Vertex-edge jump | `thm:C-S7`: both bigon graph branches and sliding; actual children and sign |
| Triple invariance | `hyp:R` after discharging it with the proved R/bridge theorem |
| Full cusp jump | `cor:C-inherits` and `cor:A-lawful`: deletion satisfies G1; threaded cusps included |
| Empty-cusp zero | `thm:C-S5` |
| Soft theorem | `thm:C-soft`: every admissible direction/attachment-sign sector, including zero sectors, and the sufficiently-small-epsilon quantifier |
| Descent and normalization | The cyclic, reversal and triangle statements required by the inherited source result |

The conclusion concerns the source C, not an arbitrary function supplied with
the desired laws. Every argument at which C is evaluated must satisfy its source
domain. A proof for an empty cusp or one soft sector is not the full target.

In the full handoff, review all commissioned source rows and both independent
computation certificates as README.md requires. Preserve raw certificate data,
coverage arguments and reproduction evidence; copied table entries are not an
exhaustive computation.

Run `python3 tools/check_lean.py work/lean --all` on the final files. This checks
all three stages in the full package and the single complete stage in the focused
package. Retain those receipts, reviews and progress history in the delivered
implementation. A receipt must still match code, reviews, sources and policy.

# Completed fidelity review — 2026-09-19 (pod executor)

**Final fidelity review — completed <<ROW57: fill at acceptance — FINAL-TIME, UTC and New York time, from `tools/progress.py --once`>> (pod executor).**
This is the 2026-09-16 review (its text of record at 02:33Z that day is preserved unchanged in the handover archive
`LEAN_HANDOVER_20260916_0233Z.tgz` and as `work/delivery/FINAL_REVIEW.md`; the 2026-09-14 text as `work/FINAL_REVIEW_DRAFT.md`)
updated section by section after the executor resumed on 2026-09-19 05:35Z under the author's response **D-AUTH-20260919**
(`work/AUTHOR_NOTES.md` L6520, verbatim copy `work/AUTHOR_RESPONSE_20260919.md`; received through Mark 05:33Z): "Continue to
completion … Both stopped branches (row 110 and row 177) are re-opened now, with no bound. Row 57 is un-deferred." Paths are
relative to the package root; `reviews/<row>.json` means `work/reviews/<row>.json`. The draft of this text was written at 13:26Z-14:00Z
2026-09-19 (9:26-10:00am ET) while row 57's wave 2 was running; every place that depends on row 57's outcome or on the closing
build cycle carries the marker `<<ROW57: …>>` and is filled by the executor at acceptance (§3.2, §4.9, §5, §7).

**Status: final; the focused stage is <<ROW57: fill at acceptance — COMPLETE / INCOMPLETE per the closing `--all` run>>.**
It follows the checklist of FINAL_REVIEW.md item by item. The machine-derived tables (§1, §2, §3, §4.4) were regenerated at
2026-09-19 13:4xZ from `python3 tools/claims.py --json`, the map and the 13:28Z `work/checks/declaration-audit.json`, through the
scratch helper `scratchpad/frdraft/gen_tables_20260919.py` (not part of the package; §7): the 184 rows of the 2026-09-16 table are
reproduced byte-identically and their axioms column re-verified against the new audit (0 mismatches), the seven rows accepted on
2026-09-19 are new lines. This is a fidelity review of implemented Lean declarations against the frozen SM15 source; it is not an
author approval and it does not claim the mathematics finished beyond what the kernel checked (§5). State at draft time (13:26Z
2026-09-19 / 9:26am ET; `tools/progress.py --once` at 13:30Z): **claims verified 131/132 (99.2%); checklist 191/192 accepted, 0
implemented-awaiting-review, 1 pending (57 `lem:gauss-two-discs`, wave 2 running); final targets 8/8 (`prop:C-chamber`,
`prop:C-silent`, `thm:C-S3`, `thm:C-S7`, `thm:C-S5`, `thm:C-soft`, `Bridge:theorem`, `SM:corner_laws_and_soft` — every fixed target of
EXECUTION.json accepted); development checker passed 13:28Z (191 mapped, 46 842 audited; `work/checks/dev-check-rows110-127-128-184-accepted.json`
= `stage-development.json`).** Final state: **<<ROW57: fill at acceptance — claims verified N/132; checklist N/192; the closing
`python3 tools/check_lean.py work/lean --all` result line (STAGE-CHECK-RESULT) with its log name and audited count; `verify_bundle.py` result>>.**
State of record on 2026-09-16 02:33Z (the previous version of this review): 124/132, 184/192, 8 pending (57, 110, 127, 128, 177, 178,
183, 184), targets 5/8, stage check FAIL — reported as incomplete. State at 2026-09-14 18:15Z: 109/132, 168/192, targets 4/8.

The seven rows accepted on 2026-09-19, in order (AUTHOR_NOTES entry times): `R:extreme_selected` (177), `R:cv_theorem` (178),
`Bridge:theorem` (183) at 08:39Z (review workflow wf_b3114d58-914); `thm:C-S7` (110), `thm:comparison` (127), `cor:C-inherits` (128),
`SM:corner_laws_and_soft` (184) at 13:26Z (workflow review-rows-110-127-128-184, 12:57-13:24Z). No new axiom, no policy edit, no tool
edit, no edit to any accepted module (comment-only edits are AUTHORISED by G-05 and PREPARED, `work/port/docdebt/`, but NOT yet applied —
D-DOC-2, §5, §6). Nothing accepted before 2026-09-19 was changed: all 184 earlier rows keep their `statement_sha256`, and at draft time
every one of the 191 accepted rows' `statement_sha256` equals `statement_hashes` of the 13:28Z audit (verified over the whole map, §1);
`RProof/RALedgers.lean` (sha256 `df745f12…`), `RProof/GenericTransport.lean` (`0e7f959d…`) and `SM/CornerChainUnits.lean` (mtime
2026-09-15 20:00Z) are byte-unchanged (the `project_sha256` entries of the 18:11Z 2026-09-15, 05:45Z and 13:28Z 2026-09-19 receipts agree).

## 0. Sources of truth used

- Row status, declaration, module, review file: `work/lean/lean-declarations.json` (192 rows; edited only through
  `work/port/map_row.py`). Claim numbering "#": `python3 tools/claims.py --json` (184 units in document order; the 8 map rows
  outside it — 5 literature interfaces, `hyp:R`, `CV:ax:R`, `lem:weak-open` — are tagged `m<map index>`). The notes and STATUS.md
  use the claims.py numbers (row 91 = `cp:finite-contact-path`, row 57 = `lem:gauss-two-discs`, row 184 = `SM:corner_laws_and_soft`).
- Kernel evidence: `work/checks/stage-development.json` (current development receipt, byte-identical to
  `work/checks/dev-check-rows110-127-128-184-accepted.json`, 2026-09-19 13:28Z: passed=true, stage=null, stage_accepted=false,
  191 mapped, 46 842 audited; `project_sha256` 710 entries) and `work/checks/declaration-audit.json` (13:28Z, 1.08 GB;
  per-declaration axioms for the 191 mapped declarations, `statement_hashes` keyed by row id); per-run receipts
  `work/checks/dev-check-*.json` (105 files, all passed: 27 of 2026-09-13, 53 of 2026-09-14, 18 of 2026-09-15, 2 of 2026-09-16,
  5 of 2026-09-19); logs `work/checks/checker-run-20260919-0542.log`, `-0808.log`, `-0839.log`, `_1256Z.log`, `_1325Z.log`. Stage
  check: NOT run in this session at draft time — `work/checks/stage-1.json` is still the 2026-09-16 00:33Z record `{"passed": false,
  "stage": 1, "state": "checking"}` and `work/checks/stage-all-check-20260916-0032.log` the 2026-09-16 FAIL; the closing `--all` run is
  part of the closing cycle (§4.9): <<ROW57: fill at acceptance — closing `--all` log name, receipt, audited count>>.
- Reviews: `work/reviews/<row>.json` (one per accepted row, 191; the reviewer's inputs sit next to it as
  `<row>-reviewer-input-statement.lean.txt` and `<row>-source-excerpt-*.txt` / `<row>-registry-excerpt.md.txt`; raw workflow output
  `<row>-review-workflow-raw.json`), plus the interface review `lit-homfly-descent.json` (not a checklist row). All 191 verdicts
  `faithful` (recounted at draft time).
- Policy: `work/lean/axiom-policy.json` = `lean/axiom-policy.json` (byte-identical, re-checked 2026-09-19): standard axioms, six
  literature keys (the five registry ids plus `"lit:homfly (descent sentence)"`, §4.3), the hypothesis (`SM.hyp_R`, mode
  `explicit_parameter`), 28 fixed target names; `blueprint/AXIOM_REGISTRY.md` (frozen; the G-07 sub-entry is prepared as
  `work/port/docdebt/registry-sub-entry.patch`, not applied at draft time); `blueprint/DEPENDENCIES.json`; the execution rule
  `/workspace/repos/lean/reassessment_rule.md` (adopted 2026-09-14 17:00Z) as amended by D-AUTH-20260919 §2 (a failed audit on cost
  never stops a branch; §6).
- Decisions and disclosed readings up to 2026-09-16: `work/AUTHOR_NOTES.md` (2026-09-13/14 labels D-*, D-F1..D-F16, D-FR1, D-ER1,
  D-CP-1, FR-*, FR-C*, FR-R*, FR-CP-*, FR-ER-*, CE-R*, K-*, R-*, GAP-1/GAP-2; 2026-09-15/16 labels D-GAP2-1..4, D-GAP2-2b, D-SC-1..6,
  D-FL-1..4, D-CC-1..5, D-CVT-1..6, D-CM-1..5, D-RM-1..7; fidelity-risk lists FR-LHD-1..4, FR-FL-*, FR-SC-1..11, FR-FC-1..7,
  FR-CC-1..15, FR-CV-155-1..9, FR-CV-165-1..4, FR-R-174..178, FR-B-183, FR-F-184-1..4, FR-CM-1..17; audits A-110-1, A-177-1, A-177-2),
  `work/drafts/gap2/GAP2_STATEMENTS_MEMO.md`, `work/drafts/pldiscs/PLDISCS_FEASIBILITY.md`, the open-items register
  `OPEN_ITEMS_20260916.md` (§A rows and leaves, §B axioms, §C library findings, §D review notes, §E documentation debts, §F tooling,
  §G the author's decisions — answered by D-AUTH-20260919), `work/RESUME_FOR_NEXT_AGENT.md`.
- **2026-09-19 additions.** `work/AUTHOR_NOTES.md` from "## D-AUTH-20260919 — the author's response to OPEN_ITEMS_20260916.md §G"
  (L6520, 05:36Z) to the 13:29Z line of the entry "ROWS 110 thm:C-S7, 127 thm:comparison, 128 cor:C-inherits, 184
  SM:corner_laws_and_soft ACCEPTED" (L7005-7023): the author's decisions G-01..G-15 and the standing rule change §2; D-DOC-1 (06:06Z),
  D-DOC-2 (10:37Z); D-TD-0 (08:23Z), D-TD-1 (the row-57 readings FR-TD-1..14 copied verbatim), D-TD-2 (11:37Z), D-TD-3 (11:54Z);
  audits A-110-2 (11:22Z) and A-177-NK-1 (NONKINK, 07:17Z); rule-3 findings of the corner waves 5-6 (10:47Z, 12:01Z, 12:04Z) and of the
  row-57 units (11:37Z, 11:54Z). `work/STATUS.md` (header last updated 13:26Z). Lane files: corner —
  `work/drafts/corner/W4_ASSEMBLY_REPORT.md`, `W5_ASSEMBLY_REPORT.md` (§5 honest state, §6 wave 6, §8 deviations), `W5_BR_REPORT.md`
  (written by the executor, §6), `W6_ASSEMBLY_REPORT_B.md` (§0, §4-§5, §8), `W6_Assembled_B.lean` (27 531 lines, the port source) and
  `W6_Assembled.lean` (27 533, instance A, cross-check), `port/CS7_B/PORT_REPORT.md` (§1 axioms, §2 the 26 deletions, §3 the 27
  rewordings); moves — `work/drafts/moves/W3D_NONKINK_REPORT.md`, `W3D_RESPAR_REPORT.md`, `W3D_RESID_REPORT.md`,
  `W3D_ASSEMBLY_REPORT.md` (§0, §2, §6), `W3D_Assembled.lean` (21 748 lines, 0 `sorry`), `W3D_AXIOMS.log`, `port/R177/PORT_REPORT.md`;
  cvtail — `work/drafts/cvtail/port/SM/CornerLawsAndSoft.lean` (the row-184 module prepared 10:36Z, edit A-22); twodiscs (row 57) —
  `work/drafts/twodiscs/PLAN_FINAL.md` (§2 risks, §5 readings), `Statements_FINAL.lean` (305 lines, frozen), `Skeleton_FINAL.lean`
  (1 039 lines, 92 leaves), `SKELETON_REPORT.md`, `W1_ASSEMBLY_REPORT.md` (§0, §2.2 corrected forms, §5 wave-2 specification),
  `W1_Assembled.lean` (13 815 lines), the unit reports `W1_U*_REPORT.md`, `W2_U6/U7/U9_REPORT.md`; documentation —
  `work/port/docdebt/APPLY.md` + 11 patches + `check_comment_only.py`.
- **Kernel evidence 2026-09-19:** 5 development receipts, all passed (mapped / audited): `dev-check-resume-20260919.json` (05:45Z;
  184 / 41 658 — the resume check, identical counts to the 2026-09-16 closing receipt), `dev-check-rows177-178-183-implemented.json`
  (08:11Z; 187 / 44 270), `dev-check-rows177-178-183-accepted.json` (08:42Z; 187 / 44 270), `dev-check-rows110-127-128-184-implemented.json`
  (12:59Z; 191 / 46 842), `dev-check-rows110-127-128-184-accepted.json` (13:28Z; 191 / 46 842; = the current `stage-development.json`).
  Per-declaration axioms: `work/checks/declaration-audit.json` (13:28Z; rows only for the 191 mapped declarations, §7). Draft-level
  `#print axioms` evidence (not checker receipts): `work/drafts/moves/W3D_AXIOMS.log` (31 declarations), the whole-file censuses of both
  W6 glue assemblies (1 453 declarations each; `W6_ASSEMBLY_REPORT_B.md` §4), `port/CS7_B/PORT_REPORT.md` §1, the executor's probe of
  12:57Z (AUTHOR_NOTES L6984-6997).
- **Reviews 2026-09-19:** `work/reviews/{r-extreme-selected, r-cv-theorem, bridge-theorem}.json` (08:39Z; workflow wf_b3114d58-914;
  briefs `work/port/review_prompt_{r-extreme-selected,r-cv-theorem,bridge-theorem}.md`) and `work/reviews/{thm-C-S7, thm-comparison,
  cor-C-inherits, sm-corner-laws-and-soft}.json` (13:25Z; workflow review-rows-110-127-128-184; briefs
  `work/port/review_prompt_{thm-C-S7,thm-comparison,cor-C-inherits,sm-corner-laws-and-soft}.md`); raw output
  `<slug>-review-workflow-raw.json`; reviewer inputs `<slug>-reviewer-input-statement.lean.txt`; excerpts
  `r-extreme-selected-source-excerpt-R_EXTREME_SELECTED_COUPLE_PROOF.md.txt` (the whole printed proof file),
  `r-cv-theorem-source-excerpt-d10_axioms-lines-15-40.tex.txt`, `bridge-theorem-source-excerpt-lines-1443-1475.md.txt` (BRIDGE.md §3),
  `thm-C-S7-source-excerpt-lines-266-276.tex.txt` (sm-4), `thm-comparison-source-excerpt-lines-299-311.tex.txt` (sm-6),
  `cor-c-inherits-source-excerpt-lines-313-369.tex.txt` (sm-6), `sm-corner-laws-and-soft-source-excerpt-TARGETS.md-lines-1-29.txt`.
- **Library (mapped and unmapped) added 2026-09-19, all sorry-free:** `RProof/GenericTransportSw.lean` (7 845 lines; the additive
  trans-free copy `G11_ConfigSw`/`G11_ParamsSw` of the accepted RIII transport, G-03 route (ii); library, imported by the row module),
  `RProof/ExtremeSelectedUnits.lean` (13 944; the row-177 units, imports `RProof.ExtremeTransportUnits`, `SM.CBProducts`,
  `CV.SingletonDi`, `SM.ZeroRotationSeed`), `RProof/ExtremeSelected.lean` (48; row 177), `RProof/CvR.lean` (25; row 178),
  `Bridge/SmRRow.lean` (18; row 183) — ported 08:06-08:08Z; `SM/CS7Units.lean` (27 000 lines, ONE module; the corner-lane unit corpus
  of waves 3-6 after the 26 deletions and 27 rewordings of `port/CS7_B/PORT_REPORT.md`; imports `SM.CornerChainUnits`,
  `SM.CS7Sliding`, `SM.BigonDeletion`, `SM.CarrierFloorRows`), `SM/CS7.lean` (97; the two leaves, `thm_C_S7_of`, `thm_C_S7_of_floor`,
  row 110), `SM/ComparisonRows.lean` (26; rows 127/128), `SM/CornerLawsAndSoft.lean` (86; row 184) — ported 12:54Z. `work/lean` now
  holds 706 `.lean` files (652 SM, 32 CV, 15 RProof, 5 Bridge, `Supplemental.lean`, `Supplemental/Audit.lean`), 345 000 lines
  (`find | xargs cat | wc -l` at draft time; 697 files / 295 911 lines on 2026-09-16). No `sorry` term anywhere in `work/lean`
  (`grep` for `sorry` bodies: 0; the word occurs only in 55 module header comments — the E-11 "sorry-free" phrases, patch 09 of D-DOC-2).
- Source frame SM15: `reference/`, `provenance/SM15`, `blueprint/` (frozen; never edited; the one authorised addition, the G-07
  registry sub-entry, is applied at the closing cycle).
- Row 57 at draft time: `work/drafts/twodiscs/` as above; the outcome, its review file, receipt and modules: <<ROW57: fill at acceptance>>.

## 1. Summary of the 132 claims / 192 checklist rows by status  (table regenerated 2026-09-19 13:4xZ; <<ROW57: fill at acceptance — regenerate after row 57 lands>>)

<!-- BEGIN:SUMMARY -->
| unit class | total | accepted | implemented (awaiting review) | pending |
|---|---|---|---|---|
| source claims (tools/claims.py: "claims verified") | 132 | 131 | 0 | 1 |
| definitions / conventions (units of work, not claims) | 52 | 52 | 0 | 0 |
| literature interfaces + hypotheses + extra lemma (map rows outside claims.py) | 8 | 8 | 0 | 0 |
| checklist rows total (work/lean/lean-declarations.json) | 192 | 191 | 0 | 1 |
| final targets (EXECUTION.json) | 8 | 8 | 0 | 0 |

Generated 2026-09-19 13:4xZ (draft) from `python3 tools/claims.py --json` (claims verified 131/132), the map and `work/checks/declaration-audit.json` (2026-09-19 13:28Z, the audit of the current receipt). Current checker receipt work/checks/stage-development.json: passed=True, stage=None, stage_accepted=False, mapped_declarations=191, audited_declarations=46842.
<!-- END:SUMMARY -->

State at draft time (`work/PROGRESS.md`, written by `tools/progress.py` at 2026-09-19 13:30:45Z: "claims verified 131/132 (99.2%);
kernel-checked awaiting review 0; 99.5% checklist (191/192 accepted); targets 8/8"; `python3 tools/progress.py --once` at
<<ROW57: fill at acceptance — the executor's exit line, UTC and New York time>> is the exit line): claims verified 131/132, checklist
191/192, targets 8/8 (all eight of EXECUTION.json: `prop:C-chamber`, `prop:C-silent`, `thm:C-S3`, `thm:C-S7`, `thm:C-S5`, `thm:C-soft`,
`Bridge:theorem`, `SM:corner_laws_and_soft`), 0 rows implemented-awaiting-review, 1 pending — the claim row 57 `lem:gauss-two-discs`
(`python3 tools/claims.py --pending-only` at draft time lists exactly this row; the eight map rows outside claims.py and the 52
definition rows are all accepted, as on 2026-09-16). The seven rows pending on 2026-09-16 other than 57 — 110, 127, 128, 177, 178, 183,
184 — were accepted on 2026-09-19 (§3.1, §3.4). All 191 accepted rows have `statement_sha256` equal to `statement_hashes` of the
13:28Z audit (re-checked at draft time over the whole map: 191/191 equal, 0 mismatches; every accepted declaration has an audit row)
and a review file with `verdict: "faithful"` (191/191; the checker enforces the same). Final: <<ROW57: fill at acceptance — 132/132,
192/192, 8/8 if row 57 is accepted; otherwise the honest state of §3.2>>.

## 2. Accepted rows — one line each  (table regenerated 2026-09-19 13:4xZ; 191 rows; <<ROW57: fill at acceptance — add row 57's line if accepted>>)

Columns: `#` claim number (claims.py) or `m<map index>`; axioms from `declaration-audit.json` (13:28Z) with `std` = propext,
Classical.choice, Quot.sound; `H` = `SM.lit_homfly`; `HD` = `SM.lit_homfly_descent` (2026-09-15; the second declaration of
lit:homfly, §4.3); `LM` = `SM.lp_lm`; `LMU` = `SM.lp_lm_uniqueness`; `NG` = `SM.ng_finite_word`; `SC` = `SM.src_contact` (the
fifth interface, declared 2026-09-15); `9` abbreviates the full set `std+H+HD+LM+LMU+NG+SC` (nine constants), the footprint of
every row downstream of `fd:contact` — now including the final theorem. Over the 191 accepted rows (recounted at draft time from the
13:28Z audit): `std` only 114 rows; `std+LM` 21; `9` 20 (13 on 2026-09-16: + 110, 127, 128, 177, 178, 183, 184); `std+H+LM+LMU` 17;
`std+H` 11; `std+SC` 2 (`src:contact`, `CV:ax:etnyre`); `std+LM+NG` 2 (rows 83, 93); `std+LM+LMU` 2; `std+NG` 1 (`ng:finite-word`);
`std+H+HD+LM+LMU` 1 (row 91) — the same ten patterns as on 2026-09-16, nothing else. Per constant: `H` in 49 rows (42 on
2026-09-16), `HD` 21 (14), `LM` 63 (56), `LMU` 40 (33), `NG` 23 (16), `SC` 22 (15). No `sorryAx`, no `Lean.ofReduceBool`, no other
constant in any mapped declaration. "Disclosed readings" is one clause taken from the review's `discrepancies` /
`stronger_than_source` / `weaker_than_source` arrays and the AUTHOR_NOTES fidelity-risk entries ("[N notes]" = the number of
entries in those three arrays; every entry is marked non-blocking by its reviewer); "labels" names the recorded risk/decision
items the reviewers cited. All 191 verdicts are `faithful`; 39 handover rows additionally carry `countersignature_20260913`
(re-review by separate sessions, AUTHOR_NOTES 2026-09-13 ~16:15Z), and `lem:chi-basic`, `lem:g1`, `prop:A-chamber` carry the SM15
`source_realignment.re_review`. The 16 rows accepted on 2026-09-15/16 and the 7 rows accepted on 2026-09-19 (177, 178, 183, 110, 127,
128, 184) each had one workflow of three lens reviewers ("literal", "definitions", "strength") + two adversarial refuters ("not
refuted"), proof withheld (§6). Identities in the map for these 23 rows: author `executor-pod-claude-fable-5-1-20260913` (151 of the
191 accepted rows; `root-implementation-20260910` 39, `executor-coldstart-claude-fable-5-1-20260912` 1); reviewer string
`reviewer-pod-claude-fable-5-1-20260913 (independent Claude Code workflow subagents …)` (151; `review_chirotope-independent-20260910`
30, `review_relgp_full-independent-20260911` 9, `reviewer-coldstart-claude-fable-5-1-20260912` 1) — the identity string carries the
date of its first use, while each review's `ai_review_disclosure` says the five subagents were spawned on 2026-09-15 / 2026-09-16 /
2026-09-19 (§7). Review workflows (AUTHOR_NOTES): wf_2975467c-92c (91 + the axiom), wf_728083df-580 (src:contact, 161),
wf_abec340f-6fd (94, 162), wf_eb7abb51-523 (99, 100), wf_dfc10382-689 (155, 165, 175), wf_2a10c8d9-b97 (103, 105, 112), wf_958e4651-ab4
(122), wf_ab43b209-c32 (174), wf_76eac4cf-aa7 (176), wf_b3114d58-914 (177, 178, 183; 2026-09-19 08:39Z), review-rows-110-127-128-184
(110, 127, 128, 184; 2026-09-19 13:25Z, 20 agents). The 184 lines of the 2026-09-16 table are reproduced byte-identically (their
readings unchanged); the seven new lines cite the review files' arrays and AUTHOR_NOTES L6640-7023.

<!-- BEGIN:ACCEPTED -->
| # | row | Lean declaration | module | review file | verdict | axioms | disclosed readings (one clause) |
|---|---|---|---|---|---|---|---|
| 1 | `def:polygon` | `SM.polygonData` | SM.Polygon | reviews/def-polygon.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); The printed meta-clause 'every notion below is invariant under σ' is not part of the definition's content and is only p… [3 notes] |
| 2 | `def:chirotope` | `SM.chirotopeData` | SM.Chirotope | reviews/def-chirotope.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Definitions are given on a wider domain than the printed one: chi and turn are defined for every n (including n = 0, 1,… [1 note] |
| 3 | `lem:chi-basic` | `SM.chi_basic` | SM.Chirotope | reviews/lem-chi-basic.json | faithful | std | handover review + countersignature 2026-09-13; SM15 wording-only change (left/right naming convention) re-read and countersigned (source_realignment.re_review) |
| 4 | `def:generic` | `SM.Generic` | SM.Generic | reviews/def-generic.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); G2 reads 'three distinct edge segments' as three pairwise distinct indices (Generic.lean:14-17); if two differently ind… [2 notes] |
| 5 | `lem:g1` | `SM.g1` | SM.G1Consequences | reviews/lem-g1.json | faithful | std | handover review + countersignature 2026-09-13; SM15 clause (iv) "two distinct adjacent edges" — SM.g1 already states i ≠ j (re_review countersigned) |
| 6 | `def:crossings` | `SM.crossingData` | SM.CrossingEquiv | reviews/def-crossings.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); The Lean crossing set, point, parameter and sign are total definitions on every LabelledTuple n (only [NeZero n] for cr… [3 notes] |
| 7 | `lem:crossing-test` | `SM.crossing_test` | SM.Crossings | reviews/lem-crossing-test.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Finiteness of X(P) (third conjunct, Crossings.lean:161) is asserted under G1 alone, whereas the source sentence (sm-1-p… [2 notes] |
| 8 | `lem:wall-segment-stability` | `SM.wall_segment_stability` | SM.WallSegmentStability | reviews/lem-wall-segment-stability.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Nonzero directions are assumed only at the centre (hnz, Lean line 121) while the source's 'nonzero oriented segments' (… [6 notes] |
| 9 | `def:chamber` | `SM.chamber_definition` | SM.CyclicChambers | reviews/def-chamber.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); CyclicChambers.lean:156-157 gives the preimage explicitly as the union of the components of the n cyclic translates gen… [2 notes] |
| 10 | `prop:chambers` | `SM.chambers` | SM.ChamberPaths | reviews/prop-chambers.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Representation remark only (not a weakening of content): the order clause is phrased with the explicit Cramer formula e… [3 notes] |
| 11 | `def:gauss` | `SM.gauss_definition` | SM.GaussDefinition | reviews/def-gauss.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); The theorem additionally proves facts the printed definition only presupposes or that follow from lem:crossing-test: in… [3 notes] |
| 12 | `def:interlace` | `SM.interlacement_definition` | SM.InterlaceDefinition | reviews/def-interlace.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Aggregate clause 2 (InterlaceDefinition.lean:19-21) asserts the 'exactly one visit of y between the two visits of x' fo… [3 notes] |
| 13 | `def:visible` | `SM.visible_signature_definition` | SM.VisibleDefinition | reviews/def-visible.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Clause 4 (VisibleDefinition.lean:16): injectivity of the alphabet embedding Cycle (Crossing P) -> Cycle (Finset (ZMod n… [5 notes] |
| 14 | `def:weak` | `SM.weak_definition` | SM.WeakGeneric | reviews/def-weak.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Domain generality (benign): WeakGeneric, weakLocus, silentLocus, WeakTuple and WeakPolygon (WeakGeneric.lean:11-25, 92-… [7 notes] |
| 15 | `def:regular` | `SM.regular_definition` | SM.RegularDefinition | reviews/def-regular.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Clauses 5-6 (RegularDefinition.lean:22-23): Regular (shift a P) <-> Regular P and principalTurn (shift a P) i = princip… [2 notes] |
| 16 | `def:shift` | `SM.reversal_definition` | SM.Reversal | reviews/def-shift.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Reversal.lean:20-24 / 75-88: involutivity of reversal and of polygonReversal is proved and included in reversal_definit… [3 notes] |
| 17 | `lem:rot` | `SM.rotation_number` | SM.RotationTheorem | reviews/lem-rot.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Extra conjunct: cyclic-shift invariance ∀ a : ZMod n, rotationNumber (shift a P) = rotationNumber P (RotationTheorem.le… [4 notes] |
| 18 | `lem:uniformrot` | `SM.uniform_rotation` | SM.UniformRotation | reviews/lem-uniformrot.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); no notes |
| 19 | `lem:shift` | `SM.shift_reversal` | SM.ShiftTheorem | reviews/lem-shift.json | faithful | std | proved as printed on SM15 (clause (iii) with −z(P), clause (iv) on the regular locus); SM12 counterexample work/repairs/ShiftZeroTurn.lean documents the erratum (scope_issue/sm15_note in the map); cold-start review 2026-09-12 + countersignature |
| 20 | `def:admissible` | `SM.admissible_definition` | SM.Admissible | reviews/def-admissible.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); The vertex count n of GenericPolygon n is a natural number while the printed pair (n,r) lives in ℤ²; since admissibilit… [3 notes] |
| 21 | `lem:fibres` | `SM.nonempty_fibres` | SM.Fibres | reviews/lem-fibres.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); no notes |
| 22 | `def:germ` | `SM.wall_germ_definition` | SM.GermDefinition | reviews/def-germ.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); The theorem additionally asserts the labelled-side clause polygonProjection '' labelledSide b = side b (GermDefinition.… [2 notes] |
| 23 | `lem:triple-sides` | `SM.triple_sides` | SM.TripleSides | reviews/lem-triple-sides.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); The Lean witness additionally asserts δ ≤ g.radius (TripleSides.lean:89); this is a trivial bookkeeping conjunct, not a… [1 note] |
| 24 | `def:walls` | `SM.named_walls_definition` | SM.NamedWallsDefinition | reviews/def-walls.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); NamedWallsData proves the printed prose claims 'the types are mutually exclusive' (exclusivity, unique_kind) and 'the t… [4 notes] |
| 25 | `lem:flat-sides` | `SM.flat_sides` | SM.FlatSides | reviews/lem-flat-sides.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); FlatSidesData asserts Function.Injective g.center (all central vertices distinct); the source only proves this inside t… [6 notes] |
| 26 | `lem:wall-sides` | `SM.wall_sides` | SM.WallSides | reviews/lem-wall-sides.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Each branch supplies one common local radius delta (0<delta<=radius) for all its local clauses at once, and includes t=… [8 notes] |
| 27 | `lem:cusp-sides` | `SM.cusp_sides_of_continuous_curve` | SM.CuspCurve | reviews/lem-cusp-sides.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); side_laws, other_crossings, needle_turns, rotation_jump, loop_arc and empty_middle_edge are asserted for every side par… [5 notes] |
| 28 | `def:deletion-halves` | `SM.deletion_halves_definition` | SM.DeletionHalvesDefinition | reviews/def-deletion-halves.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); DeletionData records several immediate consequences the printed definition leaves implicit (fused closing edge P(j+1)-P… [3 notes] |
| 29 | `lem:children` | `SM.children` | SM.Children | reviews/lem-children.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); None. The extra hypotheses 3 ≤ k (both clauses) and the instance argument NeZero k are harmless: def:polygon already re… [4 notes] |
| 30 | `lem:transport-polynomials` | `SM.transport_polynomials` | SM.TransportPolynomials | reviews/lem-transport-polynomials.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); family_exact and one_per_name (TransportPolynomials.lean:17-20): the family is exactly the image of the name type and t… [6 notes] |
| 31 | `thm:relgp` | `SM.relative_general_position` | SM.RelativeGeneralPosition | reviews/thm-relgp.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); generic_endpoint_collar (RelativeGeneralPosition.lean:49-50): a positive generic collar at both endpoints is asserted;… [6 notes] |
| 32 | `def:root` | `SM.rootData` | SM.RootBoundary | reviews/def-root.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Cosmetic only, not a fidelity loss: `rootData` bundles the edge-vector function `edge` (ℓ_g = μ_{g+1} − μ_g, Polygon.le… [3 notes] |
| 33 | `def:gates` | `SM.gatesData` | SM.Gates | reviews/def-gates.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Lean gatesData (Gates.lean:99) is defined for every n with [NeZero n], not only n >= 3 as the source's polygons require… [2 notes] |
| 34 | `lem:gates-nonzero` | `SM.gates_nonzero` | SM.Gates | reviews/lem-gates-nonzero.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); no notes |
| 35 | `def:treesum` | `SM.treesumData` | SM.TreeCoefficient | reviews/def-treesum.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Harmless generality only: openTreeRec/rootedTreeRec (TreeCoefficient.lean:15-27) are defined over any CommRing with arb… [1 note] |
| 36 | `lem:treesum-trees` | `SM.treesum_trees` | SM.PlaneTreeFormal | reviews/lem-treesum-trees.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Conjunct 3 gives the specialization of the left-hand side (the recursion) only; the statement does not literally say th… [5 notes] |
| 37 | `prop:A-chamber` | `SM.A_chamber` | SM.TreeChamber | reviews/prop-A-chamber.json | faithful | std | handover review + countersignature 2026-09-13; SM15 "constant on every labelled chamber (the root fixed)" = the labelled-chamber conjunct of SM.A_chamber (re_review countersigned) |
| 38 | `def:nearfar` | `SM.nearfarData` | SM.NearFar | reviews/def-nearfar.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); geometricBoundaryArray is defined for every LabelledTuple n and root g : ZMod n, not only for polygons satisfying (G1)… [2 notes] |
| 39 | `lem:farout` | `SM.farout` | SM.Farout | reviews/lem-farout.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Farout.lean:15-20 — the inverse polynomials Psi have coefficients in R (depending on the fixed D, H); if 'polynomial in… [6 notes] |
| 40 | `thm:single-triple` | `SM.WallGerm.single_triple_wall_response` | SM.SingleTripleWallResponse | reviews/thm-single-triple.json | faithful | std | Formal only: d and the closeness radius δ (Lean 99) are quantified inside ∀ p ω x y z (Lean 93), so they may nominally depend on the chosen… [8 notes] |
| 41 | `def:induced-roots` | `SM.induced_roots_definition` | SM.InducedRootsDefinition | reviews/def-induced-roots.json | faithful | std | Uniqueness in the nonincident case (stmt 52) is asserted only for child edges whose ordered labels are (g, g+1); an edge of P∖j with labels… [6 notes] |
| 42 | `thm:A-S3` | `SM.WallGerm.flat_law_treeCoefficient` | SM.FlatLawTree | reviews/thm-A-S3.json | faithful | std | Conjunct 1 (statement line 29) asserts as a conclusion that exactly one punctured side is the right side (τ_j = -1 at every point) and the… [4 notes] |
| 43 | `thm:A-S4` | `SM.WallGerm.cusp_law_treeCoefficient` | SM.CuspLawTree | reviews/thm-A-S4.json | faithful | std | Lean conclusion (line 34) adds existence and uniqueness of the cusp case b (exactly one of the two printed betweenness placements holds); t… [4 notes] |
| 44 | `thm:A-S7` | `SM.WallGerm.vertex_edge_law_treeCoefficient` | SM.VertexEdgeLawTree | reviews/thm-A-S7.json | faithful | std | Statement line 30: `w.BigonAt M a ∨ w.SlidingAt M a` is asserted as a conclusion (the source only assumes 'of bigon or sliding type'; the d… [4 notes] |
| 45 | `thm:A-R3E` | `SM.WallGerm.triple_and_silent_laws_treeCoefficient` | SM.TripleSilentLawsTree | reviews/thm-A-R3E.json | faithful | std | Formal nuance only (equivalent, not a discrepancy): conclusions are asserted at every pair of labelled points (t on P_+, s on P_-) rather t… [1 note] |
| 46 | `def:soft` | `SM.softInsertion_definition` | SM.SoftInsertionDefinition | reviews/def-soft.json | faithful | std | labelling of P_ε pinned only through bijectivity and cyclic successor relations |
| 47 | `lem:soft-generic` | `SM.soft_family_generic` | SM.SoftGenericLemma | reviews/lem-soft-generic.json | faithful | std | All convergence statements (D_ε → v, inherited point and both parameters, newborn point) are two-sided Tendsto along 𝓝 0 on globally define… [9 notes] |
| 48 | `thm:A-soft` | `SM.SoftDuplication.soft_theorem_treeCoefficient` | SM.SoftTheoremTree | reviews/thm-A-soft.json | faithful | std | ε₀ is an arbitrary positive real (S31 `ε0 : ℝ`, `hε0 : 0 < ε0`), not only the constant of lem:soft-generic (source 1158-1159); the source s… [5 notes] |
| 49 | `prop:A-reversal` | `SM.treeCoefficient_reversal_shift_law` | SM.ReversalShiftLaw | reviews/prop-A-reversal.json | faithful | std | Statement line 14 requires the typeclass instance `[NeZero n]` in addition to `hn : 3 ≤ n` (line 19). Every n ≥ 3 is nonzero, so no case of… [2 notes] |
| 50 | `def:decomposition` | `SM.decomposition_definition` | SM.DecompositionDefinition | reviews/def-decomposition.json | faithful | std | Statement lines 36-38: descent of IsDecomposition along the cyclic relabelling (crossingSupportShift a S under generic_shift a P) is not st… [3 notes] |
| 51 | `def:smoothing` | `SM.smoothing_definition` | SM.SmoothingDefinition | reviews/def-smoothing.json | faithful | std | continuum traversal circle replaced by the finite marked circle (Mark P); cycles as successor orbits |
| 52 | `conv:selected-visits` | `SM.selected_visits_convention` | SM.SelectedVisitsConvention | reviews/conv-selected-visits.json | faithful | std | finite successor model of the source proof over the ported Carrier lane |
| 53 | `lem:carriers` | `SM.carriers_lemma` | SM.CarriersLemma | reviews/lem-carriers.json | faithful | std | (i) "independent of the order of reconnections" has no propositional counterpart (carriers defined directly as cycles) |
| 54 | `def:uniform` | `SM.uniform_definition` | SM.UniformDefinition | reviews/def-uniform.json | faithful | std | Domain: CarrierUniform, CarrierMixed, UniformDecomposition, carrierRotation, carrierLeftTurns are defined for every S : Finset (Crossing P)… [3 notes] |
| 55 | `def:positive-lift` | `SM.positive_lift_definition` | SM.PositiveLiftDefinition | reviews/def-positive-lift.json | faithful | std | Diagram is a labelled presentation (base vertex, component order) of the printed diagram; polygonal class (sm-3:337-343) |
| 56 | `def:gauss-record` | `SM.gauss_record_definition` | SM.GaussRecordDefinition | reviews/def-gauss-record.json | faithful | std | domain = polygonal generic diagrams (regular smooth immersions of the bridge paragraph not in the class) |
| 58 | `def:flat-carriers` | `SM.flat_carriers_definition` | SM.FlatCarriers | reviews/def-flat-carriers.json | faithful | std | non-blocking (STRONGER): common_gauss_word.1 (stmt 819-820) asserts equality of the linear Gauss LISTS cut at label 0 for the sides, beyond… [20 notes] |
| 59 | `cor:flat-carriers` | `SM.flat_carriers` | SM.FlatCarriers | reviews/cor-flat-carriers.json | faithful | std | non-blocking (STRONGER): centre_turn_signs (stmt 1220-1223) adds a conclusion absent from printed clause (ii) (which speaks only of 'both s… [16 notes] |
| m60 | `lit:homfly` | `SM.lit_homfly` | SM.LinkInterfaces | reviews/lit-homfly.json | faithful | std+H | polygonal Diagram domain (def:positive-lift reading); planar isotopy = EqvGen(Reparam ∨ Deform); descent over LinkEquiv (D2); skein triples = switch-and-smooth (D3) |
| m61 | `lp:lm` | `SM.lp_lm` | SM.LinkInterfaces | reviews/lp-lm.json | faithful | std+LM | ∃-form for "the function constructed in LM §1"; witness lmF pinned by lp:lm-uniqueness; polygonal domain |
| m62 | `lp:lm-uniqueness` | `SM.lp_lm_uniqueness` | SM.LinkInterfaces | reviews/lp-lm-uniqueness.json | faithful | std+LM+LMU | competitor hypothesis Q = 1 on every crossing-free one-component polygon (formally stronger hypothesis, no effect) |
| 60 | `lp:coefficient-transport` | `SM.coefficient_transport` | SM.CoefficientTransport | reviews/lp-coefficient-transport.json | faithful | std+LM+LMU | non-blocking: S5 'the crossing-free circle' (singular) is rendered as 'every one-component crossing-free diagram' (`Diagram.IsCrossingFreeC… [2 notes] |
| 61 | `lp:core` | `SM.lp_core` | SM.PolynomialBlock | reviews/lp-core.json | faithful | std+H+LM+LMU | non-blocking: `gaussian` (stmt 1161) states the evaluation via the proof's eq. lp:gaussian (φ(l) = ia, φ(m) = −iz, sm-3:1067-1069); the the… [6 notes] |
| 62 | `lp:split-circle` | `SM.split_circle` | SM.PolynomialBlock | reviews/lp-split-circle.json | faithful | std+LM | non-blocking: the hypothesis `IsSplitCircleAddition D D'` requires only that the restriction of D' to the components other than the added c… [2 notes] |
| 63 | `rp:record-polynomial` | `SM.record_polynomial` | SM.PolynomialBlock | reviews/rp-record-polynomial.json | faithful | std+LM | `coeff_eq` (stmt 1151-1152): the coefficient clause is stated only for the Gaussian evaluation P (coefficients a^d z^k of reMap(φ(F_D)) ∈ R… [8 notes] |
| 64 | `lc:presentations` | `SM.presentations` | SM.PolynomialBlock | reviews/lc-presentations.json | faithful | std+LM | non-blocking: the illustrative instance list (page-chart changes, crossing-free replacements, compatible height choices; excerpt lines 6-9)… [6 notes] |
| 65 | `lc:single-crossing` | `SM.single_crossing` | SM.SingleCrossing | reviews/lc-single-crossing.json | faithful | std+LM | non-blocking: the conclusion `P D = 1` = `reMap (phi (T.toTG (lmF D))) = 1` does not by itself assert `imMap (phi (T.toTG (lmF D))) = 0`; t… [2 notes] |
| 66 | `mp:join` | `SM.join` | SM.MarkedProducts | reviews/mp-join.json | faithful | std+LM | labels D9; non-blocking: `MarkedDiagram.μ` (statement l.149) is data with no printed counterpart; it is fully determined by (D, I) through `comp_eq` +… [8 notes] |
| 67 | `mp:stack` | `SM.stack` | SM.Stack | reviews/mp-stack.json | faithful | std+LM | non-blocking: block tags are 0..q-1 (`Fin q`) where the print writes 1..q; the relabelling is order-preserving so "smaller-index block" is… [4 notes] |
| 68 | `mp:zero-link` | `SM.zero_link` | SM.ZeroLink | reviews/mp-zero-link.json | faithful | std | Applies only to polygonal diagrams (`Diagram` = generic `Shadow` of closed polygons with k ≥ 3 vertices, `Regular` components, `tail_off`),… [7 notes] |
| 69 | `mp:lowest` | `SM.lowest` | SM.MarkedProducts | reviews/mp-lowest.json | faithful | std+LM | non-blocking: `two_component_row` (stmt 379-382) renders the printed remark "For c = 2 this is the two-component mixed row …" (excerpt l.12… [3 notes] |
| 70 | `mp:blocks` | `SM.blocks` | SM.MarkedProducts | reviews/mp-blocks.json | faithful | std+LM | D9: clean marked join = RecordIso to joinRecord; sign_preserved as an abstract bijection; realizes clause kept and proved |
| 71 | `def:C` | `SM.corner_state_sum_definition` | SM.CornerStateSum | reviews/def-C.json | faithful | std+H | non-blocking: cornerSlot and carrierRotationInt (S:61-63, 82-84) are total in S — they have values (round of a possibly non-integer carrier… [9 notes] |
| 72 | `lem:C-X1` | `SM.C_X1` | SM.CX1 | reviews/lem-C-X1.json | faithful | std+H | non-blocking: `carrierWeight`, `wind` and the fields weight_right / weight_left / weight_mixed / wind_eq (St:22-31, 36-51) are stated for e… [7 notes] |
| 73 | `ng:front-domain` | `SM.front_domain_definition` | SM.FrontSmooth | reviews/ng-front-domain.json | faithful | std | FR-1 polygonal reading of S(F) (S is a Diagram carrying the Marking of the rounded curve G); FR-2 cusp criterion in derivative form; FR-3/FR-4 smooth = C^∞, 1-periodic parameter circles |
| 74 | `ng:smoothing-record` | `SM.ng_smoothing_record` | SM.FrontRecordBridge | reviews/ng-smoothing-record.json | faithful | std+LM | FR-1/D-F6: IsRounding S does not tie S to the rounded curves G; printed content kernel-checked as library thm SM/FrontGeomModel.lean isRounding_of_geomModel (cited, not a row) |
| 75 | `def:adeg` | `SM.adeg_definition` | SM.AdegDefinition | reviews/def-adeg.json | faithful | std | Field `domain` (statement line 26) asserts IsDomain R for the whole ring R = ℤ[a^{±1},z^{±1}]; the source (line 1889) only calls the coeffi… [3 notes] |
| 76 | `ng:commutation` | `SM.ng_commutation` | SM.FrontRowsW2S | reviews/ng-commutation.json | faithful | std+LM | labels FR-10, FR-16, FR-5, FR-8, FR-9; deform_*: only jointly C^∞ families (fixed circle indexing, fixed 1-periodic parametrizations) on [0,1] × ℝ count as 'deformations through… [13 notes] |
| 77 | `ng:front-I` | `SM.ng_front_I` | SM.FrontRowsW3 | reviews/ng-front-I.json | faithful | std+LM | labels FR-1, FR-16, FR-6, FR-8; Class: the Lean row holds for PL realizations of closed oriented Rutherford words (SM.realize : OWord → PLFront), not for arbitrary fronts… [5 notes] |
| 78 | `ng:front-II` | `SM.ng_front_II` | SM.FrontRowsW3b | reviews/ng-front-II.json | faithful | std+LM | labels FR-1, FR-16, FR-5, FR-8; Class narrowing (disclosed FR-8/FR-5): the printed 'front type-II moves' act on fronts of ng:front-domain; the Lean fields quantify only ov… [3 notes] |
| 79 | `ng:front-III` | `SM.ng_front_III` | SM.FrontRowsW3 | reviews/ng-front-III.json | faithful | std+LM | labels FR-1, FR-16, FR-8; Class narrowing (FR-8, disclosed): only realizations of closed oriented words, not arbitrary fronts of ng:front-domain; closed by the accep… [7 notes] |
| 80 | `ng:deletions` | `SM.ng_deletions` | SM.FrontRowsW3 | reviews/ng-deletions.json | faithful | std+LM | labels FR-1, FR-13, FR-16, FR-6, FR-8; Class reading FR-8 (disclosed, judged non-blocking): stated on standard realizations of closed oriented words whose letters contain the del… [8 notes] |
| 81 | `ng:circle` | `SM.ng_circle` | SM.FrontRowsW2 | reviews/ng-circle.json | faithful | std+LM | FR-8 class narrowing: sentence 1 on realizations of closed oriented Rutherford words (SM.realize), sentence 2 on PLFront (FR-11); FR-5 word layer is the printed certificate device |
| 82 | `ng:cusp-skein` | `SM.ng_cusp_skein` | SM.FrontRowsW2 | reviews/ng-cusp-skein.json | faithful | std+LM | FR-8 stated on SM.realize of closed oriented words; FR-12 unique compatible smoothing as a theorem, right-cusp templates outside the row |
| m86 | `ng:finite-word` | `SM.ng_finite_word` | SM.FrontInterfaces | reviews/ng-finite-word.json | faithful | std+NG | literature axiom stated on closed oriented words (FR-6): PrincipalChain stop rule as a consequence of Laws; empty word included (trivial) |
| 83 | `ng:local-front-bound` | `SM.ng_local_front_bound` | SM.FrontRowsW3b | reviews/ng-local-front-bound.json | faithful | std+LM+NG | labels FR-1, FR-16, FR-NB-4; The theorem is conditional on `F.IsRounding S` and asserts nothing about the existence of a rounding: for a front F with no Lean-rounding t… [3 notes] |
| 84 | `fd:transverse-neighborhood` | `SM.fd_transverse_neighborhood` | SM.TransverseNeighborhood | reviews/fd-transverse-neighborhood.json | faithful | std | FR-TN-3 no smoothness field for h (forced); FR-TN-5 TransverselyIsotopic endpoints; one false internal leaf repaired without statement change |
| 85 | `fd:parameter-avoidance` | `SM.fd_parameter_avoidance` | SM.ParameterAvoidance | reviews/fd-parameter-avoidance.json | faithful | std | FR-PA-1 K compact in EuclideanSpace ℝ (Fin d), not an abstract manifold |
| 86 | `fd:contact-motions` | `SM.fd_contact_motions` | SM.ContactMotions | reviews/fd-contact-motions.json | faithful | std | SmoothDependence proved inside the module (D-F13 superseded); unconditional |
| 87 | `fd:generic-front` | `SM.fd_generic_front` | SM.GenericFront | reviews/fd-generic-front.json | faithful | std | D-F15 compact support inside IsContactIsotopy = disclosed strengthening; FR-GF-1..8 |
| 88 | `fd:linking-calculus` | `SM.fd_linking_calculus` | SM.LinkingCalculusRow | reviews/fd-linking-calculus.json | faithful | std | D-F16 restated unconditionally (RegularPoleCount proved); framing pushoff embeddedness not asserted (printed sentence claims disjointness only) |
| 89 | `ce:rounding` | `SM.ce_rounding` | SM.CeRounding | reviews/ce-rounding.json | faithful | std | CE-R1 diagram = RegularGenericProjection (no polygonal Diagram delivered); CE-R2 ℝ-indexed SpatialFamily via the smoothTransition time clamp; CE-R4 construction constants differ (statement unaffected) |
| 90 | `ce:smoothing-record` | `SM.ce_smoothing_record` | SM.CeSmoothingRecord | reviews/ce-smoothing-record.json | faithful | std+LM | D-1 collar field on CleanCuspSmoothing; K-3 D_ε fields quantify over CuspRoundingFamily; K-5 clean neighbourhood convex (IsDisc); FR-1 polygonal reading |
| 91 | `cp:finite-contact-path` | `SM.cp_finite_contact_path` | SM.ContactPath | reviews/cp-finite-contact-path-row.json | faithful | std+H+HD+LM+LMU | labels D-GAP2-3, FR-CP-1/5/7/9, FR-LHD-1, K-5; `:= cp_finite_contact_path_of_descent lit_homfly_descent` (statement = the `ContactPathData` reviewed 2026-09-14, unchanged); WEAKER: the supplied family is an ℝ-indexed `SpatialFamily` (printed [0,1]; FR-CP-5) and both end diagrams enter through polygonal `HeightMarking` readings with no existence of a reading asserted (FR-CP-1); STRONGER (proof side): the axiom consumed bundles the isotopy-extension step the printed proof performs by hand (FR-LHD-1); citation nit: the consumed descent sentence is at sm-3:3310-3312 and the hand isotopy-extension at 3276-3312 where docstrings say 3313-3316 / 3264-3313 [14 notes] |
| 92 | `def:transverse-front` | `SM.transverse_front_definition` | SM.TransverseFront | reviews/def-transverse-front.json | faithful | std | contact space, C^∞ 1-periodic embedded loops, z′ − y x′ > 0; RegularGenericProjection is "the diagram" (GAP-1: no polygonal record built here) |
| m97 | `src:contact` | `SM.src_contact` | SM.SrcContact | reviews/src-contact.json | faithful | std+SC | labels D-SC-1..6, FR-SC-1..11; `axiom src_contact : ∃ r tb : (ℝ → E3) → ℝ, SrcContactClauses r tb` — ∃-form over the literature's r, tb (never defined by the document) with exactly the four printed formulas as fields (FR-SC-1; equivalence with the substituted consequence proved, `src_contact_iff_consequence`, standard axioms); WEAKER: the Legendrian formulas hold for KNOTS (`F.c = 1`) whose front is on ng:front-domain's class (FR-SC-2); `T₊(L)` = every positive circle of every `IsPushoffAnnulus` (FR-SC-3); r, tb, sl ℝ-valued (FR-SC-10); integrality of sl not asserted (a consequence) [9 notes] |
| 93 | `fd:ng-bound` | `SM.fd_ng_bound` | SM.NgBound | reviews/fd-ng-bound.json | faithful | std+LM+NG | labels FR-1, FR-NB-1, FR-NB-2, FR-NB-3, FR-NB-4; [presuppositional, non-blocking] The Lean row does not assert that a front admits a rounding (no existence clause); if some SmoothFront had… [8 notes] |
| 94 | `fd:contact` | `SM.fd_contact` | SM.FdContactUnits | reviews/fd-contact.json | faithful | 9 | labels D-SC-3, FR-FC-1..3, FR-SC-4/9/10; `:= fd_contact_of_units …` (eleven unit theorems, each standard axioms only); sentence 1 (the over/sign rule) rendered on def:transverse-front's class where it is definitional (FR-FC-3); STRONGER: `representative_bound` for EVERY polygonal reading X of D_T; WEAKER: conditional on `Nonempty (HeightMarking …)`, no existence of a reading asserted (FR-FC-1, the FR-1 convention; row 91 reads its endpoint identically); `degAZ 0 = 0` and `slCircle` off-class default never exercised; `sl` ℝ-valued, casts [10 notes] |
| 95 | `cf:def-turning` | `SM.turning_definition` | SM.TurningNumber | reviews/cf-def-turning.json | faithful | std | non-blocking: `IsSeamLift` (stmt 124-125) fixes the seam at parameter 0, whereas the printed lift is 'at a seam' (any cut point of ℝ/ℤ). Co… [19 notes] |
| 96 | `cf:lem-turnlift` | `SM.turnlift` | SM.TurnLift | reviews/cf-lem-turnlift.json | faithful | std | `3 ≤ n` hypothesis on the (ii) fields and `rounding` (571, 574, 579, 584, 588, 596) — not printed, but implied by `Regular P`, so vacuous (… [19 notes] |
| 97 | `cf:lem-rounding` | `SM.cf_lem_rounding` | SM.Rounding | reviews/cf-lem-rounding.json | faithful | std | FR-R1 D_ε = polygonal D carried by the smooth curve (Carried record); FR-R3 no_triple via PolygonDiagram.generic; FR-R4 period-1 parameter; witness exports more than printed |
| 98 | `cf:lem-curl` | `SM.cf_lem_curl` | SM.Curl | reviews/cf-lem-curl.json | faithful | std+LM | FR-C1 record-level carrying (RecordCarried, no τ_eval at the kink); FR-C2 disc inside any preassigned neighbourhood (stronger); FR-C4 P_{F'} = P_F via polygonal RI |
| 99 | `cf:thm-carrierfloor` | `SM.cf_thm_carrierfloor` | SM.CarrierFloorRows | reviews/cf-thm-carrierfloor.json | faithful | 9 | labels D-FL-1..4, FR-FL-R1..R3, A1..A2, B1..B5, C1..C9; `:= cf_thm_carrierfloor_of_bound transverseFrontBound` (row 94 enters as the sl-free composite `TransverseFrontBound`, FR-FL-C9); (B) is stated for the NORMALISED orientation (`C` or `C.reverse` with `D.reverse`) — a refuter confirmed the literal claim is false for an all-negative L, the printed proof's WLOG is the only true reading (FR-FL-B1); STRONGER: `junction_determined` fixes the parametrisation (FR-FL-A1), the (R) fields hold for every link diagram / every C¹ regular curve, `BClaim` adds `ε₁ ≤ clearance C`, (C) `floor` unconditional on `P X` (`P_ne_zero`); the printed mirror D̄ is the crossing switch (`Diagram.switchAll`), not `Diagram.mirror` (FR-FL-C4) [15 notes] |
| 100 | `thm:floor` | `SM.thm_floor` | SM.CarrierFloorRows | reviews/thm-floor.json | faithful | 9 | labels FR-FL-F1..F3; `:= thm_floor_of_bound transverseFrontBound`; "exactly one turn is right" rendered as "one right AND every other left" (`AllLeftOrOneRight`, the literal reversal form; equivalent because carrier turns are nonzero, lem:carriers (ii)); STRONGER: `a_floor` stated twice — in ℤ with def:C's `cornerSlot` and in ℝ with the real `carrierRotation`; `z_parity` (`InSupportM 1`, `0 ≤ mindegZZ`) with no turn hypothesis (FR-FL-F3); `mindegAZ 0 = 0` convention [7 notes] |
| 101 | `cb:blocks` | `SM.cb_blocks_definition` | SM.CBBlocks | reviews/cb-blocks.json | faithful | std+H+LM+LMU | R-1..R-12: SM block = accepted CV.Piece; owner defined via a fixed visit and pinned; hn : 3 ≤ n bundle parameter |
| 102 | `cb:products` | `SM.cb_products` | SM.CBProducts | reviews/cb-products.json | faithful | std+LM | R-4/R-5: D_H = positiveLift of a carrier of an independent refinement; P_H = recordPolynomial of the restricted record |
| 103 | `cb:singleton` | `SM.cb_singleton` | SM.CBSingleton | reviews/cb-singleton.json | faithful | 9 | labels D-CC-1..5, FR-CC-1..3; `:= cb_singleton_of_floor thm_floor`; one field `isolated_zero`: "interlaces no other self-crossing" is `Interlaces` of G_P (def:interlace, the graph the printed proof uses), not the record interlacement of D_A (FR-CC-1); proof route bounds `mindegAZ` of the full product instead of the printed `[z⁰]` rows (FR-CC-3); all three reviewer arrays empty [0 notes] |
| 104 | `cb:embedded-rotation` | `SM.cb_embedded_rotation` | SM.EmbeddedRotation | reviews/cb-embedded-rotation.json | faithful | std | D-ER1 proved independently of deferred row 57; FR-ER-2 sign read at supporting vertices (bounded region not defined); Embedded P wider than generic m = 0 |
| 105 | `lem:corner-values` | `SM.corner_values` | SM.CornerValues | reviews/lem-corner-values.json | faithful | 9 | labels FR-CC-4..6; `:= corner_values_of_floor thm_floor`; (i) the hypothesis "embedded (m_Q = 0)" is rendered by the printed gloss `carrierCrossingCount = 0` only — at most a weaker hypothesis, so the statement is at least as strong (FR-CC-4); `\|r_Q\| = 1` for the REAL `carrierRotation`, the integer form as the proved companion `embedded_rotationInt` (FR-CC-5); `d_Q = 0` in ℤ through `cornerSlot`; (ii) literally row 103's clause at (Q, y) with the redundant guard `y' ≠ y`; "uniform" kept literally though the proof does not use it [6 notes] |
| 106 | `prop:C-chamber` | `SM.prop_C_chamber` | SM.CChamber | reviews/prop-C-chamber.json | faithful | std+H | quantified over labelled representatives with polygonProjection Q ∈ chamber (polygonProjection P); entails cyclic-relabelling invariance (printed content made explicit) |
| 107 | `prop:C-silent` | `SM.prop_C_silent` | SM.CSilent | reviews/prop-C-silent.json | faithful | std+H | design B/R2 hybrid (work/drafts/csilent/PLAN_FINAL.md); exterior-extension (E) and pure-cut (C) walls as printed |
| 108 | `thm:C-S3` | `SM.thm_C_S3` | SM.CS3 | reviews/thm-C-S3.json | faithful | std+H | side values below an existential δ with τ_j = ∓1 over both Booleans (equivalent to chamber values by def:germ + prop:C-chamber); n ≥ 4 via N = n+1 |
| 109 | `lem:homflyrows` | `SM.homflyrows` | SM.MarkedProducts | reviews/lem-homflyrows.json | faithful | std+H+LM+LMU | labels D2, D9; The well-definedness of K#J and K⊔J as LinkEquiv classes (that all realizations are link-equivalent) is not stated (docstring 439); the pri… [12 notes] |
| 110 | `thm:C-S7` | `SM.thm_C_S7` | SM.CS7 | reviews/thm-C-S7.json | faithful | 9 | labels D-CC-1, FR-CC-7..10, A-110-1, A-110-2; accepted 2026-09-19 13:26Z; `:= thm_C_S7_of_floor thm_floor` (SM/CS7.lean; units SM/CS7Units.lean, 27 000 lines, ported from work/drafts/corner/W6_Assembled_B.lean after corner waves 4-6); the fixed `CS7Data.vertex_edge_law` of the accepted SM/CornerChainStatements.lean, both bigon branches and the sliding branch, actual children λ₁ λ₂, sign `s = g.contactSign M a`; NON-BLOCKING: the identity at every pair of side parameters (tp, tm) rather than the two chamber values (equivalent by prop:C-chamber), the halves' genericity proofs universally quantified (FR-CC-9), `VertexEdgeAt` = bigon ∨ sliding as a description not a hypothesis (FR-CC-7) [9 notes] |
| 111 | `thm:C-S5` | `SM.thm_C_S5` | SM.CS5 | reviews/thm-C-S5.json | faithful | std+H | conclusion on the germ's own no-loop side points P(t), t in the side interval (chamber values via prop:C-chamber) |
| 112 | `thm:C-soft` | `SM.thm_C_soft` | SM.CSoft | reviews/thm-C-soft.json | faithful | 9 | labels FR-CC-11..13; the fixed target name, `:= thm_C_soft_of_floor thm_floor` — the fifth target theorem; the genericity of P_ε is QUANTIFIED (`∀ hQ : Generic (softInsertion P j q ε)`, the consumer's `UniquenessHypotheses.soft` shape) rather than asserted, the accepted thm:A-soft's `∃ hQ` form being the proved companion `CSoftData.exists_generic` (FR-CC-12; the one "weaker" entry); the identity read in ℚ with `softAmplitudeMultiplier = (χ₋+χ₊)/2`, ℤ companion `doubled` (FR-CC-11); C on labelled tuples, the quotient descent is the consumer's business (FR-CC-13) [7 notes] |
| m118 | `hyp:R` | `SM.hyp_R` | SM.HypR | reviews/hyp-R.json | faithful | std+H | labels FR-HR-1, FR-HR-3, FR-HR-4, GAP-2; Non-blocking (FR-HR-3): the binder hn : 3 ≤ n (statement file :84) restricts to n ≥ 3, which the printed sentence does not state; it is the… [3 notes] |
| 113 | `def:star` | `SM.star_definition` | SM.StarDefinition | reviews/def-star.json | faithful | std | none disclosed (arrays empty) |
| 114 | `lem:star-generic` | `SM.star_generic_law` | SM.StarGenericLaw | reviews/lem-star-generic.json | faithful | std | Clause (ii) tangency (statement lines 29–32) is rendered by two independently sufficient characterizations at once — orthogonality of the e… [2 notes] |
| 115 | `lem:transport-lengths` | `SM.transport_lengths_law` | SM.TransportLengthsLaw | reviews/lem-transport-lengths.json | faithful | std | Nominal only: hab : a ≤ b (L19) excludes a > b, i.e. the empty Icc a b; the source's "compact interval" (S4) is a nonempty [a,b] (its proof… [3 notes] |
| 116 | `lem:transport-angle-interval` | `SM.transport_angle_interval_law` | SM.TransportAngleIntervalLaw | reviews/lem-transport-angle-interval.json | faithful | std | Statement line 20: the conjunct ∀ i, unitDir (θ i) = (Real.cos (θ i), Real.sin (θ i)) is an extra, definitionally true clause pinning the n… [4 notes] |
| 117 | `thm:mycyclic` | `SM.mycyclic` | SM.MycyclicTheorem | reviews/thm-mycyclic.json | faithful | std | orbit_fibre_pathConnected (statement L48-51): Mathlib IsPathConnected includes nonemptiness (∃ x ∈ F), so the Lean also asserts the orbit f… [4 notes] |
| 118 | `lem:transport` | `SM.transport_lemma` | SM.TransportLemma | reviews/lem-transport.json | faithful | std | Piecewise-affine is rendered as affine on the closed cells of a uniform mesh of [0,1] (statement lines 34-35), a special case of a general… [3 notes] |
| 119 | `lem:soft-rotation` | `SM.soft_rotation_law` | SM.SoftRotationLaw | reviews/lem-soft-rotation.json | faithful | std | Nuance, not a discrepancy: the Lean's threshold ε₀ (stmt l.20) is its own existential and is not identified with the ε₀ of lem:soft-generic… [3 notes] |
| 120 | `def:anchors` | `SM.anchors_definition` | SM.AnchorsDefinition | reviews/def-anchors.json | faithful | std | bound_spec (statement lines 57-61, data clause lines 166-172) requires all P_ε, 0 < ε < ε₀, to lie in one LABELLED chamber (connectedCompon… [2 notes] |
| 121 | `prop:anchors-exist` | `SM.anchors_exist` | SM.Anchors | reviews/prop-anchors-exist.json | faithful | std | Conjunct 5 (statement 152-154) omits the case-(Z) hypothesis `Admissible (m : ℤ) r` (source 404-405 says 'in case (Z)'; def:anchors 376): i… [5 notes] |
| 122 | `prop:anchor-values` | `SM.prop_anchor_values` | SM.AnchorValuesRow | reviews/prop-anchor-values.json | faithful | 9 | labels D-CM-1, FR-CM-1..5, FR-CM-3′; `:= anchor_values_of thm_C_soft`; F restricted to ℤ-valued functions `∀ n [NeZero n], GenericPolygon n → ℤ` (FR-CM-1, thm:uniqueness's reading; the one "weaker" entry); STRONGER: the anchor clauses quantify over every `ZeroAnchor`/`LoopAnchor`/`LoopAnchorZero` WITHOUT def:anchors' case conditions — a kernel-proved superset (FR-CM-3′); `loopZero_turn` asserts BOTH readings of "orientation sign of the parent triangle" (common turn sign and rotation number, FR-CM-3); `A_loop`/`A_loopZero` assert `∃!` parent root; `rotationNumber` is ℝ-valued so the (L₀) clause is an equation in ℝ after casting; `cornerPolygon = 0` below arity 3, unreachable (FR-CM-5) [8 notes] |
| 123 | `lem:A-small-values` | `SM.A_small_values_lemma` | SM.SmallValuesLemma | reviews/lem-A-small-values.json | faithful | std | Statement line 20: the conjunct `τ ≠ 0` is not in the printed sentence (source line 3-4 says only 'all turns have a common sign τ'). It is… [1 note] |
| 124 | `thm:root-indep-proof` | `SM.root_independence` | SM.RootIndependence | reviews/thm-root-indep-proof.json | faithful | std | none disclosed (arrays empty) |
| 125 | `cor:A-lawful` | `SM.A_lawful` | SM.ALawful | reviews/cor-A-lawful.json | faithful | std | flat_law (stmt 65-73) asserts Generic (deleteVertex w.center j), whereas thm:A-S3 (sm-2 401-409) states only (G1) of the deletion and the c… [7 notes] |
| 126 | `thm:uniqueness` | `SM.uniqueness` | SM.Uniqueness | reviews/thm-uniqueness.json | faithful | std | formally weaker-or-equal hypotheses (theorem at least as strong) |
| 127 | `thm:comparison` | `SM.thm_comparison` | SM.ComparisonRows | reviews/thm-comparison.json | faithful | 9 | labels D-CM-2, FR-CM-7, FR-CM-14, FR-CM-17; accepted 2026-09-19 13:26Z; `thm_comparison (hR : hyp_R) : ∀ n [NeZero n] hn P hP, cornerStateSum hn hP = amplitude P hP.1 hn := thm_comparison_of hR thm_C_S7 thm_C_soft` (SM/ComparisonRows.lean); hyp:R the EXPLICIT parameter (policy mode `explicit_parameter`) — the only accepted row, with 128, that takes `hR`; NON-BLOCKING (neutral): labelled generic tuples `P : LabelledTuple n`, `hP : Generic P` instead of polygon classes (both sides descend), A(P) rendered at root 0 (`amplitude`, root independence accepted) [4 notes] |
| 128 | `cor:C-inherits` | `SM.cor_C_inherits` | SM.ComparisonRows | reviews/cor-C-inherits.json | faithful | 9 | labels D-CM-3, D-CM-4, FR-CM-8, FR-CM-9, FR-CM-9′, FR-CM-13, FR-CM-15; accepted 2026-09-19 13:26Z; `cor_C_inherits (hR : hyp_R) : CInheritsData := cor_C_inherits_of hR thm_C_S7 thm_C_soft` (SM/ComparisonRows.lean; the 12-field `SM.CInheritsData` of SM/CInherits.lean); the (G1) deletion at a simple cusp wall generic by `cusp_deletion_generic`, threaded cusps included, no emptiness hypothesis; STRONGER: the extra field `root_values` (C(P) = A_g(P) for every root g), the κ rotation clause of `CuspLawC`, both chamber notions (inherited from the accepted `ALawfulData`) [11 notes] |
| 129 | `CV:def:polygon` | `CV.polygon_definition` | CV.Setup | reviews/cv-def-polygon.json | faithful | std | Domain extension only (non-blocking): CV.IsPolygon (stmt 47) is defined for every n : ℕ, including n = 0, 1, 2 where the print (d1_setup.te… [1 note] |
| 130 | `CV:def:regular` | `CV.regular_definition` | CV.Setup | reviews/cv-def-regular.json | faithful | std | The explanatory sub-clause 'where the two candidate values ±π are both excluded from the open interval' (source 32-33) is rendered only by… [6 notes] |
| 131 | `CV:def:guarded` | `CV.guarded_definition` | CV.Setup | reviews/cv-def-guarded.json | faithful | std | "real polynomial functions" (tex 43): the bundle records only `continuous` (S 988) and `finite` (S 987); polynomiality is not stated as a f… [9 notes] |
| 132 | `CV:def:generic` | `CV.generic_definition` | CV.Setup | reviews/cv-def-generic.json | faithful | std | The alternative wording of prop:fidelity (i), 'equivalently every remote pair whose relative interiors meet has nonzero direction determina… [7 notes] |
| 133 | `CV:def:diagrammatic` | `CV.diagrammatic_definition` | CV.Setup | reviews/cv-def-diagrammatic.json | faithful | std | The hexagon non-example of 320-325 and the printed remark that 'the clause about preimages and shared images is not implied by the others'… [7 notes] |
| 134 | `CV:def:interlace` | `CV.interlace_definition` | CV.Events | reviews/cv-def-interlace.json | faithful | std | non-blocking: the bundle is stated for `hP : CrossingGeometry P` (statement file 274, 318) while the printed row fixes a diagrammatic polyg… [8 notes] |
| 135 | `CV:def:smoothing` | `CV.smoothing_definition` | CV.Carriers | reviews/cv-def-smoothing.json | faithful | std | "do not cross" (d1:358): `noncrossing_arcs` is a determinant-sign identity plus a repeat of transversality; no field asserts non-crossing o… [15 notes] |
| 136 | `CV:lem:carriers` | `CV.carriers` | CV.CarriersLemma | reviews/cv-lem-carriers.json | faithful | std | (ii) ranges over marked points of Γ only (finite carrier model); double points via accepted def:interlace |
| 137 | `CV:lem:carrierword` | `CV.carrierword` | CV.CarrierWord | reviews/cv-lem-carrierword.json | faithful | std | binder NARROWED to diagrammatic polygons and iterated carriers (round-2 unanimous; content-preserving on every instance the source uses) |
| 138 | `CV:def:wind` | `CV.wind_definition` | CV.Carriers | reviews/cv-def-wind.json | faithful | std | The count '\|S\|+1 carriers' (exc. 22-23) is not asserted anywhere in the bundle (deferred to lem:carriers (i), row 136) — non-blocking, a ci… [13 notes] |
| 139 | `CV:def:pieces` | `CV.pieces_definition` | CV.Carriers | reviews/cv-def-pieces.json | faithful | std | non-blocking: fields `pieces_nonempty` (l.762-764), `pieces_disjoint` (l.766-767), `pieces_cover` (l.769-771) have no literal printed sente… [9 notes] |
| 140 | `CV:def:record` | `CV.record_definition` | CV.RecordHomfly | reviews/cv-def-record.json | faithful | std | non-blocking: the oriented circle Γ itself is not part of the Lean record; only the cyclic successor on V (S130, S352). [15 notes] |
| 141 | `CV:def:homfly` | `CV.homfly_definition` | CV.RecordHomfly | reviews/cv-def-homfly.json | faithful | std+H+LM+LMU | non-blocking: the derivation sentence 'obtained by applying the skein relation at a crossing between L and a split unknot' (d1_setup 554-55… [11 notes] |
| 142 | `CV:def:piecediagram` | `CV.piecediagram_definition` | CV.PieceCurve | reviews/cv-def-piecediagram.json | faithful | std+H | `erased` (stmt 626-630): the double-point clause is `Nonempty (Crossing ≃ H)` = equal cardinality only; the printed 'every double point out… [12 notes] |
| 143 | `CV:lem:piececurve` | `CV.piececurve` | CV.PieceCurve | reviews/cv-lem-piececurve.json | faithful | std | Formally only: the bundle requires hn : 3 ≤ n (statement 637), absent from d1:594; CV polygons have n ≥ 3 by def:polygon, so no printed cas… [19 notes] |
| 144 | `CV:def:rot` | `CV.rot_definition_full` | CV.RotationSmooth | reviews/cv-def-rot.json | faithful | std | non-blocking: the intermediate claims of the printed 'Why regularity is part of the definition' argument (d1_setup 748-762: deletion of a f… [17 notes] |
| 145 | `CV:lem:turnlift` | `CV.turnlift_full` | CV.TurnLift | reviews/cv-lem-turnlift.json | faithful | std | non-blocking: polygon_ray_independent (statement 118-120) is not a sentence of the lemma; it is def:rot 744-745 ('the sum is independent of… [18 notes] |
| 146 | `CV:def:X1` | `CV.X1_definition` | CV.X1 | reviews/cv-def-X1.json | faithful | std+H+LM+LMU | The normalising identities of def:homfly (P(○) = 1, skein) are not restated in this bundle (they live in row 142's piece_polynomial and in… [11 notes] |
| 147 | `CV:prop:chamberinv` | `CV.chamberinv` | CV.ChamberInvRow | reviews/cv-prop-chamberinv.json | faithful | std+H+LM+LMU | Non-blocking: clause-(i) fields (stmt 66, 68, 71) are stated for every n with [NeZero n] rather than under the printed "Fix n >= 3" (src 93… [6 notes] |
| 148 | `CV:def:event` | `CV.event_definition` | CV.Events | reviews/cv-def-event.json | faithful | std | The cusp position clause p_1(0) ∉ [p_0, p_2] implicit in the word 'cusp' is not a field of `EventExampleData` (only the docstring, stmt 633… [13 notes] |
| 149 | `CV:lem:guardconst` | `CV.guardconst` | CV.Events | reviews/cv-lem-guardconst.json | faithful | std | Domain in n: `Event (n) [NeZero n]` (reviewer 332) admits n = 1, 2, whereas the printed def:polygon (d1_setup.tex 8-9) fixes n ≥ 3; the Lea… [2 notes] |
| 150 | `CV:def:silent` | `CV.silent_definition` | CV.Events | reviews/cv-def-silent.json | faithful | std | non-blocking (documentation only): the module header (input lines 8, 19-21) and the Row 150 section comment (1061-1071, 'Also the forced Re… [5 notes] |
| 151 | `CV:lem:silence` | `CV.silence` | CV.Silence | reviews/cv-lem-silence.json | faithful | std+H+LM+LMU | Formally only: the Lean lemma is stated for n ≥ 3 (`hn : 3 ≤ n`, statement 493/505, plus `[NeZero n]`), because the accepted `CV.X1` is def… [8 notes] |
| 152 | `CV:lem:rounding` | `CV.rounding` | CV.Rounding | reviews/cv-lem-rounding.json | faithful | std | labels FR-CV1, FR-CV2, FR-CV3, FR-CV4, FR-CV5, FR-CV7, FR-R1, FR-R3, FR-R4; [W1] `Diagrammatic L` adds the no-triple / 'exactly two preimages' clause to the printed hypothesis list d3:35-38 (narrower domain; disclos… [14 notes] |
| 153 | `CV:lem:uniformrot` | `CV.uniformrot` | CV.UniformRot | reviews/cv-uniformrot.json | faithful | std | non-blocking: neg_three (stmt 284-285) concludes `rot L hL = -1` where the source (excerpt 7-8, d3:269-270) says "equality in absolute valu… [7 notes] |
| 154 | `CV:lem:curl` | `CV.curl` | CV.Curl | reviews/cv-lem-curl.json | faithful | std+LM | labels FR-C1, FR-C2, FR-C3, FR-C5, FR-C6; NON-BLOCKING: "disc" = IsDisc (any convex compact body with nonempty interior) rather than a round disc; the existential Δ is therefore dra… [18 notes] |
| 155 | `CV:thm:carrierfloor` | `CV.carrierfloor` | CV.CarrierFloor | reviews/cv-thm-carrierfloor.json | faithful | 9 | labels D-CVT-1, FR-CV-155-1..9; `:= carrierfloor_of_sm SM.cf_thm_carrierfloor` — (R)(A)(B)(C) on CV's printed binders (`LabelledTuple`, `Diagrammatic`, `Regular`, `OverUnder`, `CV.rot`/`rotAbs`) PROVED from the SM row-99 bundles through the accepted polygon bridge F6, (D) proved on CV:def:X1 objects; (B) normalised orientation with the reversal branch on SM objects and R = `\|rotationNumber (reversal L)\|` (equal to `rotAbs` by `rot_eq_rotationNumber`, `rot_reversal`; FR-CV-155-5); (A)'s domain is `Diagrammatic` (no triple points), which lem:rounding's printed list omits; (D)'s "so that P = 1 and w = 0" is commentary, not a conjunct (FR-CV-155-7) [13 notes] |
| 156 | `CV:lem:pieceintrinsic` | `CV.pieceintrinsic` | CV.PieceIntrinsic | reviews/cv-lem-pieceintrinsic.json | faithful | std+H+LM+LMU | labels F4; `same_link` (S:1007-1009): HOMFLY-PT equality instead of "present the same oriented link" — the recorded F4 replacement of CV:ax:gausscode… [15 notes] |
| 157 | `CV:lem:homflyrows` | `CV.homflyrows` | CV.HomflyRows | reviews/cv-lem-homflyrows.json | faithful | std+H+LM+LMU | labels D2, D9; Non-blocking: connected_sum reads the printed 'K # J' as EVERY clean marked join of EVERY pair of marked representatives (IsCleanMarkedJoin… [7 notes] |
| 158 | `CV:cor:groupedknot` | `CV.groupedknot` | CV.GroupedKnot | reviews/cv-cor-groupedknot.json | faithful | std+H+LM+LMU | labels D9, F4; 'retaining exactly the labels of W' / 'exactly the crossings of H₁ ∪ ⋯ ∪ H_k' is certified by a bare cardinality bijection Nonempty (Γ.Cros… [18 notes] |
| 159 | `CV:lem:fulltwist` | `CV.fulltwist` | CV.FullTwist | reviews/cv-fulltwist.json | faithful | std+H+LM+LMU | non-blocking: `Relation.ReflTransGen RII (D_H.switch q) D_L` admits the empty chain, i.e. the case D_H.switch q = D_L literally; the printe… [5 notes] |
| m166 | `CV:ax:R` | `CV.hyp_R` | RProof.X1Rows | reviews/cv-ax-R.json | faithful | std+H | CV.hyp_R is a Prop definition (the hypothesis) in the R6 all-sides chamber-value form; hn : 3 ≤ n presupposition |
| 160 | `CV:ax:homfly` | `CV.ax_homfly` | CV.Axioms | reviews/cv-ax-homfly.json | faithful | std+H+LM+LMU | DERIVED (theorem, not axiom) from SM.lit_homfly/lp_lm/lp_lm_uniqueness; D2: links = LinkEquiv classes of polygonal diagrams |
| 161 | `CV:ax:etnyre` | `CV.ax_etnyre` | CV.AxEtnyre | reviews/cv-ax-etnyre.json | faithful | std+SC | labels D-SC-4, FR-FC-4; a THEOREM from `SM.src_contact` alone (the CV `ax:*` rows are theorems, the `CV.ax_homfly` pattern; D-F10 option (iii) superseded); the CV text's undefined `sl` is read as the document's `SM.sl` (row 88's self-linking made ε-free); the redundant printed hypothesis "no downward vertical tangency" is kept; `TransverseKnot` fixes the class (C^∞, 1-periodic, `z′ − y x′ > 0`, generic xz projection) [2 notes] |
| 162 | `CV:ax:slbound` | `CV.ax_slbound` | CV.AxSlbound | reviews/cv-ax-slbound.json | faithful | 9 | labels D-SC-4, FR-FC-5/6; a THEOREM `:= ax_slbound_of SM.fd_contact` (P = homfly by lp:core); WEAKER (recorded narrowing FR-FC-5): "a transverse knot in the standard contact ℝ³" is `SM.TransverseKnot` (generic xz projection, C^∞, positively transverse, 1-periodic) — fd:contact's own domain and the sole consumer's instance (thm:carrierfloor (C)); P_T = `homfly X` for every reading X (FR-FC-6); in the never-realised case `homfly X = 0` the clause would read sl ≤ −1 [9 notes] |
| 163 | `CV:ax:gausscode` | `CV.gausscode_polynomial` | CV.Axioms | reviews/cv-ax-gausscode.json | faithful | std+H+LM+LMU | F4 replacement (scope change recorded AUTHOR_NOTES ~01:24Z): conclusion homfly D = homfly D′ instead of "present the same oriented link"; strictly weaker; all consumers pass through polynomial equality |
| 164 | `CV:selector_A` | `CV.selector_A` | CV.SelectorA | reviews/cv-selector-A.json | faithful | std | non-blocking: the ownership of the two visit marks of a selected crossing (which of v, twin v lies on which carrier) follows SM conv:select… [5 notes] |
| 165 | `CV:singleton_D_i` | `CV.singleton_D_i` | CV.SingletonDi | reviews/cv-singleton-d-i.json | faithful | 9 | labels D-CVT-3, FR-CV-165-1..4; `:= singleton_D_i_of cvt_singleton_split (carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC)`; clause (D)(i) of thm:s7universal alone (no eligibility / ε = 0 binders, which the (D) preamble attaches to (ii)-(v)); `degree_gap` in support form `slot + 2 ≤ d` (FR-CV-165-1); STRONGER (N1): quantified over every CV-generic polygon on n ≥ 3, not only the event's polygons; row 103 is the template only — nothing of it is consumable on `CV.Generic` (FR-CV-165-3) [1 note] |
| 166 | `R:localization` | `RProof.localization` | RProof.Cores | reviews/r-localization.json | faithful | std | corollary sentence 2 ("both orbits occur") omitted by executor decision (consumed by nothing) |
| 167 | `R:parity` | `RProof.parity` | RProof.Cores | reviews/r-parity.json | faithful | std | avail_wall_invariant conditional on the cross-wall support identification hs (R-LOC-2 (1)) |
| 168 | `R:exterior` | `RProof.exterior` | RProof.X1Rows2 | reviews/r-exterior.json | faithful | std+H+LM+LMU | exterior factor represented by the base row; printed full-availability binder kept |
| 169 | `R:fibre_partition` | `RProof.fibre_partition` | RProof.Cores | reviews/r-fibre-partition.json | faithful | std | X₁-free form of the partition identity for every support (the complete def:X1 summand identity lives in the X₁ rows) |
| 170 | `R:availability_0_1` | `RProof.availability_zero_one` | RProof.X1Rows2 | reviews/r-availability.json | faithful | std+H+LM+LMU | summand_transport stronger than the bare fibre identity; cross-wall fields presuppose hs |
| 171 | `R:generic_table` | `RProof.generic_table` | RProof.Cores | reviews/r-generic-table.json | faithful | std | words/tables asserted on the canonical branch s_a = s_b = s_c (relabelled instances by F2(A)) |
| 172 | `R:generic_selector` | `RProof.generic_selector` | RProof.X1Rows | reviews/r-generic-selector.json | faithful | std+H | fixed labels a = x_ef, b = x_eg, c = x_fg with the canonical branch + relabelled instances; sides named by local graphs; ownership convention kernel-checked (mixed_carrier was FALSE in design B) |
| 173 | `R:generic_transport` | `RProof.generic_transport` | RProof.GenericTransport | reviews/r-generic-transport.json | faithful | std+H+LM+LMU | G11 RIII-wall invariance proved by an explicit polygonal RIII move; hs crossing-set identification a universally quantified hypothesis of cross-wall fields |
| 174 | `R:generic_selected` | `RProof.generic_selected` | RProof.GenericSelected | reviews/r-generic-selected.json | faithful | 9 | labels D-RM-1..4, FR-R-174; accepted 2026-09-15 23:54Z; the FIXED bundle statement of the R statement panel (2026-09-14 ~06:35Z, NOTES_FINAL §6), byte-identical to the accepted siblings 168/170/172/173/175 after the theorem and bundle names; `:= r174_generic_selected_of_arc_rec r174v_arc_rec_moves_proof` — an actual R-II deletion constructed by `exists_bigonData_of_triangle` on the switched carrier diagram (SM/BigonDeletion.lean), the bigon site I-174, the wall record transport, the carrier structure and ledgers across the wall, the smoothing identification and the site inputs; the last obligation `r174_arc_rec_moves` (the two arcs of x′ carry the outer carriers' records) PROVED by two independent routes (ARCV assembled, ARCR kept as the cross-check, work/drafts/moves/); NON-BLOCKING, all in the accepted fixed shape: the sign-branch hypotheses alongside the two-edge-side graph hypotheses (equivalent in the generic orbit by row 172), the three triangle crossings and the constant crossing set `hs` as hypotheses (presuppositions, row 164), the punctured-parameter localisation form; the brief's pointer NOTES_FINAL §7 should read §6 [13 notes] |
| 175 | `R:extreme_pair_zero` | `RProof.extreme_pair_zero` | RProof.ExtremePairZero | reviews/r-extreme-pair-zero.json | faithful | 9 | labels FR-R-174..177, NOTES_FINAL §7/§12; the FIXED bundle statement of the R statement panel (2026-09-14 ~06:35Z), byte-identical to the accepted siblings 168/170/172/173, `:= extreme_pair_zero_of_singleton CV.singleton_D_i …`; STRONGER: every field over ALL punctured parameters (`Punctured E δ t`), not only "the two nearby generic chamber-side representatives"; the K3 ↔ empty pairing is a hypothesis of no field; `third_singleton_piece` (a sentence of the printed Proof) and `pair_absent_on_complete` (a presupposition) asserted as clauses; "for arbitrary outside support" read under `FullAvail`; disclosed: one refuter saw the one-line proof term (module line 85; the same term stands in the statement file's header) [9 notes] |
| 176 | `R:extreme_transport` | `RProof.extreme_transport` | RProof.ExtremeTransport | reviews/r-extreme-transport.json | faithful | 9 | labels D-RM-5, D-RM-6, D-RM-7; accepted 2026-09-16 00:12Z; the FIXED bundle statement (R statement panel, NOTES_FINAL §8), byte-identical to the accepted siblings 168/170/172/173/174/175; `:= r176a_extreme_transport_rowShape …` through the weak-port replay `est_port_weak` PROVED from the constructed R-II deletion (D-RM-5: the literal `est_PortData.port` is unrealisable) and the `wind(S) = 0` split (D-RM-6: `rot/alt₁/alt₂` need `wind ≠ 0`; both row terms vanish at `wind = 0`); D-RM-7: a draft outer-carrier Prop false in one disjunct, corrected and proved (a draft artefact, no accepted declaration involved); RProof/RALedgers.lean untouched; NON-BLOCKING, all in the fixed shape: the transports conditional on the explicit `hs` (R-LOC-2 (1), row 164), `singleton_rows_present` per side (the other side by R-PAR (P2)), `graphs_complementary` over every opposite pair (R-LOC-2 clause 4), `sign_branch` not restating σ ≠ 0 (row 172) [12 notes] |
| 177 | `R:extreme_selected` | `RProof.extreme_selected` | RProof.ExtremeSelected | reviews/r-extreme-selected.json | faithful | 9 | labels FR-R-177, A-177-1, A-177-2, G-03 route (ii), G-02b NOT used; accepted 2026-09-19 08:39Z; the FIXED bundle statement (R statement panel), byte-identical to the accepted siblings 168/170/172/173/174/175/176 after the bundle name, `:= w3ck_extreme_selected …` (RProof/ExtremeSelectedUnits.lean, 13 944 lines; the switched RIII core on the trans-free copy RProof/GenericTransportSw.lean, 7 845 lines — the accepted RProof/GenericTransport.lean untouched); proof-route disclosure: the R-II-after-smoothing obligation in its VALUE form, kink case by a flat subdivision — no event-level hypothesis, no narrowing; NON-BLOCKING, in the fixed shape: `CompleteLocal` on side t only (the empty side by R-LOC-2 clause 4), `full_absent_on_complete` over every finset, the sign ledger and the words as proof data, the localisation form [8 notes] |
| 178 | `R:cv_theorem` | `RProof.cv_R` | RProof.CvR | reviews/r-cv-theorem.json | faithful | 9 | labels D-CVT-5, FR-R-178-1, FR-R-178-2; accepted 2026-09-19 08:39Z; the staged one-liner `cv_R : CV.hyp_R := cv_R_of_rows generic_selected extreme_pair_zero extreme_transport extreme_selected` (RProof/CvR.lean; `cv_R_of_rows` RProof/RALedgers.lean:2354); no hypothesis, no R parameter; footprint `9` as FR-R-178-2 predicted (§4.3); NON-BLOCKING: the R6 all-parameters form `X1 (E.curve tp) = X1 (E.curve tm)` for all tp > 0 > tm, equivalent to the chamber form by CV:prop:chamberinv (ii); redundant index binders; `SignChanges` as the accepted def:event reading [6 notes] |
| 179 | `Bridge:B1` | `Bridge.B1` | Bridge.B1 | reviews/bridge-b1.json | faithful | std | non-blocking: `[NeZero n]` (statement line 47) is carried as an instance argument in addition to `hn : 3 ≤ n`; it is implied by hn and only… [5 notes] |
| 180 | `Bridge:B2` | `Bridge.B2` | Bridge.B1 | reviews/bridge-b2.json | faithful | std | stated under sorted naming rep e < rep f < rep k; unsorted case via exists_sorted_tripleAt |
| 181 | `Bridge:B3` | `Bridge.B3` | Bridge.B3 | reviews/bridge-b3.json | faithful | std | non-blocking: `SignChanges` (both SM and CV renderings) carries an extra `δ ≤ radius` clause absent from the printed 'there is δ>0 with φ(P… [6 notes] |
| 182 | `Bridge:B4` | `Bridge.B4` | Bridge.B4 | reviews/bridge-b4.json | faithful | std+H+LM+LMU | the C = X₁ dictionary through the accepted geo*_eq_generic lemmas (CV-DOM option (C)) |
| 183 | `Bridge:theorem` | `Bridge.sm_R` | Bridge.SmRRow | reviews/bridge-theorem.json | faithful | 9 | labels FR-B-183, BRIDGE.md §3 (19)-(21); accepted 2026-09-19 08:39Z; the staged one-liner `sm_R : SM.hyp_R := SM.sm_R_of_cv_R RProof.cv_R` (Bridge/SmRRow.lean; `SM.sm_R_of_cv_R` Bridge/SmR.lean, B1-B4 pointwise); no hypothesis; NON-BLOCKING: the row is the CONSEQUENT of the displayed implication (19) with its antecedent discharged by row 178 (formally unconditional, stronger); the side-parameter form of hyp:R equivalent to the two chamber values by prop:C-chamber (FR-HR-1); presupposition binders `hn : 3 ≤ n` [9 notes] |
| 184 | `SM:corner_laws_and_soft` | `SM.corner_laws_and_soft` | SM.CornerLawsAndSoft | reviews/sm-corner-laws-and-soft.json | faithful | 9 | labels FR-F-184-1..4, D-CVT-5, A-21, A-22; accepted 2026-09-19 13:26Z; `corner_laws_and_soft : CornerLawsAndSoftData := corner_laws_and_soft_of Bridge.sm_R thm_C_S7 thm_C_soft (cor_C_inherits Bridge.sm_R)` (SM/CornerLawsAndSoft.lean, 86 lines; one field per item of TARGETS' Required coverage: chamber, silent, flat, vertex_edge, triple : hyp_R (PROVED, no R parameter retained), cusp, empty_cusp, soft, reversal, cyclic, triangles); port edit A-22: the tail draft's CInheritsData copy replaced by `import SM.CInherits` (D-CM-3); NON-BLOCKING: `CuspLawC` asserts the deletion's genericity in its conclusion (∃ hQ), the all-side-parameter forms inherited from the accepted rows, CS3Data's existential δ and CS5Data's germ-side form; PROCESS: the row-184 reviewers found the thm-C-S7 / cor-C-inherits review files not yet written (concurrent workflow) and checked the field types against the printed statements directly; FOOTPRINT: the kernel lists SIX literature axioms where TARGETS says five interfaces — `SM.lit_homfly_descent` is the author-authorised second declaration of lit:homfly (§4.3) [6 notes] |
| m192 | `lem:weak-open` | `SM.weak_open` | SM.WeakOpen | reviews/lem-weak-open.json | faithful | std | extra supporting lemma outside the 132 (scope_note in the map) |
<!-- END:ACCEPTED -->

## 3. Pending rows — one line each with the reason  (table regenerated 2026-09-19 13:4xZ; 1 row at draft time; <<ROW57: fill at acceptance — empty table or the honest state>>)

<!-- BEGIN:PENDING -->
| # | row | policy / fixed name | status | reason at draft time (2026-09-19 13:26Z) |
|---|---|---|---|---|
| 57 | `lem:gauss-two-discs` | — (no fixed name in the policy; the lane's `SM.lem_gauss_two_discs`) | pending | <<ROW57: fill at acceptance>> — at draft time: un-deferred by the author (D-AUTH-20260919 G-09); statement FROZEN (work/drafts/twodiscs/Statements_FINAL.lean, readings FR-TD-1..14 = D-TD-1); skeleton 92 leaves; wave 1 assembled 62/92 (W1_Assembled.lean, 13 815 lines, 0 errors); wave 2 RUNNING (U6 8, U7 7, U9 5 leaves closed; U5 2 + U8 8 in flight), then the U12 assembler, port, review (§3.2) |
<!-- END:PENDING -->

**The 1 pending row at draft time** (`python3 tools/claims.py --pending-only` lists exactly row 57; the map has exactly 1 non-accepted
row): **row 57 `lem:gauss-two-discs`**, un-deferred by the author on 2026-09-19 (D-AUTH-20260919 G-09: "UN-DEFERRED. Prove it. … It
gates nothing but the stage check"), statement frozen and proving in two waves (§3.2). Nothing else is pending: the seven other rows
of the 2026-09-16 list closed on 2026-09-19 — 177 by a fourth bounded wave (3d) once the author lifted the A-177-2 consequence, 178 and
183 by their staged one-liners, 110 by three further corner waves (4-6) once the A-110-1 consequence was lifted, 127 and 128 by their
one-liners, 184 by the prepared module with edit A-22. <<ROW57: fill at acceptance — if row 57 is accepted: "No row is pending; the map
has 192 accepted rows." If not: its honest state (leaves open, sizes, the exact obligation) in the row-57 block of §3.2.>>

### 3.1 Row 110 `thm:C-S7` — CLOSED and ACCEPTED 2026-09-19 13:26Z (corner waves 4-6; audits A-110-1, A-110-2)

Record: OPEN_ITEMS_20260916.md §A-02 (the 2026-09-16 state: kernel-proved modulo five named Props, construction stopped by audit
A-110-1) and §A-03..A-12 (the leaves); D-AUTH-20260919 G-01 ("Fund the remainder … over as many waves as it takes"); AUTHOR_NOTES
"Corner wave 4: the SLIDING leaf of thm:C-S7 is CLOSED; the bigon leaf reduced to ONE Prop; wave 5 launched" (08:25Z), "Corner wave 5:
unit W5-BR finished its file but its agent died on an API 500; report written by the executor" (10:47Z), "Corner wave 5 assembled
(W5_Assembled.lean); audit A-110-2; wave 6 launched on the four live boxes" (11:22Z), "Corner wave 6: unit W6-COR CLOSED
`w5r_box_corners`" (11:47Z), "W6-ROT delivered both rotation identities but left ONE new box; unit W6-CC launched" (12:01Z), "W6-CURL
proved the curl data in a CORRECTED form (rule 3)" (12:04Z), "W6-CC CLOSED `w6r_box_centreCorners`" (12:38Z), "ROW 110 thm:C-S7 PROVED
sorry-free in the draft (corner wave 6 glued); port … started" (12:55Z), "Rows 110 / 127 / 128 / 184 PORTED and KERNEL-CHECKED"
(12:57Z), "ROWS 110 … 184 ACCEPTED" (13:26Z); reports `W4_ASSEMBLY_REPORT.md`, `W5_ASSEMBLY_REPORT.md`, `W5_BR_REPORT.md`,
`W6_ASSEMBLY_REPORT_B.md`, `port/CS7_B/PORT_REPORT.md`.

**The statement is unchanged**: `CS7Data.vertex_edge_law` of the accepted `SM/CornerChainStatements.lean` (D-CC-1: `g.VertexEdgeAt
M a → ∀ h₁ h₂ tp tm, C(P₊) − C(P₋) = contactSign · C(λ₁) · C(λ₂)`; companions `.bigon` / `.sliding`; FR-CC-7..10), frozen since
2026-09-15 15:25Z and shared with the accepted rows 103/105/112; `stmt_check.py` reports the five frozen declarations of `W3_Skeleton.lean`
byte-identical in every wave's assembly and in the ported `SM/CS7.lean` (5/5 PASS). **The row theorem** `theorem SM.thm_C_S7 :
CS7Data := thm_C_S7_of_floor thm_floor` (`SM/CS7.lean:92`; `thm_C_S7_of_floor hF := thm_C_S7_of hF (cb_singleton_of_floor hF)`) has
`#print axioms` = exactly the nine registered axioms, no `sorryAx` (PORT_REPORT §1; the executor's probe 12:57Z; the checker 12:58Z and
13:28Z). What closed between 2026-09-16 and 2026-09-19, wave by wave (all on byte-identical copies of the previous assembly, every unit a
pure insertion plus at most one body replacement, `W4/W5/W6 §1` diffs "all clean"):
- **Wave 4** (wf_112e0a7f-f6b; eight units; `W4_Assembled.lean` 19 974 lines, 0 errors): the SLIDING leaf `s7_sliding_law_at` CLOSED —
  S1′ `s7u_box_ret'` (the corrected first-return box on both sides, unit S1P) + S3′ `s7u_box_carriers'` (closed by the assembler from
  S3G's 3 137-line `s7g_box_carriers'` on RET's two transports, 109 lines of glue) through `s7u_sliding_law_at_of`; axioms standard +
  `lit_homfly`, `lp_lm`, `lp_lm_uniqueness`. RET's rule-4 finding stands: the original S1 box `s7q_box_ret` is FALSE as stated on the
  leg-M side and was dropped at port. BIGON: F's three boxes (FB1 335 lines, FB2 4 020, FB3 843), SITE's two (SITEC 608) and record
  identification (SITEH 420), K's B3 (849) all proved; K's F-aligned route built (`w4_EligDec` — a correction of W3_K_REPORT §4(a): eligible
  DECOMPOSITIONS, not supports —, `w4_liftEquiv`, `w4_eligibleEquiv`, `w4_oneNewborn_rows`, `w4_residualData`); K's B1 no longer needed;
  B2 restated in F's vocabulary as B2′ `w4_BigonReturnedRows` (the returned newborn-free rows per eligible decomposition below a radius);
  `w4_s7_bigon_law_at_of hsing (hrows : B2′)` sorry-free. `thm_C_S7` then carried `sorryAx` from exactly ONE source, the bigon leaf.
- **Wave 5** (units RT, SITE, BR, ROW; `W5_Assembled.lean` 25 237 lines, 0 errors, 1 366 new declarations): B2′ reduced to FOUR named
  geometric Props with every consumed interface proved (`W5_ASSEMBLY_REPORT.md` §5): `w5r_box_corners` (the contact-corner
  correspondence), `w5b_box_interlacingTurnData`, `w5b_box_noninterlacingTurnData` (rotation + the two half patterns), `w5b_box_curlData`
  (the curl component's value and writhe). Discharged in the merge: ROW's `w5r_box_transport` (← RT) and `w5r_box_contact` (← SITE);
  restated glue `w5_box_branch` (ROW's `w5r_box_branch` lacked the selector hypothesis; `w5_returnedRow_of` handles `wt(q_L) = 0`
  directly — ≈ 35 lines of new assembly mathematics, §8 item 6). Incident: unit W5-BR finished its 1 656-line block (0 errors) and died on
  a transient API HTTP 500 during its final `#print axioms` probe; the executor re-ran the probe and wrote `W5_BR_REPORT.md` from the
  unit's file, compile log and probe only (no content added or changed; §6). **Audit A-110-2** (11:22Z; the reassessment rule, under
  D-AUTH §2 never a stop): no counterexample, no outside assumption — the four Props are the printed sm-4:576-600 corner bookkeeping,
  the U110-I rotation identities on the centre polygon and the cb:products curl value; method unchanged; estimate 1 900-3 200 lines;
  wave 6 = COR + ROT + CURL in parallel, then GLUE.
- **Wave 6** (COR, ROT, CC, CURL + two GLUE assemblers): COR CLOSED `w5r_box_corners` exactly as stated (436 lines, standard axioms);
  ROT proved both rotation identities from the corner data and the centre polygon `L*` but stated ONE new box `w6r_box_centreCorners`
  (the corner correspondence on `L*` in principal-turn form — the wave-6 brief's phrase "in principalTurn form" was not a reading of the
  declared box, so ROT stated the needed Prop exactly; rule-3 disclosure, no new assumption); CC CLOSED that box exactly as stated (784
  lines, standard axioms); CURL proved the curl data in a CORRECTED form `w6k_box_curlData` (six radius facts `hr0 hr1 hr hη hηr hηr1`
  added — BR's box from `hloc ht` alone is not derivable; the consumer already carried them; rule 3). GLUE: BR's two turn boxes are
  stated for EVERY side parameter without a radius and cannot be given bodies as stated (the corner and centre data hold below radii only);
  like ROW's `w5r_box_branch` they were left unproved and UNUSED and the chain restated under the wave-6 radii (`w6_interlacingTurnData`,
  `w6_noninterlacingTurnData`, `w6_interlacingData`, `w6_noninterlacingData`, `w6_branchData`, `w6_box_branch`; radius = A2's ∧
  `w5r_box_corners`' ∧ `w6r_box_centreCorners`'); `w4_box_returnedRows` consumes `w6_box_branch` and is sorry-free; the bigon leaf closed
  by the recorded line `w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)`. **Deviations disclosed**
  (`W6_ASSEMBLY_REPORT_B.md` §8): the two BR turn boxes and the curl box restated with radius hypotheses and the as-stated boxes dropped as
  dead draft material; `w5b_box_curlData`'s one-token re-thread applied inside the (dead) `w5b_noninterlacingData` body; `w6r_exists_rotation`
  kept unused. Whole-file `#print axioms` census (1 453 declarations): the axiom universe of the draft is the nine registered axioms +
  `sorryAx`, the latter in EXACTLY 19 dead declarations (8 own sorries, 11 inherited), all off every path to a frozen declaration.
- **Two glue-assembler instances** ran on the same unit files (the executor's message to the running workflow agent at 12:04Z resumed a
  duplicate of its transcript): instance A wrote `W6_Assembled.lean` (27 533 lines) + `W6_ASSEMBLY_REPORT.md` + `port/CS7/`; instance B
  wrote `W6_Assembled_B.lean` (27 531 lines, sha256 `37265742…`) + `W6_ASSEMBLY_REPORT_B.md` + `port/CS7_B/`. Both 0 errors, identical
  axiom censuses (`thm_C_S7` on the nine; `sorryAx` in the same 19). Executor decision: port from instance B (complete first, 12:40Z;
  verified in a scratch olean tree), A as the cross-check (§6, §7).
- **Port** (`port/CS7_B/PORT_REPORT.md`): `SM/CS7Units.lean` = the assembled file from `namespace SM` to `end VertexEdge` minus the two
  leaves and 26 dead declarations (468 lines; the 19 `sorryAx` carriers + 7 sorry-free companions serving only them — `s7q_box_ret`,
  `w3_SlidingRet` and its consumers, K's B1/B2 boxes and `w3_BigonFSector`/`w3_BigonReturnedRows`/`w3_s7_bigon_law_at_of`,
  `w5b_box_returnedData`, the two BR turn boxes and their consumers, `w5b_box_curlData`, `w5_branchData`/`w5_box_branch`,
  `w5r_box_branch`), with 27 docstring rewordings (no `sorry` string remains; 12 "BLACK BOX" heads → "PROVED (…)"); no collapses of
  duplicate `def`s applied (listed in §4 of the report). Statements, names and bodies untouched. `SM/CS7.lean` = the frozen declarations
  of `W3_Skeleton.lean` verbatim. Installed 12:54Z; `lake build` 0 errors (84 s); mapped implemented 12:55Z; checker 12:58Z passed
  (191 mapped, 46 842 audited).
- **Review** `reviews/thm-C-S7.json` (13:25:40Z): 3 lenses `faithful`, 2 refuters "not refuted"; `kernel_check` = the nine registered
  axioms; 9 non-blocking notes, all inherited C-row conventions (the identity at every pair of side parameters; `SignChanges`' `δ ≤ radius`;
  `hn : 3 ≤ n` vacuous under `ContactSeparated` (n ≥ 5); the halves' genericity as universally quantified witnesses; "of bigon or sliding
  type" as the exhaustive dichotomy `vertexEdge_bigon_or_sliding`; a reviewer disclosure that a `grep` printed four proof-local `have :
  NeZero …` lines of `SM/CS7Units.lean`, a file the brief forbade — no statement text or proof structure read, nothing relied on). The
  `executor_notes` disclose the wave-5/6 restatements and that "the kink-case flat-subdivision route is not used here". Accepted 13:26Z;
  receipt `dev-check-rows110-127-128-184-accepted.json` (13:28Z).

Size record (for §7): D-CC-4 (2026-09-15) estimated 11-15k lines for the row; the lane produced `SM/CornerChainUnits.lean` 11 842
(shared with 103/105/112) + `SM/CS7Sliding.lean` 2 956 + `SM/BigonDeletion.lean` 5 374 (shared with the R rows) + `SM/CS7Units.lean`
27 000 + `SM/CS7.lean` 97 — the remainder owed on 2026-09-16 (≈ 8-12k) came to ≈ 18.5k assembled lines (W3 8 958 → W6 27 531, minus
deletions). The 2026-09-16 audit's diagnosis "decomposition size, not mathematics" was borne out: no leaf was false at the level of a
row statement; four draft boxes were false or not derivable as stated and were restated (rule 3), one library structure field
(`s7b_SlidingTransport.ret`, C-05) remains false on the leg-M side and is documented by the prepared patch 06 (E-08).

### 3.2 Row 57 `lem:gauss-two-discs` — PENDING AT DRAFT TIME (un-deferred by the author; wave 2 running)

<<ROW57: fill at acceptance — the final outcome block. On acceptance: the acceptance time, review file `reviews/lem-gauss-two-discs.json`
(lenses, refuters, notes), the row module(s) `SM/GaussTwoDiscs*.lean` with line counts, the row theorem's `#print axioms` (expected:
standard axioms only — no literature axiom entered any closed leaf at wave 1), the receipt(s) `dev-check-row57-*.json` (mapped 192,
audited N), D-TD-2's corrected forms and D-TD-3's rename as disclosed in the review, and FR-TD-15. If NOT accepted: the honest state —
leaves open by unit, sizes, the exact obligations, and the stage-check consequence.>>

State at draft time (13:26Z 2026-09-19), from AUTHOR_NOTES L6683-6802, L6854-6905, L6937-6949, L6998-7004 and `work/drafts/twodiscs/`:
- **The author's decision (G-09, 05:33Z):** "UN-DEFERRED. Prove it. The 2026-09-15 instruction 'Row 57 stays deferred' (D-GAP2 item 5)
  is withdrawn. Start from `work/drafts/pldiscs/PLDISCS_FEASIBILITY.md` and the lane pattern of RESUME §5. It gates nothing but the stage
  check, so it may run in parallel with rows 110 and 177." The 2026-09-14 feasibility verdict (INFEASIBLE now, 12-20k lines, PL Schoenflies)
  is superseded by the lane's route A (below); the blueprint edges 57 → 104 and 57 → 105 remain unrealised by the proof routes (D-ER1,
  `corner_values_i`) — no accepted row depends on row 57 either way.
- **Design panel (wf_134d331c-e4f, 08:23Z; D-TD-0):** architect A delivered `PLAN_A.md` + `Statements_A.lean` (typechecks); architect B,
  the judge and a standalone rerun of B all died with "response exceeded the 64000 output token maximum" spent on thinking, producing no
  file (a process incident, §6); the fidelity critic judged `Statements_A.lean` FAITHFUL with three edits (add `B ⊆ S` to `IsPLDiscSphere`;
  docstring notes on `traversalPositiveFor` and on the hypothesis choice; do not weaken any field). D-TD-0: proceed from A + the critic's
  edits; a medium-effort finalizer wrote `PLAN_FINAL.md` / `Statements_FINAL.lean`; process rule adopted: design/judge agents run at
  effort 'medium' with the instruction to decide quickly and write in small pieces.
- **The statement (FROZEN; `Statements_FINAL.lean`, 305 lines, typechecks):** `theorem SM.lem_gauss_two_discs [NeZero n] (hn : 3 ≤ n)
  (P : LabelledTuple n) (hP : Embedded P) : GaussTwoDiscsData P` (no fixed name in the policy for row 57), the bundle with one field per
  printed clause: `two_regions` (57a: `Nat.card (ConnectedComponents (sphereComplement P)) = 2` in the sphere `OnePoint Plane`),
  `pl_discs` (57b: for every side and every model scale `L` with `InsideModel L P`, the closed region is a PL disc in the two-disc-model
  charts with the circle inside it, `IsPLDiscSphere`), `pl_extension` (57c: finite positive PL boundary lifts between the closed regions
  of any two embedded polygons extend to positive PL sphere maps), `top_extension` (57d: topological extension), `exterior` (57e: the
  region of `∞` is the unbounded region, the other bounded), plus the two-disc model (supNorm square `Q_L`, `capInvFun` chart at `∞`,
  `InsideModel`). **Fidelity readings recorded BEFORE stating (D-TD-1 = PLAN_FINAL §5, FR-TD-1..14, verbatim in AUTHOR_NOTES L6736-6802):**
  FR-TD-1 `Embedded P` with `3 ≤ n`, no `Regular` hypothesis (derived), sphere = `OnePoint Plane`, orientation `det > 0` in either chart;
  FR-TD-2 regions = connected components of the complement, exterior = the component of `∞`; FR-TD-3 PL disc = `Link.IsDisc` with a finite
  straight triangulation, positive affine on each triangle, at every model scale; FR-TD-4 boundary maps as lifts `φ : ℝ → ℝ` in
  traversal coordinates (`IsPositiveBoundaryLift`, `IsFinitePL` — the accepted `rexB_pl` pattern), between the closed regions of any two
  embedded polygons incl. the two sides of one polygon; FR-TD-5 57d = `∃ F` homeomorphism onto with the boundary condition, "positive" kept
  as printed though unused; FR-TD-6 no Jordan/Schoenflies input (Mathlib has none) — 57a from the ear triangulation and ambient ear
  homeomorphisms (route A), 57b not derived from 57a; FR-TD-7 the explicit two-disc model (square gauge + a reflection making the chart
  orientation-preserving) instead of the printed Euclidean radial map — PL-homeomorphic models, sign convention verified by the Jacobian;
  FR-TD-8 STRONGER: 57b/57c at every model scale, not one large rectangle; FR-TD-9 `traversalPositiveFor` DEFINES the positive boundary
  orientation of the interior region as the traversal iff `0 < rotationNumber P` (the accepted `EmbeddedRotationData.orientation`
  convention; if wrong, 57c would be false, so unit U9 checks it); FR-TD-10 lifts instead of boundary homeomorphisms (equivalent; the
  lifting lemma not part of the row); FR-TD-11 57e rendered by `∀ s : Side` in 57b-d plus the `exterior` field; FR-TD-12 `IsPLDiscSphere`
  carries `f '' sphereCircle P = frontier D` (the circle is the whole boundary, print 490-491) and `B ⊆ S`; FR-TD-13 set-based
  `Triangulation` (not a Mathlib simplicial complex, by design); FR-TD-14 chart-membership clause of `IsPositivePLSphereMap` (standard
  subdivision condition, achievable by refinement). FR-TD-15 (D-TD-3, 11:54Z): the draft `def SM.polygonImage (P : LabelledTuple n)`
  collided with the accepted `SM.polygonImage (C : PolyComp)` of the registered `SM/Rounding.lean:140`; the DRAFT def was renamed
  `embeddedPolygonImage` (a pure renaming of a helper; statement meaning unchanged; options (b) sub-namespace and (c) editing an accepted
  module rejected — G-05 is comment-only).
- **Skeleton (`Skeleton_FINAL.lean`, 1 039 lines, 0 errors, 92 leaf `sorry`s; `SKELETON_REPORT.md`):** the row theorem assembled from six
  output leaves (`U6_two_regions`, `U6_exterior`, `U7_pl_discs_inner`, `U8_pl_discs_outer`, `U10_pl_extension`, `U11_top_extension`); the
  other 86 leaves are the units' internal contracts; `check_57_identity.py` asserts the frozen blocks byte-identical in every unit file.
- **Wave 1 (units U1, U2, U3, U4, U10, U11; assembled 11:51Z, `W1_Assembled.lean` 13 815 lines, 0 errors):** 62 of 92 leaves closed —
  58 on `[propext, Classical.choice, Quot.sound]`, 4 (`U10_boundary_map_of_lift`, `U10_pl_extension`, `U11_boundary_homeo_of_lift`,
  `U11_top_extension`) carrying `sorryAx` only through open wave-2 leaves; **no literature axiom, no `native_decide`, no unregistered
  axiom** anywhere in the row's closure. **Rule 3 (D-TD-2, 11:37Z; three INTERNAL skeleton sub-leaves false as stated, none a row
  statement):** `U3_isPositivePLFromPlane_inv` false for `L ≤ 0` — gained `(hL : 0 < L)` (closed; one consumer call site patched);
  `U4_polygonImage_ear` false as stated — kernel-checked counterexample P0=(0,0), P1=(2,0), P2=(2,2), P3=(0,3), P4=(1,−1), j=1: the point
  (0.6, 0.6) of edge 3 lies on the open diagonal and on no ear edge — gained `Embedded P`, `P(j−1) ≠ P(j+1)` and a STRICT-ear hypothesis
  (closed as `u4h_polygonImage_ear`; no consumer); `U5_exists_ear_homeo` false for a reflex ear — gained `hcut : earHull P j ∩ U' =
  segment ℝ (P (j−1)) (P (j+1))` (U6 obtains `hcut` from `u4h_regionOf_ear`). Method note (U4): the triangulation is built by strong
  induction along a clean diagonal from the lexmin vertex (the printed triangulation argument in a different induction order; no new
  assumption).
- **Wave 2 (U5, U6, U7, U8, U9 on byte-identical copies of the renamed `W1_Assembled.lean`; launched 11:54Z):** at draft time U7 (57b
  interior, 7 leaves, 12:10Z), U6 (57a/57e via the ambient parametrisation, 8 leaves, 12:22Z; 57a by `Nat.card_eq_two_iff` on two disjoint
  open connected pieces) and U9 (orientation bookkeeping, 5 leaves incl. `U9_lift_preserves_cyclicPos` — TRUE as stated; `InteriorOnLeft ↔
  σ = 1 ↔ 0 < rotationNumber` through the accepted `cb_embedded_rotation.orientation`, 13:00Z) closed ALL their leaves with no statement
  change; U5 (2 leaves) and U8 (8 leaves) in flight; open leaves 10 of 92. Then the U12 assembler (merge, `#print axioms lem_gauss_two_discs`,
  port files `work/drafts/twodiscs/port/SM/GaussTwoDiscs*.lean` in ≤ 6 modules), port, map, checker, review (3 lenses + 2 refuters with
  FR-TD-1..15 disclosed), acceptance. The reassessment rule applies per unit; under D-AUTH §2 a stall on cost never stops the lane.

### 3.3 The GAP-2 chain — CLOSED by the author's decision D-GAP2 (2026-09-15; unchanged, now carried by 21 accepted rows)

The 2026-09-14 review's §3.1 (text preserved in `work/FINAL_REVIEW_DRAFT.md`) described row 91 as proved modulo
`SM.AmbientIsotopyDescent` with no policy route to close it. On 2026-09-15 13:39Z the author (through Mark; "I authorize this
reading as the author") decided the additive form: declare the printed descent sentence of lit:homfly as its own axiom about the
existing `SM.homfly`, `axiom SM.lit_homfly_descent : SM.AmbientIsotopyDescent`, registered as a second declaration of lit:homfly
(not a sixth interface), interface-reviewed like the other four; close row 91 as `cp_finite_contact_path_of_descent
lit_homfly_descent`; declare `src:contact`; row 57 stays deferred (withdrawn 2026-09-19, G-09); the reassessment rule applies per
branch. Execution (D-GAP2-1..4, D-GAP2-2b; §4.3): the axiom module `SM/LitHomflyDescent.lean` (13:49Z), the policy key, the verifier
relaxation (CONFIRMED as the permanent data model by G-06 on 2026-09-19: "One literature label may carry several declarations. Do not
revert it"), row 91 accepted 14:25Z; then five lanes, each with a design panel (two architects + judge), fidelity risks recorded BEFORE
stating, frozen `Statements_FINAL.lean`, prover units on byte-identical copies, assembler, port, review: contact (src:contact, 161, 94,
162; 15:03Z-17:12Z), floor (99, 100; 14:58Z-17:50Z), CV/R tail (155, 165, 175; 15:49Z-18:39Z; 174/176/177 ledgers proved with the moves
as interfaces), corner (103, 105, 112; 15:25Z-20:25Z; 110 on 2026-09-19), comparison (122; 17:28Z-20:50Z; 127/128 on 2026-09-19), plus
the moves toolkit (D-RM-1..4: the generic RII deletion constructor `SM/BigonDeletion.lean`, 20:19Z) on which the R rows 174/176 closed
on 2026-09-15/16 and 177 on 2026-09-19 (§3.4). One internal leaf was false as stated and repaired without a row-statement change
(D-FL-4: `MirrorSubstitutionData.coeff` needs `(-1)^k.natAbs`, counterexample `ui_coeff_toNat_false`); two library interface Props were
unrealisable as stated and replaced by weak forms in new modules (D-RM-2; §5). On 2026-09-19 the author KEPT the bundled descent axiom as
is (G-08) and the literal `est_PortData` / `esc_MoveData` fields with their weak replays (G-04); the footprint now reaches the final
theorem: 21 accepted rows carry `SM.lit_homfly_descent` (§4.3).

### 3.4 The R obligations 174/176/177, `RProof.cv_R` (178), `Bridge.sm_R` (183) and the final theorem (184) — all ACCEPTED

The ledgers `gsc_ledger` / `est_ledger` / `esc_ledger` of 174/176/177 are PROVED from `CV.CarrierSlotFloor` (library
`RProof/RALedgers.lean`, ported 2026-09-15 18:08Z) with the Reidemeister-move realisations stated as explicit interface Props (D-F11
pattern; D-RM-1); the moves toolkit realised the generic bigon deletion (`exists_rii_deletion`; the j = 1 site builder
`exists_bigonData_of_triangle`) and the row glue (`gsc_fulltwist_of_bigon`, `est_port_weak_of_bigon`, `esc_rii_after_smoothing_of_bigons`,
`esc_switch_riii_of_chain`, `s7_rii_witnesses`; all sorry-free). `RProof/RALedgers.lean` was not edited by any unit or assembler on
2026-09-15/16 OR 2026-09-19 (D-RM-5, D-RM-6, A-177-1 D2, W3D §6: replays with extended interfaces in the row modules instead; verified
at draft time — its sha256 `df745f12…` equals the `project_sha256` entry of the 18:11Z 2026-09-15 receipt and of the 13:28Z 2026-09-19
receipt).

- **Row 174 `R:generic_selected` — ACCEPTED 2026-09-15 23:54Z** and **row 176 `R:extreme_transport` — ACCEPTED 2026-09-16 00:12Z**: as
  recorded in the 2026-09-16 review (two bounded waves each; 174's last Prop `r174_arc_rec_moves` proved by two independent routes,
  176 through the weak-port replay D-RM-5, the `wind = 0` split D-RM-6 and the corrected outer-carrier Prop D-RM-7); modules
  `RProof/GenericSelectedUnits.lean` (7 326) + `GenericSelected.lean`, `RProof/ExtremeTransportUnits.lean` (8 988) + `ExtremeTransport.lean`;
  reviews `reviews/r-generic-selected.json`, `r-extreme-transport.json`; unchanged since (statement hashes equal, §1). Row 175
  `R:extreme_pair_zero` accepted 2026-09-15 18:39Z, unchanged.
- **Row 177 `R:extreme_selected` — CLOSED 08:09Z and ACCEPTED 2026-09-19 08:39Z (wave 3d, after the author lifted the A-177-2
  consequence).** State on 2026-09-16 (OPEN_ITEMS §A-15..A-18): `w3ck_extreme_selected` in `W3C_Assembled.lean` (16 945 lines) with
  EXACTLY TWO `sorryAx` sources — `w3cx_outer_residue_data` (parity #mixedSet = 2Λ + KNOT's identification of the three components) and
  `w3cs_not_kink_site_data` (the lift crossing over x_ef is not a kink; "NOT a consequence of the site data; may need an event hypothesis").
  The author's decisions: G-02 fund the remainder; **G-02b**: one substantive derivation attempt at the non-kink condition, then the
  executor MAY add it as an explicit hypothesis on the RIII event, disclosed as a narrowing FR-R-177-K; G-03: either drop `trans` from the
  accepted `G11_Config` or port the additive trans-free copy — "Take the faster". **Wave 3d (wf_a5a89dad-0b9; units RESPAR, RESID,
  NONKINK; assembler 07:33-08:10Z; `W3D_ASSEMBLY_REPORT.md`):** RESPAR proved clause (i), the parity `#w3cb_mixedSet = 2Λ`, at every
  configuration (`w3dp_parity_at`, standard axioms; the bridge count 2Λ(J_L) = #mixedSet as the analogue of `r176m_bridge_count`); RESID
  proved the identification clause (`w3di_ident_at`, with the restrict-of-restrict record lemmas the library lacked and the word
  (α₁ β₁ | β₂ γ₁ | γ₂ α₂) on the contact carrier) — the residue was TRUE as stated and is CLOSED. **NONKINK (audit A-177-NK-1): the stated
  Prop `w3cs_not_kink_site` IS FALSE as stated** — the monogon e → e+1 → e+2 = f with g cutting the loop is a genuine 177 configuration
  satisfying every binder (rule 3 on a draft leaf; no kernel counterexample built since it is not a row statement). The unit BYPASSED it:
  the (6) obligation is consumed only through its HOMFLY VALUE form, and `w3dk_rii_value_sites` (`homfly ((D_H^x).switch y_H) = homfly
  ((D_L^x).switch y_L)` at every 177 configuration) is PROVED in both cases — the non-kink case through the constructed bigon deletion
  (`w3bi_bigon_of_site` + `exists_rii_deletion`) and the KINK case through a flat subdivision of the one-component lift
  (`w3dk_subdivReparam`, `w3dk_siteData_subdiv`, `w3dk_notKink_subdiv`, `w3dk_smooth_iso_subdiv`; axioms standard + `lit_homfly`, `lp_lm`,
  `lp_lm_uniqueness`). **Consequence: the authorised event-level hypothesis was NOT needed; no narrowing FR-R-177-K exists; no accepted
  event vocabulary was touched.** The printed proof's bigon step is replaced, in the kink pattern, by a subdivision argument reaching the
  same value identity — disclosed in the review's `executor_notes` as a proof-route note, not a statement change. The assembler
  (`W3D_Assembled.lean`, 21 748 lines, 1 667 declarations, 0 errors, 0 `sorry`) rewired the operative chain onto the VALUE form
  (`w3ck_esc_interface_ext_occ_holds := w3dk_esc_interface_ext_of w3ck_esc_outer_occ_holds w3dk_rii_value_sites_data`) and applied the
  port-time edits of §A-18: the false Prop `w3cs_not_kink_site`, its leaf and consumers, the false Props `w3bi_bigon_pair` /
  `w3bi_rii_sites`, the Wave-3b Props `w3bi_knot_after_two` / `w3bi_three_components` / `w3bi_esc_outer` (relational smoothings; superseded
  by the record-clause `w3ck_` chain) and the helper `w3b_reparam_switch` DELETED (31 declarations, 727 lines); the four restated j = 2
  bigon sub-leaves kept with their non-kink hypothesis (used only in the non-kink branch); library copies dropped by importing
  `SM.CBProducts`, `CV.SingletonDi`, `SM.ZeroRotationSeed`, `RProof.ExtremeTransportUnits`. `#print axioms w3ck_extreme_selected` = exactly
  the nine registered axioms (`W3D_AXIOMS.log`). **G-03 route (ii) taken:** the trans-free copy `G11_ConfigSw` / `G11_ParamsSw` ported as
  the library module `RProof/GenericTransportSw.lean` (7 845 lines); the accepted `RProof/GenericTransport.lean` untouched (sha256
  `0e7f959d…` unchanged since 2026-09-14 14:15Z), so no accepted row needed a re-review. Ported 08:06Z: `RProof/ExtremeSelectedUnits.lean`
  (13 944) and `RProof/ExtremeSelected.lean` (`theorem RProof.extreme_selected`, FIXED name; statement byte-identical to the accepted
  siblings 168/170/172/173/174/175/176 after the bundle name; `:= w3ck_extreme_selected …`); `lake build` 0 errors (85 s); checker passed
  08:11Z (187 mapped, 44 270 audited). Review `reviews/r-extreme-selected.json` (wf_b3114d58-914; `review_utc` 08:39:13Z): 3 lenses
  `faithful`, 2 refuters "not refuted" (both re-ran `example : RowShape @ExtremeSelectedData := @extreme_selected` on scratch files);
  `kernel_check` = the nine registered axioms; 8 non-blocking notes, all in the fixed shape: `couple` requires `CompleteLocal` on side t
  only (the opposite side empty by R-LOC-2 clause 4, the accepted `graphs_complementary`); `full_absent_on_complete` over EVERY finset
  (trivially true, proved unconditionally as `PRE_177_full_absent_on_complete`); the printed words (1), sign ledger (1a)-(1c) and the
  directed-wall remark have no field (proof data; the sign table is the accepted `GenericTableData.extreme_iff_alternating`); `hs` as a
  universally quantified hypothesis (R-LOC-2 (1)); the `{n}` implicit-vs-explicit binder difference of all siblings; one reviewer could not
  re-read the sibling modules (outside its allowed list) and closed the consumer question by the kernel check instead. Receipt
  `dev-check-rows177-178-183-accepted.json` (08:42Z).
- **Rows 178 `R:cv_theorem` and 183 `Bridge:theorem` — ACCEPTED 2026-09-19 08:39Z** through their staged one-liners, ported 08:08Z
  exactly as staged on 2026-09-16 in `work/drafts/cvtail/port/R178_183/` (the `<HH:MM>Z` header placeholders filled, the import of
  `RProof.ExtremeSelected` now resolving): `theorem RProof.cv_R : CV.hyp_R := cv_R_of_rows generic_selected extreme_pair_zero
  extreme_transport extreme_selected` (`RProof/CvR.lean`, 25 lines; `cv_R_of_rows` `RProof/RALedgers.lean:2354`, D-CVT-5, FR-R-178-1) and
  `theorem Bridge.sm_R : SM.hyp_R := SM.sm_R_of_cv_R RProof.cv_R` (`Bridge/SmRRow.lean`, 18 lines; `SM.sm_R_of_cv_R` `Bridge/SmR.lean`,
  B1-B4 pointwise; FR-B-183: BRIDGE.md §3 (19)-(21) verbatim, no new mathematics). Both have NO hypothesis and no R parameter; both have
  footprint `9`, as FR-R-178-2 / D-CVT-6 predicted (§4.3). Reviews `reviews/r-cv-theorem.json` (08:39:17Z; 6 non-blocking notes: the R6
  all-parameters form `∀ tp tm, 0 < tp → tm < 0 → X1 (E.curve tp) = X1 (E.curve tm)` — equivalent to the chamber form by the accepted
  CV:prop:chamberinv (ii) and implying it outright; `hn` and the G4 index hypotheses redundant binders derivable from `h3`; "changes sign
  at t = 0" read as `SignChanges`, the accepted def:event reading; the brief's provenance of the "R6" label corrected to the CV-DOM
  decision) and `reviews/bridge-theorem.json` (08:39:21Z; 9 non-blocking notes: the row states the CONSEQUENT of the printed implication
  with the antecedent discharged by row 178 — modus ponens, "formally stronger"; `C(P₊) = C(P₋)` at every pair of side parameters,
  equivalent by prop:C-chamber (`hyp_R_iff_base`); presupposition binders; the (T) clauses' total `edgeParameter` and `SignChanges`'
  `δ ≤ radius` inherited from B1/B3; the class "defined in SM11" = the frozen SM15 def:walls (T)). Receipt
  `dev-check-rows177-178-183-accepted.json` (08:42Z; 187 mapped, 44 270 audited).
- **Row 184 `SM:corner_laws_and_soft` — ACCEPTED 2026-09-19 13:26Z (the FINAL target).** Module `SM/CornerLawsAndSoft.lean` (86 lines),
  prepared 10:36Z from `work/drafts/cvtail/Wave1_Assembled.lean` 4231-4386 (`CyclicLawC`, `CornerLawsAndSoftData`,
  `corner_laws_and_soft_of` VERBATIM; pre-compiled without its final line) with edit A-22 (OPEN_ITEMS §A-22 / D-CM-3): the tail draft's
  `CInheritsData` / `CuspLawC` / `ReversalLawC` / `TrianglesC` copies REPLACED by `import SM.CInherits` (the comparison lane's FINAL
  12-field bundle; the three consumed fields `cusp_law`, `reversal_law`, `triangles` byte-identical Props, checked against
  `SM/CInherits.lean:24-51`), so `corner_laws_and_soft_of`'s text is unchanged; built 12:54Z once `SM.ComparisonRows` existed. The
  declaration: `theorem SM.corner_laws_and_soft : CornerLawsAndSoftData := corner_laws_and_soft_of Bridge.sm_R thm_C_S7 thm_C_soft
  (cor_C_inherits Bridge.sm_R)` — a structure with 0 parameters and 11 fields (§4.6); `#print axioms` = exactly the nine registered
  axioms, no `sorryAx` (executor's probe 12:57Z; the review's `kernel_check`; the checker 12:58Z / 13:28Z). Review
  `reviews/sm-corner-laws-and-soft.json` (13:25:50Z): 3 lenses `faithful`, 2 refuters "not refuted"; 6 non-blocking notes (§4.6, §5),
  one PROCESS note — the brief pointed the row-184 reviewers to `reviews/thm-C-S7.json` and `reviews/cor-c-inherits.json`, which did not
  yet exist during the concurrent workflow; they checked `CS7Data`, `CuspLawC`, `ReversalLawC`, `TrianglesC` directly against the printed
  thm:C-S7, thm:A-S4, cor:A-lawful, def:star and the accepted `ALawfulData` shapes and asked that the acceptance be recorded as
  contingent on rows 110/128's own reviews passing — which they did in the same workflow (13:25:40Z, 13:25:46Z) before the four rows were
  set accepted together (13:26Z). One FOOTPRINT note (strength lens): the kernel lists SIX literature axioms where TARGETS says "the five
  listed literature interfaces" — disclosed in §4.3.
- **Rows 127 `thm:comparison` and 128 `cor:C-inherits` — ACCEPTED 2026-09-19 13:26Z** as their one-liners `thm_comparison (hR : hyp_R) :
  ∀ n [NeZero n] hn P hP, cornerStateSum hn hP = amplitude P hP.1 hn := thm_comparison_of hR thm_C_S7 thm_C_soft` and `cor_C_inherits
  (hR : hyp_R) : CInheritsData := cor_C_inherits_of hR thm_C_S7 thm_C_soft` (`SM/ComparisonRows.lean`, 26 lines; signatures verbatim from
  `work/drafts/comparison/Comparison_Assembled.lean` 1009-1016; the `_of` theorems accepted-library since 2026-09-15). hyp:R is the EXPLICIT
  parameter `hR` (D-CM-2; policy mode `explicit_parameter`) — these two are the printed "Assume Hypothesis R" rows and the only accepted
  rows taking `hR`; inside row 184 it is discharged by `Bridge.sm_R`. Reviews `reviews/thm-comparison.json` (13:25:43Z; 4 non-blocking:
  A(P) at the fixed root 0 = the accepted `amplitude` with `A_lawful.root_independent`; labelled generic tuples instead of polygon classes
  — both sides descend, the polygon form exists as `thm_comparison_polygon_of`; `hyp_R` in the all-side-points form; presupposition binders)
  and `reviews/cor-C-inherits.json` (13:25:46Z; 10 notes: STRONGER — the extra field `root_values` C(P) = A_g(P) for every root g (the
  C = A substitution into cor:A-lawful's defining clause, FR-CM-13), genericity of every substituted argument ASSERTED in the conclusion
  (∃ hQ / ∧ Generic, the accepted `ALawfulData` convention), `CuspLawC` for EVERY simple cusp wall whose deletion satisfies (G1), threaded
  cusps included, with the cusp case b and the rotation identity rot(P_loop) − rot(P_no) = κ; the A-specific per-induced-root cusp sub-clause
  has no C analogue (FR-CM-9); `soft_theorem` in cor:A-lawful's ∃ hQ shape; a bookkeeping nit on the excerpt's line range 313-369 vs 313-372).

All of `RProof.extreme_selected`, `RProof.cv_R`, `Bridge.sm_R`, `SM.thm_C_S7`, `SM.thm_comparison`, `SM.cor_C_inherits`,
`SM.corner_laws_and_soft` are declared in `work/lean` under their FIXED names (`axiom-policy.json` `targets`), mapped and accepted;
D-F11 was never bent — each was mapped only once its premise was discharged.

### 3.5 `src:contact` and `hyp:R` — both accepted (unchanged)

`src:contact` (`SM.src_contact`, `SM/SrcContact.lean`; the fifth literature interface) was declared 2026-09-15 15:10Z and accepted
16:51Z (§2 line m97; §4.3). `hyp:R` unchanged from 2026-09-14 (accepted 15:45Z that day; `SM/HypR.lean`): a `def … : Prop` in the
all-sides form of the accepted prop:C-silent for the identical printed phrase (FR-HR-1; `HypRDiagonal` and `HypRBase` proved
equivalent via prop:C-chamber; FR-HR-2 simple triple walls only; FR-HR-3 `hn : 3 ≤ n`; FR-HR-8 no `axiom SM.hyp_R`); its CV
counterpart `CV:ax:R` is the accepted Prop definition `CV.hyp_R` (RProof/X1Rows.lean:124). Both hypotheses of the package are Prop
definitions; since 2026-09-19 both are PROVED as theorems — `Bridge.sm_R : SM.hyp_R` and `RProof.cv_R : CV.hyp_R` (§3.4) — and the
five literature interfaces are all declared, plus the author-authorised second declaration of lit:homfly.

### 3.6 Rows 76-80, 83, 93 — the certificate rows lane (2026-09-14 text, unchanged)

Certificate rows lane (design `work/drafts/frontrows/PLAN_FINAL.md`, statements frozen in `Statements_FINAL.lean`,
FR-8..FR-17, D-F7..D-F9): all eight certificate rows 76-83 and their consumer 93 are accepted; the front block (rows
73-94 minus the GAP-2 rows 91 and 94) is complete. The lane was ported incrementally as sorry-free modules (D-FR1),
each importing the previous one: `SM/FrontRowsW2.lean` (rows 81 `ng:circle`, 82 `ng:cusp-skein`; accepted 13:10Z),
`SM/FrontRowsW2S.lean` (the sweep block + `represent` + row 76 `SM.ng_commutation`), `SM/FrontRowsW3.lean` (leaves
`typeIII_site`, `typeI_move`, `crossedCusp_move`; rows 77 `SM.ng_front_I`, 79 `SM.ng_front_III`, 80 `SM.ng_deletions`),
`SM/FrontRowsW3b.lean` (leaf `typeII_move`, `certificate_laws`, `word_bound`; rows 78 `SM.ng_front_II`, 83
`SM.ng_local_front_bound`) and `SM/NgBound.lean` (row 93 `SM.fd_ng_bound := fd_ng_bound_of ng_local_front_bound`, recipe B of
`NGBOUND_PLAN.md`). Size: 14 666 + 8 601 + 13 267 + 3 367 = 39 901 lines for the four FrontRows modules (`wc -l`, 18:10Z),
plus 108 for `SM/NgBound.lean` (D-F9 predicted 17-23k for the lane; see §7 on the notes' "≈ 26.8k" figure). Axioms:
rows 76-80 std + `SM.lp_lm`; rows 83 and 93 std + `SM.lp_lm` + `SM.ng_finite_word` (the one declared use of the fourth
interface, as the `\status` lines predicted); the leaves `represent`, `typeI/II/III`, `crossedCusp_move` standard only.
Readings disclosed before the rows were stated and cited by the reviewers: FR-8 (the rows hold for PL realizations
`SM.realize` of closed oriented Rutherford words, not arbitrary fronts of ng:front-domain — the printed certificate
device, FR-5), FR-9/FR-10 (row 76: only jointly C^∞ families with fixed circle indexing count as deformations), FR-13,
FR-16, FR-NB-1..4 (rows 83/93: conditional on `F.IsRounding S`, no existence clause). The FR-8 fallback of D-F7 (a class
change on 76/83/93 if `represent` stalled) was NOT needed: `represent` was proved on the smooth class (15:30Z).
Record (AUTHOR_NOTES.md 2026-09-14): "Certificate rows wave 2 done … wave 3 launched — ~12:30Z"; "Sweep lane launched
(leaf `represent` → rows 76, 83) — ~13:30Z"; "Sweep lane done: `represent` PROVED, row 76 closed — ~15:30Z" (52 of 54
sweep leaves proved; the two unproved leaves were FALSE as stated, consumed by nothing, removed at port time — D-FR2);
"ng:commutation (row 76) ACCEPTED — ~16:25Z"; "Certificate rows wave 3a: U5 done, U6 wrapped with 2 of 3 leaves —
~16:55Z" (D-FR4: port the rows whose leaves are proved first); "Reassessment rule adopted; stagnation audit for row 78
(`typeII_move`) — ~17:00Z" (the bounded test: `typeII_move` proved by ~18:30Z, else rows 78/83/93 reported incomplete
with the exact remaining obligation); "Rows 77, 79, 80 ported — ~17:15Z"; "Row 78 audit outcome: `typeII_move` PROVED
within the bound — ~17:30Z" (D-FR5: the U6 version is ported, the independent U6b proof kept as cross-check);
"Rows 77, 79, 80 ACCEPTED — ~17:40Z"; "Rows 78, 83, 93 ported and mapped — ~17:50Z"; "Rows 78, 83, 93 ACCEPTED — the
certificate rows lane is complete — ~18:05Z". Reviews: 3/3 faithful and 2 refuters clean for each of the seven rows
(`work/reviews/ng-commutation.json`, `ng-front-I.json`, `ng-front-III.json`, `ng-deletions.json`, `ng-front-II.json`,
`ng-local-front-bound.json`, `fd-ng-bound.json`; reviewer inputs = the modules with every proof stripped).

## 4. The checklist of FINAL_REVIEW.md, item by item

### 4.1 The definitions denote the source objects

52 definition/convention rows are accepted with a review each (§2; complete since 2026-09-14, unchanged). Evidence per object:
**actual polygons** — `def:polygon` `SM.polygonData` (LabelledTuple n = ZMod n → ℝ × ℝ; reviews/def-polygon.json + countersignature),
`def:generic`, `def:crossings`, `def:regular`, `def:admissible`. **Connected-component chambers** — `def:chamber`
`SM.chamber_definition`: `chamber X = connectedComponent X` in `GenericPolygon n = Quotient (genericCyclicSetoid n)` =
𝓤_n/(ℤ/n) with the coinduced (quotient) topology, expanded to Mathlib primitives in reviews/prop-C-chamber.json and
its refuter; used unchanged by `prop:chambers`, `prop:A-chamber`, `prop:C-chamber`, and — through the `chamber : CChamberData` field
— by the final theorem. **Continuous wall germs** — `def:germ` `SM.wall_germ_definition` (SM.GermDefinition), `def:walls`, and the
germ-based hypotheses of `thm:C-S3` (`WallGerm.FlatAt`), `thm:C-S5`, `thm:C-S7` (`g.VertexEdgeAt M a`, the exhaustive dichotomy
`vertexEdge_bigon_or_sliding`), `prop:C-silent`, `hyp:R` (`g.TripleAt e f k`). **Independent supports, carriers** — `def:decomposition`,
`conv:selected-visits`, `lem:carriers`, `def:flat-carriers`/`cor:flat-carriers` (SM/FlatCarriers.lean), `CV:def:smoothing`,
`CV:def:wind`, `CV:def:pieces`, `CV:lem:carriers` on the accepted geometric carrier layer (CV-DOM decision option (C),
AUTHOR_NOTES ~02:20Z 2026-09-14, `work/drafts/cvdom/DECISION_FINAL.md`; disclosed: carriers are finite marked cycles, CV:lem:carrierword's
binder narrowing). **Local polynomials and records** — design decision `work/reports/design-decision-diagram-record-20260913.md`
(polygonal oriented link diagrams `Shadow`/`Diagram`, combinatorial `Record`, `Laurent₂ ℤ`), rows `def:positive-lift`,
`def:gauss-record`, `lp:core`, `rp:record-polynomial`, `lc:presentations`, `lp:split-circle`, `mp:*`, `def:adeg`,
`cf:def-turning`. **The full state sum** — `def:C` `SM.corner_state_sum_definition` / `cornerStateSum hn hP : ℤ`
(SM/CornerStateSum.lean, bundle field `state_sum` reproduces sm-3:1697-1698; reviews/def-C.json). No empty domain is
substituted: the reviewers checked non-vacuity where a bundle quantifies over a constructed class (CE-R11 witness in
`SM/CeRoundingNonVacuity.lean`; K-3/K-4 for row 90 argued, not kernel-checked — §5); for the final theorem the row-184 refuters checked
that `CornerLawsAndSoftData` has no retained hypothesis and that every field is stated on the accepted `cornerStateSum`. No definition
asserts a desired theorem: every C law is a theorem about `cornerStateSum`, not a field of a definition (TARGETS.md); the final bundle's
fields are the accepted row theorems themselves (§4.6).

### 4.2 Quantifiers, hypotheses and conclusions preserved; helper definitions expanded

Process (ACCEPT_CYCLE.md steps 4-6 as run here): the reviewers received only the SM15 source excerpt (for the R rows the printed
proof files, for row 183 BRIDGE.md §3, for row 184 TARGETS.md lines 1-29 with the cor:A-lawful excerpt), the row's Lean text with every
proof replaced by `sorry` (`work/reviews/<row>-reviewer-input-statement.lean.txt`, produced by `work/port/strip_proofs.py`) and the
definition modules; each review compares domain, quantifiers, hypotheses and conclusion clause by clause with helper definitions
expanded to primitives and records `stronger_than_source` / `weaker_than_source` / `discrepancies`; two adversarial refuters attack
the statement and re-run `#check` / `#print axioms` on scratch files. The statement hash binds the type and every local definition it
uses (DELIVERY_AUDIT.md defect 2), so a later helper change invalidates the review — all 191 hashes match the current audit (13:28Z;
re-checked at draft time). Disclosed deviations, all judged non-blocking and all recorded before the rows were stated: polygonal
readings of smooth diagrams (FR-1, FR-CP-1, CE-R1; rows 73, 74, 89-92, 97, 98); the word/PL layer as the printed certificate device
(FR-5, FR-8; rows 76-83, and 93 through 83); ℝ-indexed jointly smooth families with the smoothTransition clamp instead of [0,1] (CE-R2,
FR-CP-4/5; rows 89, 86-88); record-level carrying at the curl (FR-C1; row 98); the collar field (D-1; rows 89-91); the rounding record
theorem `isRounding_of_geomModel` supplying row 74's printed content (D-F6, `SM/FrontGeomModel.lean`); CV binders `hn : 3 ≤ n` /
`[NeZero n]` as presuppositions; CV:lem:carrierword's binder narrowing (round-2 unanimous); from 2026-09-15, the readings of §2 lines
91-176 (the descent axiom's ℝ-indexed families FR-LHD-2/FR-CP-5, the `HeightMarking` reading convention FR-1 on rows 91/94/162, the
normalised-orientation reading of clause (B) on rows 99/155, the quantified genericity of P_ε on row 112, the fixed R shape of rows
174-176); and, from 2026-09-19, the readings of the seven new lines (§2): the C-row convention "at every pair of side parameters"
instead of the two chamber values (rows 110, 127, 128, 183, 184 — equivalent by the accepted prop:C-chamber, `hyp_R_iff_base`), the R6
all-parameters form of `CV.hyp_R` (row 178; equivalent by CV:prop:chamberinv (ii)), the fixed R bundle shape of row 177 (`CompleteLocal`
on one side, `full_absent_on_complete` over every finset, `hs` as a hypothesis), the CONSEQUENT-only form of the bridge theorem (row
183), labelled generic tuples instead of polygon classes and A(P) at root 0 (rows 127/128), the asserted genericity of substituted
arguments and the extra `root_values` field (row 128), `CuspLawC`'s existential genericity vs `CS7Data`/`CSoftData`'s universal one
(row 184, FR-F-184-2). Strengthenings: 106 of the 168 reviews of 2026-09-14 list them (not re-derived here); 12 of the 16 reviews of
2026-09-15/16 and 6 of the 7 reviews of 2026-09-19 (all but `thm-comparison`) have a non-empty `stronger_than_source` array — printed
content made explicit or exports beyond print — none narrowing a conclusion. Weakenings of substance: none accepted; the F4 replacement
of `CV:ax:gausscode` is a recorded scope change (§4.3); the 2026-09-15 narrowings (row 162 to `TransverseKnot`, FR-FC-5; `src_contact`'s
Legendrian formulas for knots with generic fronts, FR-SC-2) are recorded readings; the `weaker_than_source` entries of 2026-09-19 (rows
110, 128, 184) name only presupposition binders (`hn : 3 ≤ n`, vacuous under `ContactSeparated`) and the def:germ side-point forms
(equivalent by prop:C-chamber) — no printed clause is dropped. **No narrowing was added on 2026-09-19**: the authorised FR-R-177-K
(G-02b) was not needed (§3.4).

### 4.3 Literature declarations exactly printed; no extra axiom, sorryAx or native_decide

**All five permitted interfaces are declared**, each as a single `axiom` in ∃-form over a field-named Prop structure of the
printed clauses: `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness` (`work/lean/SM/LinkInterfaces.lean`), `SM.ng_finite_word`
(`SM/FrontInterfaces.lean`) and — 2026-09-15 — `SM.src_contact` (`SM/SrcContact.lean:224`). In addition, on the author's
decision D-GAP2, **a sixth axiom constant `SM.lit_homfly_descent` is declared as the SECOND declaration of the interface
lit:homfly** (`SM/LitHomflyDescent.lean:37`), so `work/lean` contains six `axiom` declarations for five literature inputs.
TARGETS.md ("Its only unproved nonstandard inputs may be the five listed literature interfaces") is met in the sense the
author authorised: the sixth constant is a printed sentence of one of the five listed interfaces, not a sixth interface
(D-GAP2-2; confirmed on 2026-09-19 by G-06 "one literature label may carry several declarations" and G-08 "KEEP … as is"; disclosed
here as FR-R-178-2 / D-CVT-6 require). **DISCLOSURE for the final theorem:** the kernel's `#print axioms SM.corner_laws_and_soft`
lists SIX literature constants — `SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word,
SM.src_contact` — over the standard three; the row-184 strength reviewer recorded exactly this ("the kernel lists SIX literature
axioms — TARGETS says 'the five listed literature interfaces'"). A reader who counts constants rather than registry labels must read
the final theorem as resting on five literature interfaces plus one further printed sentence of lit:homfly admitted as an axiom by the
author's decision; nothing else is unproved.

**`SM.lit_homfly_descent : SM.AmbientIsotopyDescent`.** The sentence declared is exactly the last printed sentence of lit:homfly
(`blueprint/AXIOM_REGISTRY.md` lines 14-15 = `reference/SM/sm-3-statesum.tex` 920-921): **"Its value depends only on the oriented
link presented by D"**, for the map `D ↦ H_D(a,z)` of the first sentence, i.e. for the fixed witness `SM.homfly` of the accepted
`SM.lit_homfly` (whose own reading of that sentence is `HomflyClauses.descent` over `LinkEquiv`, design D2 — weaker, which was
GAP-2). It is read on the spatial vocabulary of the accepted rows 89-91: `AmbientIsotopyDescent` (`SM/ContactPathOfDescent.lean:177`,
a `def … : Prop` stated and statement-reviewed on 2026-09-14, `work/reviews/cp-finite-contact-path-conditional.json`) says that
along every jointly smooth family of oriented spatial embeddings (`SpatialFamily`, indexed by ℝ) whose two ends have ordinary
regular generic xz projections, `homfly` takes the same value on any polygonal `HeightMarking` readings of the two end diagrams.
Policy registration: `lean/axiom-policy.json` = `work/lean/axiom-policy.json`, `"literature"`, key `"lit:homfly (descent sentence)"`
→ `"SM.lit_homfly_descent"` (D-GAP2-2). Tool edit: `verify_bundle.py` enforced `set(policy['literature']) == {the five registry
ids}`; it now compares `{k.split(' ')[0] for k in policy['literature']}` with the five ids (the line carries the comment "author's
decision D-GAP2, 2026-09-15"), so the ceiling on literature INPUTS is unchanged (exactly five labels) while a second declaration
of an input is admitted under its own key (D-GAP2-2b; the one edit to a package tool in the whole execution; made permanent by G-06;
`tools/check_lean.py` untouched — its `allowed = policy['standard'] + list(policy['literature'].values())` already admits the new
value). Registry: the blueprint (frozen) still carries no sub-entry for the second declaration; the author authorised one (G-07) and it
is prepared as `work/port/docdebt/registry-sub-entry.patch` (7 lines under "## lit:homfly — AXIOM"), applied at the closing cycle
(<<ROW57: fill at acceptance — confirm the sub-entry is in `blueprint/AXIOM_REGISTRY.md` and the MANIFEST line refreshed>>).
Interface review against the registry text: `work/reviews/lit-homfly-descent.json` (3/3 lenses faithful, 2 refuters clean; 14:25Z
2026-09-15; inputs `lit-homfly-descent-reviewer-input-statement.lean.txt` = the axiom module, the frozen Prop file, the registry excerpt
`lit-homfly-registry-excerpt.md.txt`). Its disclosed readings, all judged non-blocking: STRONGER — FR-LHD-1, the clause is stated on a
jointly smooth family of EMBEDDINGS, so it bundles the isotopy-extension theorem (which the source proves itself at sm-3:3276-3312 for
this very use) with the literature sentence; the literal form `AmbientIsotopyDescentLit` and the proved split `AmbientIsotopyDescentLit
∧ IsotopyExtension → AmbientIsotopyDescent` are in the module; FR-1/FR-LHD-3, "X presents L" is record-level (`HeightMarking`), so the
axiom also asserts equal `homfly` for any two polygonal diagrams carrying the same signed O/U record of one regular generic projection.
WEAKER — FR-LHD-4, both ends must have `RegularGenericProjection` (the printed sentence covers every diagram); readings only; same
labelled circles, orientation- and label-preserving; smooth (C^∞) category only; FR-LHD-2, ℝ-indexed family (a [0,1]-isotopy enters
after a clamp); c = 0 vacuous. Truth: for the genuine HOMFLY-PT polynomial the axiom is true under the standing D2 premise (formal
Reidemeister moves + planar isotopy complete for PL link isotopy) already carried by `lp_lm_uniqueness`; it is not derivable from
`lit_homfly` alone — exactly the GAP-2 content. Axiom set of the constant itself: `[propext, Classical.choice, Quot.sound, SM.lit_homfly,
SM.lit_homfly_descent]` (its type mentions `homfly`). **Accepted rows whose footprint contains `SM.lit_homfly_descent` (21, from the
13:28Z audit; 14 on 2026-09-16):** 91 `cp:finite-contact-path` (std+H+HD+LM+LMU), and with the full set `9`: 94 `fd:contact`, 99
`cf:thm-carrierfloor`, 100 `thm:floor`, 103 `cb:singleton`, 105 `lem:corner-values`, 112 `thm:C-soft`, 122 `prop:anchor-values`, 155
`CV:thm:carrierfloor`, 162 `CV:ax:slbound`, 165 `CV:singleton_D_i`, 174 `R:generic_selected`, 175 `R:extreme_pair_zero`, 176
`R:extreme_transport`, and — new on 2026-09-19, as D-CVT-6 predicted, through `CV.carrierSlotFloor` ← `SM.cf_thm_carrierfloor.clauseC` ←
`SM.fd_contact` ← row 91 — 177 `R:extreme_selected`, 178 `R:cv_theorem`, 183 `Bridge:theorem`, and, through `thm_floor` (row 100) in
`thm_C_S7_of_floor` and `thm_C_soft_of_floor`, 110 `thm:C-S7`, 127 `thm:comparison`, 128 `cor:C-inherits`, 184 `SM:corner_laws_and_soft`.
So it now enters rows 177/178/183/184 (and 110/127/128) as well: **every final target except `prop:C-chamber`, `prop:C-silent`,
`thm:C-S3` and `thm:C-S5` depends on the author's reading.** No row accepted before 2026-09-15 depends on it.

**`SM.src_contact : ∃ r tb : (ℝ → E3) → ℝ, SrcContactClauses r tb`** (D-SC-1; registry `blueprint/AXIOM_REGISTRY.md` "src:contact —
AXIOM" = sm-3:3341-3365). The existential interface form: the literature's rotation number `r` and Thurston-Bennequin invariant
`tb` are never defined by the document, so they are existentially quantified functions `(ℝ → E3) → ℝ` and the four printed
formulas are the fields of `SrcContactClauses` — `rotation` r = (D − U)/2, `thurston_bennequin` tb = w − (D + U)/2,
`pushoff_self_linking` sl(T₊(L)) = tb − r for every positive pushoff circle of every pushoff annulus (rows 84/87's
`GenericFront.IsPositivePushoff`), `transverse_front_writhe` sl K = writhe of the front for a generic positive transverse front
(def:transverse-front). Fixed witnesses `SM.rot`, `SM.tb := Classical.choose …`, `src_contact_spec`. `SM.sl K := slCircle
K.circle` is the document's own fd:framed-linking number (row 88) at row 88's radius (D-SC-2), so the axiom has content relative
to an independent definition. **What is NOT constructed:** no contact-geometric `r` or `tb` — the axiom asserts nothing about them
beyond the two defining formulas on the front class (FR-SC-1; the ∃-form is PROVABLY equivalent to the substituted consequence
`sl(T₊) = w − D` on the Legendrian class ∧ `sl = w` on the transverse class, `src_contact_iff_consequence`, standard axioms); the
convention, D + U, provenance and scope sentences have no field (FR-SC-6/8); no transverse-isotopy class `T₊(L)` is formed (FR-SC-3).
Narrowings: Legendrian formulas for KNOTS whose front lies on ng:front-domain's class (FR-SC-2); real-valued quantities (FR-SC-10);
`slCircle T = 0` off its domain, never exercised (FR-SC-9). Consistency probe on file (D-SC-6). Interface review
`work/reviews/src-contact.json` (3/3, 2 clean, 16:51Z 2026-09-15). **Accepted rows whose footprint contains `SM.src_contact` (22;
15 on 2026-09-16):** `src:contact` itself and 161 `CV:ax:etnyre` (std+SC), and the twenty `9`-rows listed above (94, 99, 100, 103, 105,
110, 112, 122, 127, 128, 155, 162, 165, 174, 175, 176, 177, 178, 183, 184).

**"Allowed name but stronger type"** re-examined for the two 2026-09-15 constants: `lit_homfly_descent` is formally stronger than the
registry sentence in the two disclosed ways above (isotopy extension; record-level presentation) and weaker in six; every one was
matched to a printed sentence or to an accepted-layer convention by the three lenses and the two refuters, and the executor
recorded FR-LHD-1..4 before stating it (D-GAP2). `src_contact`'s four fields are the four printed formulas; nothing is stronger
(`stronger_than_source` empty), four narrowings disclosed. No axiom was added or changed on 2026-09-19 (the five `axiom` rows of the
map keep their `statement_sha256`). **Kernel evidence:** the current receipt (`dev-check-rows110-127-128-184-accepted.json` =
`stage-development.json`, 2026-09-19 13:28Z) passed with 191 mapped and 46 842 audited declarations; the audit's axiom sets over the
191 mapped declarations are exactly the ten patterns of §2's legend — subsets of {`SM.lit_homfly`, `SM.lit_homfly_descent`,
`SM.lp_lm`, `SM.lp_lm_uniqueness`, `SM.ng_finite_word`, `SM.src_contact`} over the standard three; no `sorryAx`, no
`Lean.ofReduceBool`, no other constant (recounted at draft time from the 13:28Z `declaration-audit.json`; mapped kinds: 176 theorems,
10 definitions, 5 axioms). `work/lean` contains no `sorry` (rule 3; the 2026-09-19 draft material with dead sorried declarations
stayed in `work/drafts/` and was deleted at port). The CV "axiom" rows 161 and 162 are theorems (`CV.ax_etnyre` from `SM.src_contact`;
`CV.ax_slbound` from `SM.fd_contact`), as `CV.ax_homfly` and `CV.gausscode_polynomial` were on 2026-09-14; `CV:ax:R` is a Prop
definition, not an axiom, and is now PROVED as `RProof.cv_R` (row 178). Closing-cycle caveat: the D-DOC-2 patches change comments
only (`check_comment_only.py`: 198 comment lines, 0 code lines), so no `statement_sha256` may change when they are applied — the
executor re-runs the checker afterwards and STOPS if one does (APPLY.md §3): <<ROW57: fill at acceptance — the post-patch checker
receipt and the statement-hash re-check>>.

### 4.4 The R parameter  (table regenerated 2026-09-19 13:4xZ; the column "explicit `hyp_R` parameter?" from `grep hyp_R` over the accepted row modules)

<!-- BEGIN:RTABLE -->
| obligation | policy name | status | declared? | module | axioms | explicit `hyp_R` parameter? | note |
|---|---|---|---|---|---|---|---|
| `R:localization` | `RProof.localization` | accepted | yes | RProof.Cores | std | none | accepted |
| `R:parity` | `RProof.parity` | accepted | yes | RProof.Cores | std | none | accepted |
| `R:exterior` | `RProof.exterior` | accepted | yes | RProof.X1Rows2 | std+H+LM+LMU | none | accepted |
| `R:fibre_partition` | `RProof.fibre_partition` | accepted | yes | RProof.Cores | std | none | accepted |
| `R:availability_0_1` | `RProof.availability_zero_one` | accepted | yes | RProof.X1Rows2 | std+H+LM+LMU | none | accepted |
| `R:generic_table` | `RProof.generic_table` | accepted | yes | RProof.Cores | std | none | accepted |
| `R:generic_selector` | `RProof.generic_selector` | accepted | yes | RProof.X1Rows | std+H | none | accepted |
| `R:generic_transport` | `RProof.generic_transport` | accepted | yes | RProof.GenericTransport | std+H+LM+LMU | none | accepted |
| `R:generic_selected` | `RProof.generic_selected` | accepted | yes | RProof.GenericSelected | 9 | none | accepted 2026-09-15 23:54Z (wave 2 of the moves-toolkit lane; last Prop proved by two independent routes); no R parameter |
| `R:extreme_pair_zero` | `RProof.extreme_pair_zero` | accepted | yes | RProof.ExtremePairZero | 9 | none | accepted 2026-09-15 18:39Z; from `CV.singleton_D_i` (165); no R parameter |
| `R:extreme_transport` | `RProof.extreme_transport` | accepted | yes | RProof.ExtremeTransport | 9 | none | accepted 2026-09-16 00:12Z (wave 2; weak-port replay D-RM-5, `wind = 0` split D-RM-6, corrected outer-carrier Prop D-RM-7); no R parameter |
| `R:extreme_selected` | `RProof.extreme_selected` | accepted | yes | RProof.ExtremeSelected | 9 | none | accepted 2026-09-19 08:39Z (wave 3d: residue = parity + identification; the non-kink question resolved in the VALUE form, kink case by flat subdivision — no event hypothesis; G-03 route (ii)); no R parameter |
| `R:cv_theorem` | `RProof.cv_R` | accepted | yes | RProof.CvR | 9 | none | accepted 2026-09-19 08:39Z; `theorem RProof.cv_R : CV.hyp_R` — NO hypothesis, no R parameter (the proved CV R theorem) |
| `Bridge:B1` | `Bridge.B1` | accepted | yes | Bridge.B1 | std | none | accepted |
| `Bridge:B2` | `Bridge.B2` | accepted | yes | Bridge.B1 | std | none | accepted |
| `Bridge:B3` | `Bridge.B3` | accepted | yes | Bridge.B3 | std | none | accepted |
| `Bridge:B4` | `Bridge.B4` | accepted | yes | Bridge.B4 | std+H+LM+LMU | none | accepted |
| `Bridge:theorem` | `Bridge.sm_R` | accepted | yes | Bridge.SmRRow | 9 | none | accepted 2026-09-19 08:39Z; `theorem Bridge.sm_R : SM.hyp_R` — NO hypothesis, no R parameter (the resulting SM R theorem) |
| `SM:corner_laws_and_soft` | `SM.corner_laws_and_soft` | accepted | yes | SM.CornerLawsAndSoft | 9 | none | accepted 2026-09-19 13:26Z; `theorem SM.corner_laws_and_soft : CornerLawsAndSoftData` — NO hypothesis; `triple : hyp_R` is a PROVED field (Bridge.sm_R), no R parameter retained (the unconditional final theorem) |
| `CV:ax:R` | `CV.hyp_R` | accepted | yes | RProof.X1Rows | std+H | none | accepted; the Prop definition `CV.hyp_R` (RProof/X1Rows.lean:124), consumed as the type of `RProof.cv_R` |
| `hyp:R` | `SM.hyp_R` | accepted | yes | SM.HypR | std+H | none | accepted; the Prop definition `SM.hyp_R` (SM/HypR.lean), the explicit parameter of 127/128 and the type of `Bridge.sm_R` |
| `thm:comparison` (conditional row, for comparison) | `SM.thm_comparison` | accepted | yes | SM.ComparisonRows | 9 | **YES: `(hR : hyp_R)`** (policy mode `explicit_parameter`) | accepted 2026-09-19 13:26Z; the printed 'Assume Hypothesis R' rows; discharged inside row 184 by `Bridge.sm_R` |
| `cor:C-inherits` (conditional row, for comparison) | `SM.cor_C_inherits` | accepted | yes | SM.ComparisonRows | 9 | **YES: `(hR : hyp_R)`** (policy mode `explicit_parameter`) | accepted 2026-09-19 13:26Z; the printed 'Assume Hypothesis R' rows; discharged inside row 184 by `Bridge.sm_R` |
<!-- END:RTABLE -->

Exposure, inspected on the declarations themselves (`grep -n "hyp_R\|hR"` over `SM/CS7.lean`, `SM/ComparisonRows.lean`,
`SM/CornerLawsAndSoft.lean`, `RProof/CvR.lean`, `Bridge/SmRRow.lean`, `RProof/ExtremeSelected.lean`; the executor's `#check` probe of
12:57Z; the reviewers' `#check` on scratch files): **the conditional comparison theorem exposes its R parameter** — `theorem
SM.thm_comparison (hR : hyp_R) : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P), cornerStateSum hn hP =
amplitude P hP.1 hn` (`SM/ComparisonRows.lean:17-20`; axiom-policy mode `explicit_parameter`), and so does `SM.cor_C_inherits (hR :
hyp_R) : CInheritsData` (:23); their library forms `thm_comparison_of` / `cor_C_inherits_of` likewise (FR-CM-7, FR-CM-17). **The proved CV
R theorem** `theorem RProof.cv_R : CV.hyp_R` (`RProof/CvR.lean:17`), **the resulting SM R theorem** `theorem Bridge.sm_R : SM.hyp_R`
(`Bridge/SmRRow.lean:15`) and **the unconditional final theorem** `theorem SM.corner_laws_and_soft : CornerLawsAndSoftData`
(`SM/CornerLawsAndSoft.lean:84`) have NO hypothesis of any kind — no R, lawful-quantity, corner-law or equivalent proof assumption; the
only occurrence of `hyp_R` in the final module is the FIELD `triple : hyp_R` of the bundle and the parameter of the conditional library
theorem `corner_laws_and_soft_of`, which the row theorem instantiates at `Bridge.sm_R`. `SM.hyp_R` itself IS declared and accepted (row
`hyp:R`, `work/lean/SM/HypR.lean`; audit kind `definition`, axioms std+H through `cornerStateSum`; reviews/hyp-R.json): a `def … : Prop` —
for every n ≥ 3, every wall germ `g` with `g.TripleAt e f k` (a simple triple wall, def:walls (T), FR-HR-2) and all side parameters `tp
tm`, `cornerStateSum` takes the same value on the two labelled side representatives — reading FR-HR-1 (all-sides form; `HypRDiagonal` and
`HypRBase` proved equivalent via prop:C-chamber); it is a hypothesis, never an axiom (FR-HR-8), and since 2026-09-19 a proved theorem's
type. The consumer chain is `SM.sm_R_of_cv_R : CV.hyp_R → SM.hyp_R` (B1-B4 pointwise, `Bridge/SmR.lean`, library) applied to
`RProof.cv_R := cv_R_of_rows generic_selected extreme_pair_zero extreme_transport extreme_selected` (`RALedgers.lean:2354`), exactly the
one-liners staged on 2026-09-16. In the CV lane the hypothesis is the Prop `CV.hyp_R` (RProof/X1Rows.lean:124; accepted row `CV:ax:R`,
form R6: for every simple RIII event, `X1 (E.curve t₊) = X1 (E.curve t₋)` for all `t₊ > 0 > t₋`), consumed as the *type* of the proved
`RProof.cv_R`, as the conclusion of `hyp_R_of_near_of_chamberinv` and `cv_R_of_rows`, and as the hypothesis of `SM.sm_R_of_cv_R`. Every
accepted R row — the eight of 2026-09-14, the three of 2026-09-15/16 and 177 of 2026-09-19 — exposes its parameters explicitly (`hn : 3 ≤
n`; the event hypotheses `h3 h4e h4f h4g hE`; the cross-wall crossing-set identification `hs` of R-LOC-2 (1) as a universally quantified
hypothesis of the cross-wall fields, never asserted; reviews/r-extreme-selected.json notes 1 and 4); none takes an R, lawful-quantity or
corner-law assumption — their axiom sets are `std` (four cores), `std+H(+LM+LMU)` through `CV.X1`/`homfly`, or `9` for the four rows
whose route passes through `CV.carrierSlotFloor` ← `SM.cf_thm_carrierfloor.clauseC` ← `SM.fd_contact` ← row 91, which is where `HD` and
`SC` enter the R lane (D-CVT-6; table). **No R-dependent result is imported:** the import lists of the row modules are `RProof/CvR.lean`
← `RProof.RALedgers`, `GenericSelected`, `ExtremePairZero`, `ExtremeTransport`, `ExtremeSelected`; `RProof/ExtremeSelected.lean` ←
`RProof.ExtremeSelectedUnits` ← `RProof.GenericTransportSw` (← `SM.Smoothing`, `SM.MarkedProducts`, `SM.SingleCrossing`, `CV.FullTwist`,
`RProof.GenericTransport`, `SM.BigonDeletion`, `RProof.RALedgers`), `RProof.ExtremeTransportUnits`, `SM.CBProducts`, `CV.SingletonDi`,
`SM.ZeroRotationSeed`; `Bridge/SmRRow.lean` ← `RProof.CvR`, `Bridge.SmR` — nothing downstream of `thm:comparison` or `cor:C-inherits`
(`SM.Comparison`, `SM.CInherits`, `SM.ComparisonRows`, `SM.CornerLawsAndSoft` are imported by no R or Bridge module; conversely
`SM/CornerLawsAndSoft.lean` imports `Bridge.SmRRow`, the one direction the design requires). `RProof/GenericTransport.lean` (row 173) is
unchanged; the trans-free copy is additive (§5 item 4).

### 4.5 R coverage of the printed domain; both orbits; B1-B4 — COMPLETE

Partition by outside support and availability: `R:fibre_partition` (exhaustion, disjointness, sizes 0/1/3) accepted.
Availability 0 and 1: `R:availability_0_1` accepted (summand transport stronger than the bare fibre identity).
Availability 3, generic orbit: `R:generic_table`, `R:generic_selector` (172), `R:generic_transport` (173, the RIII-wall
invariance G11 proved by an explicit polygonal RIII move) and `R:generic_selected` (174, the selected b/ac complementary-couple
identity through an actual constructed R-II deletion) accepted: **the generic orbit is complete.** Extreme orbit: `R:extreme_pair_zero`
(175), `R:extreme_transport` (176; the three singleton transports (2) with the sign branch (3)) and — since 2026-09-19 08:39Z —
`R:extreme_selected` (177, the extreme selected couple through the switched RIII on the trans-free configuration copy and the R-II
after smoothing in its value form, kink case by flat subdivision) accepted: **the extreme orbit is complete.** Exterior factor without
division: `R:exterior` accepted (base-row representative, printed full-availability binder kept). Localization and parity warrants:
`R:localization`, `R:parity` accepted (std axioms only). So the printed simple, transversal, forced-bundle domain is covered in every
availability case and in both graph orbits, and `RProof.cv_R` IS assembled from the four row theorems (row 178, `cv_R_of_rows`): **the
coverage is complete.** B1-B4 (`Bridge/B1.lean` = B1+B2, `B3.lean`, `B4.lean`; reviews/bridge-b1.json … bridge-b4.json) compare the SM15
and CV conventions clause by clause (B2 under sorted naming with the unsorted case recovered; B4 = the pointwise dictionary `X₁ = C` on
SM-generic polygons through the accepted `geo*_eq_generic` agreement lemmas, `SM/GeoCarrierAgreement.lean`), with no assumed equality of
generic loci: the agreement is proved on the accepted definitions (CV-DOM (C)); `Bridge.sm_R` (row 183) is `SM.sm_R_of_cv_R RProof.cv_R`,
the displayed (19)-(21) of BRIDGE.md §3 applied to the proved antecedent.

### 4.6 Clause table for `SM.corner_laws_and_soft`  (the final declaration IS declared and accepted; one line per field of `CornerLawsAndSoftData`)

`theorem SM.corner_laws_and_soft : CornerLawsAndSoftData := corner_laws_and_soft_of Bridge.sm_R thm_C_S7 thm_C_soft (cor_C_inherits
Bridge.sm_R)` (`work/lean/SM/CornerLawsAndSoft.lean:84-85`; mapped row `SM:corner_laws_and_soft`, accepted 2026-09-19 13:26Z;
`statement_sha256 47469f91…`; review `reviews/sm-corner-laws-and-soft.json`). **The declaration has NO hypothesis** (a structure with 0
parameters, kernel-checked by the three lenses and both refuters on scratch files); its `#print axioms` is exactly the nine registered
axioms. Every field is stated on the source `C` = `cornerStateSum hn hP` of the accepted `def:C`; `triple : hyp_R` is a PROVED field
(discharged by `Bridge.sm_R`, row 183) — **no R parameter is retained anywhere in the row.** Field by field:

| field : type | checklist clause | accepted row it comes from (review file) | how it enters `corner_laws_and_soft_of` |
|---|---|---|---|
| `chamber : CChamberData` | Chamber constancy | `prop:C-chamber` = `SM.prop_C_chamber` (SM/CChamber.lean; reviews/prop-C-chamber.json; accepted 2026-09-14) | `chamber := prop_C_chamber` |
| `silent : CSilentData` | Silence — both wall types (E) and (C) as printed | `prop:C-silent` = `SM.prop_C_silent` (SM/CSilent.lean; reviews/prop-C-silent.json; 2026-09-14) | `silent := prop_C_silent` |
| `flat : CS3Data` | Flat deletion jump — the actual deletion `deleteVertex` and the side sign | `thm:C-S3` = `SM.thm_C_S3` (SM/CS3.lean; reviews/thm-C-S3.json; 2026-09-14) | `flat := thm_C_S3` |
| `vertex_edge : CS7Data` | Vertex-edge jump — both bigon branches and sliding (`VertexEdgeAt` = bigon ∨ sliding, `vertexEdge_bigon_or_sliding`), actual children λ₁ λ₂, sign `s = contactSign` | `thm:C-S7` = `SM.thm_C_S7` (SM/CS7.lean + SM/CS7Units.lean; reviews/thm-C-S7.json; **2026-09-19 13:26Z**) | `vertex_edge := h7` at `thm_C_S7` |
| `triple : hyp_R` | Triple invariance — `hyp:R` after discharging it with the proved R/bridge theorem | `Bridge:theorem` = `Bridge.sm_R : SM.hyp_R` (Bridge/SmRRow.lean; reviews/bridge-theorem.json; **2026-09-19 08:39Z**) ← `R:cv_theorem` = `RProof.cv_R` (RProof/CvR.lean; reviews/r-cv-theorem.json) ← rows 174/175/176/177 | `triple := hR` at `Bridge.sm_R` — a PROVED field; `hyp:R` (`SM.hyp_R`, reviews/hyp-R.json) is the accepted Prop it has as type |
| `cusp : CuspLawC` | Full cusp jump on the source domain — the deletion satisfies G1 (`cusp_deletion_generic`), threaded cusps included; `cor:A-lawful`'s form | `cor:C-inherits` = `SM.cor_C_inherits` (SM/ComparisonRows.lean, bundle SM/CInherits.lean; reviews/cor-C-inherits.json; **2026-09-19 13:26Z**), field `cusp_law`; `cor:A-lawful` = `SM.A_lawful` (reviews/cor-A-lawful.json; 2026-09-14) is the template | `cusp := hinh.cusp_law` at `cor_C_inherits Bridge.sm_R` |
| `empty_cusp : CS5Data` | Empty-cusp zero (the direct result retained) | `thm:C-S5` = `SM.thm_C_S5` (SM/CS5.lean; reviews/thm-C-S5.json; 2026-09-14) | `empty_cusp := thm_C_S5` |
| `soft : CSoftData` | Soft theorem — every admissible direction/attachment-sign sector incl. zero sectors (`SoftAdmissible`), `∃ ε₁ > 0, ∀ ε < ε₁` | `thm:C-soft` = `SM.thm_C_soft` (SM/CSoft.lean; reviews/thm-C-soft.json; 2026-09-15 20:25Z) | `soft := hs` at `thm_C_soft` |
| `reversal : ReversalLawC` | Descent and normalization — the reversal identity inherited with `cor:A-lawful` | `cor:C-inherits` field `reversal_law` (reviews/cor-C-inherits.json); A-level source `prop:A-reversal` (accepted) | `reversal := hinh.reversal_law` |
| `cyclic : CyclicLawC` | Descent and normalization — the cyclic identity (`C` well defined on def:C's cyclic quotient: `cornerStateSum hn (genericShift a P).2 = cornerStateSum hn P.2`) | `def:C` = `SM.corner_state_sum_definition` (reviews/def-C.json) through the accepted library lemma `cornerStateSum_genericShift` (SM/CornerPolygon.lean); the A-level source `thm:mycyclic` (accepted) | `cyclic := fun _ _ hn P a => cornerStateSum_genericShift hn a P` |
| `triangles : TrianglesC` | Descent and normalization — the triangle normalizations inherited with `cor:A-lawful` | `cor:C-inherits` field `triangles` (reviews/cor-C-inherits.json); A-level sources `thm:root-indep-proof`, `thm:uniqueness`, `cor:A-lawful` (accepted) | `triangles := hinh.triangles` |

The reviewers' non-blocking notes on the bundle (reviews/sm-corner-laws-and-soft.json, `discrepancies` / `stronger_than_source` /
`weaker_than_source`), quoted: "the side values C(P+), C(P-), C(P_right), C(P_left), C(P_no), C(P_loop) are rendered at every pair of
germ side parameters (hyp_R, CSilentData, CS7Data, CS5Data, CuspLawC) or at parameters below an existential delta (CS3Data:2485-2487)
rather than as def:germ chamber values; equivalent under the accepted def:germ + prop:C-chamber, disclosed in the accepted rows'
reviews"; "CS7Data quantifies the genericity of the two halves universally (`∀ h₁ h₂`) and CSoftData that of P_ε (`∀ hQ`) instead of
asserting them; `vertex_halves_children` and `CSoftData.exists_generic` supply the witnesses, so no content is lost; CuspLawC by contrast
asserts the deletion's genericity existentially, matching the printed domain check" (FR-F-184-2); "cor:A-lawful's text … never uses the
word 'cyclic'; TARGETS line 21 commissions a 'cyclic' identity, and `CyclicLawC` renders it as def:C's invariance under the cyclic
relabelling `genericShift`, the natural C analogue (the A-side root-independence has no C counterpart and is correctly not a field)";
STRONGER: "`cusp : CuspLawC` also asserts the uniqueness of the cusp case `b` and the rotation-number identity rot(P_loop) − rot(P_no) =
κ; both are printed content of thm:A-S4 … the same shape is in the accepted `ALawfulData.cusp_law`"; WEAKER (form only): "as bare
formulas, `flat : CS3Data` asserts the flat identity only for side parameters below some delta > 0, and `empty_cusp` / `triple` / `silent`
/ `vertex_edge` / `cusp` state their identities at the germ's own side points rather than for every polygon of the two chambers;
equivalent to the printed chamber-value statements via the accepted prop:C-chamber (`chamber : CChamberData`, itself a field of this
bundle) and def:germ". The checklist's warning — "A proof for an empty cusp or one soft sector is not the full target" — is met: `cusp`
covers every simple cusp wall whose deletion satisfies (G1) including threaded cusps (no emptiness hypothesis, FR-CM-9/9′), `soft` every
admissible sector including zero sectors (FR-CC-12), `vertex_edge` both bigon branches and sliding (FR-CC-7).

### 4.7 The conclusion concerns the source C

Every accepted C row — the 2026-09-14 rows, the 2026-09-15 rows `cb:singleton`, `lem:corner-values`, `thm:C-soft`, `prop:anchor-values`,
and the 2026-09-19 rows `thm:C-S7`, `thm:comparison`, `cor:C-inherits`, `SM:corner_laws_and_soft` — is stated on `cornerStateSum hn hP`
of the accepted `def:C` for `P : LabelledTuple n`, `hP : Generic P`, `hn : 3 ≤ n` (reviews/prop-C-chamber.json clause 1; thm-C-S7,
thm-comparison, cor-C-inherits, sm-corner-laws-and-soft likewise — the row-127/128 reviewers: "labelled generic tuples … both sides
descend"; FR-CC-13: C on labelled tuples, the quotient descent is the consumer's business), with wall data from `def:germ`/`def:walls` and
deletions from `def:deletion-halves`/`def:induced-roots`; no row abstracts C into "a function with the laws" — `CornerLawsAndSoftData`'s
fields are the accepted C theorems' own bundle types (`CChamberData`, `CSilentData`, `CS3Data`, `CS7Data`, `CS5Data`, `CSoftData`) and
`CInheritsData`'s C-shaped laws, each mentioning `cornerStateSum`. Arguments at which C is evaluated are generic by construction or by an
asserted witness (side points of germs; `deleteVertex` under the printed n ≥ 4 / G1 conditions; the cusp deletion generic by
`cusp_deletion_generic`, asserted as `∃ hQ` in `CuspLawC`; the halves λ₁, λ₂ by `vertex_halves_children`; P_ε by `exists_generic`). The
soft theorem over every admissible sector exists as the accepted `SM.thm_C_soft`; the full-target statement over all cusps exists as the
accepted `SM.cor_C_inherits` (its `cusp_law`); the final `SM.corner_laws_and_soft` exists, is declared, mapped, kernel-checked and
reviewed (§3.4, §4.6). The comparison `C = A` (row 127) is conditional on `hyp_R` as printed and is NOT a field of the final theorem
(TARGETS commissions the C laws, not the comparison); `root_values` inside row 128 carries the same content under the same hypothesis.

### 4.8 Certificates; 4.9 the stage check

`EXECUTION.json` commissions no computation certificates in this focused package (`"certificates": []`); the "certificate rows"
76-83 are source lemmas of sm-3 (Rutherford/Ng front words), all accepted since 2026-09-14 (§3.6), not external certificates, and no
`native_decide` or external data enters the library (the 13:28Z audit: no `Lean.ofReduceBool` anywhere).

**Stage check (4.9).** NOT yet run at draft time. The last `--all` run is the 2026-09-16 00:32Z FAIL naming the eight then-pending rows
(`work/checks/stage-all-check-20260916-0032.log`; `work/checks/stage-1.json` still `{"passed": false, "stage": 1, "state": "checking"}`
from 00:33Z that day); `tools/progress.py` accordingly prints "Stage 1: not established by a current checker receipt". The closing cycle
(D-DOC-2; AUTHOR_NOTES 10:37Z; STATUS 13:26Z), in order, once row 57 is in (or, if row 57 stalls, at the build cycle after the last
accepted port): (1) apply the 11 comment-only doc-debt patches + the G-07 registry sub-entry (`work/port/docdebt/APPLY.md`, `patch -p0`,
dry-run first; `check_comment_only.py` before and after; a near-full rebuild because patches 07-09 touch root modules); (2) `lake build`;
(3) `python3 tools/check_lean.py work/lean` (development) and `python3 tools/check_lean.py work/lean --all` (the single focused stage;
also `--stage 1`) — every accepted row's `statement_sha256` must be unchanged; (4) `python3 work/port/refresh_manifest.py` for
`FINAL_REVIEW.md` (this file), `blueprint/AXIOM_REGISTRY.md` and any other manifested file touched; (5) `python3 verify_bundle.py`;
(6) `work/delivery/refresh.sh` (last refreshed 2026-09-16 02:33Z: its `FINAL_REVIEW.md`, `AUTHOR_NOTES.md`, `receipts/` (156 files),
`reviews/` (868 files) are that state); (7) the final checkpoint tarball (the author's definition of done, D-AUTH §3). **Result:**
<<ROW57: fill at acceptance — the closing `--all` run's last line verbatim (expected "checker passed: True | mapped 192 | audited N" if
row 57 is accepted; else FAIL naming `lem:gauss-two-discs`), its log and receipt names (`work/checks/stage-1.json`,
`stage-all-check-<date>.log`), the development receipt after the patches (mapped / audited), the MANIFEST refresh, the `verify_bundle.py`
line, `refresh.sh`, the tarball name and sha256>>. What binds the accepted state at draft time is the development receipt
`work/checks/dev-check-rows110-127-128-184-accepted.json` (13:28Z: passed=true, `stage: null`, `stage_accepted: false`, 191 mapped,
46 842 audited; byte-identical to the current `work/checks/stage-development.json`). Its `bundle_sha256` binds the 2026-09-16 root
`FINAL_REVIEW.md` (sha256 `1373130e…`, the MANIFEST line), so the executor re-runs the development checker after this review replaces the
root file, refreshes the MANIFEST line, re-runs `verify_bundle.py` and refreshes `work/delivery/` so that the delivered receipt binds the
delivered bytes; a receipt older than that edit is evidence about its own time only. **The single focused stage is <<ROW57: fill at
acceptance — COMPLETE (all 192 rows accepted, `--all` passed) / INCOMPLETE (reported as such, CLAUDE.md rule 9)>>.**

## 5. Remaining gaps (honest list)

1. ~~**GAP-2**~~ — **closed on 2026-09-15 by the author's decision D-GAP2**, not by a proof, and KEPT on 2026-09-19 (G-08): the
   missing clause `SM.AmbientIsotopyDescent` is asserted by the registered axiom `SM.lit_homfly_descent` (second declaration of
   lit:homfly; §4.3). Twenty-one accepted rows — including every R row of the extreme orbit, `RProof.cv_R`, `Bridge.sm_R`, `thm:C-S7`,
   `thm:comparison`, `cor:C-inherits` and the final theorem `SM.corner_laws_and_soft` — depend on it. The interface review judged it a
   faithful reading of sm-3:920-921 with the disclosed strengthening FR-LHD-1 (isotopy extension bundled) and six narrowings; a reader
   who does not accept the author's reading should treat those twenty-one rows, the final theorem among them, as "proved modulo
   Reidemeister's theorem for smooth isotopies + isotopy extension", exactly the 2026-09-14 label. TARGETS.md's "five listed literature
   interfaces" vs the kernel's six literature constants is disclosed in §4.3 and was noted by the row-184 reviewer.
2. **Row 57 `lem:gauss-two-discs`** — <<ROW57: fill at acceptance — either "accepted <time>; no gap" with its axiom set (expected standard
   only) and the three rule-3 corrected internal sub-leaves + the rename disclosed (D-TD-2, D-TD-3, FR-TD-15), or the honest open state
   (leaves, sizes, obligation) and the consequence: `--all` FAIL on this one row, stage INCOMPLETE>>. At draft time: un-deferred, statement
   frozen with readings FR-TD-1..14 (§3.2), 82 of 92 skeleton leaves closed (wave 1: 62; wave 2 so far: U6 8, U7 7, U9 5), no literature
   axiom in any closed leaf, U5 (2 leaves) and U8 (8 leaves) in flight. No accepted row depends on row 57 (D-ER1; `corner_values_i`); the
   blueprint edges 57 → 104 and 57 → 105 stay unrealised by the proof routes (blueprint frozen).
3. **Closing-cycle work not done at draft time** (§4.9): the 11 comment-only documentation patches (`work/port/docdebt/`: E-01, E-02,
   E-05, E-06, E-07, E-08, E-10, E-11 ×2, E-19; 67 files, 198 comment lines, 0 code lines, verified by `check_comment_only.py`) and the
   G-07 registry sub-entry — AUTHORISED (G-05, G-07), PREPARED 06:06Z, deferred by D-DOC-1 and then D-DOC-2 to the LAST build cycle so
   that the near-full rebuild they force does not run under a dozen live unit compiles; `check_lean.py --all`; the MANIFEST refresh;
   `verify_bundle.py`; `work/delivery/refresh.sh`; the final tarball. Until they are applied the docstring debts of §5 item 5 below
   stand as written. <<ROW57: fill at acceptance — mark each as done with its receipt/log>>.
4. **Library-interface findings — literal fields unrealisable or false as stated, KEPT by the author (G-04 "KEEP the literal fields and
   the weak replays. No edit to accepted modules"), closed by weak replays or corrected forms WITHOUT editing the accepted library:**
   - **D-RM-5 (row 176, `est_PortData.port`, `RProof/RALedgers.lean:878`)**: UNREALISABLE as stated (an RII chain cannot cross the wall);
     rendered by the WEAK port form `est_port_weak` (∃ D₀′, RII-chain ∧ `homfly D₀′ = homfly D₀`), proved from a constructed R-II
     deletion; the accepted row 176 closes through the `s176_` / `r176_` replays; the row statement untouched.
   - **D-RM-6 (row 176, `est_PortData.rot / alt₁ / alt₂`, RALedgers.lean:903-906)**: FALSE as stated without `wind(S) ≠ 0`; corrected
     forms under `wind ≠ 0` plus the `wind = 0` split (both row terms vanish there); the literal fields stay unused.
   - **D-RM-7 (row 176, draft Prop `r176_outer_carriers_L`)**: FALSE in its second disjunct; corrected two-sided form proved; a draft
     artefact.
   - **Row 174 (R174_ASSEMBLY_REPORT §8)**: the ledger's `σ` is orientation-dependent while the `gsc_Ledger` / `gsc_moves` docstrings
     read it as `crossingSign ℓ₁ ℓ₂`; `s174_hrec_prop` provable only at the ledger's binding `q′ = W.τ qAB`, used exactly there. No
     AUTHOR_NOTES entry records it (E-14); recorded here.
   - **Row 177 (`esc_MoveData.rii_after_smoothing`, C-03)**: ∀ oriented smoothings unrealisable as stated → `esc_rii_after_smoothing_weak`;
     on 2026-09-19 the obligation was consumed in its HOMFLY VALUE form (`w3dk_rii_value_sites`) with the kink case by flat subdivision;
     `esc_` interface and ledger replayed by extension inside `RProof/ExtremeSelectedUnits.lean` (RALedgers untouched).
   - **`RProof.G11_Config.trans` (A-177-1, C-04)**: the accepted configuration type carries `trans : ¬ IsAlternating …`
     (`RProof/GenericTransport.lean:125`), FALSE on the K3 side of row 177, so the 1 056 accepted `G11_Params` declarations cannot be
     instantiated at a 177 site; the accepted type OVER-SPECIFIES what its proofs use. The author authorised either dropping the field
     or porting the additive copy (G-03); **route (ii) taken**: `RProof/GenericTransportSw.lean` (7 845 lines) re-derives 905 of the 908
     configuration-dependent declarations trans-free; the accepted module is untouched and the duplication is a permanent feature of the
     library (an accepted-module rewrite would need the author to grant it and a re-review; not taken).
   - **Corner RET rule-4 defect (C-05)**: `s7b_SlidingTransport.ret` (accepted `SM/CornerChainUnits.lean:3934`) is FALSE on the leg-M
     side; the corrected `s7r_SlidingTransport'` is proved and is what `SM/CS7Units.lean` consumes (S1′ `s7u_box_ret'`); the accepted
     structure keeps its literal field, documented by the prepared patch 06 (E-08: a CAUTION in the docstring; comment-only). The false
     box `s7q_box_ret` and its consumers were deleted at port.
   - **Row 110 wave-5/6 draft boxes (rule 3, 2026-09-19)**: BR's `w5b_box_interlacingTurnData` / `w5b_box_noninterlacingTurnData`
     (stated for every side parameter without a radius — not derivable as stated), `w5b_box_curlData` (from `hloc ht` alone — not
     derivable; the corrected `w6k_box_curlData` adds the six radius facts the consumer carries), ROW's `w5r_box_branch` (no selector
     hypothesis) and `w5b_box_returnedData` (no contact-parameter facts): all restated under radii / the selector and the as-stated boxes
     dropped at port as dead draft material (PORT_REPORT §2). ROT's brief phrase "in principalTurn form" was not a reading of the declared
     box, so the needed Prop `w6r_box_centreCorners` was stated exactly and then proved (CC). None of these is a row or library statement.
   - **Row 177 wave-3d (rule 3, 2026-09-19)**: `w3cs_not_kink_site` FALSE as stated (the monogon e → e+1 → e+2 = f cut by g is a genuine
     177 configuration); `w3bi_bigon_pair`, `w3bi_rii_sites` false in the kink configuration; `w3bi_knot_after_two` /
     `w3bi_three_components` / `w3bi_esc_outer` not provable as stated (relational smoothings): all DELETED from the assembly and the
     port, superseded by the record-clause `w3ck_` chain and the VALUE form. The four j = 2 bigon sub-leaves stay restated with the
     non-kink hypothesis and are used only in the non-kink branch. No kernel counterexample was built for any of these (draft leaves,
     not row statements; `work/repairs/` not triggered).
   - **Row 57 (rule 3, D-TD-2, 2026-09-19)**: `U3_isPositivePLFromPlane_inv` (false for L ≤ 0), `U4_polygonImage_ear` (kernel-checked
     counterexample, §3.2), `U5_exists_ear_homeo` (false for a reflex ear) — internal skeleton helpers corrected without touching the
     row statement; plus the rename D-TD-3 (`embeddedPolygonImage`, FR-TD-15). <<ROW57: fill at acceptance — confirm these are the
     disclosed items of the row-57 review>>.
   - **Moves toolkit `BigonData.hk : j + 3 ≤ k`** stronger than needed (C-11), satisfied at every site; **two textually identical
     `IsPushoffAnnulus` / `IsPositivePushoff` definitions** (rows 84/87, C-12; `src:contact` uses row 87's); **library gap** — existence of
     a polygonal `HeightMarking` reading is not a library theorem, rows 91/94/162 conditional on `Nonempty (HeightMarking …)` (C-13);
     **`lem:corner-values` (i)** "embedded" as the gloss `carrierCrossingCount = 0` (C-14, FR-CC-4); **row 155's statement file** carries
     library material consumed by 165/174/176/177 but reviewed under no row (C-15). All carried over from OPEN_ITEMS §C, unchanged.
5. **Documentation debts (comment-only; all PREPARED as patches, none APPLIED at draft time — §5 item 3).** `SM/ContactPathOfDescent.lean`
   docstrings still call `AmbientIsotopyDescent` "a def : Prop, not an axiom" (E-01; patch 01) and carry stale tex locators (E-02; patch
   02: descent sentence 3310-3312, hand isotopy-extension 3276-3312, etc.); `SM/FdContactStatements.lean` locators (E-05; 03); the
   `thm-C-soft` proof locator "992-1147" → "993-1147" in four places (E-06; 04); `RProof/GenericSelected.lean` "three branches" (two
   fields) and "the six literature interfaces" (six constants, five interfaces) (E-07; 05); the `s7b_slidingMark` / `s7b_SlidingTransport`
   docstrings wrong for the leg-M side (E-08; 06); the four D2 sentences "no sixth axiom (is admitted)" in `ContactPathOfDescent`,
   `LinkMoves`, `LinkInterfaces`, `CV/Axioms` (E-10; 07); the stale headers of `FlatCarriersDefs` ("proofs are `sorry` … when the prover
   units finish"), `Bridge/SmR`, `LinkLaurentRing:80-81`, `LinkInterfaces 39-41/181-182`, `X1Rows3` (E-11; 08) and the 55 "sorry-free" /
   "no sorry" header phrases (E-11; 09, optional); `work/drafts/floor/PLAN_FINAL.md` §4's stale axiom expectation (E-19; 10); the registry
   sub-entry (E-16/B-05/G-07). Items judged NOT comment-only were left out with reasons (APPLY.md §5: frozen review inputs, JSON data,
   reports). New 2026-09-19 documentation items: the port headers of the 9 new modules stamp "Ported HH:MMZ 2026-09-19 from <draft>";
   `SM/CS7Units.lean` keeps 27 reworded docstrings and 4 `set_option linter.unusedSectionVars false in` lines; `W6_ASSEMBLY_REPORT_B.md`
   §8.7 notes the port header names `W6_Assembled_B.lean`; the row-128 statement header cites "313-372" where the excerpt file is
   "313-369" (cosmetic; the review's bookkeeping note).
6. **Reviews are AI reviews only** (STATE_OF_WORK §4): all 191 accepted rows and the two interface declarations of 2026-09-15 were reviewed
   by Claude Code subagents of the same model family as the implementer (claude-fable-5-1); the 23 rows accepted since 2026-09-14 had one
   workflow each (three lenses + two refuters, proof withheld), no second session, no countersignature by a separate session; the 39
   handover rows keep their 2026-09-13 countersignatures. Disclosed breaches of proof-withholding: a refuter of row 175 read the one-line
   proof term at `RProof/ExtremePairZero.lean:85`; a refuter of row 110 printed four proof-local `have : NeZero …` lines of
   `SM/CS7Units.lean` by `grep` (no statement text or proof structure read; nothing relied on). The row-184 reviewers were pointed at two
   review files that did not yet exist (concurrent workflow) and checked the field types against the printed statements instead
   (§3.4). **The author decided (G-10) that human review of the AI-only verdicts is not required for completion and is arranged
   separately; no human has read any review.**
7. **Strengthenings and weakenings the reviewers flagged on 2026-09-19** (all non-blocking; the full lists are the review files' arrays,
   §2): row 177's `couple` hypothesises `CompleteLocal` on side t only and `full_absent_on_complete` holds for every finset (trivially
   true, proved unconditionally); row 178 asserts the X₁ equality at every positive and every negative parameter (implies the printed
   chamber form outright) and carries redundant index binders derivable from `h3`; row 183 asserts `SM.hyp_R` unconditionally (modus
   ponens on the proved antecedent) and at every pair of side parameters; row 110 at every pair of side parameters, with `hn : 3 ≤ n`
   vacuous under `ContactSeparated`, the halves' genericity as universally quantified witnesses; row 127 on labelled generic tuples with
   A(P) at root 0; row 128's extra `root_values` field, the asserted genericity of every substituted argument, `CuspLawC` for every (G1)
   cusp wall with the cusp case b and the rotation identity, the A-specific per-induced-root sub-clause without C analogue; row 184's
   `cusp` with the printed thm:A-S4 content, its `flat` below an existential δ, its `cyclic` as `genericShift` invariance. Carried over
   unchanged: the 2026-09-15/16 items (row 122's anchor superset, row 175's all-parameter fields, row 165's every-CV-generic-polygon form,
   rows 99/155's normalised orientation, row 100's `z_parity`, ℝ-indexed families, the `HeightMarking` conditionality of 91/94/162, row
   162's `TransverseKnot`, `src_contact`'s generic-front knots, row 112's quantified genericity, row 105's gloss, the fixed R shape).
8. **The R lane's weak-form readings and the kink route (library and proof routes, not row statements):** D-RM-2 replaced two
   unrealisable D-F11 interface Props by weak forms (`est_port_weak`; `esc_rii_after_smoothing_weak`) with the old Props kept as
   recorded; row 177's proof consumes the R-II-after-smoothing obligation only through its HOMFLY VALUE form and, in the kink pattern
   (where the printed bigon move does not exist), reaches the same value identity by a flat subdivision of the one-component lift — the
   printed proof's bigon step is REPLACED there, disclosed in the review record as a proof-route note; the 110 bigon branch avoids the RI
   curl deletion by reading the curl inside `knotRestrict` (`two_component_row_of_recordIso`, `curl_block_value`; on 2026-09-19 the curl
   component's value and writhe by the record-level theorem `w6k_P_eq_of_curl`, no cb:products call). The row statements of 174/176/177
   (frozen `RowShape` bundles) and of 110 (frozen `CS7Data`) are unaffected; whether the weak forms and the subdivision suffice is proved,
   not assumed (the accepted row theorems themselves, sorry-free on the nine registered axioms).
9. **Non-vacuity / geometric-reading items argued but not kernel-checked** (carried over): K-4, FR-2, FR-ER-2, K-3 (2026-09-14 item 7);
   the truth of `src_contact` on the accepted definitions rests on the judge's numeric probe (D-SC-6) and a refuter's example, and the
   identification of the document's `sl` with Etnyre's / Geiges' `sl` is rem:sl-convention, a remark (FR-SC-4); the truth of
   `lit_homfly_descent` rests on the D2 premise (formal Reidemeister completeness). New: the two-disc model's orientation convention
   (FR-TD-7) is checked by a Jacobian computation in the plan, and FR-TD-9's boundary-orientation convention is CHECKED by unit U9's
   proof (`InteriorOnLeft ↔ σ = 1 ↔ 0 < rotationNumber`, closed 13:00Z) — kernel-checked, not argued.
10. **Conditional library theorems NOT mapped** (no content effect on accepted rows): `SM/ContactPathOfDescent.lean`
    (`cp_finite_contact_path_of_descent`, consumed by row 91), `RProof/X1Rows3.lean`, `SM/LinkingCalculus.lean`, `RProof/RALedgers.lean`
    (the three ledgers, `cv_R_of_rows`, `Bridge.sm_R_of_rows` — now consumed by the mapped rows 178/183), `SM/Comparison.lean`
    (`thm_comparison_of` — consumed by row 127), `SM/CInherits.lean` (`cor_C_inherits_of` — by row 128), `Bridge/SmR.lean`
    (`SM.sm_R_of_cv_R` — by row 183), `SM/FdContactStatements.lean`, `SM/CarrierFloor.lean` (`_of_bound` forms), `SM/CornerChainUnits.lean`,
    `SM/CS7Sliding.lean`, `SM/BigonDeletion.lean`, and the 2026-09-19 units modules `RProof/GenericTransportSw.lean`,
    `RProof/ExtremeSelectedUnits.lean`, `SM/CS7Units.lean` (`thm_C_S7_of`, `thm_C_S7_of_floor` live in the mapped `SM/CS7.lean`). All of
    these are now inside the audited import closure of the mapped modules (every one is imported, directly or transitively, by a mapped
    row module), so the checker's axiom audit DOES reach them (contrast 2026-09-16, when `SM/CS7Sliding.lean` was outside the closure; §7).
    D-F11 forbids mapping a row theorem with an undischarged premise.
11. **Blueprint edges 57 → 104 and 57 → 105** not realised by the proof routes (D-ER1; `corner_values_i`); blueprint frozen. The
    dependency column of `tools/claims.py` / `blueprint/DEPENDENCIES.json` is out of step with the proofs in three places (E-12: row 165
    from the geo-layer split, rows 127/128 no longer through 105) — used only for `--next`.
12. **Process incidents of 2026-09-19 (no effect on any accepted statement; disclosed):** (a) unit W5-BR compiled its file and died on a
    transient API HTTP 500 during its final `#print axioms` probe; the executor re-ran the probe and wrote `W5_BR_REPORT.md` from the file
    and logs, adding nothing (§3.1, §6); (b) two W6 glue-assembler instances ran on the same inputs after the executor messaged the running
    workflow agent (a duplicate transcript was resumed); both finished with identical axiom censuses; the port was taken from instance B
    (complete first) with A as the cross-check; a scratch-directory collision between them was recorded (`W6_ASSEMBLY_REPORT_B.md` §8.1)
    and no output of either was overwritten; lesson recorded: leave notes in files the agent polls instead of messaging; (c) the row-57
    design panel's architect B and judge (and a rerun of B) died on the 64 000 output-token limit spent on thinking, producing no file;
    the plan was finalised from architect A + the fidelity critic (D-TD-0) and a process rule adopted (medium effort, decide quickly,
    write in small pieces); (d) the pod container was OOM-restarted on 2026-09-18 ~01:55Z; the volume state survived intact (the resume
    receipt 05:45Z reproduces the 2026-09-16 counts 184 / 41 658).

## 6. Process

**Accept cycle used for every row** (ACCEPT_CYCLE.md, with the tooling of `work/port/`): pick the unit
(`tools/claims.py --next` / lane plan) → statement fixed BEFORE proving, fidelity risks recorded in AUTHOR_NOTES before
the row is stated → proof produced in `work/drafts/` (checked with `lake env lean`, never `lake build` there) → ported
verbatim into `work/lean/{SM,CV,RProof,Bridge}` with only a header added (`make_lane_modules.py` / the lanes' `port_build` tools,
D-FR1 for sorry-free increments) → `lake build` → `map_row.py implement` → `python3 tools/check_lean.py work/lean` (kernel check:
builds mapped modules, rejects sorryAx and unregistered axioms, writes the statement hash) → independent AI review: three
reviewer subagents with distinct lenses + two adversarial refuters, proof withheld (briefs `work/port/review_prompt_<slug>.md`,
inputs `work/reviews/<slug>-reviewer-input-statement.lean.txt`, raw output `<slug>-review-workflow-raw.json`) →
`summarize_review.py` + `write_review_and_accept.py` (unanimity required; a split verdict sends the row to round 2 with a
neutral disclosure, e.g. CV:lem:carrierword, ng:front-domain, CV:lem:carriers, CV:lem:piececurve) → row `accepted` →
checker again (receipt `work/checks/dev-check-<slug>-accepted.json`) → `tools/progress.py --once` → AUTHOR_NOTES,
STATUS.md, TASKS.json. 105 development receipts record the growth from 41 mapped / 4 579 audited (2026-09-13 13:44Z,
`dev-check-single-triple-implemented.json`) to 184 / 41 658 (2026-09-16 00:14Z) to 191 / 46 842 (2026-09-19 13:28Z,
`dev-check-rows110-127-128-184-accepted.json`); all 105 passed (99 at the 2026-09-16 00:14Z closing + `dev-check-FINAL-20260916.json`
00:59Z + 5 on 2026-09-19).

**AI-review disclosure** (text of `ai_review_disclosure` in every review written by this executor, e.g.
`work/reviews/prop-C-chamber.json`): "AI review. Four separate Claude Code subagents (model claude-fable-5-1) were
spawned by the executor on 2026-09-13 in one workflow: three reviewers with distinct lenses and one adversarial refuters
instructed to find any discrepancy. Each received only the printed SM15 source files, the row's Lean text with every
proof replaced by sorry (reviews/prop-C-chamber-reviewer-input-statement.lean.txt), and the Lean definition modules; none
saw the proof module work/lean/SM/CChamber.lean or the executor's reasoning. The executor (author) is
executor-pod-claude-fable-5-1-20260913, a different session of the same model. No human has read these reviews."
(later rows: "Five … three reviewers … two adversarial refuters … on 2026-09-14" / "… on 2026-09-15" / "… on 2026-09-16" / the seven
rows of 2026-09-19: "… spawned by the executor on 2026-09-19 in one workflow … none saw the proof module work/lean/RProof/ExtremeSelected.lean
[RProof/CvR.lean, Bridge/SmRRow.lean, SM/CS7.lean, SM/ComparisonRows.lean, SM/CornerLawsAndSoft.lean] or the executor's reasoning …").
Identities in the map (191 accepted rows, recounted at draft time): authors `executor-pod-claude-fable-5-1-20260913` (151 rows),
`root-implementation-20260910` (39), `executor-coldstart-claude-fable-5-1-20260912` (1); reviewers
`reviewer-pod-claude-fable-5-1-20260913 (independent Claude Code workflow subagents …)` (151), `review_chirotope-independent-20260910`
(30), `review_relgp_full-independent-20260911` (9), `reviewer-coldstart-claude-fable-5-1-20260912` (1). **The reviewers are AI only;
the author decided on 2026-09-19 (G-10) that human review is not required for completion and is arranged separately.**

**Lane pattern** for the large rows: design panel (two architects + judge, or three proposers + three judges) →
`PLAN_FINAL.md` with fidelity risks → `Statements_FINAL.lean` (compiles; exactly the row theorems as `sorry`) →
`Skeleton_FINAL.lean` (leaf sorries, assembly proved) → prover units on byte-identical copies (statements never change) →
false leaves repaired without statement change and recorded (FR-C8, FR-R6, CE-R10; on 2026-09-19 D-TD-2 and the corner/moves rule-3
items of §5) → assembler (statement identity check, clash scan, `#print axioms`) → statement pre-review / numeric probes → port.
**Library hygiene:** no `sorry` in `work/lean`; clash scans before every port (the row-57 clash `SM.polygonImage` vs
`SM/Rounding.lean:140` caught by the wave-1 assembler and resolved by renaming the DRAFT def, D-TD-3); never delete, rename or rewrite
an accepted declaration (D-F6 extends the library instead; G-03 route (ii) ports an additive copy rather than editing `G11_Config`;
G-05 comment-only edits are the one authorised change inside accepted modules, applied at the closing cycle with a checker re-run);
fixed target names from `axiom-policy.json`; incremental porting of sorry-free modules only (D-FR1); a checkpoint receipt after every
accept; checkpoint tarballs (`RESULT_20260919_1230Z.tgz` the latest at draft time). **Scope decisions** are in AUTHOR_NOTES with
labels (§0); the author's decisions of 2026-09-19 were received through Mark as a written response and recorded verbatim
(D-AUTH-20260919), the first author contact of the execution since D-GAP2; every other decision was taken locally (AUTONOMOUS_EXECUTION.md).

**Accept cycle 2026-09-19.** Unchanged in shape. Rows 177/178/183: W3D assembler (07:33-08:10Z) → port files `port/R177/` → executor
port 08:06-08:08Z (headers only; `RProof/GenericTransportSw.lean`, `ExtremeSelectedUnits.lean`, `ExtremeSelected.lean`; then the two
staged one-liners `RProof/CvR.lean`, `Bridge/SmRRow.lean`) → `lake build` 0 errors (85 s) → `map_row.py implement` ×3 → statements
stripped → checker 08:11Z (187 / 44 270) → workflow wf_b3114d58-914 (3 lenses + 2 refuters per row) → `write_review_and_accept.py` ×3
08:39Z → checker 08:42Z (receipt `dev-check-rows177-178-183-accepted.json`) → `progress.py --once` (127/132, 187/192, 6/8) → AUTHOR_NOTES /
STATUS. Rows 110/127/128/184: W6-GLUE assembler B (12:04-12:52Z) → port files `port/CS7_B/` (builder `port_build_B.py` with
`deletions.json` / `reword.json`; scratch-olean compile + `Axioms.lean` probe) + the row-184 module prepared 10:36Z → executor port cycle
12:54-12:55Z (`scratchpad/port_cs7.sh`: header stamps, forbidden-string check, `lake build` 0 errors 84 s, `map_row implement` ×4,
`strip_proofs` ×4) → executor `#check`/`#print axioms` probe 12:57Z → checker 12:56-12:58Z (191 / 46 842, log
`checker-run-20260919_1256Z.log`) → workflow review-rows-110-127-128-184 (12:57-13:24Z; 20 agents, 0 errors; 12/12 lenses faithful, 8/8
refuters not refuted) → `write_review_and_accept.py --allow-doc-notes` ×4 13:26Z → checker 13:26-13:28Z (receipt
`dev-check-rows110-127-128-184-accepted.json`, log `checker-run-20260919_1325Z.log`) → `progress.py --once` (131/132, 191/192, 8/8) →
AUTHOR_NOTES 13:26Z/13:29Z, STATUS 13:26Z. One build or checker at a time throughout (the D-DOC-2 deferral exists for this reason).
Heartbeat: cron every 14 min + `tools/progress.py --watch`.

**The reassessment rule as amended by the author, and how it was applied on 2026-09-19.** The rule (`/workspace/repos/lean/reassessment_rule.md`,
adopted 2026-09-14 ~17:00Z): reassess after two substantive attempts or 60 minutes of active work without a newly accepted source claim;
immediate triggers; the response is a bounded method audit with one decisive test, an effort bound and a stated consequence; report the
accepted count unchanged. **D-AUTH-20260919 §2 changed the CONSEQUENCE:** "A branch stops only for a mathematical blocker: a row
statement believed false (then a kernel-checked counterexample under `work/repairs/`) or a needed assumption that is not in the printed
proof and is not covered by §1 (then the exact question in AUTHOR_NOTES and STATUS while work continues on every other branch). A failed
audit on cost, time, estimate overrun or number of attempts never stops a branch. … This paragraph supersedes the consequences recorded
in audits A-110-1 and A-177-2." Applications, in order:
- **Resume (05:35Z):** the consequences of A-110-1 (22:40Z 2026-09-15) and A-177-2 (00:31Z 2026-09-16) — "no further construction" — were
  superseded; both branches re-opened with their stagnation histories retained and no bound; row 57 re-opened as a new lane.
- **Row 177, wave 3d (units 06:xxZ → 07:17Z; assembler 07:33-08:10Z):** the author's G-02b allowed a hypothesis after one substantive
  derivation attempt; unit NONKINK's attempt (audit A-177-NK-1) found the stated leaf FALSE and proved the consumer's value form instead,
  so the hypothesis was never taken. Closed inside one wave; accepted 08:39Z — the first newly accepted claims of the session, resetting
  the R branch's clock; the branch is finished.
- **Row 110, waves 4-6:** wave 4 (→ 08:25Z) closed the sliding leaf and reduced the bigon leaf to one Prop; wave 5 (→ 11:22Z) reduced it to
  four fully specified geometric Props with every consumed interface proved but did not close it. **Audit A-110-2 (11:22Z)**, the
  stagnation clause (no acceptance on the branch since the lane opened): diagnosis "decomposition scope; no counterexample, no outside
  assumption — the four Props are the printed sm-4:576-600 corner bookkeeping, the U110-I rotation identities on the centre polygon and
  the cb:products curl value"; method unchanged with one refinement (ROT consumes COR's Prop through the declared box); estimate
  1 900-3 200 lines; wave 6 launched; **under §2 the audit is recorded and never a stop** (accepted count reported unchanged, 127/132).
  Wave 6 closed the row at 12:55Z (12:38Z for the last box); accepted 13:26Z with 127/128/184.
- **Rule 3 / rule 4 (false-as-stated draft leaves; never a row statement) invoked on 2026-09-19:** corner — the two BR turn boxes and the
  curl box (not derivable as stated: no radius / missing radius facts), ROW's `w5r_box_branch` and BR's `w5b_box_returnedData` (missing
  hypotheses), ROT's exactly-stated new box (a brief phrase, not a false statement); moves — `w3cs_not_kink_site` (false; a genuine 177
  configuration), `w3bi_bigon_pair` / `w3bi_rii_sites` (false in the kink pattern), the relational-smoothing Props (not provable as
  stated); twodiscs — D-TD-2's three sub-leaves (one with a kernel-checked counterexample). In every case the frozen statement or accepted
  structure was left as is and the corrected form realised alongside or the dead material deleted at port (D-FR2 pattern).
- **Row 57 (new lane, 08:23Z →):** panel (with the incident of §5 item 12c), D-TD-0/1, skeleton, wave 1 (→ 11:51Z, 62/92), wave 2 (11:54Z →;
  per-unit clocks; U6/U7/U9 closed by 13:00Z). No audit was needed at draft time; <<ROW57: fill at acceptance — any audit on the lane
  and its outcome>>.

**Process caveats a reader must know** (OPEN_ITEMS §F, unchanged and confirmed): `audited_declarations` counts the import closure of
the MAPPED modules plus `Supplemental` (F-01; §7); one `lake build` or checker at a time, subagents never build (F-05); heredoc quoting
when appending to AUTHOR_NOTES (F-03); `pgrep` self-match (F-04). New on 2026-09-19: messaging a running workflow subagent resumes a
duplicate instance — leave notes in files the agent polls (AUTHOR_NOTES 12:55Z); design/judge agents at effort 'medium' with the
instruction to decide quickly and write in small pieces (D-TD-0); an agent that dies after compiling leaves a valid file — the executor
may re-run its probes and write its report from the file and logs, saying so (W5_BR_REPORT.md).

## 7. Inconsistencies noticed between the tools' output and the notes (for the executor)

Resolved since the 2026-09-16 review:
- **The 2026-09-16 §3.1, §3.4 (rows 110, 177 "kernel-proved modulo named leaves", 178/183/184 "INCOMPLETE"), §4.4-§4.7 ("not declared",
  "coverage not complete", "the final declaration is NOT declared"), §4.9 (stage FAIL on eight rows) and §5 items 2-4** are superseded by
  §3.1, §3.4, §4.4-§4.7 above; the 2026-09-16 text remains readable in `work/delivery/FINAL_REVIEW.md` and the handover archive.
  OPEN_ITEMS_20260916.md §A-02..A-22 are closed except A-01 (row 57, now a running lane); §G is answered by D-AUTH-20260919; §E's
  comment-only items are prepared as patches (D-DOC-2).
- **STATUS.md staleness of 2026-09-16** (row 176 "00:05Z", "no branch past its bound"): the 2026-09-19 header (13:26Z) is current; the
  five stacked "# STATUS" headers of 2026-09-15 and the 2026-09-14 text remain below it as history (the file now stacks the 2026-09-19
  block, the 2026-09-15 22:40Z block header-less under it, and the older headers).
- **Row 174's σ orientation dependence** (asked for by two reports, no AUTHOR_NOTES entry): still no entry (E-14); recorded in §5 item 4.
- **"Five interfaces / six constants" vocabulary** (E-10): the four "no sixth axiom" sentences in accepted modules are reworded by the
  prepared patch 07; until applied they contradict the six-constant kernel list. This review uses "the nine registered axioms" / `9`,
  "five interfaces", "six literature constants", and quotes the row-184 reviewer's note verbatim (§4.3).
- **Receipt count:** 99 at the 2026-09-16 00:14Z closing, + `dev-check-FINAL-20260916.json` (00:59Z) = 100 at the archive, + 5 on
  2026-09-19 = 105 `dev-check-*.json` files at draft time, all `passed: true`; <<ROW57: fill at acceptance — the final count after the
  row-57 receipts and the post-patch receipt>>.

Still to note (each verified in the files named):
- **`audited_declarations` is not a per-module audit of `work/lean`.** `tools/check_lean.py` builds the MAPPED modules plus
  `Supplemental` (a fixed import list in `work/lean/Supplemental.lean`, unchanged) and runs `Supplemental.auditProject` over
  `env.constants`; a library module imported by no mapped module contributes nothing to `audited_declarations`. On 2026-09-19 every new
  library module is imported by a mapped row module (`SM/CS7Units.lean` by `SM/CS7.lean`; `RProof/GenericTransportSw.lean` and
  `RProof/ExtremeSelectedUnits.lean` by `RProof/ExtremeSelected.lean`), so the closure grew 41 658 → 44 270 (+ 2 612: the 177 units and
  the trans-free copy) → 46 842 (+ 2 572: `CS7Units` + `CS7` + `ComparisonRows` + `CornerLawsAndSoft`) and their axiom sets ARE
  machine-checked; `project_sha256` grew 701 → 706 → 710 entries. Per-declaration rows in `declaration-audit.json` exist only for the 191
  mapped declarations (verified: `audit.declarations` has 191 entries, `audit.checked` = 46 842; `statement_hashes` is keyed by ROW ID,
  not by declaration name — a reader comparing it with the map must join on `id`).
- **W6 assembly line counts:** instance A's `W6_Assembled.lean` 27 533 lines, instance B's `W6_Assembled_B.lean` 27 531 (`wc -l` at
  draft time agrees with both reports); the port source is B (PORT_REPORT.md header; the module headers say so). `SM/CS7Units.lean` is
  exactly 27 000 lines by `wc -l` — a coincidence of the builder's deletions, not a rounded figure (the AUTHOR_NOTES "27,000" is exact).
- **W3D assembly:** `W3D_Assembled.lean` 21 748 lines (report §0 and `wc -l` agree); the W3C base was counted as 1 427 declarations by the
  W3D regex vs 1 428 in `W3C_ASSEMBLY_REPORT.md` (a regex difference, report §0 says so). `W3D_AXIOMS.log` lists 31 declarations.
- **"#print axioms" facts quoted for library modules** (`W3D_AXIOMS.log`, the W6 censuses, `port/CS7_B/PORT_REPORT.md` §1, the executor's
  12:57Z probe) come from `lake env lean` on scratch files, not from checker receipts; the receipts of 08:11Z/08:42Z/12:59Z/13:28Z are the
  binding evidence for the mapped declarations, and since every new library module is in the closure, the checker's "no unregistered
  axiom" verdict covers them too (unlike 2026-09-16's `SM/CS7Sliding.lean`).
- **Audit A-110-2's numbering:** AUTHOR_NOTES 11:22Z calls it "A-110-2"; `W5_ASSEMBLY_REPORT.md` does not name it (it was written before
  the audit, at 11:20Z). The NONKINK audit is named "A-177-NK-1" only in `W3D_ASSEMBLY_REPORT.md` §6; the AUTHOR_NOTES 07:17Z entry
  describes the same attempt without the label. This review uses both labels.
- **Review timestamps vs acceptance times:** the seven reviews' `review_utc` are 08:39:13/17/21Z and 13:25:40/43/46/50Z; the AUTHOR_NOTES
  acceptance entries say 08:39Z and 13:26Z (the map was written by `write_review_and_accept.py` seconds after the last review). The
  `accepted_utc` / `implemented_utc` fields of the map are `null` for every row (the schema carries them; the tooling never filled them —
  since 2026-09-13); times come from AUTHOR_NOTES and `review_utc`.
- **The row-184 brief pointed to `reviews/thm-C-S7.json` and `reviews/cor-c-inherits.json`** (the latter with a lowercase `c` — the file
  is `cor-C-inherits.json`), neither existing during the concurrent workflow; the reviewers said so and worked from the printed statements
  (§3.4). A brief for a bundle row should either run after its input rows' reviews or point to the statement files only.
- **`work/drafts/twodiscs/W1_ASSEMBLY_REPORT.md` says "62 closed (60 by the units + 2 closed here under their corrected forms)"** while
  the 11:37Z AUTHOR_NOTES tally says "60 of 92 leaves closed" before the assembler and the 11:54Z entry "62/92": consistent (the assembler
  closed the two corrected U3/U4 forms). Wave-2 open-leaf counts: 30 → 23 (U7) → 15 (U6) → 10 (U9) at draft time; <<ROW57: fill at
  acceptance — the final tally>>.
- **STATUS.md 13:26Z says "W6_Assembled.lean 27.5k lines"** without the `_B`; the port came from `_B` (27 531). Documentation only.
- **`work/delivery/`** has NOT been refreshed since 2026-09-16 02:33Z (its `FINAL_REVIEW.md` = the 2026-09-16 root file, sha256
  `1373130e…`; `receipts/` 156 files, `reviews/` 868 files) — run `refresh.sh` after this root file is final and the closing receipts exist
  (§4.9). `work/delivery/tools/gen_final_review_tables.py` is still the stale 2026-09-14 tool (E-17): its abbreviation table knows
  `H`/`LM`/`LMU`/`NG` only, its `PENDING_REASONS` carry 2026-09-14 texts for rows long accepted, its `DRAFT` target is
  `work/FINAL_REVIEW_DRAFT.md`, its `audit_axioms()` prefers the stale summary. The tables of this review were produced by
  `scratchpad/frdraft/gen_tables_20260919.py` (session scratchpad, not part of the package): it streams the 1 GB audit line-wise, reuses the
  184 lines of the 2026-09-16 table verbatim after re-verifying their axioms column (0 mismatches), adds seven curated lines, and checks
  191/191 statement hashes and verdicts. Porting these patches into the delivered tool is a tool edit for the executor, outside this
  documentation pass.
- **MANIFEST.sha256 (191 lines, 2026-09-16 02:33Z)** binds the 2026-09-16 `FINAL_REVIEW.md`, `lean/axiom-policy.json`, `verify_bundle.py`
  and the unpatched `blueprint/AXIOM_REGISTRY.md`; three of these change at the closing cycle (this file, the registry sub-entry) or
  must be re-verified (`verify_bundle.py` PASS was last recorded 2026-09-16 00:56Z).
- **`work/checks/stage-1.json`** is still the 2026-09-16 00:33Z `checking` placeholder (no `--all` run since); the closing run rewrites it.
- **`hyp_R` grep (§4.4):** the string `hyp_R` occurs in `SM/CornerLawsAndSoft.lean` only as the field type `triple : hyp_R` and the
  parameter of the library theorem `corner_laws_and_soft_of`; in `SM/ComparisonRows.lean` as the explicit `(hR : hyp_R)` of both rows; in
  `Bridge/SmRRow.lean` and `RProof/CvR.lean` only as the conclusion types `SM.hyp_R` / `CV.hyp_R`; in `SM/CS7.lean` and
  `RProof/ExtremeSelected.lean` not at all. No mapped row theorem other than 127/128 takes an R hypothesis.
- **Lane size vs estimate (row 110):** D-CC-4 11-15k; the 2026-09-16 remainder estimate ≈ 8-12k over 2-3 waves; the actual remainder was
  three waves (4, 5, 6) and ≈ 18.5k assembled lines (W3 8 958 → W6 27 531; `SM/CS7Units.lean` 27 000 after deletions), i.e. above the
  estimate by about half. Row 177's remainder estimate (≈ 1.3-2.5k, one route open) vs actual: W3C 16 945 → W3D 21 748 (+4 803 gross,
  −727 deleted), one wave. Row 57: PLAN_A estimated ≈ 21.5k lines in twelve units; wave 1 assembled 13 815 lines for 62 leaves;
  <<ROW57: fill at acceptance — the final size>>.
- **Citation nits and the 2026-09-14/15/16 items of this section** (the "21 vs 20 `w3a_` sub-leaves", skeleton line offsets, "8854 vs
  8876", the addendum's stale receipt figures, the review identity string dated by first use, the lane-size arithmetic of 2026-09-14,
  `ng:finite-word`'s axiom set without `Classical.choice`/`Quot.sound` — confirmed again by the 13:28Z audit, the only mapped declaration
  missing them —, the numbering claims.py "#" ≠ map index, `src:contact` = m97, `lem:weak-open` = m192) stand as recorded on 2026-09-16 and
  are not repeated here.
- **Placeholders left for the executor** (the only double-angle-bracket tokens in this file; every one opens with the two angle brackets followed by `ROW57`): the header's
  FINAL-TIME and STAGE-CHECK-RESULT sentences, §0 (stage check; row 57 line), §1 (heading, exit line, final counts), §2 (heading), §3
  (heading, table cell, the pending paragraph), §3.2 (the outcome block), §4.3 (registry sub-entry; post-patch receipt), §4.9 (the closing
  result; the stage verdict), §5 items 2, 3, 4 (row-57 bullet), §6 (row-57 audit), §7 (receipt count, wave-2 tally, row-57 size) — to be
  filled from `tools/progress.py --once`, the row-57 review file and receipts, the closing `--all` run's last line, `verify_bundle.py` and
  `refresh.sh`, before the MANIFEST refresh; then re-run `gen_tables_20260919.py` (or the delivered tool once patched) so that §1-§3 show
  192 rows.
