# work/delivery — the delivery package (created 2026-09-14 15:05 UTC / 11:05am ET; delivery state 18:15 UTC / 2:15pm ET)

AUTONOMOUS_EXECUTION.md asks for "sources, pins, declaration map, reviews, current checker receipts
and progress history under work/delivery/". This directory holds copies of the live evidence; the
sources are NOT copied (they are frozen in place, see "Sources"). It was created by the pod executor's
documentation agent while rows were still being accepted (15:05Z) and brought to its delivery state at 18:15Z;
the executor refreshes it once more with `bash work/delivery/refresh.sh` (no checker inside) after the final
checker run (see the last paragraph of "State at delivery").

State at delivery (2026-09-14 18:15 UTC / 2:15pm ET): claims verified 109/132 (82.6%), checklist 168/192 accepted
(0 implemented-awaiting-review, 24 pending: 22 claim rows blocked by GAP-2 — row 91 `cp:finite-contact-path`, proved
modulo Reidemeister's theorem for smooth isotopies, and its 21 downstream rows —, row 57 `lem:gauss-two-discs`
deferred as infeasible now, and the unused literature interface `src:contact`, never declared), final targets 4/8
(`prop:C-chamber`, `prop:C-silent`, `thm:C-S3`, `thm:C-S5` accepted; `thm:C-S7`, `thm:C-soft`, `thm:comparison`,
`cor:C-inherits` open). Development receipt `receipts/stage-development.json` (= `work/checks/dev-check-frontrowsw3b-accepted.json`,
18:06Z): passed=true, stage=null, stage_accepted=false, 168 mapped / 36 079 audited declarations; 79 per-run receipts,
all passed. **Stage check:** `python3 tools/check_lean.py work/lean --all` was run at 18:06Z and FAILED as expected —
"FAIL: stage is incomplete; unaccepted rows: Bridge:theorem, CV:ax:etnyre, CV:ax:slbound, CV:singleton_D_i,
CV:thm:carrierfloor, R:cv_theorem, R:extreme_pair_zero, R:extreme_selected, R:extreme_transport, R:generic_selected,
SM:corner_laws_and_soft, cb:singleton, cf:thm-carrierfloor, cor:C-inherits, cp:finite-contact-path, fd:contact,
lem:corner-values, lem:gauss-two-discs, prop:anchor-values, src:contact, thm:C-S7, thm:C-soft, thm:comparison, thm:floor"
(log `work/checks/stage-all-attempt-1806.log`, not matched by refresh.sh's log glob and therefore read in place;
`work/checks/stage-1.json` = `receipts/stage-1.json` records passed=false). **The single focused stage is INCOMPLETE and
is reported as such** (FINAL_REVIEW.md, completed review §3, §4.8, §5). The root `FINAL_REVIEW.md` (checklist + the
completed review appended at 18:15Z; `FINAL_REVIEW.md` here is its hand-made copy — refresh.sh looks for a
`work/FINAL_REVIEW.md` that does not exist) is part of the checker's bundle (`bundle_sha256` in the receipt), so the
executor runs the final development checker (`python3 tools/check_lean.py work/lean`) AFTER this edit and then refreshes
this package once more, so that the delivered receipt binds the delivered bytes. Until that run, `receipts/stage-development.json`
binds the pre-edit root FINAL_REVIEW.md and is evidence about 18:06Z only.

## Layout

| path | content | live original |
|---|---|---|
| `README.md` | this file | — |
| `refresh.sh` | re-copies everything below and rewrites `MANIFEST.sha256`; runs no Lean tool | — |
| `MANIFEST.sha256` | sha256 of every file in this directory (excluding itself) | — |
| `AUTHOR_NOTES.md` | the decision log (every local decision, fidelity risk, deferral, GAP-2 memo) | `work/AUTHOR_NOTES.md` |
| `FINAL_REVIEW.md` | copy of the ROOT `FINAL_REVIEW.md`: the checklist followed by "Completed fidelity review — 2026-09-14 (pod executor)" (final counts, the 168 accepted rows with review files and axioms, the 24 pending rows with reasons, the checklist item by item, the stage-check result, remaining gaps, process, inconsistencies) | `FINAL_REVIEW.md` (package root) |
| `FINAL_REVIEW_DRAFT.md` | the working copy the completed review was finalized in (same content as the appended section) | `work/FINAL_REVIEW_DRAFT.md` |
| `pins/lean-toolchain` | `leanprover/lean4:v4.34.0-rc2` | `work/lean/lean-toolchain` |
| `pins/lake-manifest.json` | resolved dependency pins (Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0` + 8 others) | `work/lean/lake-manifest.json` |
| `pins/lake-manifest.shipped.json` | the manifest as shipped at handover (byte-identical to the live one on 2026-09-14; refresh.sh warns if they ever differ) | `work/lake-manifest.shipped.json` |
| `pins/lakefile.toml`, `pins/ENVIRONMENT.md` | build configuration and the pinned-setup notes | `work/lean/` |
| `pins/axiom-policy.json` | standard axioms, the five literature names, the fixed target names the checker enforces | `work/lean/axiom-policy.json` |
| `declaration-map/lean-declarations.json` | the 192-row checklist map (id, source, line, declaration, module, status, author, reviewer, statement_sha256, review_file) — the file `work/port/map_row.py` edits and the checker reads | `work/lean/lean-declarations.json` |
| `reviews/` | exact mirror of `work/reviews/`: one `<row>.json` per accepted row (verdict, reason, hashes, AI-review disclosure, lenses, refuters, kernel check) plus what each reviewer saw (`<row>-reviewer-input-statement.lean.txt`, `<row>-source-excerpt-*.txt`, `<row>-registry-excerpt.md.txt`), the raw workflow outputs (`*-review-workflow-raw.json`), the 2026-09-13 countersignature raw output and the historical technical reviews | `work/reviews/` |
| `receipts/stage-development.json` | the current checker receipt (binds project bytes, bundle bytes, reviews, policy) | `work/checks/stage-development.json` |
| `receipts/declaration-audit.json.gz` | the current declaration audit, gzipped (raw ≈ 0.8 GB: it carries the expanded definition bodies the statement hashes bind) | `work/checks/declaration-audit.json` |
| `receipts/declaration-audit.summary.json` | the same audit without bodies: per mapped declaration `{declaration, kind, module, axioms}` and all `statement_hashes` | derived |
| `receipts/dev-check-*.json` | every per-run development receipt of this execution (79 at delivery, 2026-09-13 13:44Z 41 mapped / 4 579 audited → 2026-09-14 18:06Z 168 / 36 079, all passed) | `work/checks/dev-check-*.json` |
| `receipts/stage-1.json` | the failed stage-check receipt of 18:06Z (`passed: false`); its log stays at `work/checks/stage-all-attempt-1806.log` | `work/checks/stage-1.json` |
| `receipts/checker-run-*.log` | checker run logs where kept | `work/checks/` |
| `progress/progress-watch.log`, `progress/PROGRESS.md`, `progress/progress/{history.jsonl,latest.json,scope.json,claims-*.json*}` | the 15-minute reporter's history ("claims verified X/132") | `work/progress-watch.log`, `work/PROGRESS.md`, `work/progress/` |
| `progress/STATUS.md`, `progress/TASKS.json` | resume point with all checkpoints; task states | `work/STATUS.md`, `work/TASKS.json` |
| `tools/gen_final_review_tables.py` | regenerates the four machine-derived tables of FINAL_REVIEW_DRAFT.md from claims.py, the map, the audit summary and the reviews (no Lean, no checker) | — |

## Sources (not copied — frozen in place)

The source frame is **SM15** (frozen 2026-09-12; `SM15_REALIGNMENT.md`, `ERRATUM_20260912.md`,
`CHANGES_SINCE_20260909.md`). Nothing under these paths was edited during execution, and the checker
receipt hashes them:

- `reference/` — SM (`reference/SM/sm-0-legend.tex … sm-6-comparison.tex`, `sm.tex`, `sm-refs.bib`),
  `reference/R/` (CV and RA files), `reference/BRIDGE/BRIDGE.md`.
- `provenance/SM15/` — the SM15 manifest; `provenance/SM12/` — the historical pin the earliest reviews
  bound to; `provenance/BRIDGE_REALIGNMENT_SM15.json` — the bridge-quotation ledger.
- `blueprint/` — the 172 source rows + 19 R/bridge/final obligations regenerated on SM15
  (`STATEMENTS_AND_PROOFS.md`, `AXIOM_REGISTRY.md`, `DEPENDENCIES.json`, `NODES.tsv`, `ORDER.md`).
- `SOURCES/` + `LITERATURE.md` — the literature behind the five admitted interfaces.

The Lean library itself stays at `work/lean/` (SM, CV, RProof, Bridge; `lake-manifest.json`,
`lean-toolchain`, `axiom-policy.json`, `lean-declarations.json` are the originals of the copies above).
The candidate lane `work/checks/*.body.lean` / `*.prototype.lean` (previous executor) and the drafts
`work/drafts/` (design panels, skeletons, statement files, memos) remain in place and are cited by path
from AUTHOR_NOTES.md and FINAL_REVIEW_DRAFT.md.

## How to re-verify

From the package root, on a machine with nothing installed (SETUP.md; ~5 min to an hour):

```sh
bash setup.sh                                   # git, python, elan, pinned Lean, Mathlib cache, lake build, checker
export PATH="$HOME/.elan/bin:$PATH"             # every new shell
python3 tools/check_lean.py work/lean           # development check: builds the mapped modules, rejects sorryAx and
                                                # unregistered axioms, rewrites work/checks/{stage-development,declaration-audit}.json
python3 tools/check_lean.py work/lean --all     # the stage check (single complete focused stage); passes only when
                                                # every row of the package is accepted — NOT the case at delivery
                                                # (24 rows pending; it FAILED at 18:06Z with "stage is incomplete")
python3 tools/claims.py --pending-only          # the open rows
python3 tools/progress.py --once                # "claims verified X/132"
```

Then compare: `receipts/stage-development.json` ↔ the fresh `work/checks/stage-development.json`
(`passed`, `mapped_declarations`, `audited_declarations`, and the `project_sha256` / `bundle_sha256`
maps must agree with the bytes on disk); every accepted row's `statement_sha256` in
`declaration-map/lean-declarations.json` ↔ `statement_hashes` in the audit ↔ the row's
`reviews/<row>.json`; each review's `source_sha256` ↔ the SM15 file named in the row's `source`;
`reviewed_files_sha256` ↔ the Lean files the reviewer read. A receipt must still match code, reviews,
sources and policy (FINAL_REVIEW.md, last paragraph); an old receipt is evidence about its own time only.

On this pod the environment is `source /workspace/envs/lean/env.sh` (Python 3.11 venv, elan on local
disk, `work/lean/.lake` symlinked to local disk; AUTHOR_NOTES.md 2026-09-13).

## Refreshing this package

```sh
bash work/delivery/refresh.sh        # copies, gzips the audit, writes the summary and MANIFEST.sha256; ~20 s
python3 work/delivery/tools/gen_final_review_tables.py --write   # then rewrite the draft's tables
cp FINAL_REVIEW.md work/delivery/FINAL_REVIEW.md                 # the root review is copied by hand (refresh.sh does not)
```

refresh.sh never runs the checker or lake: run `python3 tools/check_lean.py work/lean` (or `--all`)
first if the receipts should be current. It mirrors `work/reviews/` with `--delete`, overwrites the
other copies, and warns if the live lake-manifest differs from the shipped one.
