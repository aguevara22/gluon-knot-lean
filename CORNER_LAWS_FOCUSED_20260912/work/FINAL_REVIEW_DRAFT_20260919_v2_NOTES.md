# FINAL_REVIEW_DRAFT_20260919_v2.md — notes for the executor (finisher, 2026-09-19 15:16Z-15:55Z / 11:16-11:55am ET)

`work/FINAL_REVIEW_DRAFT_20260919_v2.md` (1 657 lines) is the 13:26Z draft (`FINAL_REVIEW_DRAFT_20260919.md`, 1 408 lines) with every
row-57 and map-state placeholder filled, the §1/§2/§3/§4.4 tables regenerated (15:20Z, 192 rows), the §(b) numbers re-counted, and —
because the closing `--all` run finished (PASSED 15:36Z) and D-DOC-3/D-DOC-4 were recorded while the file was being written — the
closing-run results already quoted from the receipts. The draft was not edited; both passes are reproducible from
`scratchpad/frdraft2/make_v2.py` (pass 1, on the draft) and `scratchpad/frdraft2/fix_v2.py` (pass 2, on v2); every replacement asserted a
unique anchor. Tables: `scratchpad/frdraft2/gen_tables_v2.py` (the drafter's generator + row 57's curated line + 15:20Z stamps + an
empty-PENDING row), outputs `tables.md`, `stats.json` there. No Lean tool, no `lake`, no checker was run by the finisher; all facts below
were read from files.

## (a) Every remaining `<<CLOSING: …>>` marker (7 distinct texts, 21 occurrences; no `<` or `>` inside any marker, so
`re.sub(r'<<CLOSING:[^<>]*>>', …)` or a per-marker `str.replace` fills them; the same text is used wherever the same value is needed)

| marker text (verbatim) | lines | what fills it |
|---|---|---|
| `<<CLOSING: final time — "HH:MM UTC / h:mmam ET" from the executor's exit tools/progress.py --once>>` | 55, 221 | the time of the executor's exit `python3 tools/progress.py --once`, both clocks, e.g. `16:05 UTC / 12:05pm ET` (`TZ=America/New_York date`). Line 55 reads "completed <marker> (pod executor)"; line 221 reads "`python3 tools/progress.py --once` at <marker> repeats it". |
| `<<CLOSING: stage verdict — COMPLETE or INCOMPLETE per the closing --all result>>` | 68, 1230 | `COMPLETE` (the 15:36Z `--all` run passed: `stage-1.json` passed=true, stage_accepted=true; all 192 rows accepted). Write `INCOMPLETE (reported as such)` only if the post-install re-run fails. Line 68: "the focused stage is <marker>."; line 1230: "The single focused stage is <marker>** (COMPLETE = …)". |
| `<<CLOSING: post-install development receipt — name, HH:MMZ, mapped / audited — and the final dev-check-*.json count>>` | 1228, 1264, 1424, 1546 | after installing this file as root `FINAL_REVIEW.md` and re-running `python3 tools/check_lean.py work/lean`: "`work/checks/dev-check-<name>.json` (HH:MMZ; passed, 192 mapped, 49 212 audited); N `dev-check-*.json` files in all" (108 at 15:36Z, so N = 108 + the receipts you add). |
| `<<CLOSING: MANIFEST.sha256 refresh — time, line count and the refreshed FINAL_REVIEW.md line (sha256 prefix); the registry line is unchanged>>` | 1223, 1264, 1609 | after `python3 work/port/refresh_manifest.py`: "refreshed HH:MMZ; 191 lines; `FINAL_REVIEW.md` = `<first 8 hex>…`; the `blueprint/AXIOM_REGISTRY.md` line unchanged (`2d00dec7…`)". Refresh AFTER the final bytes of FINAL_REVIEW.md are in place (i.e. after filling these markers). |
| `<<CLOSING: verify_bundle.py result line and time>>` | 79, 1223, 1265, 1609 | the last line of `python3 verify_bundle.py` verbatim + time, e.g. "`verify_bundle.py` PASS (HH:MMZ)". |
| `<<CLOSING: work/delivery/refresh.sh time and receipts/reviews file counts>>` | 1225, 1265, 1604 | after `work/delivery/refresh.sh`: "refreshed HH:MMZ: `receipts/` N files, `reviews/` M files, `FINAL_REVIEW.md` = the installed root file" (`find work/delivery/receipts -type f | wc -l`, same for reviews; 156 / 868 before). |
| `<<CLOSING: final tarball name and sha256>>` | 1225, 1265, 1453 | "`RESULT_20260919_<stamp>.tgz` (sha256 `<64 hex>`, <location>)". |

Order that keeps every sentence true: fill the post-install receipt marker last-but-one (it needs the checker run on the installed file),
then MANIFEST/verify/refresh/tarball, then the final time; the stage verdict can be filled now (COMPLETE) unless the re-run fails.

## (b) What the finisher changed (draft → v2)

- Header: final-time and stage-verdict markers rewritten as `CLOSING:` markers; the state sentence now quotes 15:21Z (132/132, 192/192, 8/8,
  receipt `dev-check-row57-accepted.json` 192 / 49 212) and the closing state (`--all` PASSED 15:36Z, stage-1 191 / 49 207, development
  192 / 49 212, post-patch receipt `dev-check-FINAL-20260919.json`); "seven rows" → "eight rows accepted on 2026-09-19" with row 57 at
  15:14Z; the patch sentence (ten Lean/drafts patches applied 15:16Z; registry sub-entry applied and reverted, D-DOC-3; D-DOC-4); the
  unchanged-modules sentence extended to the 15:16Z receipt and the comment-only patch 06 on `SM/CornerChainUnits.lean`.
- §0: kernel-evidence bullet (15:36Z receipts, stage-1.json, audits, 108 receipts by day, the three `--all` logs); reviews 192; policy bullet
  (registry unchanged, D-DOC-3); AUTHOR_NOTES range extended to L7149-7154 with all row-57, D-DOC-3, D-DOC-4 entries; lane files (W2
  reports, W2_Assembled, PORT_REPORT, port files); "Kernel evidence 2026-09-19" 8 development receipts + the stage receipt + the row-57
  axiom censuses; "Reviews 2026-09-19" + the row-57 review, inputs, excerpt; library paragraph: the six GaussTwoDiscs modules with line
  counts, 712 files / 366 040 lines (658 SM, 32 CV, 15 RProof, 5 Bridge, 2 Supplemental), `sorry` grep 55 → 0 after patch 09; source
  frame (blueprint unchanged); row-57 line filled.
- §1: heading re-stamped 15:20Z; SUMMARY block regenerated (192/192, 0 pending; footer 15:20Z / 15:16Z audit / receipt 192 / 49 212);
  paragraph rewritten to the 15:21Z state (`--pending-only` empty, 192/192 hashes and verdicts, `--all` PASSED 15:36Z).
- §2: heading 15:20Z, 192 rows; legend: `std` 114 → 115, "192 accepted rows", 192 verdicts, 8 rows of 2026-09-19, identity counts 151 → 152,
  workflow review-row-57, eight new lines; ACCEPTED block regenerated — 184 old lines byte-identical (0 axiom-column mismatches), 7 drafter
  lines, + row 57's line (`std`, "[12 notes]"; its reading text is the generator's NEW dict entry, amended to say "recorded counterexamples,
  two of them kernel-checked"); note on the D-DOC-4 field correction of `ng-finite-word.json` (line unchanged).
- §3: heading 15:20Z, 0 rows; PENDING block regenerated with a single "(none)" row; the pending paragraph → "No row is pending".
- §3.2: retitled "accepted 15:14Z 2026-09-19 (… route A, two waves over 92 leaves; audit A-57-1)"; the marker block replaced by the
  Outcome block (declaration, review with lens/refuter counts 7+5 / 8+5 / 6+5, the reviewers' Jacobian check of FR-TD-7, route A / no
  Jordan-Schoenflies, the six modules with line counts = 20 996, axioms standard only with every source, receipts 14:57Z/15:16Z, the
  disclosed items D-TD-2 (four sub-leaves, two kernel-checked counterexamples) and D-TD-3, the optional not-done de-duplication of
  `u8h_f_*`, the reviewers' non-blocking notes and strengthenings, `weaker_than_source` empty, A-57-1); "State at draft time" → "How the
  lane ran" with the AUTHOR_NOTES ranges; wave-1 bullet: "three … a fourth at wave 2"; wave-2 bullet rewritten to the final run (U5 13:39Z
  with the `U5_pushforward_edges` counterexample, U8 14:32Z, open-leaf counts to 0, U12 assembler, port, checker, review, acceptance).
- §4.2: RALedgers hash sentence extended to the 15:16Z receipt; 192 hashes; the eight new lines and 7 of 8 strengthening reviews; row 57's
  readings added.
- §4.3: the registry paragraph rewritten to D-DOC-3 (applied 15:16Z, reverted 15:29Z, why, blueprint unchanged, MANIFEST line correct);
  HD footprint "21 from the 15:16Z audit — unchanged by row 57"; kernel-evidence sentence to the 15:16Z receipt (192 / 49 212, 177
  theorems); the closing-cycle caveat → the confirmed post-patch check (`dev-check-FINAL-20260919.json`).
- §4.4: heading 15:20Z; RTABLE regenerated (byte-identical to the drafter's).
- §4.8: audit stamp 15:16Z.
- §4.9: rewritten as the record of the closing cycle: PASSED 15:36Z with the log's first line, the stage-1 scope (191 = all but
  `lem:weak-open`), steps (1) patches, (2) build 521 s, (3a) FAIL ng:finite-word, D-DOC-3, (3b) FAIL again, diagnosis, D-DOC-4, (3c) PASS;
  steps (4)-(7) as markers; the binding receipts; the post-install re-run marker; the verdict marker.
- §5: item 2 → "accepted 15:14Z; no gap" with the axiom set, D-TD-2 (four items, which are kernel-checked), D-TD-3, FR-TD-1..14, the
  not-done de-duplication; item 3 → the closing-cycle record (ten patches standing, registry reverted, `--all` passed, open steps as
  markers); item 4 row-57 bullet → four sub-leaves, confirmed against the review's `executor_notes`; item 5 header → "PREPARED … APPLIED
  15:16Z" (describes the pre-patch state), 15 new module headers, the registry sub-entry reverted; item 6 → 192 rows, 24 since 2026-09-14;
  item 7 → row 57's strengthenings; item 9 → FR-TD-7 re-derived by the reviewers, FR-TD-9 kernel-checked; NEW item 13 → D-DOC-4 disclosed.
- §6: 108 receipts and the growth to 192 / 49 212 (15:16Z, 15:36Z); disclosure text lists `SM/GaussTwoDiscs.lean`; identities 192 / 152;
  library hygiene "the blueprint never changed"; tarball marker; the row-57 accept cycle appended; rule-3 line "four sub-leaves (two
  kernel-checked)"; row-57 bullet with the full A-57-1 summary.
- §7: OPEN_ITEMS all closed (E-16/B-05 stays a note); STATUS header 15:15Z; receipt count 108 + marker; the audited-declarations bullet
  (→ 49 212, +2 370; 716 entries; 192 audit rows at 15:16Z); `#print axioms` evidence list + receipts 14:57Z/15:16Z/15:36Z; review
  timestamps incl. 15:14:16Z; wave-2 tally final (0 open; the "two vs four corrected forms" counting note); delivery bullet (gen_tables_v2,
  192/192, stats diff); MANIFEST bullet (registry line correct again; FINAL_REVIEW.md line to refresh); stage-1.json bullet (PASS receipt;
  the two 50-byte FAIL logs; the audit now stage-1); NEW bullets: "191 mapped vs 192" explained; the G-07 / D-DOC-3 / D-DOC-4 episode;
  row-57 bookkeeping nits (header stamp 14:52Z vs notes 14:53Z; review_utc 15:14:16Z vs entries 15:15Z; "three" vs four sub-leaves; the
  receipts' one differing `bundle_sha256` entry; "67 files" = 66 + registry); the placeholders bullet → the markers bullet above.

## (c) What was verified, and how (all read-only, 15:16Z-15:45Z)

- `python3 tools/progress.py --once` (15:18Z, 15:21Z): 132/132, 192/192, 8/8, awaiting review 0. `python3 tools/claims.py --json`: 132/132,
  184 units. `python3 tools/claims.py --pending-only`: empty table.
- `gen_tables_v2.py` (15:20Z, against the 15:16Z `declaration-audit.json`): 192 audit rows, 192 hashes, 192/192 statement hashes equal,
  192/192 verdicts faithful, patterns {std 115, std+LM 21, 9 20, std+H+LM+LMU 17, std+H 11, std+LM+LMU 2, std+LM+NG 2, std+SC 2, std+NG 1,
  std+H+HD+LM+LMU 1}, per constant H 49 / LM 63 / LMU 40 / NG 23 / HD 21 / SC 22, kinds 177 theorems / 10 definitions / 5 axioms, no
  sorryAx, no unregistered axiom, `ng_finite_word` the only declaration without Classical.choice/Quot.sound, 184 old lines 0 mismatches.
  Diff to the drafter's `stats.json`: only the row-57 increments.
- 15:45Z re-check against the 15:35Z stage-1 audit (`tail` of the 1.08 GB file, `statement_hashes`): 191 hashes, 191/191 equal for the
  stage-1 rows; `lem:weak-open` absent from that audit (outside stage 1), not a mismatch.
- Receipts read: `dev-check-row57-implemented.json` (14:57Z; 192 / 49 212; 716 `project_sha256` entries), `dev-check-row57-accepted.json`
  (15:16Z; same counts; differs from the former in one `bundle_sha256` entry, `lean-declarations.json`; byte-identical to
  `stage-development.json` at 15:16Z), `dev-check-FINAL-20260919.json` (15:36Z; 192 / 49 212; = `stage-development.json` now),
  `stage-1.json` (15:35Z; passed, stage 1, 191 / 49 207, stage_accepted true; = `stage-check-FINAL-20260919.json`). `RALedgers`,
  `GenericTransport`, `CornerChainUnits` hashes equal between the 13:28Z and 15:16Z receipts.
- Logs: `checker-all-run-20260919_1525Z.log` and `_1529Z.log` = "FAIL: source review hash mismatch: ng:finite-word" (50 bytes each);
  `_1533Z.log` begins `"all_required_stages_passed": true` with the stage-1 receipt. `rc 0, 133 s` and `lake build 521 s, 4 295 jobs` are
  quoted from AUTHOR_NOTES 15:29Z/15:36Z (not re-measured).
- Row 57: `work/reviews/lem-gauss-two-discs.json` read in full (verdict faithful; 7/8/6 discrepancies and 5/5/5 strengthenings for the
  literal/definitions/strength lenses; `weaker_than_source` empty ×3; two refuters `refuted: false`; `review_utc` 15:14:16Z;
  `kernel_check` quoting axioms standard, checker 14:57Z 192 / 49 212); modules `wc -l` 274 / 4 972 / 5 462 / 7 385 / 2 811 / 92 = 20 996,
  headers "Ported 14:52Z"; draft files `wc -l` (W2_Assembled 20 912, W2_U5..U9, reports); `W2_ASSEMBLY_REPORT.md` and `port/PORT_REPORT.md`
  key lines (0 errors, 0 sorry declarations, 96 × standard axioms, 1 467 declarations, 80 → 15 warnings, IDENTITY OK). The axiom set is
  quoted from those records and the review — the finisher did not run lean (the closing build was running; instruction).
- Library: `find work/lean -name '*.lean' | wc -l` = 712; total lines 366 040; per directory SM 658 / CV 32 / RProof 15 / Bridge 5 /
  Supplemental 1 + `Supplemental.lean`; `grep -rli sorry work/lean --include=*.lean | wc -l` = 0 (15:18Z and 15:42Z, after patch 09).
- Counts: `dev-check-*.json` 107 at 15:16Z → 108 at 15:36Z (by mtime 27/53/18/2/8); `MANIFEST.sha256` 191 lines, mtime 2026-09-16 02:33Z;
  `work/delivery/receipts` 156, `reviews` 868 files; root `FINAL_REVIEW.md` and `work/delivery/FINAL_REVIEW.md` unchanged (02:33Z).
- Registry: `sha256sum blueprint/AXIOM_REGISTRY.md` = `2d00dec7…` = the MANIFEST line; mtime 15:29Z; `grep -c "descent sentence"` = 0.
  Patches: `grep '^+++'` over the ten standing patches → 66 files; the registry patch → `blueprint/AXIOM_REGISTRY.md`.
- D-DOC-4: `work/reviews/ng-finite-word.json` `source_sha256` = `fa17a1b1…` = `sha256sum reference/SM/sm-3-statesum.tex`; its
  `executor_notes` ends with the recorded correction; mtime 15:33Z.
- Stage-1 scope: `tools/check_lean.py` `selected_rows` (stage1 = Y source rows minus SKIP/CERTIFICATE + EXTRA in focused mode); in the map
  only `lem:weak-open` has `stage1: false` (the R/Bridge/SM rows have `null` and enter through EXTRA).

## (d) Caveats the executor should know

- The closing steps (4)-(7) and the post-install checker re-run had not happened at 15:55Z; the seven marker texts above are the only
  double-angle-bracket tokens in the file. After filling them, re-run the development checker, THEN refresh the MANIFEST line for
  `FINAL_REVIEW.md`, THEN `verify_bundle.py`, `refresh.sh`, the tarball — the text of §4.9 promises that order.
- Two sentences carry my own timing ("completed at 15:20-15:55Z (11:20-11:55am ET)" in the header; "re-verified 15:45Z" in the receipt
  fill); adjust if the install happens much later.
- The header's "State at 15:21Z" and §1's `work/PROGRESS.md` quote are from `progress.py` at 15:18:57Z/15:21:30Z; the progress line
  still said "Stage 1: not established by a current checker receipt" then (stage-1.json was written at 15:35Z) — §1 and §4.9 say so.
- The `#print axioms` value for `SM.lem_gauss_two_discs` is quoted from the U12 census, PORT_REPORT §1, the executor's 14:55Z probe and
  the review's `kernel_check`, not re-run by the finisher.
- The kernel-checked status of the four D-TD-2 counterexamples is stated as recorded: U4's and `U5_pushforward_edges`' kernel-checked
  (AUTHOR_NOTES 11:37Z, 13:39Z), U3's (L ≤ 0) and `U5_exists_ear_homeo`'s (reflex ear) "shown by explicit configurations".
- `declaration-audit.json` is now the stage-1 audit (191 rows); anyone regenerating the tables must use a development audit (re-run
  `check_lean.py work/lean` first) or accept `lem:weak-open`'s absence.
- `scratchpad/frdraft2/` (this session's scratchpad) holds `claims.json`, `tables.md`, `stats.json`, `gen_tables_v2.py`, `make_v2.py`,
  `fix_v2.py`; nothing under `work/lean`, `reference/`, `provenance/`, `blueprint/` was touched.
