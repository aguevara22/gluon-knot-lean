# Research log — leaning (Lean formalization handover)

Internal progress log; not subject to the writing guidelines.

## 2026-09-14 — Unwrapped `lean_handover_mark.tgz`; independent status audit

**What arrived.** `lean_handover_mark.tgz` (106 MB, 5,942 entries, no absolute paths) from Mark's pod executor,
built 2026-09-14 21:15 UTC. Extracted in place to `CORNER_LAWS_FOCUSED_20260912/` (248 MB), `handover_extras/`
(pod CLAUDE.md, Mark's reassessment rule, the executing session's memory files) and `HANDOVER_README.md`.
Package = Lean 4 formalization "Corner state sum: wall laws and soft theorem", source frame SM15 (frozen 2026-09-12),
final declaration `SM.corner_laws_and_soft`. Pins: Lean `v4.34.0-rc2`, Mathlib `85e3a25e006c`.

**Self-reported state (handover):** claims verified 109/132; checklist rows 168/192 accepted; final targets 4/8
(prop:C-chamber, prop:C-silent, thm:C-S3, thm:C-S5); zero sorry; four registered literature axioms; stage check
`--all` INCOMPLETE (24 rows).

**Independently verified here (static, no build):**
- 667 `.lean` files, 247,952 lines (628 SM, 28 CV, 5 RProof, 4 Bridge, 2 Supplemental).
- Comment-stripped token scan over all 667 files: 0 `sorry`, 0 `admit`, 0 `native_decide`; no `unsafe`,
  `implemented_by`, `@[extern]`, `opaque`, `partial def`; `set_option` only linter/maxHeartbeats.
- Exactly four `axiom` declarations: `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness` (SM/LinkInterfaces.lean),
  `SM.ng_finite_word` (SM/FrontInterfaces.lean). `SM.src_contact` never declared.
- Every one of the 671 files hashed in the origin's final checker receipt (`work/checks/stage-development.json`,
  passed=true, 168 mapped, 36,079 audited) matches byte-for-byte on disk; no extra `.lean` files. The 38 bundle
  files in the receipt match too. So the shipped sources ARE the state the origin checker built and passed.
- Declaration map: 168 accepted / 24 pending; every accepted row has a review file, author ≠ reviewer, and a
  statement hash that matches the shipped audit (`work/delivery/receipts/declaration-audit.json.gz`): 168/168.
- `tools/progress.py --once` → 109/132, 168/192, 4/8; `tools/claims.py --pending-only` → the same 24 rows as the
  stage log `work/checks/stage-all-attempt-1806.log` (22 GAP-2 claim rows + row 57 + src:contact).
- 12 fixed-name target declarations are absent from the sources (thm_C_S7, thm_C_soft, thm_comparison,
  cor_C_inherits, corner_laws_and_soft, Bridge.sm_R, RProof.cv_R, RProof.generic_selected / extreme_pair_zero /
  extreme_transport / extreme_selected, SM.src_contact) — consistent with the pending list.
- Axiom footprint over accepted rows: lit_homfly 28 rows (incl. all four accepted targets, hyp:R, CV:ax:R, B4),
  lp_lm 42, lp_lm_uniqueness 19, ng_finite_word 3; 114 rows use only propext/choice/Quot.sound.
- Work/delivery MANIFEST.sha256: 930/930 OK.

**Discrepancies / hygiene found:**
1. `python3 verify_bundle.py` exits 1: root `MANIFEST.sha256` still holds the 2026-09-12 hash of `FINAL_REVIEW.md`,
   which the executor completed on 09-14. Consequence: `bash setup.sh` as shipped would STOP at its verification
   step (after the build, before `check_lean.py`). Fix = refresh that one manifest line, or run the checker directly.
2. The development checker's build+audit does not reach 3 modules: `Bridge/SmR.lean`, `SM/CeRoundingNonVacuity.lean`,
   `SM/ContactPathOfDescent.lean` (unmapped conditional library). They are covered by `lake build` only.
3. Two accepted rows have a non-accepted blueprint prerequisite: cb:embedded-rotation ← lem:gauss-two-discs (D-ER1,
   recorded), thm:uniqueness ← prop:anchor-values (recorded nowhere I found; kernel-wise harmless, blueprint deviation).
4. Stray 7-byte file `=3` at the package root (shell artefact, not in the manifest).
5. Reviews are AI-only (same model family as the implementer, disclosed); no human has read any of the 168.

**Not verified: the full rebuild.** Attempted the compute-policy route (GCP c3-standard-8, ~$0.70) — the harness
permission classifier denied `gcloud compute instances create` ("Modify Shared Resources"). Declined a full local
build (~20-40 min on 8+ cores) under the laptop compute policy. Light smoke test done instead: `work/lean/.lake`
→ symlink to `~/leanbuild/corner_laws_20260912.lake`, whose `packages/` is an APFS clone of
`~/Documents/ChatGPT/surfaceleanology/.lake/packages` (all 9 pins identical; mathlib 85e3a25e fully built,
8,381 oleans). `lake env lean Supplemental/Audit.lean` OK (18 s); `lake env lean SM/Polygon.lean` OK (21 s).
Full build when allowed: `cd work/lean && lake build`, then `python3 tools/check_lean.py work/lean`
(expect passed=true, 168 mapped, 36,079 audited).

**The blocker (GAP-2), in one paragraph.** Row 91 cp:finite-contact-path needs "ambient isotopy of links ⇒ equal
HOMFLY". The printed literature input lit:homfly ends "Its value depends only on the oriented link presented by D"
(status line cites Reidemeister for the descent), but the executor's design decision D2 rendered that clause as
`HomflyClauses.descent : LinkEquiv D D' → H D = H D'` (planar isotopy + the three moves between polygonal
diagrams), i.e. weaker than printed, with "no sixth axiom". Row 91 is proved modulo the single Prop
`SM.AmbientIsotopyDescent` (SM/ContactPathOfDescent.lean, statement reviewed clean). 22 claim rows sit behind it,
including all four remaining targets and the final theorem. Routes (work/drafts/gap2/CPRow91_PLAN.md §7):
(α) restate the axiom's descent clause spatially — small code, but it rewrites an accepted declaration and forces
re-review of the 28 rows using lit_homfly; (α') split form `AmbientIsotopyDescentLit ∧ IsotopyExtension`
(second part ~3-5k lines of analysis); (β) prove Reidemeister's theorem for smooth isotopies (multi-thousand
lines). Also open: row 57 lem:gauss-two-discs (PL Jordan–Schoenflies, 12-20k lines, deferred; not on the critical
path) and src:contact (statable any time; consumers blocked).

**Decision needed from the owner:** GAP-2 route. Nothing else moves the count.

## 2026-09-14 (later) — Big-picture view: the proof DAG published

Built an interactive dependency graph of the package: nodes = the 192 checklist rows (`work/lean/lean-declarations.json`),
edges = the 443 blueprint edges (`blueprint/DEPENDENCIES.json`), colour = acceptance state, pending reasons quoted from
FINAL_REVIEW.md §3. Two views: (1) the critical path (31 nodes: 24 pending + 8 targets + lit:homfly, hyp:R, CV:ax:R),
laid out top-down in six columns; (2) all rows in eleven chapter swim lanes, prerequisites to the left, with pan/zoom,
lane filters, a "what blocks the final theorem" mode, and a detail panel (needs / needed by / root causes).
Facts the graph makes explicit: only 3 pending rows have all prerequisites accepted (91 cp:finite-contact-path,
57 lem:gauss-two-discs, src:contact); every other pending row traces back to 91 and/or src:contact; row 57 has no
pending consumer. Layer depth: 16 for the full graph, 11 for the critical chain.
Published: https://claude.ai/artifact/PVbJdqo11QXKqNdeYKyb1x (private). Local copy: `leaning/corner_laws_proof_graph.html`.
Generator: scratchpad `build_dag.py` + `dag.tmpl.html` (not in the project; re-runnable against the package).

## 2026-09-15 — Owner decision on GAP-2: restate

Owner (Seif) decided: restate the HOMFLY axiom so it carries the printed descent clause. Recommended concrete form:
declare the clause as its own Lean axiom about the existing `SM.homfly` (the Prop `SM.AmbientIsotopyDescent` already
exists in SM/ContactPathOfDescent.lean), register it in `work/lean/axiom-policy.json` under lit:homfly, interface-review it
against sm-3:920-921, and close row 91 with `cp_finite_contact_path_of_descent`. This touches no accepted declaration
(`homfly`'s definition is unchanged), so the 28 consumers keep their statement hashes and need no re-review. Work continues
on Mark's pod (review workflows, keys, executor memory live there). Also asked: declare src:contact (needed by rows 94, 161),
refresh the FINAL_REVIEW.md line in the root MANIFEST.sha256, delete the stray `=3`.
Build question clarified for the owner: "build" = Lean re-checking all 667 files (~20-40 min on 8 cores); the tarball
shipped no checked outputs; Mark's receipts + byte-identical hashes stand in for a local run until one is allowed.

## 2026-09-15 — Private GitHub repository created and seeded

`https://github.com/aguevara22/corner-laws-lean` (private; owner aguevara22; Mark not added yet). Working copy at
`~/repos/corner-laws-lean` (outside iCloud; `work/lean/.lake` symlinked to `~/leanbuild/corner_laws_20260912.lake`).
Layout: the package as `CORNER_LAWS_FOCUSED_20260912/`, `handover/` (Mark's note + session memory), `docs/` (GAP-2
decision record, proof-graph SVGs, interactive page, generators), `tools_extra/static_audit.py`, this log, README with
the Mermaid critical path and the full-graph image.
Trap found while seeding: the package's own `.gitignore` starts with `work/`, so the first commit silently held only 163
files (no Lean code). Fixed by dropping that line; the root MANIFEST.sha256 was refreshed for `.gitignore` and
`FINAL_REVIEW.md`, after which `verify_bundle.py` passes and the static audit reports PASS with 0 warnings. The stray
`=3` file was removed. No other package file changed; receipt hashes still match. Seed commit amended and force-pushed
(repo minutes old, no collaborators). 5,668 files, largest 1.6 MB.
Next: add Mark when the owner says so; add the static audit as a GitHub Action; executor switches to commit-per-row.

## 2026-09-19 — Status audit of the 2026-09-16 handover; the author's response drafted and sent

**What arrived.** `LEAN_HANDOVER_20260916_0233Z.tgz` (126 MB, sha256 `ada22b6c…`), the pod executor's state at 2026-09-16
02:33 UTC after the GAP-2 work of 09-15/16. Self-reported: claims verified 124/132; checklist 184/192; targets 5/8;
697 `.lean` files, 295,911 lines; zero sorry; six literature axiom constants for the five interfaces (the descent axiom
`SM.lit_homfly_descent` added on D-GAP2); `check_lean.py --all` FAIL by design (eight rows pending).

**Independently verified here (static, no build):** `verify_bundle.py` PASS (191 files); root MANIFEST 191/191; comment-stripped
scan 0 `sorry`; exactly six `axiom` declarations; final development receipt `dev-check-FINAL-20260916.json` passed, 184 mapped,
41,658 audited, and all 701 file hashes in it match the shipped `work/lean`; `claims.py --pending-only` = the same eight rows
as the stage log (57, 110, 127, 128, 177, 178, 183, 184); the two tarball copies in Downloads are byte-identical.

**What was blocking.** Not mathematics: the reassessment rule. Both remaining branches had failed two or more bounded attempts
(corner branch 110: three waves + one bounded wave, original estimate 11–15k lines, ~24k produced and 8–12k still owed; R branch
177: two windows + wave 3c), so the audits A-110-1 and A-177-2 recorded "no further construction; a decision for the author".
Row 57 had been deferred by the 09-15 instruction. One genuinely mathematical finding: at the 177 site the intermediate Prop
"the lift crossing over x_ef is not a kink" does NOT follow from the site data (SITE §4 exhibits a kink loop satisfying
D4, D5, clear, clear_vertex), and `IsSimpleRIII` forbids adjacent triangle edges but not label distance 2.

**Owner decision (Seif), 2026-09-19:** continue to completion; cost, time and attempt counts are not grounds for stopping;
rows 110 and 177 re-opened with no bound; row 57 un-deferred; G-02b: one substantive derivation attempt at the non-kink
condition, then an event-level non-kink hypothesis admissible with disclosure; G-03 either route; G-05/G-07 authorised;
G-06 confirmed; G-08/G-04 keep; G-10 not required for completion. Drafted as `AUTHOR_RESPONSE_20260919.md` (now
`handover/AUTHOR_RESPONSE_20260919.md`), sent through Mark; recorded verbatim on the pod as `D-AUTH-20260919`
(AUTHOR_NOTES L6520) at 05:36 UTC.

## 2026-09-20 — FINAL result received and verified; repository brought to the final state

**What arrived.** `FINAL/RESULT_FINAL_20260919_1554Z.tgz` (142 MB, sha256 `40c1be0b6f709aa80d2b79026d3c10764a21a9bb132009eac63bab0a06b4baae`,
matches `RESULT_FINAL_NOTE.md`), the pod executor's closing state, 2026-09-19 15:55 UTC — about ten and a half hours after
the response was recorded. Timeline (work/STATUS.md): 05:35Z resumed (the pod had OOM-restarted on 09-18; volume state
intact); 08:39Z rows 177/178/183 accepted; 13:26Z rows 110/127/128/184 accepted; 15:14Z row 57 accepted; 15:36Z
`check_lean.py --all` PASS; 15:55Z tarball.

**Self-reported:** claims verified 132/132; checklist 192/192; targets 8/8; stage 1 PASS (191 mapped, 49,207 audited);
development 192 / 49,212; zero sorry; the nine registered axioms.

**Independently verified here (static, no build):**
- Extraction byte-identical to the tarball (6,741 files, 0 differing).
- `verify_bundle.py` PASS (191 files); root MANIFEST 191/191; `claims.py --pending-only` empty; `progress.py --once` 132/132,
  192/192, 8/8.
- 712 `.lean` files, 366,040 lines (658 SM, 32 CV, 15 RProof, 5 Bridge, 1 Supplemental, + Supplemental.lean);
  comment-stripped scan 0 `sorry`/`admit`/`native_decide`; 0 `#print`/`#eval`; exactly the same six `axiom` declarations as on 09-16.
- `work/checks/stage-1.json`: passed, stage 1, stage_accepted, 191 mapped, 49,207 audited; its `project_sha256` (716 files)
  matches the shipped `work/lean` 716/716; its `evidence_sha256` (191 review files) matches `work/reviews` 191/191; its
  `bundle_sha256` matches every frozen root file except `FINAL_REVIEW.md` (see caveat). `stage-development.json`: passed,
  192 / 49,212, 716/716. `checker-all-run-20260919_1533Z.log` first line `"all_required_stages_passed": true`.
- Declaration map: 192/192 accepted; every accepted row's `review_file` exists, all 528 lens verdicts `faithful`, no refutation.
- Shipped audit (`work/delivery/receipts/declaration-audit.json.gz`, 49,212 checked): `SM.corner_laws_and_soft`,
  `SM.thm_C_S7`, `RProof.extreme_selected`, `RProof.cv_R`, `Bridge.sm_R`, `SM.thm_comparison`, `SM.cor_C_inherits` each carry
  exactly the nine registered axioms, no sorryAx; `SM.lem_gauss_two_discs` standard axioms only. Usage over the 192 rows:
  lp_lm 63, lit_homfly 49, lp_lm_uniqueness 40, ng_finite_word 23, src_contact 22, lit_homfly_descent 21.
- Final theorem: `theorem corner_laws_and_soft : CornerLawsAndSoftData := corner_laws_and_soft_of Bridge.sm_R thm_C_S7
  thm_C_soft (cor_C_inherits Bridge.sm_R)` (`work/lean/SM/CornerLawsAndSoft.lean`); no R parameter remains.
- Static audit (`tools_extra/static_audit.py`): PASS, 0 warnings (output in README §5).

**How the three hard rows closed.** Row 177: the non-kink question resolved WITHOUT any hypothesis — the intermediate Prop
was indeed false as stated (the monogon e → e+1 → e+2 = f cut by g is a genuine 177 configuration), but the obligation the row
needs was proved in its HOMFLY-value form in both cases, the kink case by a flat subdivision of the one-component lift
(`w3dk_*`); G-02b not used, no narrowing; G-03 route (ii) (additive trans-free copy `RProof/GenericTransportSw.lean`,
7,845 lines; accepted module untouched). Row 110: corner waves 4–6 (`W6_Assembled.lean` 27.5k lines; `SM/CS7Units.lean`
27,000 lines), audits A-110-1/2. Row 57: 21k lines over six `GaussTwoDiscs*` modules, standard axioms only; four internal
skeleton sub-lemmas false as stated, replaced by corrected proved forms (two with kernel-checked counterexamples); the row
statement unchanged. Housekeeping: ten comment-only patches applied (G-05); the G-07 registry sub-entry applied and reverted
(D-DOC-3: it changed the frozen registry's hash, which the stage check binds through row ng:finite-word).

**Caveats carried forward.** (1) `FINAL_REVIEW.md` was rewritten after the last checker run (15:52Z receipt vs 15:54/15:55Z
text), so the receipts bind the code, the reviews and the frozen sources but not the final review text; `progress.py` prints
"Stage 1: not established by a current checker receipt" for that reason. A fresh `bash setup.sh` + `check_lean.py --all` on a
32 GB machine would close it; not done outside the pod. (2) Unchanged disclosures: five admitted literature interfaces as six
axiom constants, the descent axiom by the author's decision (21 accepted rows incl. the final theorem depend on it); every
review AI-written, none read by a human. (3) Documentation only: U8's duplicate fan toolkit in row 57 (73 declarations),
15 linter warnings, row 174's σ orientation note recorded in FINAL_REVIEW §5 rather than AUTHOR_NOTES.

**Repository.** `CORNER_LAWS_FOCUSED_20260912/` replaced by the final package (rsync, `.lake` symlink kept). Relative to the
tarball exactly two files differ, both repo-only as on 09-15: `.gitignore` (the `work/` line dropped) and `MANIFEST.sha256`
(refreshed for `.gitignore` with the package's own `work/port/refresh_manifest.py`; `verify_bundle.py` PASS); eight `__pycache__`
`.pyc` files not copied. Added: `handover/AUTHOR_RESPONSE_20260919.md`, `handover/RESULT_FINAL_NOTE_20260919.md`,
`handover/handover_extras_20260916/`. Figures in `docs/` regenerated from the final map (`build_dag.py` patched for the
all-accepted case). Tag `final-20260919-1554Z`.

**Open question raised by the owner: fidelity against a letter instead of SM15.** Yes, in principle and in practice: a Lean
theorem's meaning is fixed by its statement, the definitions that statement unfolds to, and the axioms — never by the proofs.
The shipped audit lists the final theorem's statement closure: 383 project declarations, all in the SM namespace (234
definitions, 26 inductive types, 96 lemmas used inside definitions, 26 structures/instances, 1 axiom — `SM.lit_homfly`, because
`SM.homfly` is `Classical.choose` of it), on top of Mathlib. A "statement package" (those declarations with every proof
stripped, the six axioms, the theorem's type, and the kernel's axiom list as the certificate) is the object to check a letter
against; `work/port/strip_proofs.py` and the audit's `semantic_dependencies` are the existing tools. Not built yet.

## 2026-09-21 — README rewritten as a self-contained project description

On the owner's request the README no longer narrates the execution history. It now states what is proved (the
nine clauses with their printed identities and the Lean structure), what it rests on (the five admitted interfaces
with the descent sentence flagged), how to read the statement without the proofs (the 383-declaration closure,
now listed in `docs/statement_closure.md`, generated by `docs/graph/statement_closure.py` from the shipped audit),
how it was checked, the layout, the four caveats that matter, and a short provenance note. History and process
details remain in this log, `FINAL_REVIEW.md`, `work/AUTHOR_NOTES.md` and `handover/`.
