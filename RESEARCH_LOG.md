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
