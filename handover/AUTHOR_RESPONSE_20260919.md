# Author's response to OPEN_ITEMS_20260916.md §G — 2026-09-19

To the next executor of `CORNER_LAWS_FOCUSED_20260912` (frame SM15). This document answers every
decision reserved for the author in `OPEN_ITEMS_20260916.md` §G and `work/RESUME_FOR_NEXT_AGENT.md` §7.
Record it verbatim in `work/AUTHOR_NOTES.md` as a dated entry `D-AUTH-20260919`, the way D-GAP2 was
recorded at AN L5144, then resume. Nothing below changes an accepted row by itself.

## 0. The answer in one line

Continue to completion. Cost, time, estimate overruns and the number of previous attempts are not
grounds for stopping any branch. Both stopped branches (row 110 and row 177) are re-opened now, with no
bound. Row 57 is un-deferred.

## 1. Decisions, by register item

**G-01 — Row 110 `thm:C-S7`: YES.** Fund the remainder (the S1′ restatement, S3, B1, B2, B3; about
8-12k lines, over as many waves as it takes). Resume per OPEN_ITEMS §A-02 in the order of
`work/drafts/corner/W3_ASSEMBLY_REPORT.md` §7. Then rows 127 and 128 (§A-13, §A-14), then row 184
(§A-20 to §A-22).

**G-02 — Row 177 `R:extreme_selected`: YES.** Fund the remainder: `w3cx_outer_residue_data` (§A-16)
and `w3cs_not_kink_site_data` (§A-17), the port-time statement edits (§A-18), then rows 178 and 183
(§A-19), then row 184.

**G-02b — the non-kink condition at the 177 site (§A-17).** First attempt the derivation from the
177 configuration data, routes (i)/(ii) of `work/drafts/moves/W3C_SITE_REPORT.md` §4: the two carrier
edges of `x_ef` are not at cyclic distance 2 in `geoCornerPolygon`, argued through the Gauss-word /
adjacency data or through `LocalizationData`'s disc. If no derivation is found after one substantive
attempt, the executor MAY add the non-kink condition as an explicit hypothesis on the RIII event
(route (i) of SITE §4: `e`, `f` not at label distance 2 in `P`, and no `T`-crossing on `e` or `f`
between the polygon vertex and `x_ef`), in whatever form the executor judges least invasive. An edit
to accepted event vocabulary for this purpose is authorised, with a checker re-run and a re-review of
any accepted row whose statement changes. Disclose it as a narrowing (FR-R-177-K) in the row's
review record and in FINAL_REVIEW §5. Do not stop to ask again.

**G-03 — `RProof.G11_Config.trans`: executor's choice.** Both routes are authorised: (i) drop the
field `trans` from the accepted module `work/lean/RProof/GenericTransport.lean` (line 125), then
checker re-run and re-review of any accepted row whose statement unfolds `G11_Config` (none is
expected); or (ii) port the additive trans-free copy `G11_ConfigSw` / `G11_ParamsSw`. Take the faster.

**G-09 — Row 57 `lem:gauss-two-discs`: UN-DEFERRED. Prove it.** The 2026-09-15 instruction "Row 57
stays deferred" (D-GAP2 item 5) is withdrawn. Start from `work/drafts/pldiscs/PLDISCS_FEASIBILITY.md`
and the lane pattern of RESUME §5. It gates nothing but the stage check, so it may run in parallel
with rows 110 and 177.

**G-06 — the `verify_bundle.py` relaxation (label-part comparison, D-GAP2-2b): CONFIRMED** as the
permanent data model. One literature label may carry several declarations. Do not revert it.

**G-05 — comment-only edits inside accepted modules: AUTHORISED**, provided no declaration, statement
or proof body changes and the checker is re-run afterwards. Clear the docstring debts of §E.

**G-07 — registry sub-entry: AUTHORISED.** The executor may add one sub-entry for
`SM.lit_homfly_descent` under "## lit:homfly — AXIOM" in `blueprint/AXIOM_REGISTRY.md`. No other
change to the blueprint.

**G-08 — the bundled descent axiom: KEEP** `axiom SM.lit_homfly_descent : AmbientIsotopyDescent` as is.

**G-04 — the false-as-stated fields of `est_PortData` / `esc_MoveData`: KEEP** the literal fields
and the weak replays. No edit to accepted modules. FINAL_REVIEW §5 items 6 and 11 remain the record.

**G-10 — human review of the AI-only verdicts: not required for completion.** The author arranges it
separately. Do not wait for it.

**G-11 to G-15: optional.** Not required for completion. Do one only if a pending row needs it.

## 2. Standing rule change: the consequence of a failed audit

Keep the reassessment audits. They are what found the false S1 leaf and the kink case. But the
consequence of a failed audit changes:

- A branch stops only for a mathematical blocker: a row statement believed false (then a kernel-checked
  counterexample under `work/repairs/`, as the package rules already require), or a needed assumption
  that is not in the printed proof and is not covered by §1 above (then the exact question, in one
  paragraph, in AUTHOR_NOTES and STATUS, while work continues on every other branch).
- A failed audit on cost, time, estimate overrun or number of attempts never stops a branch. Record
  the audit, change method if the audit says so, and continue.
- No branch needs a new authorisation from the author to be re-opened. This paragraph supersedes the
  consequences recorded in audits A-110-1 and A-177-2 and the rule of thumb in OPEN_ITEMS §F-06.

## 3. Definition of done

`python3 tools/check_lean.py work/lean --all` passes; claims verified 132/132; checklist 192/192;
final targets 8/8; FINAL_REVIEW.md complete, with every axiom footprint and every disclosed narrowing
recorded; `python3 verify_bundle.py` PASS; a checkpoint tarball of the final state.

## 4. Practical notes

- Resume from the archive `LEAN_HANDOVER_20260916_0233Z.tgz` (sha256 `ada22b6c…`), which is the
  02:33Z 2026-09-16 state. The build directory is not in it; rebuild with `bash setup.sh` or
  `lake build` on a machine with at least 32 GB of RAM.
- Keep the 15-minute progress reports, the one-checker-at-a-time rule, the AUTHOR_NOTES discipline,
  and the checkpoint tarballs every 1-2 hours.
