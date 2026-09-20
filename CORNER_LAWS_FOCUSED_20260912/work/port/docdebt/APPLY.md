# work/port/docdebt — the §E documentation-debt patches (prepared 2026-09-19, NOT yet applied)

Prepared 2026-09-19 by a documentation agent of the pod executor from `OPEN_ITEMS_20260916.md` §E, under the
author's authorisation **D-AUTH-20260919** (`work/AUTHOR_NOTES.md`, items **G-05**: comment-only edits inside
accepted modules, provided no declaration, statement or proof body changes and the checker is re-run; **G-07**:
one sub-entry for `SM.lit_homfly_descent` under "## lit:homfly — AXIOM" in `blueprint/AXIOM_REGISTRY.md`, no
other blueprint change). Nothing under `work/lean/`, `blueprint/` or `work/drafts/` has been modified: every
change is a reviewable unified diff in this directory, generated with `diff -u` against a scratch copy. The
executor APPLIES them at the next build cycle.

**Mechanical guarantee.** `check_comment_only.py` (this directory) classifies every line of a Lean file with a
comment scanner (nested `/- -/`, `/-- -/`, `/-! -/`, `--`, string literals respected) and asserts that the
sequence of non-comment lines (code text and blank lines outside comments) is IDENTICAL before and after each
patch. It was run on all eleven patches against the live package root (in a temporary copy) at preparation:
`RESULT: comment-only`. Re-run it before applying (30 s, no Lean, no lake):

```
cd <package root>
python3 work/port/docdebt/check_comment_only.py --root . \
  --patches work/port/docdebt/0*.patch work/port/docdebt/10-*.patch work/port/docdebt/registry-sub-entry.patch
```
(`.md` targets — patch 10 and the registry patch — are reported "not checked (not Lean)"; review them by eye.)

## 1. The patches, in application order

Paths inside the patches are package-root-relative (`work/lean/…`, `blueprint/…`, `work/drafts/…`); apply every
one from the package root with `patch -p0`. The order matters where two patches touch the same file
(01→02→07 on `SM/ContactPathOfDescent.lean`; 04→06 on `SM/CornerChainUnits.lean`; 07→08→09 on
`SM/LinkInterfaces.lean`; 08→09 on `SM/LinkLaurentRing.lean`; 07→09 on `SM/LinkMoves.lean`, `CV/Axioms.lean`):
a later patch was generated against the state AFTER the earlier ones. Skipping a patch is safe only for the last
one on each file (09 and 10 and the registry patch can each be omitted freely; omitting an earlier one may make a
later hunk on the same file apply with an offset or fail — then regenerate rather than force).

| # | patch | §E item | files (line ranges BEFORE → AFTER) | what changes |
|---|---|---|---|---|
| 01 | `01-E01-contactpathofdescent-descent-axiom-docstrings.patch` | E-01 | `work/lean/SM/ContactPathOfDescent.lean` 11→11-14 (module docstring "never mapped unless GAP-2 closes"), 54-55→57-61 (§1 "a def : Prop, not an axiom"), 173-174→179-185 (docstring of `def AmbientIsotopyDescent`) | each now says the assumption LIVES in `SM/LitHomflyDescent.lean` as the registered axiom `SM.lit_homfly_descent : AmbientIsotopyDescent` (policy label "lit:homfly (descent sentence)", D-GAP2, review `work/reviews/lit-homfly-descent.json`; row 91 = `cp_finite_contact_path_of_descent lit_homfly_descent`) |
| 02 | `02-E02-contactpathofdescent-tex-line-refs.patch` | E-02 | `work/lean/SM/ContactPathOfDescent.lean` lines 16, 24, 40-43, 50, 52, 63, 67, 69, 74, 109, 115, 119, 130, 169, 186, 215-216, 233, 242, 259, 280, 433, 490, 568, 578, 597, 611, 618, 623, 643, 690 (post-01 numbering; one number per line); `work/lean/SM/LitHomflyDescent.lean` 24 | tex locators re-read against `reference/SM/sm-3-statesum.tex`: descent sentence 3310-3312 (was 3313-3315/3313-3316), hand isotopy-extension 3276-3312 (was 3264-3313, 8 places incl. LitHomflyDescent:24), `ContactPathData` field ranges 3212-3214 / 3214-3219 / 3220-3222 / 3222-3225 (table, field docstrings and the (E-3)-(E-6) unit docstrings), statement 3212-3231, proof 3234-3326 (was -3327), lp:core step 3313-3314 (was 3316-3317 / 3314-3317), "Combining…" 3314-3315 (was 3317-3318), "The two actual diagrams" 3247-3250/3247-3255 (was 3243-3248/3243-3252), display cp:smoothing-record 3251-3255 (was 3249-3251), the η/concatenated-family paragraph 3259-3268 (was 3254-3262), display cp:flattened-family 3263-3268 (was 3258-3262). Locators found CORRECT and left: 3210-3233, 3235, 3238-3239 |
| 03 | `03-E05-fdcontactstatements-tex-line-refs.patch` | E-05 (line refs only) | `work/lean/SM/FdContactStatements.lean` 29, 37 | closing sentences 3419-3421 (was 3418-3421); "display fd:representative-bound (sm-3:3412-3418; the display itself 3416-3418)". `:35` 3409-3411 is correct and untouched. The axiom-count wording E-05 also names lives in AUTHOR_NOTES / review JSON / a receipt name, not in the module — nothing to patch there |
| 04 | `04-E06-thm-C-soft-proof-locator.patch` | E-06 | `work/lean/SM/CSoft.lean` 11; `work/lean/SM/CornerChainStatements.lean` 40, 273; `work/lean/SM/CornerChainUnits.lean` 6792 | "proof 992-1147" → "993-1147" (sm-4 `\begin{proof}` is line 993). E-06 counted three places; a fourth (CornerChainUnits:6792) is included |
| 05 | `05-E07-genericselected-docstring.patch` | E-07 | `work/lean/RProof/GenericSelected.lean` 28-29→28-31, 36-38→38-40 | "the three branches are the fields" → the bundle has TWO fields (`couple_canonical`, `couple_relabelled`, described); "the six literature interfaces" → six literature axiom constants under the five registered interfaces (`lit_homfly_descent` the second declaration of lit:homfly) |
| 06 | `06-E08-s7b-slidingmark-leg-M-caution.patch` | E-08 (+ §C-05) | `work/lean/SM/CornerChainUnits.lean` 3815→3815-3823 (docstring of `def s7b_slidingMark`), 3928-3929→3936-3938 (U110-B part III section comment), 3933→3942-3945 (docstring of `structure s7b_SlidingTransport`) | CAUTION added: the mark map / structure are right on the leg-(M−1) side only; on the leg-M side `nextMark μ_M = v_ℓ` makes `ret` false for every `vm` (RET rule 4); the corrected `s7r_slidingMark'` / `s7r_SlidingTransport'` live in `work/drafts/corner/W3_Assembled.lean` (report `W3_RET_REPORT.md` §2) with `ret` proved |
| 07 | `07-E10-five-interfaces-six-constants-wording.patch` | E-10 | `work/lean/SM/ContactPathOfDescent.lean` 55-56→55-58; `work/lean/SM/LinkMoves.lean` 758-759→758-762; `work/lean/SM/LinkInterfaces.lean` 48→48-50; `work/lean/CV/Axioms.lean` 69→69-72 | the four D2 sentences "no sixth axiom (is admitted)" — now contradicted by a sixth axiom CONSTANT — reworded to FR's vocabulary: Reidemeister's theorem is admitted as no axiom; `SM.lit_homfly_descent` is the descent sentence itself, the second declaration of lit:homfly; five literature interfaces, six axiom constants |
| 08 | `08-E11-stale-headers.patch` | E-11 (headers), AN 2026-09-13 "documentation defects (a)-(c)" | `work/lean/SM/FlatCarriersDefs.lean` 6, 12-13→12-14; `work/lean/Bridge/SmR.lean` +1 header line after line 1; `work/lean/SM/LinkLaurentRing.lean` 80-81→80-84; `work/lean/SM/LinkInterfaces.lean` 23, 39-41→39-43, 181-182→183-185; `work/lean/RProof/X1Rows3.lean` 27-28→27-29 | FlatCarriersDefs: "proved … when the prover units finish" / "proofs are `sorry`" → proved in SM/FlatCarriers.lean, accepted 2026-09-13; SmR: dated header note — GAP-2 closed by D-GAP2, `Bridge.sm_R` waits only on `RProof.cv_R` (row 178) ← row 177; LinkLaurentRing/LinkInterfaces (a): `T`/`R` separation is a review POLICY, `T = R` is `rfl` at default transparency; (b) `lmF` identified with the source function only through lp:lm-uniqueness; (c) header field-name drift "skein" → "[the field is named `sourceSkein`]"; X1Rows3: row 173 is accepted in RProof/GenericTransport.lean, `GT_G11` proved as `GT_G11_strong` |
| 09 | `09-E11-sorry-wording-in-headers.patch` | E-11 (the 55 "sorry-free"/"no sorry" headers) | 55 `.lean` files under `work/lean/` (list in §3), one or two header lines each (68 lines) | the string `sorry` leaves every module comment: "sorry-free" → "placeholder-free", "no sorry"/"no `sorry`" → "no placeholder", "never `sorry`" → "never a placeholder", "every `sorry` of the skeleton" → "every placeholder of the skeleton" (CChamber:31), "The `sorry`s are exactly the mp:stack chain of §6" → "The draft's placeholders (its §6, NOT ported here) are …" (PolynomialBlock:27). After 08+09: `grep -rli sorry work/lean --include=*.lean | wc -l` = 0 (was 55). OPTIONAL — meaning-neutral, largest footprint; the executor may omit it |
| 10 | `10-E19-plan-final-axiom-expectation.patch` | E-19 | `work/drafts/floor/PLAN_FINAL.md` §4, +5 lines after line 338 (a `>` note; nothing rewritten) | dated note: the "`SM.lp_lm` only / plus `SM.lit_homfly`" axiom expectation is stale — `cf_thm_carrierfloor_R`, `uf_z_parity` also depend on `lit_homfly`, `lp_lm_uniqueness`; accepted rows 99/100 carry the full nine (FR §4.3) |
| R | `registry-sub-entry.patch` | E-16 / B-05 / **G-07** | `blueprint/AXIOM_REGISTRY.md` +7 lines after line 18 (inside "## lit:homfly — AXIOM", before "## lp:lm — AXIOM") | a `###` sub-entry naming `SM.lit_homfly_descent : SM.AmbientIsotopyDescent` (module SM/LitHomflyDescent.lean; policy label "lit:homfly (descent sentence)"; D-GAP2 2026-09-15; review work/reviews/lit-homfly-descent.json, faithful, 3 lenses + 2 refuters, 2026-09-15T14:25Z; FR-LHD-1..4; not a sixth interface). Format matches the registry: heading, `reference/SM/sm-3-statesum.tex:920–921` locator, a verbatim ```tex block (the two source lines, byte-checked), prose. The five existing headings and blocks are untouched |

Total: 67 files (65 Lean modules, 2 Markdown files); 198 comment lines added or rewritten (142 removed-side lines), 0 code lines.

## 2. Exact commands

From the package root (`CORNER_LAWS_FOCUSED_20260912/`). Dry-run first, then apply; stop at the first failure.

```
cd /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912
python3 work/port/docdebt/check_comment_only.py --root . \
  --patches work/port/docdebt/0*.patch work/port/docdebt/10-*.patch work/port/docdebt/registry-sub-entry.patch
for p in work/port/docdebt/0[1-9]-*.patch work/port/docdebt/10-*.patch work/port/docdebt/registry-sub-entry.patch; do
  patch -p0 --dry-run --no-backup-if-mismatch -i "$p" > /dev/null || { echo "DRY-RUN FAILED: $p"; break; }
  patch -p0 --no-backup-if-mismatch -i "$p" || { echo "APPLY FAILED: $p"; break; }
done
```
Individually, in order (each is `patch -p0 --no-backup-if-mismatch -i <file>`):
```
patch -p0 --no-backup-if-mismatch -i work/port/docdebt/01-E01-contactpathofdescent-descent-axiom-docstrings.patch
patch -p0 --no-backup-if-mismatch -i work/port/docdebt/02-E02-contactpathofdescent-tex-line-refs.patch
patch -p0 --no-backup-if-mismatch -i work/port/docdebt/03-E05-fdcontactstatements-tex-line-refs.patch
patch -p0 --no-backup-if-mismatch -i work/port/docdebt/04-E06-thm-C-soft-proof-locator.patch
patch -p0 --no-backup-if-mismatch -i work/port/docdebt/05-E07-genericselected-docstring.patch
patch -p0 --no-backup-if-mismatch -i work/port/docdebt/06-E08-s7b-slidingmark-leg-M-caution.patch
patch -p0 --no-backup-if-mismatch -i work/port/docdebt/07-E10-five-interfaces-six-constants-wording.patch
patch -p0 --no-backup-if-mismatch -i work/port/docdebt/08-E11-stale-headers.patch
patch -p0 --no-backup-if-mismatch -i work/port/docdebt/09-E11-sorry-wording-in-headers.patch      # optional
patch -p0 --no-backup-if-mismatch -i work/port/docdebt/10-E19-plan-final-axiom-expectation.patch
patch -p0 --no-backup-if-mismatch -i work/port/docdebt/registry-sub-entry.patch
```
`--no-backup-if-mismatch` keeps `patch` from leaving `.orig` files in `work/lean` (the checker's `audited_declarations`
walks the tree; stray files would show up in receipts). If a hunk is rejected (`.rej`), do NOT edit the live
file by hand — the file changed since 2026-09-19; regenerate the patch from the current text.

Post-apply mechanical checks (no Lean):
```
grep -rn "3264-3313\|3313-331[56]\|992-1147" work/lean --include=*.lean | wc -l        # expect 0
grep -rli "sorry" work/lean --include=*.lean | wc -l                                  # expect 0 after 09 (55 before)
grep -c "^### lit:homfly (descent sentence)" blueprint/AXIOM_REGISTRY.md              # expect 1
python3 work/port/docdebt/check_comment_only.py --pair <pre-apply copy of work/lean> work/lean   # if a copy was kept
```

## 3. Rebuild footprint (what the executor must expect from the next checker run)

**The checker MUST be re-run after applying** (D-AUTH-20260919 G-05 makes it a condition): `python3 tools/check_lean.py
work/lean --all` and `--stage 1`, then `python3 verify_bundle.py`; receipts re-bind `project_sha256`. One build or checker
at a time (`pgrep -f '^python3 tools/check_lea[n]'` first; `work/RESUME_FOR_NEXT_AGENT.md`). Docstrings are stored in the
`.olean`, so lake rebuilds every changed module AND its transitive dependents: patches **07, 08, 09** touch the root of the
library (`SM/LinkLaurentRing.lean`, `SM/LinkMoves.lean`, `SM/LinkInterfaces.lean`, `SM/LinkDiagram.lean`, … — 92 to 103 of the
697 modules import each transitively), so applying them means an essentially FULL rebuild of `work/lean`; patches **01-06**
alone touch mid-level and leaf modules (`SM/ContactPathOfDescent.lean` 27 dependents, `SM/FdContactStatements.lean` 23,
`SM/CornerChainUnits.lean` 7, `RProof/GenericSelected.lean` 0). If the next build cycle is a full one anyway (a new row
port), the difference is nil; otherwise apply 01-06 (+10, +registry) first and 07-09 with the next full build.

Every touched Lean module is inside the audited import closure (692 of 697 modules; `Supplemental` included); 32 of the 65
carry accepted rows (the checker re-verifies their statement hashes — comments are not part of a statement, so no
`statement_sha256` in `work/lean/lean-declarations.json` changes; if one did, STOP: a patch touched code). Per file
(rows = accepted rows mapped to the module in `lean-declarations.json`; last column = number of `work/lean` modules that
transitively import it):

| file | patches | rows mapped to it | in audited closure | modules that transitively import it |
|---|---|---|---|---|
| blueprint/AXIOM_REGISTRY.md | registry | (not Lean) | — | — |
| work/drafts/floor/PLAN_FINAL.md | 10 | (not Lean) | — | — |
| work/lean/Bridge/B1.lean | 09 | Bridge:B1, Bridge:B2 | yes | 15 |
| work/lean/Bridge/B3.lean | 09 | Bridge:B3 | yes | 14 |
| work/lean/Bridge/SmR.lean | 08 | — | yes | 6 |
| work/lean/CV/Axioms.lean | 07,09 | CV:ax:homfly, CV:ax:gausscode | yes | 41 |
| work/lean/CV/Carriers.lean | 09 | CV:def:smoothing, CV:def:wind, CV:def:pieces | yes | 40 |
| work/lean/CV/ChamberInv.lean | 09 | — | yes | 19 |
| work/lean/CV/Events.lean | 09 | CV:def:interlace, CV:def:event, CV:lem:guardconst, CV:def:silent | yes | 48 |
| work/lean/CV/FullTwist.lean | 09 | CV:lem:fulltwist | yes | 7 |
| work/lean/CV/RecordHomfly.lean | 09 | CV:def:record, CV:def:homfly | yes | 38 |
| work/lean/CV/Rotation.lean | 09 | — | yes | 41 |
| work/lean/CV/RotationSmooth.lean | 09 | CV:def:rot | yes | 11 |
| work/lean/CV/Setup.lean | 09 | CV:def:polygon, CV:def:regular, CV:def:guarded, CV:def:generic, CV:def:diagrammatic | yes | 55 |
| work/lean/CV/TurnLift.lean | 09 | CV:lem:turnlift | yes | 10 |
| work/lean/RProof/GenericSelected.lean | 05 | R:generic_selected | yes | 0 |
| work/lean/RProof/X1Rows3.lean | 08 | — | yes | 8 |
| work/lean/SM/ALawful.lean | 09 | cor:A-lawful | yes | 5 |
| work/lean/SM/Anchors.lean | 09 | prop:anchors-exist | yes | 8 |
| work/lean/SM/BowTie.lean | 09 | — | yes | 14 |
| work/lean/SM/CChamber.lean | 09 | prop:C-chamber | yes | 25 |
| work/lean/SM/CS5.lean | 09 | thm:C-S5 | yes | 0 |
| work/lean/SM/CSoft.lean | 04 | thm:C-soft | yes | 1 |
| work/lean/SM/CX1.lean | 09 | lem:C-X1 | yes | 35 |
| work/lean/SM/CarrierCornerPolygon.lean | 09 | — | yes | 71 |
| work/lean/SM/CarrierCrossings.lean | 09 | — | yes | 75 |
| work/lean/SM/CarrierNeighborSeparation.lean | 09 | — | yes | 75 |
| work/lean/SM/CarrierNoncrossing.lean | 09 | — | yes | 70 |
| work/lean/SM/CarrierSelfIntersections.lean | 09 | — | yes | 70 |
| work/lean/SM/CoefficientTransport.lean | 09 | lp:coefficient-transport | yes | 71 |
| work/lean/SM/ContactPathOfDescent.lean | 01,02,07 | — | yes | 27 |
| work/lean/SM/CornerChainStatements.lean | 04 | — | yes | 9 |
| work/lean/SM/CornerChainUnits.lean | 04,06 | — | yes | 7 |
| work/lean/SM/CornerStateSum.lean | 09 | def:C | yes | 45 |
| work/lean/SM/FdContactStatements.lean | 03 | — | yes | 23 |
| work/lean/SM/FlatCarriers.lean | 09 | def:flat-carriers, cor:flat-carriers | yes | 53 |
| work/lean/SM/FlatCarriersDefs.lean | 08 | — | yes | 58 |
| work/lean/SM/FrontInterfaces.lean | 09 | ng:finite-word | yes | 32 |
| work/lean/SM/FrontSmooth.lean | 09 | ng:front-domain | yes | 43 |
| work/lean/SM/HypR.lean | 09 | hyp:R | yes | 17 |
| work/lean/SM/LinkDiagram.lean | 09 | — | yes | 103 |
| work/lean/SM/LinkDiagramExtras.lean | 09 | — | yes | 72 |
| work/lean/SM/LinkDiagramRecord.lean | 09 | — | yes | 77 |
| work/lean/SM/LinkInterfaces.lean | 07,08,09 | lit:homfly, lp:lm, lp:lm-uniqueness | yes | 92 |
| work/lean/SM/LinkLaurentRing.lean | 08,09 | — | yes | 94 |
| work/lean/SM/LinkMoves.lean | 07,09 | — | yes | 94 |
| work/lean/SM/LinkPositiveLift.lean | 09 | — | yes | 54 |
| work/lean/SM/LinkRecord.lean | 09 | — | yes | 100 |
| work/lean/SM/LinkRecordExtension.lean | 09 | — | yes | 73 |
| work/lean/SM/LinkRecordExtras.lean | 09 | — | yes | 72 |
| work/lean/SM/LitHomflyDescent.lean | 02 | — | yes | 26 |
| work/lean/SM/LocalPolynomial.lean | 09 | — | yes | 79 |
| work/lean/SM/MyCyclicB.lean | 09 | — | yes | 9 |
| work/lean/SM/PolynomialBlock.lean | 09 | lp:core, lp:split-circle, rp:record-polynomial, lc:presentations | yes | 70 |
| work/lean/SM/RootIndependence.lean | 09 | thm:root-indep-proof | yes | 6 |
| work/lean/SM/SingleCrossing.lean | 09 | lc:single-crossing | yes | 71 |
| work/lean/SM/SmallValues.lean | 09 | — | yes | 8 |
| work/lean/SM/Smoothing.lean | 09 | — | yes | 71 |
| work/lean/SM/SoftRotation.lean | 09 | — | yes | 10 |
| work/lean/SM/StarPolygons.lean | 09 | — | yes | 9 |
| work/lean/SM/TransportAngleInterval.lean | 09 | — | yes | 11 |
| work/lean/SM/TransportLemma.lean | 09 | lem:transport | yes | 7 |
| work/lean/SM/TransportLengths.lean | 09 | — | yes | 11 |
| work/lean/SM/TurnLift.lean | 09 | cf:lem-turnlift | yes | 35 |
| work/lean/SM/TurningNumber.lean | 09 | cf:def-turning | yes | 48 |
| work/lean/SM/Uniqueness.lean | 09 | thm:uniqueness | yes | 4 |
| work/lean/SM/ZeroLink.lean | 09 | mp:zero-link | yes | 29 |

## 4. After the registry patch (G-07)

`blueprint/AXIOM_REGISTRY.md` is a manifested root file (`MANIFEST.sha256` line 129), so `python3 verify_bundle.py` FAILS
until its line is refreshed:
```
python3 work/port/refresh_manifest.py blueprint/AXIOM_REGISTRY.md
python3 verify_bundle.py            # expect PASS (191 files)
```
(`refresh_manifest.py` rewrites only the named file's line; the same tool refreshed `lean/axiom-policy.json` and
`FINAL_REVIEW.md` on 2026-09-15.) Then record the blueprint change as a dated AUTHOR_NOTES entry (the package rule: a new
dated entry, never an edit of an old one), citing D-AUTH-20260919 G-07 and this patch; `TARGETS.md:8` ("five listed
literature interfaces") stays as is — the sub-entry is under the lit:homfly heading, so the count of headings is still
five. FINAL_REVIEW §4.3 and §7 should mention the sub-entry when FR is next regenerated (OPEN_ITEMS §E-16 → done).

The `work/lean` modules are NOT in `MANIFEST.sha256` (only the `lean/` skeleton is), so patches 01-09 need no manifest
step; `work/delivery/refresh.sh` copies receipts and declaration maps, run it after the checker as usual.

## 5. Items of §E deliberately NOT patched (and why)

- **E-03** frozen reviewer-input file (`work/reviews/cp-finite-contact-path-reviewer-input-statement.lean.txt` 100-101): its
  sha256 is bound in the accepted review — must not be regenerated (the register says so). Record in FR §7.
- **E-04** `source_sha256` fields in two review JSONs: data fields, not comments; an executor bookkeeping decision.
- **E-05** beyond the two line refs: the axiom-count wording is in AUTHOR_NOTES (old entries are never edited) and in
  `cv-ax-slbound.json` `kernel_check` (review data); the receipt name `dev-check-fdcontact-row162-implemented.json` is a file
  name. Nothing in the module.
- **E-09, E-12 to E-15, E-17, E-18, E-21, E-22, E-24 to E-28**: reports, STATUS, FR, AUTHOR_NOTES, tools, review briefs,
  dependency data, README files — not module comments; each already has its "Decision" (executor / none) in the register.
  E-15 (review-brief locators) is a cheap executor edit of `work/port/review_prompt_*.md` but was kept out of a
  "module comments" batch so that the templates are fixed by whoever next uses them (note the caution about
  `review_prompt_cvtail-rows.md:36`, whose "§7" is correct).
- **E-20** staged 178/183 files (`<HH:MM>Z` placeholders, an import of a module that does not exist yet): to be filled at
  port time by the porter — a patch now would be overwritten.
- **E-23** prose `sorry` mentions in the DRAFTS `W3_Assembled.lean` / `W3C_Assembled.lean`: reworded at port time in the
  ported module (the drafts are live work under the re-opened rows 110/177 and change daily; a patch would go stale).
- **G-12** (`SM/SrcContact.lean:152`, the Etnyre §2.2 (3) attribution): comment-only but a CONTENT judgement reserved for
  the author ("confirm or soften"); D-AUTH-20260919 lists it as optional, so it is not in this batch.
- `SM/CornerChainUnits.lean:14` "row 110 is unmapped", `RProof/X1Rows.lean:105` "(`extreme_selected`, `cv_R`) are NOT
  declared", `SM/FrontInterfaces.lean:12`: still TRUE (rows 110, 177, 178 are open) — not stale, left alone.

## 6. Provenance

Scratch copies and the edit scripts (exact-once string replacements) lived in the agent's session scratchpad and are
not needed to apply anything: the patches are self-contained. Verification at preparation, 2026-09-19 ~06:00Z / 2:00am ET:
`check_comment_only.py --root . --patches …` → `RESULT: comment-only` for all eleven patches; every tex locator changed in
02/03/04 was re-read in `reference/SM/sm-3-statesum.tex` / `sm-4-knotlaws.tex`; the registry's quoted tex lines 920-921 are
byte-identical to the source; `diff -rq` of the live `work/lean`, `blueprint/AXIOM_REGISTRY.md` and
`work/drafts/floor/PLAN_FINAL.md` against the pre-work snapshot shows no change (nothing was applied).
