# FINAL_REVIEW addendum — DRAFT 2026-09-15 ~23:15Z (documentation agent of the pod executor)

Ready-to-paste replacement text for the sections of the root `FINAL_REVIEW.md` (763 lines, 2026-09-14 18:15Z) that
changed on 2026-09-15. Blocks (A)-(I) below map onto the existing sections as noted in each heading; the executor folds
them in after the three R waves report. Everything in «double angle brackets» is a placeholder the executor fills in at
the closing pass: «OUTCOME-174», «OUTCOME-176», «OUTCOME-177» (and the dependent «STATUS-178/183/184»), the final numbers
«CLAIMS», «CHECKLIST», «TARGETS», «PENDING-N», «FINAL-TIME», «RECEIPT», «AUDITED», «MAPPED», «STAGE-CHECK-RESULT», and every
«VERIFY» (a fact this draft could not confirm from the files; confirm or delete). Facts below were read from
`work/AUTHOR_NOTES.md` lines 5144-6328 (every 2026-09-15 entry), `work/STATUS.md`, `work/lean/lean-declarations.json`,
`work/lean/axiom-policy.json` (= `lean/axiom-policy.json`, byte-identical), the 15 review files of 2026-09-15, the 15
receipts `work/checks/dev-check-*.json` of 2026-09-15, `work/checks/declaration-audit.json` (21:09Z), the draft state
reports named in §3, `verify_bundle.py` (package root) and `tools/check_lean.py`. No Lean tool was run for this draft;
the numbers of the current state are those recorded at 22:40Z, not a fresh measurement.

---------------------------------------------------------------------------------------------------------------------

## (A) New header block — replaces "# Completed fidelity review — 2026-09-14 (pod executor)" and its two paragraphs

# Completed fidelity review — 2026-09-16 (pod executor)

**Final fidelity review — completed «FINAL-TIME» UTC / «FINAL-TIME-ET» ET (pod executor).** This is the 2026-09-14 review
(kept below unchanged as the state of record at 18:15Z that day) updated at the closing pass after the executor worked
through the GAP-2 chain on 2026-09-15 under the author's decision D-GAP2 (`work/AUTHOR_NOTES.md`, 13:39Z). Paths are
relative to the package root; `reviews/<row>.json` means `work/reviews/<row>.json`. The focused stage is «INCOMPLETE /
COMPLETE» (§4.9).

**Status: final; the focused stage is «INCOMPLETE».** The 2026-09-15 addendum was drafted by the executor's documentation
agent at ~23:15Z while three bounded waves were still running (rows 174, 176, 177; AUTHOR_NOTES 22:34Z, 22:37Z, 22:00Z)
and finalized at «FINAL-TIME» after «their outcomes: see §3.4». It follows the checklist of FINAL_REVIEW.md item by item.
The machine-derived tables (§1, §2, §3, §4.4) were regenerated at «TABLE-TIME» from `python3 tools/claims.py --json`,
the map and `work/checks/declaration-audit.json` («VERIFY: `work/delivery/tools/gen_final_review_tables.py` needs the
abbreviation table extended by `HD` and `SC` before it is re-run, §7»). This is a fidelity review of implemented Lean
declarations against the frozen SM15 source; it is not an author approval and it does not claim the mathematics finished
(§5). Final state: **claims verified «CLAIMS»/132 («CLAIMS-PCT»%); checklist «CHECKLIST»/192 accepted, 0
implemented-awaiting-review, «PENDING-N» pending; final targets «TARGETS»/8; `python3 tools/check_lean.py work/lean --all`
«STAGE-CHECK-RESULT» (§4.9).** State at the time of this draft (22:40Z, STATUS.md header; AUTHOR_NOTES 20:50Z, 22:40Z):
claims verified 122/132 (92.4%), checklist 182/192 (94.8%), 10 pending (57, 110, 127, 128, 174, 176, 177, 178, 183, 184),
targets 5/8 (`prop:C-chamber`, `prop:C-silent`, `thm:C-S3`, `thm:C-S5`, `thm:C-soft` of EXECUTION.json's eight; open:
`thm:C-S7`, `Bridge:theorem`, `SM:corner_laws_and_soft`); current receipt `work/checks/stage-development.json` =
`dev-check-cs7sliding-library.json` (21:09Z; byte-identical): passed=true, 182 mapped, 39 005 audited.

The fourteen rows accepted on 2026-09-15, in order (AUTHOR_NOTES entry times): `cp:finite-contact-path` (91, 14:25Z),
`src:contact` (m97) and `CV:ax:etnyre` (161) (16:51Z), `fd:contact` (94) and `CV:ax:slbound` (162) (17:12Z),
`cf:thm-carrierfloor` (99) and `thm:floor` (100) (17:50Z), `CV:thm:carrierfloor` (155), `CV:singleton_D_i` (165),
`R:extreme_pair_zero` (175) (18:39Z), `cb:singleton` (103), `lem:corner-values` (105), `thm:C-soft` (112) (20:25Z),
`prop:anchor-values` (122) (20:50Z). One new literature declaration: `axiom SM.lit_homfly_descent :
SM.AmbientIsotopyDescent` (13:49Z; interface-reviewed 14:25Z; §4.3). One package-tool edit: `verify_bundle.py` line 100
(D-GAP2-2b; §4.3). Nothing accepted before 2026-09-15 was changed: all 168 earlier rows keep their `statement_sha256`
(«VERIFY at the closing checker run: every accepted row's hash equals `statement_hashes` of the final audit»).

---------------------------------------------------------------------------------------------------------------------

## (B) §0 "Sources of truth used" — delta (append after the existing bullets)

- **2026-09-15 additions.** Decisions and disclosed readings: `work/AUTHOR_NOTES.md` from "## D-GAP2 — the author's
  decision on GAP-2 (additive form) received" (13:39Z) to "## Closing pass begun" (22:41Z): labels D-GAP2-1..4, D-GAP2-2b,
  D-SC-1..6, D-FL-1..4, D-CC-1..5, D-CVT-1..6, D-CM-1..5, D-RM-1..6; fidelity-risk lists FR-LHD-1..4, FR-FL-*, FR-SC-1..11,
  FR-FC-1..7, FR-CC-1..15, FR-CV-155-1..9, FR-CV-165-1..4, FR-R-174..178, FR-B-183, FR-F-184-1..4, FR-CM-1..17 (+ FR-CM-3′,
  FR-CM-9′); reassessment audits A-110-1 (20:46Z; concluded 22:40Z) and A-177-1 (21:21Z; succeeded 22:00Z); the
  reassessment note of 17:24Z (D-RM-1). Lane plans: `work/drafts/{floor,contact,corner,cvtail,comparison,moves}/PLAN_FINAL.md`
  with `Statements_FINAL.lean` each. Draft state of the open rows: `work/drafts/corner/port/CS7_STATE.md`,
  `work/drafts/corner/W3_ASSEMBLY_REPORT.md` (§6 honest state, §7 order of attack), `work/drafts/moves/W3_A1_ASSEMBLY_REPORT.md`
  (§0, §6), `work/drafts/moves/R174_ASSEMBLY_REPORT.md` (§3, §5, §8), `work/drafts/moves/R176_ASSEMBLY_REPORT.md` (§0, §3,
  §5), «the wave-2 / Wave-3b reports written after 2026-09-16 00:30Z».
- **Kernel evidence 2026-09-15:** 15 development receipts, all passed (mapped / audited): `dev-check-row91-implemented`
  (13:57Z; 169 / 36 184), `-row91-accepted` (14:29Z), `-srccontact-row161-implemented` (15:10Z; 171 / 36 331),
  `-fdcontact-row162-implemented` (16:43Z; 173 / 36 542), `-srccontact-row161-accepted` (16:53Z), `-fdcontact-row162-accepted`
  (17:14Z), `-floor-rows-implemented` (17:19Z; 175 / 37 093), `-floor-rows-accepted` (17:52Z), `-cvtail-rows-implemented`
  (18:11Z; 178 / 37 588), `-cvtail-rows-accepted` (18:41Z), `-corner-rows-implemented` (20:03Z; 181 / 38 949),
  `-corner-rows-accepted` (20:27Z), `-row122-implemented` (20:30Z; 182 / 39 005), `-row122-accepted` (20:52Z),
  `-cs7sliding-library` (21:09Z; 182 / 39 005; = the current `stage-development.json`). Per-declaration axioms:
  `work/checks/declaration-audit.json` (21:09Z, 977 MB; rows only for the 182 mapped declarations, §7). Logs
  `work/checks/checker-run-2028.log`, `-2049.log`, `-2106.log`, `port-*-chain.log`. `work/checks/stage-1.json` is still the
  2026-09-14 18:06Z record (`passed: false`) until the closing `--all` run («RECEIPT»).
- **Reviews 2026-09-15:** `work/reviews/{cp-finite-contact-path-row, src-contact, cv-ax-etnyre, fd-contact, cv-ax-slbound,
  cf-thm-carrierfloor, thm-floor, cv-thm-carrierfloor, cv-singleton-d-i, r-extreme-pair-zero, cb-singleton,
  lem-corner-values, thm-C-soft, prop-anchor-values}.json` (row reviews) and `lit-homfly-descent.json` (interface review of the
  new axiom; not a checklist row); raw workflow output `<slug>-review-workflow-raw.json`; reviewer inputs
  `<slug>-reviewer-input-statement.lean.txt` plus the shared statement files `carrier-floor-statements-reviewer-input.lean.txt`,
  `corner-chain-statements-reviewer-input.lean.txt`, `corner-rows-reviewer-input-statement.lean.txt`,
  `anchor-values-statements-reviewer-input.lean.txt`, `fd-contact-statements-reviewer-input.lean.txt`.
- **Policy 2026-09-15:** `work/lean/axiom-policy.json` = `lean/axiom-policy.json` (identical): `literature` now has six
  keys — the five registry ids plus `"lit:homfly (descent sentence)": "SM.lit_homfly_descent"` (D-GAP2-2); `verify_bundle.py`
  line 100 compares the label part of each literature key with the five registry ids (D-GAP2-2b); root `MANIFEST.sha256`
  lines for `lean/axiom-policy.json`, `verify_bundle.py` and `FINAL_REVIEW.md` refreshed by `work/port/refresh_manifest.py`
  (AUTHOR_NOTES 13:39Z item 4, 13:52Z; `python3 verify_bundle.py` reported PASS at 13:50Z and after the edit — «VERIFY at
  the closing pass after FINAL_REVIEW.md changes again»).
- **Library (not mapped) added 2026-09-15:** `SM/LitHomflyDescent.lean` (39 lines, the axiom), `SM/SrcContact.lean` (287; the
  fifth interface + `SM.sl`), `SM/FdContactStatements.lean`, `SM/FdContactUnits.lean` (1 444), `SM/CarrierFloor.lean` (3 822),
  `SM/CarrierFloorRows.lean`, `SM/CornerChainStatements.lean` (330), `SM/CornerChainUnits.lean` (11 842), `SM/CBSingleton.lean`,
  `SM/CornerValues.lean`, `SM/CSoft.lean`, `SM/CornerPolygon.lean`, `SM/AnchorValues.lean`, `SM/AnchorValuesRow.lean`,
  `SM/CuspDeletionGeneric.lean`, `SM/Comparison.lean`, `SM/CInherits.lean` (204), `SM/BigonDeletion.lean` (5 374),
  `SM/CS7Sliding.lean` (2 956), `CV/AxEtnyre.lean`, `CV/AxSlbound.lean`, `CV/CarrierFloor.lean`, `CV/SingletonDi.lean`,
  `RProof/RALedgers.lean` (2 371), `RProof/ExtremePairZero.lean`. `work/lean` now holds 693 `.lean` files (648 SM, 32 CV, 7
  RProof, 4 Bridge, `Supplemental.lean`, `Supplemental/Audit.lean`), ≈ 279.5k lines (`find | wc -l`, 22:5xZ; 665 / ≈ 248k on
  2026-09-14).

---------------------------------------------------------------------------------------------------------------------

## (C) §1 Summary table — replaces the SUMMARY block and the "Final state" paragraph

## 1. Summary of the 132 claims / 192 checklist rows by status  (table regenerated «TABLE-TIME»)

<!-- BEGIN:SUMMARY -->
| unit class | total | accepted | implemented (awaiting review) | pending |
|---|---|---|---|---|
| source claims (tools/claims.py: "claims verified") | 132 | «CLAIMS» (122 at 22:40Z) | 0 | «132−CLAIMS» (10) |
| definitions / conventions (units of work, not claims) | 52 | 52 | 0 | 0 |
| literature interfaces + hypotheses + extra lemma (map rows outside claims.py) | 8 | 8 | 0 | 0 |
| checklist rows total (work/lean/lean-declarations.json) | 192 | «CHECKLIST» (182) | 0 | «192−CHECKLIST» (10) |
| final targets (EXECUTION.json) | 8 | «TARGETS» (5) | 0 | «8−TARGETS» (3) |

Generated «TABLE-TIME» UTC from `python3 tools/claims.py --json` (claims verified «CLAIMS»/132), the map and
`work/checks/declaration-audit.json`. Current checker receipt work/checks/stage-development.json: passed=«True»,
stage=«None / 1», stage_accepted=«False / True», mapped_declarations=«MAPPED», audited_declarations=«AUDITED».
<!-- END:SUMMARY -->

Final state (`python3 tools/progress.py --once` at «FINAL-TIME»: "claims verified «CLAIMS»/132 …"; `work/PROGRESS.md`):
claims verified «CLAIMS»/132, checklist «CHECKLIST»/192, targets «TARGETS»/8, 0 rows implemented-awaiting-review,
«PENDING-N» pending. At 22:40Z on 2026-09-15 (STATUS.md header): 122/132, 182/192, 5/8, 10 pending — the eight map rows
outside claims.py are all accepted (the last, `src:contact`, at 16:51Z), the 52 definition rows were complete on
2026-09-14, and the ten pending rows are all claim rows: 57 (deferred), 110, 127, 128, 174, 176, 177, 178, 183, 184
(§3). The GAP-2 ceiling of 109/132 recorded on 2026-09-14 is gone: the author's decision D-GAP2 (13:39Z) admitted the
descent sentence as a second declaration of lit:homfly, row 91 closed at 14:25Z, and the chain 91 → src:contact → 94 →
99 → 100 → 103/105/112 → 122 and 155 → 165 → 175 was accepted the same day. All «CHECKLIST» accepted rows have
`statement_sha256` equal to `statement_hashes` of the final audit and a review file with `verdict: "faithful"` («VERIFY
at the closing run»; the checker enforces the same).

---------------------------------------------------------------------------------------------------------------------

## (D) §2 additions — the 14 rows accepted on 2026-09-15 (append to the ACCEPTED table; update the legend)

Legend change for §2: axioms from `declaration-audit.json` with `std` = propext, Classical.choice, Quot.sound;
`H` = `SM.lit_homfly`; **`HD` = `SM.lit_homfly_descent` (new; the second declaration of lit:homfly, §4.3)**; `LM` = `SM.lp_lm`;
`LMU` = `SM.lp_lm_uniqueness`; `NG` = `SM.ng_finite_word`; **`SC` = `SM.src_contact` (new; the fifth interface, declared
2026-09-15)**. `9` abbreviates the full set `std+H+HD+LM+LMU+NG+SC` (nine constants), the footprint of every row downstream of
`fd:contact`. Over the 182 accepted rows (recounted from `declaration-audit.json` 21:09Z): `std` only 114 rows; `std+LM` 21;
`std+H+LM+LMU` 17; `std+H` 11; `9` 11; `std+SC` 2 (`src:contact`, `CV:ax:etnyre`); `std+LM+NG` 2 (rows 83, 93); `std+LM+LMU` 2;
`std+NG` 1 (`ng:finite-word`); `std+H+HD+LM+LMU` 1 (row 91). Per constant: `H` in 40 rows (28 on 2026-09-14), `HD` 12, `LM`
54 (42), `LMU` 31 (19), `NG` 14 (3), `SC` 13. No `sorryAx`, no `Lean.ofReduceBool`, no other constant in any mapped
declaration. All 14 new verdicts are `faithful`, each from one workflow of three lens reviewers ("literal", "definitions",
"strength") + two adversarial refuters ("not refuted"), proof withheld (§6). "[N notes]" = the number of entries in the
review's `discrepancies` + `stronger_than_source` + `weaker_than_source` arrays; every entry is marked non-blocking by its
reviewer.

| # | row | Lean declaration | module | review file | verdict | axioms | disclosed readings (one clause) |
|---|---|---|---|---|---|---|---|
| 91 | `cp:finite-contact-path` | `SM.cp_finite_contact_path` | SM.ContactPath | reviews/cp-finite-contact-path-row.json | faithful | std+H+HD+LM+LMU | labels D-GAP2-3, FR-CP-1/5/7/9, FR-LHD-1, K-5; `:= cp_finite_contact_path_of_descent lit_homfly_descent` (statement = the `ContactPathData` reviewed 2026-09-14, unchanged); WEAKER: the supplied family is an ℝ-indexed `SpatialFamily` (printed [0,1]; FR-CP-5) and both end diagrams enter through polygonal `HeightMarking` readings with no existence of a reading asserted (FR-CP-1); STRONGER (proof side): the axiom consumed bundles the isotopy-extension step the printed proof performs by hand (FR-LHD-1); citation nit: the consumed descent sentence is at sm-3:3310-3312 and the hand isotopy-extension at 3276-3312 where docstrings say 3313-3316 / 3264-3313 [14 notes] |
| m97 | `src:contact` | `SM.src_contact` | SM.SrcContact | reviews/src-contact.json | faithful | std+SC | labels D-SC-1..6, FR-SC-1..11; `axiom src_contact : ∃ r tb : (ℝ → E3) → ℝ, SrcContactClauses r tb` — ∃-form over the literature's r, tb (never defined by the document) with exactly the four printed formulas as fields (FR-SC-1; equivalence with the substituted consequence proved, `src_contact_iff_consequence`, standard axioms); WEAKER: the Legendrian formulas hold for KNOTS (`F.c = 1`) whose front is on ng:front-domain's class (FR-SC-2); `T₊(L)` = every positive circle of every `IsPushoffAnnulus` (FR-SC-3); r, tb, sl ℝ-valued (FR-SC-10); integrality of sl not asserted (a consequence) [9 notes] |
| 161 | `CV:ax:etnyre` | `CV.ax_etnyre` | CV.AxEtnyre | reviews/cv-ax-etnyre.json | faithful | std+SC | labels D-SC-4, FR-FC-4; a THEOREM from `SM.src_contact` alone (the CV `ax:*` rows are theorems, the `CV.ax_homfly` pattern; D-F10 option (iii) superseded); the CV text's undefined `sl` is read as the document's `SM.sl` (row 88's self-linking made ε-free); the redundant printed hypothesis "no downward vertical tangency" is kept; `TransverseKnot` fixes the class (C^∞, 1-periodic, `z′ − y x′ > 0`, generic xz projection) [2 notes] |
| 94 | `fd:contact` | `SM.fd_contact` | SM.FdContactUnits | reviews/fd-contact.json | faithful | 9 | labels D-SC-3, FR-FC-1..3, FR-SC-4/9/10; `:= fd_contact_of_units …` (eleven unit theorems, each standard axioms only); sentence 1 (the over/sign rule) rendered on def:transverse-front's class where it is definitional (FR-FC-3); STRONGER: `representative_bound` for EVERY polygonal reading X of D_T; WEAKER: conditional on `Nonempty (HeightMarking …)`, no existence of a reading asserted (FR-FC-1, the FR-1 convention; row 91 reads its endpoint identically); `degAZ 0 = 0` and `slCircle` off-class default never exercised; `sl` ℝ-valued, casts [10 notes] |
| 162 | `CV:ax:slbound` | `CV.ax_slbound` | CV.AxSlbound | reviews/cv-ax-slbound.json | faithful | 9 | labels D-SC-4, FR-FC-5/6; a THEOREM `:= ax_slbound_of SM.fd_contact` (P = homfly by lp:core); WEAKER (recorded narrowing FR-FC-5): "a transverse knot in the standard contact ℝ³" is `SM.TransverseKnot` (generic xz projection, C^∞, positively transverse, 1-periodic) — fd:contact's own domain and the sole consumer's instance (thm:carrierfloor (C)); P_T = `homfly X` for every reading X (FR-FC-6); in the never-realised case `homfly X = 0` the clause would read sl ≤ −1 [9 notes] |
| 99 | `cf:thm-carrierfloor` | `SM.cf_thm_carrierfloor` | SM.CarrierFloorRows | reviews/cf-thm-carrierfloor.json | faithful | 9 | labels D-FL-1..4, FR-FL-R1..R3, A1..A2, B1..B5, C1..C9; `:= cf_thm_carrierfloor_of_bound transverseFrontBound` (row 94 enters as the sl-free composite `TransverseFrontBound`, FR-FL-C9); (B) is stated for the NORMALISED orientation (`C` or `C.reverse` with `D.reverse`) — a refuter confirmed the literal claim is false for an all-negative L, the printed proof's WLOG is the only true reading (FR-FL-B1); STRONGER: `junction_determined` fixes the parametrisation (FR-FL-A1), the (R) fields hold for every link diagram / every C¹ regular curve, `BClaim` adds `ε₁ ≤ clearance C`, (C) `floor` unconditional on `P X` (`P_ne_zero`); the printed mirror D̄ is the crossing switch (`Diagram.switchAll`), not `Diagram.mirror` (FR-FL-C4) [15 notes] |
| 100 | `thm:floor` | `SM.thm_floor` | SM.CarrierFloorRows | reviews/thm-floor.json | faithful | 9 | labels FR-FL-F1..F3; `:= thm_floor_of_bound transverseFrontBound`; "exactly one turn is right" rendered as "one right AND every other left" (`AllLeftOrOneRight`, the literal reversal form; equivalent because carrier turns are nonzero, lem:carriers (ii)); STRONGER: `a_floor` stated twice — in ℤ with def:C's `cornerSlot` and in ℝ with the real `carrierRotation`; `z_parity` (`InSupportM 1`, `0 ≤ mindegZZ`) with no turn hypothesis (FR-FL-F3); `mindegAZ 0 = 0` convention [7 notes] |
| 155 | `CV:thm:carrierfloor` | `CV.carrierfloor` | CV.CarrierFloor | reviews/cv-thm-carrierfloor.json | faithful | 9 | labels D-CVT-1, FR-CV-155-1..9; `:= carrierfloor_of_sm SM.cf_thm_carrierfloor` — (R)(A)(B)(C) on CV's printed binders (`LabelledTuple`, `Diagrammatic`, `Regular`, `OverUnder`, `CV.rot`/`rotAbs`) PROVED from the SM row-99 bundles through the accepted polygon bridge F6, (D) proved on CV:def:X1 objects; (B) normalised orientation with the reversal branch on SM objects and R = `|rotationNumber (reversal L)|` (equal to `rotAbs` by `rot_eq_rotationNumber`, `rot_reversal`; FR-CV-155-5); (A)'s domain is `Diagrammatic` (no triple points), which lem:rounding's printed list omits; (D)'s "so that P = 1 and w = 0" is commentary, not a conjunct (FR-CV-155-7) [13 notes] |
| 165 | `CV:singleton_D_i` | `CV.singleton_D_i` | CV.SingletonDi | reviews/cv-singleton-d-i.json | faithful | 9 | labels D-CVT-3, FR-CV-165-1..4; `:= singleton_D_i_of cvt_singleton_split (carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC)`; clause (D)(i) of thm:s7universal alone (no eligibility / ε = 0 binders, which the (D) preamble attaches to (ii)-(v)); `degree_gap` in support form `slot + 2 ≤ d` (FR-CV-165-1); STRONGER (N1): quantified over every CV-generic polygon on n ≥ 3, not only the event's polygons; row 103 is the template only — nothing of it is consumable on `CV.Generic` (FR-CV-165-3) [1 note] |
| 175 | `R:extreme_pair_zero` | `RProof.extreme_pair_zero` | RProof.ExtremePairZero | reviews/r-extreme-pair-zero.json | faithful | 9 | labels FR-R-174..177, NOTES_FINAL §7/§12; the FIXED bundle statement of the R statement panel (2026-09-14 ~06:35Z), byte-identical to the accepted siblings 168/170/172/173, `:= extreme_pair_zero_of_singleton CV.singleton_D_i …`; STRONGER: every field over ALL punctured parameters (`Punctured E δ t`), not only "the two nearby generic chamber-side representatives"; the K3 ↔ empty pairing is a hypothesis of no field; `third_singleton_piece` (a sentence of the printed Proof) and `pair_absent_on_complete` (a presupposition) asserted as clauses; "for arbitrary outside support" read under `FullAvail`; disclosed: one refuter saw the one-line proof term (module line 85; the same term stands in the statement file's header) [9 notes] |
| 103 | `cb:singleton` | `SM.cb_singleton` | SM.CBSingleton | reviews/cb-singleton.json | faithful | 9 | labels D-CC-1..5, FR-CC-1..3; `:= cb_singleton_of_floor thm_floor`; one field `isolated_zero`: "interlaces no other self-crossing" is `Interlaces` of G_P (def:interlace, the graph the printed proof uses), not the record interlacement of D_A (FR-CC-1); proof route bounds `mindegAZ` of the full product instead of the printed `[z⁰]` rows (FR-CC-3); all three reviewer arrays empty [0 notes] |
| 105 | `lem:corner-values` | `SM.corner_values` | SM.CornerValues | reviews/lem-corner-values.json | faithful | 9 | labels FR-CC-4..6; `:= corner_values_of_floor thm_floor`; (i) the hypothesis "embedded (m_Q = 0)" is rendered by the printed gloss `carrierCrossingCount = 0` only — at most a weaker hypothesis, so the statement is at least as strong (FR-CC-4); `|r_Q| = 1` for the REAL `carrierRotation`, the integer form as the proved companion `embedded_rotationInt` (FR-CC-5); `d_Q = 0` in ℤ through `cornerSlot`; (ii) literally row 103's clause at (Q, y) with the redundant guard `y' ≠ y`; "uniform" kept literally though the proof does not use it [6 notes] |
| 112 | `thm:C-soft` | `SM.thm_C_soft` | SM.CSoft | reviews/thm-C-soft.json | faithful | 9 | labels FR-CC-11..13; the fixed target name, `:= thm_C_soft_of_floor thm_floor` — the fifth target theorem; the genericity of P_ε is QUANTIFIED (`∀ hQ : Generic (softInsertion P j q ε)`, the consumer's `UniquenessHypotheses.soft` shape) rather than asserted, the accepted thm:A-soft's `∃ hQ` form being the proved companion `CSoftData.exists_generic` (FR-CC-12; the one "weaker" entry); the identity read in ℚ with `softAmplitudeMultiplier = (χ₋+χ₊)/2`, ℤ companion `doubled` (FR-CC-11); C on labelled tuples, the quotient descent is the consumer's business (FR-CC-13) [7 notes] |
| 122 | `prop:anchor-values` | `SM.prop_anchor_values` | SM.AnchorValuesRow | reviews/prop-anchor-values.json | faithful | 9 | labels D-CM-1, FR-CM-1..5, FR-CM-3′; `:= anchor_values_of thm_C_soft`; F restricted to ℤ-valued functions `∀ n [NeZero n], GenericPolygon n → ℤ` (FR-CM-1, thm:uniqueness's reading; the one "weaker" entry); STRONGER: the anchor clauses quantify over every `ZeroAnchor`/`LoopAnchor`/`LoopAnchorZero` WITHOUT def:anchors' case conditions — a kernel-proved superset (FR-CM-3′); `loopZero_turn` asserts BOTH readings of "orientation sign of the parent triangle" (common turn sign and rotation number, FR-CM-3); `A_loop`/`A_loopZero` assert `∃!` parent root; `rotationNumber` is ℝ-valued so the (L₀) clause is an equation in ℝ after casting; `cornerPolygon = 0` below arity 3, unreachable (FR-CM-5) [8 notes] |

Identities in the map for these 14 rows: author `executor-pod-claude-fable-5-1-20260913`; reviewer string
`reviewer-pod-claude-fable-5-1-20260913 (independent Claude Code workflow subagents …)` — the identity string carries the
date of its first use, while each review's `ai_review_disclosure` says the five subagents were spawned on 2026-09-15 (§7).
Review workflows (AUTHOR_NOTES): wf_2975467c-92c (91 + the axiom), wf_728083df-580 (src:contact, 161), wf_abec340f-6fd (94,
162), wf_eb7abb51-523 (99, 100), wf_dfc10382-689 (155, 165, 175), wf_2a10c8d9-b97 (103, 105, 112), wf_958e4651-ab4 (122).

---------------------------------------------------------------------------------------------------------------------

## (E) §3 Pending rows — replaces the PENDING block, the "by reason" list and §3.1-§3.5

## 3. Pending rows — one line each with the reason  (table regenerated «TABLE-TIME»; «PENDING-N» rows)

<!-- BEGIN:PENDING -->
| # | row | policy / fixed name | status | reason at completion |
|---|---|---|---|---|
| 57 | `lem:gauss-two-discs` | — | pending | DEFERRED by the author (D-GAP2 item 5, "Row 57 stays deferred", 2026-09-15 13:39Z); state unchanged since the 2026-09-14 review §3.2: judged INFEASIBLE now (PL Schoenflies on S², 12-20k lines, `work/drafts/pldiscs/PLDISCS_FEASIBILITY.md` §2.4); its only non-GAP-2 consumer 104 proved without it (D-ER1); its other consumer 105 (i) was proved unconditionally (corner lane, `corner_values_i`) |
| 110 | `thm:C-S7` | `SM.thm_C_S7` | pending | KERNEL-PROVED MODULO FIVE NAMED LEAVES; corner construction STOPPED by audit A-110-1 (concluded 22:40Z, §3.1, §6): `thm_C_S7 := thm_C_S7_of_floor thm_floor` typechecks in `work/drafts/corner/W3_Assembled.lean` (8 958 lines, sha256 109050d9…, 0 errors) with `sorryAx` through the two branch leaves — sliding `s7_sliding_law_at` ⇐ S1 `w3_SlidingRet` + S3 `w3_SlidingCarriers` (≈ 1 800-2 750 lines; S2 `w3_SlidingOrder` proved), bigon `s7_bigon_law_at` ⇐ B1 `w3_BigonFSector` (2 300-3 600) + B2 `w3_BigonReturnedRows` (3 500-5 400) + B3 `w3_BigonOneNewborn` (400-700) (≈ 6 200-9 700); axioms of the draft `thm_C_S7`: the nine registered + `sorryAx`, nothing unregistered; the fixed name is NOT declared in `work/lean` (D-F11); library ported: `SM/CornerChainUnits.lean`, `SM/CS7Sliding.lean`, `SM/BigonDeletion.lean` |
| 127 | `thm:comparison` | `SM.thm_comparison` | pending | one-liner blocked on 110 only: `thm_comparison hR := thm_comparison_of hR thm_C_S7 thm_C_soft` (port report of the comparison lane, 20:27Z); `SM.thm_comparison_of` PROVED and ported (`SM/Comparison.lean`; std+H+LM+LMU), hyp:R as the explicit parameter (D-CM-2, policy mode `explicit_parameter`); not declared |
| 128 | `cor:C-inherits` | `SM.cor_C_inherits` | pending | one-liner blocked on 110 only: `cor_C_inherits hR := cor_C_inherits_of hR thm_C_S7 thm_C_soft`; `SM.cor_C_inherits_of` and the one lemma leaf `cusp_deletion_generic` (standard axioms; the (G1) deletion at a simple cusp wall is generic, sm-6:335-359) PROVED and ported (`SM/CInherits.lean`, `SM/CuspDeletionGeneric.lean`; D-CM-3/4, FR-CM-8/9/9′); not declared |
| 174 | `R:generic_selected` | `RProof.generic_selected` | «STATUS-174» | «OUTCOME-174». State before wave 2 (R174_ASSEMBLY_REPORT §3, §5; AUTHOR_NOTES 22:37Z): every `gsc_Ledger` field realised (site `s174_site`, `hrec` = `r174h_hrec_tau`, site inputs `r174x_hx'/hw'`, WALL items 2-3, CARRIERS item 1, SMOOTH items 5-6); composition `r174_generic_selected_of_arc_rec` PROVED in the FIXED signature, `sorryAx`-free on the library base (`R174_Port_GenericSelectedUnits_draft.lean`, 6 847 lines, 0 sorry); ONE open Prop `r174_arc_rec_moves` (the two arcs of x′ on the carrier diagram of τ qAB carry the records of qA and qB; 0.6-1.5k lines); wave 2 = wf_94fd5719-317 (ARCV / ARCR, two independent routes, + an assembler that declares `RProof.generic_selected` if closed; units 00:45Z, assembler 01:15Z 2026-09-16); `RProof/RALedgers.lean` untouched |
| 176 | `R:extreme_transport` | `RProof.extreme_transport` | «STATUS-176» | «OUTCOME-176». State before wave 2 (R176_ASSEMBLY_REPORT §0, §3, §5; AUTHOR_NOTES 22:34Z): site `s176_site_of_event`, `hrec` (HSUCC), LEDGER (12)-(14) under `wind ≠ 0`, the `wind(S) = 0` split (`r176_est_row_H_weak_uniform`, 13 lines) and the composition `r176_extreme_transport_of_curl_outer_mixed : … → RowShape @ExtremeTransportData` PROVED, registered axioms only on the port-time copy (`R176_Port_draft.lean`, 6 339 lines, 0 sorry); THREE open Props `r176s_curl_removal` (record-level R-I of the kink, 0.6-0.9k; shared with 174/110), `r176_outer_carriers_L` (1.5-2.5k), `r176_mixed_bridge` (0.4-0.7k); wave 2 = wf_b437050b-aad (CURL / OUTER / MIXED + assembler; units 00:45Z, assembler 01:15Z); library-interface findings D-RM-5, D-RM-6 (§5) |
| 177 | `R:extreme_selected` | `RProof.extreme_selected` | «STATUS-177» | «OUTCOME-177». Audit A-177-1's decisive test SUCCEEDED 21:56Z (bound 00:30Z): the trans-free copy `G11_ConfigSw`/`G11_ParamsSw` (`work/drafts/moves/W3_A1_Assembled.lean`, 7 827 lines, 1 096 declarations) re-derives 905 of the accepted namespace's 908 configuration-dependent declarations; `G11_core_sw` and `esc_switch_riii_of_chain` are `sorryAx`-FREE on std+H+LM+LMU — row 177 (4), the switched RIII core, is closed; the `esc_` ledger was proved 17:47Z (`RProof/RALedgers.lean`); open before Wave 3b (W3_A1_ASSEMBLY_REPORT §6): unit E (3 sub-leaves feeding `w3e_strong_case_sw`, 0.7-0.9k), unit G (the two j = 2 bigon sites on `smoothDiagram` outputs, 2.0-2.4k), unit H (record side, 1.9k), the (4)/(6) realisers of `esc_MoveData.switch_riii` / `rii_after_smoothing` (0.7-1.3k; the D4/D5 orientation data "not yet derived — the riskiest open point"), the `esc_interface` replay (F-177-2, by extension not by editing RALedgers — A-177-1 D2); Wave 3b = wf_60663334-7b6 (E / G / H / REAL + assembler; units 00:30Z, assembler 01:00Z 2026-09-16); STATUS 22:40Z: unit E closed, `w3e_strong_case_sw` sorry-free |
| 178 | `R:cv_theorem` | `RProof.cv_R` | «STATUS-178» | assembly PROVED as library: `RProof.cv_R_of_rows (h174 : RowShape @GenericSelectedData) (h175 …) (h176 …) (h177 …) : CV.hyp_R := hyp_R_of_near_of_chamberinv (A2_cvRNear_of_rows rowShape_170 rowShape_172 rowShape_173 h174 h175 h176 h177) cvt_chamberInvII` (`RProof/RALedgers.lean:2354`; D-CVT-5, FR-R-178-1); with 175 accepted, `RProof.cv_R := cv_R_of_rows generic_selected extreme_pair_zero extreme_transport extreme_selected` the moment 174, 176, 177 exist; footprint will contain `HD` and `SC` (FR-R-178-2, §4.3) |
| 183 | `Bridge:theorem` | `Bridge.sm_R` | «STATUS-183» | `Bridge.sm_R_of_rows … : SM.hyp_R := SM.sm_R_of_cv_R (RProof.cv_R_of_rows …)` PROVED (`RProof/RALedgers.lean:2365`; `SM.sm_R_of_cv_R` in `Bridge/SmR.lean`, 2026-09-14); reduces to `Bridge.sm_R := SM.sm_R_of_cv_R RProof.cv_R` (FR-B-183: BRIDGE.md §3 (19)-(21) verbatim, no new mathematics); waits only for 178 |
| 184 | `SM:corner_laws_and_soft` | `SM.corner_laws_and_soft` | pending | assembly `corner_laws_and_soft_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData) (hinh : CInheritsData) : CornerLawsAndSoftData` PROVED in the DRAFT `work/drafts/cvtail/Wave1_Assembled.lean:4367` (not ported; D-CVT-5, FR-F-184-1..4); needs 183 (`hR := Bridge.sm_R`), 110 (`h7 := thm_C_S7`), 128 (`hinh := cor_C_inherits Bridge.sm_R`) AND the `CInheritsData` UNIFICATION: the draft's 11-field bundle (`vertex_edge_law : CS7Data`, `triple_law : hyp_R`, `soft_theorem : CSoftData`) must be replaced by the comparison lane's FINAL 12-field `SM.CInheritsData` (`SM/CInherits.lean:52`: `root_values` added; the three fields in `ALawfulData` shapes, the bundle direction proved by the §6 `example`s, FR-CM-15) — field-type edits only, `corner_laws_and_soft_of` unchanged (D-CM-3; port note 20:27Z); `hs := thm_C_soft` is available since 20:25Z; reported INCOMPLETE |
<!-- END:PENDING -->

**The «PENDING-N» pending rows, by reason** (at 22:40Z: 10; `python3 tools/claims.py --pending-only` «VERIFY lists the
same»; all ten are claim rows — the interface row `src:contact` and `hyp:R` are accepted):
- **1 deferred claim row** — 57 (the author's decision, D-GAP2 item 5).
- **1 row kernel-proved modulo named leaves** — 110 `thm:C-S7`: five named Props, ≈ 8-12k lines, 2-3 further waves; stopped
  by audit A-110-1 (§3.1). The 2026-09-14 estimate D-CC-4 was 11-15k lines for the whole row; the corner lane produced
  `SM/CornerChainUnits.lean` (11 842 lines, library) + `SM/CS7Sliding.lean` (2 956) + the 8 958-line draft and still owes the
  remainder above.
- **2 one-liners blocked on 110** — 127, 128 (their `_of` theorems are proved and ported).
- **3 R rows in bounded waves at draft time** — 174 (one Prop), 176 (three Props), 177 (Wave 3b): «OUTCOME-174/176/177».
- **3 assemblies proved modulo inputs** — 178 (`cv_R_of_rows`), 183 (`sm_R_of_rows`), 184 (`corner_laws_and_soft_of`, draft);
  184 additionally needs 128 → 110 and the `CInheritsData` unification, so it is INCOMPLETE whatever the R waves return.

### 3.1 Row 110 `thm:C-S7` — kernel-proved modulo five named leaves; audit A-110-1

Record: AUTHOR_NOTES "Corner chain … design panel judged" (15:25Z; D-CC-1..4, FR-CC-1..15), "Corner wave 1 assembled" (18:46Z),
"Corner wave 2b launched (row 110 sliding branch)" (18:58Z), "Reassessment audit A-110-1" (20:46Z), "Corner wave 2b merged; the
sliding companion ported as SM/CS7Sliding.lean" (21:02Z), "Corner wave 3 launched (the bounded decisive test)" (21:06Z),
"Corner wave 3: six of eight units back; interim reading" (22:01Z), "… corner K composed" (22:17Z), "Audit A-110-1 concluded:
the decisive test did NOT close row 110; corner construction stops" (22:40Z); state files `work/drafts/corner/port/CS7_STATE.md`
and `W3_ASSEMBLY_REPORT.md` §6 (honest state and the mechanical port recipe), §7 (order of attack).

The statement is fixed and reviewed as part of the corner-chain statements: `CS7Data.vertex_edge_law` (D-CC-1: `g.VertexEdgeAt
M a → ∀ h₁ h₂ tp tm, C(P₊) − C(P₋) = contactSign · C(λ₁) · C(λ₂)`, the consumer's shape; companions `.bigon` / `.sliding`;
the type dichotomy `vertexEdge_bigon_or_sliding` is a description, not a hypothesis, FR-CC-7; `s = g.contactSign M a`, FR-CC-8;
the halves' genericity proofs universally quantified, FR-CC-9; sides at every pair of side parameters, FR-CC-10) in the
accepted `SM/CornerChainStatements.lean` (shared with the accepted rows 103/105/112). What is proved: `thm_C_S7_of (hF :
FloorTheoremData) (hsing : CbSingletonData) : CS7Data` from exactly two leaves, and the sorry-free reductions of those leaves to
five named Props — `w3_s7_sliding_law_at_of₂ : w3_SlidingRet → w3_SlidingCarriers → …` (W3_Assembled.lean:4829) and
`w3_s7_bigon_law_at_of : w3_BigonFSector → w3_BigonReturnedRows → w3_BigonOneNewborn → …` (:8876). Everything else on the path
(sg_daughters_products, sft_same_sign, sft_loop, U110-A/B/C/D/H/I, A2, E, SPLIT, RET, ROT's angle/merge/algebra/transport, F's
residual identity, SITE's bigon site, BLOCK's rows, J's floor entries, K's row algebra) is proved; the library parts are ported
(`SM/CornerChainUnits.lean`, `SM/CS7Sliding.lean` = the sliding companion after wave 2b, `SM/BigonDeletion.lean` = the generic
RII (bigon) deletion constructor of the moves toolkit, D-RM-4).

**The RET finding (rule 4, false-as-stated leaf, no statement change):** unit RET found `s7b_SlidingTransport.ret` FALSE as
stated on the side whose contact crossing is {a, M} (the mark map sends λ₁'s vertex 0 to μ_M, whose successor is the leg visit,
an image mark of λ₂); the corrected mark map `s7r_slidingMark'` (λ₁'s vertex 0 → v_a, λ₂'s → μ_M) has its `ret` PROVED there, so
S1 `w3_SlidingRet` (= ROT's `s7q_box_ret`) and S3 must be RESTATED on `s7r_SlidingTransport'` before RET's material can be
consumed (W3_ASSEMBLY_REPORT §7 item 1; CS7_STATE.md). The row statement `CS7Data` is untouched by this.

**Audit A-110-1** (rule: three substantive waves on one branch without accepting the row; §6): diagnosis "decomposition size,
not mathematics" — the leaves are concrete geometric transports of carrier data through the wall, the same shape as the
completed G11 RIII transport (11k lines); decisive test = corner wave 3 (eight units + merge assembler) closing both leaves
sorry-free with registered axioms only, bound 2026-09-16 00:30Z; consequence on failure "no further corner construction; row
110 reported kernel-proved modulo the named leaves, 127/128/184 incomplete, effort to the R rows". The wave finished 22:38Z
inside the bound with the criterion NOT met (sliding two Props, bigon three Props); the consequence was applied at 22:40Z.
The remainder (≈ 8-12k lines, 2-3 further waves) is recorded as a decision for the author, not the executor.

### 3.2 Row 57 `lem:gauss-two-discs` — deferred (unchanged; the author confirmed the deferral, D-GAP2 item 5)

Text of the 2026-09-14 §3.2 stands. New on 2026-09-15: `lem:corner-values` (i), the other consumer of row 57 per
`blueprint/DEPENDENCIES.json`, was proved unconditionally by the corner lane (`corner_values_i`, graft of architect A, 15:25Z),
so no accepted row depends on row 57 and the blueprint edges 57 → 104 and 57 → 105 are both unrealised by the proof route.

### 3.3 The GAP-2 chain — CLOSED by the author's decision D-GAP2 (replaces the 2026-09-14 §3.1)

The 2026-09-14 review's §3.1 paragraph described row 91 as proved modulo `SM.AmbientIsotopyDescent` with no policy route to
close it. On 2026-09-15 13:39Z the author (through Mark; "I authorize this reading as the author") decided the additive form:
declare the printed descent sentence of lit:homfly as its own axiom about the existing `SM.homfly`, `axiom SM.lit_homfly_descent
: SM.AmbientIsotopyDescent`, registered as a second declaration of lit:homfly (not a sixth interface), interface-reviewed like the
other four; close row 91 as `cp_finite_contact_path_of_descent lit_homfly_descent`; declare `src:contact`; row 57 stays deferred;
the reassessment rule applies per branch. Execution (D-GAP2-1..4, D-GAP2-2b; §4.3): the axiom module `SM/LitHomflyDescent.lean`
(13:49Z), the policy key, the verifier relaxation, row 91 accepted 14:25Z; then five lanes, each with a design panel (two
architects + judge), fidelity risks recorded BEFORE stating, frozen `Statements_FINAL.lean`, prover units on byte-identical
copies, assembler, port, review: contact (src:contact, 161, 94, 162; 15:03Z-17:12Z), floor (99, 100; 14:58Z-17:50Z), CV/R tail
(155, 165, 175; 15:49Z-18:39Z; 174/176/177 ledgers proved with the moves as interfaces), corner (103, 105, 112; 15:25Z-20:25Z;
110 open), comparison (122; 17:28Z-20:50Z; 127/128 proved modulo 110), plus the moves toolkit (D-RM-1..4: the generic RII
deletion constructor `SM/BigonDeletion.lean`, 20:19Z). One internal leaf was false as stated and repaired without a row-statement
change (D-FL-4: `MirrorSubstitutionData.coeff` needs `(-1)^k.natAbs`, counterexample `ui_coeff_toNat_false`); two library
interface Props were unrealisable as stated and replaced by weak forms in new modules (D-RM-2; §5).

### 3.4 The R obligations 174/176/177, `RProof.cv_R` (178), `Bridge.sm_R` (183) and the final theorem (184)

«Replace this paragraph with the outcomes.» At draft time: 175 accepted (18:39Z); 174 and 176 in their bounded second waves
(the site + consumer wave was the first substantive attempt on each row's consumer obligations, D-RM-2's sites the first on the
move interfaces — both landed; §6), 177 in Wave 3b after audit A-177-1 (§6). The ledgers `gsc_ledger` / `est_ledger` /
`esc_ledger` of 174/176/177 are PROVED from `CV.CarrierSlotFloor` (library `RProof/RALedgers.lean`, 18:11Z) with the
Reidemeister-move realisations stated as explicit interface Props (D-F11 pattern; D-RM-1); the moves toolkit realised the
generic bigon deletion (`exists_rii_deletion`, general j; the j = 1 site builder `exists_bigonData_of_triangle`) and the row
glue `gsc_fulltwist_of_bigon`, `est_port_weak_of_bigon`, `esc_rii_after_smoothing_of_bigons`, `esc_switch_riii_of_chain`,
`s7_rii_witnesses` (all sorry-free, 20:19Z). None of `RProof.generic_selected`, `RProof.extreme_transport`,
`RProof.extreme_selected`, `RProof.cv_R`, `Bridge.sm_R`, `SM.corner_laws_and_soft`, `SM.thm_C_S7`, `SM.thm_comparison`,
`SM.cor_C_inherits` is declared in `work/lean` at draft time (`grep -rn` over `work/lean` for `theorem <name>`: no hit; D-F11).
`RProof/RALedgers.lean` was not edited by any unit or assembler (D-RM-5, D-RM-6, A-177-1 D2: replays with extended interfaces
in the row modules instead). If «OUTCOME-174/176/177» all close: 178 `:= cv_R_of_rows …`, 183 `:= SM.sm_R_of_cv_R RProof.cv_R`
become one-liners with footprint `9` (§4.3), the R coverage of §4.5 becomes complete, and only 110 → 127/128 → 184 stay open.

### 3.5 `src:contact` and `hyp:R` — both accepted

`src:contact` (`SM.src_contact`, `SM/SrcContact.lean`; the fifth literature interface) was declared 15:10Z and accepted 16:51Z
(§2 line m97; §4.3). `hyp:R` unchanged from 2026-09-14 (accepted 15:45Z that day; `SM/HypR.lean`). Both hypotheses of the package
(`SM.hyp_R`, `CV.hyp_R`) are Prop definitions; the five literature interfaces are now all declared, plus the author-authorised
second declaration of lit:homfly.

---------------------------------------------------------------------------------------------------------------------

## (F) §4.3 Literature declarations — replacement text; plus §4.4 / §4.6 deltas

### 4.3 Literature declarations exactly printed; no extra axiom, sorryAx or native_decide

**All five permitted interfaces are declared**, each as a single `axiom` in ∃-form over a field-named Prop structure of the
printed clauses: `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness` (`work/lean/SM/LinkInterfaces.lean`), `SM.ng_finite_word`
(`SM/FrontInterfaces.lean`) and — new 2026-09-15 — `SM.src_contact` (`SM/SrcContact.lean:224`). In addition, on the author's
decision D-GAP2, **a sixth axiom constant `SM.lit_homfly_descent` is declared as the SECOND declaration of the interface
lit:homfly** (`SM/LitHomflyDescent.lean:37`), so `work/lean` contains six `axiom` declarations for five literature inputs.
TARGETS.md ("Its only unproved nonstandard inputs may be the five listed literature interfaces") is met in the sense the
author authorised: the sixth constant is a printed sentence of one of the five listed interfaces, not a sixth interface
(D-GAP2-2; disclosed here as FR-R-178-2 / D-CVT-6 require).

**`SM.lit_homfly_descent : SM.AmbientIsotopyDescent`.** The sentence declared is exactly the last printed sentence of lit:homfly
(`blueprint/AXIOM_REGISTRY.md` lines 14-15 = `reference/SM/sm-3-statesum.tex` 920-921): **"Its value depends only on the oriented
link presented by D"**, for the map `D ↦ H_D(a,z)` of the first sentence, i.e. for the fixed witness `SM.homfly` of the accepted
`SM.lit_homfly` (whose own reading of that sentence is `HomflyClauses.descent` over `LinkEquiv`, design D2 — weaker, which was
GAP-2). It is read on the spatial vocabulary of the accepted rows 89-91: `AmbientIsotopyDescent` (`SM/ContactPathOfDescent.lean:177`,
a `def … : Prop` stated and statement-reviewed on 2026-09-14, `work/reviews/cp-finite-contact-path-conditional.json`) says that
along every jointly smooth family of oriented spatial embeddings (`SpatialFamily`, indexed by ℝ) whose two ends have ordinary
regular generic xz projections, `homfly` takes the same value on any polygonal `HeightMarking` readings of the two end diagrams.
Policy registration: `lean/axiom-policy.json` = `work/lean/axiom-policy.json`, `"literature"`, key `"lit:homfly (descent sentence)"`
→ `"SM.lit_homfly_descent"` (D-GAP2-2). Tool edit: `verify_bundle.py` line ≈ 100 enforced `set(policy['literature']) == {the five
registry ids}`; it now compares `{k.split(' ')[0] for k in policy['literature']}` with the five ids, so the ceiling on literature
INPUTS is unchanged (exactly five labels) while a second declaration of an input is admitted under its own key
(D-GAP2-2b; the one edit to a package tool in the whole execution, reversible, flagged to Mark and the author;
`tools/check_lean.py` untouched — its `allowed = policy['standard'] + list(policy['literature'].values())` already admits the new
value). Interface review against the registry text: `work/reviews/lit-homfly-descent.json` (3/3 lenses faithful, 2 refuters
clean; 14:25Z; inputs `lit-homfly-descent-reviewer-input-statement.lean.txt` = the axiom module, the frozen Prop file, the
registry excerpt `lit-homfly-registry-excerpt.md.txt`). Its disclosed readings, all judged non-blocking: STRONGER — FR-LHD-1,
the clause is stated on a jointly smooth family of EMBEDDINGS, so it bundles the isotopy-extension theorem (which the source
proves itself at sm-3:3276-3311 for this very use) with the literature sentence; the literal form `AmbientIsotopyDescentLit` and
the proved split `AmbientIsotopyDescentLit ∧ IsotopyExtension → AmbientIsotopyDescent` are in the module; FR-1/FR-LHD-3, "X
presents L" is record-level (`HeightMarking`), so the axiom also asserts equal `homfly` for any two polygonal diagrams carrying the
same signed O/U record of one regular generic projection. WEAKER — FR-LHD-4, both ends must have `RegularGenericProjection` (the
printed sentence covers every diagram); readings only; same labelled circles, orientation- and label-preserving; smooth (C^∞)
category only; FR-LHD-2, ℝ-indexed family (a [0,1]-isotopy enters after a clamp); c = 0 vacuous. Truth: for the genuine
HOMFLY-PT polynomial the axiom is true under the standing D2 premise (formal Reidemeister moves + planar isotopy complete for PL
link isotopy) already carried by `lp_lm_uniqueness`; it is not derivable from `lit_homfly` alone — exactly the GAP-2 content. Axiom
set of the constant itself: `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent]` (its type mentions
`homfly`). **Accepted rows whose footprint contains `SM.lit_homfly_descent` (12, from `declaration-audit.json` 21:09Z):** 91
`cp:finite-contact-path` (std+H+HD+LM+LMU), and with the full set `9`: 94 `fd:contact`, 162 `CV:ax:slbound`, 99
`cf:thm-carrierfloor`, 100 `thm:floor`, 155 `CV:thm:carrierfloor`, 165 `CV:singleton_D_i`, 175 `R:extreme_pair_zero`, 103
`cb:singleton`, 105 `lem:corner-values`, 112 `thm:C-soft`, 122 `prop:anchor-values` — plus, when declared, 178/183/184 and
174/176/177 through `CV.carrierSlotFloor` (D-CVT-6). No row accepted before 2026-09-15 depends on it.

**`SM.src_contact : ∃ r tb : (ℝ → E3) → ℝ, SrcContactClauses r tb`** (D-SC-1; registry `blueprint/AXIOM_REGISTRY.md` "src:contact —
AXIOM" = sm-3:3341-3365). The existential interface form: the literature's rotation number `r` and Thurston-Bennequin invariant
`tb` are never defined by the document, so they are existentially quantified functions `(ℝ → E3) → ℝ` and the four printed
formulas are the fields of `SrcContactClauses` — `rotation` r = (D − U)/2, `thurston_bennequin` tb = w − (D + U)/2,
`pushoff_self_linking` sl(T₊(L)) = tb − r for every positive pushoff circle of every pushoff annulus (rows 84/87's
`GenericFront.IsPositivePushoff`), `transverse_front_writhe` sl K = writhe of the front for a generic positive transverse front
(def:transverse-front). Fixed witnesses `SM.rot`, `SM.tb := Classical.choose …`, `src_contact_spec`. `SM.sl K := slCircle
K.circle` is the document's own fd:framed-linking number (row 88) at row 88's radius (D-SC-2), so the axiom has content relative
to an independent definition (the GAP-2 memo's §3(a)(ii) objection of 2026-09-14 no longer applied). **What is NOT constructed:**
no contact-geometric `r` or `tb` (no winding of L′ in ξ, no contact-framing linking number) — the axiom asserts nothing about them
beyond the two defining formulas on the front class (FR-SC-1; the ∃-form is PROVABLY equivalent to the substituted consequence
`sl(T₊) = w − D` on the Legendrian class ∧ `sl = w` on the transverse class, `src_contact_iff_consequence`, standard axioms); the
convention, D + U, provenance and scope sentences have no field (theorems `lcContactForm_toE3`, `alpha_eq_lcContactForm`,
`isPositiveTransverse_iff`, the accepted `downCount_add_upCount`; FR-SC-6/8, the ng:finite-word precedent); no transverse-isotopy
class `T₊(L)` is formed (FR-SC-3). Narrowings: Legendrian formulas for KNOTS whose front lies on ng:front-domain's class
(FR-SC-2); real-valued quantities (FR-SC-10); `slCircle T = 0` off its domain, never exercised (FR-SC-9). Consistency probe on file
(D-SC-6: transverse unknot sl = −1 = front writhe; a Legendrian eye's pushoff gives sl = −0.9998 ≈ w − D = tb − r; a refuter's
Legendrian with D ≠ U confirmed the sign convention). Interface review `work/reviews/src-contact.json` (3/3, 2 clean, 16:51Z).
**Accepted rows whose footprint contains `SM.src_contact` (13):** `src:contact` itself and 161 `CV:ax:etnyre` (std+SC), and the
eleven `9`-rows listed above (94, 162, 99, 100, 155, 165, 175, 103, 105, 112, 122).

**"Allowed name but stronger type"** re-examined for the two new constants: `lit_homfly_descent` is formally stronger than the
registry sentence in the two disclosed ways above (isotopy extension; record-level presentation) and weaker in six; every one was
matched to a printed sentence or to an accepted-layer convention by the three lenses and the two refuters, and the executor
recorded FR-LHD-1..4 before stating it (D-GAP2). `src_contact`'s four fields are the four printed formulas; nothing is stronger
(`stronger_than_source` empty), four narrowings disclosed. **Kernel evidence:** the current receipt (21:09Z) passed with 182
mapped and 39 005 audited declarations; the audit's axiom sets over the 182 mapped declarations are exactly the ten patterns of
§2's legend — subsets of {`SM.lit_homfly`, `SM.lit_homfly_descent`, `SM.lp_lm`, `SM.lp_lm_uniqueness`, `SM.ng_finite_word`,
`SM.src_contact`} over the standard three; no `sorryAx`, no `Lean.ofReduceBool`, no other constant («re-count at «RECEIPT»»).
`work/lean` contains no `sorry` (rule 3; the open leaves live in `work/drafts/`). The CV "axiom" rows 161 and 162 are theorems
(`CV.ax_etnyre` from `SM.src_contact`; `CV.ax_slbound` from `SM.fd_contact`), as `CV.ax_homfly` and `CV.gausscode_polynomial`
were on 2026-09-14.

### 4.4 delta — the R table (replace the rows of 175 and, per outcome, 174/176/177/178/183/184)

| obligation | policy name | status | declared? | module | axioms | note |
|---|---|---|---|---|---|---|
| `R:generic_selected` | `RProof.generic_selected` | «STATUS-174» | «yes/no» | «RProof.GenericSelected…/—» | «9/—» | «OUTCOME-174» (before wave 2: composition proved modulo `r174_arc_rec_moves`) |
| `R:extreme_pair_zero` | `RProof.extreme_pair_zero` | accepted | yes | RProof.ExtremePairZero | std+H+HD+LM+LMU+NG+SC | accepted 2026-09-15 18:39Z; from `CV.singleton_D_i` (165) |
| `R:extreme_transport` | `RProof.extreme_transport` | «STATUS-176» | «yes/no» | «—» | «9/—» | «OUTCOME-176» (before wave 2: composition proved modulo three Props; D-RM-5/6 weak-form replays) |
| `R:extreme_selected` | `RProof.extreme_selected` | «STATUS-177» | «yes/no» | «—» | «9/—» | «OUTCOME-177» (switched RIII core `G11_core_sw` closed 21:56Z; (6) realiser and unit E/G/H open before Wave 3b) |
| `R:cv_theorem` | `RProof.cv_R` | «STATUS-178» | «yes/no» | «RProof.…/—» | «9/—» | `cv_R_of_rows` proved (RALedgers.lean:2354); «one-liner declared / still needs 174/176/177» |
| `Bridge:theorem` | `Bridge.sm_R` | «STATUS-183» | «yes/no» | «Bridge.…/—» | «9/—» | `sm_R_of_rows` proved (RALedgers.lean:2365); waits only for 178 |
| `SM:corner_laws_and_soft` | `SM.corner_laws_and_soft` | pending | no | — | — | INCOMPLETE — needs 183, 128 → 110, and the CInheritsData unification (§3) |

Exposure paragraph addition: `SM.thm_comparison` would take `SM.hyp_R` as the explicit parameter and is not declared (blocked on
110 only, §3); its library form `SM.thm_comparison_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData)` (`SM/Comparison.lean`) exposes
`hR` explicitly, as does `cor_C_inherits_of` (FR-CM-7, FR-CM-17). The accepted 175 exposes `hn : 3 ≤ n` and the event hypotheses
like its siblings and takes no R, lawful-quantity or corner-law assumption (reviews/r-extreme-pair-zero.json); its footprint is
`9` through `CV.singleton_D_i` ← `CV.carrierSlotFloor` ← `SM.cf_thm_carrierfloor.clauseC` ← `SM.fd_contact` ← row 91, which is
where `HD` and `SC` enter the R lane (D-CVT-6).

### 4.6 delta — the clause table for `SM.corner_laws_and_soft` (the final declaration is NOT declared)

| Clause | Status at completion («FINAL-TIME») |
|---|---|
| Chamber constancy and silence | **accepted** (unchanged) |
| Flat deletion jump | **accepted** (unchanged) |
| Vertex-edge jump (`thm:C-S7`) | **open — kernel-proved modulo five named leaves** (§3.1); `SM.thm_C_S7` not declared; both bigon branches and the sliding branch are covered by the fixed `CS7Data` and by the draft proof's two leaves, the actual children `λ₁, λ₂` and the sign `s = contactSign` as printed (FR-CC-7..9) |
| Triple invariance (`hyp:R` discharged) | «open / **discharged**»: `SM.hyp_R` accepted; `Bridge.sm_R_of_rows` proved; `Bridge.sm_R` «not declared / declared» (§3.4) |
| Full cusp jump (`cor:C-inherits`) | **open** on 110 only: `cor_C_inherits_of` and `cusp_deletion_generic` proved (threaded cusps included, no emptiness hypothesis, FR-CM-9/9′); `SM.cor_C_inherits` not declared |
| Empty-cusp zero | **accepted** (unchanged) |
| Soft theorem (`thm:C-soft`) | **accepted 2026-09-15 20:25Z**: `SM.thm_C_soft` (`SM/CSoft.lean`; reviews/thm-C-soft.json) — every admissible q (all direction / attachment-sign sectors incl. zero sectors, `SoftAdmissible`), `∃ ε₁ > 0, ∀ ε < ε₁` (FR-CC-12) |
| Descent and normalization | **accepted** as A-level rows (unchanged); their transfer to C is inside `cor_C_inherits_of` (`root_values`, `shift_invariant`, `descends`, `reversal_law`, `triangles`), proved modulo 110 |

---------------------------------------------------------------------------------------------------------------------

## (G) §5 Remaining gaps (honest list) — full replacement

## 5. Remaining gaps (honest list)

1. ~~**GAP-2**~~ — **closed on 2026-09-15 by the author's decision D-GAP2**, not by a proof: the missing clause
   `SM.AmbientIsotopyDescent` is now asserted by the registered axiom `SM.lit_homfly_descent` (second declaration of lit:homfly;
   §4.3). Twelve accepted rows and every future R-lane / final-theorem declaration depend on it. The interface review judged
   it a faithful reading of sm-3:920-921 with the disclosed strengthening FR-LHD-1 (isotopy extension bundled) and six
   narrowings; a reader who does not accept the author's reading should treat those twelve rows as "proved modulo
   Reidemeister's theorem for smooth isotopies + isotopy extension", exactly the 2026-09-14 label.
2. **Row 110 `thm:C-S7` is open**: kernel-proved modulo five named Props (S1, S3; B1, B2, B3; ≈ 8-12k lines, 2-3 waves) after
   audit A-110-1 stopped the corner construction (§3.1). Its two one-liner consumers 127 `thm:comparison` and 128
   `cor:C-inherits` and, through 128, the final theorem 184 are INCOMPLETE for this reason alone. The remainder is the author's
   decision.
3. **Rows 174/176/177/178/183**: «OUTCOME-174/176/177; if any of the three failed, its audit and the honest state "ledger, site,
   transport and composition proved; N named geometric leaves open" (174: 1; 176: 3; 177: unit E/G/H + realisers) go here,
   and 178/183 stay undeclared».
4. **Row 184 `SM.corner_laws_and_soft`** is INCOMPLETE regardless of item 3: `corner_laws_and_soft_of` is proved only in the
   draft `work/drafts/cvtail/Wave1_Assembled.lean`, needs `thm_C_S7` (item 2) and `cor_C_inherits Bridge.sm_R`, and its
   `CInheritsData` parameter must be re-typed to the comparison lane's FINAL `SM.CInheritsData` (§3, row 184).
5. **Row 57** `lem:gauss-two-discs` deferred (the author, D-GAP2 item 5); no accepted row depends on it.
6. **Two library-interface findings of the R lane (false-as-stated fields of accepted library structures, NOT edited):**
   - **D-RM-5 (row 176, `est_PortData.port`)**: the literal field "the switched D₊ is carried to D₀ by oriented RII moves"
     (`Relation.ReflTransGen RII ((carrierDiagram … q').switch y) (carrierDiagram … q)`, `RProof/RALedgers.lean:878`) is
     UNREALISABLE as stated — an RII chain cannot cross the wall (`OutsideMatch.eval_eq`; both moves-panel architects and the
     judge, D-RM-2). The printed "port relation" sentence is rendered by the WEAK port form `est_port_weak` (∃ D₀′, RII-chain
     ∧ `homfly D₀′ = homfly D₀`), which IS proved from an actual constructed R-II deletion (`est_port_weak_of_bigon` on
     `exists_rii_deletion`, `SM/BigonDeletion.lean`; the ledger re-base `fulltwist_coefficient_of_port_weak`). The accepted
     library keeps its literal field; row 176 closes through the `s176_` / `r176_` weak replays (D-RM-5, 20:37Z); the row leaf
     statement `RowShape @ExtremeTransportData` is untouched. The site report's proposed 5-line edit (F-176-1) was NOT applied.
   - **D-RM-6 (row 176, `est_PortData.rot / alt₁ / alt₂`, RALedgers.lean:903-906)**: FALSE as stated without the hypothesis
     `wind(S) ≠ 0` — a MIXED affected carrier breaks `UniformOrOneDissentCV` and `R = R₁ + R₂ + 1` (unit LEDGER, 22:17Z). The
     corrected forms are realised under `wind ≠ 0` (`r176l_est_port_relation_uniform` / `_weak_uniform`) and the row closes
     through a replay of `est_row_H` with a `wind = 0` split (both row terms vanish there: `rowTerm_of_mem_Ind`, `GT_wind_eq`;
     13 lines, `r176_est_row_H_weak_uniform`). The printed proof's "clean outer carriers" sentence is thus rendered by the weak
     form; the literal fields stay in the library unused by the composition. Also recorded by the R176 assembler (§3.1):
     `r176l_smooth_black_box` was stated too strongly (binders lacked `hcomp`, `habc`, `hu hv hju hjv huv`); superseded by
     `r176_outer_carriers_L` / `r176_mixed_bridge` with the full binder list.
   - **Row 174 (R174_ASSEMBLY_REPORT §8, no statement edit needed):** the ledger's `σ` is orientation-dependent (`r174w_sigma =
     −τ(m_AB)`, equal to `crossingSign ℓ₁ ℓ₂` in the printed orientation and its negative in the reversed one) while the
     docstrings of `gsc_Ledger` / `gsc_moves` read σ as `crossingSign ℓ₁ ℓ₂`; `s174_hrec_prop` is provable only at the ledger's
     binding `q' = W.τ qAB` (false for arbitrary q′) and is used exactly there. «VERIFY: the report asks for an AUTHOR_NOTES
     entry on the orientation dependence; none was found in AUTHOR_NOTES at draft time.»
7. **Row 177's configuration type (A-177-1):** the accepted transport's `RProof.G11_Config` carries the field `trans :
   ¬ IsAlternating …` (`RProof/GenericTransport.lean:125`, "the divide over-order of the three strands is transitive"), which is
   FALSE on the K3 side of row 177 — the very reason 177 switches a crossing — although no accepted proof uses `trans` except the
   D8 table. The configuration type therefore OVER-SPECIFIES what its proofs use; none of the 1 056 accepted declarations of
   `RProof.G11_Params` can be instantiated at a 177 site. Remedy taken: the ADDITIVE trans-free copy `G11_ConfigSw` /
   `G11_ParamsSw` (905 of 908 declarations re-derived; `gu6_htrans` becomes the hypothesis `htrans`, `riii` the parametrised
   `w3de_riii_param`, `core_of_params` becomes `G11_core_sw`; `W3_A1_Assembled.lean`, 7 827 lines, compiles in 36 s). The
   author's cheaper option — drop `trans` from `G11_Config`, statement-neutral for every row, ≈ 4k lines instead of ≈ 12.5-13k —
   is a rewrite inside an accepted module, which the package forbids and only the author could grant; NOT taken, recorded.
8. **Stale docstrings on `AmbientIsotopyDescent`** (`SM/ContactPathOfDescent.lean`): the module and the predicate were written
   on 2026-09-14 when the clause was an undischarged premise; its header line 1 said row 91 is "NOT mapped". Fixed 2026-09-15
   22:40Z by a comment-only header (line 2: the descent clause is asserted by the registered axiom, row 91 IS mapped and accepted);
   the docstrings that call `AmbientIsotopyDescent` "a `def … : Prop`, not an axiom" remain LITERALLY TRUE of the predicate — the
   assumption lives in `SM/LitHomflyDescent.lean`. Also carried over from STATUS.md item 6 (2026-09-14): docstring fixes owed in
   `LinkLaurentRing.lean:80-81`, `LinkInterfaces.lean 55-60/180-181`, `FlatCarriersDefs.lean` header («VERIFY whether done»);
   the citation nits of §2 (row 91: 3310-3312 vs 3313-3316, 3276-3312 vs 3264-3313; row 94 and the `thm-C-soft` proof locator
   992 vs 993; the frozen Prop file's docstring "exactly what the printed proof consumes at sm-3:3313-3316").
9. **Reviews are AI reviews only** (STATE_OF_WORK §4): all 182 accepted rows and the two interface declarations of 2026-09-15
   were reviewed by Claude Code subagents of the same model family as the implementer (claude-fable-5-1); the 14 rows of
   2026-09-15 had one workflow each (three lenses + two refuters, proof withheld), no second session, no countersignature by a
   separate session; the 39 handover rows keep their 2026-09-13 countersignatures. One disclosed breach of proof-withholding:
   a refuter of row 175 read the one-line proof term at `RProof/ExtremePairZero.lean:85` (identical to the term in the statement
   file's header). No human has read any review.
10. **Strengthenings and weakenings the reviewers flagged on 2026-09-15** (all non-blocking; the full lists are the review
    files' arrays, §2): row 122's anchor clauses are a proved SUPERSET of the printed anchors (no def:anchors case conditions,
    FR-CM-3′) and F has the integer codomain (FR-CM-1); row 175's fields hold for ALL punctured parameters and drop the K3 ↔ empty
    pairing hypothesis (FR-R-175, the RowShape convention); row 165 holds for every CV-generic polygon (N1); rows 99/155's
    clause (B) is asserted for the normalised orientation only — the literal claim is false for all-negative polygons, so this is
    a correction of the reading, not a loss (FR-FL-B1 / FR-CV-155-5); row 100's `z_parity` has no turn hypothesis; row 91 and the
    new axiom take ℝ-indexed families (FR-CP-5, FR-LHD-2); rows 94/162/91 assert nothing for a knot without a polygonal
    `HeightMarking` reading (FR-1); row 162 narrows to `TransverseKnot` (FR-FC-5); `src_contact`'s Legendrian formulas hold for
    knots with generic fronts only (FR-SC-2); row 112 quantifies the genericity of P_ε instead of asserting it (FR-CC-12, the
    `∃ hQ` form recovered by `exists_generic`); row 105's hypothesis "embedded" is the gloss m_Q = 0 (FR-CC-4).
11. **The R lane's weak-form readings (library, not row statements):** D-RM-2 replaced two unrealisable D-F11 interface Props
    by weak forms — `est_port_weak` (item 6) and `esc_rii_after_smoothing_weak` (∃ one pair = the library `smoothDiagram` with
    record clauses, instead of ∀ oriented smoothings) — with the old Props kept as recorded; the 110 bigon branch avoids the RI
    curl deletion (no `RIData` anywhere) by reading the curl inside `knotRestrict` (`two_component_row_of_recordIso`,
    `curl_block_value`). The row statements of 174/176/177 (frozen `RowShape` bundles) are unaffected; whether the weak forms
    suffice is proved, not assumed (`fulltwist_coefficient_of_port_weak`, `esc_rii_after_smoothing_of_bigons`, sorry-free).
12. **Non-vacuity / geometric-reading items argued but not kernel-checked** (carried over): K-4, FR-2, FR-ER-2, K-3 (2026-09-14
    item 7); new: the truth of `src_contact` on the accepted definitions rests on the judge's numeric probe (D-SC-6) and a
    refuter's example, and the identification of the document's `sl` with Etnyre's / Geiges' `sl` is rem:sl-convention, a remark
    (FR-SC-4); the truth of `lit_homfly_descent` rests on the D2 premise (formal Reidemeister completeness).
13. **Conditional library theorems NOT mapped** (no content effect on accepted rows): `SM/ContactPathOfDescent.lean`
    (`cp_finite_contact_path_of_descent`, now consumed by the mapped row 91), `Bridge/SmR.lean`, `RProof/X1Rows3.lean`,
    `SM/LinkingCalculus.lean` (2026-09-14 item 8), and new: `RProof/RALedgers.lean` (the three ledgers, `cv_R_of_rows`,
    `Bridge.sm_R_of_rows`), `SM/Comparison.lean` (`thm_comparison_of`), `SM/CInherits.lean` (`cor_C_inherits_of`),
    `SM/FdContactStatements.lean` (`fd_contact_of_units`, `ax_etnyre_of`, `ax_slbound_of`), `SM/CarrierFloor.lean` (`_of_bound`
    forms), `SM/CornerChainUnits.lean` (`cb_singleton_of_floor` …; row 110's `thm_C_S7_of` is NOT in it), `SM/CS7Sliding.lean`,
    `SM/BigonDeletion.lean`. D-F11 forbids mapping a row theorem with an undischarged premise; the checker's axiom audit does
    not reach library modules that no mapped module imports (§7).
14. **Blueprint edges 57 → 104 and 57 → 105** not realised by the proof routes (D-ER1; `corner_values_i`); blueprint frozen.

---------------------------------------------------------------------------------------------------------------------

## (H) §6 Process — additions (append after the existing "Reassessment rule" paragraph; the accept-cycle and lane
## paragraphs stand, with the receipt count "79 development receipts … 168 / 36 079" updated to "94 … 182 / 39 005 (21:09Z)")

**Accept cycle 2026-09-15.** Unchanged (ACCEPT_CYCLE.md + `work/port/`): statement fixed BEFORE proving with the fidelity
risks in AUTHOR_NOTES (the five lane entries 14:58Z, 15:03Z, 15:25Z, 15:49Z, 17:28Z each end with "FIDELITY RISKS … verbatim"
before the units were launched) → design panel (two architects: fidelity vs feasibility, + judge; scores recorded) →
`Statements_FINAL.lean` frozen → prover units on byte-identical copies with prefixed helpers → statement pre-review (non-vacuity,
numeric probes) → assembler (statement identity check, clash scan, `#print axioms`) → porter agent (headers only; §0 interface
copies replaced by imports after a byte-identity check against the accepted module) → `lake build` → `map_row.py implement` →
checker → three lenses + two refuters (briefs `work/port/review_prompt_<slug>.md`) → `write_review_and_accept.py` → checker →
`tools/progress.py --once` → AUTHOR_NOTES / STATUS / TASKS. 15 receipts on 2026-09-15 (§0), all passed; 95 `dev-check-*.json` files
in `work/checks/` at draft time (the 2026-09-14 review counted 79 — «VERIFY: 79 + 15 = 94; one receipt is unaccounted for
in that count»), the closing run adds «RECEIPT». Heartbeat: cron every 14 min + `tools/progress.py --watch`.

**AI-review disclosure 2026-09-15** (`ai_review_disclosure` of each of the 15 review files): "AI review. Five separate Claude Code
subagents (model claude-fable-5-1) were spawned by the executor on 2026-09-15 in one workflow: three reviewers with distinct
lenses and two adversarial refuters instructed to find any discrepancy. Each received only the printed SM15 source files, the
row's Lean text with every proof replaced by sorry (reviews/<slug>-reviewer-input-statement.lean.txt), and the Lean definition
modules; none saw the proof module … or the executor's reasoning. …" (the interface review of the axiom: "… only the printed
registry text, the axiom module, the previously reviewed Prop file and the Lean definition modules"). Identities in the map
(182 accepted rows): authors `executor-pod-claude-fable-5-1-20260913` (142 rows), `root-implementation-20260910` (39),
`executor-coldstart-claude-fable-5-1-20260912` (1); reviewers `reviewer-pod-claude-fable-5-1-20260913 (…)` (142),
`review_chirotope-independent-20260910` (30), `review_relgp_full-independent-20260911` (9),
`reviewer-coldstart-claude-fable-5-1-20260912` (1) (recounted from the map at draft time: 128 + 14 = 142).

**The reassessment rule and how it was applied on 2026-09-15** (`/workspace/repos/lean/reassessment_rule.md`: reassess after
two substantive attempts or 60 minutes of active work without a newly accepted source claim; immediate triggers — domain
mismatch, circular dependency, impossible interface, repeated failure, growing helper scope; the response is a bounded method
audit with one decisive test, an effort bound and a stated consequence; only a newly accepted claim resets stagnation; a new
window is not a new accepted claim; report the accepted count unchanged). The author's instruction of 13:39Z: "Apply the
reassessment rule per branch as before." Applications, in order:
- **Resume state (13:39Z):** the GAP-2 branch resumed with its stagnation history (last accepted claims on it rows 89/90,
  2026-09-14 morning; the 2026-09-14 17:00Z audit had recorded the branch as blocked pending the author's decision). Decisive
  test of the window: row 91 accepted by ~14:45Z, bound 60 min, consequence "bounded audit before any further construction".
  **PASSED at 14:25Z** — the first newly accepted claim on the branch, resetting its clock. Each lane then started its own clock
  (floor 14:58Z, contact 15:03Z, corner 15:25Z, CV/R 15:49Z, comparison 17:28Z), and the corner rule was applied per UNIT
  (D-CC-4, D-RM-2: 2 attempts / 60 min).
- **Reassessment note D-RM-1 (17:24Z; rows 110 bigon, 174, 176, 177):** trigger = wave-1 evidence that every RA-type unit proved
  its LEDGER but stated its moves as interfaces and unit U110-G reported NO-GO on the RII/RI witnesses (no generic RII/RI
  constructor in the library). Diagnosis (step 2): "not mathematics, not representation — a missing generic geometric
  CONSTRUCTOR consumed by four rows"; the accepted G11 lane (row 173, one RIII site, ≈ 11k lines) as the feasibility precedent.
  Decision (step 3): ONE shared moves-toolkit lane instead of four realisations. Decisive test (step 4): the panel's judge
  exhibits a TYPECHECKED constructor statement whose output discharges `gsc_moves` / `est_port_relation` / the 110 bigon
  hypothesis by instantiation, with a unit decomposition ≤ 12k lines; bound ≈ 1 h; consequence on failure "174/176/177 and the
  bigon branch of 110 reported 'ledger proved, move stated'"; CONJECTURE labelled (constructor ≈ 8k lines). **Evaluated at
  D-RM-2 (18:24Z):** (i) statement delivered, (ii) consumer glue PROVED, (iii) size AT the boundary for the constructor scope,
  NOT met for the lane as a whole (20-24k incl. 177; ≈ 35-42k for everything the four rows need) → "passed for the constructor
  scope, not for the lane": Waves 1-2 authorised, Wave 3 (row 177) only after Wave 1 closes. Wave 1 closed 20:03Z-20:19Z
  (`SM/BigonDeletion.lean`, D-RM-4: "D-RM-1's decisive test … PASSES").
- **D-CC-5 (18:04Z; acceptance bottleneck, not mathematics):** rows 103/105/112 did not need the still-running heavy unit
  U110-A; wave 2a was decoupled so that proved leaves were not idle behind an unrelated unit — the rule's "diagnose the
  review/acceptance bottleneck instead of discarding a valid proof" (accepted 20:25Z).
- **Audit A-110-1 (20:46Z; row 110):** trigger = three substantive waves (1, 2a/A2, 2b/E) on one branch without accepting the
  row; the lane's other rows were accepted at 20:25Z but the collaborator's "per branch" instruction audits 110 on its own.
  Steps 1-3 in §3.1; decisive test = corner wave 3 (8 units: sliding RET/SPLIT/ROT, bigon F/SITE/BLOCK/J/K + merge assembler),
  success = `Corner_Assembled.lean` with both leaves sorry-free on registered axioms; bound 2026-09-16 00:30Z (≈ 3.5 h
  wall-clock; hard stops given to the agents: units 00:00Z, assembler 00:30Z); consequence on failure stated in advance;
  CONJECTURE labelled. Interim reading 22:01Z (six of eight units back): sliding may close, bigon will not. **Concluded 22:40Z,
  inside the bound: FAILED** (sliding 2 Props, bigon 3 Props); the consequence was applied verbatim — no further corner
  construction, 110 reported kernel-proved modulo named leaves, 127/128/184 incomplete, effort to the R rows. Accepted count
  reported unchanged (121/132 at the audit, 122/132 at its conclusion).
- **Audit A-177-1 (21:21Z; row 177):** immediate triggers — impossible interface (the accepted `G11_Config.trans` is false at a
  177 site, §5 item 7) and growing scope (Wave 3 honest size 12.5-13k vs the plan's 8-10k); the 177 branch had produced no
  accepted claim since 15:49Z. Diagnosis: representation, not mathematics. Options: (i) edit `G11_Config` (statement-neutral,
  ≈ 4k — a rewrite of an accepted module, only the author can grant; NOT taken), (ii) additive trans-free copy, (iii) abandon
  ("ledger proved, moves stated"). Decision (ii) as ONE bounded test: two provers (W3-A1 BC: `GenericTransport.lean` 235-4917;
  W3-A1 DE: 4918-8630 with D8 re-typed as `w3a_riii_param`) + assembler; success = `W3_A1_Assembled.lean` compiles with 0 errors
  and no open `w3a_` sub-leaf; bound units 00:15Z, assembler 00:30Z (2026-09-16); consequence on failure "no further 177
  construction; 177 'ledger proved, moves stated'; 178/183/184 incomplete"; CONJECTURE labelled. Decisions on the skeleton's
  open points D1-D5 recorded (D2: F-177-2 is a replay with an extended interface, NOT an edit of RALedgers). **SUCCEEDED
  21:56Z** (W3_A1_ASSEMBLY_REPORT §0: 7 827 lines, 0 errors, all 20 `w3a_` closed, `G11_core_sw` sorry-free). Wave 3b then
  launched as a NEW bounded window (22:00Z; units E/G/H/REAL + assembler; units 00:30Z, assembler 01:00Z) with the 177 branch's
  stagnation history since 15:49Z retained and the failure consequence restated ("ledger proved, switched RIII core proved,
  bigon-after-smoothing stated"). «OUTCOME-177».
- **Rows 174 and 176 (22:37Z, 22:34Z):** wave 1 (site + consumer units + assembler) = the FIRST substantive attempt on each
  row's consumer obligations (the sites, launched 19:19Z, were the first attempt on the move interfaces and landed 20:31Z /
  20:37Z); each produced a sorry-free composition with a shrinking named remainder (174: one Prop; 176: three). Wave 2 = the
  SECOND attempt, bounded (units 00:45Z, assembler 01:15Z 2026-09-16), with the audit and the honest-state wording fixed in
  advance ("ledger, site, transport and composition proved; N named geometric leaves open"). STATUS 22:40Z: "no branch currently
  past its bound". «OUTCOME-174», «OUTCOME-176».
- **Rule 4 (false-as-stated leaves) invoked four times, never on a row statement:** D-FL-4 (`MirrorSubstitutionData.coeff`,
  15:12Z), D-RM-2 (`est_PortData.port`, `esc_MoveData.rii_after_smoothing`), D-RM-6 (`est_PortData.rot/alt₁/alt₂`), RET
  (`s7b_SlidingTransport.ret`, 22:40Z); plus the R176 assembler's binder defect in `r176l_smooth_black_box`. In every case the
  accepted structure or frozen statement was left as is and the corrected form was realised alongside (D-FR2 pattern).

---------------------------------------------------------------------------------------------------------------------

## (I) §7 Inconsistencies noticed between the tools' output and the notes (for the executor) — replacement

Resolved since the 2026-09-14 review:
- `work/delivery/refresh.sh` line 92 now copies the ROOT `FINAL_REVIEW.md` (`cp -f "$ROOT/FINAL_REVIEW.md" …`, comment "fixed
  18:20Z"); the 2026-09-14 §7 note about `work/FINAL_REVIEW.md` is obsolete. `work/delivery/` itself has NOT been refreshed since
  2026-09-14 18:21Z (its `FINAL_REVIEW.md`, `AUTHOR_NOTES.md`, `receipts/`, `reviews/` are that day's) — run `refresh.sh` after
  the root file is final.
- `SM/ContactPathOfDescent.lean` header (2026-09-14 §5 item 8 and the "documentation debt" of 14:25Z): fixed 22:40Z (§5 item 8).
- `hyp:R`, rows 76-80/83/93, the GAP-2 row count: all closed on 2026-09-14; nothing further.

Still to note (each verified in the files named):
- **`audited_declarations` is not a per-module audit of `work/lean`.** `tools/check_lean.py` builds the MAPPED modules plus
  `Supplemental` (a fixed list of 70 imports in `work/lean/Supplemental.lean`, none of the 2026-09-15 library modules) and runs
  `Supplemental.auditProject` over `env.constants` of that environment; `checked` counts every constant whose origin module is a
  project file, but only constants LOADED by those imports exist in `env`. A library module imported by no mapped module is
  built (`project_sha256` hashes the file) yet contributes nothing to `audited_declarations` and its axiom sets are not
  machine-checked by the checker. Evidence: `dev-check-cs7sliding-library.json` (21:09Z, after `SM/CS7Sliding.lean` was ported)
  reports the same 39 005 audited declarations as `dev-check-row122-accepted.json` (20:52Z) while its `project_sha256` has one
  more file (697 vs 696); `SM/BigonDeletion.lean` (489 declarations, ported 20:19Z) lies between the receipts of 20:03Z (38 949)
  and 20:30Z (39 005), a difference of 56. The `#print axioms` facts quoted in AUTHOR_NOTES for `SM/BigonDeletion.lean`,
  `SM/CS7Sliding.lean`, `RProof/RALedgers.lean`, `SM/Comparison.lean`, `SM/CInherits.lean` come from `lake build` and scratch
  files, not from a checker receipt. Per-declaration rows in `declaration-audit.json` exist only for the mapped declarations
  (`byname == names`), so a `grep '"module": "SM.CornerChainUnits"'` finds nothing although that module IS in the audited closure.
- **"21 vs 20 `w3a_` sub-leaves":** audit A-177-1 (AUTHOR_NOTES 6194) and `W3_SKELETON_REPORT.md` §2.2 say "21 sub-leaves"; the
  success entry (6221) and `W3_A1_ASSEMBLY_REPORT.md` §0 say "all 20 `w3a_*` sub-leaves closed". The report's §1 reconciles them:
  21 replaced `sorry` lines = 20 `w3a_` + `w3a_exists_params`; "the skeleton has 20 `w3a_` statements". Same content.
- **Skeleton line numbers "207 vs 199":** `W3_SKELETON_REPORT.md` places `end G11_ConfigSw` at line 207 (§2.0, §2.2 "lines 350-615",
  the insertion recipe at line 265); the unit reports found the actual line is 199 and every §2 number is offset by 8 ("its
  '207' is line 199, '412' is 404", `W3_A1_BC_REPORT.md` 39, 83; `W3_A1_DE_REPORT.md` 88; `W3_A1_ASSEMBLY_REPORT.md` §7 "anchor on
  names, not skeleton line numbers"). Documentation only; the assembled file compiles.
- **Bigon glue line "8854 vs 8876":** `CS7_STATE.md` gives `w3_s7_bigon_law_at_of` at "line 8854"; `W3_ASSEMBLY_REPORT.md` §6 and
  `grep -n` on `W3_Assembled.lean` give 8876 (sliding glue 4829 in both). CS7_STATE.md is off by 22 lines there.
- **"Seven registered literature axioms + the standard three"** (AUTHOR_NOTES 16:40Z on `SM.fd_contact`; repeated in
  `reviews/cv-ax-slbound.json` `kernel_check`) describes the nine-element list `propext, Classical.choice, Quot.sound,
  lit_homfly, lit_homfly_descent, lp_lm, lp_lm_uniqueness, ng_finite_word, src_contact`, which is SIX literature constants
  (five interfaces + the second declaration) + three standard = nine; the later entries say "the nine registered axioms" and
  `CS7_STATE.md` says "six registered literature axioms". This review uses "the nine registered axioms" / `9`.
- **F-177-2 wording:** `W3_A1_ASSEMBLY_REPORT.md` §6 plans the `esc_interface` replay as an EDIT of `RProof/RALedgers.lean:2027`
  ("add `(hGT …) (hR …)` to the hypotheses of `esc_interface` … ≈ 10-30 lines"); audit A-177-1 D2 rules the opposite ("NOT an edit
  of RALedgers — the realiser replays `esc_` with an extended interface `esc_interface_ext`, exactly as D-RM-5 did for 176"). The
  executor's decision governs; the report's plan is superseded. «VERIFY at the outcome that RALedgers.lean is byte-unchanged
  since 18:11Z.»
- **Estimates for the R realisations differ:** the CV/R assembler (17:47Z) gave 39-60k lines (30-45k with a shared toolkit); D-RM-2
  (18:24Z) gave ≈ 35-42k for everything the four rows need, 20-24k for the toolkit incl. 177. Both were estimates before the
  constructor landed; the actual toolkit Wave 1 is 5 470 lines assembled (`Moves_Assembled.lean`) / 5 374 ported, "well under
  the estimate" (20:03Z), and the row-side drafts are 8 703 (174), 8 198 (176), 7 827 (177 Wave 3) lines.
- **Row 110 size:** D-CC-4 estimated 11-15k Lean lines for thm:C-S7; the lane produced ≈ 11.8k (CornerChainUnits, shared with
  103/105/112) + 3.0k (CS7Sliding) + the 9.0k draft with ≈ 8-12k still owed. The 2026-09-14 §7 lane-size remark (26.8k vs 39.9k)
  is unaffected.
- **Review identity string:** the map's `reviewer` for every 2026-09-15 row is `reviewer-pod-claude-fable-5-1-20260913 (…)`
  although the subagents were spawned on 2026-09-15 (each review's `ai_review_disclosure` and `review_utc` say so); the string is
  the workflow's standing identity, dated by its first use, not the review date. Likewise `author` `…-20260913`.
- **`work/delivery/tools/gen_final_review_tables.py`:** its abbreviation table (line 22) knows `H`, `LM`, `LMU`, `NG` only — `HD`
  (`SM.lit_homfly_descent`) and `SC` (`SM.src_contact`) must be added before the tables are regenerated, or the axioms column will
  print raw names; its `PENDING_REASONS` still carries the 2026-09-14 texts for the now-accepted rows 91 ("proved modulo one
  named clause … never mapped"), `src:contact` ("NEVER DECLARED"), 94, `hyp:R` ("NOT STATED"), 76-80/83/93 — unused for accepted
  rows but stale; the reasons for 110/127/128/174-178/183/184 must be replaced by §3's texts.
- **STATUS.md** stacks five "# STATUS" headers (14:00Z, 16:52Z, 17:52Z, 18:40Z, 22:40Z) above the 2026-09-14 text; the top block is
  current. Its 22:40Z line "row-177 Wave 3b … assembler 01:00Z" agrees with AUTHOR_NOTES 22:00Z (units 00:30Z, assembler 01:00Z);
  174/176 "01:15Z" agrees with 22:34Z/22:37Z (units 00:45Z).
- **`work/checks/stage-1.json`** is the 2026-09-14 18:06Z record (`{"passed": false, "stage": 1, "state": "checking"}`); no
  `--all` run happened on 2026-09-15. The closing `python3 tools/check_lean.py work/lean --all` will «PASS / FAIL naming the
  «PENDING-N» unaccepted rows»; expected at draft time: FAIL naming `lem:gauss-two-discs, thm:C-S7, thm:comparison,
  cor:C-inherits, SM:corner_laws_and_soft` and whichever of `R:generic_selected, R:extreme_transport, R:extreme_selected,
  R:cv_theorem, Bridge:theorem` remain.
- **Citation nits** recorded by the reviewers (documentation only): row 91's consumed descent sentence sm-3:3310-3312 (docstrings
  3313-3316), the hand isotopy-extension 3276-3312 (docstrings 3264-3313; `SM/LitHomflyDescent.lean` module docstring repeats
  3264-3313); field docstring ranges of `ContactPathData` off by one; `thm-C-soft` proof locator 992 vs 993; the brief pointer
  "341-343 (def:transverse-front)" should be 3328-3339; the conditional review's `source_sha256` fa17a1b1… is the sha of the whole
  `sm-3-statesum.tex`, not of the excerpt file (the excerpt is byte-identical to the source lines).
- **`blueprint/DEPENDENCIES.json` / `tools/claims.py` dependency column:** row 165 lists `cb:singleton` (103) as a dependency, but
  the CV row is proved from this lane's geo-layer split (`cvt_singleton_split`), not from row 103 (FR-CV-165-3); rows 127/128 no
  longer depend on 105 (`corner_values_i`, D-CM-5). As on 2026-09-14, the column is used only for `--next`.
- Numbering unchanged: claims.py "#" (184 units) ≠ map index (192 rows); `cp:finite-contact-path` is 91 in claims.py and 95 in
  the map (index 94 zero-based); `src:contact` is m97. The notes and this review use claims.py numbers.
- The 2026-09-14 §2 legend sentence "the four declared literature interfaces — nothing else appears" and §4.3's "Four of the five
  permitted interfaces are declared … `SM.src_contact` is not declared (§3.5)" are superseded by (D) and (F) above.
