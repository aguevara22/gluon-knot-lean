# ASSEMBLY_REPORT — cf:lem-curl (row 98), assembled file `Curl_Assembled.lean`

Assembler subagent, 2026-09-14 (08:14 UTC / 4:14 am ET). Directory: `work/drafts/curl/`. Nothing written under
`work/lean`; no `lake build`. Check command (the only one used): `cd work/lean && lake env lean ../drafts/curl/<file>.lean`.

**Result.** `Curl_Assembled.lean` (8353 lines, 451,692 bytes) = `Skeleton_FINAL.lean` with 52 of the 54 leaf `sorry`
bodies replaced by the units' proofs and the units' 628 helper declarations inserted; **0 errors**, 27.8 s;
`grep -c sorry` = **4** (2 leaf `sorry`s + the 2 prose mentions at lines 17/518 inherited from the skeleton);
**`#print axioms SM.cf_lem_curl` = `[propext, Classical.choice, Quot.sound, SM.lp_lm]`** — no `sorryAx`.
The two remaining `sorry`s are Unit G's `ξ_strictMonoOn` / `ξ_strictAntiOn` (lines 865, 868), which are **false as
stated** in a degenerate case (§3) and on which nothing in the file depends.

Inputs (sha256, first 16 hex): Skeleton_FINAL f3661df6a1362150 · Statements_FINAL 6ceead2c2bbb2361 · U_MF b4024dc537674d5d ·
U_G cd17b85fc8d7ded2 · U_HT f17fe745f55a00ca · U_R 7e105408f1b08fa6 · U_K1 b1b1dad7d7093722 · U_K2 f5d529d8ceb9bac9 ·
U_CA bd6f6b6772395641. Output: Curl_Assembled 117d5e885abcce88. Script: `assemble_curl.py` (this directory; a copy of
`/workspace/scratch/curl_assemble.py`), deterministic: `python3 assemble_curl.py` regenerates the file.

## 1. Diff of every unit against the skeleton (task 1) — no violation

Method: `difflib.SequenceMatcher` on line lists (same hunks as `diff`), every hunk classified.

| unit | hunks | `replace` hunks (each = exactly one `  sorry` line of one leaf of that unit) | `insert` hunks (helpers), skeleton position | lines added | non-`sorry` skeleton lines removed |
|---|---|---|---|---|---|
| U_MF | 11 | 11: hasDerivAt_cModel, hasDerivAt_bModel, cModel_double, fitA_add, fitA_smul, det_fitA_pos, fitA_ray_minus, fitA_ray_plus, yFit_bound, xFit_pos, orderedRay_condition | none | 53 | 0 |
| U_G | 19 | 17: det_vDir_u, planeDot_vDir_u, expansion, exists_chart, hasDerivAt_η, hasDerivAt_ξ, **ξ_strictMonoOn**, **ξ_strictAntiOn**, η_strictMonoOn, exists_cuts, cut_displacement, endpoint_tangent, exists_disc_in_chart, disc_isDisc, p_mem_interior_disc, tail_tangent_ne, exists_cutFit | before 633 (`det_vDir_u`), before 811 (`exists_cutFit`) | 457 | 0 |
| U_HT | 10 | 9: blend_smooth, blend_eq_left, blend_eq_right, sep_of_deriv, deriv_blend_ge, blend_between, deriv_blend_le, rot_shiftCurve, rot_sub_rot_of_window | before 714 (`blend_smooth`); the other five `ht_` helpers sit inside replace hunks (after a leaf body, before the next leaf) | 166 | 0 |
| U_R | 6 | 4: inserted_arc_props, exists_glued_arc, exists_loop_of_arc, exists_smoothCurl | before 755 (`inserted_arc_props`), before 819 (`exists_glued_arc`) | 1675 | 0 |
| U_K1 | 5 | 4: exists_kinkLocation, RIData.crossingPoint_ψ, RIData.sign_ψ, RIData.writhe_eq | before 894 (`exists_kinkLocation`) | 334 | 0 |
| U_K2 | 2 | 1: exists_kinkInsertion | before 899 (`exists_kinkInsertion`) | 4020 | 0 |
| U_CA | 9 | 8: cycBetween_ext_of_insert_pair, cycBetween_fract_gap, cycBetween_fract_pair, exists_carriedAssembly, deriv_eq_of_offWindow, doublePoints_diff_eq, one_neg_u_of, one_double_of | before 927 (`cycBetween_ext_of_insert_pair`) | 582 | 0 |

- Every removed line in every unit is a `  sorry` line (`diff Skeleton_FINAL.lean U_X.lean | grep '^<'` shows only
  `<   sorry`); every replaced leaf belongs to the unit that replaced it; the 54 leaves are covered exactly once.
  No statement, definition, structure, field, name, docstring or import was changed by any unit. Nothing to reject.
- U_G's two hunks for `ξ_strictMonoOn` / `ξ_strictAntiOn` are partial proofs with one residual `sorry` each
  (the degenerate branch). Per the rules they were **not adopted**; the skeleton's plain `  sorry` was kept.
- New declaration names per unit are all prefixed (`g_` 31, `ht_` 6, `r_` 57, `k1_` 20, `k2_` 471, `ca_` 45);
  **no name is declared by two units**; no unit re-declares a skeleton name. (The skeleton itself declares
  `smoothWrithe_eq`, `T`, `one` twice in different namespaces — inherited, compiles.)
- All eight insertion points lie in §7's single `namespace Curl` (`open Set`, `variable (S : CurlSite)` from
  line 631), so helper blocks share one context wherever they land.

## 2. Assembly (task 2)

`assemble_curl.py`: collects every non-`equal` hunk of every unit as an edit on skeleton line ranges, skips the two
residual-`sorry` hunks, sorts by skeleton position (inserts before replaces at equal positions), checks that no two
edits overlap (they do not: 52 single-line replaces on distinct `sorry` lines, 8 inserts at 8 distinct positions), and
splices. Verified afterwards: each of the 60 inserted blocks occurs contiguously in the output (`block in text`),
and `diff Skeleton_FINAL.lean Curl_Assembled.lean | grep '^<'` is exactly `52 × "<   sorry"`.

**De-duplication of identical helpers** (statement and proof byte-identical modulo the name; the kept copy precedes every
use of the dropped copy in file order; references renamed with an identifier-boundary regex, then compiled):
- `ca_deriv_eq_of_eqOn_Icc` (U_CA) dropped → `ht_deriv_eq_of_eqOn_Icc` (U_HT, sits at skeleton position 880, Unit T;
  CA's one use is at ≥ 927). Same statement, same proof (both reports flagged it).
- `r_planeDot_smul_left` (U_R) dropped → `g_planeDot_smul_left` (U_G, inside the `exists_chart` hunk, position 647;
  R's 14 uses are at ≥ 755). Alpha-equivalent statement (`b` vs `w`), same proof.
- `r_euclideanLength_add_le` ≡ `g_euclideanLength_add_le` — **kept both**: R uses it in its first helper block
  (position 755) *before* G's copy (position 811); the first assembly attempt de-duplicated it and failed with
  `Unknown identifier g_euclideanLength_add_le` at line 1364; reverted.
- Same-suffix pairs with different statements were left alone: `g_/r_hasDerivAt_planeDot`,
  `g_/r_strictMonoOn_of_deriv_pos` (G: `HasDerivAt` on `Ioo`; R: `Differentiable` + `deriv` on `Icc`),
  `ht_/ca_offWindow_of_mem_Icc` (`[s₂, s₁+1]` vs `[s₂−1, s₁]`), `k2_/ca_transverse`.
  CA's copies of the §8 lemmas (`ca_τ_offClosedWindow`, `ca_offWindow_of_offClosed`, `ca_F'_τ`, `ca_loop_fract`) stay
  (hoisting §8 text would alter the skeleton's order). Helper count in the assembled file: 628.
- **Rename on clash**: none needed (no cross-unit or work/lean clash, §6).

**One proof-text repair (the "small gap", task 3).** The first full compile gave `#print axioms SM.cf_lem_curl` *with*
`sorryAx`: Unit R's helper `r_glued_off` (used by `exists_glued_arc`, hence by `exists_smoothCurl` and the row) called
the two Unit-G leaves `ξ_strictMonoOn S hα hβ hθ` / `ξ_strictAntiOn S hα hβ hθ` as black boxes at four sites — legitimately,
since R was built on a skeleton copy where they were available, but those leaves are unprovable as stated (§3). In
`r_glued_off` the `CutFit` `cf` gives `α' ≤ s₁ < t₀ < s₂ ≤ β'`, i.e. the non-degenerate case, so the four calls were
redirected to Unit G's proved helpers, with `hθ` restricted:
```
ξ_strictMonoOn S hα hβ hθ  ↦  g_ξ_strictMonoOn S hα (fun t ht => hθ t ⟨ht.1, ht.2.trans (cf.lt_s₂.trans_le cf.le_β').le⟩)
ξ_strictAntiOn S hα hβ hθ  ↦  g_ξ_strictAntiOn S hβ (fun t ht => hθ t ⟨(cf.α'_le.trans_lt cf.s₁_lt).le.trans ht.1, ht.2⟩)
```
(assembled lines 2664, 2667, 2686, 2691; scripted in `assemble_curl.py`). Statements untouched; only these four proof
lines differ from `U_R.lean`. After this, no declaration outside the two leaves themselves uses `sorry`.

## 3. Unproved leaves (task 3) — exactly two, both FALSE as stated

`SM.Curl.ξ_strictMonoOn {α' β'} (hα : S.α ≤ α') (hβ : β' ≤ S.β) (hθ : ∀ t ∈ Icc α' β', |θrel S t| < π/2) : StrictMonoOn (ξ S) (Icc α' S.t₀)`
`SM.Curl.ξ_strictAntiOn … : StrictAntiOn (ξ S) (Icc S.t₀ β')` (assembled lines 862-868; skeleton 659-664).

- Unit G proved both for `α' ≤ β'` and for the one-point interval; the residual case `β' < α' < t₀` (resp.
  `t₀ < β' < α'`) makes `hθ` vacuous and the conclusion can fail. Counterexample (U_G_REPORT.md, numerically probed,
  checked here by hand): unit circle `F(t) = (cos 2πt, sin 2πt)` with a crossing-free diagram, `t₀ = 0`, `u = (0,1)`,
  `v = (1,0)`, `θ(t) = 2πt + π/2`, `[α, β] = [−0.7, 0.1]` (all `CurlSite` hypotheses hold); `ξ(t) = cos 2πt − 1`,
  `ξ(−0.7) = −1.309 > ξ(−0.5) = −2`, so `ξ` is not strictly monotone on `[α', t₀] = [−0.7, 0]`, while `β' = −0.8 < α'`
  satisfies `hα`, `hβ`, `hθ` (vacuous). Not kernel-checked (would need a `SmoothRegularLoop`/`RecordCarried` instance
  for the circle); not attempted within the 30-minute budget since the leaf is not provable anyway.
- The statements were **not changed** (frozen). They stay `sorry`, and after §2's repair **nothing depends on them**:
  `#print axioms` of all 52 other leaves, of `SM.Curl.curlWitness`, `SM.exists_curl_main`, `SM.CurlData`,
  `SM.cf_lem_curl` show no `sorryAx` (per-leaf prints from the /tmp copy, §4).
- Recommendation for the executor at porting time (work/lean admits no `sorry`): either add the hypothesis
  `(hab : α' ≤ β')` to both leaves — then the first branch of U_G's bodies (`g_ξ_strictMonoOn`/`g_ξ_strictAntiOn`, lines
  825-858 of U_G.lean) proves them — or delete the two leaves, which no consumer uses. Record either as an AUTHOR_NOTES
  entry (chain repair, FR-C8 style). Neither is a target-row statement.

## 4. Compile, sorry count, axioms (task 4)

- `cd work/lean && lake env lean ../drafts/curl/Curl_Assembled.lean`: exit 0, **0 errors**, 27.8 s wall (1m35 user),
  log `/workspace/scratch/curl_assembled_compile.log`. Warnings: 2 × `declaration uses sorry` (lines 865, 868), the
  inherited `<;>` linter note at line 588 (`cModel_one`) plus one more in a unit proof, `dif_pos`/`dif_neg` deprecations
  (U_K2, 2), unused-variable notes (`hlam` ×3, `hα'`, `hβ'`, `hr` — from frozen statements of `exists_glued_arc` etc. —
  `hη`, `hs`, `hpos`, `hneg`, 10 hints). No `sorry`-unrelated error or unknown identifier.
- `grep -c sorry Curl_Assembled.lean` = **4**: lines 865, 868 (the two leaves) and the prose mentions at 17, 518.
- The skeleton's own trailing `#print axioms` (kept at the end of the assembled file) print in the official log:
  `'SM.cf_lem_curl' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lp_lm]`,
  `'SM.CurlData' … [propext, Classical.choice, Quot.sound, SM.lp_lm]`, `'SM.Carried.toRecordCarried' … [propext, Classical.choice, Quot.sound]`.
- /tmp copy `/tmp/Curl_Assembled_axioms.lean` (assembled file + `#print axioms` for the row, `CurlData`, `curlWitness`
  and all 54 leaves + a constant dump; log `/workspace/scratch/curl_axioms_compile.log`): 52 leaves =
  `[propext, Classical.choice, Quot.sound]`; `ξ_strictMonoOn`, `ξ_strictAntiOn` = the same + `sorryAx`;
  `SM.Curl.curlWitness`, `SM.cf_lem_curl` = `[propext, Classical.choice, Quot.sound, SM.lp_lm]`. (The one error in that
  log is my appendix's misspelt `#print axioms SM.Curl.exists_curl_main` — the theorem is `SM.exists_curl_main`; not part
  of the assembled file.)

## 5. Byte-identity with Statements_FINAL.lean (task 5)

Paragraph check (blank-line-separated blocks containing a declaration, 27 of them, docstrings included): **26 occur
verbatim** in `Curl_Assembled.lean` (`RecordCarried` + its 4 lemmas, `Carried.toRecordCarried`, `CurlSite` + `p`, `T`,
`ofCarried`, `CurlWitness` + `doublePoints_eq`, `smoothWrithe_eq`, `CurlData`, …). The 27th is the row itself:
`theorem cf_lem_curl : CurlData` — the head is identical; Statements has docstring `/-- cf:lem-curl. -/` and body
`:= by sorry`, the skeleton (and hence the assembly) has the judge's docstring `/-- cf:lem-curl, assembled from the
chain; … -/` and the proved `where` instance. This difference is the skeleton's, not the assembly's (Skeleton_FINAL was
the frozen input; the row's name and type are what the checker reads). Line-level check: every non-blank line of
Statements_FINAL.lean from `namespace SM` on occurs in order in the assembled file except those two row lines.

## 6. Name-clash scan against work/lean (task 6)

Lean-based, not textual: (a) the /tmp copy dumped the assembled file's constants (`env.constants.map₂`, internal names
filtered): **989**; (b) `/tmp/curl_lib_dump.lean` imported all **644** project modules with oleans (`SM.*` 610, `CV.*`,
`RProof.*`, `Bridge.*`, `Supplemental*`; 6501 modules with Mathlib) and dumped the **15,510** non-Mathlib constants.
Intersection of fully-qualified names: **0** (`clashes = []`). No `work/lean/SM/Curl.lean` exists and no module declares
anything under `SM.Curl`, `SM.CurlSite`, `SM.CurlWitness`, `SM.CurlData`, `SM.RecordCarried`, `SM.cf_lem_curl` or
`SM.Link.RIData.{crossingPoint_ψ, sign_ψ, writhe_eq}`. Same-last-component overlaps in other namespaces (e.g.
`SM.Curl.vDir` vs `SM.CornerRounding.vDir`, `SM.CurlWitness.writhe_eq` vs `SM.Link.RecordIso.writhe_eq`, structure
boilerplate `mk/rec/casesOn/…`) are not clashes and cause no ambiguity in the file's `open` state.

## 7. Notes for the port to `SM/Curl.lean`

- Imports `SM.Rounding`, `SM.LinkMoves`, `SM.PolynomialBlock` (the latter brings `SM.Smoothing`, which U_K2 uses).
  Mathlib's MeanValue file is not in the closure; the units derive the slope MVT from Rolle (`g_`, `ht_`, `r_` copies).
- The four repaired lines of §2 exceed 100 characters; wrap when porting.
- Remove the two false leaves or add `hab : α' ≤ β'` (§3) before porting: work/lean admits no `sorry`.
- Drop the three trailing `#print axioms` and the "(all `sorry`)" wording of the §7 header when porting.
