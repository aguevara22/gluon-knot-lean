# RPC_ASSEMBLY_REPORT.md — assembly of `SM.regularPoleCount` (fd:regular-pole-count)

Written 2026-09-14 10:13 UTC / 6:13am ET by the RegularPoleCount assembler agent.
Output: `work/drafts/fd/RPC_Assembled.lean` (1297 lines, sha256 `39a7fb08ee85dc2d5588da31a5f6fc3f8168f460d74e2402535975d0f5e2730a`).
Scripts (kept for reproducibility): `work/drafts/fd/RPC_assemble.py` (assembly + freeze/contiguity checks),
`work/drafts/fd/RPC_clash_scan.py` (namespace-aware name-clash scan).  Nothing under `work/lean` was written.

## Result in one line

**0 `sorry`, 0 errors, 0 unproved leaves, 0 name clashes.**  `SM.regularPoleCount : RegularPoleCount` and
`SM.crossing_formula_unconditional` depend on `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`.

## 1. Statement-freeze verification (task item 1)

For each unit file `diff RPC_Skeleton.lean RPC_U_<u>.lean` was parsed hunk by hunk (`RPC_assemble.py`):

| unit | hunks | skeleton lines removed | all removed lines are `  sorry` | helpers added | other changes |
|---|---|---|---|---|---|
| A | 11 (`163c`, `173c`, `179c`, `196c`, `204c`, `211c`, `220c`, `240c`, `265c`, `282c`, `294c`) | 11 | yes | 1 (`ua_integral_integral_swap`, placed after A4) | none |
| B | 9 (`300a` + `305c`, `312c`, `325c`, `333c`, `344c`, `358c`, `366c`, `400c`) | 8 | yes | 6 (`ub_exists_unit_orth`, `ub_contDiff_chart`, `ub_approximates_deriv_on_nhds`, `ub_exists_sign_nhd`, `ub_chart_eq_zero`, `ub_exists_pos_le`) | none |
| C | 6 (`412c`, `421c`, `429c`, `446c`, `453c`, `463c`) | 6 | yes | 6 (`uc_abs_eq_sign_mul`, `uc_sign_mul_sign`, `uc_chartDensity_polar`, `uc_contDiff_bumpPhi`, `uc_hasDerivAt_bumpPhi`, `uc_hasDerivAt_radial`) | none |
| D | 4 (`484c`, `496c`, `513c`, `528c`) | 4 | yes | 3 (`ud_shift_mem`, `ud_shift_inj`, `ud_shift_coord`) | none |

* Every removed line is exactly `  sorry` (29 in total = all leaves of the skeleton); no `theorem`/`def`/
  `structure` header, docstring, `import`, `open`, or `namespace` line differs from the skeleton in any unit.
* Each unit's hunks lie inside that unit's `section U<u>` (A: skeleton lines 163–294, B: 300–400, C: 412–463,
  D: 484–528); hunks of different units touch disjoint skeleton lines (checked by the script).
* The added lines of every hunk were cross-checked against the unit file's own text (byte-identical).
* **No violations found; nothing was rejected.**

## 2. Assembly (task item 2)

`RPC_assemble.py` applies all 30 hunks to the skeleton in one pass (`NcM,K` → replace the single skeleton
line `N` (a `  sorry`) by unit lines `M..K`; `NaM,K` → insert unit lines `M..K` after skeleton line `N`).
Checks performed after writing the file:
* **contiguity**: every one of the 30 added blocks occurs in `RPC_Assembled.lean` exactly once and contiguously
  (re-verified after the docstring rewrite, §6);
* **reverse diffs**: `diff RPC_U_<u>.lean RPC_Assembled.lean` removes only that unit's other-unit `  sorry`
  lines (A 18, B 21, C 23, D 25) plus the 6 rewritten module-docstring lines — nothing else;
* **helpers**: the 16 helper names are pairwise distinct and prefixed by unit (`ua_`/`ub_`/`uc_`/`ud_`);
  no identical helper appears in two units, so no de-duplication and no renaming was needed.
  (Units A, C, D each prove `ContDiff ℝ ∞ (bumpPhi χ)` inline as a local `have`; only U-C exposes it as the
  top-level `uc_contDiff_bumpPhi`.  Left as is: local `have`s are not declarations.)

Helper declarations (all in `SM.RPC`):

| helper | line | unit |
|---|---|---|
| `ua_integral_integral_swap` | 244 | U-A |
| `ub_exists_unit_orth` | 515 | U-B |
| `ub_contDiff_chart` | 601 | U-B |
| `ub_approximates_deriv_on_nhds` | 624 | U-B |
| `ub_exists_sign_nhd` | 634 | U-B |
| `ub_chart_eq_zero` | 643 | U-B |
| `ub_exists_pos_le` | 690 | U-B |
| `uc_abs_eq_sign_mul` | 870 | U-C |
| `uc_sign_mul_sign` | 877 | U-C |
| `uc_chartDensity_polar` | 922 | U-C |
| `uc_contDiff_bumpPhi` | 949 | U-C |
| `uc_hasDerivAt_bumpPhi` | 954 | U-C |
| `uc_hasDerivAt_radial` | 959 | U-C |
| `ud_shift_mem` | 1129 | U-D |
| `ud_shift_inj` | 1138 | U-D |
| `ud_shift_coord` | 1144 | U-D |

## 3. Unproved leaves (task item 3)

**None.**  All 29 leaves are proved with the frozen statements:

| leaf | declaration (`SM.RPC.*`) | header line in `RPC_Assembled.lean` | lines (header + proof) |
|---|---|---|---|
| A1 | `cross_fderiv_eq_smul` | 172 | 12 |
| A2 | `fderiv_oneForm_apply` | 187 | 23 |
| A3 | `contDiff_oneForm` | 213 | 6 |
| A4 | `fderiv_oneForm_antisymm` | 230 | 11 |
| A5 | `integral_fderiv_eu_eq_zero` | 259 | 18 |
| A6 | `integral_fderiv_ev_eq_zero` | 280 | 15 |
| A7 | `integral_triple_mul_mk_eq_zero` | 298 | 34 |
| A8 | `contDiff_cutoffK` | 350 | 15 |
| A9 | `mk_cutoffK_one` | 387 | 9 |
| A10 | `gaussIntegral_eq_shift` | 407 | 25 |
| A11 | `gaussIntegral_eq_integral_bump` | 437 | 70 |
| B1 | `exists_frame` | 542 | 9 |
| B2 | `frame_parseval` | 554 | 14 |
| B4 | `det_eq_fin_two` | 578 | 7 |
| B5 | `det_chartDeriv` | 589 | 10 |
| B6 | `exists_strict_equiv_chart` | 609 | 11 |
| B7 | `exists_regular_nhd` | 653 | 35 |
| B8 | `exists_disjoint_balls` | 699 | 25 |
| B9 | `exists_nhdSystem` | 750 | 55 |
| C1 | `deriv_bumpPhi_eq_zero_of_lt` | 814 | 11 |
| C2 | `chartDensity_chart` | 829 | 13 |
| C3 | `chartDensity_mem_ball` | 846 | 22 |
| C4 | `integral_bump_on_nhd` | 885 | 34 |
| C5 | `integral_chartDensity_eq_radial` | 932 | 15 |
| C6 | `integral_radial` | 979 | 60 |
| D1 | `integral_box_eq_setIntegral` | 1056 | 10 |
| D2 | `setIntegral_box_eq_sum` | 1071 | 13 |
| D3 | `integral_bump_eq_sum_of_system` | 1091 | 35 |
| D4 | `exists_shift` | 1162 | 87 |

## 4. Compile, `sorry` count, axioms (task item 4)

* `cd work/lean && lake env lean ../drafts/fd/RPC_Assembled.lean` → exit 0, **0 errors**, 7.5 s.
  One warning: `751:78 Variable name \`hP\` is not explicitly referenced` — the hypothesis `hP : 0 < P` in the
  frozen statement of `exists_nhdSystem` (B9) is not needed by the proof.  The statement was inherited from the
  skeleton and left unchanged (the top-level `regularPoleCount` passes `hP` to it).  Harmless; the checker
  rejects axioms, not linter warnings.
* `grep -c sorry work/drafts/fd/RPC_Assembled.lean` → **0** (also case-insensitive).
* `#print axioms` on a `/tmp` copy of the final file (`/tmp/rpc_axioms/RPC_Final_Axioms.lean`):
  * `'SM.regularPoleCount' depends on axioms: [propext, Classical.choice, Quot.sound]`
  * `'SM.crossing_formula_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]`
  * additionally all 70 top-level declarations of the file were printed (`/tmp/rpc_axioms/RPC_Axioms.lean`,
    log `/workspace/scratch/rpc_asm/axioms.log`): every one is `[propext, Classical.choice, Quot.sound]`;
    no `sorryAx` anywhere.

## 5. Name-clash scan (task item 5)

`RPC_clash_scan.py` indexes every non-private top-level declaration of the 652 `.lean` files under `work/lean`
(13,648 declarations), tracking `namespace`/`section`/`end` so that each name is fully qualified, and compares
against the 70 fully-qualified names of `RPC_Assembled.lean` (68 in `SM.RPC`, plus `SM.regularPoleCount`,
`SM.crossing_formula_unconditional`).
* exact fully-qualified clashes: **0**;
* short-name shadows in an enclosing namespace (`SM.<x>` or root `<x>` for an `SM.RPC.<x>`, which would make
  references inside `SM.RPC` ambiguous once co-imported): **0**;
* pre-existing `SM.RPC.*` declarations in `work/lean`: **0** (the namespace is new);
* informational only: `SM.SpatialLink.GermData.chart` shares the short name `chart` with `SM.RPC.chart` in an
  unrelated namespace — not an enclosing one, so no ambiguity.
* Sanity check of the index: `SM.RegularPoleCount` (LinkingCalculus.lean:526),
  `SM.crossing_formula_of_regularPoleCount` (:1954), `SM.gaussIntegral` (:373), `SM.gaussDensity` (:368),
  `SM.LinkingCalculus.Family.triple` (:963) are all found; `SM.regularPoleCount`,
  `SM.crossing_formula_unconditional`, `SM.RPC.eu2` are absent, as expected.
* Row `fd:linking-calculus` has no fixed target declaration name in `axiom-policy.json` (checked
  `lean-declarations.json`: status pending, declaration empty), so the skeleton's names stand.

## 6. Docstring and `#`-commands (task item 6)

The `sorry` count is 0, so the module docstring (lines 1–35) was rewritten: it now describes the assembled,
completely proved file (route, structure, the four sections, the meaning of the inherited `-- LEAF` markers and
`(PROVED)` tags, helper prefixes, axiom footprint).  The word `sorry` appears nowhere in the file; there are no
`#print`, `#eval` or `#check` lines (there were none in the skeleton either).  Everything below the docstring is
exactly the skeleton plus the units' hunks.

## 7. Notes for the lead

* The file is ready to be promoted to a module (suggested `work/lean/SM/RegularPoleCount.lean`, keeping
  `import SM.LinkingCalculus` and the three extra Mathlib imports); the assembler did not touch `work/lean`
  and did not run `lake build`, per instructions.
* `crossing_formula_unconditional` is stated with `∑ᶠ p ∈ mixedCrossings P C₁ C₂ ν, lcCrossingSign C₁ C₂ ν p`
  exactly as in the skeleton, via `crossing_formula_of_regularPoleCount regularPoleCount h hν`.
* Unit-file idiosyncrasies preserved verbatim: U-C's `integral_chartDensity_eq_radial` does not need
  `hχ : χ.rOut < 1` and consumes it with `have _ := hχ` (frozen statement); U-B's B9 has the unused `hP`
  (warning above).
