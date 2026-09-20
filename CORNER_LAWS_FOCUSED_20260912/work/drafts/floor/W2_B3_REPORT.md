# Unit U-B3 report (wave 2, 2026-09-15) — leaf `ub_tangencyCount_of_admissible`

File: `work/drafts/floor/W2_B3.lean` (= `Wave2_Skeleton.lean` + this unit's hunk).  Helper prefix `ub3_`.

## 1. Result

| item | value |
|---|---|
| leaf proved | `ub_tangencyCount_of_admissible` (W2_B3.lean l.1063; skeleton l.962) — statement byte-identical, only the `sorry` body replaced |
| helpers added (5, all `ub3_`, inserted immediately before the leaf's docstring, same section) | `ub3_dirOf_add_pi` (l.960), `ub3_dirOf_add_int_mul_pi` (l.967), `ub3_levels_of_admissible` (l.980), `ub3_arc_of_admissible` (l.1000), `ub3_rotationNumber_pos` (l.1038) |
| compile | `cd work/lean && lake env lean ../drafts/floor/W2_B3.lean`: **exit 0, 0 errors**, 15 s.  Warnings: 3 × `declaration uses 'sorry'` (other units: `ui_mirrorSubstitution` l.1838, `ulift_exists_transverse_lift` l.3048, `cf_thm_carrierfloor_C_of_bound` l.3062) + the 2 frozen unused-binder warnings (`hturn` l.608, `hu` l.2332) already present in the skeleton |
| `grep -c sorry` | skeleton **6** (4 leaf bodies + 2 docstring mentions) → W2_B3.lean **5** (3 leaf bodies + 2 mentions) |
| diff vs skeleton | `diff Wave2_Skeleton.lean W2_B3.lean \| grep '^<'` = exactly one line, `  sorry`; added lines contain no `sorry/admit/native_decide/axiom/set_option/@[simp]/attribute` |
| statement identity | `tools/wave1_stmt_check.py` re-pointed at (Wave2_Skeleton.lean, W2_B3.lean): declarations checked: 242; byte-identical statements found: 242; mismatches: 0 |
| axioms (scratch copy + `#print axioms`) | `SM.ub_tangencyCount_of_admissible`, `SM.ub_BClaim`, `SM.cf_thm_carrierfloor_B`, and all five `ub3_` helpers: `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**; clause (B) of row 99 is now fully proved |
| name clashes | the 5 new names grepped whole-word over `work/lean/**/*.lean`: 0 hits |
| nothing under `work/lean` touched; no `lake build` | yes |

## 2. Proof route (as PLAN_FINAL.md §3 (B) U-B3 / WAVE1_ASSEMBLY_REPORT.md §5)

Leaf hypotheses: `hturn : ∀ i, principalTurn C.P i ≠ 0`, `hpos : AllPosOrOneNeg C.P`, `hu : AdmissibleDirection C u`,
`h : Admissible C D ε`.  Goal: `TangencyCount (Round C D ε h) u |rot| ∧ TangencyCount (Round C D ε h) (-u) |rot|`.

1. **Argument of `u`.**  `φ := (planeComplex u).arg`; `dirOf φ = u` from the accepted polar form
   `CornerRounding.G1_smul_dirOf_arg u` (Rounding.lean:1165) with `hu.1 : euclideanLength u = 1` and `one_smul`.
   `dirOf (φ + π) = −u` by `ub3_dirOf_add_pi` (`Real.cos_add_pi`, `Real.sin_add_pi`, `rfl` on the pair).
2. **`rot > 0`** (`ub3_rotationNumber_pos`): `principalTurn_sign D.regular` (UniformRotation.lean:12) turns `hturn` into
   `∀ i, SM.turn C.P i ≠ 0` (`sign_eq_zero_iff`) and `hpos` into the sign pattern all-`1` (`sign_pos`) or one-`−1`-rest-`1`
   (`sign_neg`/`sign_pos`); `uniform_rotation C.hk C.P D.regular` (UniformRotation.lean:64) clause (i) resp. (iii) gives
   `1 ≤ rot`.  Hence `|rot| = rot` (`abs_of_pos`).
3. **Both hypotheses of `ub_levelCount` for every `ψ` with `dirOf ψ = ±u`** — used at `ψ = φ` and `ψ = φ + π`:
   - `ub3_dirOf_add_int_mul_pi`: `dirOf (ψ + nπ) = dirOf ψ` (`n` even) or `= −dirOf ψ` (`n` odd), via
     `Int.even_or_odd` and `ub2_dirOf_eq_iff` (the U-B2 helper, angles mod `2π`).
   - `ub3_levels_of_admissible` (`hφ`): `θu C j = ψ + nπ` would give `dirOf (θu C j) = ±dirOf ψ = ±u`; but
     `dirOf (θu C j) = uDir C ↑j = normalize (edge C.P (↑j − 1))` (`dirOf_θu D.regular`, Rounding.lean:1207, `rfl`
     on `uDir`), against the edge clause `hu.2.1 (↑j − 1)` — four sign cases, `neg_neg` for the `−(−u)` one.
   - `ub3_arc_of_admissible` (`harc`): for `turn C j < 0` and `x := ψ + nπ ∈ [θu j + ϑ_j, θu j]`, the profile
     parameter `s := (x − θu j)/ϑ_j ∈ [0,1]` (`div_nonneg_of_nonpos`, `div_le_one_of_neg`) satisfies
     `θu j + s ϑ_j = x` (`div_mul_cancel₀`); `dirOf (arg (uDir C ↑j)) = dirOf (θu C j)` (`ua_dirOf_arg_uDir` +
     `dirOf_θu`) shifts by `2πm` (`ub2_dirOf_eq_iff`), so `dirOf (arg (uDir ↑j) + s · principalTurn C.P ↑j) = dirOf x
     = ±u`, against the arc clause `hu.2.2 ↑j` (`principalTurn C.P ↑j = turn C j` is `rfl`).
4. **Assemble.**  `ub_levelCount C D ε h φ …` gives `TangencyCount (Round …) (dirOf φ) rot`, rewritten by `dirOf φ = u`;
   `ub_levelCount C D ε h (φ + π) …` gives the `−u` half by `dirOf (φ + π) = −u`.  `ub_globalLift` is not needed
   separately (it is already inside `ub_levelCount`).

Wave-1 helpers consumed: `ub2_dirOf_eq_iff`, `ua_dirOf_arg_uDir`, `ub_levelCount` (leaf, proved).  Accepted library:
`G1_smul_dirOf_arg`, `dirOf_θu`, `PolygonDiagram.regular`, `principalTurn_sign`, `uniform_rotation`, `rotationNumber`
(RotationNumber.lean:10), `PolyComp.hk`; Mathlib: `Int.even_or_odd`, `sign_pos/sign_neg/sign_eq_zero_iff`,
`div_nonneg_of_nonpos`, `div_le_one_of_neg`, `div_mul_cancel₀`, `abs_of_pos`, `Real.cos_add_pi/sin_add_pi`.

## 3. Fidelity notes

- The leaf is TRUE as frozen; no hypothesis is missing.  `hturn` is used only through `uniform_rotation`'s `hτ`;
  `hpos` only for `rot ≥ 1` (the printed "after the normalisation, rot ≥ 1", sm-3:4368-4370 / lem:uniformrot).
- `ub_levelCount` already carries the positive-derivative clause (FR-FL-B3) and the finiteness/`ncard` form (FR-FL-B2); this
  unit only supplies its two angle hypotheses from `AdmissibleDirection` and the `φ ↦ φ + π` shift (the forbidden set is
  `π`-periodic because `n` ranges over `ℤ`, PLAN §3 (B) U-B3).
- `ub_exists_admissibleDirection` (the unit's other leaf) was already proved by the assembler (wave 1, §4); untouched.
- Other units' leaves (`ui_mirrorSubstitution`, `ulift_exists_transverse_lift`, `cf_thm_carrierfloor_C_of_bound`) untouched.

## 4. Scratch (scratchpad, not part of the deliverable)

`ub3_scratch.lean` (imports + local copies of the frozen definitions, `ub_levelCount` black-boxed as `sorry`, the five
helpers and the leaf; compiles in 9 s), `W2_B3_compile.log`, `W2_B3_axioms.lean/.log` (`#print axioms`),
`w2b3_stmt_check.py`.
