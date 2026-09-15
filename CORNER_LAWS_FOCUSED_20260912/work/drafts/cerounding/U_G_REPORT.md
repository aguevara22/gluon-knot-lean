# U-G report — germ / chart / rectangle (ce:rounding, row 89)

Unit G of PLAN_FINAL.md §4, worked 2026-09-14 on the pod.  File: `work/drafts/cerounding/U_G.lean`
(a byte-identical copy of `Skeleton_FINAL.lean` before this unit; statements untouched).
Check: `cd work/lean && lake env lean ../drafts/cerounding/U_G.lean` — exit 0, 0 errors (~8 s on the
pod), the only warnings are the pre-existing ones (other units' `sorry`, the two unused simp
arguments of `chart_add_disp`, the five `letI` style hints).  `grep -c sorry`: 37 before → 27 after
(10 leaf bodies removed; the 4 mentions in the header comment and the 23 leaves of U-P/U-C/U-L/U-E
remain).  `diff Skeleton_FINAL.lean U_G.lean`: exactly ten `  sorry` lines replaced and one inserted
block (the two helpers below); nothing else differs.

## Leaves proved (10 / 10) — all with axioms `[propext, Classical.choice, Quot.sound]` (no `sorryAx`)

| leaf | U_G.lean | how |
|---|---|---|
| `SpatialLink.exists_germData` | 260-266 | destructure `ExactCuspGerm`, shrink `δ` to `min δ (1/3)`, `Set.Ioo_subset_Ioo`, anonymous constructor |
| `GermData.chart_proj` | 316-330 | components of `g.formula t ht` by `congrArg`; `ext`, `simp only [chart, xzOf, xOf, zOf, u, x₀, y₀, z₀]`, `rw` the two components, `field_simp; ring` |
| `GermData.u_strictMonoOn_or_strictAntiOn` | 374-402 | `deriv g.u = deriv (yOf …)` (`deriv_sub_const`), `≠ 0` on `J`; continuity of `deriv g.u` (`ContDiff.continuous_deriv`); IVT `IsPreconnected.intermediate_value` on `isPreconnected_Ioo` shows the derivative cannot take both signs; then the two helpers below |
| `GermData.rect_subset_closedBall` | 440-457 | `mem_closedBall_zero_iff`, `Prod.norm_def`, `Real.norm_eq_abs`; `|uMin³|, |uMax³| ≤ M³` via `abs_pow`, `pow_le_pow_left₀`; `max_le`, `abs_le`; no hypothesis on `η` needed, as planned |
| `GermData.uMin_neg` | 459-470 | `u t₀ = 0`, `t₀ ± η ∈ J`, the dichotomy; `min_le_left/right` |
| `GermData.uMax_pos` | 472-482 | same with `le_max_left/right` |
| `GermData.u_mem_Icc_of_mem` | 487-497 | `StrictMonoOn.monotoneOn` / `StrictAntiOn.antitoneOn` on the ends, in both cases |
| `GermData.mem_Icc_of_u_mem` | 500-528 | both cases: increasing `uMin = u(t₀−η)`, `uMax = u(t₀+η)` (`min_eq_left`, `max_eq_right`); decreasing `uMin = u(t₀+η)`, `uMax = u(t₀−η)`; a parameter outside `[t₀−η, t₀+η]` but in `J` has `u` strictly outside `[uMin, uMax]` — contradiction (`by_contra`, `push Not`, `not_le`) |
| `GermData.u_mem_Ioo_of_mem` | 531-540 | strict version of `u_mem_Icc_of_mem` |
| `GermData.abs_u_le_M` | 542-545 | `u_mem_Icc_of_mem` + `abs_le_max_abs_abs` (`g.M η` unfolds by defeq) |

CE-R10 probe (`mem_Icc_of_u_mem` with `u` decreasing): TRUE as stated — `uMin`/`uMax` are the
`min`/`max` of the two end values, so the decreasing case only swaps which end realises which; both
cases are proved.  No leaf of this unit is false or needs a stronger hypothesis.

## Helpers added (inside `namespace SpatialLink.GermData`, U_G.lean 340-373, immediately before
`u_strictMonoOn_or_strictAntiOn`)

```lean
theorem ug_strictMonoOn_of_deriv_pos {f : ℝ → ℝ} {a b : ℝ} (hf : Differentiable ℝ f)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < deriv f x) : StrictMonoOn f (Set.Ioo a b)
theorem ug_strictAntiOn_of_deriv_neg {f : ℝ → ℝ} {a b : ℝ} (hf : Differentiable ℝ f)
    (hneg : ∀ x ∈ Set.Ioo a b, deriv f x < 0) : StrictAntiOn f (Set.Ioo a b)
```
Why: Mathlib's `strictMonoOn_of_deriv_pos` / `strictAntiOn_of_deriv_neg` (and `exists_deriv_eq_slope`,
`exists_hasDerivAt_eq_slope`, `Convex.image_sub_lt_mul_sub_of_deriv_lt`) live in
`Mathlib.Analysis.Calculus.Deriv.MeanValue`, which is NOT in the import closure of
`SM.CeSmoothingRecord` + `SM.Rounding` + `Mathlib.Analysis.SpecialFunctions.SmoothTransition`
(checked with `#check`).  Rolle (`exists_deriv_eq_zero`) IS available, so the helper is Rolle applied
to the chord difference `f t − f x − m (t − x)` (the same technique as `r_strictMonoOn_of_deriv_pos`
in SM/Curl.lean, which is also outside this file's import closure); the antitone version applies the
monotone one to `-f` (`Differentiable.neg`, `deriv.neg`).  Full names:
`SM.SpatialLink.GermData.ug_strictMonoOn_of_deriv_pos`, `…ug_strictAntiOn_of_deriv_neg`.  The
assembler should NOT add `import Mathlib.Analysis.Calculus.Deriv.MeanValue` on my account; if
another unit adds it, the helpers keep working (distinct names).

## Mathlib / toolchain pitfalls met (v4.34.0-rc2 pin)

- `ContDiff.differentiable` now takes `n ≠ 0` (not `1 ≤ n`): `g.u_smooth.differentiable (by simp)`;
  `ContDiff.continuous_deriv` still takes `1 ≤ n`: `(by exact_mod_cast le_top)` (as SM/FrontSmooth.lean:185).
- `deriv.neg` is stated for `-f` (`Pi.neg`), not for `fun t => -f t`; instantiate with `(f := -f)`.
- `push_neg` is deprecated in this toolchain (warning) — use `push Not` (the skeleton already does).
- A structure instance `{ A := …, δ := …, … }` split over continuation lines inside `⟨ ⟩` failed to
  parse ("expected '}'", fields on a less-indented line); the anonymous constructor
  `⟨⟨A, min δ (1/3), hA, …⟩⟩` in field order is robust.
- `p ∈ s ×ˢ t` destructures directly: `obtain ⟨⟨h1l, h1u⟩, ⟨h2l, h2u⟩⟩ := hp`.
- `lt_or_gt_of_ne : a ≠ b → a < b ∨ b < a`; `abs_le_max_abs_abs : a ≤ b → b ≤ c → |b| ≤ max |a| |c|`;
  `pow_le_pow_left₀ (ha : 0 ≤ a) (hab : a ≤ b) (n)`; `IsPreconnected.intermediate_value ha hb hf :
  Icc (f a) (f b) ⊆ f '' s` — all available.
- Membership in `g.J` (a `def` for `Set.Ioo`) is built with `⟨by linarith, by linarith⟩`, as the
  skeleton's `t₀_mem_J` does; `g.uMin η = …` from `min_eq_left` and `StrictMonoOn g.u g.J` from the
  helper on `Set.Ioo` both go through by defeq (no `unfold` needed).

## For the assembler / executor

- Nothing outside the ten leaf bodies and the inserted 34-line helper block was touched; no import,
  statement, name or docstring changed.  The file compiles standalone; merge = take lines 262-266,
  318-330, 340-402, 441-457, 461-470, 473-482, 490-497, 502-528, 533-540, 544-545 of U_G.lean.
- The downstream leaves that cite this unit (`clean`, `arc_injOn`, `arc_no_crossing`, `inside`,
  `chart_core`, `exists_eta`) get exactly the statements they were promised; in particular
  `mem_Icc_of_u_mem` needs `t ∈ g.J` (as stated) and `rect_subset_closedBall` has no hypothesis.
- Scratch used: `/tmp/UG_scratch.lean` (lines 1-397 of the skeleton + closings, ~10 s per iteration).
