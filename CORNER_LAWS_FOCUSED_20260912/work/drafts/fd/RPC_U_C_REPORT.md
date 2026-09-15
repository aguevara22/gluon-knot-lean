# RPC_U_C_REPORT.md — unit U-C (change of variables on one neighbourhood; polar normalisation)

File: `work/drafts/fd/RPC_U_C.lean` (copy of `RPC_Skeleton.lean` with the six U-C leaves proved).
Written 2026-09-14.  Compile: `cd work/lean && lake env lean ../drafts/fd/RPC_U_C.lean` → **0 errors**,
23 `declaration uses sorry` warnings (exactly the 23 leaves of units A, B, D; no other warnings).
`grep -c sorry`: 29 before → 23 after.  `diff RPC_Skeleton.lean RPC_U_C.lean` removes only the six
lines `  sorry`; every definition, statement, name and docstring is byte-identical to the skeleton.

## Leaves proved (6/6)

| leaf | name | line | axioms |
|---|---|---|---|
| C1 | `deriv_bumpPhi_eq_zero_of_lt` | 410 | propext, Classical.choice, Quot.sound |
| C2 | `chartDensity_chart` | 425 | + `sorryAx` via B2 `frame_parseval` only |
| C3 | `chartDensity_mem_ball` | 442 | propext, Classical.choice, Quot.sound |
| C4 | `integral_bump_on_nhd` | 481 | + `sorryAx` via B2 (through C2) and B5 `det_chartDeriv` only |
| C5 | `integral_chartDensity_eq_radial` | 528 | propext, Classical.choice, Quot.sound |
| C6 | `integral_radial` | 575 | propext, Classical.choice, Quot.sound |

The glue `integral_chartDensity` (`∫ ψ = 1`, line 637) is now **sorry-free**
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`).  C2 and C4 become sorry-free as soon as
U-B delivers B2 and B5.  Leaves left in this unit: none.

## Helpers added (all `uc_`-prefixed, placed immediately before the leaf that uses them)

Before C4 (lines 465-474):
* `uc_abs_eq_sign_mul (t : ℝ) : |t| = Real.sign t * t` — trichotomy + `Real.sign_of_pos/neg/zero`.
* `uc_sign_mul_sign {t} (ht : t ≠ 0) : Real.sign t * Real.sign t = 1` — `Real.sign_apply_eq_of_ne_zero`.

Before C5 (line 518):
* `uc_chartDensity_polar χ ρ θ : chartDensity χ (ρ * cos θ, ρ * sin θ) = chartDensity χ (ρ, 0)` —
  `mul_pow`, `cos_sq_add_sin_sq`; the `if` condition and both `√` arguments rewrite at once.

Before C6 (lines 545-567):
* `uc_contDiff_bumpPhi χ : ContDiff ℝ ∞ (bumpPhi χ)`.
* `uc_hasDerivAt_bumpPhi χ z : HasDerivAt (bumpPhi χ) (deriv (bumpPhi χ) z) z`.
* `uc_hasDerivAt_radial χ (hρ : ρ ^ 2 < 1) : HasDerivAt (fun ρ => -bumpPhi χ (√(1 - ρ ^ 2)))
  (ρ * (deriv (bumpPhi χ) (√(1 - ρ ^ 2)) / √(1 - ρ ^ 2))) ρ` — `HasDerivAt.sqrt`, `HasDerivAt.comp`,
  `congr_deriv` + `field_simp`.

## How the proofs went vs. the plan (what the assembler/executor should know)

* **No integrability or measurability bookkeeping was needed anywhere except C6.**
  - C4: `setIntegral_eq_integral_of_forall_compl_eq_zero`, `integral_image_eq_integral_abs_det_fderiv_smul`,
    `setIntegral_congr_fun`, `integral_const_mul` all have no integrability hypotheses.
  - C5: instead of Fubini (`setIntegral_prod`) I used `MeasureTheory.setIntegral_prod_mul
    (f := fun ρ => ρ * ψ(ρ,0)) (g := fun _ => 1) (Ioi 0) (Ioo (-π) π)`, which needs only `SFinite` and
    no integrability.  `volume` on `ℝ × ℝ` is `volume.prod volume` by `Measure.volume_eq_prod` (rfl).
    `∫ θ in Ioo (-π) π, 1 = 2π` by `setIntegral_const`, `measureReal_def`, `Real.volume_Ioo`,
    `ENNReal.toReal_ofReal`.  **Consequently the hypothesis `hχ : χ.rOut < 1` of C5 is unused**; the
    statement is frozen so it stays, and the proof references it with `have _ := hχ` to silence the
    unused-variable linter.  (C6 does use `rOut < 1`, essentially: `ρ₁ = √(1 − (1 − rOut)²)` and the
    boundary value `φ(1 − rOut) = 0` need `0 < 1 − rOut`.)
* **C6 route**: `setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self`
  shrinks `Ioi 0` to `Ioc 0 ρ₁` (integrand `= 0` for `ρ > ρ₁`: if `ρ² < 1` then
  `√(1 − ρ²) < 1 − rOut` by `Real.sqrt_lt'` and C1; else the `if` is false), then
  `intervalIntegral.integral_of_le`, `intervalIntegral.integral_congr` (on `uIcc 0 ρ₁` the integrand is
  `ρ φ'(√(1−ρ²))/√(1−ρ²)`), `intervalIntegral.integral_eq_sub_of_hasDerivAt` with the primitive
  `−φ(√(1−ρ²))` (`uc_hasDerivAt_radial`; interval integrability from `ContinuousOn` using
  `ContDiff.continuous_deriv (by simp)` for `deriv (bumpPhi χ)`), and the boundary values
  `√(1 − ρ₁²) = 1 − rOut` (`Real.sq_sqrt`, `sub_sub_cancel`, `Real.sqrt_sq`), `χ(1 − rOut) = 0`
  (`zero_of_le_dist`, `dist = |−rOut| = rOut`), `χ 1 = 1` (`one_of_mem_closedBall`,
  `Metric.mem_closedBall_self`), `√1 = 1`; finish `field_simp; ring`.
* **C3**: the plan's two-case split is as stated (`0 ≤ 1 − rOut`: `Real.le_sqrt` then `nlinarith`;
  `1 − rOut < 0`: `linarith` from `s < 1 < 2 rOut ≤ r²`).  The sup-norm step is
  `Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_lt_iff, abs_lt_of_sq_lt_sq`.
* **C1**: `filter_upwards [Iio_mem_nhds hZ]`, `χ.zero_of_le_dist` with `Real.dist_eq, abs_sub_comm,
  abs_of_nonneg`, then `Filter.EventuallyEq.deriv_eq`, `deriv_const`.  Strictness of `Z < 1 − rOut` is
  used (open neighbourhood `Iio`).
* **C2**: `frame_parseval … (G x)` + `hn x`, `real_inner_comm (G x) e₁/e₂` to match the chart's
  `⟪e₁, G x⟫` order, `ite_eq_left`, `Real.sqrt_sq hx.le`.

## Mathlib pitfalls hit (toolchain v4.34.0-rc2 / Mathlib pin)

* `if_pos` / `if_neg` are **deprecated** in this toolchain ("Use `ite_eq_left` / `ite_eq_right`");
  same signatures, used those instead.
* `le_or_lt` does not exist; use `le_or_gt`.
* `ContDiff.continuous_deriv (h) (hn : 1 ≤ n)` with `n = ∞ : WithTop ℕ∞`: `le_top` does NOT typecheck
  (`∞` is `↑⊤`, not `⊤`); `(by simp)` does.
* `rw [setIntegral_prod_mul]` fails to find the pattern `?f z.1 * ?g z.2` (higher-order); instantiate
  `f, g, s, t` explicitly in a `have` and rewrite with that.
* `polarCoord_target : polarCoord.target = Ioi 0 ×ˢ Ioo (-π) π` and `polarCoord_symm_apply` are the
  `@[simps]`-generated names; `integral_comp_polarCoord_symm f : ∫ p in polarCoord.target,
  p.1 • f (polarCoord.symm p) = ∫ p, f p` has no hypotheses.
* `integral_image_eq_integral_abs_det_fderiv_smul` takes the measure explicitly (`volume` first), the
  `IsAddHaarMeasure volume` instance on `ℝ × ℝ` comes from `Mathlib.Analysis.SpecialFunctions.PolarCoord`.
* `ContDiffBump.zero_of_le_dist : f.rOut ≤ dist x c → f x = 0` (argument order `dist x c`).
* `field_simp` alone closed the derivative-value goals in `uc_hasDerivAt_radial` and C4's pointwise
  identity; a trailing `ring` errors with "no goals".

## Nothing false or under-hypothesised

All six statements are true as stated with the given hypotheses; none needed strengthening.  The only
oddity is the redundant `hχ` in C5 (see above), which is harmless.
