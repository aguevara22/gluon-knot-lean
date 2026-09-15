# RPC_U_A_REPORT.md — unit U-A (algebra and exactness) of `RPC_Skeleton.lean`

File: `work/drafts/fd/RPC_U_A.lean` (copy of the skeleton with the 11 U-A leaves proved).
Written 2026-09-14 by the U-A prover agent.  Plan of record: `work/drafts/fd/RPC_PLAN.md` §U-A.

## Result

* **All 11 leaves of U-A are proved**; `sorry` count 29 → 18 (the 18 remaining are exactly the
  U-B (8), U-C (6), U-D (4) leaves, lines ≥ 503).
* Compile: `cd work/lean && lake env lean ../drafts/fd/RPC_U_A.lean` → **0 errors**, 6.5 s here;
  the only warnings are the 18 `declaration uses sorry` of the other units.  No other warnings
  (no deprecations, no unused simp args).
* Axioms (checked with `#print axioms` on a scratch copy): every U-A theorem and the helper depend
  on `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`.
* Statement freeze verified by `diff` against `RPC_Skeleton.lean`: the only removed lines are the
  11 `  sorry` lines; every `theorem/def/structure` header line is byte-identical; docstrings untouched.
  No leaf needed a weaker conclusion or a stronger hypothesis; nothing was found false.

| leaf | name | line | proof size | notes |
|---|---|---|---|---|
| A1 | `cross_fderiv_eq_smul` | 160 | 11 | `cross_cross_eq` twice + `Family.inner_fderiv_eq_zero`; `exact h2.symm` closes `c = triple • G x` by unfolding `Family.triple` definitionally |
| A2 | `fderiv_oneForm_apply` | 175 | 20 | `HasFDerivAt.inner`, `HasDerivAt.comp_hasFDerivAt`, `Family.hasFDerivAt_fderiv_apply`, `HasFDerivAt.cross`, `HasFDerivAt.mul`; `simp only` + `ring` (pattern of `Family.fderiv_triple_apply`) |
| A3 | `contDiff_oneForm` | 201 | 4 | `hk.comp (hG.inner ℝ contDiff_const)` times `(contDiff_const.cross hG).inner ℝ (Family.contDiff_fderiv_apply hG w)` |
| A4 | `fderiv_oneForm_antisymm` | 218 | 7 | `rw` A2 twice + `Family.fderiv_fderiv_symm`, then `linear_combination core_algebra …` (the `G''` terms cancel inside `ring`) |
| A5 | `integral_fderiv_eu_eq_zero` | 247 | 16 | swap via helper `ua_integral_integral_swap`, FTC per `v`-slice (`hasDerivAt_sliceU`), `hper (a, v)` |
| A6 | `integral_fderiv_ev_eq_zero` | 268 | 13 | FTC on the inner integral (`hasDerivAt_sliceV`), `hper (u, b)` |
| A7 | `integral_triple_mul_mk_eq_zero` | 286 | 33 | `calc`: pointwise A4, `integral_sub` inside and outside (integrability from continuity: `Family.contDiff_fderiv_apply`, `continuous_parametric_integral`), then A5 + A6 with `periodic_oneForm` |
| A8 | `contDiff_cutoffK` | 338 | 15 | `contDiff_iff_contDiffAt`; at `Z = 1`: `cutoffK χ =ᶠ[𝓝 1] 0` from `χ.eventuallyEq_one`, `contDiffAt_const.congr_of_eventuallyEq`; at `Z ≠ 1`: `ContDiffAt.div` |
| A9 | `mk_cutoffK_one` | 375 | 8 | `χ 1 = 1` (`one_of_mem_closedBall`, `Metric.mem_closedBall_self`), `deriv (fun z => χ z) 1 = 0` via `Filter.EventuallyEq.deriv_eq` + `deriv_const`, `deriv_bumpPhi`, `ring` |
| A10 | `gaussIntegral_eq_shift` | 395 | 22 | `Function.Periodic.intervalIntegral_add_eq` on the inner integrals (periodicity in `v`) and on `u ↦ ∫_b^{b+P}` (periodicity in `u`), then `gaussDensity_eq_triple'` |
| A11 | `gaussIntegral_eq_integral_bump` | 425 | 66 | A10; pointwise `(1/4π)·D = D·mk(k_χ)(Z) + D·φ'(Z)` from `mk_cutoffK`; `integral_const_mul`, `integral_add` (inner and outer, integrability from continuity), A7 with `k = cutoffK χ`, `uncurry G` periodicities from `hpu`/`hpv` |

## Helper added (allowed by rule 2; prefix `ua_`)

* `ua_integral_integral_swap` (line 232, immediately before `-- LEAF A5`):
  `Continuous (uncurry f) → ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y` for
  **arbitrary** `a b c d`.  Needed because the library lemma `integral_integral_swap_of_continuous`
  demands `a ≤ b`, `c ≤ d`, while the leaves A5/A7/A11 carry **no sign hypothesis on `P`**
  (the skeleton's statements have `{P : ℝ}` with only periodicity).  Proof: the four sign cases via
  `intervalIntegral.integral_symm` + `intervalIntegral.integral_neg` + the library lemma.
  (A6, A10, A11 need no sign either: FTC and `Periodic.intervalIntegral_add_eq` are sign-free.)

## Mathlib / library pitfalls met (for the assembler and the other units)

1. `intervalIntegral.integral_eq_sub_of_hasDerivAt` cannot be `apply`ed to a goal of the form
   `∫ u in a..a+P, ∂F(u,v) = F (a+P, v) − F (a, v)` (higher-order unification of `?f ?b − ?f ?a`);
   use `refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => F (u, v)) ?_ ?_`.
2. `ContinuousLinearMap.add_apply / zero_apply / smul_apply` are deprecated in this Mathlib; the root
   `add_apply`, `zero_apply`, `smul_apply` work in `simp only` (as the library's `fderiv_triple_apply` does).
3. `hasDerivAt_sliceU/V`, `integral_integral_swap_of_continuous`, `continuous_parametric_integral`
   live in namespace `SM` (not `SM.LinkingCalculus`); with `open LinkingCalculus` inside `SM` they are
   reachable unqualified.  `Family.*` lemmas are `SM.LinkingCalculus.Family.*`.
4. `hasDerivAt_sliceU` is stated with `(1, 0)`; `exact` unifies it with `eu2` (plain `def`, unfolded
   at default transparency) — no `simp only [eu2]` needed.
5. `Function.Periodic.intervalIntegral_add_eq hf t s : ∫ x in t..t+T = ∫ x in s..s+T` has no sign
   hypothesis; instantiating `t = 0` leaves `0 + P`, fixed by `rwa [zero_add] at this`.
6. `uncurry G (u, v)` is definitionally `G u v`, and `y + (P, 0)` is definitionally
   `(y.1 + P, y.2 + 0)`; a `show` line converts between the curried statement (`⟪G u v, N⟫`, `hpu`)
   and the uncurried one (`Periodic (uncurry G) (P, 0)`) without lemmas.
7. Continuity of `deriv (bumpPhi χ)`: `ContDiff ℝ ∞ (bumpPhi χ)` is
   `((contDiff_const.add contDiff_id).mul χ.contDiff).div_const _`, then `.continuous_deriv (by simp)`.
   Continuity of `mk (cutoffK χ)` is obtained from `funext (mk_cutoffK χ)` rather than from A8.
8. `ContDiffBump` facts used: `χ.eventuallyEq_one : ⇑χ =ᶠ[𝓝 1] 1`, `χ.one_of_mem_closedBall`,
   `χ.rIn_pos`, `χ.contDiff`; `Filter.EventuallyEq.deriv_eq` gives `deriv (fun z => χ z) 1 = deriv (fun _ => 1) 1`.
9. Continuity of `fun p : ℝ × ℝ => g (p.1, p.2)` from `Continuous g`: `hg.comp (continuous_fst.prodMk continuous_snd)`;
   slices: `hg.comp (continuous_const.prodMk continuous_id)`.  `Continuous.intervalIntegrable _ _` then gives
   `IntervalIntegrable`.

## For the assembler

* Dependencies inside U-A only: A4 ← A1, A2; A7 ← A3, A4, A5, A6, `periodic_oneForm`; A11 ← A7, A8, A10,
  `mk_cutoffK` (← A9, `mk_cutoffK_of_ne`).  No U-A leaf uses any statement from U-B/U-C/U-D.
* To merge: take lines 158–496 of `RPC_U_A.lean` (from `-- LEAF A1` to `end UA`) — or simply the whole
  `section UA` block (lines 99–496) — into the assembled file; the helper sits inside the section.
* Iteration recipe that worked: a `/tmp` scratch made of the file's lines 1–296 (through `end UA`) plus
  `end RPC / end / end SM` compiles in ~5 s; the full file in ~6.5 s on this pod.
