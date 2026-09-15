# RPC_U_B_REPORT.md — unit U-B (frame, chart Jacobian, inverse-function neighbourhoods)

File: `work/drafts/fd/RPC_U_B.lean` (copy of `RPC_Skeleton.lean` with the U-B leaves filled in).
Written 2026-09-14 by the U-B prover agent.  Compile:
`cd work/lean && lake env lean ../drafts/fd/RPC_U_B.lean` → **0 errors**; warnings = the 21 remaining
`sorry`s of units A (11), C (6), D (4) plus the pre-existing unused-variable `hP` in the frozen
statement of `exists_nhdSystem`.  `grep -c sorry`: **29 before → 21 after**.
`diff RPC_Skeleton.lean RPC_U_B.lean`: the only removed lines are the eight `  sorry` bodies of the
U-B leaves; 200 lines added, all inside skeleton lines 300–400 (section `UB`).  No statement,
definition, name or docstring was changed.

## Leaves proved (8 of 8)

| leaf | name | axioms (`#print axioms`) |
|---|---|---|
| B1 | `exists_frame` | propext, Classical.choice, Quot.sound |
| B2 | `frame_parseval` | propext, Classical.choice, Quot.sound |
| B4 | `det_eq_fin_two` | propext, Classical.choice, Quot.sound |
| B5 | `det_chartDeriv` | + `sorryAx` **only through A1** `cross_fderiv_eq_smul` (black box) |
| B6 | `exists_strict_equiv_chart` | + `sorryAx` only through A1 (via B5) |
| B7 | `exists_regular_nhd` | + `sorryAx` only through A1 (via B6) |
| B8 | `exists_disjoint_balls` | propext, Classical.choice, Quot.sound |
| B9 | `exists_nhdSystem` | + `sorryAx` only through A1 (via B7) |

Leaves left in unit B: none.  All eight statements are true as frozen; no hypothesis is missing.
(`hP : 0 < P` in B9 is not needed by the proof — the linter warns; the statement is frozen, leave it.)

Note on the task text: it listed `deriv_bumpPhi_eq_zero_of_lt` among the U-B names, but
`RPC_PLAN.md` assigns it to **U-C as leaf C1**; I did not touch that `sorry` (rule 3).  A verified
proof is given at the end of this report for the U-C prover.

## Helpers added (all `ub_*`, each immediately before the leaf that uses it)

* `ub_exists_unit_orth {N} (hN : ‖N‖ = 1) : ∃ e, ‖e‖ = 1 ∧ ⟪N, e⟫ = 0` (before B1).  Case split on
  `N 0 ^ 2 < 1`: if yes take `v = EuclideanSpace.single 0 1`, else `N 1 = 0` and `v = single 1 1`;
  then `e = ‖N × v‖⁻¹ • (N × v)` with `‖N × v‖² = 1 − ⟪N,v⟫² > 0` (`norm_cross_sq`).
* `ub_contDiff_chart (e₁ e₂) (hG) : ContDiff ℝ ∞ (chart e₁ e₂ G)` (before B6):
  `(contDiff_const.inner ℝ hG).prodMk (contDiff_const.inner ℝ hG)`.
* `ub_approximates_deriv_on_nhds (hf : HasStrictFDerivAt f f' a) (hc : 0 < c) : ∃ s ∈ 𝓝 a,
  ApproximatesLinearOn f f' s c` (before B7) — a 5-line replica of Mathlib's
  `HasStrictFDerivAt.approximates_deriv_on_nhds`, specialised to `ℝ × ℝ`; see pitfall 1.
* `ub_exists_sign_nhd (hD : Continuous D) (hp : D p ≠ 0) : ∃ W, IsOpen W ∧ p ∈ W ∧ ∀ x ∈ W,
  Real.sign (D x) = Real.sign (D p)` (before B7).
* `ub_chart_eq_zero (hN : cross e₁ e₂ = N) (hp : G p = N) : chart e₁ e₂ G p = 0` (before B7).
* `ub_exists_pos_le {α} (T : Finset α) (f : α → ℝ) (hf : ∀ t ∈ T, 0 < f t) : ∃ r > 0, ∀ t ∈ T,
  r ≤ f t` (before B8; used by B8 twice and by B9): `Finset.exists_min_image`, `T = ∅ ⇒ r = 1`.

## How each leaf was proved (deviations from RPC_PLAN.md)

* **B1** as planned (coordinate vector, `norm_cross_sq`, `cross_cross_eq`); `‖N × e₁‖ = 1` from
  `‖·‖² = 1` and `‖·‖ ≥ 0` by `nlinarith`.
* **B2** NOT the projection route of the plan.  Shorter: Lagrange `‖x × N‖² = ‖x‖²‖N‖² − ⟪x,N⟫²`
  (`norm_cross_sq x N`, `‖N‖² = 1`) and BAC-CAB `x × N = x × (e₁ × e₂) = ⟪x,e₂⟫e₁ − ⟪x,e₁⟫e₂`
  (`cross_cross_eq`), whose squared norm is `⟪x,e₂⟫² + ⟪x,e₁⟫²` by `norm_sub_sq_real`, `norm_smul`,
  `real_inner_smul_left/right`, `h₁₂`; `linarith`.  ~15 lines.
* **B4** exactly the plan's primary route (the `Fin 2 → ℝ` fallback was not needed):
  `rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]`,
  then `simp only [LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one,
  Module.Basis.coe_finTwoProd_repr, ContinuousLinearMap.coe_coe]` and `simp` (for `![a,b] 0 = a`).
* **B5** as planned: `inner_cross_cross' e₁ e₂ (G' eu2) (G' ev2)` rewritten with `hN`,
  `cross_fderiv_eq_smul`, `real_inner_smul_right`, `real_inner_comm (G x) N`; after `det_eq_fin_two`
  and `simp only [chartDeriv, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
  innerSL_apply_apply]` the goal is `key.symm` up to the definitional `eu2 = (1,0)` (`exact` closes it).
* **B6** via `ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero` (one step, instead of
  `LinearMap.equivOfDetNeZero` + `toContinuousLinearEquiv`), `coe_toContinuousLinearEquivOfDetNeZero`,
  and `ContDiffAt.hasStrictFDerivAt' (hasFDerivAt_chart …) (by simp)`.
* **B7** WITHOUT `HasStrictFDerivAt.toOpenPartialHomeomorph` / `map_nhds_eq_of_equiv` (not importable,
  pitfall 1).  With `e, he` from B6, `c := ‖(e.symm : →L)‖₊⁻¹ / 2` (`0 < ‖e.symm‖₊` from
  `e.subsingleton_or_nnnorm_symm_pos` and `not_subsingleton (ℝ × ℝ)`; `c < ‖e.symm‖₊⁻¹` by
  `NNReal.half_lt_self`), `ub_approximates_deriv_on_nhds he hc0` gives `s ∈ 𝓝 p` with
  `hs : ApproximatesLinearOn (chart …) ↑e s c`; `V := s' ∩ U' ∩ {0 < Z} ∩ W` with `s' ⊆ s` open
  (`mem_nhds_iff`), `U' ⊆ U` open, `W` from `ub_exists_sign_nhd`.  Injectivity: `hs.injOn (Or.inr hcN)`
  restricted with `.mono`.  Ball: `(hs.mono_set hVs).open_image e.toNonlinearRightInverse hVopen
  (Or.inr hcN)` gives `IsOpen (chart '' V)`; `chart p = 0 ∈ chart '' V`; `Metric.mem_nhds_iff`.
  (`e.toNonlinearRightInverse.nnnorm` is `‖↑e.symm‖₊` by `rfl`, so `Or.inr hcN` typechecks directly.)
* **B8** as planned with `ub_exists_pos_le` on `S` (radii `ε p` from `Metric.isOpen_iff`, chosen with
  `choose` after a `∀ p, ∃ ε > 0, p ∈ S → …` formulation) and on
  `T := (S ×ˢ S).filter (fun q => q.1 ≠ q.2)` with `dist q.1 q.2 / 2`; `r := min r₁ r₂`;
  `Metric.ball_subset_ball`, `Metric.ball_disjoint_ball`.
* **B9** as planned.  `V` and `r` are obtained by `choose` from `∀ p, ∃ V, p ∈ S → (…)` (value `∅`/`1`
  off `S`); `rmin` from `ub_exists_pos_le`; `K := box \ ⋃ p ∈ S, V p` compact via
  `(isCompact_Icc.prod isCompact_Icc).diff (isOpen_iUnion fun p => isOpen_iUnion fun hp => …)`;
  `G x ≠ N` on `K` else `x ∈ S` (`hS`) and `x ∈ V x` (`mem_iUnion₂.mpr ⟨x, hxS, _⟩`);
  `exists_delta_of_compact`; the structure is built with an anonymous-constructor record.

## Mathlib pitfalls (this Mathlib pin, Lean 4.34.0-rc2)

1. **The inverse-function-theorem module is not imported.**  `Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`
   (`HasStrictFDerivAt.toOpenPartialHomeomorph`, `.map_nhds_eq_of_equiv`, `.approximates_deriv_on_nhds`,
   `.localInverse`) is NOT reachable from the five imports of the skeleton; `Jacobian` only pulls in
   `…InverseFunctionTheorem.ApproximatesLinearOn`.  Everything needed is in that layer:
   `HasStrictFDerivAt.isLittleO` + `Asymptotics.IsLittleO.def` + `nhds_prod_eq`/`mem_prod_same_iff`
   rebuild the approximation on a neighbourhood; `ApproximatesLinearOn.injOn`, `.open_image`,
   `.mono_set`, `ContinuousLinearEquiv.toNonlinearRightInverse`.  No import was added (imports frozen).
2. `Basis` is `Module.Basis`: `Module.Basis.finTwoProd`, `Module.Basis.finTwoProd_zero/one`,
   `Module.Basis.coe_finTwoProd_repr` (`⇑((finTwoProd R).repr x) = ![x.1, x.2]`, `rfl`).
   `rw [ContinuousLinearMap.det]` works (it is an `abbrev` for `LinearMap.det ↑f`).
3. `innerSL_apply` does not exist; the lemma is `innerSL_apply_apply : innerSL 𝕜 v w = ⟪v, w⟫`.
4. `ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero` / `coe_toContinuousLinearEquivOfDetNeZero`
   (Topology/Algebra/Module/FiniteDimension.lean) replace the two-step `equivOfDetNeZero` route.
5. `ContDiffAt.hasStrictFDerivAt' (hf : ContDiffAt 𝕂 n f x) (hf' : HasFDerivAt f f' x) (hn : n ≠ 0)`;
   `(by simp)` proves `∞ ≠ 0`.
6. `EuclideanSpace.single_apply`/`norm_single` are deprecated (→ `PiLp.single_apply`, `PiLp.norm_single`);
   `simp` proves `‖EuclideanSpace.single i 1‖ = 1`; `EuclideanSpace.inner_single_right` produces a
   `starRingEnd` that `simp` removes over `ℝ`.
7. `pos_of_ne_zero` needs `IsBotZeroClass` and fails on `ℝ`; use `(norm_nonneg w).lt_or_eq`.
8. For `⋃ p ∈ S, V p` with `S : Finset`, prefer `isOpen_iUnion fun p => isOpen_iUnion fun hp => …` and
   `mem_iUnion₂.mpr ⟨p, hp, _⟩` over `isOpen_biUnion`/`mem_biUnion` (those want `s : Set`).
9. `Real.sign_of_neg`/`Real.sign_of_pos` are the sign lemmas (`Real.sign r = -1` / `= 1`).
10. `linarith` does not see through `z ∈ Iio a`; `rw [mem_Iio] at hz` first (C1 probe).
11. Compile time: with cached `.olean`s a full `lake env lean` of the 780-line file takes ~6 s, not 1 min.

## For the assembler / executor

* Section `UB` of `RPC_U_B.lean` (lines 299–594) can be pasted over section `UB` of the skeleton
  verbatim; it depends on the U-A statement `cross_fderiv_eq_smul` (A1) and on the skeleton's proved
  lemmas `inner_cross_cross'`, `hasFDerivAt_chart`, `exists_delta_of_compact`, `inner_lt_one_of_ne`
  (unchanged, still in place), plus `SM.LinkingCalculus` names `cross_cross_eq`, `norm_cross_sq`,
  `inner_cross_self_left/right`, `inner_eq_sum`, `Family.contDiff_triple`.
* Helper names `ub_*` are unique in the file; no `open` was added; `NNReal` is referred to by name
  (the `ℝ≥0` notation is not opened in the skeleton).
* Verified: `#print axioms SM.regularPoleCount` now lists `sorryAx` only from the remaining 21 leaves.

## Verified proof of C1 for the U-C prover (NOT applied — belongs to unit C)

Compiles axiom-clean against the skeleton header (`/tmp/ub/c1probe.lean`):
```lean
theorem deriv_bumpPhi_eq_zero_of_lt (χ : ContDiffBump (1 : ℝ)) {Z : ℝ} (hZ : Z < 1 - χ.rOut) :
    deriv (bumpPhi χ) Z = 0 := by
  have hev : bumpPhi χ =ᶠ[𝓝 Z] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds hZ] with z hz
    rw [mem_Iio] at hz
    have hχ : χ z = 0 := χ.zero_of_le_dist (by
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith [χ.rOut_pos])]
      linarith)
    simp [bumpPhi, hχ]
  rw [hev.deriv_eq, deriv_const]
```
