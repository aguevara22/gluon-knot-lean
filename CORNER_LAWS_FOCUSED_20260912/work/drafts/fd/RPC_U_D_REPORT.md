# RPC_U_D_REPORT.md — unit U-D (assembly) of `SM.regularPoleCount`

File: `work/drafts/fd/RPC_U_D.lean` (copy of `RPC_Skeleton.lean`; only the four U-D `sorry` bodies
replaced and three `ud_` helpers inserted immediately before `-- LEAF D4`).  Written 2026-09-14.

Compile: `cd work/lean && lake env lean ../drafts/fd/RPC_U_D.lean` → exit 0, **0 errors**, exactly
25 `declaration uses sorry` warnings, all at other units' leaves (A1-A11, B1-B9, C1-C6).
`grep -c sorry`: **29 before → 25 after**.  `diff RPC_Skeleton.lean RPC_U_D.lean` removes exactly
four lines, all `  sorry`; no statement, name or docstring changed.

## Leaves proved (4 of 4)

| leaf | name | line | axioms |
|---|---|---|---|
| D1 | `integral_box_eq_setIntegral` | 481 | propext, Classical.choice, Quot.sound |
| D2 | `setIntegral_box_eq_sum` | 496 | propext, Classical.choice, Quot.sound |
| D3 | `integral_bump_eq_sum_of_system` | 516 | + `sorryAx`, only through the black boxes C1, C3, C4, `integral_chartDensity` (C5/C6) |
| D4 | `exists_shift` | 587 | propext, Classical.choice, Quot.sound (uses the PROVED `gaussDensity_periodic`) |

Leaves left: none.  No leaf was false or needed a stronger hypothesis; every statement was proved
exactly as frozen.

## Helpers added (all before `-- LEAF D4`, sorry-free)

* `ud_shift_mem` (line 554): for `0 < a < P`, `u ∈ [0,P)`, `u ≠ a`:
  `a < u + P·[u < a] < a + P`.
* `ud_shift_inj` (line 563): `u ↦ u + P·[u < a]` is injective on `[0,P)`
  (`split_ifs at h <;> linarith`).
* `ud_shift_coord` (line 569): for `u ∈ [a, a+P]`, `u' := u − P·[P ≤ u]` lies in `[0,P)`
  and, when `u' ≠ a`, `u' + P·[u' < a] = u`.
These are the 1-D coordinate facts behind the shift map `τ p = (p.1 + P·[p.1 < a], p.2 + P·[p.2 < b])`;
applying them per coordinate keeps `exists_shift` free of nested `if` case analysis.

## How each leaf is proved

* **D1** — verbatim `DivergenceTheorem.lean:530-540` pattern: `simp only [intervalIntegral.integral_of_le,
  ha, hb, setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]` then
  `(setIntegral_prod _ hI).symm`, `hI` from `hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)`.
  `volume` on `ℝ × ℝ` unifies with `volume.prod volume` definitionally (no `Measure.volume_eq_prod` needed).
* **D2** — `setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_Icc.prod measurableSet_Icc)
  (iUnion₂_subset hVsub) (fun x hx => hzero x hx.1 hx.2)` then `integral_biUnion_finset S
  (fun p hp => (hVo p hp).measurableSet) (fun p hp q hq hpq => hdisj p hp q hq hpq) (fun p hp => hI.mono_set (hVsub p hp))`.
  `Set.Pairwise (↑S) (Disjoint on V)` is accepted directly from `hdisj` by defeq (`Finset.mem_coe`,
  `Function.onFun`), no unfolding needed.
* **D3** — continuity of the integrand: `Family.contDiff_triple hG eu2 ev2` (library) and
  `ContDiff ℝ ∞ (bumpPhi χ)` (`((contDiff_const.add contDiff_id).mul χ.contDiff).div_const _` after
  `rfl`-unfolding `bumpPhi χ = fun z => (1 + z) * χ z / (4 * π)`), then `hφ.continuous_deriv (by simp)`
  composed with `hG.continuous.inner continuous_const`.  Then `integral_box_eq_setIntegral` (the box bounds
  `a := a, a' := a + P, b := b, b' := b + P` must be passed explicitly; the beta-reduced form is joined to
  the goal with `refine hbox.trans ?_`), `setIntegral_box_eq_sum` with `sys.V`, `sys.V_isOpen`,
  `sys.V_subset` weakened through `prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self`, `sys.disjoint_V`,
  and `hzero` from `sys.small` + `hχδ` + `deriv_bumpPhi_eq_zero_of_lt` (strict `<` via `linarith`);
  finally `Finset.sum_congr rfl` with `integral_bump_on_nhd … (fun w hw => chartDensity_mem_ball χ sys.r_pos hχr hw)`,
  `integral_chartDensity χ hχ₁`, `mul_one`.  Exactly the plan's call shape; no hypothesis was missing.
* **D4** — `T := hfin.toFinset`; `a`, `b` from `(Ioo_infinite hP).exists_notMem_finset (T.image Prod.fst)`
  (resp. `Prod.snd`); `τ` as above; `S := T.image τ`.  Membership in `T` is unfolded once
  (`hmemT`, by `rw [Finite.mem_toFinset]; exact Iff.rfl` — the set-builder/`×ˢ`/`Ico` membership is
  definitionally `((0 ≤ p.1 ∧ p.1 < P) ∧ (0 ≤ p.2 ∧ p.2 < P)) ∧ G p.1 p.2 = N`).  (i) interior:
  `ud_shift_mem` per coordinate.  (ii) `←`: `hτG` (periodicity, `split_ifs <;> simp only [hGu, hGv, add_zero]`);
  `→`: reduce `x` to `q = (x.1 − P·[P ≤ x.1], x.2 − P·[P ≤ x.2])`, `q ∈ T` by `ud_shift_coord` and the
  periodicity lemmas `hGu' : G (u − P·[P ≤ u]) v = G u v`, `hGv'`, then `τ q = x` by `Prod.ext` and the third
  component of `ud_shift_coord` fed with `q.1 ≠ a` (from `a ∉ T.image Prod.fst`).  (iii) `Finset.sum_image`
  with `InjOn τ ↑T` (`ud_shift_inj` per coordinate) and `hτD` from `gaussDensity_periodic hpu hpv`.
  `uncurry G x = N` is definitionally `G x.1 x.2 = N` (handled by `have … : G x.1 x.2 = N := hGx` / `show`).

## Mathlib pitfalls met (this pin)

* `if_pos` / `if_neg` are deprecated → `ite_eq_left h` / `ite_eq_right h` (same shape).
* `Set.mem_setOf_eq` is deprecated (use `Set.mem_ofPred_eq`); avoided altogether via `Iff.rfl`.
* `Set.Infinite.exists_notMem_finset` (not `exists_not_mem_finset`); `Set.Ioo_infinite` needs `a < b`.
* `integral_box_eq_setIntegral` has all box bounds implicit; when the RHS is not yet in the goal, pass
  `(a := …) (a' := …) (b := …) (b' := …)` or the elaborator cannot synthesize them.
* `rw [← hGu (u - P) v]` rewrites the LHS `G (u - P) v`; do the `u`-shift and the `v`-shift in separate
  1-D lemmas (`hGu'`, `hGv'`) rather than chaining both `←` rewrites on a two-shift term (the first rewrite
  changes the term the second one is looking for).
* `Finset.image` needs `DecidableEq (ℝ × ℝ)`; `classical` at the start of `exists_shift` supplies it
  (the frozen statement itself needs no decidability).

## For the assembler / executor

* U-D is complete and self-contained: paste lines 481-675 of `RPC_U_D.lean`
  (section `UD`, including the three `ud_` helpers) over the skeleton's `UD` section.  Nothing outside the
  section was touched; the glue theorems `regularPoleCount` / `crossing_formula_unconditional` still
  compile unchanged.
* D3 will become sorry-free automatically once C1 (`deriv_bumpPhi_eq_zero_of_lt`), C3
  (`chartDensity_mem_ball`), C4 (`integral_bump_on_nhd`), C5, C6 land; it uses only their statements.
* The compile of this 722-line file takes ~7 s in this pin (the heavy work is in the imports), so
  iterating on the assembled file is cheap.
