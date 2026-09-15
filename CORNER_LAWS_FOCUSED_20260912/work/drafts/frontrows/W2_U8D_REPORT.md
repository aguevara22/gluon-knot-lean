# W2_U8D_REPORT — unit U8D (L-smooth, deformation leaves): `deform_downCount`, `deform_writhe`, `deform_P`

Written 2026-09-14 10:05 UTC / 6:05am ET by the U8D prover.  File: `work/drafts/frontrows/W2_U8D.lean` (copy of
`Skeleton_W1.lean` with the three deformation leaves proved and one delimited infrastructure block added).
Checked with `cd work/lean && lake env lean ../drafts/frontrows/W2_U8D.lean` (Lean v4.34.0-rc2, project Mathlib pin).

## 1. Result

| item | value |
|---|---|
| leaves | `deform_downCount`, `deform_writhe`, `deform_P` — **all three PROVED**, statements unchanged.  `represent` NOT touched (still `sorry`, as instructed). |
| compile | **0 errors**; the only warnings are the 10 `declaration uses sorry` of the other units' leaves (U3: 5, U5: 1, U6: 3, U8 `represent`: 1) |
| `grep -c sorry` | 13 before (Skeleton_W1.lean) → **10 after** |
| `diff Skeleton_W1.lean W2_U8D.lean` | exactly three deleted lines (the three `:= sorry` bodies) + 1622 inserted lines (6 `import` lines, the block `namespace U8D … end U8D`, the three bodies); no definition, structure, statement, name or docstring touched |
| `#print axioms` (scratch copy `/tmp/u8d/W2_ax.lean`) | `deform_downCount`, `deform_writhe`: `[propext, Classical.choice, Quot.sound]`; `deform_P`: the same + `SM.lp_lm` (through `P`, exactly as PLAN_FINAL §7 FR-13 predicts).  No `sorryAx`, no `SM.ng_finite_word`, no new axiom.  The infrastructure (`U8D.persist`, `U8D.eventually_occHyp`, …) uses only the standard three. |
| size | block lines 3675–5285 of W2_U8D.lean (≈1.6k lines, 141 declarations); the estimate was 2.5–4k for the three leaves |
| imports added | `Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn`, `Mathlib.Analysis.Calculus.MeanValue`, `Mathlib.Analysis.Calculus.Deriv.MeanValue`, `Mathlib.Topology.LocallyConstant.Basic`, `Mathlib.Analysis.Normed.Operator.Banach`, `Mathlib.Analysis.Calculus.TangentCone.Prod` (all already built in the project's Mathlib; they were not in the skeleton's import closure).  Six `import` lines after `import SM.PolynomialBlock` — the only change outside the block and the three bodies. |

## 2. Route (PLAN_FINAL §4 L-smooth, executed without any implicit-function theorem in the parameter)

All three leaves are "locally constant on the connected parameter interval".  Write `d : F.NonsingularDeformation F'`,
`I := Icc (0:ℝ) 1` (a `PreconnectedSpace`), `path t` for `t : I`, and `ρ d t₀ t : Fin (path t₀).c ≃ Fin (path t).c`
(`finCongr`, from `c_eq`).

1. **Joint continuity of the `u`-derivatives (Part B).**  `pd d i k := fderivWithin ℝ (pd d i (k-1)) dom · (0,1)` on
   `dom := Icc 0 1 ×ˢ univ` (a `UniqueDiffOn` set), `ContDiffOn ℝ ∞` by `contDiffOn_infty_iff_fderivWithin`, hence
   `pdI d i k : I × ℝ → Plane` is `Continuous`, and `pd_eq` identifies it with `iteratedDeriv k` of the component
   (chain rule through `u ↦ (t, u)` with `HasFDerivWithinAt.comp_hasDerivWithinAt`; this is where the family's
   smoothness *within* the closed region is used, so the endpoints `t = 0, 1` need no extension).  `eval_eq`,
   `vel_eq`, `acc_eq`, `jerk_eq` read `path t`'s front notions off the family (`path_comp_eq`, `cast_ρ`).
2. **Persistence of a nondegenerate zero (Part C, `persist`).**  For `Φ : X → E → G` with a jointly continuous
   derivative `DΦ`, a zero `y₀` of `Φ x₀` with invertible derivative `L`, and any small radius `ε`: for `x` near `x₀`,
   `Φ x` has exactly one zero in `ball y₀ ε`.  Proof: the mean-value inequality
   (`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`) makes `Φ x` an `ApproximatesLinearOn` of `L` with
   constant `‖L⁻¹‖⁻¹/2` on the ball; injectivity by `ApproximatesLinearOn.injOn`, existence by
   `surjOn_closedBall_of_nonlinearRightInverse` (the image of the ball of radius `ε/2` contains a ball about
   `Φ x y₀`, which is small).  The parameter space `X` is an arbitrary topological space — here `I`.
3. **Cusps (Part D).**  A cusp is a zero of the `x`-velocity alone (`isCusp_iff_fst`, from `no_vertical`);
   `persist` in dimension one (`L` = multiplication by `x''(t₀,u₀) ≠ 0`, `cusp_nonvertical`) gives `cusp_exu`;
   the discriminant `x''·det(γ'',γ''')` is jointly continuous and nonzero, so its sign is constant on a box
   (`cusp_down`); no new cusps by compactness of `Icc 0 1 \ ⋃ near ε p` and
   `IsCompact.eventually_forall_of_forall_eventually` (`cusp_nonew`).  The radii are chosen with the filter
   `𝓝[>] 0` (`Finset.eventually_all`, `eventually_sep`) and extracted once (`eventually_cuspHyp`).  The
   combinatorial core `CuspHyp.downCount_eq` builds the bijection `p ↦ (ρ p.1, Int.fract (φ p))` between the cusp
   Finsets (`Finset.card_bij`), the mod-1 bookkeeping through `Sep`/`fract_ne_of_sep` (Part A).
4. **Double points and the record (Parts F, G).**  For a double point `(p, q)`, `persist` in `ℝ × ℝ → Plane` with
   `L = planeEquiv (vel p) (vel q)` (`(s,r) ↦ s•a − r•b`, inverse by Cramer, `det a b ≠ 0` = `transverse`) gives
   `double_persist`; slope order and `crossSign` are box conditions (`double_pres`, via `slDiff`, `dtFun`).  No new
   double points (`double_nonew`) needs, besides compactness, **uniform local injectivity** of every component
   (`uniform_injOn`): near a regular point `x(t,·)` is strictly monotone (`strictMonoOn_of_deriv_pos`); near a cusp
   `φ` of `path t` the function `u ↦ det(γ''(t,φ), γ(t,u))` has vanishing first and second derivative at `φ` and
   nonvanishing third derivative on the interval (`det(γ'', γ''') ≠ 0`, `cusp_semicubical`, kept away from zero on a
   box), hence is strictly monotone (`strictMonoOn_of_third_deriv_pos`, `injOn_of_third_deriv`) — the printed
   "no accumulation at a semicubical cusp"; the local radii are glued by `IsCompact.elim_nhds_subcover` on
   `Icc (-1) 2`.  The combinatorial core `OccHyp.toFrontRecEquiv` builds `FrontRecEquiv A B` (circles,
   occurrences, cyclic order, meeting, over rule, signs — the front's named record); the cyclic order is
   transported by `cycBetween_fract_of_sep`, the stability of `cycBetween` under perturbations smaller than the
   mod-1 separation (proved through the characterization `cycBetween a b c ↔ fract (b−a) < fract (c−a)`,
   `cycBetween_iff_fract`).  Partners are unique by `no_triple` (`partner_unique`, `eq_partner`).
5. **Glue.**  `IsLocallyConstant.iff_eventually_eq` + `IsLocallyConstant.apply_eq_of_preconnectedSpace` on `I`
   for `t ↦ (path t).downCount`, `t ↦ (path t).writhe` (`FrontRecEquiv.writhe_eq`, a `Finset.sum_bij` on
   `crossingPairs`) and `t ↦ decide (Nonempty ((path t).Marking S))` (`transportMarking` in both directions,
   `FrontRecEquiv.symm`).  `deform_P`: the marking of `F` on `S` transports to a marking of `F'` on `S`, so
   `F'.IsRounding S` (with the `GeomRounding` of `S'`), and the accepted `IsRounding.P_eq` gives `P S = P S'`.

## 3. Helpers added (namespace `SM.FrontRows.U8D`, block `/-! ### U8D infrastructure -/`, W2_U8D.lean:3675–5285)

| part | names |
|---|---|
| A — real-line toolbox | `Sep`, `Sep.neg`, `Sep.symm_sub`, `Sep.pos`, `fract_eq_add_int`, `fract_add_of_sep`, `fract_ne_of_sep`, `not_cycBetween_self_mid`, `fract_sub_of_mem_Ico`, `cycBetween_iff_fract`, `fract_fract_sub_fract`, `fract_sub_fract_eq_add_int`, `cycBetween_fract_of_sep`, `near`, `isOpen_near`, `eventually_sep`, `fract_sub_ne_zero` |
| C — persistence | `persist` |
| B — the family | `I` (+ `PreconnectedSpace I` instance), `dom`, `uniqueDiffOn_dom`, `mem_dom`, `comp`, `Γ`, `contDiffOn_Γ`, `pd`, `contDiffOn_pd`, `continuousOn_pd`, `pd_eq`, `pdI`, `continuous_pdI`, `pdI_eq`, `path_comp_eq`, `eval_eq`, `vel_eq`, `acc_eq`, `jerk_eq`, `hasDerivAt_pdI`, `ρ`, `cast_ρ`, `ρ_symm_apply_cast`, `ρ_val` |
| D — cusps | `isCusp_iff_fst`, `CuspHyp` (+ `CuspHyp.φ`, `φ_mem`, `φ_cusp`, `φ_unique`, `φ_abs`, `f`, `sameParam_f`, `f_mem`, `f_injective`, `f_surjective`, `f_down`, `downCount_eq`), `gx`, `gxx`, `disc`, `continuous_gx`, `continuous_gxx`, `continuous_disc`, `isCusp_iff_gx`, `cuspDisc_eq`, `hasDerivAt_gx`, `cusp_persist`, `cusp_exu`, `cusp_down`, `cusp_nonew`, `eventually_cuspHyp`, `downCount_eq_of_deformation` |
| G — the record | `FrontRecEquiv` (+ `comp_eq_iff`, `symm`, `writhe_eq`), `fst_mem_occSet_of_mem_crossingPairs`, `snd_mem_occSet_of_mem_crossingPairs`, `transportMarking`, `partner_unique`, `partner`, `partner_ne`, `eval_partner`, `eq_partner`, `partner_partner`, `mem_doubleSet_partner`, `box`, `mem_box`, `OccHyp` (+ `sol`, `sol_mem`, `sol_eval`, `sol_unique`, `φ`, `φ_mem`, `φ_abs`, `φ_partner`, `Φ₀`, `sameParam_Φ₀`, `eval_Φ₀`, `slope_Φ₀`, `crossSign_Φ₀`, `Φ₀_ne`, `eval_Φ₀_partner`, `Φ₀_mem`, `Φ`, `Φ_injective`, `Φ_surjective`, `toEquiv`, `toEquiv_val`, `toFrontRecEquiv`) |
| F — double points, glue | `eventually_sign_iff`, `planeMap`, `planeMap_apply`, `planeInv`, `planeInv_apply`, `planeEquiv`, `coe_planeEquiv`, `box_mono`, `strictMonoOn_of_third_deriv_pos`, `injOn_of_third_deriv`, `Φ2`, `DΦ2`, `hasFDerivAt_Φ2`, `continuous_Φ2`, `continuous_DΦ2`, `double_persist`, `slDiff`, `dtFun`, `continuous_dtFun`, `double_pres`, `hasDerivAt_det_pdI`, `Wfun`, `continuous_Wfun`, `injOn_near`, `uniform_injOn`, `nearDiag`, `isOpen_nearDiag`, `double_nonew`, `eventually_occHyp`, `writhe_eq_of_deformation`, `marking_nonempty_of_deformation`, `P_eq_of_deformation` |

Leaf bodies: `deform_downCount … := h.elim fun d => U8D.downCount_eq_of_deformation d`,
`deform_writhe … := h.elim fun d => U8D.writhe_eq_of_deformation d`,
`deform_P … := h.elim fun d => U8D.P_eq_of_deformation d S S' hS hS'`.

## 4. Notes for the reviewer / executor

* All three leaves are true as stated and were proved with the hypotheses of `NonsingularDeformation` exactly as
  frozen: joint `C^∞` smoothness on the closed region `Icc 0 1 ×ˢ univ` is used only through the joint continuity of
  the first three `u`-partials (`ContDiffOn.fderivWithin` within the region); constancy of `c` only through the
  reindexing `ρ`.  Nothing in Statements_FINAL / the skeleton changed.  The route needs no implicit-function theorem
  in `t` (which would fail at `t = 0, 1`) — `persist` replaces it (FR-9's "jointly smooth on `[0,1]`" is exactly
  what is consumed).
* Reusable beyond this unit: `persist` (parametrized persistence of nondegenerate zeros, any parameter space),
  `FrontRecEquiv` / `transportMarking` (the named record of a `SmoothFront` as a transportable object — the same
  notion `represent` will need to compare a smooth front with a realization), `strictMonoOn_of_third_deriv_pos`
  (local injectivity of a semicubical cusp), `cycBetween_fract_of_sep` (stability of the cyclic order), and the
  `fract`/`Sep` toolbox.  These could be ported as a library module `SM/FrontDeform.lean` if the executor prefers.
* Six Mathlib imports were added at the top of the file (listed in §1); they are standard modules already built in
  the project's Mathlib and can be merged verbatim.  `open Classical` is confined to the block.
* Row 76 now waits only on `represent` (U8, not this unit) together with U1/U3 for the word clauses.
* Scratch development files (not deliverables): `/tmp/u8d/p_*.lean` (the parts), `/tmp/u8d/dev.lean` (their
  concatenation with a dev copy of the structure), `/tmp/u8d/W2_ax.lean` (axiom probe).
