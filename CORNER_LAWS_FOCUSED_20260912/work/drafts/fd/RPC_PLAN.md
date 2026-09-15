# RPC_PLAN.md — proof plan for `SM.regularPoleCount` along the bump-primitive route

Companion to `work/drafts/fd/RPC_Skeleton.lean` (compiles with 0 errors via
`cd work/lean && lake env lean ../drafts/fd/RPC_Skeleton.lean`; `#print axioms SM.regularPoleCount`
= `[propext, sorryAx, Classical.choice, Quot.sound]`, the `sorryAx` coming only from the 29 leaves).
Feasibility analysis: `work/drafts/fd/REGULAR_POLE_COUNT_FEASIBILITY.md`.  Written 2026-09-14.

Conventions.  `G : ℝ × ℝ → E3` uncurried, `D x = Family.triple G eu2 ev2 x = ⟪G x, G_u × G_v⟫`
(`= gaussDensity` by the proved `gaussDensity_eq_triple'`), `Z x = ⟪G x, N⟫`, `eu2 = (1,0)`,
`ev2 = (0,1)`.  `χ : ContDiffBump (1:ℝ)` (`χ = 1` on `[1−rIn, 1+rIn]`, `0` off `(1−rOut, 1+rOut)`),
`k_χ = cutoffK χ`, `φ = bumpPhi χ`, `ψ = chartDensity χ`, `F = chart e₁ e₂ G`.
Every leaf is stated so that a prover needs only the STATEMENTS of the other leaves, never their
proofs; cross-unit uses are listed per leaf.  Numeric identities were probed in Python (see
"truth check").  Sizes are lines of Lean including helper `have`s.

## Units

| unit | leaves | est. lines | depends on (statements only) | content |
|---|---|---|---|---|
| U-A algebra/exactness | 11 (A1-A11) | 400 | — | exterior derivative of `G^*(k(Z)(N×x)·dx)`, Green on the period box, the cutoff `k_χ`, `gaussIntegral = ∫∫ D·φ'(Z)` |
| U-B frame/IFT | 8 (B1,B2,B4-B9) | 475 | A1 (via B5) | orthonormal frame, chart Jacobian `D·Z`, inverse-function neighbourhoods, the `NhdSystem` |
| U-C change of variables/polar | 6 (C1-C6) | 415 | B2, B5 | `∫_V D·φ'(Z) = sign(D p)·∫ψ`, `∫ψ = 1` |
| U-D assembly | 4 (D1-D4) | 280 | C1, C3, C4 | Fubini/localisation on the box, main lemma, shift of the fundamental domain |
| glue (PROVED in the skeleton) | 0 | — | A11, B1, B9, D3, D4 | `regularPoleCount`, `crossing_formula_unconditional`, `mk_cutoffK`, `integral_chartDensity` |

Total estimate for the leaves: ~1570 lines (range 1300-2000); with the skeleton's 577 lines the finished
file is ~1900-2500 lines.  Already proved in the skeleton (13 lemmas): `inner_cross_cross'`,
`core_algebra`, `gaussDensity_eq_triple'`, `gaussDensity_periodic`, `periodic_oneForm`,
`hasDerivAt_bump`, `deriv_bumpPhi`, `mk_cutoffK_of_ne`, `mk_cutoffK`, `hasFDerivAt_chart`,
`exists_delta_of_compact`, `inner_lt_one_of_ne`, `integral_chartDensity`, plus the two final theorems.

Suggested order inside a unit: U-A: A1, A2, A3 → A4 → A5, A6 → A7; A8, A9 → A10 → A11.
U-B: B1, B2, B4 → B5 → B6 → B7; B8 → B9.  U-C: C1 → C3; C2 → C4; C5, C6.  U-D: D1, D2 → D3; D4.

## U-A. Algebra and exactness

**A1** `cross_fderiv_eq_smul` (line 160) — `G_a × G_b = triple G a b x • G x` when `‖G‖ ≡ 1`.
Sketch: `c := cross (G'a) (G'b)`; `cross c (G x) = 0` by `cross_comm_neg`/`cross_cross_eq` and
`Family.inner_fderiv_eq_zero hG hn x a`, `… x b`; then `cross (G x) (cross c (G x)) = ⟪G x,G x⟫•c − ⟪G x,c⟫•G x`
(`cross_cross_eq`) with LHS `= 0`, `⟪G x,G x⟫ = 1` (`real_inner_self_eq_norm_sq`), so `c = ⟪G x,c⟫•G x`,
and `⟪G x, c⟫ = triple G a b x` by definition.  Mathlib/file: `cross_cross_eq`, `cross_zero_right`,
`real_inner_self_eq_norm_sq`, `Family.inner_fderiv_eq_zero`.  ~30 lines.  Truth: standard; if `G'a, G'b`
are dependent both sides are `0`.

**A2** `fderiv_oneForm_apply` (line 167) — chain/product rule for `y ↦ k(Z y)·⟪N × G y, G'(y) w⟫` in direction `c`:
`k'(Z)⟪G'c,N⟫⟪N×G,G'w⟫ + k(Z)(⟪N×G'c, G'w⟫ + ⟪N×G, G''c w⟫)`.
Sketch: `HasFDerivAt` of `y ↦ ⟪G y, N⟫` (`(hG.differentiable _ y).hasFDerivAt.inner ℝ (hasFDerivAt_const N y)`
or `HasFDerivAt.inner`), compose with `hk.differentiable` (`HasDerivAt.comp_hasFDerivAt`); `y ↦ fderiv ℝ G y w`
has derivative `(fderiv ℝ (fderiv ℝ G) x).flip w`-type via `Family.hasFDerivAt_fderiv_apply hG x w`;
`HasFDerivAt.cross` (in the file) for `cross N (G y)`; `HasFDerivAt.inner`, `HasFDerivAt.mul`; finish with
`HasFDerivAt.fderiv` and `simp`.  Pattern: `Family.fderiv_triple_apply` (file lines ~990-1010).  ~60 lines.
Truth: routine calculus; `fderiv ℝ (fderiv ℝ G) x c w` is `∂_c(G' w)` as in `fderiv_triple_apply`.

**A3** `contDiff_oneForm` (line 177) — smoothness of `y ↦ oneForm k N G y w`.
Sketch: `hk.comp (hG.inner contDiff_const)` times `(contDiff_const.cross hG).inner (Family.contDiff_fderiv_apply hG w)`;
`ContDiff.mul`.  Mathlib/file: `ContDiff.inner`, `ContDiff.cross` (file), `Family.contDiff_fderiv_apply`.  ~20 lines.  Truth: clear.

**A4** `fderiv_oneForm_antisymm` (line 191) — `∂_u B − ∂_v A = D · m_k(Z)`.
Sketch: `rw [fderiv_oneForm_apply hk N hG x ev2 eu2, fderiv_oneForm_apply hk N hG x eu2 ev2,
Family.fderiv_fderiv_symm hG x eu2 ev2]`; the two `⟪N×G, G''…⟫` terms cancel; the rest is
`core_algebra (G x) (G'eu2) (G'ev2) N (k Z) (deriv k Z) (triple …) (hn x) hN (cross_fderiv_eq_smul hG hn x eu2 ev2)`
after `real_inner_comm` on `⟪G'c, N⟫`; unfold `mk`; `ring`/`linear_combination`.  ~30 lines.
Truth: checked symbolically in the feasibility report §2 and numerically (`m_k ≡ 1/(4π)` for `k = −1/(4π(1−Z))`).

**A5** `integral_fderiv_eu_eq_zero` (line 201) — `∫_a^{a+P} ∫_b^{b+P} ∂_u F = 0` for smooth `F` periodic in `(P,0)`.
Sketch: swap the order with `integral_integral_swap_of_continuous` (file line 454; integrand continuous by
`Family.contDiff_fderiv_apply`), then per `v`: `∫_a^{a+P} ∂_u F(u,v) du = F(a+P,v) − F(a,v)`
(`intervalIntegral.integral_eq_sub_of_hasDerivAt` with `Family.hasDerivAt_slice`-style lemma:
`hasDerivAt_sliceU` (file line 407) or `HasFDerivAt.comp_hasDerivAt` along `u ↦ (u,v)`), `= 0` by `hper (a, v)`
(`Prod.mk_add_mk`, `add_zero`); then `integral_zero`.  Pattern: `Family.integral_fderiv1_eq_zero` (file ~1146).
~35 lines.  Truth: clear.

**A6** `integral_fderiv_ev_eq_zero` (line 208) — same in the `v`-direction: inner FTC directly, `hper (u, b)`.  ~25 lines.

**A7** `integral_triple_mul_mk_eq_zero` (line 215) — `∫∫ D · m_k(Z) = 0`.
Sketch: `intervalIntegral.integral_congr` twice with `fderiv_oneForm_antisymm` (pointwise, `(u,v)`), split
with `intervalIntegral.integral_sub` (both pieces `IntervalIntegrable` by continuity from `contDiff_oneForm` +
`Family.contDiff_fderiv_apply`; the inner integrals are continuous in `u` by `continuous_parametric_integral`
(file 464) or `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous`), then
`integral_fderiv_eu_eq_zero (contDiff_oneForm hk N hG ev2) (periodic_oneForm k N hpu ev2)` and
`integral_fderiv_ev_eq_zero (contDiff_oneForm hk N hG eu2) (periodic_oneForm k N hpv eu2)`.  ~45 lines.
Truth: `Periodic G (P,0)` is the uncurried form of `∀ v, Periodic (fun u => G u v) P`; both used consistently.

**A8** `contDiff_cutoffK` (line 239) — `cutoffK χ` is `C^∞` on `ℝ`.
Sketch: `contDiff_iff_contDiffAt`; at `Z ≠ 1`: `ContDiffAt.div` of `(χ.contDiff.sub contDiff_const)` and
`contDiff_const.mul (contDiff_const.sub contDiff_id)` with denominator `≠ 0` (`Real.pi_pos`); at `Z = 1`:
`cutoffK χ =ᶠ[𝓝 1] 0` because `χ = 1` on `closedBall 1 χ.rIn` (`ContDiffBump.one_of_mem_closedBall`,
`Metric.closedBall_mem_nhds`), so `contDiffAt_const.congr_of_eventuallyEq`.  ~40 lines.
Truth: `cutoffK χ Z = (χ Z − 1)/(…) = 0/(…) = 0` on the ball, including at `Z = 1` (division by `0` is `0`).

**A9** `mk_cutoffK_one` (line 263) — the cutoff identity at `Z = 1`.
Sketch: LHS: `mk (cutoffK χ) 1 = 2·1·cutoffK χ 1 − (1 − 1^2)·deriv … = 2·cutoffK χ 1`, and `cutoffK χ 1 = 0`
(`χ 1 = 1` by `one_of_mem_closedBall (Metric.mem_closedBall_self χ.rIn_pos.le)`; `sub_self`, `zero_div`).
RHS: `deriv_bumpPhi`, `χ 1 = 1`, and `deriv (fun z => χ z) 1 = 0` since `(fun z => χ z) =ᶠ[𝓝 1] fun _ => 1`
(`Filter.EventuallyEq.deriv_eq`, `deriv_const`); then `field_simp`/`ring`.  ~25 lines.
Truth: both sides `0`; the `(1 − 1²)` factor kills the `deriv (cutoffK χ) 1` term regardless of its value.

**A10** `gaussIntegral_eq_shift` (line 277) — `gaussIntegral P G = (1/(4π)) ∫_a^{a+P}∫_b^{b+P} triple (uncurry G) eu2 ev2`.
Sketch: unfold `gaussIntegral`; `gaussDensity_eq_triple' hG` pointwise; the inner function
`v ↦ triple … (u,v)` is `P`-periodic (`gaussDensity_periodic` + the same rewrite, or `Family.periodic_triple`
with `Periodic (uncurry G) (0,P)`), so `∫_0^P = ∫_b^{b+P}` by `Function.Periodic.intervalIntegral_add_eq hf b 0`
(then `zero_add`); the outer function `u ↦ ∫_b^{b+P} …` is `P`-periodic likewise; shift to `a`.  ~40 lines.
Truth: `Periodic.intervalIntegral_add_eq : ∫ t..t+T = ∫ s..s+T` — exact statement checked (`#check` in /tmp/rpc_test0.lean).

**A11** `gaussIntegral_eq_integral_bump` (line 288) — STEP 1: `gaussIntegral P G = ∫∫ D · φ'(Z)`.
Sketch: `gaussIntegral_eq_shift`; pointwise `(1/(4π))·D = D·mk (cutoffK χ) Z + D·deriv φ Z` from `mk_cutoffK`
(`ring`); `intervalIntegral.integral_add` twice (integrability: `mk (cutoffK χ)` continuous as
`1/(4π) − deriv (bumpPhi χ)` with `bumpPhi` smooth, or via `contDiff_cutoffK`; `triple` continuous by
`Family.contDiff_triple`); `integral_triple_mul_mk_eq_zero (contDiff_cutoffK χ) hN hG' hn' hpu' hpv' a b`
with `G' = uncurry G`, `hpu' : Periodic (uncurry G) (P,0)` from `hpu` (`Prod.mk_add_mk`); `integral_const_mul`.
~50 lines.  Truth: `uncurry G (u,v) = G u v` definitionally; the statement's integrand uses `G u v` on purpose.

## U-B. Frame, chart Jacobian, inverse-function neighbourhoods

**B1** `exists_frame` (line 303) — positive orthonormal frame `(e₁, e₂, N)`, `cross e₁ e₂ = N`.
Sketch: some coordinate vector `E j := EuclideanSpace.single j 1` has `⟪N, E j⟫² < 1` (else `‖N‖² = 3`);
`w := cross N (E j)`, `‖w‖² = 1 − ⟪N,E j⟫² > 0` (`norm_cross_sq`); `e₁ := ‖w‖⁻¹ • w`, `e₂ := cross N e₁`;
`‖e₂‖ = 1` (`norm_cross_sq`, `⟪N,e₁⟫ = 0` by `inner_cross_self_left`); `⟪e₁,e₂⟫ = 0` (`inner_cross_self_right`);
`cross e₁ (cross N e₁) = ⟪e₁,e₁⟫•N − ⟪e₁,N⟫•e₁ = N` (`cross_cross_eq`).  ~60 lines.  Truth: standard.

**B2** `frame_parseval` (line 309) — Parseval `⟪x,e₁⟫² + ⟪x,e₂⟫² + ⟪x,N⟫² = ‖x‖²`.
Sketch: `y := x − ⟪x,e₁⟫•e₁ − ⟪x,e₂⟫•e₂` is `⊥ e₁, e₂`; `cross y N = cross y (cross e₁ e₂) = ⟪y,e₂⟫•e₁ − ⟪y,e₁⟫•e₂ = 0`
(`cross_cross_eq`), so `y = ⟪y,N⟫•N` (as in A1, with `‖N‖ = 1` from `norm_cross_sq`), `⟪y,N⟫ = ⟪x,N⟫`
(`N ⊥ e₁,e₂`: `inner_cross_self_*`); then `‖x‖² = ‖y‖² + ⟪x,e₁⟫² + ⟪x,e₂⟫²` by expanding `‖x‖² = ⟪x,x⟫`
with `x = y + ⟪x,e₁⟫•e₁ + ⟪x,e₂⟫•e₂` (`inner_add_left`, `real_inner_smul_*`).  Alternative: coordinates +
`nlinarith` is NOT recommended.  ~45 lines.  Truth: `(e₁,e₂,N)` is an orthonormal basis.

**B4** `det_eq_fin_two` (line 323) — `det f = (f(1,0)).1 (f(0,1)).2 − (f(0,1)).1 (f(1,0)).2` for `f : ℝ×ℝ →L ℝ×ℝ`.
Sketch: `ContinuousLinearMap.det` unfolds to `LinearMap.det ↑f`; `← LinearMap.det_toMatrix (Basis.finTwoProd ℝ)`,
`Matrix.det_fin_two`, `LinearMap.toMatrix_apply`, `Basis.finTwoProd_zero/one`; `(Basis.finTwoProd ℝ).repr (x,y) 0 = x`
etc. (`Basis.finTwoProd_repr`? else `Basis.repr_apply`/`Basis.finTwoProd` unfolds to `Basis.prod`, `Basis.prod_repr_inl`).
~30 lines.  Truth: the matrix has columns `f(1,0), f(0,1)`; `det = ad − bc`.

**B5** `det_chartDeriv` (line 330) — `det (chartDeriv x) = D x · Z x`.
Sketch: `det_eq_fin_two`; `chartDeriv … w = (⟪e₁, G'w⟫, ⟪e₂, G'w⟫)` (`ContinuousLinearMap.prod_apply`,
`comp_apply`, `innerSL_apply`); the expression is `⟪cross e₁ e₂, cross (G'eu2) (G'ev2)⟫` by `inner_cross_cross'`
(read right to left), `= ⟪N, triple•G x⟫ = triple · ⟪N, G x⟫` (`hN`, `cross_fderiv_eq_smul`, `real_inner_smul_right`,
`real_inner_comm`).  ~35 lines.  Truth: Binet–Cauchy orientation matches `(e₁,e₂,N)` positive.

**B6** `exists_strict_equiv_chart` (line 339) — invertible strict derivative of the chart at a regular preimage.
Sketch: `det (chartDeriv p) = D p · ⟪N,N⟫ = D p ≠ 0` (`det_chartDeriv`, `hp`, `real_inner_self_eq_norm_sq`, `hNu`);
`e := (LinearMap.equivOfDetNeZero (chartDeriv p : ℝ×ℝ →ₗ[ℝ] ℝ×ℝ) h).toContinuousLinearEquiv`; `(e : →L) = chartDeriv p`
by `ContinuousLinearMap.ext` + `rfl`; `HasStrictFDerivAt`: `(contDiffAt_chart).hasStrictFDerivAt (by simp)`
where `ContDiffAt ℝ ∞ (chart …) p` from `hG.inner`/`ContDiff.prodMk`, and `fderiv = chartDeriv` by
`(hasFDerivAt_chart e₁ e₂ hG p).fderiv`; or directly `HasFDerivAt` + `ContDiffAt` ⇒ strict (`ContDiffAt.hasStrictFDerivAt'`).
~45 lines.  Truth: `LinearMap.equivOfDetNeZero` (Determinant.lean:567) exists; `toContinuousLinearEquiv` (FiniteDimension.lean:368).

**B7** `exists_regular_nhd` (line 351) — the inverse-function neighbourhood at `p`.
Sketch: `obtain ⟨e, he⟩ := exists_strict_equiv_chart …`; `Φ := he.toOpenPartialHomeomorph (chart …)`;
`p ∈ Φ.source` (`mem_toOpenPartialHomeomorph_source`), `Φ.open_source`, `Φ.injOn` (`PartialEquiv.injOn`; `Φ = chart` as
functions by `toOpenPartialHomeomorph_coe`); `U' := interior U` or from `mem_nhds_iff`; `W₁ := {x | 0 < Z x}` open
(`isOpen_lt continuous_const (hG.continuous.inner continuous_const)`), `p ∈ W₁` (`Z p = ⟪N,N⟫ = 1`);
`W₂ := {x | 0 < D x}` or `{x | D x < 0}` according to the sign of `D p` (`Family.contDiff_triple` continuous;
`Real.sign_of_pos/neg`); `V := Φ.source ∩ U' ∩ W₁ ∩ W₂`; `V ∈ 𝓝 p`; `chart '' V ∈ 𝓝 (chart p)` by
`he.map_nhds_eq_of_equiv ▸ image_mem_map`; `chart p = 0` (`⟪e₁,N⟫ = 0`, `⟪e₂,N⟫ = 0` from `hN` and
`inner_cross_self_*`); `Metric.mem_nhds_iff`.  ~80 lines.  Truth: standard IFT consequences.

**B8** `exists_disjoint_balls` (line 362) — disjoint equal-radius balls around a finite set inside an open `W`.
Sketch: for each `p ∈ S` pick `ε_p` with `ball p ε_p ⊆ W` (`Metric.isOpen_iff`); let `m := ` the minimum of
`ε_p` over `S` and of `dist p q / 2` over distinct pairs (`Finset.exists_min_image` on `S` and on
`(S ×ˢ S).filter (·.1 ≠ ·.2)`, or `Finset.inf'`); `S = ∅` ⇒ `r = 1`.  Disjointness: `Metric.ball_disjoint_ball`
(`r + r ≤ dist p q`).  ~60 lines.  Truth: finite minimum of positives is positive.

**B9** `exists_nhdSystem` (line 393) — THE NEIGHBOURHOOD SYSTEM (`Nonempty (NhdSystem …)`).
Sketch: `exists_disjoint_balls S (isOpen_Ioo.prod isOpen_Ioo) hSint` ⇒ `r₀`; for `p ∈ S`,
`exists_regular_nhd hN hNu hG hn ((hS p _).mpr hp) (hreg p hp) (Metric.ball_mem_nhds p hr₀)` ⇒ `V p, r p`
(use `Classical.choose` after `choose` on `∀ p, p ∈ S → ∃ …`; set `V p := ∅` off `S`); `r := ` min of `r p` over `S`
(`Finset.exists_min_image`, `S = ∅` ⇒ `1`); `K := (Icc a (a+P) ×ˢ Icc b (b+P)) \ ⋃ p ∈ S, V p` compact
(`(isCompact_Icc.prod isCompact_Icc).diff (isOpen_biUnion …)`); on `K`, `G x ≠ N` (else `x ∈ S` by `hS`, so
`x ∈ V x ⊆ ⋃`), hence `Z x < 1` (`inner_lt_one_of_ne (hn x) hNu`); `exists_delta_of_compact hG.continuous hK` ⇒ `δ`;
assemble the structure.  ~120 lines.  Truth: the empty-`S` case gives an empty union and any `δ` from the
compact box (the lemma handles it).

## U-C. Change of variables on one neighbourhood; polar normalisation

**C1** `deriv_bumpPhi_eq_zero_of_lt` (line 410) — `deriv (bumpPhi χ) Z = 0` for `Z < 1 − rOut`.
Sketch: on `Iio (1 − rOut)` (open, `∋ Z`) `χ = 0` by `ContDiffBump.zero_of_le_dist` (`dist z 1 = 1 − z ≥ rOut`),
so `bumpPhi χ =ᶠ[𝓝 Z] 0`; `Filter.EventuallyEq.deriv_eq`, `deriv_const`.  ~20 lines.  Truth: strict `<` is
essential (at `Z = 1 − rOut` the argument needs one-sided derivatives; the consumers D3, C3, C6 only use strict).

**C2** `chartDensity_chart` (line 417) — `ψ (F x) = φ'(Z)/Z` when `Z > 0`.
Sketch: `frame_parseval … (G x)` with `hn x` gives `⟪e₁,G x⟫² + ⟪e₂,G x⟫² = 1 − Z²` (after `real_inner_comm`);
`1 − Z² < 1`; unfold `chartDensity`, `if_pos`; `√(1 − (1 − Z²)) = √(Z²) = Z` (`Real.sqrt_sq hx.le`).  ~35 lines.
Truth: `chart` is `(⟪e₁, G x⟫, ⟪e₂, G x⟫)` (this order, matching `innerSL`).

**C3** `chartDensity_mem_ball` (line 426) — `ψ w ≠ 0 → w ∈ ball 0 r` when `0 < r`, `2·rOut ≤ r²`.
Sketch: from `hw`, `w.1² + w.2² < 1` and `deriv φ (√(1 − s)) ≠ 0` (`s := w.1²+w.2²`), so by contraposition of
`deriv_bumpPhi_eq_zero_of_lt`, `1 − rOut ≤ √(1 − s)`; if `1 − rOut ≥ 0` square: `(1 − rOut)² ≤ 1 − s`, so
`s ≤ 2 rOut − rOut² < 2 rOut ≤ r²`; if `1 − rOut < 0` then `s < 1 < 2 rOut ≤ r²` (as `rOut > 1`); finally
`‖w‖ = max |w.1| |w.2|` (`Prod.norm_def`, `Real.norm_eq_abs`) and `|w.i|² ≤ s < r²` ⇒ `|w.i| < r`
(`abs_lt_of_sq_lt_sq`/`pow_lt_pow_left`), `Metric.mem_ball, dist_zero_right`.  ~40 lines.  Truth: checked
both branches; `0 < r` is needed (added) since `ball 0 r = ∅` for `r ≤ 0`.

**C4** `integral_bump_on_nhd` (line 436) — `∫_V D·φ'(Z) = sign(D p) · ∫_{ℝ²} ψ`.
Sketch: RHS: `∫ ψ = ∫_{chart '' V} ψ` (`setIntegral_eq_integral_of_forall_compl_eq_zero`: off `chart '' V ⊇ ball 0 r`,
`ψ = 0` by contraposition of `hsupp`); `integral_image_eq_integral_abs_det_fderiv_smul volume hV.measurableSet
(fun x _ => (hasFDerivAt_chart e₁ e₂ hG x).hasFDerivWithinAt) hinj ψ`; pointwise on `V`:
`|det (chartDeriv x)| • ψ (chart x) = |D x · Z x| · φ'(Z x)/Z x` (`det_chartDeriv`, `chartDensity_chart`)
`= |D x| · φ'(Z x)` (`abs_mul`, `abs_of_pos (hZ x hx)`, `Z ≠ 0`) `= sign(D p) · D x · φ'(Z x)`
(`|D x| = sign (D x) * D x`: `Real.sign_mul_self`-type — prove by `rcases lt_trichotomy (D x) 0` with
`Real.sign_of_pos/neg/zero`; then `hsgn x hx`); pull the constant out (`integral_const_mul`/`setIntegral_congr_fun`);
conclude `∫ψ = sign(D p) · LHS`, and multiply by `sign(D p)` using `sign(D p)² = 1` (`hD`, `Real.sign_of_pos/neg`).
~110 lines.  Truth: if `D p = 0` the statement would still hold but the proof needs `hD` (included).

**C5** `integral_chartDensity_eq_radial` (line 451) — `∫_{ℝ²} ψ = 2π ∫_{ρ>0} ρ ψ(ρ,0)`.
Sketch: `← integral_comp_polarCoord_symm (chartDensity χ)`; `polarCoord_target`; `polarCoord_symm_apply`;
`chartDensity χ (ρ cos θ, ρ sin θ) = chartDensity χ (ρ, 0)` (`mul_pow`, `cos_sq_add_sin_sq`, `ring_nf` inside the
`if`); `Measure.volume_eq_prod`, `Measure.prod_restrict`, `setIntegral_prod` (integrability: the integrand is
bounded—`rOut < 1` makes `ψ = 0` for `1 − s < (1 − rOut)²`, so `ψ` is bounded by `sup |φ'| / (1 − rOut)`—and
supported in `ρ < 1`; `Measurable` via `Measurable.ite`, `measurableSet_lt`, continuity of `deriv (bumpPhi χ)` and `√`);
inner integral `∫_{Ioo (−π) π} c = 2π·c` (`setIntegral_const`, `Real.volume_Ioo`, `sub_neg_eq_add`, `two_mul`);
`integral_const_mul`.  ~90 lines.  Truth: `chartDensity χ (ρ,0)` uses `ρ² + 0²`; sign of `2π`: `volume (Ioo (−π) π) = π − (−π) = 2π`.

**C6** `integral_radial` (line 461) — `∫_{ρ>0} ρ ψ(ρ,0) = 1/(2π)`.
Sketch: `ρ₁ := √(1 − (1 − rOut)²)`, `0 < ρ₁ < 1`; split `Ioi 0 = Ioc 0 ρ₁ ∪ Ioi ρ₁` (`setIntegral_union`, or
`intervalIntegral.integral_of_le` + `setIntegral_eq_zero_of_forall_eq_zero` on `Ioi ρ₁`: for `ρ₁ < ρ < 1`,
`√(1 − ρ²) < 1 − rOut` ⇒ `deriv φ … = 0` by `deriv_bumpPhi_eq_zero_of_lt`; for `ρ ≥ 1`, `if_neg`);
on `[0, ρ₁]`: `H ρ := bumpPhi χ (√(1 − ρ²))` has `HasDerivAt H (deriv φ (√(1−ρ²)) · (−ρ/√(1−ρ²)))` for `ρ² < 1`
(`Real.hasDerivAt_sqrt`, `HasDerivAt.comp` with `hasDerivAt_bump`-style `((χ.contDiff).differentiable …)` for `bumpPhi`,
`hasDerivAt_id`, `HasDerivAt.const_sub`, `HasDerivAt.pow`); on `Ioc 0 ρ₁` the integrand equals `−H'`
(`if_pos`, `div_eq_mul_inv`); `intervalIntegral.integral_eq_sub_of_hasDerivAt` (continuity of `H'` on `[0,ρ₁]` from
`ρ₁ < 1`); `H 0 = φ(1) = 2·χ 1/(4π) = 1/(2π)` (`Real.sqrt_one`, `one_of_mem_closedBall`), `H ρ₁ = φ(1 − rOut) = 0`
(`Real.sqrt_sq (1 − rOut ≥ 0)`, `zero_of_le_dist`).  ~120 lines.  Truth: Python quadrature with a concrete
smooth bump (`rIn = 0.1, rOut = 0.3`) gives `0.15915494…` = `1/(2π)` to 10 digits.

## U-D. Assembly

**D1** `integral_box_eq_setIntegral` (line 481) — `∫_a^{a'}∫_b^{b'} f(u,v) = ∫_{Icc a a' ×ˢ Icc b b'} f`.
Sketch: `intervalIntegral.integral_of_le ha/hb`, `setIntegral_congr_set Ioc_ae_eq_Icc` (twice, inside the outer
integral via `integral_congr`), `(setIntegral_prod _ hI).symm` with `hI : IntegrableOn f (Icc a a' ×ˢ Icc b b')`
(`hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)`), `Icc_prod_Icc`.  Copy of
`DivergenceTheorem.lean:530-540`.  ~25 lines.  Truth: verbatim Mathlib pattern.

**D2** `setIntegral_box_eq_sum` (line 490) — box integral = `∑_{p∈S} ∫_{V p} f` when `f = 0` on `box ∖ ⋃ V p`.
Sketch: `setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_Icc.prod measurableSet_Icc)
(iUnion₂_subset hVsub) hzero` (note `⋃ p ∈ S` as `⋃ p, ⋃ (_ : p ∈ S)`), then `integral_biUnion_finset S
(fun p hp => (hVo p hp).measurableSet) (pairwise from hdisj: Set.Pairwise (↑S) (Disjoint on V)) (fun p hp =>
hI.mono_set (hVsub p hp))`.  ~45 lines.  Truth: hypotheses of `integral_biUnion_finset` checked (Bochner/Set.lean:120).

**D3** `integral_bump_eq_sum_of_system` (line 504) — MAIN LEMMA: `∫∫ D·φ'(Z) = ∑_{p∈S} sign(D p)`.
Sketch: `integral_box_eq_setIntegral` (continuity: `Family.contDiff_triple`, `bumpPhi` smooth ⇒ `deriv` continuous,
`inner`), `le_add_of_nonneg_right hP.le`; `setIntegral_box_eq_sum` with `V := sys.V`, `sys.V_isOpen`,
`sys.V_subset` (then `Ioo ⊆ Icc`), `sys.disjoint_V`, and `hzero`: for `x` in the box off the union, `sys.small`
gives `Z x < 1 − δ ≤ 1 − rOut`, so `deriv_bumpPhi_eq_zero_of_lt` ⇒ integrand `0` (`mul_zero`);
`Finset.sum_congr rfl`: per `p ∈ S`, `integral_bump_on_nhd χ h₁ h₂ h₁₂ hN hG hn (hreg p hp) (sys.V_isOpen p hp)
(sys.injOn_V p hp) (sys.pos_V p hp) (sys.sign_V p hp) (sys.ball_subset p hp) (fun w hw =>
chartDensity_mem_ball χ sys.r_pos hχr hw)`, then `integral_chartDensity χ hχ₁`, `mul_one`.  ~80 lines.
Truth: `sys.r_pos` supplies `0 < r` for C3; `hχδ`, `hχr`, `hχ₁` are exactly what the glue provides.

**D4** `exists_shift` (line 520) — SHIFT of the fundamental domain.
Sketch: `T := hfin.toFinset`; `A := T.image Prod.fst`, `B := T.image Prod.snd` finite, so pick `a ∈ Ioo 0 P \ A`,
`b ∈ Ioo 0 P \ B` (`Set.Ioo.infinite`/`(Set.Ioo_infinite hP).exists_not_mem_finset`); `τ p := (p.1 + if p.1 < a then P else 0,
p.2 + if p.2 < b then P else 0)`; `S := T.image τ`.  (i) `x ∈ S → x ∈ Ioo × Ioo`: case split on the `if`s, using
`p ∈ Ico 0 P`, `a ∉ A`, `b ∉ B` for strictness.  (ii) `G x = N ↔ x ∈ S` on the closed box: `←` from (i) and
periodicity (`hpu`, `hpv`); `→`: reduce `x` to `q := (x.1 − if x.1 ≥ P then P else 0, …) ∈ Ico 0 P ×ˢ Ico 0 P`
with `G q = N` (periodicity), so `q ∈ T`; `x.1 ≠ a, a+P` because `q.1 ∉ A`; hence `τ q = x`.  (iii) the sum:
`Finset.sum_image` (`τ` injective on `T`: coordinates in `[0,P)` are recovered mod `P`) and
`gaussDensity_periodic` for `sign D (τ p) = sign D p`.  ~130 lines.  Truth: checked case by case in the
feasibility report §2 Step 3; `P > 0` is used for `Ioo 0 P` nonempty/infinite.

## The corollary

`SM.crossing_formula_unconditional` (skeleton line 570):
`DisjointPair P C₁ C₂ → GenericDirection C₁ C₂ ν →
linking P C₁ C₂ = (1/2) * ∑ᶠ p ∈ mixedCrossings P C₁ C₂ ν, lcCrossingSign C₁ C₂ ν p`,
proved as `crossing_formula_of_regularPoleCount regularPoleCount h hν`.  This is sm-3:2802-2804 with the
isolated hypothesis discharged.  A structure-level `fd_linking_calculus_unconditional` (the field
`crossing_formula` without the `RegularPoleCount →` antecedent) would require editing the statement of
`LinkingCalculusData` in `SM/LinkingCalculus.lean`, which is the executor's call; the derived theorem above is
the statement-preserving form and is what the row's report should cite.

## Risks and what to watch

* U-C is the API-heaviest unit (change of variables, polar coordinates, measurability of `chartDensity`); if
  `integral_comp_polarCoord_symm`'s integrability bookkeeping is painful, an alternative for C5/C6 is to
  compute `∫ ψ` on `EuclideanSpace ℝ (Fin 2)` via `MeasureTheory.Measure.integral_fun_norm_addHaar`
  (`HaarToSphere.lean`) — but then `chart` must land there instead of `ℝ × ℝ`; do not switch unless stuck.
* B4 depends on how `Basis.finTwoProd` exposes `repr`; if awkward, state the `2×2` determinant through
  `LinearMap.toMatrix` with `Fin 2 → ℝ` and `ContinuousLinearEquiv.finTwoArrow`.
* All leaves are stated with the hypotheses the glue actually supplies (checked by compilation of
  `regularPoleCount`); do not weaken conclusions or strengthen hypotheses without re-running the skeleton.
* Names in `SM.LinkingCalculus` used by the leaves: `Family.triple`, `Family.contDiff_triple`,
  `Family.contDiff_fderiv_apply`, `Family.hasFDerivAt_fderiv_apply`, `Family.fderiv_triple_apply`,
  `Family.inner_fderiv_eq_zero`, `Family.fderiv_fderiv_symm`, `Family.fderiv_periodic`,
  `Family.periodic_fderiv_apply`, `Family.periodic_triple`, `integral_integral_swap_of_continuous`,
  `continuous_parametric_integral`, `hasDerivAt_sliceU/V`, `pderivU_eq_fderiv`, `pderivV_eq_fderiv`,
  `cross_*`, `inner_cross_*`, `norm_cross_sq`, `HasFDerivAt.cross`, `ContDiff.cross`.
