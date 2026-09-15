# TN_PLAN.md — leaf plan for `TN_Skeleton.lean` (row 84 fd:transverse-neighborhood)

Date: 2026-09-14.  Skeleton: `work/drafts/fd/TN_Skeleton.lean` (959 lines; 0 errors; 40 leaves
with `sorry`; statement part lines 27-198 byte-identical to `TransverseNeighborhood.lean` 67-238;
`#print axioms SM.fd_transverse_neighborhood` = `[propext, sorryAx, Classical.choice, Quot.sound]`,
the `sorryAx` only through the leaves; `moser_identity`, `alphaT_Vf` are axiom-clean).
Check: `cd work/lean && lake env lean ../drafts/fd/TN_Skeleton.lean`.  Route: `FD_84_87_FEASIBILITY_v2.md` §1.
Line numbers below are the `theorem` lines in the skeleton.

Notation: torus coordinates `p = (θ, w) : ℝ × ℝ²`, `u = w 0`, `v = w 1`; `alpha p v = v 2 − p 1 * v 0`;
`alpha0 w τ η = τ + w 0 * η 1 − w 1 * η 0`; `aT T θ = α(T′)`, `cT = √(2aT)`, `chart T` = the paper's `F`;
`gfun T` = `g`, `Pf = 1 + t g`, `Nf = 2P − t g_u(1−t)u − t g_v(1+t)v`, `Vf` = `V_t` (closed form),
`muf` = `μ_t`, `alphaT t` = `α_t`, `nuF` = `ν`, `dalphaT t` = `dα_t`; `Yfield` the suspended cut-off
field on `ℝ × (ℝ × ℝ²)`, `Theta` its flow, `Phi t p = (Theta t (0,p)).2`; `Hmap = chart ∘ Phi 1 ∘ (θ-reduction)`,
`hfun = aT(θ(Φ₁p)) · exp ∫₀¹ μ_t(Φ_t p)`; `helix N b θ = b(cos Nθ, −sin Nθ)`; `annulus0 N b κ (θ,s) = (θ+κs, helix N (b−s) θ)`;
`Vamb`, `pushfwd`, `Psi` the paper's `V`, `X = H_*V`, `Ψ`.

## 0. Numerical truth checks performed (pure-python finite differences, `/tmp/fd/probe_tn2.py`)

Curve `T = (cos θ, sin θ + 0.3 sin 2θ, sin 2θ/4 + 0.05 sin θ + 0.05 sin 3θ)`, `a(θ) = 1/2 + 0.2 cos θ`
(non-constant `a`, `c′ ≠ 0`).  (a) `pullback_chart`: `α(F)(DF ξ) = a((1+g)ξ_θ − 2vξ_u)`, max error
`2·10⁻¹⁰` over 20 random points; (b) `dalphaT_eq` (antisymmetrised derivative), error `3·10⁻⁶`
(nested FD noise); (c) annulus `B^*α₀ = (1 − N(b−s)²)dθ + κ ds`, error `3·10⁻¹⁰`, negative for
`s < 0`, positive for `0 < s < b`; (d) `α₀(L₀′) = 1 − Nb² = 0` to `4·10⁻¹¹`; (e) RK4 integration of
`ṗ = V_t(p)`: `α_t(Φ_t p)(DΦ_t w)·e^{−∫₀ᵗμ}` constant to 6 digits at `t = 0, ¼, ½, ¾, 1`
(= `α₀(p)(w) = 0.293000`), which validates the sign of `ν`, the closed forms and D1–D2 together;
(e′) `‖V‖/‖w‖ ≤ 0.76` and `N > 1`, `P > 1/2` on `|w| ≤ 0.02`, `|t| ≤ 4` (at `|w| ≤ 0.1` the margin
`N > 1` FAILS for this `T` — the radius must be small: existence only, no fixed constant in the leaves);
(f) end-to-end `α(H)(DH ξ) = h·α₀(p)(ξ)` with `H = F∘Φ₁`: `0.27062384` vs `0.27062384`.
The Moser identities themselves are proved in Lean (`MoserIdentityCheck.lean`, `moser_identity`, `alphaT_Vf`).

## 1. Unit table

| unit | leaves | depends on | est. lines | content |
|---|---|---|---|---|
| A chart | A1–A7 (7) | — | 700 | `F` smooth, periodic, `DF`, uniform IFT radius, injectivity radius, open images, `F^*α = a·β` |
| B forms/field | B1–B6 (6) | — | 500 | `g` smooth/periodic, `dα_t` as antisymmetrised derivative, `P, N` margins, `V` smooth on the tube, `‖V‖ ≤ C‖w‖` |
| C flow | C1–C9 (9) | B (defs) | 1 000 | `Y` smooth/compact support, `τ = t`, ODE of `Φ`, `Φ₁` diffeo, Grönwall a-priori radius, periodicity of `Φ`, core fixed, variational equation |
| D model | D1–D7 (7) | A, B, C | 900 | pullback ODE, its solution, local form of `H`, `H^*α = hα₀`, injective/immersion/open |
| E Legendrian & annulus | E1–E7 (7) | statement only | 550 | `N, b`, helix norm, `α₀(L₀′) = 0`, `L` Legendrian/embedded, the annulus, the transverse isotopy |
| F ambient isotopy | F1–F4 (4) | statement only | 500 | pushforward value, smoothness, compact support, tracked helix |
| PROVED in skeleton | — | — | ≈ 250 | Moser identities, `exists_goodRadius`, flow existence/smoothness, `Hmap_smoothOn/periodic/core`, `model`, `exists_legendrian`, `ambientIsotopy`, `carries`, row theorem |
| total | 40 | | ≈ 4 150 | (memo estimate 3 500; the split into independent leaves costs interface glue) |

Cross-dependencies: E and F need only the statement structures (`IsTransverseModel` etc.) — fully
parallel with A–D.  D needs C9/C4/C6 (flow) and A7/A-radii/B3.  C needs B1/B5/B6 (smoothness and
bound of `V`).  Within a unit the order listed is a sensible order.

## 2. Leaves

Format: **id `name` (line)** — statement in words · proof sketch · Mathlib · size · truth.

### Unit A
- **A1 `contDiff_chart` (260)** — `F` is `C^∞` · `T` smooth ⇒ `deriv T` smooth (`ContDiff.iterate_deriv`/`contDiff_top_iff_deriv`), `aT` smooth (`alpha` bilinear in coordinates via `PiLp.proj`), `cT = √(2 aT)` smooth since `aT > 0` (`ContDiff.sqrt`), `E1`, `E2` smooth (`contDiff_euclidean`/`!₂` components), sums and `smul` · `ContDiff.smul`, `ContDiff.add`, `contDiff_fst/snd`, `EuclideanSpace.proj` · 80 · trivially true.
- **A2 `chart_periodic` (265)** — `aT, cT, deriv T, F` are `2π`-periodic · `deriv_comp_add_const`: `deriv (fun x => T (x + c)) θ = deriv T (θ + c)` and `T (· + 2π) = T` · `Function.Periodic`, `deriv_comp_add_const` · 40 · true.
- **A3 `fderiv_chart` (272)** — explicit `DF(θ,w)(τ,η)` · chain/product rule on `T + cT • (u E1(T) + v E2)`, `E1(T θ) = (1,0,y_T)` has θ-derivative `(0,0,y′)`; `fderiv` of `p ↦ p.2 0` is `(τ,η) ↦ η 0` · `HasFDerivAt.smul`, `HasFDerivAt.add`, `hasFDerivAt_fst/snd`, `HasDerivAt.comp_hasFDerivAt` · 150 · true (checked as part of probe (a)).
- **A4 `exists_chart_bij_radius` (283)** — uniform radius with `DF` bijective · at `w = 0`: `DF(τ,η) = τT′ + c(η₀E1 + η₁E2)`, injective (apply `alpha`: `τ a = 0`; then coordinates 0,1); linear injective on `ℝ×ℝ² → ℝ³` (`finrank 3 = 3`) ⇒ bijective (`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`); the set of `p` with `det(DF p) ≠ 0` is open (`ContinuousLinearMap.continuous_det`, `ContDiff.continuous_fderiv`); it contains the compact `Icc 0 (2π) × {0}` ⇒ a uniform `ρ` by `generalized_tube_lemma`; periodicity (A2) extends to all `θ` · 250 · true (sm-3:2419-2422).
- **A5 `exists_chart_inj_radius` (288)** — injectivity radius · by contradiction with `ρ = 1/(n+1)`: pairs `(θₙ,wₙ) ≠ (θₙ′,wₙ′)` mod `2π` with equal images and `‖wₙ‖,‖wₙ′‖ → 0`; reduce `θ` to `[0,2π]`, `IsCompact.tendsto_subseq` twice; continuity gives `T θ* = T θ*′` ⇒ `θ*′ ≡ θ*` (T embedded) ⇒ both sequences eventually lie in the source of `HasStrictFDerivAt.toOpenPartialHomeomorph` at `(θ*,0)` (A4 gives `DF` invertible there) where `F` is injective — contradiction · `IsCompact.tendsto_subseq`, `OpenPartialHomeomorph.injOn`, `Metric.tendsto_atTop` · 300 · true (sm-3:2422-2427).
- **A6 `chart_isOpen_image` (295)** — open sets in the good tube map to open sets · pointwise `HasStrictFDerivAt.map_nhds_eq_of_equiv` with the equiv from bijectivity (`ContinuousLinearEquiv.ofBijective`), then `isOpen_iff_mem_nhds` · 80 · true.
- **A7 `pullback_chart` (732)** — `α(F p)(DF p ξ) = a((1+g)ξ_θ − 2vξ_u)` · A3 + `alpha` linear: `α_F(cE1) = c(y_T − y_F) = −c²v = −2av`, `α_F(cE2) = 0`, `α_F(∂_θF) = a + c u y′ − c v x′ − c c′ u v` (memo §1.2), divide by `a` · `alpha` linearity lemmas (as `ContactMotions.alpha_add/alpha_smul`) · 150 · **numerically verified** (probe (a), err `2·10⁻¹⁰`).

### Unit B
- **B1 `contDiff_gfun` (395)** — `g` smooth · quotient of smooth by `aT > 0` (`ContDiff.div`), A1's pieces · 60 · true.
- **B2 `gfun_periodic` (405)** — `g, g_u, g_v` periodic · A2 for `g`; `fderiv` of a periodic function is periodic (`fderiv_comp_add_const`-type argument on `ℝ × ℝ²` with the shift `(2π, 0)`) · 60 · true.
- **B3 `dalphaT_eq` (422)** — `dα_t(x,y) = D_pα_t[x](y) − D_pα_t[y](x)` · `fderiv` of `q ↦ Pf t q * y.1 − (1+t) q.2 1 * y.2 0 + (1−t) q.2 0 * y.2 1` is `x ↦ t·Dg[x] y.1 − (1+t) x.2 1 y.2 0 + (1−t) x.2 0 y.2 1`; `Dg[x] = g_θ x.1 + g_u x.2 0 + g_v x.2 1` (`fderiv` on a product, `Pi` basis of `ℝ²`); antisymmetrise, `g_θ` cancels, `−(1+t) + (1−t)`-terms give `2(x_u y_v − x_v y_u)`; `ring` · `fderiv_add/sub/mul_const`, `EuclideanSpace` basis expansion `w = w 0 • single 0 1 + w 1 • single 1 1` · 150 · **numerically verified** (probe (b)).
- **B4 `exists_PN_radius` (429)** — `P > 1/2`, `N > 1` on a uniform tube for `|t| ≤ 4` · `P = 1`, `N = 2` on the core (`Pf_core`, `Nf_core`); `(t,θ,w) ↦ P, N` continuous (B1, `contDiff_gu/gv`); compact `Icc (−4) 4 × Icc 0 (2π) × {0}` ⇒ `generalized_tube_lemma`; periodicity (B2) in `θ` · 150 · true (probe (e′) at small radius; NOT true at `|w| ≤ 0.1` for the test curve — the leaf is existential, fine).
- **B5 `contDiffOn_Vf` (468)** — `V` jointly smooth where `N ≠ 0` · `ContDiffOn.div` with `Nf ≠ 0` from `GoodRadius.N_pos` (on the closed `2ρ`-tube, so on the open one), components via `!₂` · 100 · true.
- **B6 `exists_Vf_bound` (474)** — `‖V_t(θ,w)‖ ≤ C‖w‖` on the `2ρ`-tube · closed forms: `|2uv/N| ≤ 2‖w‖²/1 ≤ 4ρ‖w‖`, `|u(1+g)/N| ≤ (1+G)‖w‖`, `|v(g−1)/N| ≤ (1+G)‖w‖` with `G = sup|g|` on the compact tube (`IsCompact.exists_bound_of_continuousOn`, periodicity) · `EuclideanSpace.norm_eq`, `Prod.norm_def`/`norm_prod_le_iff`, `abs_le` · 120 · true (probe (e′): ratio `≤ 0.76`).

### Unit C
- **C1 `contDiff_Yfield` (523)** — `Y` smooth · `contDiff_iff_contDiffAt`; at `(τ,p)` with `‖p.2‖ < 2ρ` and `|τ| < 4`: `Y` is a product of smooth functions (`contDiff_cut1`, `contDiff_norm_sq`, B5 at the point) · at other points `Y = (χ_τ τ, 0)` on a neighbourhood (`cutoff = 0` for `‖w‖ ≥ ρ`, `χ_τ = 0` for `|τ| ≥ 3`; use `ContDiffAt.congr_of_eventuallyEq`) · `ContDiffOn.contDiffAt`, `Filter.eventually_of_mem` · 150 · true.
- **C2 `hasCompactSupport_Yfield` (528)** — support in `Icc (−3) 3 × Icc (−21) 21 × closedBall 0 ρ` · `HasCompactSupport.intro` (`isCompact_Icc.prod (isCompact_Icc.prod (isCompact_closedBall _ _))`), `cut1_of_ge` · 60 · true.
- **C3 `Theta_fst` (560)** — `pr₁Θ_t(0,p) = t` on `[−2,2]` · `τ(t) := (Θ_t(0,p)).1` solves `τ′ = χ_τ(τ)`, `τ(0) = 0` (`HasDerivAt.fst` of the flow ODE); `σ(t) = t` solves the same ODE on `Ioo (−2) 2` (`chiTau_eq_one`); `ContactMotions.ODE_unique_Ioo` with `χ_τ` Lipschitz (smooth with bounded derivative: `lipschitzWith_of_nnnorm_fderiv_le`, or `ContDiff.locallyLipschitz` + compactness); extend to the closed interval by continuity · 120 · true.
- **C4 `hasDerivAt_Phi` (566)** — `∂_tΦ_t(p) = cutoff(Φ_t p) • V_t(Φ_t p)` for `|t| < 2` · `(isGlobalFlow_Theta).hasDerivAt t (0,p)` projected to the second component (`HasDerivAt.snd`), rewrite `Yfield`, C3 (`τ = t`), `chiTau_eq_one` · 60 · true.
- **C5 `Phi_one_inverse` (573)** — `Φ₁` is a diffeomorphism · inverse `Ψ p′ = (Θ_{−1}(1,p′)).2`; `Θ_{−1}(Θ_1(0,p)) = (0,p)` (`IsGlobalFlow.neg_apply` with a Lipschitz constant from `exists_lipschitzWith_of_hasCompactSupport'`); C3 gives `Θ_1(0,p) = (1, Φ₁p)`; conversely `Θ_{−1}(1,p′)` has first component `0` (C3 reversed: apply C3 to `t = −1`… note `Θ_{−1}(1,p′) = Θ_{−1}(Θ_1(0, Ψ p′))` — prove `(Θ_{−1}(1,p′)).1 = 0` from the τ-ODE as in C3) · smoothness: `contDiff_Theta` composed · 150 · true.
- **C6 `exists_aprioriRadius` (588)** — Grönwall a-priori bound (sm-3:2456-2463) · with `C` from B6 set `δ₁ := ρ e^{−3C}/8`; continuation: let `S = {t ∈ [0,2] : ∀ s ∈ [0,t], ‖w(s)‖ ≤ ρ/4 ∧ |θ(s) − θ₀| ≤ 1}`, closed, contains `0`; on `S` the cutoff is `1` so `w′ = V^w`, `‖w′‖ ≤ C‖w‖` ⇒ `‖w(t)‖ ≤ e^{Ct}‖w₀‖ ≤ e^{2C}δ₁ < ρ/8` (`norm_le_gronwallBound_of_norm_deriv_right_le` with `δ = ‖w₀‖, K = C, ε = 0`, `gronwallBound_ε0`), and `|θ′| = |2uv/N| ≤ 2‖w‖² ≤ ρ²/8 ≤ 1/8` (`ρ ≤ 1`, `N > 1`) ⇒ `|θ(t) − θ₀| ≤ 1/4`; strict margins ⇒ `S` is also open in `[0,2]` ⇒ `S = [0,2]`; mirror for `[−1,0]` · `norm_le_gronwallBound_of_norm_deriv_right_le`, `isClosed_Icc`, `IsPreconnected.eq_univ`-style or `csSup` argument · 300 · true (probe (e′)); the constants `20` (θ-cutoff), `4π + 1 < 20` (`Real.pi_le_four`) are checked in `cutoff_along` (proved).
- **C7 `Phi_shift` (606)** — `Φ_t(θ₀+2π, w₀) = Φ_t(θ₀,w₀) + (2π,0)` for `|θ₀| ≤ 2π` · both curves solve `ṗ = cutoff(p)•V_t(p)` on `[−1,2]` (C4; `cutoff = 1` along both by C6/`cutoff_along` since `|θ₀ + 2π| ≤ 4π`; `Vf_periodic`); same initial value; uniqueness for the time-dependent field: use the uniqueness of `Θ` (`ODE_unique_Ioo` on `ℝ × (ℝ×ℝ²)` for the suspended autonomous field, comparing `Θ_t(0,(θ₀+2π,w₀))` with `(t, Φ_t(θ₀,w₀) + (2π,0))`, which is a solution of the `Y`-ODE because `Yfield` is invariant under the θ-shift where `χ_θ = 1`) · 200 · true.
- **C8 `Phi_core` (614)** — the core is fixed · the constant curve `(θ,0)` solves the ODE (`Vf_core`), uniqueness as in C7 · 60 · true.
- **C9 `hasDerivAt_fderiv_Phi` (621)** — variational equation · as `ContactMotions.hasDerivAt_fderiv_flow`: `uncurry Θ` is `C^∞` (`contDiff_Theta`), so `∂_t D_qΘ_t(q) = DY(Θ_t q) ∘ D_qΘ_t(q)` by `ContDiffAt.isSymmSndFDerivAt` + `HasFDerivAt.comp_hasDerivAt`; restrict to `q = (0,p)`, second component, inputs `(0,x)`; `D_p[(Θ_t(0,p)).1] = 0` by C3; `DY(t, Φ_t p)(0, x) = (0, D_p(cutoff•V_t)(Φ_t p) x)` for `|t| < 2` (`χ_τ′ = 0` there since `χ_τ ≡ 1` near); `cutoff ≡ 1` near the trajectory (C6 with margin `ρ/4 < ρ/2`) ⇒ `D(cutoff•V_t) = DV_t` (`Filter.EventuallyEq.fderiv_eq`) · 250 · true (validated indirectly by probe (e)).

### Unit D
- **D1 `hasDerivAt_alphaT_flow` (688)** — `A′ = μ A` · product rule for `(t, q, x) ↦ alphaT t q x` composed with `t ↦ (t, Φ_t p, J_t w)`: `∂_t alphaT = nuF` (`Pf` linear in `t`; `(1+t), (1−t)`), `D_q alphaT[V]` and `alphaT(DV·Jw)` from C4 (cutoff `= 1`), C9; then `D_qα[V](x) + α(DV x) = dα(V,x) + D_q(α(V))[x]` (B3) with `D_q(α_t(V_t)) = 0` (`alphaT_Vf` holds on the open tube where `P,N ≠ 0` ⇒ derivative of the zero function, `Filter.EventuallyEq.fderiv_eq`); finish with `moser_identity` · `HasDerivAt.mul`, `HasFDerivAt.comp_hasDerivAt`, `HasDerivAt.clm_apply` · 250 · **numerically verified** (probe (e)).
- **D2 `alphaT_flow_one` (699)** — `A(1) = e^{∫₀¹μ} A(0)`, `A(0) = α₀(p)(w)` · `B(t) := A(t)·exp(−∫₀ᵗ μ_s(Φ_s p) ds)` has derivative `0` on `Ioo (−1) 2` (D1, `intervalIntegral.integral_hasDerivAt_right` with continuity of `s ↦ μ_s(Φ_s p)`: `muf` continuous on the tube, `contDiff_uncurry_Phi`), so `B(1) = B(0)` (`is_const_of_deriv_eq_zero` on an open interval or `constant_of_derivWithin_zero`); `A(0)`: `Phi_zero`, `fderiv_id`, `alphaT_zero` · 120 · true (probe (e)).
- **D3 `Hmap_eventuallyEq` (709)** — local form · with `k = round(θ/2π)`: on the open set where `round` is locally constant, `Hmap = chart ∘ Φ₁ ∘ shift_k` literally; at a seam (`θ/2π` a half-integer) the two candidate `k`'s differ by one and `chart_periodic` + `Phi_shift` (`|redθ| ≤ π ≤ 2π`, `‖w‖ < δ₁`) identify the two formulas on a neighbourhood · `Filter.eventually_of_mem`, `round` locally constant away from half-integers (`Int.fract`, `abs_sub_round`) · 200 · true.
- **D4 `Hmap_pullback` (725)** — `α(H)(DH(τ,η)) = h·α₀(w)(τ,η)` · D3 + `fderiv` congruence (`Filter.EventuallyEq.fderiv_eq`), chain rule `D(chart ∘ Φ₁ ∘ shift) = Dchart · DΦ₁ · id`, A7 at `Φ₁(θ′,w)`: `α(chart q)(Dchart q ξ) = aT q.1 ((1+g q)ξ_θ − 2 q_v ξ_u) = aT q.1 · alphaT 1 q ξ` (`alphaT_one`) with `ξ = DΦ₁ (τ,η)`, then D2; unfold `hfun` (`redθ θ = θ − 2πk` with the same `k`, by `redθ_spec`) · 150 · **numerically verified** (probe (f)).
- **D5 `Hmap_injective` (739)** — `H` injective mod `2π` · `Hmap(θ,w) = chart(Φ₁(θ′,w))`, `Φ₁(θ′,w)` lies in the `ρ/4`-tube (C6) ⊂ `2ρ`-tube where `chart_inj` applies ⇒ `Φ₁(θ′,w)` and `Φ₁(θ″,w′)` agree up to a θ-shift by `2πk`; `Phi_shift` moves the shift to the initial point; `Φ₁` injective (C5) ⇒ `(θ′,w) = (θ″ + 2πk, w′)` ⇒ conclusion with `redθ_spec` · 200 · true.
- **D6 `Hmap_immersion` (747)** — `DH` injective · D3, chain rule, `DΦ₁` injective (C5: `DΨ ∘ DΦ₁ = id`), `Dchart` bijective on the `2ρ`-tube (`GoodRadius.chart_bij`, image point in the `ρ/4`-tube by C6) · 100 · true.
- **D7 `Hmap_open_map` (754)** — images of open sets are open · `H` is a local diffeo on the open `δ₁`-tube (D6 + equal dimension ⇒ `HasStrictFDerivAt.map_nhds_eq_of_equiv`), so `H '' (U ∩ solidTorus δ₁)` is open; take `V := H '' (U ∩ solidTorus δ₁)` and `inter_eq_left.2 (image_subset _ inter_subset_right)` · 100 · true.

### Unit E (hypothesis `hm : IsTransverseModel T δ H h`)
- **E1 `exists_N_b` (787)** — `N ≥ 1`, `b = N^{−1/2} < δ`, `Nb² = 1` · `exists_nat_gt (1/δ²)`, `b := 1/√N`, `Real.sq_sqrt`, `div_pow` · 40 · true.
- **E2 `norm_helix` (792)** — `‖helix‖ = |b|` · `EuclideanSpace.norm_eq`, `Fin.sum_univ_two`, `cos² + sin² = 1`, `Real.sqrt_sq_eq_abs` · 30 · true.
- **E3 `alpha0_helix` (796)** — `α₀(L₀′) = 1 − Nb²` · `deriv` of `!₂[b cos Nθ, −b sin Nθ]` is `!₂[−bN sin, −bN cos]`; `alpha0 = 1 + u·(−bN cos) − v·(−bN sin) = 1 − Nb²(cos² + sin²)` · `HasDerivAt.cos/sin`, `deriv` of `!₂` componentwise (`PiLp` / `WithLp.toLp` derivative: derive via `HasDerivAt` of each coordinate and `hasDerivAt_pi`-style lemma for `EuclideanSpace`) · 80 · **numerically verified** (probe (d)).
- **E4 `legendrian_L` (802)** — `α(L′) = 0` · `deriv (fun θ => H (θ, helix θ)) = fderiv H (θ,helix θ) (1, helix′ θ)` (`HasFDerivAt.comp_hasDerivAt`, `hm.smooth` on the open torus, `norm_helix` for membership), `hm.pullback`, E3 · 80 · true.
- **E5 `embedded_L` (808)** — `L` embedded circle · smooth (composition, `ContDiffOn` on the open torus ⇒ `ContDiffAt`), periodic (`hm.periodic`, `helix` periodic since `N` integer: `Real.cos_add_int_mul_two_pi`), injective mod `2π` (`hm.injective` gives `helix θ = helix θ′` and `θ′ = θ + 2πk`), immersion (`hm.immersion` and `(1, helix′) ≠ 0`) · 120 · true (sm-3:2479-2480).
- **E6 `pushoffAnnulus` (820)** — `H∘B` is a pushoff annulus · the nine fields: `eps_pos`, `b_pos`; `smooth` (composition into the open torus: `‖helix N (b−s) θ‖ = |b − s| < δ` for `−ε < s < b`); `periodic`; `core` (`annulus0 (θ,0) = (θ, helix b θ)`); `injective` (`hm.injective` then radius `|b−s| = |b−s′|` with `s, s′ < b` ⇒ `s = s′`, then `θ+κs ≡ θ′+κs`); `immersion` (`DB = [(1, helix′), (κ, −(cos,−sin))]` independent: the `w`-parts are orthogonal, nonzero for `s ≠ b`; `hm.immersion`); `transverse` (`α(D(H∘B)(0,1)) = h·α₀(DB(0,1)) = h κ ≠ 0`); `positive` (`α(D(H∘B)(1,0)) = h(1 − N(b−s)²) > 0` for `0 < s < b`, via `Nb² = 1`) · `B^*α₀` computation is the core (sm-3:2495-2497) · 350 · **numerically verified** (probe (c)).
- **E7 `transverselyIsotopic_pushoff` (828)** — `H∘B(·,s₀)` transversely isotopic to `T` · family `F s θ := H (annulus0 (θ, s₀ + s(b − s₀)))`, `s ∈ [0,1]`; joint smoothness (as E6); each circle embedded (E6's injectivity/immersion restricted, or E5-style) and positive transverse for `s < 1`; at `s = 1`: `annulus0 (θ, b) = (θ + κb, 0)`, `H(θ+κb, 0) = T(θ+κb)` (`hm.core`) — but the family must be positive transverse at `s = 1` too: `α(T′(θ+κb)) > 0` holds by hypothesis? NO: `IsTransverseModel` does not include `IsPositiveTransverse T`; **the leaf as stated needs `T` positive transverse at `s = 1`.  Check: `alpha (H(θ+κb,0)) (D H (1,0)) = h(θ+κb,0)·1 > 0` by `pullback`+`alpha0_zero_left`, and `deriv (T ∘ (·+κb)) = DH(θ+κb,0)(1,0)` — so positivity at `s = 1` follows from the model alone.** ✓; `ρ θ := θ + κb` is a circle reparametrization · 250 · true.

### Unit F (hypothesis `hm`, `0 < N`, `0 < b < δ`)
- **F1 `pushfwd_apply` (876)** — `X(H p) = DH(p)(V p)` for `p` in the torus · the chosen preimage `p′` satisfies `H p′ = H p` ⇒ `hm.injective`: `p′.2 = p.2`, `p′.1 = p.1 + 2πk`; `V` periodic (`helix` periodic, `‖·‖` unchanged), `H` periodic ⇒ `fderiv H` periodic (shift invariance of `fderiv`) · 100 · true.
- **F2 `contDiff_pushfwd` (884)** — `X` smooth · on the open image `U = H '' solidTorus δ` (open by `hm.open_map` with `U = univ`): at `q₀ = H p₀`, `hm.immersion` + dimension ⇒ `HasStrictFDerivAt` with an equiv ⇒ `ContDiffAt.localInverse` `Hinv` smooth near `q₀` with `H (Hinv q) = q`; F1 gives `X q = DH(Hinv q)(V(Hinv q))` near `q₀` (need `Hinv q ∈ solidTorus δ` near `q₀`: continuity of `Hinv`), smooth by composition (`ContDiff.fderiv` of `H` on the open torus, `Vamb` smooth: `chiAmb ∘ ‖·‖²`, `helix`); outside `K := H '' (Icc 0 (2π) ×ˢ closedBall 0 R₂)` (compact, `⊆ U`): `X = 0` on the open `Kᶜ` (any preimage of `q ∉ K` has `‖w‖ > R₂` ⇒ `chiAmb = 0` ⇒ `V = 0`) · 300 · true (sm-3:2522-2530).
- **F3 `hasCompactSupport_pushfwd` (889)** — support ⊆ `K` as above · `HasCompactSupport.intro` (`(isCompact_Icc.prod (isCompact_closedBall _ _)).image_of_continuousOn`) · 80 · true.
- **F4 `psi_track` (924)** — `Ψ_t(L θ) = H(θ, (1−t)v(θ))` · the curve `γ(t) = H(θ,(1−t)helix θ)` has `γ′ = DH(θ,(1−t)v)(0, −v) = DH(V)` (since `chiAmb((1−t)²b²) = 1`: `(1−t)b ≤ b < R₁`), `= X(γ t)` by F1; `γ(0) = L θ`; uniqueness (`ODE_unique_global` with the Lipschitz constant from F2/F3) against the flow curve · 150 · true (sm-3:2542-2547).

## 3. Assembly (proved in the skeleton)
`exists_goodRadius` (A4, A5, B4) → `exists_aprioriRadius` (C6) → `model` (D1–D7 + proved
`Hmap_smoothOn`, `Hmap_periodic`, `Hmap_core`, `hfun_pos`) → `exists_legendrian` (E1–E7) →
`ambientIsotopy` (F2, F3 + `globalFlow_fixed_of_notMem`, row 86) → `carries` (F4) →
`fd_transverse_neighborhood`.
