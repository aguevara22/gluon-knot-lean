# Feasibility memo v2 — rows 84 (fd:transverse-neighborhood) and 87 (fd:generic-front)

Date: 2026-09-14.  Toolchain: Lean v4.34.0-rc2, Mathlib pin 85e3a25e (`work/lean`).  Supersedes
`FD_84_86_FEASIBILITY.md` §2 for row 84.  What changed since v1: (i) smooth dependence of ODE
flows on initial data is **proved** (`SmoothDependence.lean`, `ContactMotionsFinal.lean` lines
1386-1434: `SM.ContactMotions.contDiff_uncurry` for any finite-dimensional `E : Type`, `SM.smoothDependence`,
`SM.fd_contact_motions : ContactMotionsData` unconditional); (ii) row 85 is accepted
(`work/lean/SM/ParameterAvoidance.lean`, `SM.fd_parameter_avoidance`, `SM.exists_param_avoiding`);
(iii) this memo re-reads the row-84 "Gray–Moser" step in coordinates and finds it is a **rational
identity**, checked in Lean (`work/drafts/fd/MoserIdentityCheck.lean`, 102 lines, 0 errors).

## 0. Summary

| row | verdict | estimate | two hardest steps | statement file |
|---|---|---|---|---|
| 84 fd:transverse-neighborhood | **FEASIBLE** (clear route, every step has a Mathlib or project tool; no Gray–Moser, no Cartan, no Lie derivative) | ≈ 3 500 lines (range 3 000–4 500) | (a) the uniform inverse-function / injectivity radius of the chart `F` and the local smooth inverse of `H` for the pushforward (sm-3:2421-2428, 2522-2530), ≈ 500 lines; (b) the explicit calculus of `V_t`, `μ_t` and the pullback ODE along the time-dependent flow (sm-3:2440-2475), ≈ 900 lines | `work/drafts/fd/TransverseNeighborhood.lean` — still fits, **no change required** (§1.6); /tmp check with `sorry` row theorem passes |
| 87 fd:generic-front | **HARD** (4 000–10 000; lower end) — clear route, all tools exist (rows 85, 86, IFT, Grönwall); long because of six independent constructions each with its own compactness/openness bookkeeping | ≈ 5 200 lines (range 4 500–7 000) | (a) the exact cusp germ with the `C²`-closeness of the cut-off flow (sm-3:2731-2768), ≈ 1 400 lines; (b) the two parametric-transversality steps (`C`, `R`) with their rank computations and uniform parameter balls (sm-3:2686-2714), ≈ 900 lines | `work/drafts/fd/GenericFront_Statement.lean` (280 lines, 0 errors, 0 warnings); /tmp check with `sorry` row theorem passes |

Neither row needs Sard.  Row 87's three transversality steps are exactly row 85 with
`(d, q) = (1, 2)`, `(2, 3)`, `(3, 4)` (§2.3); Mathlib's `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`
(equal dimensions) and `dimH_image_le` / `Real.dimH_of_nonempty_interior` are not needed beyond
what row 85 already consumed.

## 1. Row 84 fd:transverse-neighborhood (statement sm-3:2395-2409, proof 2410-2559)

### 1.1 The printed proof, step by step

| # | tex | step |
|---|---|---|
| S1 | 2411-2418 | `a = α(T′) > 0`, `c = √(2a)`, frame `E₁ = ∂_x + y∂_z`, `E₂ = ∂_y`, chart `F(θ,u,v) = T + c(uE₁ + vE₂)` |
| S2 | 2419-2421 | `DF` at the core has independent columns `T′, cE₁, cE₂` |
| S3 | 2421-2428 | IFT + compactness: uniform radius with `DF` invertible; injectivity radius by the limiting argument; `F` embeds a tube |
| S4 | 2429-2439 | `β = F^*α/a`; `β = dθ` on the core, `dβ(∂_u,∂_v) = 2`; `α_t = (1−t)α₀ + tβ` contact with `α_t(∂_θ) > 0` on a uniform tube |
| S5 | 2440-2453 | `ν = β − α₀`, `X₁, X₂` (basis of `ker α_t`), `D_t = dα_t(X₁,X₂) ≠ 0`, `V_t`, `(ι_{V_t}dα_t)|_{ker α_t} = −ν|_{ker α_t}`, `V_t = 0` on the core |
| S6 | 2454-2463 | `‖V_t‖ ≤ C√(u²+v²)`, Grönwall `r(t) ≤ e^{Ct} r(0)`, initial disc `< ρe^{−C}/2`, flow `Φ_t` exists on `[0,1]`, fixes the core, invertible onto its image |
| S7 | 2464-2475 | `ν + ι_{V_t}dα_t = μ_t α_t`; `d/dt Φ_t^*α_t = (μ_t∘Φ_t) Φ_t^*α_t`; `Φ_1^*β = exp(∫μ) α₀`; `H = F∘Φ_1`, `h = (a∘pr_θ∘Φ_1)·exp(∫μ) > 0` |
| S8 | 2476-2481 | `L₀(θ) = (θ, b cos Nθ, −b sin Nθ)`, `Nb² = 1`, Legendrian for `α₀`, embedded; `L = H∘L₀` |
| S9 | 2481-2506 | annulus `B(θ,s) = (θ+κs, (b−s)cos Nθ, −(b−s)sin Nθ)`, `B^*α₀ = (1−N(b−s)²)dθ + κ ds`, transverse, circles negative/Legendrian/positive, small positive circle = the pushoff, family to `s = b` = transverse isotopy to `T(θ+κb)` |
| S10 | 2507-2530 | `χ` from `η(s) = e^{−1/s}`, `V(θ,w) = (0, −χ(|w|²)v(θ))`, `H` has open image `U` and smooth inverse (IFT), `X = H_*V` extended by `0`, globally smooth, support in compact `K ⊂ U` |
| S11 | 2531-2541 | `X` bounded ⇒ global flow `Ψ_t`; inverse `Ψ_{−t}`; diffeomorphisms; identity outside `K`; orientation |
| S12 | 2542-2559 | `Ψ_t(L θ) = H(θ,(1−t)v(θ))` by uniqueness; `Ψ_1∘L = T`; remarks |

### 1.2 The decisive re-reading: everything in S4–S7 is explicit

In the chart `F = (x_T + cu, y_T + cv, z_T + cuy_T)` one computes, with no exterior calculus
(`α_q(w) = w_z − q_y w_x`, `∂_uF = cE₁`, `∂_vF = cE₂`, `∂_θF = T′ + c′(uE₁+vE₂) + cu(0,0,y′_T)`):

```
F^*α(∂_v) = 0,   F^*α(∂_u) = −c²v = −2av,   F^*α(∂_θ) = a + c u y′ − c v x′ − c c′ u v
β = (1 + g) dθ − 2v du,          g := (c u y′ − c v x′ − c c′ u v)/a            (exact, not only on the core)
α_t = (1 + t g) dθ − (1+t) v du + (1−t) u dv,      ν = g dθ − v du − u dv
dα_t = 2 du∧dv + t (g_u du + g_v dv)∧dθ           (the θ-derivative of g drops out)
P := α_t(∂_θ) = 1 + t g,   N := P·D_t = 2P − t g_u (1−t) u − t g_v (1+t) v     (N = 2 on the core)
V_t = ( 2uv/N , u(1+g)/N , v(g−1)/N ),             μ_t = [ g + t(g_u u(1+g) + g_v v(g−1))/N ] / P
```

`MoserIdentityCheck.lean` (namespace `MoserCheck`) takes the printed definitions of `X₁, X₂, D_t, V_t, μ_t`
(sm-3:2440-2446, 2464-2465) with `u, v, t, g, g_u, g_v` as formal reals and proves by `field_simp; ring`:
`D_eq` (`D_t = N/P`), `Vθ_eq/Vu_eq/Vv_eq` (the closed forms), `alphaT_V` (`α_t(V_t) = 0`, sm-3:2468),
`moser_identity` (`ν(w) + dα_t(V_t, w) = μ_t α_t(w)` for every `w`, sm-3:2464-2466), `D_core`, `V_core`.
So the "Gray–Moser computation with a time-dependent form" of v1 is a 100-line algebraic lemma, and
the "Cartan formula" (sm-3:2468) reduces, exactly as in row 86 (`ContactMotions.hasDerivAt_alpha_flow`),
to the product rule `d/dt[α_t(γ)(Jw)] = ν(γ)(Jw) + Dα_t(γ)[γ̇](Jw) + α_t(γ)(J̇w)` with `γ̇ = V_t(γ)`,
`J̇ = DV_t(γ)J` (variational equation), and the two-line identity
`Dα[V](x) + α(DV x) = dα(V,x) + D(α(V))[x]` where `α_t(V_t) ≡ 0` kills the last term.  Contactness
(`α_t∧dα_t ≠ 0`) is never needed as such: only `P > 0` and `N > 0` on a tube, which hold on the core
(`P = 1`, `N = 2`) and hence on a uniform tube by continuity and compactness in `(t, θ)`.

### 1.3 Step → tool → lines

| step | Mathlib / project tool | status | lines |
|---|---|---|---|
| S1 | `contDiff_euclidean`, `ContDiff.sqrt` (`a > 0`), `PiLp.proj` coordinates as row 86 (`coordCLM`, `!₂[…]`) | available | 100 |
| S2 | explicit `DF(θ,0)(τ,η) = τT′ + c(η₀E₁ + η₁E₂)`; injectivity by applying `alpha` then coordinates 0, 1 | available | 100 |
| S3 uniform radius | invertibility of `DF` is open (`ContinuousLinearMap.continuous_det`, `ContDiff.continuous_fderiv`), contains the compact core `Icc 0 (2π) × {0}` ⇒ tube (`generalized_tube_lemma`, periodicity) | new | 120 |
| S3 injectivity radius | contradiction: `IsCompact.tendsto_subseq` on `[0,2π]`, `T` embedded ⇒ limits agree mod `2π`, then `HasStrictFDerivAt.toOpenPartialHomeomorph` (local injectivity on an open source) | new | 250 |
| S3 `F` open on the tube; local inverse smooth (needed for S10 `H⁻¹`) | `HasStrictFDerivAt.map_nhds_eq_of_equiv` / `isOpenMap_of_hasStrictFDerivAt_equiv`; `ContDiffAt.localInverse`, `ContDiffAt.to_localInverse`, `OpenPartialHomeomorph.contDiffAt_symm`; injectivity mod `2π` makes the pushforward independent of the preimage | new | 250 |
| S4–S5 | the explicit formulas of §1.2; smoothness of `g, V_t, μ_t` where `P, N ≠ 0` (`ContDiff.div`); `P, N > 0` on a uniform tube (continuity + `generalized_tube_lemma`); `V_t = 0` on the core; `MoserIdentityCheck` transported to the concrete `g` | new, algebra done | 450 |
| S6 time-dependent flow | suspension: `Y(τ, p) = (b(τ), b(τ)·χ_ρ(w)·χ_θ(θ)·V_τ(p))` on `ℝ × ℝ³`, `b` a bump `= 1` on `[−1, 2]`, `χ_ρ` a `w`-cutoff `= 1` on `|w| ≤ ρ`, `χ_θ` a `θ`-cutoff `= 1` on `[−4π, 4π]` ⇒ `Y` is `C^∞` compactly supported ⇒ global flow (`exists_isGlobalFlow_of_hasCompactSupport'`) jointly `C^∞` (`SM.ContactMotions.contDiff_uncurry` with `E = ℝ × ℝ³`); `Φ_t(p) := pr₂ Θ_t(0, p)`; time-one map bijective with smooth inverse `p′ ↦ pr₂ Θ_{−1}(1, p′)` | new, corollary of the proved theorem | 250 |
| S6 a-priori bound | `‖V_t(θ,w)‖ ≤ C‖w‖` from `V_t = 0` on the core + mean value (`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`) or directly from the closed forms; `norm_le_gronwallBound_of_norm_deriv_right_le` ⇒ trajectories from `|w| < δ` stay in `|w| < ρ`, `|θ − θ₀| < 1`, where all cutoffs are `1`; uniqueness (`ODE_solution_unique_univ`) identifies the flow with the uncut flow and gives `2π`-periodicity | new | 250 |
| S7 variational equation for the time-dependent flow | as row 86 `hasDerivAt_fderiv_flow` (`ContDiffAt.isSymmSndFDerivAt`, `HasFDerivAt.comp_hasDerivAt`, `HasDerivAt.clm_apply`) applied to `uncurry Φ` | adapt | 150 |
| S7 pullback ODE + solution | product rule + `moser_identity`; `intervalIntegral.integral_hasDerivAt_right`, `HasDerivAt.exp`, `is_const_of_deriv_eq_zero` as row 86 `alpha_flow_eq` | adapt | 250 |
| S7 `H = F∘Φ_1` model | pullback chain rule (`fderiv_comp`), `h = a(pr_θ Φ_1)·exp(∫μ) > 0`; `IsTransverseModel` fields: smooth (`ContDiff.comp`), periodic (S6), injective mod `2π` (S3 + bijectivity), immersion (`DF` invertible on tube, `DΦ_1` invertible), `open_map` (composition of open maps), core (`V_t = 0` on core) | new | 250 |
| S8 | `Real.cos/sin` calculus, `alpha0` computation, degree-one first coordinate for injectivity | new | 150 |
| S9 | `B^*α₀` by direct `deriv` computation (re-derived by hand for this memo: `(1 − N(b−s)²)dθ + κ ds`), `IsPushoffAnnulus (H∘B)` via `IsTransverseModel.pullback` (`α = hα₀`, `h > 0`), `IsPositivePushoff`, `TransverselyIsotopic` with `ρ(θ) = θ + κb` | new | 350 |
| S10 | `χ(s) = Real.smoothTransition ((R₂² − s)/(R₂² − R₁²))` (`Real.smoothTransition.contDiff`, `one_of_one_le`, `zero_of_nonpos`), `V`, pushforward via the local inverse of `H` (S3 row), `HasCompactSupport` from `K = H([0,2π] × closedBall R₂)` | new | 250 |
| S11 | `exists_isGlobalFlow_of_hasCompactSupport`, `SM.ContactMotions.contDiff_uncurry`, `IsGlobalFlow.leftInverse/rightInverse`; `IsCompactlySupportedAmbientIsotopy` fields | reuse | 100 |
| S12 | `ODE_solution_unique_univ` with the explicit curve `t ↦ H(θ,(1−t)v(θ))`, whose derivative is `DH·(0,−v) = X` where `χ = 1` | adapt | 120 |
| assembly | `TransverseNeighborhoodConclusion` | — | 100 |
| **total** | | | **≈ 3 500** |

Uncertainty: the `fderiv` bookkeeping of S4–S7 on `ℝ × EuclideanSpace ℝ (Fin 2)` is the main
risk of overrun (row 86's analogous block cost ≈ 400 lines for a time-independent field); an
overrun to 4 500 would still be a single unit.  No step is blocked.

### 1.4 Statement check (`TransverseNeighborhood.lean`)

The existing bundle fits the route without change: `IsTransverseModel` (`smooth` as `ContDiffOn` on
the open solid torus, `periodic`, `injective` mod `2π`, `immersion`, `open_map`, `core`, `factor_pos`,
`pullback`) is exactly what S7 produces (`H = F∘Φ_1` is even globally defined and smooth, and its
image is open, both stronger than demanded); `IsPushoffAnnulus` with domain `Ioo (−ε) b` matches S9
(`positive` for `0 < s < b`; the printed "`0 < s ≤ b`" end circle is `T(θ+κb)`, covered by
`TransverselyIsotopic`); `IsCompactlySupportedAmbientIsotopy` matches S11; `carries` matches S12.
Optional (not printed, not needed): a field `IsOpen (H '' solidTorus δ)` would save the consumer of
S10 a re-derivation.  The /tmp file `TN_sorry.lean` = the draft + `theorem fd_transverse_neighborhood :
TransverseNeighborhoodData := sorry` compiles with only the `sorry` warning.

### 1.5 Verdict

**FEASIBLE**, ≈ 3 500 lines.  Decisive reasons: (1) smooth dependence is proved, and its
time-dependent, periodic form is a corollary by suspension and cut-off (§1.3 S6) — no new analysis;
(2) the Moser step is an explicit rational identity already checked in Lean; (3) every remaining
step (IFT radius, bump functions, Grönwall, uniqueness, trigonometric annulus) has a direct Mathlib
tool.  Hardest: S3 (uniform radii + local inverse, ≈ 500) and S4–S7 (explicit calculus, ≈ 900).

### 1.6 Fidelity risks (row 84)

* **FR-TN-1** (sm-3:2397) `S¹ = ℝ/2πℤ` as `2π`-periodic lifts; "embedded" = injective mod `2π` + immersion.
* **FR-TN-2** (sm-3:2399-2400) "smooth embedding `H : S¹ × D_δ → ℝ³`" = `C^∞` on the open solid torus +
  injective mod `2π` + immersion + images of open sets relatively open; the proof gives a global
  diffeomorphism onto an open set, so the field is weaker than what is proved, never stronger.
* **FR-TN-3** (sm-3:2401-2403) `h` quantified with `H`, only `h > 0` demanded (printed clause); the proof's
  `h` is smooth but smoothness is not a printed clause.
* **FR-TN-4** (sm-3:2405, 2490-2502) "positive transverse pushoff" = a small positive circle of a
  transverse annulus with `L` as zero circle (the paper's "source convention", sm-3:2501-2502);
  if a consumer needs Etnyre's pushoff a bridge lemma is required.
* **FR-TN-5** (sm-3:2405-2406, 2503-2504) transverse isotopy ends at an orientation-preserving
  reparametrization `T∘ρ` (`T(θ+κb)`).
* **FR-TN-6** (sm-3:2481-2482, 2501) the annulus domain is the open `(−ε, b)`; the closed end `s = b`
  is reached only through the isotopy clause.
* **FR-TN-7** (sm-3:2406-2408, 2538-2541) "ordinary ambient isotopy … preserving their orientations" =
  compactly supported family of `C^∞` diffeomorphisms of `ℝ³` with `Ψ_1∘L = T` as parametrized
  circles; the extension to `S³` and orientation-preservation of `Ψ_t` (sm-3:2538-2541) are not
  clauses of the statement and are not stated.

## 2. Row 87 fd:generic-front (statement sm-3:2613-2630, proof 2631-2783)

### 2.1 The printed proof, step by step, with parameter counts

| # | tex | step | codimension |
|---|---|---|---|
| P0 | 2632-2638 | `Φ_a` = composition of time-`a_i` flows of compactly supported `H_i` (row 86); `∂_{a_i}(Φ_a∘L)|₀ = X_{H_i}∘L`; `s ↦ Φ_{sa}` is a contact isotopy; images are Legendrian embeddings | — |
| P1 | 2639-2658 | simultaneous zeros of `(x′, x″)`: at such `θ₀`, `y′ ≠ 0`; `H₂ = −½(y−y₀)²`, `H₃ = −⅙(y−y₀)³` (bumped) give columns `(y′, y″)ᵀ`, `(0, y′²)ᵀ`, det `y′³ ≠ 0`; finitely many neighbourhoods; positive minimum on the complement; uniform ball; **row 85 with `(d,q) = (1,2)`**; zeros of `x₁′` simple ⇒ finite; `y₁′ ≠ 0` there | `1 < 2` |
| P2 | 2659-2685 | uniform collar: cover by regular intervals (`x₁′` of fixed sign) and critical intervals (`x₁″, y₁′` fixed signs, opposite endpoint signs of `x₁′`); front injective on each (integral of `y(θ₊) − y(θ₋)`); margins persist under `C²`-small perturbation; Lebesgue number `δ` | — |
| P3 | 2686-2714 | `K₂` (pairs at distance `≥ δ`), `K₃` (triples); `C(θ,η,a) = (x_a′(θ), p_a(θ) − p_a(η)) ∈ ℝ³`, `R(θ,η,τ,a) = (p_a(θ)−p_a(η), p_a(θ)−p_a(τ)) ∈ ℝ⁴`; ranks 3, 4 via `H₂` at the first point and `H^x = −(y−y_q)`, `H^z = 1` at the others; uniform ball; **row 85 simultaneously with `(2,3)`, `(3,4)`** | `2 < 3`, `3 < 4` |
| P4 | 2715-2730 | remaining double points: both regular, `y` values differ, tangent det `x′(θ)x′(η)(y(η)−y(θ)) ≠ 0` ⇒ transverse, isolated (IFT), finitely many; all properties persist under `C²`-small Legendrian perturbation | — (no avoidance) |
| P5 | 2731-2768 | exact cusp germ: `x = f(y)`, `A = ½f″(y₀) ≠ 0`, `ψ = ∫(f − q)`, `H = ψ(y)` has the explicit flow `(x − sψ′, y, z + s(ψ − yψ′))`; at `s = 1`, `x = q(y)`, `z` by Legendrianity; cutoff of radius `O(ε)`; `‖X_H‖_{C²} = O(ε)`; time-one map `C²`-close to `id` via `J′ = DX J`, `M′ = DX M + D²X[J,J]`; inner subarc uses the exact formula; margins retained | — |
| P6 | 2769-2783 | concatenation with flat reparametrizations; `Φ_s^*α = c_s α`, `c_s > 0`; `Φ_s∘B` transverse annulus, `α((Φ_s∘K)′) = (c_s∘K)α(K′) > 0`; oriented knot type preserved | — |

### 2.2 Step → tool → lines

| step | tool | status | lines |
|---|---|---|---|
| P0 | `ContactMotionsData.compositions_smooth` (joint `C^∞` in `(a,p)`), `.contact`, `.confFactor_pos`, `.diffeo`; `∂_{a_i}Φ_a|₀ = X_{H_i}` from `IsGlobalFlow.hasDerivAt` + chain rule with `Φ_0 = id`; Legendrian preserved: `alpha (Φ p) (DΦ v) = c·alpha p v = 0` | reuse + 150 new | 150 |
| P1 rank | `∂_a x_a′(θ) = ∂_θ ∂_a x_a(θ)` (`ContDiffAt.isSymmSndFDerivAt` on the jointly smooth `(θ,a) ↦ Φ_a(L θ)`); `X_{H}` for `H = bump·H₂`: on the open set where the bump is `1`, `fderiv` agrees (`Filter.EventuallyEq.fderiv_eq`), so `hamVF` is the unbumped one; `2×2` determinant `y′³` | new | 300 |
| P1 uniform ball + avoidance | nonzero minor is open; compact zero set covered by finitely many (`IsCompact.elim_finite_subcover`); positive minimum of `‖(x′,x″)‖` on the compact complement (`IsCompact.exists_isMinOn`); `ParameterAvoidanceHyp` with `K = Icc 0 (2π)`, `m = 2n`, `q = 2`; `SM.exists_param_avoiding` | new | 300 |
| P1 finiteness of cusps | simple zeros isolated ⇒ `IsCompact.finite` with `IsDiscrete`, or `Set.Infinite.exists_accPt_of_subset_isCompact` for the contradiction | new | 120 |
| P2 local injectivity | cleaner than the printed inverse branches: for `θ₁ < θ_c < θ₂` with `x(θ₁) = x(θ₂) = X`, integration by parts gives `z(θ₂) − z(θ₁) = ∫_{θ₁}^{θ₂} y′(θ)(X − x(θ)) dθ`, integrand of fixed sign (`x` monotone on each side) ⇒ `intervalIntegral_pos_of_pos_on`; regular intervals: `x` strictly monotone (`StrictMonoOn` from `deriv > 0`) | new | 300 |
| P2 margins + Lebesgue number | sign conditions on compact intervals are open in `a` because `(θ,a) ↦ x_a′, x_a″, y_a′` are continuous (`generalized_tube_lemma`) — no `C^k`-closeness needed; Lebesgue number by the printed compactness argument | new | 300 |
| P3 ranks | explicit `X_H` values `(1,0,y_q)`, `(0,0,1)` for `H^x, H^z`; block-triangular `3×3` and `4×4` minors; disjoint bumps (`Metric.ball` radii `< dist/2`) | new | 400 |
| P3 uniform ball + avoidance | as P1 with `K₂ ⊂ ℝ²`, `K₃ ⊂ ℝ³` compact (circular distance `≥ δ` on `[0,2π]^k`, periodic lifts as FR-PA-1); `finite_collection` / `exists_param_avoiding` with `ι = Fin 2`, `(d,q) = (2,3), (3,4)`; shrink to keep P2 margins | new | 500 |
| P4 | tangent det formula from `z′ = y x′`; `y(θ) ≠ y(η)` from embeddedness; isolation via `HasStrictFDerivAt.toOpenPartialHomeomorph` on `(θ,η) ↦ p(θ) − p(η)`; finiteness in compact `K₂` (`IsCompact.finite`) | new | 350 |
| P5 germ algebra | `y` as local parameter: 1-D IFT (`HasStrictDerivAt.toOpenPartialHomeomorph`/`localInverse`), `f = x∘y⁻¹`, `f″(y₀) = x″/y′² ≠ 0`; the explicit flow by `ContactMotionsHyp.hamFlow_unique`; `z` formula by FTC (`intervalIntegral.integral_eq_sub_of_hasDerivAt`) from `z′ = y x′` | new | 400 |
| P5 cutoff estimates | `ψ = O(u⁴)` by Taylor (`taylor_mean_remainder_lagrange` or repeated MVT); `‖D^k(ψ·bump_ε)‖ ≤ Cε^{4−k}` by `norm_iteratedFDeriv_mul_le`, `ContDiffBump` with `rIn = ε/2, rOut = ε` and `‖D^k bump‖ ≤ Cε^{−k}` (needs scaling of a fixed bump — not in Mathlib's `ContDiffBump` API; ≈ 100 lines) | new | 350 |
| P5 `C²`-closeness of the time-one map | new general lemma: `‖X‖_{C²} ≤ η ≤ 1` ⇒ `‖φ_1 − id‖_{C²} ≤ Cη`; needs the second variational equation `M′ = DX(φ)M + D²X(φ)[J,J]` from joint `C^∞` (as `hasDerivAt_fderiv_flow`, one order up) and Grönwall twice; alternative: rescaling `p = p_c + εp̃` and joint smoothness in `ε` — similar cost | new | 400 |
| P5 assembly | inner subarc stays where the cutoff is `1` (displacement `O(ε³)` vs gap `ε/2`); P2/P4 margins persist under `C²`-small perturbation (they are open `C²` conditions with positive margins) | new | 250 |
| P6 | flat reparametrization from `Real.smoothTransition`; conformal factors multiply (`ContactMotionsData.contact`); `IsPushoffAnnulus (Φ_s∘B)` from diffeo + contact; `TransverselyIsotopic` with `F s = Φ_s∘K`, `ρ = id`; `knot_type` witnessed by `Φ` | new | 450 |
| bundle | `GenericFrontConclusion` | — | 150 |
| **total** | | | **≈ 5 200** |

### 2.3 Parametric transversality: what the printed proof actually uses

Only row 85, three times, each with parameter rank `q` at every zero guaranteed by explicit
Hamiltonians and an openness/shrinking argument; `(d, q)`: cusps-of-`(x′,x″)` `(1,2)`; cusp on
another branch `(2,3)`; triple point `(3,4)`.  Transverse double points (P4) and the cusp normal
form (P5) are not avoidance steps.  Row 85's `K` must be a compact subset of `ℝ^d`: `Icc 0 (2π)`,
`{(θ,η) ∈ [0,2π]² : circular dist ≥ δ}`, `{(θ,η,τ) ∈ [0,2π]³ : pairwise ≥ δ}` (chart reading
FR-PA-1; periodicity of `C`, `R` in each variable makes the lift lossless).  No Sard, no
Hausdorff dimension beyond row 85's internals.

### 2.4 The statement (`GenericFront_Statement.lean`)

`SM.GenericFrontData := ∀ L, GenericFrontHyp L → ∃ Φ, GenericFrontConclusion L Φ`;
`GenericFrontHyp` = `IsEmbeddedCircle L ∧ IsLegendrian L` (2614);
`GenericFrontConclusion L Φ` fields: `isotopy : IsContactIsotopy Φ` (2614-2615),
`legendrian_circle`, `legendrian` for `L_g = Φ 1 ∘ L` (2615), `generic : IsGenericFront (Φ 1 ∘ L)`
(2615-2625: `finite_cusps`, `exact_germ`, `finite_double`, `transverse_double`, `no_triple`,
`no_cusp_on_branch`), `pushoff` (2627-2629), `knot_type` (2629-2630).  `IsExactCuspGerm L θc :=
∃ A ≠ 0, y′(θc) ≠ 0 ∧ ∃ ε > 0, ∀ |θ − θc| < ε, x θ = x θc + A(y θ − y θc)² ∧ z θ = z θc + A y θc (y θ − y θc)² + ⅔A(y θ − y θc)³`
(2621-2625).  "Oriented topological knot type" is rendered as the ambient isotopy class of the
parametrized oriented embedding: `∃ Ψ, IsCompactlySupportedAmbientIsotopy Ψ ∧ ∀ θ, Ψ 1 (L θ) = Φ 1 (L θ)`
— the standard definition (same oriented knot type ⇔ an orientation-preserving ambient isotopy
carries one to the other; the parameter carries the orientation), honest because the printed
proof's witness is `Φ` itself (2780-2781) and the consumer sm-3:3476-3490 composes exactly such
families.  Weaker renderings (equal images up to homeomorphism of `ℝ³`) would lose the orientation
and are not what the consumer uses.  The notions shared with row 84 are verbatim copies in
`SM.GenericFront` (dedupe at porting time by importing `SM.TransverseNeighborhood`).

### 2.5 Verdict

**HARD**, ≈ 5 200 lines (4 500–7 000), lower end of the band; a clear route with no missing
theorem.  Decisive reasons: the proof is six independent constructions (P1–P6), each needing its
own compactness/openness bookkeeping over `(θ, a)`; P5 needs one genuinely new analytic lemma
(`C²`-closeness of the time-one map of a `C²`-small field, ≈ 400 lines, second variational
equation) and a scaled-bump derivative estimate; P3's rank computations are mechanical but large.
Hardest: P5 (≈ 1 400) and P3 (≈ 900).  Recommended order: row 84 first (it exercises the
time-dependent flow and the IFT tooling), then row 87 P0 → P1 → P4 → P2 → P3 → P6 → P5, with P5
last since the statement's germ clause is the only clause depending on it.

### 2.6 Fidelity risks (row 87)

* **FR-GF-1** (2614) circles as `2π`-periodic lifts; "embedding" = injective mod `2π` + immersion.
* **FR-GF-2** (2614-2615) `IsContactIsotopy` includes **compact support**, absent from the printed
  statement, present in the printed proof (2632-2638, 2769-2772) and used by the consumer
  (sm-3:3480-3481 "the two smooth compactly supported ambient flows").  Deliberate strengthening.
* **FR-GF-3** (2616-2617) "cusp" = parameter with `x′ = 0` (consumer's reading sm-3:3470-3474);
  "semicubical" is carried by the germ clause; finiteness counted on one period.
* **FR-GF-4** (2617) double points as ordered pairs distinct mod `2π`; transversality = nonzero
  determinant of the front velocities `(x′, z′)`; the printed `x′(θ)x′(η)(y(η) − y(θ))` is this
  determinant for Legendrian curves (2717-2721).
* **FR-GF-5** (2621-2626) exact germ: `y′(θc) ≠ 0` makes `u = y − y₀` a local coordinate; "may
  increase or decrease" = no sign condition on `y′(θc)`; identities on a `θ`-neighbourhood.
* **FR-GF-6** (2627-2629) "a chosen thin positive-pushoff annulus" = any `IsPushoffAnnulus` of `L`
  (row 84's notion, sm-3:2490-2502); "thin" imposes no extra condition; the conclusion is quantified
  over all such annuli, which the proof supports (2773-2779).
* **FR-GF-7** (2629-2630) oriented knot type as in §2.4 (parametrized ambient isotopy class).
* **FR-GF-8** (2615) `L_g` is identified with the parametrized `Φ 1 ∘ L` (2632 "`Φ_a∘L`"); no
  reparametrization is allowed at the end of the contact isotopy.

## 3. Dependencies and porting notes

Row 84 imports `SM.ContactMotions` (for `IsGlobalFlow`, `exists_isGlobalFlow_of_hasCompactSupport`,
`contDiff_uncurry`, `alpha`) once `ContactMotionsFinal.lean` is ported; row 87 imports rows 84
(notions), 85 (`ParameterAvoidanceHyp`, `exists_param_avoiding`) and 86 (`ContactMotionsData`,
`hamFlow`, `composeFlows`, `hamFlow_unique`).  Shared readings as in v1 §3: `ℝ³ = EuclideanSpace ℝ (Fin 3)`,
`alpha p v = v 2 − p 1 * v 0`, pullbacks stated pointwise, smooth = `ContDiff ℝ ∞`.
Files: `work/drafts/fd/FD_84_87_FEASIBILITY_v2.md` (this memo), `work/drafts/fd/GenericFront_Statement.lean`
(280 lines, 0 errors/warnings), `work/drafts/fd/MoserIdentityCheck.lean` (102 lines, 0 errors),
`work/drafts/fd/TransverseNeighborhood.lean` (unchanged, still compiles); /tmp checks
`/tmp/fd/TN_sorry.lean`, `/tmp/fd/GF_sorry.lean` (each: only the `sorry` warning; sanity lemmas
`[propext, Classical.choice, Quot.sound]`).
