# Feasibility memo — rows 84 (fd:transverse-neighborhood) and 86 (fd:contact-motions)

Date: 2026-09-14.  Toolchain: Lean v4.34.0-rc2, Mathlib pin 85e3a25e (the project's `work/lean`).
Sources: reference/SM/sm-3-statesum.tex:2395-2409 (row 84 statement), 2410-2559 (proof);
2586-2597 (row 86 statement), 2598-2611 (proof).  Sibling row 85 (fd:parameter-avoidance,
work/drafts/fd/ParameterAvoidance.lean) is the style model.

## 0. Summary of verdicts

| row | verdict | what is delivered |
|---|---|---|
| 86 fd:contact-motions | **provable-with-new-infrastructure**, the infrastructure being ONE missing Mathlib theorem (smooth dependence of an ODE flow on the initial point).  Everything else is proved: global existence of the flow, its uniqueness, group law, bijectivity, `C^∞` in time, the infinitesimal contact identity `L_{X_H} α = H_z α`, the conformal-factor ODE and its solution `c = exp ∫ H_z ∘ φ`, positivity and smoothness of `c`, smooth dependence of finite compositions on the times, `C^k`-closeness on compact sets. | `ContactMotions.lean`: faithful bundle `SM.ContactMotionsData`; `SM.fd_contact_motions : SmoothDependence → ContactMotionsData` with the one explicit hypothesis `SM.SmoothDependence` (the missing theorem, stated for compactly supported `C^∞` fields on `ℝ³`); unconditional theorems for the flow's existence/uniqueness/group law/time-smoothness. |
| 84 fd:transverse-neighborhood | **blocked** on the same missing theorem (twice: the Moser flow `Φ_t` and the ambient flow `Ψ_t` must be diffeomorphisms) *and* needs ≈ 3 000–5 000 further lines of new infrastructure (Gray/Moser computation with a time-dependent form, inverse-function-theorem embedding radius, pushoff/transverse-isotopy definitions).  Not provable in this unit. | `TransverseNeighborhood.lean`: faithful STATEMENT only (compiling Prop bundle `SM.TransverseNeighborhoodData`, no theorem), plus this memo. |

The missing Mathlib fact, precisely: *for a `C^∞` (even `C^1`) vector field with compact support on
`ℝ^n`, the global flow `φ : ℝ × ℝ^n → ℝ^n` is `C^∞` (resp. `C^1`) jointly in `(s, p)`.*  Mathlib's
`Mathlib/Analysis/ODE/*` (this pin) has: Picard–Lindelöf existence on a closed time interval for
every initial point of a ball (`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`),
uniqueness (`ODE_solution_unique_of_mem_Ioo`, `ODE_solution_unique_univ`), Grönwall
(`dist_le_of_trajectories_ODE`: the flow is *Lipschitz* in the initial point), and regularity of a
solution *in time* (`IsPicardLindelof.contDiffOn_enat_Icc_of_hasDerivWithinAt`).  It has **no**
differentiability of the flow in the initial point (no variational equation, no `ContDiff` of
`uncurry φ`).  `Mathlib/Dynamics/Flow.lean` is purely topological, and
`Mathlib/Geometry/Manifold/IntegralCurve/*` only does existence/uniqueness/uniform time on
manifolds.  Grep evidence: no declaration in those directories mentions dependence on the initial
condition beyond `exists_eventually_eq_hasDerivAt` (a local *set-theoretic* flow).

## 1. Row 86 fd:contact-motions

### 1.1 Printed statement, clause by clause (sm-3:2586-2597)

1. "For a smooth compactly supported `H : ℝ³ → ℝ`" — hypotheses `ContDiff ℝ ∞ H`, `HasCompactSupport H`.
2. "the vector field `X_H = −H_y ∂_x + (H_x + y H_z) ∂_y + (H − y H_y) ∂_z`" — an explicit map
   `hamVF H : ℝ³ → ℝ³` in coordinates `(x, y, z) = (p 0, p 1, p 2)` of `EuclideanSpace ℝ (Fin 3)`.
3. "has a global flow `φ_H^s`" — `φ : ℝ → ℝ³ → ℝ³`, `φ 0 = id`, `∂_s φ s p = X_H (φ s p)` for all
   `s, p`, and the flow law `φ (s+t) = φ s ∘ φ t`.
4. "of coorientation-preserving contact diffeomorphisms for `α = dz − y dx`" — each `φ s` is a
   `C^∞` bijection with `C^∞` inverse `φ (−s)`; contact: `α_{φ s p}(Dφ_s(p) v) = c · α_p(v)`;
   coorientation-preserving: `c > 0`.
5. "`(φ_H^s)^*α = c_s^H α` with a smooth positive function `c_s^H`, its conformal factor" — the
   explicit `c_s^H(p) = exp (∫_0^s H_z (φ_v p) dv)` (sm-3:2603-2606), smooth in `(s, p)`, positive.
6. "Finite compositions of their small-time flows depend smoothly on the times" — for
   `H_1, …, H_n` the map `(a, p) ↦ φ_{H_1}^{a_1} ∘ ⋯ ∘ φ_{H_n}^{a_n} (p)` is `C^∞` on `ℝ^n × ℝ³`.
7. "and are arbitrarily `C^k`-close to the identity on compact sets for each fixed finite `k`" —
   for every compact `K`, `k`, `ε > 0` there is `δ > 0` such that `|a_i| < δ` for all `i` gives
   `‖D^j (Φ_a − id)(p)‖ < ε` for all `j ≤ k`, `p ∈ K`.

### 1.2 Mathlib facts needed and their status

| need | Mathlib | status |
|---|---|---|
| `X_H` is `C^∞` with compact support | `contDiff_euclidean`, `ContDiff.contDiff_fderiv_apply`, `EuclideanSpace.proj`, `HasCompactSupport.fderiv`, `HasCompactSupport.mul_left` | available |
| bounded + globally Lipschitz from `C^1` + compact support | `HasCompactSupport.isCompact_range`, `IsCompact.exists_bound_of_continuousOn`, `lipschitzWith_of_nnnorm_fderiv_le`, `ContDiff.continuous_fderiv` | available |
| existence on `[−T, T]` for every `T` and every initial point | `IsPicardLindelof.of_time_independent` with `a = L·T`, `r = 0`, then `exists_eq_forall_mem_Icc_hasDerivWithinAt` | available; gluing to a global solution must be done here (≈ 150 lines) |
| uniqueness / flow law / inverse | `ODE_solution_unique_of_mem_Ioo`, `ODE_solution_unique_univ` | available |
| `C^∞` in time | `contDiff_succ_iff_deriv` induction with `deriv = X ∘ φ` | available |
| continuity in `(s, p)` | `dist_le_of_trajectories_ODE` (Lipschitz in `p`) + continuity in `s` | available |
| **smoothness in `p`** (needed for "diffeomorphism", `Dφ_s`, `c` smooth, clauses 6-7) | — | **missing** (see §0) |
| variational equation `∂_s Dφ_s = DX ∘ Dφ_s` from joint `C^2` | `ContDiffAt.isSymmSndFDerivAt`, `HasFDerivAt.clm_apply`, `hasFDerivAt_prodMk_right` | available (derived here, ≈ 150 lines) |
| infinitesimal identity `L_{X_H} α = H_z α` in coordinates | pure algebra after `fderiv` computations; the trick `α(DX_H w) = dH(w) − H_y w_y` avoids second derivatives of `H` | provable (≈ 200 lines) |
| conformal-factor ODE `ċ = (H_z ∘ φ) c`, solution `exp ∫` | `intervalIntegral.integral_hasDerivAt_right`, `HasDerivAt.exp`, constancy of `β e^{−∫}` (`is_const_of_deriv_eq_zero`) | available |
| pullback of a 1-form | no differential forms on manifolds in Mathlib; stated in coordinates as `alpha (φ s p) (fderiv ℝ (φ s) p v) = c s p * alpha p v` | by design |
| compositions smooth in `(a, p)` | `ContDiff.comp`, induction on `n` | available given joint smoothness of each flow |
| `C^k`-closeness on compacts | `iteratedFDeriv_comp_add_left`, `ContinuousLinearMap.iteratedFDeriv_comp_right`, `ContDiff.continuous_iteratedFDeriv`, compactness (`IsCompact.uniformContinuousOn_of_continuous` or a tube argument), `iteratedFDeriv_sub_apply` | available given joint smoothness |

### 1.3 Verdict and plan

Provable-with-new-infrastructure; the infrastructure is exactly one theorem.  Plan executed in
`ContactMotions.lean`:

* `SM.ContactMotions.IsGlobalFlow X φ` (Prop: `φ 0 p = p`, `HasDerivAt (φ · p) (X (φ s p)) s`);
  `globalFlow X := Classical.epsilon (IsGlobalFlow X)`.
* Unconditional: `exists_isGlobalFlow` / `exists_isGlobalFlow_of_hasCompactSupport` (a compactly
  supported `C^1` field on `ℝ³` has a global flow), `IsGlobalFlow.unique`, `.add`, `.bijective`,
  `.contDiff_time` (joint continuity in `(s, p)` via Grönwall is available but was not needed).
* `SM.SmoothDependence : Prop` — the missing theorem, stated once, as an explicit hypothesis
  (no placeholder declaration): every global flow of a compactly supported `C^∞` field on `ℝ³` is
  `C^∞` in `(s, p)`.
* Conditional on that hypothesis: the full bundle `ContactMotionsData` via
  `fd_contact_motions : SmoothDependence → ContactMotionsData`.
* Also unconditional: the contact identity for *any* jointly-`C^∞` global flow of `X_H`
  (`alpha_flow_eq`, `ContactMotionsHyp.contact_of_contDiff`), so the hypothesis is consumed only
  through the smoothness of `globalFlow` (`ContactMotionsHyp.contDiff_uncurry_hamFlow`).

Outcome (Part 2, same day): `ContactMotions.lean`, 896 lines, 0 errors, 0 warnings, axioms
`[propext, Classical.choice, Quot.sound]` for `SM.fd_contact_motions` and all unconditional
theorems; see `FD_84_86_REPORT.md`.  The `EuclideanSpace` coordinate algebra was handled with
`PiLp.proj` (`coordCLM`) and `!₂[…]`; the `iteratedFDeriv` bookkeeping for clause 7 with
`iteratedFDeriv_comp_add_left` + `ContinuousLinearMap.iteratedFDeriv_comp_right` and
`generalized_tube_lemma`.

Proving `SmoothDependence` itself: the classical route (difference quotients + Grönwall for `C^1`
dependence, then the augmented system `(X, DX·w)` for `C^k` by induction) is estimated at
4 000–6 000 lines of new Lean with high risk; out of this unit's budget.  Recorded as the gap.

## 2. Row 84 fd:transverse-neighborhood

### 2.1 Printed statement, clause by clause (sm-3:2395-2409)

1. "Let `α = dz − y dx` and let `T : ℝ/(2πℤ) → ℝ³` be a smooth embedded oriented circle with
   `α(T′) > 0`" — hypotheses: `T : ℝ → ℝ³`, `C^∞`, `2π`-periodic, injective modulo `2π`,
   `α_{T θ}(T' θ) > 0` (positive transverse; implies immersion).
2. "There are `δ > 0` and a smooth embedding `H : S¹ × D_δ → ℝ³` fixing the parametrized core `T`"
   — `H : ℝ × ℝ² → ℝ³`, `2π`-periodic in `θ`, `C^∞` on `ℝ × ball 0 δ`, immersion, injective
   modulo `2π`, topological embedding of the quotient (images of open sets relatively open),
   `H (θ, 0) = T θ`.
3. "`H^*α = h α_0`, `α_0 = dθ + u dv − v du`, `h > 0`" — for all `(θ, w)` in the domain and all
   `(τ, ω)`: `α_{H(θ,w)}(DH(θ,w)(τ, ω)) = h(θ, w) · (τ + u ω_v − v ω_u)`, `h > 0` smooth.
4. "There is an oriented Legendrian knot `L` in this neighbourhood whose positive transverse
   pushoff is transversely isotopic to `T`" — `L` smooth embedded circle in `H(S¹ × D_δ)` with
   `α(L') = 0`; a positive transverse pushoff (a positive-transverse circle of a transverse
   annulus with `L` as its `s = 0` circle, sm-3:2490-2504) that is transversely isotopic to `T`
   (smooth family of positive transverse embedded circles ending at an orientation-preserving
   reparametrization of `T`, sm-3:2503-2504 "`T(θ + κb)`, which is the same oriented transverse
   knot").
5. "An explicit compactly supported ordinary ambient isotopy carries the parametrized `L` to the
   parametrized `T`, preserving their orientations" — `Ψ : ℝ → ℝ³ → ℝ³` jointly `C^∞`, `Ψ 0 = id`,
   each `Ψ t` a diffeomorphism, `Ψ t p = p` outside a fixed compact set, `Ψ 1 (L θ) = T θ` for all
   `θ` (the parameter is carried, which is the orientation clause).

### 2.2 Mathlib facts needed and their status

| need | Mathlib | status |
|---|---|---|
| the frame `E_1 = ∂_x + y ∂_z`, `E_2 = ∂_y` and the chart `F(θ,u,v) = T + c (u E_1 + v E_2)` (2411-2419) | explicit map; `C^∞` by `contDiff_euclidean` | available |
| "inverse function theorem and compactness give a common radius on which every derivative is invertible" (2420-2422) | `HasStrictFDerivAt.toPartialHomeomorph` / `ContDiffAt.toPartialHomeomorph`; the *uniform* radius over the compact circle needs a new compactness argument (the local inverses have no uniform-size API) | new infrastructure, ≈ 400 lines |
| injectivity radius by the limiting argument (2422-2427) | sequential compactness on `S¹`; needs periodic-lift bookkeeping | new, ≈ 300 lines |
| `β = F^*α / a`, `dβ(∂_u, ∂_v) = 2` on the core, the linear family `α_t` and the contact condition `α_t ∧ dα_t ≠ 0` on a neighbourhood (2429-2439) | no exterior calculus on manifolds in Mathlib; must be done as explicit coordinate expressions of `fderiv` of `F`; the "common smaller neighbourhood" is another compactness argument | new, ≈ 500 lines |
| the Moser vector field `V_t` (2440-2450), its bound `‖V_t‖ ≤ C√(u²+v²)` and the a-priori estimate `r(t) ≤ e^{Ct} r(0)` (2455-2461) | Grönwall (`norm_le_gronwallBound_of_norm_deriv_right_le`) | available, but the setup is new (≈ 300 lines) |
| existence of `Φ_t`, `t ∈ [0,1]`, on the small disc, "fixing the core and invertible onto its image" (2461-2463) | Picard–Lindelöf for a *time-dependent* field on a *bounded* domain (the field is only defined near the core): needs the continuation argument with the a-priori bound | new, ≈ 300 lines |
| `Φ_1` is a diffeomorphism onto its image and `H = F ∘ Φ_1` is a smooth embedding (2463, 2472-2474) | **smooth dependence on the initial point — missing** | **blocked** |
| Cartan formula `d/dt Φ_t^*α_t = Φ_t^*(ν + L_{V_t} α_t)` and the scalar ODE (2465-2472) | no Lie derivative / Cartan formula in Mathlib; the coordinate derivation needs `∂_t D_pΦ_t` (variational equation, needs joint `C^2`) | blocked by the same gap, plus ≈ 400 new lines |
| `L_0`, the annulus `B`, `B^*α_0` (2476-2504) | explicit trigonometric computation | provable, ≈ 300 lines |
| the bump `χ`, the field `V`, its pushforward `X = H_* V` extended by zero (2505-2530) | `expNegInvGlue`/`Real.smoothTransition` for `χ`; pushforward needs `H⁻¹` smooth on the open image (inverse function theorem on the whole domain — new) | new, ≈ 400 lines |
| global flow `Ψ_t` of the compactly supported `X`, "ambient diffeomorphisms", orientation-preserving (2532-2541) | existence: this unit's `exists_isGlobalFlow`; **diffeomorphism: missing** (same gap) | **blocked** |
| `Ψ_t (L θ) = H(θ, (1−t) v(θ))` by uniqueness (2543-2547) | `ODE_solution_unique_univ` | available |

### 2.3 Verdict

Blocked: two of the printed steps (2463 and 2532-2541) need the flow to be a diffeomorphism, i.e.
the same missing smooth-dependence theorem as row 86, and even granting it the remaining new
infrastructure (uniform inverse-function radius, coordinate Gray/Moser computation with a
time-dependent form, pushoff and transverse-isotopy notions) is ≈ 3 000–5 000 lines — beyond
this unit.  Delivered: the faithful statement `SM.TransverseNeighborhoodData` as a compiling Prop
bundle (one field per printed clause, definitions of Legendrian/positive-transverse circles,
transverse annulus and pushoff, transverse isotopy, compactly supported ambient isotopy), no
theorem: `TransverseNeighborhood.lean`, 266 lines, 0 errors, 0 warnings.

## 3. Shared readings

* `ℝ³ = EuclideanSpace ℝ (Fin 3)` with `(x, y, z) = (p 0, p 1, p 2)`, as in row 85; `α_p(v) = v 2 − p 1 * v 0`.
* `S¹ = ℝ/2πℤ` is read through `2π`-periodic lifts on `ℝ` (the chart reading FR-PA-1 of row 85; the
  consumers of these rows apply them to parametrized circles).
* "smooth" = `ContDiff ℝ ∞`; "smooth embedding" of an open domain = `C^∞` + injective immersion +
  topological embedding (images of open sets relatively open in the image).
* Pullback of a 1-form along a map `f` is stated pointwise as `α_{f p}(Df(p) v)`.
