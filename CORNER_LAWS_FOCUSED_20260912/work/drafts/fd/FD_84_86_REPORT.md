# Rows 84 (fd:transverse-neighborhood) and 86 (fd:contact-motions) — report

Date: 2026-09-14.  Lemmas `fd:contact-motions` ("Explicit contact motions",
reference/SM/sm-3-statesum.tex:2586-2597, proof 2598-2611) and `fd:transverse-neighborhood`
("A transverse neighbourhood and its Legendrian pushoff", sm-3:2395-2409, proof 2410-2559).
Two rows of the fd block 84-88; row 85 (`ParameterAvoidance.lean`) is the style model, row 88 is
with a sibling agent.  Pure analysis, Mathlib only, no dependency on the diagram layer.
Feasibility memo: `work/drafts/fd/FD_84_86_FEASIBILITY.md` (Part 1 of the task).

| item | row 86 fd:contact-motions | row 84 fd:transverse-neighborhood |
|---|---|---|
| file | `work/drafts/fd/ContactMotionsFinal.lean` (1,437 lines; `ContactMotions.lean` + `SmoothDependence.lean`, §4 below) | `work/drafts/fd/TransverseNeighborhood.lean` (266 lines) |
| verdict | **proved unconditionally** (2026-09-14): `SM.SmoothDependence` — smooth dependence of an ODE flow on the initial point, which Mathlib lacks — is proved in the module as `SM.smoothDependence`; see §4 | **stated only** (compiling Prop bundle `SM.TransverseNeighborhoodData`, no theorem): blocked on the same missing theorem at two printed steps, plus ≈ 3 000–5 000 lines of further new infrastructure (memo §2) |
| main declaration | `SM.fd_contact_motions : SM.ContactMotionsData` (unconditional); also `SM.fd_contact_motions_of_smoothDependence : SM.SmoothDependence → SM.ContactMotionsData` and `SM.smoothDependence : SM.SmoothDependence` | `SM.TransverseNeighborhoodData : Prop` (definition) |
| bundle | `SM.ContactMotionsData` (8 fields, one per printed clause), hypotheses `SM.ContactMotions.ContactMotionsHyp` (2 fields) | `SM.TransverseNeighborhoodConclusion T δ H h L Ψ` (7 fields, one per printed clause), hypotheses `SM.TransverseNeighborhoodHyp T` (2 fields) |
| check | `cd work/lean && lake env lean ../drafts/fd/ContactMotionsFinal.lean` — 0 errors, 0 warnings, ≈ 10 s | `cd work/lean && lake env lean ../drafts/fd/TransverseNeighborhood.lean` — 0 errors, 0 warnings, ≈ 6 s |
| axioms (`#print axioms` on a /tmp copy) | `SM.fd_contact_motions` (unconditional), `SM.smoothDependence`, `SM.fd_contact_motions_of_smoothDependence`, `SM.ContactMotions.ContactMotionsHyp.isGlobalFlow`, `.hamFlow_unique`, `.contDiff_hamFlow_time`, `.contact_of_contDiff`, `SM.ContactMotions.alpha_flow_eq`, `SM.ContactMotions.exists_isGlobalFlow_of_hasCompactSupport`: all `[propext, Classical.choice, Quot.sound]` | `SM.TransverseNeighborhood.IsTransverseModel.alpha_core` (sanity lemma): `[propext, Classical.choice, Quot.sound]` |
| placeholders | none; every declaration is proved, including `SM.smoothDependence` | none; no theorem is claimed |
| intended home | `work/lean/SM/ContactMotions.lean` | `work/lean/SM/TransverseNeighborhood.lean` (statement layer); at porting time import `SM.ContactMotions` and drop the duplicate `SM.TransverseNeighborhood.alpha` |

## 1. Row 86 — clause → field map

Printed statement (sm-3:2586-2597): "For a smooth compactly supported H : ℝ³ → ℝ, the vector
field X_H = −H_y ∂_x + (H_x + y H_z) ∂_y + (H − y H_y) ∂_z has a global flow φ_H^s of
coorientation-preserving contact diffeomorphisms for α = dz − y dx: (φ_H^s)^*α = c_s^H α with a
smooth positive function c_s^H, its conformal factor.  Finite compositions of their small-time
flows depend smoothly on the times and are arbitrarily C^k-close to the identity on compact sets
for each fixed finite k."

Notation: `ℝ³ = EuclideanSpace ℝ (Fin 3)`, `(x, y, z) = (p 0, p 1, p 2)`;
`alpha p v = v 2 − p 1 * v 0` is `α_p(v)`; `pd H i p = fderiv ℝ H p (e i)` is `∂_i H`;
`hamVF H p = !₂[−H_y, H_x + y H_z, H − y H_y]` is `X_H`; `hamFlow H = globalFlow (hamVF H)` is `φ_H`
(`globalFlow X = Classical.epsilon (IsGlobalFlow X)`, the unique global flow);
`confFactor H s p = exp (∫_0^s pd H 2 (hamFlow H v p) dv)` is `c_s^H(p)`;
`composeFlows n Hs a p = φ_{H_0}^{a_0} (⋯ (φ_{H_{n−1}}^{a_{n−1}} p))`.

### Hypotheses: `ContactMotionsHyp H : Prop`

| tex | printed clause | field |
|---|---|---|
| 2587 | "smooth" | `smooth : ContDiff ℝ ∞ H` |
| 2587 | "compactly supported" | `compactSupport : HasCompactSupport H` |

### Conclusion: `ContactMotionsData : Prop`

| tex | printed clause | field |
|---|---|---|
| 2591 | "has a global flow `φ_H^s`" | `isGlobalFlow : ∀ H, ContactMotionsHyp H → IsGlobalFlow (hamVF H) (hamFlow H)` (`φ 0 p = p`, `HasDerivAt (φ · p) (X_H (φ s p)) s` for all `s, p`) |
| 2591 | "flow" (group law) | `flow_add : … → ∀ s t p, hamFlow H (s + t) p = hamFlow H s (hamFlow H t p)` |
| 2591-2592 | "diffeomorphisms" | `diffeo : … → ContDiff ℝ ∞ (uncurry (hamFlow H)) ∧ ∀ s, ContDiff ℝ ∞ (hamFlow H s) ∧ ContDiff ℝ ∞ (hamFlow H (−s)) ∧ LeftInverse (hamFlow H (−s)) (hamFlow H s) ∧ RightInverse …` |
| 2591-2593 | "contact … for `α = dz − y dx`: `(φ_H^s)^*α = c_s^H α`" | `contact : … → ∀ s p v, alpha (hamFlow H s p) (fderiv ℝ (hamFlow H s) p v) = confFactor H s p * alpha p v` (FR-CM-1) |
| 2591, 2593 | "coorientation-preserving", "positive" | `confFactor_pos : … → ∀ s p, 0 < confFactor H s p` (FR-CM-2) |
| 2593 | "a smooth positive function `c_s^H`, its conformal factor" | `confFactor_smooth : … → ContDiff ℝ ∞ (fun q : ℝ × ℝ³ => confFactor H q.1 q.2)` (FR-CM-3); the formula `c = exp ∫_0^s H_z ∘ φ^v` of sm-3:2603-2606 is the definition (`ContactMotions.confFactor_eq`) |
| 2594-2595 | "Finite compositions of their small-time flows depend smoothly on the times" | `compositions_smooth : ∀ n Hs, (∀ i, ContactMotionsHyp (Hs i)) → ContDiff ℝ ∞ (fun q : (Fin n → ℝ) × ℝ³ => composeFlows n Hs q.1 q.2)` (FR-CM-5) |
| 2595-2596 | "and are arbitrarily `C^k`-close to the identity on compact sets for each fixed finite `k`" | `compositions_close : ∀ n Hs, (∀ i, …) → ∀ K, IsCompact K → ∀ k ε, 0 < ε → ∃ δ > 0, ∀ a, (∀ i, |a i| < δ) → ∀ j ≤ k, ∀ p ∈ K, ‖iteratedFDeriv ℝ j (fun p => composeFlows n Hs a p − p) p‖ < ε` (FR-CM-6) |

Row theorem: `SM.fd_contact_motions : ContactMotionsData := fd_contact_motions_of_smoothDependence smoothDependence`,
where `SM.fd_contact_motions_of_smoothDependence (hsd : SmoothDependence) : ContactMotionsData` is assembled
from `ContactMotionsHyp.isGlobalFlow`, `.hamFlow_add`, `.contDiff_uncurry_hamFlow hsd`,
`contDiff_flow_space`, `.hamFlow_leftInverse`, `.hamFlow_rightInverse`, `.contact_of_contDiff`,
`confFactor_pos`, `.contDiff_confFactor_of_contDiff`, `contDiff_composeFlows`,
`composeFlows_close`.

### The hypothesis `SmoothDependence` (proved 2026-09-14, §4)

```
def SmoothDependence : Prop :=
  ∀ X : ℝ³ → ℝ³, ContDiff ℝ ∞ X → HasCompactSupport X →
    ∀ φ : ℝ → ℝ³ → ℝ³, IsGlobalFlow X φ → ContDiff ℝ ∞ (uncurry φ)
```
"Smooth ODE dependence" (sm-3:2611): the global flow of a `C^∞` compactly supported field is
`C^∞` in `(s, p)`.  Used exactly once, in `ContactMotionsHyp.contDiff_uncurry_hamFlow`.  Mathlib
(pin 85e3a25e) has, in `Mathlib/Analysis/ODE/`, existence (`IsPicardLindelof.*`), uniqueness
(`ODE_solution_unique*`), Grönwall (`dist_le_of_trajectories_ODE`, i.e. Lipschitz dependence on
the initial point) and `C^n` regularity *in time* (`IsPicardLindelof.contDiffOn_enat_Icc_of_hasDerivWithinAt`);
`Mathlib/Dynamics/Flow.lean` is topological; `Mathlib/Geometry/Manifold/IntegralCurve/*` has
existence/uniqueness/uniform time.  No declaration gives differentiability of the flow in the
initial point.  It is proved in `ContactMotionsFinal.lean` §7–§13 (≈ 550 new lines; route in §4
below and in `SMOOTH_DEPENDENCE_REPORT.md`), so the row is unconditional.

### What is proved without `SmoothDependence`

| declaration | content | tex |
|---|---|---|
| `ContactMotions.exists_isGlobalFlow` | a bounded globally Lipschitz field on a complete normed space has a global flow | 2607-2610 |
| `ContactMotions.exists_isGlobalFlow_of_hasCompactSupport` | a compactly supported `C^1` field on `ℝ³` has a global flow | 2607-2610 |
| `ContactMotionsHyp.isGlobalFlow` | `hamFlow H` is a global flow of `X_H` | 2591 |
| `ContactMotionsHyp.hamFlow_add`, `.hamFlow_leftInverse`, `.hamFlow_rightInverse`, `.hamFlow_bijective`, `.hamFlow_unique` | group law, inverse `φ^{−s}`, bijectivity, uniqueness | 2591, 2610 |
| `ContactMotionsHyp.contDiff_hamFlow_time` | `s ↦ φ_H^s p` is `C^∞` | 2611 |
| `ContactMotions.alpha_hamVF` | `α(X_H) = H` | 2599 |
| `ContactMotions.alpha_fderiv_hamVF` | `α_q(DX_H(q) w) = dH_q(w) − H_y(q) w_y` (the coordinate content of `ι_{X_H} dα = H_z α − dH`) | 2599-2600 |
| `ContactMotions.hasDerivAt_fderiv_flow` | the variational equation `∂_s Dφ_s = DX_H ∘ Dφ_s` for any jointly `C^∞` flow | — |
| `ContactMotions.hasDerivAt_alpha_flow` | `∂_s α_{φ_s p}(Dφ_s v) = H_z(φ_s p) α_{φ_s p}(Dφ_s v)`, i.e. `L_{X_H} α = H_z α` along the flow | 2601 |
| `ContactMotions.hasDerivAt_confFactorOf` | the scalar ODE `∂_s c = (H_z ∘ φ) c` | 2602 |
| `ContactMotions.alpha_flow_eq` | `(φ^s)^*α = exp(∫_0^s H_z ∘ φ^v) α` for any jointly `C^∞` global flow of `X_H` | 2603-2605 |
| `ContactMotions.contDiff_confFactorOf` | `c` is `C^∞` in `(s, p)` for any jointly `C^∞` flow | 2593 |
| `ContactMotions.contDiff_composeFlows`, `composeFlows_close` | clauses 6-7 given the joint smoothness of each flow | 2594-2596 |

So the hypothesis is consumed only through "`hamFlow H` is jointly `C^∞`"; everything the printed
proof does by hand is formalised.

### Route notes (Mathlib used)

* Global existence: `IsPicardLindelof.of_time_independent` on `[−(n+1), n+1]` with ball radius
  `a = L(n+1)`, `r = 0` (`mul_max_le` is an equality), then
  `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`,
  `HasDerivWithinAt.hasDerivAt` on the open interval; gluing `γ t := α_{⌈|t|⌉₊} t` with
  `ODE_solution_unique_of_mem_Ioo` and `HasDerivAt.congr_of_eventuallyEq`.
* Lipschitz/bounded from compact support: `HasCompactSupport.isCompact_range`,
  `Bornology.IsBounded.exists_norm_le`, `HasCompactSupport.fderiv`, `ContDiff.continuous_fderiv`,
  `lipschitzWith_of_nnnorm_fderiv_le`.
* Time smoothness: induction with `contDiff_one_iff_deriv`, `contDiff_succ_iff_deriv`
  (`deriv (φ · p) = X_H ∘ φ · p`), `contDiff_infty`.
* Variational equation: `ContDiff.fderiv_right`, `HasFDerivAt.comp_hasDerivAt`,
  `HasDerivAt.clm_apply`, `HasFDerivAt.clm_apply`, `ContDiffAt.isSymmSndFDerivAt`
  (`minSmoothness_of_isRCLikeNormedField`), `hasFDerivAt_prodMk_right`, `HasFDerivAt.unique`.
* Coordinates on `EuclideanSpace ℝ (Fin 3)`: `PiLp.proj` as `coordCLM i`, `contDiff_euclidean`,
  `!₂[…]` notation, `fin_cases`.
* Conformal factor: `intervalIntegral.integral_hasDerivAt_right`, `HasDerivAt.exp`,
  `is_const_of_deriv_eq_zero`, `intervalIntegral.integral_same`.
* Compositions: `contDiff_apply`, `contDiff_pi`, `Fin.tail`; closeness:
  `iteratedFDeriv_comp_add_left`, `ContinuousLinearMap.iteratedFDeriv_comp_right`,
  `ContinuousMultilinearMap.compContinuousLinearMapL`, `ContDiff.continuous_iteratedFDeriv`,
  `iteratedFDeriv_fun_zero`, `isOpen_biInter_finset`, `generalized_tube_lemma`, `pi_norm_lt_iff`.

### Fidelity readings (row 86)

FR-CM-1 (pullback stated pointwise on vectors, Mathlib has no form calculus); FR-CM-2
(coorientation-preserving = `c > 0`); FR-CM-3 (`c` jointly smooth, containing the printed
"smooth"); FR-CM-4 (diffeomorphism = `C^∞` with `C^∞` inverse `φ^{−s}`); FR-CM-5 (compositions for
any `n`, any Hamiltonians with the hypothesis, joint smoothness in `(a, p)`); FR-CM-6
(`C^k`-closeness = uniform bound on `‖D^j(Φ_a − id)‖`, `j ≤ k`, on `K`, for `|a_i| < δ`).  All are
recorded in the module docstring.

## 2. Row 84 — clause → field map (statement only)

Printed statement (sm-3:2395-2409): "Let α = dz − y dx and let T : ℝ/(2πℤ) → ℝ³ be a smooth
embedded oriented circle with α(T′) > 0.  There are δ > 0 and a smooth embedding
H : S¹ × D_δ → ℝ³ fixing the parametrized core T such that H^*α = hα₀, α₀ = dθ + u dv − v du,
h > 0.  There is an oriented Legendrian knot L in this neighbourhood whose positive transverse
pushoff is transversely isotopic to T.  An explicit compactly supported ordinary ambient isotopy
carries the parametrized L to the parametrized T, preserving their orientations."

Notation: circles are `2π`-periodic maps `ℝ → ℝ³` (FR-TN-1); `S¹ × D_δ` is
`solidTorus δ = univ ×ˢ Metric.ball 0 δ ⊆ ℝ × EuclideanSpace ℝ (Fin 2)`, `(u, v) = (w 0, w 1)`;
`alpha0 w τ η = τ + w 0 * η 1 − w 1 * η 0` is `α₀` on the tangent vector `(τ, η)`.

### Hypotheses: `TransverseNeighborhoodHyp T : Prop`

| tex | printed clause | field |
|---|---|---|
| 2397-2398 | "a smooth embedded oriented circle" | `circle : IsEmbeddedCircle T` (`C^∞`, `Periodic T (2π)`, injective modulo `2π`, `deriv T θ ≠ 0`) |
| 2398 | "with `α(T′) > 0`" | `transverse : IsPositiveTransverse T` (`∀ θ, 0 < alpha (T θ) (deriv T θ)`) |

### Conclusion: `TransverseNeighborhoodData := ∀ T, Hyp T → ∃ δ H h L Ψ, TransverseNeighborhoodConclusion T δ H h L Ψ`

| tex | printed clause | field |
|---|---|---|
| 2399-2404 | "There are `δ > 0` and a smooth embedding `H : S¹ × D_δ → ℝ³` fixing the parametrized core `T` such that `H^*α = hα₀`, `h > 0`" | `model : IsTransverseModel T δ H h` — fields `delta_pos`, `smooth` (`ContDiffOn ℝ ∞ H (solidTorus δ)`), `periodic`, `injective` (modulo `2π`), `immersion` (`Injective (fderiv ℝ H (θ,w))`), `open_map` (topological embedding, FR-TN-2), `core` (`H (θ, 0) = T θ`), `factor_pos`, `pullback` (`alpha (H (θ,w)) (fderiv ℝ H (θ,w) (τ, η)) = h (θ,w) * alpha0 w τ η`) |
| 2405 | "There is an oriented Legendrian knot `L`" | `legendrian_circle : IsEmbeddedCircle L`, `legendrian : IsLegendrian L` |
| 2405 | "in this neighbourhood" | `mem_neighbourhood : ∀ θ, L θ ∈ H '' solidTorus δ` |
| 2405-2406 | "whose positive transverse pushoff is transversely isotopic to `T`" | `pushoff_isotopic : ∃ T', IsPositivePushoff L T' ∧ TransverselyIsotopic T' T` (FR-TN-4, FR-TN-5) |
| 2406-2407 | "An explicit compactly supported ordinary ambient isotopy" | `ambient : IsCompactlySupportedAmbientIsotopy Ψ` (`t ∈ [0,1]`, jointly `C^∞`, `Ψ 0 = id`, each `Ψ t` a `C^∞` bijection with `C^∞` inverse, identity outside a compact set) |
| 2407-2408 | "carries the parametrized `L` to the parametrized `T`, preserving their orientations" | `carries : ∀ θ, Ψ 1 (L θ) = T θ` |

Auxiliary notions: `IsPushoffAnnulus L ε b B` (sm-3:2490-2502: smooth embedded periodic annulus
`B(θ, s)`, `−ε < s < b`, `B(·,0) = L`, transverse to the contact planes, positive-transverse
circles for `s > 0`), `IsPositivePushoff L T'` (`T' = B(·, s₀)`, `0 < s₀ < b`),
`IsCircleReparam ρ` (`ρ' > 0`, `ρ(θ + 2π) = ρ θ + 2π`), `TransverselyIsotopic T₀ T₁` (smooth family
of positive transverse embedded circles on `[0,1]` from `T₀` to `T₁ ∘ ρ`).  Sanity lemmas (not
clauses): `alpha0_zero_left`, `alpha0_core`, `IsTransverseModel.alpha_core`
(`α_{T θ}(DH(θ,0)(1,0)) = h(θ,0)`).

### Why not proved (memo §2, summary)

* sm-3:2461-2463 "Smooth ODE existence, continuation and uniqueness give a flow `Φ_t`, fixing the
  core and invertible onto its image" and 2472-2474 `H = F ∘ Φ_1` a smooth embedding: needs `Φ_1`
  to be a diffeomorphism, i.e. smooth dependence on the initial point — the same gap as row 86,
  here for a time-dependent field on a bounded domain.
* sm-3:2532-2541 "Smooth ODE continuation gives its global flow `Ψ_t` … thus these are ambient
  diffeomorphisms": existence is this unit's `exists_isGlobalFlow_of_hasCompactSupport`;
  "diffeomorphisms" is the gap again.
* Even granting the gap: the uniform inverse-function radius (2420-2427), the coordinate
  Gray–Moser computation with the time-dependent family `α_t` and the Cartan formula (2429-2472),
  the pushforward `X = H_* V` (2522-2530) are ≈ 3 000–5 000 new lines.

### Fidelity readings (row 84)

FR-TN-1 (periodic lifts for `S¹`; embedded compact circle = injective immersion); FR-TN-2 (smooth
embedding of the open solid torus = `C^∞` + injective mod period + immersion + images of open sets
relatively open); FR-TN-3 (`h` quantified with `H`, determined by it, only positivity demanded);
FR-TN-4 (positive pushoff = small positive circle of a transverse annulus with `L` as its zero
circle, the paper's "source convention" sentence 2501-2502); FR-TN-5 (transverse isotopy may end at
an orientation-preserving reparametrization of `T`, sm-3:2503-2504).

## 3. Risks

* Row 86: closed unconditionally on 2026-09-14 (§4).  Reviewer input: the statement part
  `ContactMotionsFinal.lean` lines 130–894 (byte-identical to `ContactMotions.lean` lines 106–869
  up to two docstring edits) and the readings FR-CM-1…7 of §4.
* Row 86: `EuclideanSpace` coordinate lemmas use `PiLp.proj` (`coordCLM`) rather than
  `EuclideanSpace.proj` (instance-path mismatch in `HasDerivAt` composition); `ω` is reserved by
  `open scoped ContDiff` (tangent vectors are named `η`).
* Row 84: the bundle is a statement with no consumer check; `alpha` is duplicated in
  `SM.TransverseNeighborhood` (to be replaced by `SM.ContactMotions.alpha` at porting time).  The
  pushoff notion (FR-TN-4) is the paper's; if a later row needs Etnyre's convention directly, a
  bridge lemma is required.
* Both: no `lake build`; both files are drafts compiled with `lake env lean`; for row 86 the
  name-clash scan and the `import Supplemental` test are done (§4); for row 84 a joint-import test
  is needed before porting (distinct namespaces `SM.ContactMotions`, `SM.TransverseNeighborhood`,
  no shared top-level names except the intended `SM.SmoothDependence`, `SM.ContactMotionsData`,
  `SM.fd_contact_motions`, `SM.TransverseNeighborhoodHyp`, `SM.TransverseNeighborhoodConclusion`,
  `SM.TransverseNeighborhoodData`).

## 4. Row 86 now unconditional (2026-09-14)

`SM.SmoothDependence` is proved.  The final row-86 module for porting is
**`work/drafts/fd/ContactMotionsFinal.lean`** (1,437 lines) = `ContactMotions.lean` (statement part
byte-identical, two docstring edits) + `SmoothDependence.lean` §2–§8 re-targeted at
`ContactMotions.IsGlobalFlow` (module §7–§13), with the two extra imports
`Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension`, `Mathlib.Analysis.Calculus.ContDiff.FiniteDimension`.
(`ContactMotions_SmoothDependence_MERGED.lean` was the mechanical merge test; superseded, may be deleted.)

| item | value |
|---|---|
| row theorem | `SM.fd_contact_motions : SM.ContactMotionsData` (line 1434, unconditional, `:= fd_contact_motions_of_smoothDependence smoothDependence`) |
| conditional form (renamed) | `SM.fd_contact_motions_of_smoothDependence : SM.SmoothDependence → SM.ContactMotionsData` (line 905; the former `fd_contact_motions`) |
| the theorem | `SM.smoothDependence : SM.SmoothDependence` (line 1430), from `SM.ContactMotions.contDiff_uncurry` (line 1386; any finite-dimensional real normed `E : Type`) |
| compile | `cd work/lean && lake env lean ../drafts/fd/ContactMotionsFinal.lean` — 0 errors, 0 warnings |
| axioms (`#print axioms`, /tmp copy) | `SM.fd_contact_motions`, `SM.smoothDependence`, `SM.fd_contact_motions_of_smoothDependence`, `SM.ContactMotionsData`: `[propext, Classical.choice, Quot.sound]` |
| forbidden strings | none: no placeholder tactic, no `#print`, no `#eval`, no "modulo" |
| **statement part** (reviewer input) | **lines 130–894** (`namespace SM` … last field of `ContactMotionsData`) = `ContactMotions.lean` lines 106–869, byte-identical except (a) the §6 header docstring, line 847 (was line 823), and (b) the docstring of `SmoothDependence`, lines 851–856 (was 827–831); verified by a line-by-line comparison.  Inside it: `e`/`alpha`/`pd`/`hamVF` 144–158, `coordCLM` 182, `IsGlobalFlow` 244–246, `globalFlow` 453, `confFactorOf` 604, `hamFlow` 677, `confFactor` 680, `ContactMotionsHyp` 683–687, `composeFlows` 753–755, `SmoothDependence` 857–859, `ContactMotionsData` 864–894. |
| module docstring | lines 11–128: rewritten to describe the module as it is (row unconditional, proof route §7–§13), cites sm-3:2586-2597 (statement) and 2598-2611 (proof); FR-CM-1…7 |
| name-clash scan | every top-level declaration of the module (126 names, structure fields included, fully qualified via the Lean environment) against every declaration of `work/lean` (13,337 parsed in 649 files, namespaces tracked): **0 exact clashes**.  Six short-name coincidences in other namespaces only: `ContactMotionsHyp.smooth` ~ `SM.CurlWitness.smooth`, `SM.Link.IsRealizable.smooth`, `SM.Link.Record.smooth`, `SM.Link.RecordIso.smooth`, `SM.RoundingWitness.smooth`; `IsGlobalFlow.add`/`.neg`/`.zero` ~ `SM.Link.InSupportM.add`/`.neg`/`.zero`; `IsGlobalFlow.hasDerivAt` ~ `SM.SmoothLoop.hasDerivAt`; `IsGlobalFlow.unique` ~ `CV.IsLinkingNumber.unique`.  Definitive check: the module compiles after `import Supplemental` (the built root, 70 modules).  Importing all 613 built `SM.*` oleans at once is impossible for a pre-existing library-internal reason unrelated to row 86 (`SM.contactForm` is declared in both `SM.TransverseFront` and `SM.LinkingCalculus`). |

### Proof route of `smoothDependence` (module §7–§13; details in `SMOOTH_DEPENDENCE_REPORT.md`)

Time reversal (`IsGlobalFlow.neg`) and Lipschitz dependence by Grönwall
(`dist_le_of_trajectories_ODE`); the variational estimate `hasFDerivAt_flow_of_variational` — if
`D' = DX(φ t p) ∘ D`, `D 0 = 1`, then `φ T` has derivative `D T` at `p` (mean value inequality +
`norm_le_gronwallBound_of_norm_deriv_right_le` on the error `φ t (p+h) − φ t p − D t h`); the
augmented system `(x, A) ↦ (X x, DX(x) ∘ A)` on `E × (E →L E)` cut off by a bump in `A`
(`augFieldCut`, again `C^∞` compactly supported); induction on the order (`SpaceSmooth k`,
`contDiff_succ_iff_fderiv`) giving `φ s ∈ C^∞` in space; joint smoothness by suspension — the
time-one map of the flow of `(τ, x) ↦ (0, χ(τ) • X x)` is `(τ, φ τ x)` for `|τ| < R`.

### Readings and fidelity risks of the row-86 statement — what the reviewer must see

Printed statement sm-3:2586-2597; proof 2598-2611.  Lean: `ℝ³ = EuclideanSpace ℝ (Fin 3)`,
`(x, y, z) = (p 0, p 1, p 2)`, "smooth" = `ContDiff ℝ ∞` (`C^∞`, not analytic).

* **FR-CM-0 (the objects).** `X_H` (2588-2590) is `hamVF H p = !₂[−H_y, H_x + y H_z, H − y H_y]`
  with `pd H i p = fderiv ℝ H p (e i)`; `α = dz − y dx` is `alpha p v = v 2 − p 1 * v 0`; the flow
  `φ_H` (2591) is `hamFlow H = globalFlow (hamVF H) = Classical.epsilon (IsGlobalFlow (hamVF H))`,
  i.e. *a* global flow chosen by choice for every `H`, which under `ContactMotionsHyp H` is *the*
  global flow (`hamFlow_unique`, from `IsGlobalFlow.unique`); `IsGlobalFlow X φ` is
  `φ 0 p = p ∧ ∀ s p, HasDerivAt (φ · p) (X (φ s p)) s`.  Risk: a reviewer must accept that the
  printed "has a global flow `φ_H^s`" is rendered by a definite description plus the field
  `isGlobalFlow` (2591), not by an existential.
* **FR-CM-1 (pullback, 2591-2593).** `(φ_H^s)^*α = c_s^H α` is stated pointwise on tangent vectors:
  `alpha (hamFlow H s p) (fderiv ℝ (hamFlow H s) p v) = confFactor H s p * alpha p v` for all
  `p, v`.  Mathlib has no pullback calculus of differential forms.  Risk: none mathematically
  (the identity of 1-forms is exactly this identity on all vectors); the reviewer should check the
  direction (`fderiv` of `φ^s` at `p` applied to `v`, evaluated at `φ^s p`).
* **FR-CM-2 (coorientation-preserving, 2591; "positive", 2593).** `0 < confFactor H s p`.
* **FR-CM-3 (smooth conformal factor, 2593).** `confFactor H s p := exp (∫_0^s pd H 2 (hamFlow H v p) dv)`
  — the *definition* is the printed formula of 2603-2606, and `contact` is the identity with that
  factor; `confFactor_smooth` gives `C^∞` jointly in `(s, p)`, containing the printed "smooth
  function `c_s^H`".  Risk: the reviewer must accept that `c` is defined by the formula rather than
  produced existentially (this is stronger: it pins the factor down).
* **FR-CM-4 (diffeomorphisms, 2591-2592; inverse by backwards uniqueness, 2610).** `diffeo`:
  `hamFlow H` is `C^∞` jointly in `(s, p)`, each `hamFlow H s` and `hamFlow H (−s)` is `C^∞`, and
  `hamFlow H (−s)` is a two-sided inverse of `hamFlow H s` (`LeftInverse`, `RightInverse`).
* **FR-CM-5 (compositions depend smoothly on the times, 2594-2595).**
  `composeFlows n Hs a p = φ_{H_0}^{a_0} (⋯ (φ_{H_{n−1}}^{a_{n−1}} p))` for any `n`, any Hamiltonians
  `Hs : Fin n → ℝ³ → ℝ` each satisfying the hypothesis, any `a : Fin n → ℝ`;
  `compositions_smooth` is `C^∞` jointly in `(a, p) ∈ ℝ^n × ℝ³` for *all* times (the printed
  "small-time" is not a restriction here; it enters only in FR-CM-6).  Risk: reading "finite
  compositions of their small-time flows" as compositions of flows of possibly *different*
  Hamiltonians (the paper's use); the Lean is the general reading, which contains the same-`H` one.
* **FR-CM-6 (`C^k`-closeness, 2595-2596).** `compositions_close`: for every compact `K`, `k : ℕ`,
  `ε > 0` there is `δ > 0` such that `(∀ i, |a i| < δ) → ∀ j ≤ k, ∀ p ∈ K,
  ‖iteratedFDeriv ℝ j (fun p => composeFlows n Hs a p − p) p‖ < ε`.  Readings: "`C^k`-close" =
  uniform bound on the derivatives of order `≤ k` on `K`; "arbitrarily" = `∀ ε`; "small-time" =
  `|a_i| < δ`; `δ` may depend on `K, k, ε` and the `H_i`; the norm is the operator norm induced
  by the Euclidean norm (immaterial, all norms on `ℝ³` are equivalent and `ε` is arbitrary).
* **FR-CM-7 (smooth ODE dependence, 2611).** The paper cites it as standard; here it is the theorem
  `smoothDependence`, proved for `C^∞` compactly supported fields on any finite-dimensional real
  normed space `E : Type` (`ContactMotions.contDiff_uncurry`) and specialised to `ℝ³`.  The
  hypothesis `ContDiff ℝ ∞ X` + `HasCompactSupport X` is exactly what `X_H` satisfies for a smooth
  compactly supported `H` (`contDiff_hamVF`, `hasCompactSupport_hamVF`).
* **Hypotheses (2587).** `ContactMotionsHyp H`: `ContDiff ℝ ∞ H` and `HasCompactSupport H`; every
  field of `ContactMotionsData` is quantified as `∀ H, ContactMotionsHyp H → …`.
* **Not formalised (by design).** The Lie-derivative formulation `L_{X_H} α = H_z α` (2599-2601)
  appears only as its coordinate content along the flow (`hasDerivAt_alpha_flow`); the printed
  proof steps are not clauses of the statement.
