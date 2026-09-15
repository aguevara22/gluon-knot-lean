# GF_PLAN.md — leaf plan for `GF_Skeleton.lean` (row 87 fd:generic-front)

Date: 2026-09-14.  Skeleton: `work/drafts/fd/GF_Skeleton.lean` (625 lines; 0 errors, 0 warnings;
26 leaves with `sorry`; statement part lines 26-202 byte-identical to `GenericFront_Statement.lean`
79-255; `#print axioms SM.fd_generic_front` = `[propext, sorryAx, Classical.choice, Quot.sound]`,
`sorryAx` only through the leaves; `concat_one`, `hamIsotopy_one` axiom-clean).  Imports the built
`SM.ContactMotions` (row 86: `composeFlows`, `hamFlow`, `hamVF`, `globalFlow`, `fd_contact_motions`) and
`SM.ParameterAvoidance` (row 85: `ParameterAvoidanceHyp`, `zeroParams`, `exists_param_avoiding`,
`ParameterAvoidanceHyp.isClosed_zeroParams`, `.interior_zeroParams_eq_empty`).  Independent of the
row-84 skeleton (its notions are the copies in `SM.GenericFront`).
Check: `cd work/lean && lake env lean ../drafts/fd/GF_Skeleton.lean`.  Route: `FD_84_87_FEASIBILITY_v2.md` §2.

Notation: `hamIsotopy n Hs a s = composeFlows n Hs (s • a)` (the path `Φ_{sa}`); `xParam L n Hs a θ`
= `x`-coordinate of `Φ_a(L θ)`; `frontParam` = `(x_a, z_a)`; `par : ℝ^n → (Fin n → ℝ)`; `cuspMap`
= `(x_a′, x_a″)` on `ℝ^1 × ℝ^n`; `Cmap`, `Rmap`, `K2 δc`, `K3 δc` as printed (sm-3:2685-2690);
`Stage1` (embedded, Legendrian, `NoDoubleZero`), `Stage2` (+ collar `LocallyInjectiveFront`,
`NoCuspOnBranch`, `NoTriple`), `Stage3` (+ transverse, finite double points); `cuspHam f y₀ A` = `ψ`,
`cuspFlowMap ψ s` the explicit flow; `concat Φ Ψ` the flat concatenation (`Real.smoothTransition`).

## 0. Numerical truth checks (`/tmp/fd/probe_gf.py`, finite differences)

(i) `X_{H^x} = (1, 0, y_q)`, `X_{H^z} = (0,0,1)`, `X_{H₂}(q) = 0`, `x`-velocity of `H₂` is `y − y₀`
(P3.1) — exact; (ii) `∂_s cuspFlowMap = X_{ψ(y)} ∘ cuspFlowMap` (P5.1) — agree to `10⁻⁶`;
(iii) germ (P5.3): for `f = x₀ + Au² + ½u³ + 0.3u⁴` and the Legendrian `z = z₀ + ∫ y f′`, after the
time-one map `x − x₀ = Au²` and `z − z₀ = Ay₀u² + ⅔Au³` to 8 digits at `u = 0.05, −0.1, 0.2`;
(iv) P1.1 columns at a double zero: `(y′, y″)`, `(0, y′²)`, det `= y′³` — exact; (v) P4.1 determinant
identity `x′(θ)z′(η) − z′(θ)x′(η) = x′(θ)x′(η)(y(η) − y(θ))` — exact; (vi) P2.1 integration by parts
`z(θ₂) − z(θ₁) = ∫ y′(X − x)` for a cusp curve, `0.01800000` both sides.

**Leaf corrected during review:** P5.4 as first drafted (no hypotheses on `f′(y₀)`, `f″(y₀)`) was
FALSE (`ψ` is then only `O(u²)`); the skeleton now assumes `f′(y₀) = 0`, `f″(y₀) = 2A`.

## 1. Unit table

| unit | leaves | depends on | est. lines | content |
|---|---|---|---|---|
| P0 | P0.1–P0.3 (3) | row 86 | 400 | `Φ_{sa}` is a contact isotopy; contactomorphisms preserve Legendrian embedded circles; `∂_{aᵢ}Φ_a|₀ = X_{Hᵢ}` |
| P1 | P1.1–P1.4 (4) | P0.3, row 85 | 800 | zeros of `(x′,x″)`: rank-2 family, avoidance ⇒ `NoDoubleZero`, finite cusps, `y′ ≠ 0` at cusps |
| P2 | P2.1–P2.2 (2) | — | 600 | uniform collar; stability of `Stage1` + collar under small parameters |
| P3 | P3.1–P3.4 (4) | P0.3, P2 | 1 000 | local `X_H` models; the `C`/`R` family with ranks 3, 4; avoidance ⇒ no cusp on branch, no triple |
| P4 | P4.1–P4.2 (2) | — | 350 | transverse double points; finiteness |
| P5 | P5.1–P5.7 (7) | P0, P1.3/1.4, row 86 | 1 500 | explicit `ψ(y)`-flow, local graph, exact germ, `C²`-small cut-off Hamiltonian, `C²`-closeness of time-one maps, stability of `Stage3`, assembly over the cusps |
| P6 | P6.1–P6.4 (4) | — | 450 | concatenation is a contact isotopy; annulus and positive circles carried; circles of an annulus embedded |
| PROVED in skeleton | — | — | ≈ 120 | `hamIsotopy_one`, `step1`, `step2` (with the monotonicity of `ParameterAvoidanceHyp` in the radius and the two-set avoidance via `interior_union_isClosed_of_interior_empty`), `step3`, `isGenericFront_of_stage3`, `concat_one`, row theorem |
| total | 26 | | ≈ 5 200 | (memo estimate 5 200) |

Order: P0 → P1 → P2 → P3 → P4 → P6 → P5 (P5 last; only the `exact_germ` clause depends on it).
P2, P4, P6 depend only on the statement notions and can start at once.

## 2. Leaves

Format: **id `name` (line)** — statement · sketch · Mathlib/project · size · truth.

### P0 (sm-3:2632-2638)
- **P0.1 `isContactIsotopy_hamIsotopy` (225)** — `s ↦ composeFlows n Hs (s•a)` is an `IsContactIsotopy` · `ambient.smooth`: `fd_contact_motions.compositions_smooth n Hs hHs` composed with `(s,p) ↦ (s•a, p)`; `zero`: `composeFlows_zero` + `ContactMotionsHyp.hamFlow_zero`; `diffeo`: inverse = reversed composition of `hamFlow (Hs i) (−s aᵢ)` (induction on `n`, `hamFlow_leftInverse/rightInverse`; smooth by `fd_contact_motions.diffeo`); `support`: `K = ⋃ᵢ tsupport (hamVF (Hs i))` (`HasCompactSupport` of each, `Finset` union compact); each flow fixes points outside its support (as `globalFlow_fixed_of_notMem` in `TN_Skeleton.lean`, or `hamFlow_unique` against the constant curve); `contact`: chain rule, `fd_contact_motions.contact` and `confFactor_pos`, product of the `c`'s · 300 · true.
- **P0.2 `contact_preserves_legendrian` (231)** — `Φ_s ∘ L` embedded Legendrian · smooth: `ContDiffOn` slice of `uncurry Φ`; periodic: trivial; injective: from the inverse; immersion: `deriv (Φ_s ∘ L) = DΦ_s(L θ)(L′)` and `DΦ_s` injective (`DΨ ∘ DΦ_s = id` by chain rule on `Ψ ∘ Φ_s = id`); Legendrian: `alpha (Φ p)(DΦ v) = c · alpha p v = 0` · `HasFDerivAt.comp_hasDerivAt`, `fderiv_comp` · 80 · true.
- **P0.3 `fderiv_composeFlows_zero` (237)** — `∂_{aᵢ}(Φ_a p)|₀ = X_{Hᵢ}(p)` · induction on `n`: `composeFlows (n+1) Hs a p = hamFlow (Hs 0) (a 0) (composeFlows n …)`; at `a = 0` inner map is `id`, `hamFlow (Hs 0) 0 = id`, `D_p hamFlow^0 = id`; `∂_s hamFlow s p|₀ = X_H p` (`IsGlobalFlow.hasDerivAt`); joint smoothness for the chain rule (`compositions_smooth`) · `HasFDerivAt.comp`, `fderiv_pi`-style for `Pi.single` · 150 · true.

### P1 (sm-3:2639-2658; row 85 with `(d,q) = (1,2)`)
- **P1.1 `exists_cusp_avoidance` (296)** — a family `Hs` and radius `r` with `ParameterAvoidanceHyp 1 n 2 Kper1 0 r (cuspMap L n Hs)` · zero set `Z = {θ ∈ [0,2π] : x′ = x″ = 0}` compact; if empty, `n = 0` and `‖(x′,x″)‖ ≥ m > 0` (`IsCompact.exists_isMinOn`) gives no zeros for small `a` (continuity in `a`), rank vacuous; else for each `θ₀ ∈ Z`, `y′(θ₀) ≠ 0` (P1.4-type argument), bump Hamiltonians `H₂ = χ·(−½(y−y₀)²)`, `H₃ = χ·(−⅙(y−y₀)³)` (`ContDiffBump`, `ContactMotionsHyp`); columns of `∂_a cuspMap` at `(θ₀, 0)`: `(y′, y″)`, `(0, y′²)` (P0.3, `hamVF` of `H₂, H₃` where `χ = 1`, `∂_θ` of `(y−y₀)`, `½(y−y₀)²`), det `y′³ ≠ 0`; the `2×2` minor is continuous in `(θ, a)`, nonzero on a neighbourhood of `(θ₀,0)`; finitely many neighbourhoods cover `Z × {0}` (`IsCompact.elim_finite_subcover`); on the complement of their union in `[0,2π]`, `‖cuspMap(·,0)‖ ≥ m > 0`, so for `‖a‖ < r` no zero lies there (uniform continuity); `rank`: `finrank (range D) = 2` from a nonzero `2×2` minor (`rank_eq_iff_range_eq_top`, surjectivity from two independent images); `smooth`: `cuspMap` is `C^∞` (θ-derivatives of the jointly smooth `xParam`, as `ContactMotions.iteratedFDeriv_partial`) · 450 · true (probe (iv)).
- **P1.2 `noDoubleZero_of_notMem` (303)** — avoidance ⇒ `NoDoubleZero (Φ_a ∘ L)` · unfold `zeroParams`; for `θ ∈ [0,2π]` direct; general `θ`: `Φ_a ∘ L` is `2π`-periodic (`L` is), `deriv` of a periodic function is periodic (`deriv_comp_add_const`), reduce `θ` by `Int.fract`/`toIcoMod` · 80 · true.
- **P1.3 `finite_cusps_of_stage1` (310)** — finitely many cusps in one period · zeros of `x′` in the compact `Icc 0 (2π)` are isolated (`x″ ≠ 0` at each: `HasStrictDerivAt` ⇒ locally injective, `x′` nonzero on a punctured neighbourhood) ⇒ `IsDiscrete`/`IsCompact.finite` or `Set.Infinite.exists_accPt_of_subset_isCompact` for the contradiction; `x′` continuous (`ContDiff.continuous_deriv`) · 120 · true.
- **P1.4 `deriv_y_ne_zero_at_cusp` (314)** — `y′ ≠ 0` at cusps · `z′ = y x′ = 0`, `x′ = 0`, `deriv L θ ≠ 0` (immersion) ⇒ `y′ ≠ 0`; coordinates of `deriv L` via `hasDerivAt_coord`-type lemma (`PiLp.proj`) · 40 · true.

### P2 (sm-3:2659-2685)
- **P2.1 `exists_collar` (336)** — `∃ δc, LocallyInjectiveFront L δc` · finite cover of `[0,2π]` by open intervals: regular (`x′` of fixed sign) and critical (one zero of `x′`, `x″`, `y′` of fixed sign); front injective on each: regular — `x` strictly monotone (`strictMonoOn_of_deriv_pos`); critical — for `θ₁ < θ_c < θ₂`, `x(θ₁) = x(θ₂) = X`: `z(θ₂) − z(θ₁) = ∫_{θ₁}^{θ₂} y x′ = [y x]_{θ₁}^{θ₂} − ∫ y′ x = ∫ y′ (X − x)` (`intervalIntegral.integral_mul_deriv_eq_deriv_mul`), integrand of fixed sign and not a.e. zero (`intervalIntegral_pos_of_pos_on` after a sign normalisation) ⇒ `≠ 0`; Lebesgue number: `lebesgue_number_lemma_of_metric` on the compact circle (via `[0,2π]` with periodic wrap: use `circDist`) · 300 · true (probe (vi)).
- **P2.2 `stage1_stable` (342)** — `∃ r > 0, ∀ ‖a‖ < r`, `Stage1` and the collar `δc` persist · `Stage1.circle/legendrian`: P0.2 with `hamIsotopy m Hs (par a)` at `s = 1` (`hamIsotopy_one`); `NoDoubleZero`: `‖(x_a′, x_a″)‖ ≥ m/2` for small `a` by uniform continuity of the jointly smooth map on `[0,2π] × closedBall 0 1`; collar: the sign conditions defining the cover intervals are open in `a` (`generalized_tube_lemma` on compact closed subintervals × `{0}`), so the same intervals and the same Lebesgue number work · 300 · true (sm-3:2675-2677).

### P3 (sm-3:2686-2714; row 85 with `(2,3)`, `(3,4)`)
- **P3.1 `hamVF_local_models` (372)** — values of `X_H` at `q` for `χ·H^x`, `χ·H^z`, `χ·H₂` with `χ = 1` near `q` · `hamVF` uses `fderiv H q` and `H q`; `Filter.EventuallyEq.fderiv_eq` (`χ·H =ᶠ H`), then `pd` computations: `H^x_y = −1`, `H^x_x = H^x_z = 0`, `H^x − y H^x_y = y_q`; `H^z`: all derivatives `0`, value `1`; `H₂`: derivative `−(y − y_q) = 0` at `q`, value `0` · `fderiv_const_mul`, `EuclideanSpace` coordinates as in `ContactMotions` (`coordCLM`) · 100 · true (probe (i)).
- **P3.2 `exists_CR_avoidance` (381)** — one family, radius `≤ r₀`, `ParameterAvoidanceHyp` for `Cmap` on `K2 δc` and `Rmap` on `K3 δc` · zero sets `Z_C ⊆ K2`, `Z_R ⊆ K3` compact; at `(θ,η) ∈ Z_C`: `L θ ≠ L η` (embedded, `circDist ≥ δc`), disjoint balls, `H₂` at `L θ` (changes `x′(θ)` by `y′(θ) ≠ 0`, P1.4, and nothing at `η`), `H^x, H^z` at `L η` (independent `(x,z)`-velocities `(1,y_η)`, `(0,1)`, supports missing `L θ`); the `3×3` minor is block-triangular, nonzero; at `(θ,η,τ) ∈ Z_R`: `H^x, H^z` at `L η` and at `L τ`, `4×4` block-diagonal minor; finitely many charts cover both zero sets, positive minima on the compact complements, shrink to `r ≤ r₀`; `dim_lt`: `2 < 3`, `3 < 4`; `smooth`: `Cmap`, `Rmap` are `C^∞` (jointly smooth `frontParam`, θ-derivative of `xParam`) · 600 · true.
- **P3.3 `noCuspOnBranch_of_C` (390)** — `C ≠ 0` on `K2 × {a}` + collar ⇒ `NoCuspOnBranch` · given `θ ∈ cuspSet`, `η` with `front η = front θ`, `¬SameParam`: reduce both to `[0,2π)` (`toIcoMod`), if `circDist ≥ δc` then `(θ̄, η̄) ∈ K2` and `Cmap = 0` contradicts `ha`; else the collar gives `front θ ≠ front η` · periodicity of `Φ_a ∘ L`, `cuspMap`/`frontParam` unfolding · 150 · true.
- **P3.4 `noTriple_of_R` (398)** — as P3.3 with triples: if all three pairwise `circDist ≥ δc` then `Rmap = 0` in `K3`; otherwise some pair is within `δc` and the collar contradicts equality of their fronts · 150 · true.

### P4 (sm-3:2715-2730)
- **P4.1 `transverse_double_of_stage2` (454)** — every double point is transverse · both regular: `x′(θ) ≠ 0` else `θ ∈ cuspSet` and `η` is on another branch (`NoCuspOnBranch`); `y(θ) ≠ y(η)`: else `L θ = L η` (equal `x, z` and `y`) contradicting injectivity mod `2π`; `z′ = y x′` ⇒ `det = x′(θ)x′(η)(y(η) − y(θ)) ≠ 0` · `mul_ne_zero`, `sub_ne_zero` · 100 · true (probe (v)).
- **P4.2 `finite_double_of_stage2` (460)** — finitely many double points in one period square · pairs with `circDist < δc` are excluded by the collar; the rest lie in the compact `K2 δc`; the map `G(θ,η) = front θ − front η : ℝ² → ℝ²` has invertible derivative at a transverse double point (`det ≠ 0`) ⇒ locally injective (`HasStrictFDerivAt.toOpenPartialHomeomorph`) ⇒ zeros isolated ⇒ `IsCompact.finite` with `IsDiscrete`; project to `Ico × Ico` · 250 · true.

### P5 (sm-3:2731-2768)
- **P5.1 `hamFlow_of_y_only` (481)** — `hamFlow (ψ ∘ y) = cuspFlowMap ψ` · `hamVF (ψ∘y) = (−ψ′(y), 0, ψ(y) − yψ′(y))` (`pd` computations); `cuspFlowMap ψ` is a global flow (`y` constant, `x, z` affine in `s`: `HasDerivAt` trivial); **`H = ψ(y)` is NOT compactly supported on `ℝ³`**, so `ContactMotionsHyp` does not apply — but `X_H` is bounded with bounded derivative (ψ compactly supported) hence globally Lipschitz (`lipschitzWith_of_nnnorm_fderiv_le`); then `IsGlobalFlow.unique` and `Classical.epsilon_spec` identify `globalFlow` with the explicit flow · 150 · true (probe (ii)).
- **P5.2 `exists_local_graph` (487)** — near a cusp `x = f(y)` with `f′(y₀) = 0`, `f″(y₀) ≠ 0`, `f` globally `C^∞` · `y′(θc) ≠ 0` (P1.4) ⇒ 1-D IFT `HasStrictDerivAt.toOpenPartialHomeomorph` / `ContDiffAt.localInverse` gives a smooth local inverse `θ(y)`; `f₀ := x ∘ θ(·)` smooth near `y₀`; extend to a global smooth `f` by a bump inside the chart ball (`ContDiffBump`, `f := b·f₀ + (1−b)·x₀` with `if` outside); `f′(y₀) = x′(θc)/y′(θc) = 0`; `f″(y₀) = x″(θc)/y′(θc)²` (chain rule twice with `x′(θc) = 0`), nonzero by `NoDoubleZero` · 250 · true.
- **P5.3 `exactGerm_of_cuspFlow` (495)** — the exact germ · `A := f″(y₀)/2 ≠ 0`; `y`-coordinate unchanged by `cuspFlowMap` so `y′(θc) ≠ 0` persists; `x_new = f(y) − ψ′(y) = f − (f − q) = q(y) = x₀ + Au²` (`intervalIntegral.deriv_integral_right`/FTC for `ψ′`); `z_new`: compare derivatives near `θc`: `z_new′ = y y′(f′ − ψ″) = y y′ q′ = 2Auy y′` and `(z₀ + Ay₀u² + ⅔Au³)′ = 2Au y′(y₀ + u)`, equal, values equal at `θc` ⇒ equal on a neighbourhood (`is_const_of_deriv_eq_zero` on an interval / `Filter.Eventually` + `HasDerivAt` uniqueness) · 250 · true (probe (iii)).
- **P5.4 `exists_small_cusp_hamiltonian` (507)** — `C²`-small cut-off Hamiltonian · Taylor (`taylor_mean_remainder_lagrange` or `ContDiff` + MVT thrice) gives `|ψ^{(j)}(y)| ≤ C|u|^{4−j}` for `j ≤ 3` on `|u| ≤ 1` (from `f′(y₀) = 0`, `f″(y₀) = 2A`: `f − q = O(u³)`); `H = ψ(y)·b_ε(p − p_c)` with `b_ε` a scaled bump (`ContDiffBump` with `rIn = ε/2`, `rOut = ε`; derivative bounds `‖D^k b_ε‖ ≤ C_k ε^{−k}` — Mathlib has no scaled-bump derivative API: build `b_ε(p) = b_1((p − p_c)/ε)` and use `iteratedFDeriv` of a composition with a linear map `ContinuousLinearMap.iteratedFDeriv_comp_right`); Leibniz `norm_iteratedFDeriv_mul_le` ⇒ `‖D^k H‖ ≤ Cε^{4−k}`, `k ≤ 3`, on the support (`|y − y₀| ≤ ε`); `hamVF` involves `H` and its first derivatives times `y` (bounded) ⇒ `‖D^k X_H‖ ≤ Cε` for `k ≤ 2`; choose `ε ≤ min ε₀ (η/C)` · 400 · true after the correction (see §0).
- **P5.5 `flow_C2_close` (518)** — `‖D^k(φ₁ − id)‖ ≤ C₀η` for `k ≤ 2` when `‖D^k X‖ ≤ η ≤ 1` · `k = 0`: `‖φ_t p − p‖ ≤ ∫₀ᵗ‖X‖ ≤ η`; `k = 1`: `J_t = Dφ_t(p)` solves `J′ = DX(φ)J` (`ContactMotions.hasDerivAt_fderiv_flow` pattern for a general compactly supported field, via `contDiff_uncurry`), so `(J − I)′ = DX(φ)(J − I) + DX(φ)`, Grönwall (`norm_le_gronwallBound_of_norm_deriv_right_le`, `δ = 0, K = η, ε = η`) ⇒ `‖J₁ − I‖ ≤ e^η − 1 ≤ 2η`; `k = 2`: `M_t = D²φ_t(p)` solves `M′ = DX(φ)M + D²X(φ)[J,J]` (one more `isSymmSndFDerivAt` step), `‖M₁‖ ≤ η(1+2η)²e^η ≤ 27η`; `C₀ = 30` · 400 · true.
- **P5.6 `stage3_stable` (527)** — `Stage3` and the cusp set persist under `C²`-small bijective `Ψ` supported near the cusps with `x′_new(θc) = 0` · curve-level `C²`-closeness: `(Ψ∘L)′ = DΨ(L)L′`, `(Ψ∘L)″ = D²Ψ(L)[L′,L′] + DΨ(L)L″` ⇒ `‖(Ψ∘L)^{(k)} − L^{(k)}‖ ≤ Cη` uniformly; then: regular intervals keep `x′ ≠ 0`; critical intervals keep the `x″`, `y′` signs and endpoint signs of `x′` ⇒ exactly one zero of `x′_new`, which is `θc` by hypothesis ⇒ `cuspSet` unchanged; collar persists (P2.2 argument); `NoCuspOnBranch`, `NoTriple`, transverse double points: the old bad-configuration maps `C, R` have positive minima on `K2, K3` (compact, nonvanishing) and the front is `C⁰`-close, `x′` is `C⁰`-close ⇒ still nonvanishing; transversality: `det` is `C⁰`-close to the old positive-minimum `det` on the compact set of near-double pairs (or re-derive by P4.1 from the persisted properties); finiteness by P4.2; embeddedness: `Ψ` bijective; Legendrian: from the contact hypothesis on `Ψ` (added in review; without it the leaf is false) · 450 · true as now stated.
- **P5.7 `exists_germ_isotopy` (541)** — the cusp-normalising contact isotopy · finitely many cusps `θ₁,…,θ_N` (P1.3) with `y′ ≠ 0` (P1.4); local graphs `f_j` (P5.2); `η, rc` from P5.6 (with the contact hypothesis, P5.7's `Φ 1` is contact); `ε₀ := rc/2` and `η/(N·C₀)` in P5.4 for each `j`, disjoint balls (cusp points distinct, `L` embedded); `Φ := hamIsotopy N Hs 1` (P0.1); `Φ 1 − id` is `C²`-small: each factor by P5.5, compositions of `C²`-small maps are `C²`-small (induction; chain rule bounds); `x′_new(θ_j) = 0` and the exact germ at `θ_j`: on the inner ball the Hamiltonian is `ψ_j(y)` and the other flows are the identity there, the inner subarc `|θ − θ_j| < ε/8‖L′‖` stays in the inner ball (displacement `≤ η ≤ ε/8`) so `Φ 1 = cuspFlowMap ψ_j 1` there (uniqueness: the explicit flow of `ψ_j(y)`, P5.1, and the cut-off flow agree on trajectories that stay where the cutoff is `1`); P5.3 gives `IsExactCuspGerm`; P5.6 gives `Stage3` and `cuspSet (Φ 1 ∘ L) = cuspSet L` so every cusp of the new curve is one of the `θ_j` · 500 · true.

### P6 (sm-3:2769-2783)
- **P6.1 `isContactIsotopy_concat` (571)** — `concat Φ Ψ` is a contact isotopy · `smooth`: on `s < 1/2` the left branch is `Φ(τ(2s), p)` with `τ = smoothTransition` (`ContDiffOn.comp` with `MapsTo` into `[0,1]`), on `s > 1/2` the right branch; at `s = 1/2` both branches equal `Φ 1 p` on a neighbourhood? — no: for `s < 1/2` close to `1/2`, `τ(2s) < 1`; joint smoothness at the join uses flatness: `τ^{(k)}(1) = 0 = τ^{(k)}(0)` for `k ≥ 1` (`smoothTransition` is constant on `(−∞,0]` and `[1,∞)`, so all derivatives vanish at `0` and `1` by continuity), so all `s`-derivatives of both branches tend to `0` at the join and the pieces glue to a `C^∞` function (`ContDiffOn` on `Icc 0 1 ×ˢ univ` via `contDiffOn_of_locally_contDiffOn`, or prove `C^k` for each `k` with the one-sided derivative criterion) — this gluing lemma is the substantial part; `zero`: `τ(0) = 0`, `Φ 0 = id`; `diffeo`: composition of diffeos; `support`: union of the two compact sets; `contact`: composition, product of the `c`'s · 300 · true.
- **P6.2 `pushoffAnnulus_map` (577)** — `Φ_s ∘ B` is a pushoff annulus of `Φ_s ∘ L` · nine fields: `smooth` (`ContDiffOn.comp` with `MapsTo`), `periodic`, `core` (`B(·,0) = L`), `injective` (`Φ_s` injective), `immersion` (`DΦ_s` injective), `transverse` (`alpha (Φ q)(DΦ x) = c·alpha q x`, `c ≠ 0`), `positive` (`c > 0`) · 120 · true (sm-3:2773-2778).
- **P6.3 `transverselyIsotopic_contact` (584)** — `K ↦ Φ_1 ∘ K` through positive transverse embedded circles · `F s θ := Φ s (K θ)`, jointly smooth (`ContDiffOn` of `uncurry Φ` composed with `(s,θ) ↦ (s, K θ)`), each embedded (P0.2's argument) and positive (`alpha ((Φ_s∘K)′) = c·alpha(K′) > 0`), `F 0 = K` (`Φ 0 = id`), `F 1 = (Φ 1 ∘ K) ∘ id` with `IsCircleReparam id` (`deriv id = 1 > 0`) · 100 · true.
- **P6.4 `IsPushoffAnnulus.circle` (590)** — `B(·, s₀)` is an embedded circle for `s₀ ∈ (−ε, b)` · smooth: `hB.smooth` on the open domain composed with `θ ↦ (θ, s₀)`; periodic: `hB.periodic`; injective: `hB.injective` (same `s₀`); immersion: `deriv = fderiv B (θ,s₀) (1,0) ≠ 0` by `hB.immersion` (`(1,0) ≠ 0`) · 60 · true.

## 3. Leaves needing a hypothesis fix before proving (found in review)
- **P5.4** — fixed in the skeleton (`f′(y₀) = 0`, `f″(y₀) = 2A` added).
- **P5.6** — the conclusion `Stage3 (Ψ ∘ L)` includes `legendrian`, which needs `Ψ` contact; the
  pointwise contact hypothesis `∀ p, ∃ c > 0, ∀ v, alpha (Ψ p) (DΨ_p v) = c · alpha p v` has been
  ADDED in the skeleton (the intended `Ψ = Φ₃ 1` is contact by P0.1, so P5.7 can still use it).
All other leaves were checked (numerically where numeric, §0; by argument otherwise) and are
believed true as stated.

## 4. Assembly (proved in the skeleton)
`step1` (P0.1, P0.2, P1.1, P1.2 + `exists_param_avoiding` with `ι = Unit`) → `step2` (P2.1, P2.2,
P3.2–P3.4, monotonicity of `ParameterAvoidanceHyp` in the radius, two-set avoidance by
`interior_union_isClosed_of_interior_empty` + `Dense.exists_mem_open`) → `step3` (P4.1, P4.2) →
`exists_germ_isotopy` (P5.7) → `isGenericFront_of_stage3` (P1.3) → `concat`/`concat_one`, P6.1–P6.4
→ `fd_generic_front`.
