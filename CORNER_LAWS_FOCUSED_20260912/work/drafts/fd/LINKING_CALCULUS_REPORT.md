# Row 88 fd:linking-calculus — report

Date: 2026-09-14.  Row 88 of tools/claims.py, lemma `fd:linking-calculus` ("Linking calculus and
uniform transverse framing"), reference/SM/sm-3-statesum.tex:2785-2826 (statement), 2827-3010
(proof).  Last row of the fd block 84-88 (sibling row 85 fd:parameter-avoidance, drafted 2026-09-14
in `work/drafts/fd/ParameterAvoidance.lean`).  Pure analysis; Mathlib only; no dependency on the
project's diagram layer.

| item | value |
|---|---|
| file | `work/drafts/fd/LinkingCalculus.lean` (2075 lines) |
| main declaration | `SM.fd_linking_calculus : SM.LinkingCalculusData` |
| bundle | `SM.LinkingCalculusData` (9 fields, one per printed clause of the conclusion; the commentary sentence 2805-2806 has no field) |
| hypothesis structures | `IsSmoothCircle`, `DisjointPair`, `DisjointPairFamily`, `GenericDirection`, `FramedFamily`, `TransverseFamily`, `IsPositiveTransverseEmbedding` (one field per printed hypothesis clause) |
| isolated hypothesis | `SM.RegularPoleCount : Prop` (fd:regular-pole-count, sm-3:2894-2897), used only by the field `crossing_formula`, which is stated as `RegularPoleCount → …` |
| check | `cd work/lean && lake env lean ../drafts/fd/LinkingCalculus.lean` — 0 errors, 0 warnings, about 9-11 s |
| axioms | `#print axioms SM.fd_linking_calculus` on a /tmp copy: `[propext, Classical.choice, Quot.sound]` |
| placeholders | none; every declaration is proved; no placeholder axiom, no `native_decide`, no new axiom (201 top-level declarations) |
| intended home | `work/lean/SM/LinkingCalculus.lean` (imports Mathlib only; add the port header at porting time) |

## 1. Clause → field map

Notation: `E3 = EuclideanSpace ℝ (Fin 3)` (oriented `ℝ³`, coordinates `p 0, p 1, p 2 = x, y, z`),
`cross a b` the cross product, `⟪a, cross b c⟫ = det ![a, b, c]` (`inner_cross_eq_det`).  Circles
are `P`-periodic maps `ℝ → E3` (`S¹ = ℝ/Pℤ`, `P > 0`; FR-LC-1).

### The pairing (sm-3:2787-2793)

| tex | printed | Lean |
|---|---|---|
| 2787-2788 | "two disjoint smooth oriented parametrized circles `C₁, C₂` in oriented `ℝ³`" | `DisjointPair P C₁ C₂` = `pos : 0 < P`, `circle₁ circle₂ : IsSmoothCircle P Cᵢ` (`ContDiff ℝ ∞ Cᵢ`, `Periodic Cᵢ P`), `disjoint : ∀ u v, C₂ v ≠ C₁ u` |
| 2792 | `G(u,v) = (C₂(v) − C₁(u))/|C₂(v) − C₁(u)|` | `gaussMap C₁ C₂ u v = ‖C₂ v − C₁ u‖⁻¹ • (C₂ v − C₁ u)` |
| 2791 | `G_u`, `G_v` | `pderivU G u v = deriv (fun u' => G u' v) u`, `pderivV G u v = deriv (fun v' => G u v') v` (FR-LC-2) |
| 2791 | `G·(G_u × G_v)` | `gaussDensity G u v = ⟪G u v, cross (pderivU G u v) (pderivV G u v)⟫` |
| 2790-2791 | `ℓ(C₁,C₂) = (1/4π) ∫_{S¹×S¹} G·(G_u × G_v) du dv` | `linking P C₁ C₂ = gaussIntegral P (gaussMap C₁ C₂)`, `gaussIntegral P G = (1/(4π)) * ∫ u in 0..P, ∫ v in 0..P, gaussDensity G u v` |

### The conclusion: `LinkingCalculusData : Prop`

| tex | printed clause | field | status |
|---|---|---|---|
| 2794 | "It is symmetric" | `symm : ∀ P C₁ C₂, DisjointPair P C₁ C₂ → linking P C₁ C₂ = linking P C₂ C₁` | proved |
| 2794-2795 | "and is constant under smooth families of disjoint oriented pairs" | `family_const : ∀ P C₁ C₂, DisjointPairFamily P C₁ C₂ → ∀ s ∈ Icc 0 1, ∀ s' ∈ Icc 0 1, linking P (C₁ s) (C₂ s) = linking P (C₁ s') (C₂ s')` | proved |
| 2795-2798 | "Call a direction `ν ∈ S²` generic for the pair if at every parameter pair `(u,v)` at which `C₂(v) − C₁(u)` is parallel to `ν` the tangents of the two circles projected along `ν` are linearly independent" | definition `GenericDirection C₁ C₂ ν` (`unit : ‖ν‖ = 1`, `indep : ∀ u v, Parallel (C₂ v − C₁ u) ν → LinearIndependent ℝ ![projAlong ν (deriv C₁ u), projAlong ν (deriv C₂ v)]`) | definition |
| 2798-2799 | "the projection along such a `ν` displays the pair with finitely many transverse mixed crossings" | `finite_crossings : … → GenericDirection C₁ C₂ ν → (mixedCrossings P C₁ C₂ ν).Finite`, `mixedCrossings = {p ∈ [0,P)² | Parallel (C₂ p.2 − C₁ p.1) ν}` (FR-LC-5) | proved |
| 2799-2802 | "Let `ν` point toward the observer and orient the projection plane so that its positive basis followed by `ν` is positive in `ℝ³`; at a mixed crossing the strand nearer the observer is over" | `planeDet ν x y = ⟪ν, cross x y⟫ (= det(x, y, ν))`; in `crossingSign`, the over strand is `C₂` iff `0 < ⟪C₂ v − C₁ u, ν⟫` (FR-LC-4) | convention |
| 2802-2804 | "Then `ℓ(C₁,C₂)` equals one half the sum over the mixed crossings of the overpass-first sign `sgn det(u_o,u_u)` of the projected over and under tangents" | `crossing_formula : RegularPoleCount → … → linking P C₁ C₂ = (1/2) * ∑ᶠ p ∈ mixedCrossings P C₁ C₂ ν, crossingSign C₁ C₂ ν p` | proved from the isolated hypothesis (FR-LC-6) |
| 2805-2806 | "Thus it has exactly the linking normalization used in the source's front calculations." | commentary, no field | — |
| 2808-2810 | "let `C_s`, `0 ≤ s ≤ 1`, be a smooth family of embedded oriented circles and let `v_s` be a smooth vector field along them, everywhere linearly independent of `∂_u C_s`" | `FramedFamily P C v` (`smooth`, `smooth_v` jointly `C^∞`; `periodic`, `periodic_v`; `embedded : ∀ s ∈ Icc 0 1, ∀ u u', C s u = C s u' → ∃ k : ℤ, u' = u + k * P`; `indep : ∀ s ∈ Icc 0 1, ∀ u, LinearIndependent ℝ ![deriv (C s) u, v s u]`) (FR-LC-3, FR-LC-7) | hypothesis |
| 2810-2812 | "One common sufficiently small positive `ε` gives disjoint framed pairs `(C_s, C_s + εv_s)` throughout the family." | `framing_uniform : … → ∃ ε₀ > 0, ∀ s ∈ Icc 0 1, ∀ ε, 0 < ε → ε ≤ ε₀ → DisjointPair P (C s) (pushoff (C s) (v s) ε)` | proved |
| 2812-2813 | "Their pairing is independent of that radius and of `s`." | `framing_invariant`: for every `ε₀ > 0` such that the pairs are disjoint for `s ∈ [0,1]`, `ε ∈ (0,ε₀]`: `linking P (C s) (pushoff (C s) (v s) ε) = linking P (C s') (pushoff (C s') (v s') ε')` (FR-LC-8) | proved |
| 2813-2814 | "This includes a homotopy of normal framings on a fixed curve." | `framing_homotopy`: the previous field for `FramedFamily P (fun _ => C) v` | proved |
| 2816-2820 | "If `T_s : S¹ → ℝ³`, `0 ≤ s ≤ 1`, is a smooth family of embeddings with `(dz − y dx)(∂_u T_s) > 0`, there is one `ε₀ > 0` such that `T_s` and `T_s + ε∂_y` are disjoint positive transverse embeddings for every `s` and `0 < ε ≤ ε₀`" | `TransverseFamily P T` (`positive : ∀ s ∈ Icc 0 1, ∀ u, 0 < contactForm (T s u) (deriv (T s) u)`, `contactForm p w = w 2 − p 1 * w 0`); `transverse_uniform : … → ∃ ε₀ > 0, ∀ s ∈ Icc 0 1, ∀ ε, 0 < ε → ε ≤ ε₀ → IsPositiveTransverseEmbedding P (T s) ∧ IsPositiveTransverseEmbedding P (pushoff (T s) (fun _ => ey) ε) ∧ DisjointPair P (T s) (pushoff (T s) (fun _ => ey) ε)` | proved |
| 2820-2824 | "The number `sl(T_s) = ℓ(T_s, T_s + ε∂_y)` is independent of such `ε` and of `s`." | `selfLinking P T ε = linking P T (pushoff T (fun _ => ey) ε)`; `self_linking_invariant`: for every `ε₀ > 0` with the disjointness property, `selfLinking P (T s) ε = selfLinking P (T s') ε'` | proved |

Row theorem: `SM.fd_linking_calculus : LinkingCalculusData`, assembled from
`DisjointPair.linking_comm`, `DisjointPairFamily.linking_eq`, `DisjointPair.finite_mixedCrossings`,
`crossing_formula_of_regularPoleCount`, `FramedFamily.exists_uniform_disjointPair`,
`FramedFamily.linking_pushoff_eq`, `TransverseFamily.exists_uniform`, `TransverseFamily.selfLinking_eq`.

## 2. The isolated hypothesis `RegularPoleCount` (fd:regular-pole-count, sm-3:2894-2897)

```
def RegularPoleCount : Prop :=
  ∀ (P : ℝ) (G : ℝ → ℝ → E3) (N : E3), 0 < P → ContDiff ℝ ∞ (uncurry G) →
    (∀ v, Periodic (fun u => G u v) P) → (∀ u, Periodic (G u) P) → (∀ u v, ‖G u v‖ = 1) →
    ‖N‖ = 1 → (∀ u v, G u v = N → gaussDensity G u v ≠ 0) →
    ∀ hfin : {p : ℝ × ℝ | p ∈ Ico 0 P ×ˢ Ico 0 P ∧ G p.1 p.2 = N}.Finite,
      gaussIntegral P G = ∑ p ∈ hfin.toFinset, Real.sign (gaussDensity G p.1 p.2)
```
This is the printed formula `∫_{S¹×S¹} G^*ω = ∑_{p ∈ G⁻¹(N)} σ(p)` for a regular value `N` of a smooth
doubly periodic `G : S¹×S¹ → S²`, with `ω` the outward area form of `S²` divided by `4π`
(`G^*ω = (1/4π) G·(G_u × G_v) du dv`) and `σ(p) = sgn (G·(G_u × G_v))(p)` the local orientation
sign (the sign of the Jacobian of `G` at `p` for the outward orientation of `S²` at `N = G(p)`).
"Regular value" is rendered as `G·(G_u × G_v) ≠ 0` at every preimage (for a map into `S²`, `G_u, G_v`
span the tangent plane at `N` iff `G_u × G_v ≠ 0` iff, `G_u × G_v` being parallel to `N`,
`⟪N, G_u × G_v⟫ ≠ 0`).  The finiteness of the preimage in one fundamental domain is taken as an
explicit hypothesis so that the sum is a finite sum (it is proved for the Gauss map of a generic
pair in `DisjointPair.finite_mixedCrossings`, of which the two preimages are subsets).

Its printed proof (sm-3:2869-2916) is the Stokes-type argument with the primitive
`λ_N = −(X dY − Y dX)/(4π(1 − Z))` of `ω` on `S² ∖ {N}`, Green's formula on the torus minus small
inverse discs (with a partition of unity), and the limit of the boundary terms.  Mathlib has the
divergence theorem on boxes only (`MeasureTheory.integral_divergence_of_hasFDerivWithinAt_off_countable`),
no Stokes theorem on a manifold with boundary, no degree theory; a formalisation of this statement
was judged far beyond the row's budget and is the single open item of the row.  Everything else the
crossing clause needs (finiteness of the preimages, the derivative of the Gauss map at a crossing,
the identification of the local orientation sign with the overpass-first sign at both poles, the
sum over the two poles) is proved in `LinkingCalculus.Crossing`.

## 3. The route (all proved except as stated in §2)

File layout: §0 algebra of oriented `ℝ³` (`LinkingCalculus.cross`, triple product, BAC-CAB, Lagrange
identity, projections); §1 definitions, hypothesis structures, `RegularPoleCount`, the bundle, and
the shared analytic helpers (`contDiff_gaussMap`, `pderivU_eq_fderiv`, `contDiff_gaussDensity`,
`integral_integral_swap_of_continuous`, `continuous_parametric_integral`); §2 symmetry; §3 packaging;
§4 interpolation; §5 transverse family; §6 constancy (`LinkingCalculus.Family`); §7 framing radius
(`LinkingCalculus.Framing`); §8 crossings (`LinkingCalculus.Crossing`); §9 the row.

### §0-1 Algebra and shared helpers

| declaration | content | Mathlib used |
|---|---|---|
| `cross`, `cross_apply0/1/2`, `cross_comm_neg`, `cross_add_*`, `cross_smul_*`, `cross_neg_*`, `cross_sub_*`, `cross_self`, `cross_zero_*` | the cross product on `E3` (transport of `crossProduct`), coordinate identities | `crossProduct`, `cross_apply`, `fin_cases`/`ring` |
| `inner_cross_eq_det`, `inner_cross_expand`, `inner_cross_cyclic`, `inner_cross_swap`, `inner_cross_self_left/right` | triple product = determinant, cyclicity, antisymmetry | `triple_product_eq_det`, `PiLp.inner_apply` |
| `cross_cross_eq` (BAC-CAB), `norm_cross_sq` (Lagrange), `norm_cross_le` | `a × (b × c) = ⟪a,c⟫b − ⟪a,b⟫c`, `|a × b|² = |a|²|b|² − ⟪a,b⟫²` | `real_inner_self_eq_norm_sq`, `pow_le_pow_iff_left₀` |
| `inner_cross_eq_zero_of_orth` | three vectors orthogonal to `g ≠ 0` have zero triple product (sm-3:2849-2851) | `Matrix.exists_mulVec_eq_zero_iff` |
| `cross_ne_zero_of_linearIndependent` | independent pair ⇒ nonzero cross product | `LinearIndependent.pair_iff`, `LinearIndependent.ne_zero` |
| `crossₗ`, `crossL`, `contDiff_cross`, `ContDiff.cross`, `HasFDerivAt.cross` | the cross product as a continuous bilinear map, its calculus | `LinearMap.mk₂`, `LinearMap.toContinuousLinearMap`, `IsBoundedBilinearMap.contDiff`, `HasFDerivAt.clm_apply` |
| `projAlong`, `Parallel`, `inner_projAlong`, `parallel_iff_projAlong_eq_zero`, `projAlong_add/smul/neg`, `inner_cross_projAlong` | projection along `ν`, `det(Pa, Pb, ν) = det(a, b, ν)` | `inner_sub_left`, `inner_smul_left` |
| `gaussMap_swap`, `norm_gaussMap`, `gaussMap_ne_zero`, `contDiff_gaussMap` | `G̃ = −G`, `|G| = 1`, smoothness of the Gauss map (sm-3:2828-2829) | `ContDiff.norm`, `ContDiff.inv`, `ContDiff.smul` |
| `hasDerivAt_sliceU/V`, `pderivU_eq_fderiv`, `pderivV_eq_fderiv` | slice derivatives are Fréchet partials (FR-LC-2) | `HasFDerivAt.comp_hasDerivAt`, `HasDerivAt.prodMk` |
| `gaussDensity_eq_of_contDiff`, `contDiff_gaussDensity`, `continuous_gaussDensity` | the density is smooth for a smooth `G` | `ContDiff.fderiv_right`, `ContDiff.clm_apply`, `ContDiff.inner` |
| `integral_integral_swap_of_continuous`, `continuous_parametric_integral` | Fubini on a rectangle, continuity of a parametric integral (sm-3:2830-2832) | `MeasureTheory.integral_integral_swap`, `Measure.prod_restrict`, `ContinuousOn.integrableOn_compact`, `intervalIntegral.integral_of_le`, `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` |

### §2 Symmetry (sm-3:2794; proof 2838-2841)

| step (tex) | declaration | Mathlib used |
|---|---|---|
| 2838-2840 "Exchanging the two curves negates both the difference vector and the cross product, leaving this scalar unchanged" | `gaussDensity_swap : gaussDensity (gaussMap C₂ C₁) v u = gaussDensity (gaussMap C₁ C₂) u v` | `deriv.neg`, `inner_neg_left`, `cross_neg_left/right`, `inner_cross_swap` |
| 2840 "after exchanging the integration variables" | `DisjointPair.linking_comm` | `integral_integral_swap_of_continuous`, `continuous_gaussDensity` |

The printed equivalent integrand fd:gauss-integrand (2833-2836) is not needed for symmetry and is not
proved separately; §8 proves the pointwise formula `G·(G_u × G_v) = |D|⁻² ⟪G, (−C₁') × C₂'⟫`
(`Crossing.gaussDensity_gaussMap`), which is fd:gauss-integrand up to `G = D/|D|`.

### §6 Constancy under smooth families (sm-3:2794-2795; proof 2843-2867), namespace `LinkingCalculus.Family`

| step (tex) | declaration | Mathlib used |
|---|---|---|
| 2843-2848 `A = G·(G_u×G_v)`, `B = G·(G_s×G_v)`, `C = G·(G_u×G_s)` | `triple G a b x := ⟪G x, cross (fderiv ℝ G x a) (fderiv ℝ G x b)⟫` (abstract, any normed domain), `contDiff_triple`, `contDiff_fderiv_apply` | `ContDiff.fderiv_right`, `ContDiff.clm_apply`, `ContDiff.inner` |
| 2852-2854 product rule for the triple product | `hasFDerivAt_fderiv_apply`, `fderiv_triple_apply` (`∂_c⟪G, G'a × G'b⟫ = ⟪G'c, G'a×G'b⟫ + ⟪G, G''ca × G'b⟫ + ⟪G, G'a × G''cb⟫`) | `HasFDerivAt.inner`, `fderivInnerCLM_apply`, `HasFDerivAt.clm_apply`, `HasFDerivAt.cross`, `HasFDerivAt.fderiv` |
| 2849-2851 "all lie in the plane orthogonal to `G`; every scalar triple product vanishes" | `inner_fderiv_eq_zero` (`|G| ≡ 1 ⇒ ⟪G, G'a⟫ = 0`), `inner_cross_eq_zero_of_orth` | `HasFDerivAt.unique`, `hasFDerivAt_const`, `real_inner_self_eq_norm_sq` |
| 2855-2862 "the two terms containing `G_{uv}` cancel …; the remaining terms match by equality of mixed derivatives" (fd:gauss-divergence) | `fderiv_fderiv_symm`, `fderiv_triple_div` (`∂_c A_{ab} = ∂_a A_{cb} + ∂_b A_{ac}` for arbitrary directions) | `ContDiffAt.isSymmSndFDerivAt`, `minSmoothness_of_isRCLikeNormedField`, `cross_comm_neg` |
| periodicity of `G`, `A`, `B`, `C` and derivatives | `fderiv_periodic`, `periodic_fderiv_apply`, `periodic_triple` | `fderiv_comp_add_right` |
| slices on `ℝ × ℝ × ℝ` | `eu ev es`, `hasDerivAt_slice1/2/3`, `continuous_slice1/2/3`, `continuous_intS`, `continuous_intS_slice2`, `continuous_intVS` | `HasFDerivAt.comp_hasDerivAt`, `HasDerivAt.prodMk`, `continuous_parametric_integral` |
| FTC along coordinate lines | `ftc_slice1/2/3` | `intervalIntegral.integral_eq_sub_of_hasDerivAt`, `Continuous.intervalIntegrable` |
| 2863-2865 "Integrating a full period in `u` kills `∂_u B` …; in `v` kills `∂_v C`" | `integral_fderiv1_eq_zero`, `integral_fderiv2_eq_zero` | `integral_integral_swap_of_continuous` (twice for the `B` term, once for `C`), periodicity |
| 2866-2867 "the derivative of fd:gauss-linking is zero" | `integral_triple_eq` (`∫∫ A(·,·,s') = ∫∫ A(·,·,s)` for `s ≤ s'`, via `A(s') − A(s) = ∫_s^{s'} ∂_s A = ∫_s^{s'} (∂_u B + ∂_v C)`) | `intervalIntegral.integral_sub/add/congr` |
| the family Gauss map | `gaussFam`, `contDiff_gaussFam`, `norm_gaussFam`, `gaussFam_periodic_u/v`, `gaussDensity_eq_triple` (the printed integrand is `A`) | `contDiff_gaussMap`-style composition, `HasDerivAt.deriv` |
| exports | `linking_const_of_family_global` (family over all of `ℝ`, `le_total` for the order of `s, s'`); `DisjointPairFamily.linking_eq` (the `[0,1]`-family, reparametrised by `σ t = s + (s' − s)·smoothTransition t`) | `Real.smoothTransition.{contDiff, zero_of_nonpos, one_of_one_le, nonneg, le_one}` |

Differentiation under the integral sign is avoided: the pointwise FTC in `s` followed by Fubini for
the (globally continuous) integrands gives the same result with fewer hypotheses.

### §8 (i) Finiteness of the mixed crossings (sm-3:2798-2799; proof 2881-2883), namespace `LinkingCalculus.Crossing`

| step | declaration | Mathlib used |
|---|---|---|
| `Φ(u,v) = P_ν(C₂(v) − C₁(u))`, zeros = crossings | `projAlongL` (the projection as a CLM), `defect`, `parallel_iff_projAlong_eq_zero` | `innerSL`, `ContinuousLinearMap.smulRight` |
| `dΦ(a,b) = b P_ν C₂' − a P_ν C₁'` | `defectDeriv`, `defectDeriv_apply`, `hasFDerivAt_defect` | `HasDerivAt.hasFDerivAt`, `HasFDerivAt.comp`, `hasFDerivAt_fst/snd` |
| "the inverse function theorem makes it discrete" | `defectDeriv_ker_eq_bot` (genericity ⇒ injective derivative), `eventually_defect_ne` (isolated zeros) | `LinearIndependent.pair_iff`, `LinearMap.ker_eq_bot'`, `LinearMap.exists_antilipschitzWith`, `HasFDerivAt.eventually_ne` |
| "it is closed in a compact torus" | `finite_defect_zeros`, export `DisjointPair.finite_mixedCrossings` | `isClosed_singleton.preimage`, `IsCompact.inter_left`, `isDiscrete_iff_nhdsNE`, `Filter.inf_principal_eq_bot`, `IsCompact.finite`, `Set.Finite.subset` |

### §8 (ii) The crossing formula (sm-3:2802-2804; proof 2917-2941), from `RegularPoleCount`

| step (tex) | declaration | Mathlib used |
|---|---|---|
| derivative of `D/|D|` | `hasDerivAt_normalize` (`(f/‖f‖)' = ‖f‖⁻¹ • projAlong (f/‖f‖) f'`) | `HasDerivAt.norm_sq`, `HasDerivAt.sqrt`, `HasDerivAt.inv`, `HasDerivAt.smul`, `Real.sqrt_sq` |
| 2921-2922 "Up to a positive common factor the projected derivatives of `G` are `−C₁', C₂'`" | `hasDerivAt_chord_left/right`, `pderivU_gaussMap`, `pderivV_gaussMap`, `gaussDensity_gaussMap` (`G·(G_u×G_v) = |D|⁻² ⟪G, (−C₁') × C₂'⟫`) | `HasDerivAt.congr_deriv`, `match_scalars`, `field_simp` |
| both poles are regular values (2920-2921 "the projected tangents are independent, so both poles are regular values") | `eq_smul_of_cross_eq_zero`, `cross_eq_smul_of_orth` (for `x, y ⊥ ν`: `x × y = ⟪ν, x × y⟫ ν`), `inner_cross_ne_zero_of_linearIndependent`, `gaussDensity_gaussMap_ne_zero` | `cross_cross_eq`, `cross_ne_zero_of_linearIndependent`, `inner_cross_projAlong` |
| `G = ±ν ⇔ D ∥ ν` | `norm_smul_gaussMap`, `parallel_of_gaussMap_eq`, `gaussMap_eq_or_eq_neg` | `norm_smul`, `abs_of_pos/neg` |
| 2923-2935 the sign at `G = ν` is `det_ν(C₂', C₁')` (second component over), at `G = −ν` it is `det_ν(C₁', C₂')` (first component over) — "again the overpass-first sign" | `sign_mul_of_pos`, `sign_gaussDensity_eq_crossingSign` | `Real.sign_of_pos/neg`, `ite_eq_left/right` |
| 2935-2938 "Formula fd:regular-pole-count at each pole says that each of these two signed crossing sums equals `ℓ`. Adding them and dividing by two" | export `crossing_formula_of_regularPoleCount` (`hreg` at `N = ν`, `N = −ν`; the preimages are disjoint subsets of `mixedCrossings` with union `mixedCrossings`) | `finsum_mem_eq_finite_toFinset_sum`, `Finset.sum_union`, `Finset.disjoint_left`, `Set.Finite.mem_toFinset`, `linarith` |

### §7 The framing radius (sm-3:2810-2812; printed proof 2942-2965), namespace `LinkingCalculus.Framing`

The printed proof builds the four-dimensional normal chart `F(s,u,r,t) = (s, C_s(u) + r v_s(u) + t n_s(u))`
and proves a uniform injectivity radius by the inverse function theorem and a compactness argument
on colliding sequences.  The Lean proof reaches the printed conclusion (a common `ε₀` with
`C_s + εv_s` disjoint from `C_s`) by a direct estimate (FR-LC-8):

| step | declaration | Mathlib used |
|---|---|---|
| joint continuity of `∂_u C_s`, `∂²_u C_s`, periodicity of `∂_u C_s` | `deriv_sliceV_eq`, `contDiff_deriv_sliceV`, `continuous_deriv_sliceV`, `tangent_eq`, `continuous_tangent`, `continuous_deriv2`, `periodic_deriv`, `exists_int_sub_mem_Ico` | `ContDiff.fderiv_right`, `ContDiff.clm_apply`, `deriv_comp_add_const`, `Int.sub_floor_div_mul_nonneg/lt` |
| Taylor remainder `‖C_s(u') − C_s(u) − (u'−u)C_s'(u)‖ ≤ K (u'−u)²` from `‖∂²_u C_s‖ ≤ K` | `taylor_bound` | `Convex.norm_image_sub_le_of_norm_deriv_le` (twice), `HasDerivAt.smul_const`, `HasDerivAt.sub` |
| uniform constants `c ≤ ‖∂_u C_s × v_s‖`, `‖v_s‖ ≤ V`, `‖∂²_u C_s‖ ≤ K` on `[0,1] × ℝ` | `exists_cross_lower_bound`, `exists_v_bound`, `exists_deriv2_bound` | `IsCompact.exists_isMinOn`, `IsCompact.exists_bound_of_continuousOn`, `isCompact_Icc.prod`, `Function.Periodic.sub_int_mul_eq` |
| local step: a collision `C_s(u) + εv_s(u) = C_s(u')` with `|u' − u| ≤ η`, `ηKV < c`, is impossible for every `ε > 0` (cross the relation `εv = δT + R` with `v`) | `local_contra` | `norm_cross_le`, `cross_smul_right`, `cross_self`, `cross_comm_neg` |
| global step: `m > 0` bounds `‖C_s(u+d) − C_s(u)‖` below for `d ∈ [η, P − η]` (embeddedness) | `not_int_mul_of_mem_Ioo`, `exists_global_min` | `IsCompact.exists_isMinOn` on `Icc 0 1 ×ˢ Icc 0 P ×ˢ Icc η (P−η)` |
| assembly: `η = min (P/4) (c/(2KV))`, `ε₀ = m/(2V)`, reduction of `(u,u')` mod `P`, three cases | `exists_reduce_pair`, `exists_uniform_pushoff_aux`, export `FramedFamily.exists_uniform_pushoff` | `Function.Periodic.sub_eq`, `le_or_gt` |

### §3-5, §9 Packaging, interpolation, the transverse family, the row

| step (tex) | declaration | Mathlib used |
|---|---|---|
| "disjoint framed pairs" as `DisjointPair` | `contDiff_slice`, `contDiff_pushoff`, `periodic_pushoff`, `FramedFamily.isSmoothCircle(_pushoff)`, `FramedFamily.disjointPair_pushoff`, `FramedFamily.exists_uniform_disjointPair` | `ContDiff.comp`, `ContDiff.const_smul` |
| 2968-2970 "Interpolating between two positive radii stays in the same disc. The already proved paired invariance therefore gives both family and radius independence." | `Interp.interp`, `Interp.interp_zero/one`, `Interp.interp_mem_Icc/Ioc`, `FramedFamily.linking_pushoff_eq_of_global`, `FramedFamily.linking_pushoff_eq` (path `t ↦ (interp s s' t, interp ε ε' t)` and `linking_const_of_family_global`) | `Real.smoothTransition.*` |
| 2986-2988 independence of `∂_u T_s` and `∂_y` by applying `dz − y dx` | `contactForm_add_smul`, `contactForm_ey`, `ey_ne_zero`, `TransverseFamily.framedFamily` | `LinearIndependent.pair_iff`, `PiLp.single_apply` |
| 2989-2998 `a₀ = min(z' − yx') > 0`, `M ≥ |x'|`, `ε₀ M < a₀/2`, fd:pushoff-positive-clearance | `contactForm_pushoff` (`α_{T+ε∂_y}(w) = α_T(w) − ε w_x`), `deriv_pushoff_const`, `deriv_slice_eq`, `continuous_fderiv_slice`, `TransverseFamily.exists_uniform_positive` | `IsCompact.exists_isMinOn`, `IsCompact.exists_bound_of_continuousOn`, `deriv_add_const`, `fun_prop` |
| 2817-2820 the uniform `ε₀` (disjointness from §7, positivity from the previous line) | `TransverseFamily.isPositiveTransverseEmbedding(_pushoff)`, `TransverseFamily.exists_uniform_of`, `TransverseFamily.exists_uniform` | — |
| 2820-2824 `sl(T_s)` independent of `ε` and `s` | `TransverseFamily.selfLinking_eq` (the framed family `(T, ∂_y)` and `FramedFamily.linking_pushoff_eq`) | — |
| the row | `fd_linking_calculus : LinkingCalculusData` | — |

## 4. Readings and fidelity risks

* **FR-LC-1 (period convention).**  Printed: `S¹ × S¹` with `du dv`, no period given; the consumer
  fd:transverse-neighborhood (sm-3:2398) uses `T : ℝ/(2πℤ) → ℝ³`, the direction-loop rows use `ℝ/ℤ`.
  Lean: `S¹ = ℝ/Pℤ` with `P > 0` a parameter of every definition and hypothesis structure; the
  integral is over `[0,P]²`.  Both circles share the period (one parametrised circle `S¹`).  The
  value of `ℓ` is independent of the parametrisation (the integrand is the pullback of a 2-form),
  but this reparametrisation invariance is not printed and not proved here; a consumer working with
  `2π`-periodic curves instantiates `P = 2π`.
* **FR-LC-2 (partial derivatives).**  `G_u`, `G_v` are the derivatives of the one-variable slices
  (`deriv`); for the smooth Gauss map they equal the Fréchet partial derivatives
  (`pderivU_eq_fderiv`, `pderivV_eq_fderiv`), which is how the family computation uses them.
* **FR-LC-3 (smooth families on `[0,1]`).**  A "smooth family `C_s`, `0 ≤ s ≤ 1`" is rendered as the
  restriction to `s ∈ [0,1]` of a jointly `C^∞` map `ℝ × ℝ → E3`; the hypotheses (disjointness,
  embeddedness, independence, positivity) are imposed only for `s ∈ [0,1]`.  The paper itself uses
  "a smooth local extension in `s`" at the endpoints (sm-3:2953-2954); every smooth family on a
  closed interval extends.  The constancy proof reparametrises the family through
  `Real.smoothTransition` so that the pair is disjoint for every real parameter and no uniform
  neighbourhood argument is needed.
* **FR-LC-4 (orientations and the crossing sign).**  Orientation of a circle = direction of the
  parameter; orientation of `ℝ³` = the standard one (`det ![e₀,e₁,e₂] = 1`, `cross` the usual cross
  product).  "Orient the projection plane so that its positive basis followed by `ν` is positive in
  `ℝ³`": for `x, y ⊥ ν` the plane determinant is `det(x, y, ν) = ⟪ν, x × y⟫ = planeDet ν x y`.  "`ν`
  points toward the observer; the strand nearer the observer is over": at a crossing
  `C₂(v) − C₁(u) = t ν`, `C₂(v)` is nearer iff `t > 0` iff `0 < ⟪C₂ v − C₁ u, ν⟫`.  `Real.sign` takes
  the values `−1, 0, 1` (it is never `0` at a crossing of a generic direction:
  `Crossing.gaussDensity_gaussMap_ne_zero`, `Crossing.sign_gaussDensity_eq_crossingSign`).
* **FR-LC-5 (generic direction, crossings).**  "Parallel to `ν`" is `∃ t, w = t • ν` (both signs;
  the paper's proof confirms: "a crossing between the components is exactly a preimage of `ν` or
  `−ν`", sm-3:2919-2920).  "Projected along `ν`" is the orthogonal projection onto `ν^⊥`,
  `projAlong ν w = w − ⟪w, ν⟫ • ν`.  "Linearly independent" is Mathlib's `LinearIndependent ℝ ![·,·]`.
  "Finitely many transverse mixed crossings": the crossings are counted in one fundamental domain
  `[0,P)²` of the parameter torus (`mixedCrossings`); transversality is the defining independence,
  so the field asserts finiteness.  Crossings of a component with itself are not part of the
  statement (mixed crossings only).
* **FR-LC-6 (the crossing formula).**  The field `crossing_formula` is `RegularPoleCount → …`; see
  §2.  The derivation from `RegularPoleCount` follows the printed proof (sm-3:2917-2941) exactly: at
  `G = ν` the second component is over and the local orientation sign is `sgn det_ν(−C₁', C₂') =
  sgn det_ν(C₂', C₁')`; at `G = −ν` the first component is over and the sign is `sgn det_ν(C₁', C₂')`;
  the two signed counts each equal `ℓ`, and their sum over the disjoint union of the two preimages is
  the sum over the mixed crossings.  The sum is written with `∑ᶠ` (`finsum`) so that the field does
  not depend on the finiteness field; it equals the finite sum by `finsum_mem_eq_finite_toFinset_sum`.
* **FR-LC-7 (embedded circles).**  "Embedded oriented circle" is rendered as injectivity on `ℝ/Pℤ`
  (`C u = C u' → ∃ k : ℤ, u' = u + k * P`); the immersion condition `∂_u C ≠ 0` follows from the
  independence hypothesis (framed family) or from `(dz − y dx)(∂_u T) > 0` (transverse family) and is
  not repeated.  "Positive transverse embedding" (`IsPositiveTransverseEmbedding`) is: smooth,
  `P`-periodic, injective on `ℝ/Pℤ`, `(dz − y dx)(∂_u T) > 0` everywhere, with `dz − y dx` evaluated
  at the point `T(u)` on the vector `∂_u T(u)` (`contactForm p w = w 2 − p 1 * w 0`).
* **FR-LC-8 (the framing clauses).**  "Disjoint framed pairs" is rendered as `DisjointPair` for the
  pair `(C_s, C_s + ε v_s)` (the pushoff is smooth and periodic; its embeddedness is not claimed).
  "Independent of that radius" is proved for every common radius `ε₀ > 0` with the disjointness
  property, not only for the one constructed; this is what the printed proof shows ("Interpolating
  between two positive radii stays in the same disc", sm-3:2968-2969) and slightly strengthens the
  printed sentence.  The proof of the radius clause is not the printed one: the paper builds the
  four-dimensional normal chart `F(s,u,r,t)` (fd:family-normal-chart, sm-3:2942-2965) and proves
  its uniform injectivity; the Lean proof estimates directly (a Taylor remainder bound for `C_s`
  and a compactness minimum away from the diagonal).  The normal-chart injectivity statement itself,
  which the paper reuses later (sm-3:3285, "the argument of the uniform normal chart in the proof of
  Lemma fd:linking-calculus"), is therefore not available from this file; see open items.
* **FR-LC-9 (the transverse clause).**  `∂_y` is `ey = EuclideanSpace.single 1 1`; the pushoff
  `T_s + ε∂_y` is `pushoff (T s) (fun _ => ey) ε`.  The "positive transverse embedding" property of
  `T_s` itself is restated in the conclusion (it is part of the hypotheses).  The constant `a₀/2`
  clearance of fd:pushoff-positive-clearance is not exported; only positivity is claimed.

## 5. Open items

1. `RegularPoleCount` (fd:regular-pole-count) is the only unformalised ingredient; the field
   `crossing_formula` is conditional on it.  A proof needs Stokes/Green on the torus minus finitely
   many discs and the primitive `λ_N` of the area form; none of this is in Mathlib.  Alternative
   routes (a homotopy-invariance/degree argument) need degree theory, also absent.
2. Port to `work/lean/SM/LinkingCalculus.lean` (Mathlib-only imports; the port header per the
   accepted modules' convention).  Consumers: the later fd rows (86-87, generic front, contact),
   which will instantiate `P = 2π`.
3. Reparametrisation invariance of `ℓ` (not printed) would make the period parameter irrelevant for
   consumers; not attempted.
4. The uniform normal-chart injectivity of sm-3:2942-2965 (reused at sm-3:3285 for the ce rows) is
   not proved here (FR-LC-8); the radius clause was proved by a direct estimate instead.
5. Mathlib API notes for the porter: `ContDiff.differentiable`/`ContDiffAt.differentiableAt` take
   `n ≠ 0`; `HasDerivAt.prodMk` (not `.prod`); `ContDiff.smul` is stated with the pointwise `•`
   (use `ContDiff.const_smul` for `fun x => c • f x`); `∞` (scoped `ContDiff`) is `((⊤ : ℕ∞) : WithTop ℕ∞)`,
   distinct from `⊤ = ω`, so `le_top` does not prove `m + 1 ≤ ∞` (use `by simp`);
   `EuclideanSpace.single_apply` is deprecated for `PiLp.single_apply`; `Function.Periodic.deriv` does
   not exist (`periodic_deriv` here, via `deriv_comp_add_const`); `IsDiscrete` is a structure
   (`isDiscrete_iff_nhdsNE`), `IsCompact.finite : IsCompact s → IsDiscrete s → s.Finite`;
   `ContDiffAt.isSymmSndFDerivAt` needs `minSmoothness ℝ 2 ≤ n` (`minSmoothness_of_isRCLikeNormedField`).
