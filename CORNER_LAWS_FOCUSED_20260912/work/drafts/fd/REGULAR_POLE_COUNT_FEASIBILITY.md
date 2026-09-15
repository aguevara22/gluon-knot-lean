# Feasibility probe: `SM.RegularPoleCount` (fd:regular-pole-count, sm-3:2894-2897)

Written 2026-09-14 by the feasibility-probe agent (bounded ~90 min). Scope: the single unproved
ingredient of row 88 fd:linking-calculus, `def RegularPoleCount : Prop` at
`work/lean/SM/LinkingCalculus.lean:526`. Nothing under `work/lean` was touched; all Lean checks ran
as `lake env lean /tmp/<file>.lean` importing the built `SM.LinkingCalculus` plus Mathlib modules.
Test files: `/tmp/rpc_stmts.lean` (statement skeleton, 164 lines, typechecks with `sorry`),
`/tmp/rpc_alg.lean`, `/tmp/rpc_cpt.lean`, `/tmp/rpc_mk.lean` (three calibration proofs, see §5).

**Follow-up (same day):** the proof skeleton along this route is `work/drafts/fd/RPC_Skeleton.lean`
(compiles, 29 `sorry` leaves, `SM.regularPoleCount` and `SM.crossing_formula_unconditional` proved from them);
per-leaf plan: `work/drafts/fd/RPC_PLAN.md`.

## 0. Verdict in one paragraph

**FEASIBLE** (estimate 1400-2000 lines; clear route; no topology). The winning route is NOT the
printed one (deleted discs, Green on the punctured torus, a limit h → 0 of cap boundary integrals)
and NOT a winding-number route. It is the standard "bump form" proof of degree theory: replace the
singular primitive `λ_N = −(X dY − Y dX)/(4π(1−Z))` by a *globally smooth* primitive
`λ_χ = k_χ(Z)·(N × x)·dx` with `k_χ(Z) = (χ(Z) − 1)/(4π(1−Z))`, `χ` a `ContDiffBump` at `Z = 1`.
Then `dλ_χ = ω − ρ` with `ρ = φ'(Z) dA`, `φ(Z) = (1+Z)χ(Z)/(4π)`, a smooth 2-form of total mass 1
supported in a small cap around `N`. Exactness on the torus (one-variable FTC + periodicity, already
the pattern of `LinkingCalculus.Family.integral_fderiv1_eq_zero`) gives
`(1/4π)∫∫ D = ∫∫ D·φ'(Z∘G)`; the right side lives in the finitely many inverse-function-theorem
neighbourhoods of the preimages and is evaluated there by Mathlib's change-of-variables formula
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`, giving `σ(p)·∫_{ℝ²} ψ = σ(p)`.
No limit, no boundary integrals around discs, no winding number, no independence of `N`.
Main risk: volume of finite-family ε-management and measure-theory plumbing, not mathematics.

## 1. Mathlib inventory (question 1)

Present (all names checked against the pinned Mathlib, `lake env lean`):
* Box divergence theorem: `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` and the
  2-D corollaries `integral2_divergence_prod_of_hasFDerivAt[_off_countable]`,
  `integral_divergence_prod_Icc_of_hasFDerivAt_of_le` (`Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:427-560`;
  note the pinned names say `hasFDerivAt`, not `hasFDerivWithinAt`). **Not needed** by the chosen
  route: the exactness step reduces to FTC per slice + Fubini swap, both already in the file
  (`ftc_slice*`, `integral_integral_swap_of_continuous`, `Family.integral_fderiv{1,2}_eq_zero`).
* Change of variables: `integral_image_eq_integral_abs_det_fderiv_smul (hs : MeasurableSet s)
  (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g)` and
  `integral_target_eq_integral_abs_det_fderiv_smul` for an `OpenPartialHomeomorph`
  (`Mathlib/MeasureTheory/Function/Jacobian.lean:1213,1225`). Works on `ℝ × ℝ` with `volume`.
* Inverse function theorem: `ContDiffAt.hasStrictFDerivAt`, `HasStrictFDerivAt.toOpenPartialHomeomorph`,
  `mem_toOpenPartialHomeomorph_source`, `map_nhds_eq_of_equiv` (`InverseFunctionTheorem/FDeriv.lean:117-190`),
  `PartialEquiv.injOn`.
* Smooth cutoffs: `ContDiffBump (c : E)` with `rIn, rOut, one_of_mem_closedBall, zero_of_le_dist,
  support_eq, contDiff, nonneg`; instance `hasContDiffBump_of_innerProductSpace` (import
  `Mathlib.Analysis.Calculus.BumpFunction.InnerProduct`).
* Polar coordinates: `integral_comp_polarCoord_symm (f : ℝ × ℝ → E) :
  ∫ p in polarCoord.target, p.1 • f (polarCoord.symm p) = ∫ p, f p`.
* Determinant on `ℝ × ℝ`: `LinearMap.det_toMatrix`, `Basis.finTwoProd`, `Matrix.det_fin_two`;
  `ContinuousLinearMap.det` is an abbrev for `LinearMap.det ↑f`.
* Misc: `IsCompact.exists_isMaxOn`, `Function.Periodic.intervalIntegral_add_eq`,
  `setIntegral_eq_integral_of_forall_compl_eq_zero`, `integral_finset_biUnion`,
  second-derivative symmetry via `ContDiffAt.isSymmSndFDerivAt` (already wrapped as
  `Family.fderiv_fderiv_symm`), `Family.inner_fderiv_eq_zero` (⟪G, G'a⟫ = 0 from ‖G‖ ≡ 1),
  `Family.fderiv_periodic`, `Family.triple`, `contDiff_fderiv_apply`, the whole `cross` algebra
  (`inner_cross_cyclic`, `cross_cross_eq`, `inner_cross_projAlong`, ...).
* Stereographic projection exists (`stereoToFun/stereoInvFun`, `Geometry/Manifold/Instances/Sphere.lean`)
  but is not needed; the orthogonal projection to `N^⊥` is a simpler chart near `N`.

Absent (grep over the pinned Mathlib):
* No topological degree of a map, no winding number of a loop (zero hits for `winding`), no Stokes
  on manifolds with boundary, no homotopy invariance of line integrals. `circleIntegral` is for
  literal circles in ℂ. Covering-space lifting exists (`IsCoveringMap.liftPath`, `liftHomotopy`,
  `monodromy_theorem`, `existsUnique_continuousMap_lifts`, `Complex.isCoveringMap_exp`,
  `AddCircle.isCoveringMap_coe`), but connecting a lift of `arg ∘ F` to `∮ Im(F̄ dF)/|F|²` and to
  `sign det DF(p)` would be several hundred lines from scratch. The chosen route needs none of it.

## 2. The route in detail (question 2)

Conventions: `G : ℝ × ℝ → E3` (uncurried), `D = Family.triple G eu2 ev2 = ⟪G, G_u × G_v⟫ =
gaussDensity`, `Z = ⟪G, N⟫`, `eu2 = (1,0)`, `ev2 = (0,1)`. All statements below are in
`/tmp/rpc_stmts.lean` and typecheck (`sorry` bodies). Support column: M = Mathlib lemma applies
directly, F = already in `LinkingCalculus.lean`, S = from scratch (elementary), P = proved in /tmp.

Step 0 (algebra, S/F, ~120 lines).
* `cross_fderiv_eq_smul : cross (G'a) (G'b) = triple G a b x • G x` from ‖G‖ ≡ 1 (uses
  `inner_fderiv_eq_zero`, `cross_cross_eq`: `(a×b)×g = 0` when `a,b ⊥ g`).
* Binet–Cauchy `⟪a×b, c×d⟫ = ⟪a,c⟫⟪b,d⟫ − ⟪a,d⟫⟪b,c⟫` — **P**, 3 lines (`simp [inner_eq_sum,
  cross_apply*]; ring`).
* `core_algebra` — **P**, 20 lines: `k'·(⟪gu,n⟫⟪n×g,gv⟫ − ⟪gv,n⟫⟪n×g,gu⟫) + k·(⟪n×gu,gv⟫ − ⟪n×gv,gu⟫)
  = D·(2Zk − (1−Z²)k')` given `gu×gv = D•g`, ‖g‖ = ‖n‖ = 1. This is the entire exterior-derivative
  computation once the product/chain rule is expanded.

Step 1 (exactness on the torus, F/S, ~250 lines).
* `oneForm k N G x w := k ⟪G x, N⟫ * ⟪cross N (G x), fderiv ℝ G x w⟫` (= `G^*(k(Z)(N×x)·dx)`).
* `fderiv_oneForm_antisymm : ∂_u(oneForm · ev2) − ∂_v(oneForm · eu2) = D · mk k Z` with
  `mk k Z = 2Zk(Z) − (1−Z²)k'(Z)`. Proof: `HasFDerivAt` product/chain rule as in
  `Family.fderiv_triple_apply`, the second-derivative terms cancel by `fderiv_fderiv_symm`, then
  `core_algebra`. Sanity: `k = −1/(4π(1−Z))` gives `mk ≡ 1/(4π)`, i.e. `d(G^*λ_N) = G^*ω`, the
  printed identity sm-3:2876-2878.
* `integral_fderiv_eu_eq_zero`, `integral_fderiv_ev_eq_zero`: `∫_a^{a+P}∫_b^{b+P} ∂_u F = 0` for
  smooth `F` periodic in `u` — two-variable copies of `Family.integral_fderiv1_eq_zero` (25 lines
  each in the file; FTC per slice + periodicity, swap for the `v`-direction).
* `integral_triple_mul_mk_eq_zero : ∫∫ D · mk k Z = 0` for ANY smooth `k` — combine the two.
* `cutoffK χ Z := (χ Z − 1)/(4π(1−Z))`, `bumpPhi χ Z := (1+Z) χ Z/(4π)`;
  `contDiff_cutoffK` (S, ~30 lines: on `{Z < 1}` a smooth quotient, on `ball 1 rIn` identically 0,
  glue with `contDiff_iff_contDiffAt` + `ContDiffAt.congr_of_eventuallyEq`);
  `mk_cutoffK : mk (cutoffK χ) Z = 1/(4π) − deriv (bumpPhi χ) Z` — **P** for `Z ≠ 1`
  (`/tmp/rpc_mk.lean`, ~35 lines incl. helpers, `field_simp; ring`); the point `Z = 1` is the
  locally-constant case (both sides 0), ~15 more lines.
* `gaussIntegral_eq_integral_bump : gaussIntegral P G = ∫_a^{a+P}∫_b^{b+P} D · φ'(Z)` — the two
  previous items plus `pderivU_eq_fderiv`, `Periodic.intervalIntegral_add_eq` for the box shift.

Step 2 (localisation and change of variables, M/S, ~600-800 lines).
* Positive orthonormal frame `(e₁, e₂, N)` with `cross e₁ e₂ = N` for a unit `N` (S, ~40 lines;
  explicit: `e₁ ∝ N × e_j` for a coordinate vector `e_j` not parallel to `N`, `e₂ = N × e₁`).
* `chart e₁ e₂ G x := (⟪G x, e₁⟫, ⟪G x, e₂⟫) : ℝ × ℝ`; `det_fderiv_chart : det (D chart) = D · Z`
  (Binet–Cauchy with `e₁×e₂ = N` and `cross_fderiv_eq_smul`; the `LinearMap.det` on `ℝ × ℝ` via
  `det_toMatrix (Basis.finTwoProd ℝ)` + `det_fin_two`, ~40 lines), and Parseval
  `⟪G,e₁⟫² + ⟪G,e₂⟫² + Z² = 1` (~15 lines).
* `exists_regular_nhd`: at a preimage `p` with `D p ≠ 0`, IFT for `chart` (derivative invertible
  since `det = D·1 ≠ 0`) gives an open `V ∋ p`, `V ⊆ U` (any prescribed nhd), `InjOn chart V`,
  `Z > 0` and `sign D = sign D p` on `V` (continuity), and `ball 0 r ⊆ chart '' V`
  (`map_nhds_eq_of_equiv`, `chart p = 0`). M + ~80 lines of plumbing.
* Disjoint neighbourhoods for the finitely many preimages (S, ~60 lines: `U_p := ball p (r₀)` with
  `r₀` half the minimum pairwise distance, `Finset.exists_min_image`), all inside the open box.
* `exists_delta_of_compact` — **P**, 12 lines (`/tmp/rpc_cpt.lean`): on the compact
  `K = box ∖ ⋃ V_p`, `Z ≤ 1 − δ`. Needs `Z = 1 ↔ G = N` for unit vectors
  (`inner_eq_one_iff_of_norm_one`) and that every preimage in the closed box is one of the `p`.
* `chartDensity χ w := φ'(√(1−|w|²))/√(1−|w|²)` on the disc, `0` outside.
* `integral_bump_on_nhd : ∫_V D·φ'(Z) = sign(D p) · ∫_{ℝ²} chartDensity χ` — pointwise
  `D φ'(Z) = sign(D p)·|det D chart|·chartDensity (chart x)` on `V` (uses `Z = √(1−|chart x|²)`,
  `Z > 0`), then `integral_image_eq_integral_abs_det_fderiv_smul` and
  `setIntegral_eq_integral_of_forall_compl_eq_zero` (support of `chartDensity` inside `ball 0 r ⊆ chart '' V`).
  M + ~120 lines.
* `integral_chartDensity : ∫_{ℝ²} chartDensity χ = 1` when `χ.rOut < 1`: `integral_comp_polarCoord_symm`,
  the angular integral is `2π`, the radial integral is `∫_0^1 φ'(√(1−r²)) r/√(1−r²) dr =
  φ(1) − φ(0) = 2·(1/(4π)) − 0 = 1/(2π)` by FTC with `d/dr √(1−r²) = −r/√(1−r²)`
  (`intervalIntegral.integral_comp_mul_deriv` or `integral_eq_sub_of_hasDerivAt`; care at the
  endpoint `r = 1` where the substitution is singular — restrict to `[0, 1−ε]` where the integrand
  vanishes anyway because `φ' = 0` for `Z ≤ 1 − rOut`). S, ~120-150 lines; the fiddliest analysis.
* `integral_bump_eq_sum` (main lemma on a closed period box with no preimage on its boundary):
  `∃ δ₀ > 0, ∀ χ, χ.rOut < δ₀ → ∫∫ D·φ'(Z) = ∑_{p} sign (D p)`: box integral → integral over
  `⋃ V_p` (`setIntegral_eq_integral_of_forall_compl_eq_zero` + Fubini `setIntegral_prod` as in
  `DivergenceTheorem.lean:530-540`) → `integral_finset_biUnion` → per-`V_p` result. ~150 lines.

Step 3 (fundamental-domain shift, S, ~120 lines).
* `exists_shift`: choose `a, b ∈ (0,P)` avoiding the finitely many coordinates of the preimages
  (mod `P`); then no preimage lies on `∂([a,a+P]×[b,b+P])`, the preimages in that box are
  `τ(p) = p + (P·[p.1 < a], P·[p.2 < b])` for `p ∈ hfin`, `τ` is injective, and
  `gaussDensity ∘ τ = gaussDensity` by periodicity (`Finset.sum_image`/`sum_nbij`).
* `regularPoleCount : RegularPoleCount`: unfold, `gaussIntegral_eq_integral_bump` on the shifted box
  with `χ := ⟨1, rOut/2, rOut⟩` for `rOut < min δ₀ 1`, then `integral_bump_eq_sum`, then the sum
  bijection. The `Prop` `RegularPoleCount` is consumed unchanged by `crossing_formula`; nothing in
  the row's statement moves.

## 3. Why the other routes are worse

* Printed route (discs, Green on the punctured torus, `h → 0`): needs Stokes on a region with
  curved boundary (absent) or the partition-of-unity argument of sm-3:2903-2916 (large), plus a
  limit of cap boundary integrals `−(1+cos h)/2 → −1` requiring uniform control of `G^*λ_N` on
  shrinking circles. Estimated 4000+ lines.
* Squares instead of discs + box divergence theorem: the complement of `n` squares in the box is a
  grid of `O(n²)` rectangles with cancelling interior edges (heavy bookkeeping), and the boundary
  term of each small square is a winding number `∮ G^*λ_N → −σ(p)` whose evaluation is exactly
  "degree of a local diffeomorphism = sign of the Jacobian": needs homotopy to the linear map plus
  discreteness of `∮ d arg` — several hundred lines of from-scratch topology. The bump route makes
  this vanish: the sign enters only through `|det|` in the change of variables.
* Complex-analytic winding numbers via stereographic projection: Mathlib has no winding number and
  no `∮ dz/z = 2πi·(index)` for general loops; would be built from `IsCoveringMap.liftPath` for
  `Complex.exp`. Not competitive.
* "Signed count is constant on regular values" (degree independence of `N`): pure topology, not
  in Mathlib, and NOT needed — the bump route works at the given `N` directly. The paper itself
  says its proof uses no degree theorem (sm-3:2914-2916); the bump route honours that.

## 4. Estimate and risk (question 3)

| part | lines | support | risk |
|---|---|---|---|
| 0 algebra (`cross_fderiv_eq_smul`, Binet–Cauchy, `core_algebra`, Parseval, frame) | 150 | F/P | low (2 of 4 proved) |
| 1 exactness (`fderiv_oneForm_antisymm`, two Green lemmas, `contDiff_cutoffK`, `mk_cutoffK`, `gaussIntegral_eq_integral_bump`) | 300 | F/P | low-medium: derivative bookkeeping like `fderiv_triple_apply` (verbose but mechanical) |
| 2a IFT neighbourhoods + disjointness + compactness | 250 | M/P | medium: finite-family ε-management, `OpenPartialHomeomorph` API |
| 2b det of the chart + change of variables on one `V` | 200 | M | medium: `LinearMap.det` on `ℝ×ℝ`, `HasFDerivWithinAt` from `HasFDerivAt`, measurability |
| 2c polar normalisation `∫ ψ = 1` | 150 | M/S | medium: singular substitution at `r = 1` (avoidable as noted) |
| 2d box → union → sum (`integral_bump_eq_sum`) | 150 | M | medium: Fubini conversions iterated-interval ↔ set integral on `ℝ×ℝ` |
| 3 shift + Finset bijection + assembly | 200 | S | low-medium: bookkeeping |
| **total** | **1400** (range 1400-2000) | | |

Calibration: three from-scratch pieces attempted cold compiled in 1-3 iterations each
(`core_algebra` 20 lines, `exists_delta_of_compact` 12 lines, `mk_cutoffK` generic case ~35 lines);
API friction seen: `ContDiff.differentiable` wants `n ≠ 0`, this Mathlib's `deriv_mul` is stated
with Pi-multiplication (use `HasDerivAt.mul` then `.deriv`), `Set.mem_setOf_eq` is deprecated.
Previous estimates in this project ran 5-10x pessimistic when a clean route existed; the bump route
is that clean route, so the 1400-2000 figure is meant literally, not as a floor.

Honest caveats. (i) The route is a different PROOF from the printed one (bump 2-form on the sphere
instead of deleted discs and a limit); the STATEMENT proved is exactly the printed
fd:regular-pole-count as encoded in `RegularPoleCount`, so this is a proof-route deviation to record
in the report, not a fidelity issue. (ii) The hypothesis `hfin` (finite preimage in `[0,P)²`) is
used as given; regularity `D ≠ 0` at preimages is essential for the IFT step. (iii) Nothing in the
route depends on `N` being `ν` or `−ν`; the frame construction handles every unit `N`.

## 5. Verdict (question 4)

**FEASIBLE**: < 3000 lines (best estimate 1400-2000), a clear route with every step either a
direct Mathlib application, a copy of an existing `Family` lemma, or elementary analysis, and three
of the "unknown-friction" pieces already proved in /tmp. Suggested order: Step 0 → Step 1 (gets the
identity `gaussIntegral = ∫∫ D·φ'(Z)`, the mathematical heart, ~450 lines) → Step 2b/2c (change of
variables and normalisation, the API-heavy part) → Step 2a/2d → Step 3 → assemble and discharge the
`RegularPoleCount` hypothesis of `crossing_formula`, which would complete row 88 unconditionally.
