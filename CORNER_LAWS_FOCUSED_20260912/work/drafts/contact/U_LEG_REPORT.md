# U_LEG_REPORT — unit LEG (U2 + U3), prover report

File: `work/drafts/contact/U_LEG.lean` (copy of `Skeleton_FINAL.lean`; frozen parts untouched).
Check: `cd work/lean && lake env lean ../drafts/contact/U_LEG.lean` → **0 errors**, 9 warnings
"declaration uses `sorry`" (the leaves of the other units: `u_circle`, `u_sl_radius`, `u_sl_family`,
`u_sl_reparam`, `u_sl_isotopy`, `u_reading`, `u_transport`, `u_regular`, `u_family`).
`grep -c sorry`: **12 before → 10 after** (line 19 is the module docstring's mention; the other 9 are
the leaves above).  `diff Skeleton_FINAL.lean U_LEG.lean`: one pure insertion (`560a561,1061`, the
helper block) and the two `sorry` bodies replaced; no statement, definition, name or docstring changed.
`#print axioms SM.u_legendrianFront` / `SM.u_spatialOf`: `[propext, Classical.choice, Quot.sound]`
(no `sorryAx`, no `src_contact`, no literature axiom).

## Leaves

| leaf | status | body |
|---|---|---|
| `u_spatialOf : U_spatialOf` (U3) | **PROVED** | `⟨ulg_sp h1, fun _ _ => rfl, ulg_cusped h1 h2 h3⟩` |
| `u_legendrianFront : U_legendrianFront` (U2) | **PROVED** | `⟨ulg_front h1 h2 h3, ⟨⟨h1, h2⟩, rfl, fun _ _ => rfl⟩⟩` |

Leaves left in this unit: none.  No leaf of this unit is false or needs a stronger hypothesis.

## Route (PLAN_FINAL §6 U2+U3, followed as written)

1. `ulg_T Lc := fun t => toSpace (Lc (2πt))` (1-periodic `Space` curve); coordinates are `rfl`
   (`ulg_xOf/yOf/zOf/xzOf`: `xzOf (ulg_T Lc) t = GenericFront.front Lc (2πt)`); derivatives by the
   chain rule through the scaling (`ulg_hasDerivAt_scale`): `deriv (xzOf (ulg_T Lc)) t = (2π x′, 2π z′)`
   at `θ = 2πt` (`ulg_deriv_xzOf`), `deriv (ulg_T Lc) t = (2π x′, 2π y′, 2π z′)`.
2. `ulg_sp h1 : SpatialLink 1` (`T := fun _ => ulg_T Lc`; smooth, periodic, embedded via
   `toE3_toSpace` + `IsEmbeddedCircle.injective` + cancel `2π`, regular via `immersion`).
3. `ulg_cusped : (ulg_sp h1).CuspedProjection`:
   * `cusps_finite`: cusp ⇔ `x′(2πt) = 0` (`ulg_deriv_xzOf_eq_zero_iff`, from `z′ = y x′` = `ulg_z'`),
     so `cuspSet ⊆ (θ ↦ (0, θ/2π)) '' (GenericFront.cuspSet Lc ∩ Ico 0 2π)`, finite by `finite_cusps`;
   * `exact_germ`: from `IsExactCuspGerm` at `θc = 2πt₀`; `y′ ≠ 0` on a δ-interval by continuity of
     `deriv (coordY Lc)` (`Metric.eventually_nhds_iff` on `ContinuousAt.eventually_ne`), radius
     `δ = min ε δ₁ / 2π` (`ulg_abs_scale_lt` converts `|s − t| < δ/2π` to `|2πs − 2πt| < δ`); the three
     coordinate formulas are the printed ones (`Prod.ext hx (Prod.ext rfl _)`, `ring` for `2/3·A` vs `2A/3`);
   * `doubles_finite`, `transverse`, `no_triple`, `heights_distinct`: `ulg_isDoubleOf_iff :
     IsDoubleOf (ulg_sp h1).projLoop p q ↔ (2π p.2, 2π q.2) ∈ doublePoints Lc` (through
     `SameT.sameParam_iff` and `ulg_sameT_iff : SameT s t ↔ GenericFront.SameParam (2πs) (2πt)`), then
     `finite_double` (image under `(θ,η) ↦ (0, θ/2π)`), `transverse_double` (`det = (2π)²·(x′z′ − z′x′)`),
     `no_triple`, and embeddedness (`ext i; fin_cases i` on `E3` with the two front coordinates and the height).
4. `ulg_front h1 h2 h3 : SmoothFront` BUILT from `sp`: `c := 1`, `comp := fun _ => (ulg_sp h1).projLoop 0`,
   so `(ulg_front …).comp i = (ulg_sp h1).projLoop 0` is `rfl` (`ulg_front_comp`) and
   `(F.comp i).γ t = GenericFront.front Lc (2πt)` is `rfl` — the `IsLegendrianFrontOf` witness is
   `⟨⟨h1, h2⟩, rfl, fun _ _ => rfl⟩`.  Fields: `cusps_finite`/`doubles_finite`/`transverse`/`no_triple`
   reuse step 3 (`ulg_pairs_finite` for the ordered-pair set); `no_vertical` = `ulg_no_vertical`
   (`x′ = 0 ⇒ (x′, z′) = 0`); `cusp_alone` from `no_cusp_on_branch`; **`cusp_semicubical` /
   `cusp_nonvertical`** = `ulg_semicubical`, the R2 item:
   * `ulg_loop_eventually_germ`: near a cusp parameter `t`, `xzOf (ulg_T Lc) =ᶠ[nhds t] germFront A y₀ x₀ z₀ ∘ u`
     with `u s := coordY Lc (2πs) − coordY Lc (2πt)` (smooth, `u t = 0`, `u′ t = 2π y′(2πt) ≠ 0`);
   * `ulg_comp_derivs` (the chain-rule lemma of PLAN §7 R2): for smooth `g : ℝ → Plane`, `u : ℝ → ℝ` and a
     point with `g′(u t) = 0`: `(g∘u)″(t) = u′² • g″(u t)` and `(g∘u)‴(t) = 3u′u″ • g″(u t) + u′³ • g‴(u t)`
     (Leibniz to order 3 via `HasDerivAt.scomp` / `HasDerivAt.smul` / `HasDerivAt.mul`, derivatives of `g∘u`
     computed as functions to order 2, then pointwise);
   * `ulg_germ_cusp`: with `germFront`'s derivatives at `0` (`deriv_germFront`, `iteratedDeriv_two/three_germFront`
     of FrontSmooth) this gives `det(γ″, γ‴) = 8A²u′⁵ ≠ 0` and `x″ = 2A u′² ≠ 0`; eventual equality transfers the
     derivatives (`hγ.deriv.deriv_eq`, `hγ.deriv.deriv.deriv_eq`).

## Helpers added (57, prefix `ulg_`, all in §5.4 immediately before `theorem u_legendrianFront`)

curve and derivatives: `ulg_T`, `ulg_T_def`, `ulg_contDiff_toSpace`, `ulg_toSpace_injective`, `ulg_two_pi_pos`,
`ulg_two_pi_ne`, `ulg_hasDerivAt_scale`, `ulg_smooth_scale`, `ulg_T_smooth`, `ulg_T_periodic`, `ulg_xOf`, `ulg_yOf`,
`ulg_zOf`, `ulg_xzOf`, `ulg_hasDerivAt_coord`, `ulg_hasDerivAt_xOf/yOf/zOf`, `ulg_deriv_xOf/yOf/zOf`,
`ulg_hasDerivAt_xzOf`, `ulg_deriv_xzOf`, `ulg_hasDerivAt_T`, `ulg_deriv_T`, `ulg_z'`, `ulg_deriv_xzOf_eq_zero_iff`,
`ulg_deriv_T_ne_zero`, `ulg_T_sameT`;
parameter bridge `θ = 2πt`: `ulg_sameT_iff`, `ulg_mem_Ico_iff`, `ulg_not_sameParam_of_ne`, `ulg_abs_scale_lt`,
`ulg_mem_cuspSet_iff`;
U3: `ulg_sp` (def), `ulg_sp_T`, `ulg_sp_projLoop_γ`, `ulg_isCusp_iff`, `ulg_cuspSet_finite`, `ulg_exact_germ`,
`ulg_isDoubleOf_iff`, `ulg_doubles_finite`, `ulg_pairs_finite`, `ulg_transverse`, `ulg_no_triple`,
`ulg_heights_distinct`, `ulg_cusped`;
U2: `ulg_iteratedDeriv_two`, `ulg_iteratedDeriv_three`, `ulg_comp_derivs`, `ulg_germ_cusp`,
`ulg_loop_eventually_germ`, `ulg_semicubical`, `ulg_no_vertical`, `ulg_cusp_alone`, `ulg_front` (def), `ulg_front_comp`.

## Mathlib / library pitfalls met (this pin)

* `EuclideanSpace` coordinates elaborate to `(Lc θ).ofLp i`; `simpa using h` does NOT see through
  `GenericFront.front` — ascribe the type (`have h0 : Lc θ 0 = Lc η 0 := congrArg Prod.fst hfr`), then
  `ext i; fin_cases i <;> simpa using …` works as in `gp1_deriv_y_ne_zero`.
* `Filter.EventuallyEq.deriv` is `protected`: use dot notation (`hγ.deriv`, `hγ.deriv.deriv_eq`).  The
  skeleton has no `open Topology`, so write `nhds t` / `Filter.EventuallyEq (nhds t) f g` (no `𝓝`, no `=ᶠ`).
* `ContDiff.iterate_deriv n` yields `ContDiff ℝ ∞ (deriv^[n] f)`; it is accepted definitionally as
  `ContDiff ℝ ∞ (deriv (deriv f))` for `n = 2` (`have hg2 : … := hg.iterate_deriv 2`).
* `HasDerivAt.smul` is stated for `c • f` (pointwise); restate it as `HasDerivAt (fun s => c s • f s) … s`
  (defeq) BEFORE `rw [h.deriv]` — `rw` is syntactic.  `HasDerivAt.mul` for `u′·u′` avoids `HasDerivAt.pow`'s casts.
* `iteratedDeriv 2 f = deriv (deriv f)`: `rw [iteratedDeriv_succ, iteratedDeriv_one]` (`ulg_iteratedDeriv_two`);
  FrontSmooth's `iteratedDeriv_two_germFront` / `iteratedDeriv_three_germFront` are stated with `iteratedDeriv`,
  so rewrite backwards (`rw [← ulg_iteratedDeriv_two, iteratedDeriv_two_germFront]`).
* `det` on `Plane` after `smul`: `simp only [det, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]; ring`
  (`Prod.fst_add`/`Prod.snd_add` are unused there and the linter flags them).
* `2 * π * t / (2 * π) = t` is `mul_div_cancel_left₀ t (h : 2 * π ≠ 0)`; `2 * π * (δ / (2 * π)) = δ` by `field_simp`.
* `Metric.eventually_nhds_iff.1 (hcont.continuousAt.eventually_ne hy')` gives the radius on which `y′ ≠ 0`;
  convert `dist` with `Real.dist_eq`.  `nlinarith` closes `t ∈ Ico 0 1 ↔ 2πt ∈ Ico 0 (2π)`.
* `GenericFront.IsExactCuspGerm`'s `z` formula has `2 / 3 * A`, `SpatialLink.ExactCuspGerm` and `germFront`
  have `2 * A / 3`: `show` the coordinate goal in `coordZ` form, `rw [hz]; ring`.
* `hLc.differentiable (by simp)` for `1 ≤ ∞` (as in the library).

## For the assembler / executor

* The helper block is self-contained: it uses §0 (`toE3`, `toSpace`, `toE3_toSpace`) and the accepted layer
  (`GenericFront.*`, `ContactMotions.hasDerivAt_coord/contDiff_coord`, FrontSmooth's `germFront_*`,
  `SameT.*`, `SpatialLink`) — standard axioms only.  It can be ported verbatim into a `SM/FdContactUnits*.lean`
  module (rename prefix at porting time if desired).
* Exported for U5 (`U_transport`) should the executor want the definitional package of PLAN §5: `ulg_sp h1`,
  `ulg_front h1 h2 h3`, `ulg_front_comp : (ulg_front h1 h2 h3).comp i = (ulg_sp h1).projLoop 0 := rfl`.  NOTE the
  frozen statements `U_spatialOf` / `U_legendrianFront` quantify `sp` and `F` separately, so `U_package_of`
  does not see the definitional link; `U_transport`'s statement already works from the hypotheses
  `sp.T i t = toSpace (Lc (2πt))` and `IsLegendrianFrontOf Lc F` alone (and `IsLegendrianFrontOf.unique`
  identifies any such `F` with `ulg_front`).  Reusable for U5/U6: `ulg_deriv_xzOf_eq_zero_iff` (cusp ⇔ `x′ = 0`),
  `ulg_z'` (`z′ = y x′`), `ulg_deriv_xzOf`, `ulg_deriv_T`, `ulg_isDoubleOf_iff`, `ulg_sameT_iff`, `ulg_mem_Ico_iff`.
* Sign/orientation check done in passing: `IsTransverseDouble L θ η = x′(θ)z′(η) − z′(θ)x′(η) ≠ 0` equals
  `det (deriv xz θ) (deriv xz η) / (2π)²`, so row 87's transversality is exactly row 91's / ng:front-domain's.
* Size: ≈500 lines for U2+U3 together (PLAN estimated 1,400); the R2 chain-rule lemma is 45 lines.
