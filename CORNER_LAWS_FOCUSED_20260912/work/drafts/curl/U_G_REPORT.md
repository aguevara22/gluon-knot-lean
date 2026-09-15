# U_G_REPORT — Unit G (positive-turn chart, cuts, disc, cut-fit), 2026-09-14

File: `work/drafts/curl/U_G.lean` (copy of `Skeleton_FINAL.lean` with the Unit G sorries filled).
Check: `cd work/lean && lake env lean ../drafts/curl/U_G.lean` — **0 errors**; the only non-sorry warning is the
inherited `<;>` linter note at line 567. `grep -c sorry`: 56 before → **41** after (15 leaves closed; the two
degenerate-case leaves below keep one `sorry` each; the two remaining hits at lines 17/518 are the skeleton's
prose). No statement, definition, structure, name or docstring was changed (checked: all 54 docstring+statement
blocks of `Skeleton_FINAL.lean` occur verbatim in `U_G.lean`, and every non-`sorry` line of the skeleton is
present). `#print axioms` of the 17 leaves: 14 are `[propext, Classical.choice, Quot.sound]`; `exists_cutFit`
adds `sorryAx` only through the Unit-F black boxes `xFit_pos`, `yFit_bound`; `ξ_strictMonoOn`, `ξ_strictAntiOn`
through their own residual `sorry`.

## Leaves proved (15 of 17, all clauses)

`det_vDir_u`, `planeDot_vDir_u`, `expansion`, `exists_chart`, `hasDerivAt_η`, `hasDerivAt_ξ`, `η_strictMonoOn`,
`exists_cuts`, `cut_displacement`, `endpoint_tangent`, `exists_disc_in_chart`, `disc_isDisc`,
`p_mem_interior_disc`, `tail_tangent_ne`, `exists_cutFit`.

Proof notes (for the assembler / Unit R):
- Frame: `g_vDir_eq : vDir S = (u₂, −u₁)`, `g_u_sq : u₁² + u₂² = 1`, `g_u_eq : u = (cos θ(t₀), sin θ(t₀))`
  (from `tangent_at` + `lift`), `g_T_eq : T t = (cos θ t, sin θ t)` on `[α, β]`.
- Chart derivatives: `g_hasDerivAt_planeDot` (component derivatives through `ContinuousLinearMap.fst/snd`
  `.hasFDerivAt.comp_hasDerivAt`), `g_deriv_eq_smul_T : γ' = |γ'| • T`, `g_planeDot_T_u = cos θrel`,
  `g_planeDot_T_v = −sin θrel`.
- **Mean value theorem**: Mathlib's `exists_hasDerivAt_eq_slope` / `strictMonoOn_of_deriv_pos`
  (`Mathlib.Analysis.Calculus.Deriv.MeanValue`) are NOT in the import closure of `SM.Rounding`/`SM.LinkMoves`/
  `SM.PolynomialBlock`; only Rolle (`exists_hasDerivAt_eq_zero`) is. Derived here: `g_exists_hasDerivAt_eq_slope`,
  `g_strictMonoOn_of_deriv_pos`, `g_strictAntiOn_of_deriv_neg` (general real-function lemmas; Unit H's
  `sep_of_deriv`/`deriv_blend_*` provers may want them too — same names would clash, so reuse or rename).
- Monotonicity in the form the construction needs: `g_ξ_strictMonoOn (hα) (hθ on Icc α' t₀) : StrictMonoOn ξ (Icc α' t₀)`
  and `g_ξ_strictAntiOn (hβ) (hθ on Icc t₀ β') : StrictAntiOn ξ (Icc t₀ β')`; `exists_cuts` and `exists_cutFit`
  use these, not the leaves.
- `exists_cuts`: `a = max α' (t₀ − δ/3)`, `b = min β' (t₀ + δ/3)`, level `m = max (ξ a) (ξ b) < ξ t₀ = 0`,
  `intermediate_value_Icc` on `[a, t₀]` and `intermediate_value_Icc'` on `[t₀, b]`.
- `exists_disc_in_chart`: `g_ne_p` — `γ t ≠ p` for `t ∈ [β', α' + 1]` (on `[β', β]` by `embedded`; for `t > β`
  the pair `(fract t₀, fract t)` would be a double point of `F`, so `carried.doubles` gives an occurrence `v`
  with `τ v = fract t₀`, contradicting `no_double v ⌊t₀⌋`; `t − t₀ ∈ (0, 1)` is not an integer via
  `Int.fract_eq_fract`). Minimum of `eucDist (γ t) p` on the compact complementary arc (`isCompact_Icc.exists_isMinOn`),
  `r = min (m/2) (ε/2)` with `ball p ε ⊆ Δ₀`; reduction of `t` into `[β', β' + 1)` by `n₀ = −⌊t − β'⌋`.
- Discs: `disc S r = planeComplex ⁻¹' closedBall` (`g_disc_eq_preimage`), convexity via `Convex.is_linear_preimage`
  with `CornerRounding.E_planeComplex_add`/`planeComplex_smul`; compactness via closed + bounded inside the product
  `closedBall p r` (`CornerRounding.E_dist_le_eucDist`); interior via the product ball of radius `r/2`
  (`g_ball_subset_disc`, `CornerRounding.E_eucDist_le_add`). The `E_*` lemmas of Rounding.lean §Unit E live in
  namespace `SM.CornerRounding` (the namespace stays open through the `discs` section), hence the prefix.
- `exists_cutFit`: cuts within `δ = min δ₁ δ₂ δ₃` of `t₀` where `|γ t − p| < r/2`, `|η t| < r/24`, `|θrel t| < π/3`;
  `a = −sin θrel s₁`, `b = cos θrel s₁ > 1/2`, `c = sin θrel s₂`, `d = cos θrel s₂ > 1/2` (`endpoint_tangent`,
  `neg_smul` for `T_plus`); `ℓ_pos` from `η_strictMonoOn`; `old_in_disc` from `|γ t − p| < r/2`; `ins_in_disc` from
  `|Φc t − p| ≤ |p₋ − p| + (ℓ/12)·|A(c t − b(−2))| ≤ r/2 + (ℓ/12)(4(x + |y|) + 12)` with `x ≤ 11`
  (`g_xFit_le`: `2ac ≤ 4bc` since `a ≤ 1 < 2b`), `|y| < 11/4` (`g_yFit_abs_lt` from `yFit_bound`), `ℓ < r/12`,
  so `< r/2 + 67r/144 < r`. Model bounds `|z₁| ≤ 4`, `|z₂| ≤ 12` (`g_model_diff_bounds`:
  `t³ − t + 6 = (t+2)((t−1)² + 2)`, `6 + t − t³ = (2−t)((t+1)² + 2)`); `|A z| ≤ |z₁|(|x| + |y|) + |z₂|`
  (`g_fitA_bound`, triangle inequality `g_euclideanLength_add_le`, `euclideanLength_smul`, `g_vDir_unit`).
  The route does not need `inserted_arc_props` (Unit R).

## Leaves left (2), FALSE as stated in a degenerate case — statement NOT changed (rule 4)

`ξ_strictMonoOn {α' β'} (hα : α ≤ α') (hβ : β' ≤ β) (hθ : ∀ t ∈ Icc α' β', |θrel t| < π/2) : StrictMonoOn ξ (Icc α' t₀)`
and its mirror `ξ_strictAntiOn … : StrictAntiOn ξ (Icc t₀ β')`.

- Proved: the case `α' ≤ β'` (then `hθ α'` gives `θrel α' > −π/2`, and `θrel` is monotone on the arc, so
  `|θrel| < π/2` on all of `[α', t₀]`; mirror with `hθ β'`), and the case `t₀ ≤ α'` (resp. `β' ≤ t₀`), where the
  interval has at most one point. The residual `sorry` is exactly the case **`β' < α' < t₀`** (resp.
  `t₀ < β' < α'`), where `Icc α' β' = ∅`, `hθ` is vacuous, and the conclusion can fail.
- Counterexample (numerically probed): the unit-speed circle `F(t) = (cos 2πt, sin 2πt)` (a `SmoothRegularLoop`
  carrying a crossing-free diagram), `t₀ = 0`, `u = (0, 1)`, `v = (1, 0)`, `θ(t) = 2πt + π/2`, arc `[α, β] = [−0.7, 0.1]`
  (`β − α = 0.8 < 1`, embedded, no double point, `θ` strictly increasing, `T = u` on the arc only at `t = 0`). Then
  `ξ(t) = cos 2πt − 1` and on `[α', t₀] = [−0.7, 0]`: `ξ(−0.7) = −1.309 > ξ(−0.5) = −2.000`, so `ξ` is not strictly
  monotone there; with `β' = −0.8 < α'` all hypotheses hold (`hθ` vacuous). Cause: `θrel` on `[−0.7, −0.5)` lies
  below `−π`, where `ξ' = −|γ'| sin θrel < 0`.
- Missing hypothesis: `α' ≤ β'` (weakest) — or `α' < t₀ < β'` as the neighbouring leaves (`exists_cuts`,
  `exists_disc_in_chart`, `exists_cutFit`) already carry. Every caller in the plan has `t₀ < β'`
  (`exists_chart` supplies `α' < t₀ < β'`), so the fix is harmless. Suggested repair for the assembler (statement
  change, so not done here): add `(hab : α' ≤ β')` to both leaves; the proofs are then the first branch of the
  present bodies verbatim (`g_ξ_strictMonoOn`/`g_ξ_strictAntiOn`). Unit R should call the `g_` forms (or the leaf
  with `t₀ < β'` known) — the leaf as stated is a black box only where `α' ≤ β'` is known.

## Helpers added (31, all `g_`-prefixed, each placed immediately before the first leaf using it)

`g_u_sq`, `g_vDir_eq` (before `det_vDir_u`); `g_hasDerivAt_planeDot`, `g_deriv_eq_smul_T`, `g_planeDot_smul_left`,
`g_u_eq`, `g_T_eq`, `g_planeDot_T_u`, `g_planeDot_T_v` (before `hasDerivAt_η`); `g_exists_hasDerivAt_eq_slope`,
`g_strictMonoOn_of_deriv_pos`, `g_strictAntiOn_of_deriv_neg`, `g_continuous_ξ`, `g_continuous_η`, `g_θrel_t₀`,
`g_ξ_t₀`, `g_η_t₀`, `g_θrel_neg`, `g_θrel_pos`, `g_ξ_strictMonoOn`, `g_ξ_strictAntiOn` (before `ξ_strictMonoOn`);
`g_γ_fract`, `g_ne_p` (before `exists_disc_in_chart`); `g_disc_eq_preimage`, `g_ball_subset_disc` (before
`disc_isDisc`); `g_model_diff_bounds`, `g_euclideanLength_add_le`, `g_vDir_unit`, `g_fitA_bound`, `g_xFit_le`,
`g_yFit_abs_lt` (after `structure CutFit`, before `exists_cutFit`).

## Mathlib / toolchain pitfalls (v4.34.0-rc2, pin 85e3a25e)

- MVT not imported (see above); Rolle `exists_hasDerivAt_eq_zero` is. `Real.pi_gt_three` is not imported either
  (`Real.two_le_pi`, `Real.pi_le_four`, `Real.pi_pos` are); not needed in the end.
- `push_neg` is deprecated (warning "Prefer `push Not`"); avoided with `not_le.mp`/`not_lt.mp`.
  `Set.mem_setOf_eq` is deprecated in favour of `Set.mem_ofPred_eq`.
- Structure-instance notation `{ f₁ := a,` newline `  f₂ := b }` fails with "unexpected identifier; expected '}'"
  unless the continuation line is indented to the column of the first field; positional `⟨…⟩` constructors avoid it
  (used for `CutFit`, 20 fields in declaration order).
- Component derivatives: `(ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hγ` gives
  `HasDerivAt (fun s => (γ s).1) (γ' t).1 t` directly (no `HasDerivAt.fst`).
- `Metric.continuousWithinAt_iff`/`continuousAt_iff` produce `dist`; `Real.dist_eq` then `abs_lt`.
- `IsMinOn` is used via `isMinOn_iff.mp hmin x hx`.
- `Int.fract`: `Int.self_sub_floor` (`a − ⌊a⌋ = fract a`), `Int.fract_eq_fract : fract a = fract b ↔ ∃ z : ℤ, a − b = z`;
  integers strictly between `−1` and `0` are excluded by `exact_mod_cast` + `omega`.
- `SmoothRegularLoop` inherits `SmoothLoop.eq_add_int`, `.continuous`, `.hasDerivAt` by dot notation.
