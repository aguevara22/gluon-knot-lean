# TN_U_D_REPORT.md — Unit D (the model `H = F ∘ Φ₁`) of `TN_Skeleton.lean`

Date: 2026-09-14.  File: `work/drafts/fd/TN_U_D.lean` (1418 lines; skeleton 959).
Check: `cd work/lean && lake env lean ../drafts/fd/TN_U_D.lean` → **0 errors, 0 non-sorry warnings**, ≈ 9 s.
`grep -c sorry`: 42 before → 35 after (33 leaves of units A, B, C, E, F + 2 textual mentions of
`sorryAx` in the module docstring).  Diff against the skeleton (multiset of lines): the only lines
removed are the seven `  sorry` bodies of D1–D7; 466 lines added (14 helpers + 7 proofs); every
definition, statement, name and docstring is byte-identical.  One block was **relocated**, see §3.

## 1. Leaves proved (7/7)

| leaf | name | line | proof idea as implemented |
|---|---|---|---|
| D1 | `hasDerivAt_alphaT_flow` | 797 | product rule in `t` on the explicit `A(t) = (1+t g)(Jw)_θ − (1+t)γ_v(Jw)_u + (1−t)γ_u(Jw)_v` with C4 (`γ̇ = V_t(γ)`, cutoff `= 1` by `cutoff_along`), C9 applied to `w` (`HasDerivAt.clm_apply`), chain rule for `g∘γ`; then `linear_combination hZ + hM + (t·x_θ)·hEV − (t·V_θ)·hEx` with `hZ` = Fact Z (`td_alphaT_Vf_deriv`), `hM` = `moser_identity`, `hEV/hEx` = basis expansion of `Dg` (`td_fderiv_gfun_expand`).  **B3 `dalphaT_eq` is not used**: the antisymmetrised derivative is recovered from the expansion of `Dg` and Fact Z. |
| D2 | `alphaT_flow_one` | 923 | `B(s) = A(s)·exp(−∫₀ˢ μ)` has derivative `0` on `(−1,2)` (D1 + `td_hasDerivAt_integral_muf`), `constant_of_has_deriv_right_zero` on `[0,1]`, `A(0) = α₀(w₀)(w)` by `Phi_zero`, `fderiv_id`, `alphaT_zero`. |
| D3 | `Hmap_eventuallyEq` | 1029 | `⟨round(θ/2π), td_Hmap_eventuallyEq_round …⟩`. |
| D4 | `Hmap_pullback` | 1071 | `td_Hmap_eventuallyEq_round` (value by `eq_of_nhds`, derivative by `EventuallyEq.fderiv_eq`), chain rule `td_hasFDerivAt_chart_Phi`, A7 `pullback_chart`, `← alphaT_one`, D2, unfold `hfun`/`redθ`, `ring`. |
| D5 | `Hmap_injective` | 1083 | `chart_inj` on the images (in the `ρ/4 ≤ 2ρ`-tube by `hδ`), the θ-shift `m` satisfies `|2πm| ≤ 2π + 2 < 4π` (uses `Real.two_le_pi`) so `m ∈ {−1,0,1}` (`omega`); `Phi_shift` moves the shift to the initial point, `Phi_one_inverse` gives injectivity of `Φ₁`, `redθ_spec` finishes with `k = b − a − 1, b − a, b − a + 1`. |
| D6 | `Hmap_immersion` | 1166 | derivative of the local form = `DF ∘ DΦ₁`; `DF` injective by `GoodRadius.chart_bij` (`td_norm_Phi_one`), `DΦ₁` injective by `td_injective_fderiv_Phi_one`. |
| D7 | `Hmap_open_map` | 1183 | `V := H '' (U ∩ solidTorus δ₁)`; openness pointwise: `ContDiffAt.hasStrictFDerivAt` of the local form transported by `HasStrictFDerivAt.congr_of_eventuallyEq`, injective (D6) ⇒ surjective (`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`, `finrank 3 = 3` by `simp`) ⇒ `ContinuousLinearEquiv.ofBijective`, `HasStrictFDerivAt.map_nhds_eq_of_equiv`, `Filter.image_mem_map`. |

Leaves left: **none**.

## 2. Helpers added (prefix `td_`, each immediately before the leaf that first uses it)

Before D1 (line 683): `td_hasDerivAt_fst`, `td_hasDerivAt_snd_coord` (derivatives of the components
`(f s).1`, `(f s).2 i` of a curve in `ℝ × ℝ²`), `td_fderiv_gfun_expand` (`Dg[y] = g_θ y_θ + g_u y_u + g_v y_v`,
no hypotheses), `td_differentiableAt_Vf` (B5 ⇒ `Vf T t` differentiable on the open tube, `|t| < 4`),
`td_alphaT_Vf_deriv` (**Fact Z**: `t Dg[x] V_θ − (1+t) x_v V_u + (1−t) x_u V_v + α_t(q)(DV_t(q) x) = 0`,
proved by the "line trick": the one-variable function `s ↦ α_t(q + s x)(V_t(q + s x))` is eventually `0`
and its explicit product-rule derivative must therefore vanish — no `fderiv` of a composite is ever
computed as a CLM).
Before D2 (line 841): `td_continuousOn_muf` (`s ↦ μ_s(Φ_s p)` continuous on `(−1,2)`, `P, N ≠ 0` from
`GoodRadius` and the a-priori radius), `td_hasDerivAt_integral_muf` (FTC, `intervalIntegral.integral_hasDerivAt_right`).
Before D3 (line 939): `td_redθ_mem4`, `td_redθ_mem2` (`|redθ| ≤ π`), `td_norm_Phi_one` (time-one point in the
`2ρ`-tube), `td_chart_Phi_shift` (`F(Φ₁(θ'+2π, w')) = F(Φ₁(θ', w'))` for `|θ'| ≤ 2π`, `‖w'‖ < δ₁`: C7 + A2),
`td_Hmap_eventuallyEq_round` (**the local form with the explicit `k = round(θ/2π)`**, on the neighbourhood
`|p_θ/2π − θ/2π| < 1/2 ∧ ‖p_w‖ < δ₁`; the two roundings differ by at most one, `round_eq_iff` + `omega`).
Before D4 (line 1047): `td_hasFDerivAt_chart_Phi` (chain rule for `p ↦ F(Φ₁(p_θ − c, p_w))`).
Before D6 (line 1144): `td_injective_fderiv_Phi_one` (`DΨ ∘ DΦ₁ = id` from C5).

D4, D6, D7 use `td_Hmap_eventuallyEq_round` rather than the existential D3: `hfun` is defined with
`redθ θ = θ − 2π·round(θ/2π)`, so the explicit `k` is needed to connect the pullback with `hfun`.

## 3. Structural change the ASSEMBLER must replicate

In the skeleton, LEAF A7 `pullback_chart` (docstring + statement + `sorry`, 6 lines) is declared
**after** LEAF D4 `Hmap_pullback`, which uses it (as TN_PLAN.md prescribes).  Lean cannot reference a
later declaration, so in `TN_U_D.lean` the A7 block was moved, byte-identical, to just before the D4
helpers (now lines 1039–1044).  Any assembled file must place `pullback_chart` (with Unit A's proof)
before `Hmap_pullback`.  Nothing else was reordered.

## 4. Black boxes used (statements only)

A1 `contDiff_chart`, A2 `chart_periodic`, A7 `pullback_chart`; B1 `contDiff_gfun` (and the proved
`contDiff_gu/gv`), B5 `contDiffOn_Vf`; C4 `hasDerivAt_Phi`, C5 `Phi_one_inverse`, C6 through the
hypothesis `hδ : AprioriRadius`, C7 `Phi_shift`, C9 `hasDerivAt_fderiv_Phi`.  Proved skeleton items
used: `moser_identity`, `alphaT_Vf`, `alphaT_zero`, `alphaT_one`, `cutoff_along`, `Phi_zero`,
`contDiff_Phi`, `contDiff_uncurry_Phi`, `GoodRadius.{pos, chart_bij, chart_inj, P_pos, N_pos}`,
`abs_redθ_le`, `redθ_spec`.  Not used: B2, B3, B4, B6, C1–C3, C8, A3–A6.  No leaf needed a
stronger hypothesis; all seven are true as stated.

## 5. Mathlib pitfalls at this pin (v4.34.0-rc2)

- `simpa using` does not unfold `Function.comp`: add `Function.comp_def` when the result is `g ∘ f`.
- `hl.comp_hasDerivAt x hf` with an expected type fails to unify `?l ∘ f` with `fun s => l (f s)`;
  write `have := hl.comp_hasDerivAt x hf; exact this`.
- `HasDerivAt.mul/add/sub/const_mul` produce Pi-algebra lambdas and beta-unreduced `(f + g) t` in the
  derivative; `simp only [Pi.add_apply, Pi.mul_apply]` before `linear_combination`/`ring`.
- `convert h using 1` on a `HasFDerivAt` goal left an instance goal `AddCommGroup (ℝ × ℝ²)` with no
  ext lemma; use `HasFDerivAt.congr_fderiv` + `ContinuousLinearMap.ext fun x => by simp`.
- `Real.pi_gt_three` is not imported here; `Real.two_le_pi`, `Real.pi_le_four`, `Real.pi_pos` are.
- `Set.image_subset` no longer exists (use `Set.image_mono` or a `rintro` proof); `push_neg` is
  deprecated (`not_lt.1` suffices).
- `ContDiffAt.hasStrictFDerivAt` takes `(hn : n ≠ 0)`; `ContinuousLinearEquiv.coe_ofBijective` is not
  `rfl` for the CLM coercion — `rw` it before `HasStrictFDerivAt.map_nhds_eq_of_equiv`.
- `round_eq_iff : round x = n ↔ x ∈ Ico (n − 1/2) (n + 1/2)`; cast `ℤ` bounds with `exact_mod_cast`,
  then `omega` for the three-case split.
- `GoodRadius.P_pos t ht θ w hw` is stated at `(θ, w)`; use it at a point `q` via a type ascription
  `have h : 1/2 < Pf T t q := hρ.P_pos t ht _ _ hq` (structure eta is definitional).
- Avoid `set` for atoms that later enter `ring`/`linear_combination` (let-bound fvars are not
  identified with their values); explicit terms were used throughout.

## 6. Notes for the executor

No numerical constant beyond `2 ≤ π ≤ 4` enters Unit D.  The margins used: `ρ/4 ≤ 2ρ` (time-one
point inside the chart's good tube), `|redθ| ≤ π ≤ 2π` for `Phi_shift`, `|redθ| ≤ π ≤ 4π` for the
a-priori radius, `t ∈ (−1,2) ⊂ [−4,4]` for `P, N` positivity.
