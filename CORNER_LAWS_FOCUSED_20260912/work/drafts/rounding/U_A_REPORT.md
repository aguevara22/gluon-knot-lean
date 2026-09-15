# U_A_REPORT — Unit A (one junction arc), cf:lem-rounding

File: `work/drafts/rounding/U_A.lean` (copy of Skeleton_FINAL.lean with the Unit A sorries filled).
Check: `cd work/lean && lake env lean ../drafts/rounding/U_A.lean` → **0 errors, 0 non-sorry warnings**
(45 "declaration uses sorry" warnings = other units' leaves and everything downstream of them).
`grep -c sorry`: **54 before → 47 after** (7 leaves). Prefix (lines 1-616) and suffix (from `### Unit G`)
of the file are byte-identical to Skeleton_FINAL.lean; every original declaration is present with its
statement unchanged (checked mechanically, 149 declarations).
`#print axioms` of all seven leaves (in a scratch copy): `[propext, Classical.choice, Quot.sound]` —
no dependence on any other unit's sorry (Unit A uses only the PROVED `smoothTransition_symm` from Unit P).

## Leaves proved (7/7)
| leaf | proof idea |
|---|---|
| `dirOf_injOn_of_lt_pi` | `cos(α−β) = cos²β + sin²β = 1` ⇒ `α − β = 2πn` (`Real.cos_eq_one_iff`); `|2πn| < π` ⇒ `n = 0` |
| `M_pos` | integrand `cos(ϑ(φ−½)) ≥ cos(ϑ/2) > 0` everywhere (`|ϑ(φ−½)| ≤ |ϑ|/2`, `Real.cos_le_cos_of_nonneg_of_le_pi` via `cos_abs`); `intervalIntegral.intervalIntegral_pos_of_pos` |
| `juncLen_pos` | `div_pos` from `M_pos`, `cos(ϑ/2) > 0` |
| `integral_juncDir` | bisector frame `e_w = dirOf(θu+ϑ/2)`, `e_z = (−sin, cos)(θu+ϑ/2)`: `juncDir = cos w • e_w + sin w • e_z`, `w = ϑ(φ−½)`; `∫₀¹ sin w = 0` by the reflection `s ↦ 1−s` (`integral_comp_sub_left` + `smoothTransition_symm`); `u + v = 2cos(ϑ/2) • e_w` |
| `juncArc_mem_disc` | frame coordinates of `γ(s) − q`: `x_w = ℓ F(s) − ε cos(ϑ/2)`, `x_z = ℓ G(s) + ε sin(ϑ/2)` with `F = ∫₀ˢ cos w` strictly increasing from `0` to `M` (`ℓM = 2ε cos(ϑ/2)`) ⇒ `|x_w| ≤ ε cos(ϑ/2)`; `G = ∫₀ˢ sin w` has `ϑ·G ≤ 0` (sign of `w` flips at `s = ½`, `φ(½) = ½`, total `0`) and `|G| ≤ |sin(ϑ/2)|/2` (`|sin w| ≤ |sin(ϑ/2)|`, split at `½`), `ℓ ≤ 2ε` (from `M ≥ cos(ϑ/2)`) ⇒ `|x_z| ≤ ε|sin(ϑ/2)|`; `x_w² + x_z² ≤ ε²` |
| `juncArc_mem_open_disc` | same, `0 < F(s) < M` strictly on `(0,1)` ⇒ strict `x_w` bound |
| `juncArc_injOn` | `planeDot (γ(s) − q) e_w = x_w(s)` and `x_w` strictly increasing (`F` strictly mono, `ℓ > 0`) |

The bisector-frame argument of PLAN_FINAL §3 was used (not the cone/chord fallback). The bounds are
exactly the ones of the numeric probe: `|x_w| ≤ ε cos(ϑ/2)` (strict inside), `|x_z| ≤ ε|sin(ϑ/2)|`, `ℓ ≤ 2ε`.

## Helpers added (27, all `theorem`, prefix `A_`, placed before the first leaf that uses them, inside
`namespace CornerRounding` — Unit A has no `section` of its own). They are NOT marked `private` so that
Units G/X can reuse them (the assembler may add `private` if preferred; nothing outside Unit A uses them yet).

Positivity / bounds of the integrand: `A_abs_arg_le`, `A_cos_half_pos`, `A_cos_half_le`, `A_cos_arg_pos`,
`A_continuous_cos`, `A_continuous_sin`.
Frame algebra: `A_juncDir_eq` (juncDir in the frame), `A_integral_juncDir` (∫₀ˢ juncDir in the frame),
`A_dirOf_add_dirOf` (`u + v = 2cos(ϑ/2)•e_w`), `A_dirOf_frame` (`u = cos(ϑ/2)•e_w − sin(ϑ/2)•e_z`),
`A_euclideanLength_frame` (`‖X•e_w + Z•e_z‖ = √(X²+Z²)`), `A_planeDot_frame` (`⟨X•e_w + Z•e_z, e_w⟩ = X`),
`A_juncArc_sub` (`juncArc s − (A₀ + ε•u)` in the frame — the key identity).
Bisector coordinate: `A_F_strictMono` (`s ↦ ∫₀ˢ cos w` is `StrictMono` on all of ℝ), `A_cos_half_le_M`
(`cos(ϑ/2) ≤ M ϑ`), `A_juncLen_mul_M` (`ℓ·M = 2ε cos(ϑ/2)`), `A_juncLen_le` (`ℓ ≤ 2ε`).
Transverse coordinate: `A_integral_sin_symm` (`∫₀¹ sin w = 0`), `A_smoothTransition_half` (`φ(½) = ½`),
`A_smoothTransition_le_half`, `A_half_le_smoothTransition`, `A_mul_sin_nonneg`, `A_mul_sin_nonpos`
(`ϑ sin(ϑt)` has the sign of `t` for `|t| ≤ ½`), `A_integral_sin_sign` (`ϑ·∫₀ˢ sin w ≤ 0` on `[0,1]`),
`A_abs_sin_arg_le` (`|sin w| ≤ |sin(ϑ/2)|`), `A_integral_sin_bound` (`|∫₀ˢ sin w| ≤ |sin(ϑ/2)|/2` on `[0,1]`),
`A_Z_sq_le` (the `x_z²` bound, pure real arithmetic).

## Mathlib (pin) facts worth knowing for the other units
- `le_or_lt` and `Ne.lt_or_lt` do NOT exist in this pin: use `le_or_gt a b : a ≤ b ∨ b < a` and
  `lt_or_gt_of_ne h : a < b ∨ b < a`.
- `strictMono_of_deriv_pos` / `strictMonoOn_of_deriv_pos` are NOT available with the file's imports (they live
  in `Mathlib.Analysis.Calculus.Deriv.MeanValue`, not imported by the skeleton). I did not add an import;
  strict monotonicity of `∫₀ˢ cos w` is proved from `intervalIntegral.integral_interval_sub_left` +
  `intervalIntegral_pos_of_pos`. Unit P (`smoothTransition_strictMonoOn`) and Unit G3 should plan accordingly
  (or the assembler adds the import once, at the top).
- `Real.cos_abs (x : ℝ) : cos |x| = cos x` — explicit argument (`Real.cos_abs.symm` does not parse).
- `Real.abs_sin_eq_sin_abs_of_abs_le_pi (hx : |x| ≤ π) : |sin x| = sin |x|` exists and is handy.
- `Real.sqrt_le_left (hy : 0 ≤ y) : √x ≤ y ↔ x ≤ y^2`, `Real.sqrt_lt' (hy : 0 < y) : √x < y ↔ x < y^2`,
  `sq_le_sq'`, `sq_lt_sq'` (`-b ≤ a → a ≤ b → a² ≤ b²`), `neg_sq`.
- `intervalIntegral.integral_comp_sub_left (f) (d)` takes `f` EXPLICIT; use it as
  `have := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1) (fun x => …) 1` then `simp only [sub_self, sub_zero] at this`
  (`rw` fails because the lemma's LHS is `f (d − x)` un-beta-reduced).
- `intervalIntegral.integral_mono_on (hab) (hf) (hg) (h)` — the three side conditions are explicit;
  `intervalIntegrable_const (c := …)`, `intervalIntegral.integral_zero`, `intervalIntegral.integral_const_mul`,
  `intervalIntegral.integral_smul_const`, `intervalIntegral.integral_add_adjacent_intervals`,
  `intervalIntegral.norm_integral_le_of_norm_le_const` all as in PLAN_FINAL §5.
- `Continuous.intervalIntegrable` needs `(μ := MeasureTheory.volume)` when the measure is not determined.
- `module` tactic is available (used once, in `A_juncArc_sub`).
- Pitfalls hit: `rw [Real.cos_add]` on a goal containing `cos (θu + ϑ/2 + w)` rewrites `cos (θu + ϑ/2)` first —
  pass the explicit first argument `Real.cos_add (θu + ϑ / 2)`. `abs_of_nonneg (by linarith)` inside `rw`
  unifies with the FIRST `|·|` in the goal — ascribe the type. `(e : T)` ascription does not make a `have`
  display as `T` (a `Continuous ((fun _ => ϑ) * f)` stayed a Pi-product) — use `have h : T := e`.
  `simp`/`norm_num` rewrite `1 / 2` to `2⁻¹` and break syntactic matching with `M`'s integrand — use `simp only`.

## About the statements (nothing false, nothing missing)
- All seven leaves are true as stated and proved without extra hypotheses.
- `h0 : ϑ ≠ 0` is not needed for `juncArc_injOn` (nor, in fact, for the two disc lemmas; it is used only to
  split the sign of `sin(ϑ/2)` in `A_Z_sq_le`). In `juncArc_injOn` the frozen hypothesis is consumed by a
  `have _ := h0` to avoid the unused-variable lint; no statement was changed.
- `M ϑ` is definitionally `∫ s in 0..1, Real.cos (ϑ * (Real.smoothTransition s - 1 / 2))`; every helper spells the
  integrand exactly this way (`1 / 2`), so `M ϑ` unfolds by `rfl`/defeq against `A_F_strictMono`'s function at `1`.
- For Unit X (`doubles_curveMap`, junction–junction within one disc; junction–straight exclusion): the useful
  exports are `A_juncArc_sub` (frame coordinates of the arc about its corner), `A_F_strictMono`,
  `A_planeDot_frame`, `A_euclideanLength_frame`, and the two disc leaves; `juncArc_injOn` is the simple-arc fact.
- For Unit G2 (`integral_tangentField_junction`): `integral_juncDir` is the value; `A_integral_juncDir` gives
  the same integral over `[0, s]` for any `s` (frame form) if a partial-junction integral is needed.
