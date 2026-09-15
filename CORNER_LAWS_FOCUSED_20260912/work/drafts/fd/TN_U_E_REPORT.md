# TN_U_E_REPORT.md — Unit E (Legendrian knot, annulus, pushoff) of `TN_Skeleton.lean`

Date: 2026-09-14.  File: `work/drafts/fd/TN_U_E.lean` (copy of `TN_Skeleton.lean` with the seven
Unit E leaves proved).  Compile: `cd work/lean && lake env lean ../drafts/fd/TN_U_E.lean` → **0 errors**,
about 8 s (the imports are prebuilt).  `grep -c sorry`: **42 before → 35 after** (33 leaves of units
A–D, F + the 2 mentions of the word in the module docstring, lines 16 and 18).
`diff TN_Skeleton.lean TN_U_E.lean | grep '^<'` shows exactly the seven `  sorry` lines: no
statement, definition, name or docstring was changed; everything else is additions.

## Leaves proved (7/7)

| leaf | name | proof in one line |
|---|---|---|
| E1 | `exists_N_b` | `exists_nat_gt (1/δ²)`, `b := 1/√N`; `Real.lt_sqrt`, `div_lt_iff₀`, `Real.sq_sqrt`, `field_simp` |
| E2 | `norm_helix` | `EuclideanSpace.norm_eq`, `Fin.sum_univ_two`, `Real.sqrt_sq_eq_abs`, `cos² + sin² = 1` |
| E3 | `alpha0_helix` | special case `Nb² = 1` of the helper `te_alpha0_helix : α₀(1, v_r′) = 1 − N r²` |
| E4 | `legendrian_L` | `te_alpha_curve` (`α(L′) = h·(1 − N b²)`) with `c = 0`, then `hb` |
| E5 | `embedded_L` | `te_embedded_curve` with `c = 0` (`simpa` removes the `θ + 0`) |
| E6 | `pushoffAnnulus` | nine fields; chain rule `D(H∘B) = DH·DB`, `DB` explicit (`te_fderiv_annulus0_apply`), kernel of `DB` trivial, `B^*α₀(0,1) = κ`, positivity from `te_circle` |
| E7 | `transverselyIsotopic_pushoff` | family `F s θ = H(B(θ, s₀ + s(b − s₀)))`, reparametrization `ρ θ = θ + κ b`; each circle by `te_circle`; `F 1 = T ∘ ρ` via `helix N 0 θ = 0` and `hm.core` |

`#print axioms` of all seven leaves and of the assembled `exists_legendrian`:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

Unused-hypothesis warnings (statements are frozen, so left as is): `hN : 0 < N` in `embedded_L`
(the curve is embedded for every `N`, since its θ-coordinate has degree one) and `hκ : κ ≠ 0` in
`transverselyIsotopic_pushoff` (the isotopy works for every `κ`; `κ ≠ 0` is only needed for the
`transverse` field of E6).  These are the only non-`sorry` warnings in the file.

## Helpers added (prefix `te_`, each placed immediately before the first leaf that uses it)

Before E2: `te_norm_helix`.
Before E3: `te_hasDerivAt_toLp2` (derivative of `θ ↦ !₂[f θ, g θ]` from the coordinates, via
`hasDerivAt_pi` and the CLE `PiLp.continuousLinearEquiv 2 ℝ _`), `te_hasDerivAt_helix`
(`v_r′ = −rN(sin Nθ, cos Nθ)`), `te_alpha0_helix` (`α₀(v_r)(1, v_r′) = 1 − N r²`).
Before E4: `te_helix_periodic`, `te_contDiff_helix`, `te_mem_ball` (`‖v_r‖ = |r| < δ`),
`te_mem_solidTorus`, `te_isOpen_solidTorus`, `te_contDiffAt_H` (from `hm.smooth` on the open torus),
`te_hasFDerivAt_H`, `te_hasDerivAt_curve` (`d/dθ H(θ + c, v_r θ) = DH·(1, v_r′)`),
`te_alpha_curve` (`α = h·(1 − N r²)` along that circle, for any `|r| < δ`, any shift `c`).
Before E5: `te_embedded_curve` (`θ ↦ H(θ + c, v_r θ)` is an embedded circle for `|r| < δ`).
Before E6: `te_hasFDerivAt_toLp2`, `te_toLp2_apply` (Fréchet version of the `!₂` derivative and
its evaluation), `te_contDiff_annulus0`, `te_hasFDerivAt_annulus0` (existence of `DB` with its
values, stated as `∃ L, HasFDerivAt B L q ∧ ∀ v, L v = …` to avoid writing the CLM),
`te_differentiableAt_annulus0`, `te_fderiv_annulus0_apply`
(`DB(θ,s)(τ,σ) = (τ + κσ, !₂[−(b−s)N sin·τ − cos·σ, −(b−s)N cos·τ + sin·σ])`),
`te_injective_fderiv_annulus0` (kernel trivial for every `s`, via `injective_iff_map_eq_zero` and
`linear_combination (−cos)·A + sin·B − σ·(cos² + sin² − 1)`), `te_circle` (the circles
`H∘B(·,σ)`, `0 < σ ≤ b`, are embedded and positive transverse: `α = h(1 − N(b−σ)²)`,
`(b−σ)² < b²` by `pow_lt_pow_left₀`, `N b² = 1`).
Before E7: `te_helix_zero`.

No new `def`s; no changes outside Unit E's section.

## Mathematics as formalised

- `α₀(v_r)(1, v_r′) = 1 + u v′ − v u′ = 1 − N r²(cos² + sin²)` with `u = r cos Nθ`, `v = −r sin Nθ`.
- `B^*α₀ = (1 − N(b−s)²) dθ + κ ds`: the `dθ` part is `te_alpha_curve` with `r = b − s`, `c = κ s`;
  the `ds` part is the `transverse` field: `α₀(v_{b−s})(κ, (−cos, sin)) = κ + (b−s)cos sin − (b−s) sin cos = κ`.
- Immersion of `B` at every `s` (including `s = b`, as the paper remarks): the radial and angular
  parts of `DB` are orthogonal, so `DB(τ,σ) = 0 ⇒ σ = 0 ⇒ τ = 0`.
- E7 positivity at `s = 1` (the TN_PLAN.md remark): `annulus0(θ, b) = (θ + κ b, 0)` and the
  general formula `α = h(1 − N(b−σ)²)` gives `h > 0` at `σ = b`; `IsPositiveTransverse T` is NOT
  needed (`te_circle` only uses `hm`).  The plan's concern is resolved as it predicted.

## Mathlib pitfalls (this pin)

- `!₂[a, b]` is `WithLp.toLp 2 ![a, b]`; `WithLp` is a structure now, `(!₂[a,b]) 0 = a` by `simp`.
  `contDiff_euclidean` is stated with `(f x).ofLp i`; `fin_cases i <;> simp <;> fun_prop` works
  (`Real.contDiff_cos/sin` are `fun_prop`-registered).
- There is no `hasDerivAt_euclidean`; go through `hasDerivAt_pi` / `hasFDerivAt_pi'` on
  `Fin 2 → ℝ` and compose with `(PiLp.continuousLinearEquiv 2 ℝ (fun _ => ℝ)).symm.toContinuousLinearMap`
  (`te_hasDerivAt_toLp2`, `te_hasFDerivAt_toLp2`).  Evaluating that CLM: `ext i; fin_cases i <;> rfl`.
- `ContDiffAt.differentiableAt` now takes `n ≠ 0` (not `1 ≤ n`); `by simp` proves `∞ ≠ 0`.
- `convert … using 1` on `HasDerivAt` after `HasDerivAt.const_mul` produces spurious instance
  goals (`instAddCommGroup = normedCommRing.toAddCommGroup`); use `HasDerivAt.congr_deriv (by ring)`.
- `hasFDerivAt_fst/snd` need a type ascription before `.const_mul`/`.const_sub`
  (`have hsnd : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) q := hasFDerivAt_snd`).
- `ContinuousLinearMap.coe_comp'` is deprecated → `coe_comp`.
- `Real.cos_add_nat_mul_two_pi : cos (x + n * (2π)) = cos x` (with `mul_add` for `N(θ + 2π)`).
- `pow_lt_pow_left₀ (h : a < b) (ha : 0 ≤ a) (hn : n ≠ 0)`.
- `∀ {s}, … → …` hypotheses proved by `fun {s} hs => …` (the implicit binder must be named).

## For the assembler / executor

- Unit E depends only on the statement structures and `hm : IsTransverseModel T δ H h`; nothing
  from units A–D or F is used, so the block (helpers + leaves, lines 776-1148 of `TN_U_E.lean`) can
  be pasted into the assembled file as is.
- `mem_L` (already proved in the skeleton) still uses the leaf name `norm_helix`; unchanged.
- `exists_legendrian` (assembly) now has no `sorryAx` in its axioms.
