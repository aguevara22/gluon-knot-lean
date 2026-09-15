# GF_U_P1_REPORT.md — unit P1 of `GF_Skeleton.lean` (row 87 fd:generic-front)

Date: 2026-09-14.  File: `work/drafts/fd/GF_U_P1.lean` (1073 lines; skeleton 625).
Check: `cd work/lean && lake env lean ../drafts/fd/GF_U_P1.lean` — **0 errors**, ~8 s.
Warnings: the 22 expected `declaration uses sorry` (other units' leaves and everything downstream
of them) plus ONE linter warning at line 710 (`hHs` not referenced) — that binder is in the FROZEN
statement of P1.2 and is genuinely unnecessary for its proof; silence with `_hHs` at porting time.
`grep -c sorry`: 27 before (26 leaves + the docstring mention at line 15) → 23 after.
`diff GF_Skeleton.lean GF_U_P1.lean | grep '^<'` shows exactly four `  sorry` lines removed; no
definition, structure, statement, name or docstring was touched; helpers were inserted only
immediately before P1.1 and P1.2.

## 1. Leaves

| leaf | name | line | status | axioms |
|---|---|---|---|---|
| P1.1 | `exists_cusp_avoidance` | 560 | PROVED | `[propext, sorryAx, Classical.choice, Quot.sound]` — `sorryAx` ONLY through P0.3 `fderiv_composeFlows_zero` (black box) |
| P1.2 | `noDoubleZero_of_notMem` | 709 | PROVED | `[propext, Classical.choice, Quot.sound]` |
| P1.3 | `finite_cusps_of_stage1` | 741 | PROVED | `[propext, Classical.choice, Quot.sound]` |
| P1.4 | `deriv_y_ne_zero_at_cusp` | 762 | PROVED | `[propext, Classical.choice, Quot.sound]` |

`step1` (proved glue) still type-checks unchanged; its `sorryAx` now comes only from P0.1–P0.3.
Nothing left unproved in this unit; no leaf was false or under-hypothesised.

## 2. What was proved and how (deviation from the printed construction — read this)

**P1.1.** The statement is existential in `(n, Hs, r)`, so the family is my choice.  I did NOT use
the printed per-cusp bumps `H₂ = −½(y−y₀)²`, `H₃ = −⅙(y−y₀)³` with a finite cover of the zero set
(sm-3:2643-2652; the frozen docstring of P1.1 still describes that construction).  Instead: one
cut-off `χ : ContDiffBump (0 : ℝ³)` with `rIn = R`, `rOut = R+1`, where `L(ℝ) ⊆ ball 0 R`
(compactness of `L '' Icc 0 2π` + periodicity), and the TWO Hamiltonians
```
H_a = χ · cos y,   H_b = χ · sin y          (n = 2, Hs = fun i p => χ p * ![cos, sin] i (p 1))
```
Since `χ = 1` on the whole curve, `X_{H_a}(L s)_x = sin(y s)`, `X_{H_b}(L s)_x = −cos(y s)`
everywhere (`gp1_hamVF_zero_bump`).  The columns of `D(cuspMap)` at `(θ, 0)` are
`(gᵢ′(θ), gᵢ″(θ))` with `gᵢ = X_{Hᵢ}(L ·)_x` (`gp1_cuspMap_column`, via P0.3 and the symmetry of
mixed partials), i.e.
```
col_a = (cos y·y′,  −sin y·y′² + cos y·y″),   col_b = (sin y·y′,  cos y·y′² + sin y·y″),
det = y′³ (cos² + sin²) = y′³        for EVERY θ (Wronskian of cos, sin is 1).
```
At a zero of `cuspMap(·, 0)` we have `x′(θ) = 0`, so `y′(θ) ≠ 0` (`gp1_deriv_y_ne_zero`) and the
minor is nonzero.  Radius: the set `W = {minor ≠ 0} ∪ {cuspMap ≠ 0}` is open and contains
`Kper1 × {0}`; `generalized_tube_lemma` gives `u ×ˢ v ⊆ W` with `v ∋ 0` open, `ball 0 ε ⊆ v`,
`r := ε/2`.  Every zero in `Kper1 × closedBall 0 r` then lies in `{minor ≠ 0}`, and a nonzero
`2×2` minor gives `range = ⊤` (`gp1_range_eq_top_of_minor`, Cramer) hence `finrank = 2`
(`rank_eq_iff_range_eq_top`).  No `IsCompact.exists_isMinOn`, no finite subcover, no uniform
continuity.  The plan's probe (iv) (columns `(y′,y″)`, `(0,y′²)`, det `y′³`) is the special case
of the same computation for the printed family; the identity used here is checked symbolically in
the proof (`linear_combination (y′)^3 * cos_sq_add_sin_sq`).

**P1.2.** `coordX (composeFlows n Hs (par a) ∘ L) = xParam L n Hs (par a)` is `rfl`; `xParam` is
`2π`-periodic (from `hL.circle.periodic`), so are its first two derivatives
(`gp1_periodic_deriv`); reduce `θ` by `toIcoMod two_pi_pos 0 θ` (`toIcoMod_mem_Ico`,
`toIcoMod_add_toIcoDiv_zsmul`, `Periodic.sub_zsmul_eq`); the witness in `ℝ^1` is
`θ' • EuclideanSpace.single 0 1` (`(θ' • single 0 1) 0 = θ'` by `simp`).  `hHs` is not needed.

**P1.3.** By contradiction: `Set.Infinite.exists_accPt_of_subset_isCompact` on `Icc 0 2π` gives an
accumulation point `θ`; `x′` continuous ⇒ `θ ∈ cuspSet`; `NoDoubleZero` ⇒ `x″(θ) ≠ 0`;
`HasDerivAt.eventually_ne` ⇒ `x′ ≠ 0` on a punctured neighbourhood; contradiction with
`accPt_iff_frequently` (which yields `∃ᶠ y in 𝓝 θ, y ≠ θ ∧ y ∈ S`; pair with
`eventually_nhdsWithin_iff`).

**P1.4.** `gp1_deriv_y_ne_zero` (needs only `IsEmbeddedCircle` + `IsLegendrian`, not `Stage1`):
`hasDerivAt_coord` gives `deriv (coord i) = (deriv L θ) i`; `alpha` ⇒ `z′ = y x′ = 0`; then all three
coordinates of `deriv L θ` vanish, contradicting `immersion`.

## 3. Helpers added (17, all `gp1_`, all before the first leaf that uses them)

Before P1.1 (lines 294–557):
- `gp1_deriv_y_ne_zero` — P1.4 at the `GenericFrontHyp` level (used by P1.1 and P1.4).
  **Reusable by P3.2 / P5.2** (they need `y′ ≠ 0` at cusps of the current curve).
- `gp1_deriv_partial_eq` — `deriv (fun t => G (a,t)) θ = fderiv ℝ G (a,θ) (0,1)`.
- `gp1_fderiv_partial_eq` — `fderiv ℝ (fun b => G (b,θ)) a v = fderiv ℝ G (a,θ) (v,0)`.
- `gp1_contDiff_partial_deriv` — the `θ`-partial derivative of a jointly `C^∞` `G : A × ℝ → ℝ` is
  jointly `C^∞`.  **Reusable by P3.2** (smoothness of `Cmap`, `Rmap`) and P2.2.
- `gp1_fderiv_fderiv_apply` — `fderiv (fun z => fderiv G z w) z v = fderiv (fderiv G) z v w`.
- `gp1_mixed` — mixed partials commute (`ContDiffAt.isSymmSndFDerivAt` +
  `ContactMotions.minSmoothness_two_le`).
- `gp1_contactMotionsHyp_bump` — `χ · h(y)` satisfies `ContactMotionsHyp` (`ContDiffBump`).
- `gp1_hamVF_zero_bump` — `X_{χ·h(y)}(p)_x = −h′(p 1)` where `χ = 1` nearby.  **Reusable by
  P3.1/P3.2** (it is the `H₂`-type local model in `x`; the same proof pattern —
  `Filter.EventuallyEq.fderiv_eq` from `χ.one_of_mem_closedBall` — gives the `H^x`, `H^z` models).
- `gp1_range_eq_top_of_minor`, `gp1_finrank_eq_two_of_minor` — nonzero `2×2` minor ⇒ onto ⇒
  `finrank = 2`.  (P3.2 needs `3×3`, `4×4` analogues; same Cramer pattern, or block-triangular.)
- `gp1_isCompact_Kper1` — `Kper1 = (θ ↦ θ • single 0 1) '' Icc 0 2π`.  **Reusable** pattern for
  `K2 δc`, `K3 δc`.
- `gp1_fderiv_apply_coord2` — `fderiv f p v i = fderiv (fun q => f q i) p v` for `f : X → ℝ^2`.
- `gp1_contDiff_xJoint` — `(a, θ) ↦ x_a(θ)` is `C^∞` on `ℝ^n × ℝ` (row 86 `compositions_smooth`).
- `gp1_fderiv_xJoint_zero` — P0.3 transported to `ℝ^n` (via `EuclideanSpace.equiv`), coordinate 0.
- `gp1_contDiff_cuspMap` — `cuspMap L n Hs` is `C^∞` for ANY admissible family.  **Reusable by P2.2**
  (its `NoDoubleZero` stability needs exactly this joint smoothness).
- `gp1_cuspMap_column` — the two entries of the parameter-`i` column of `D(cuspMap)` at `(t, 0)`:
  `deriv gᵢ (t 0)` and `deriv (deriv gᵢ) (t 0)`, `gᵢ s = hamVF (Hs i) (L s) 0`; generic in `n, Hs`.

Before P1.2 (line 702): `gp1_periodic_deriv` — `Periodic f c → Periodic (deriv f) c`
(Mathlib has no `Function.Periodic.deriv`; `deriv_comp_add_const` does it).  **Reusable by P3.3/P3.4**
(periodicity of `x_a′`).

## 4. Mathlib pitfalls met (this pin, Lean v4.34.0-rc2)

- `ContDiff.differentiable` wants `n ≠ 0`, `ContDiff.fderiv_right` wants `m + 1 ≤ n`,
  `ContDiff.continuous_fderiv` wants `n ≠ 0`: pass `(by simp)`, NOT `le_top`.
  `contDiff_infty_iff_deriv : ContDiff 𝕜 ∞ f ↔ Differentiable 𝕜 f ∧ ContDiff 𝕜 ∞ (deriv f)`.
- `WithLp` is a structure: `p i` elaborates to `p.ofLp i`; `!₂[a, b] 0 = a` by `simp`;
  `!₂[a,b] = 0` is destructured with `congrFun (congrArg WithLp.ofLp h) 0`; `EuclideanSpace.single_apply`
  is deprecated (use `PiLp.single_apply`); `(fun i => a i) = EuclideanSpace.equiv (Fin n) ℝ a` is
  `rfl` (this is how `par` is handled); `par 0 = 0` needs `funext; simp [par]`.
- `PiLp.proj 2 (fun _ : Fin k => ℝ) i` MUST carry the ascription `(… : ℝ^k →L[ℝ] ℝ)`; and
  `(proj).hasFDerivAt.comp` / `(proj).contDiff` do not unify against a lambda `fun q => f q i`
  when given an expected type — elaborate first (`have h := …`) then `rw [h.fderiv]; rfl` or
  `exact h`.  `EuclideanSpace.proj i` has the same issue (its type is `StrongDual`).
- Converting `HasFDerivAt` (composition with `inr`) to a statement about `deriv`: `simpa using
  h.hasDerivAt` fails on the `ℝ` instance diamond (`RCLike.toInnerProductSpaceReal.toModule` vs
  `Semiring.toModule`, from the `InnerProductSpace` import).  Use `show fderiv ℝ f θ 1 = _`
  (`deriv f θ = fderiv ℝ f θ 1` is `rfl`), `rw [h.fderiv]; rfl`.
- `HasDerivAt.deriv` after `.comp`/`.mul`/`.neg` produces `Function.comp` / `Pi.mul` forms that `rw`
  will not match against `fun s => …`; give the `HasDerivAt` an explicit lambda type first
  (see `d11`, `d02`, `d12` in P1.1).
- `fin_cases k` leaves `⟨0, ⋯⟩` and `↑T`; `show … 0 = …` restates them; `field_simp` did not see
  the reordered denominator — `rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hm]; ring`
  works.  `div_add_div_same` is gone (use `← add_div`).
- Missing in Mathlib: `Function.Periodic.deriv`, `HasFDerivAt.comp_of_eq` (used
  `ContinuousLinearEquiv.comp_right_fderiv` + `map_zero`), `ContinuousLinearMap.mem_range`
  (use `LinearMap.range_eq_top`), `fderiv_deriv`.
- `push_neg` is deprecated in this pin (`simp only [not_or, not_not]`).
- `accPt_iff_frequently` is `∃ᶠ y in 𝓝 x, y ≠ x ∧ y ∈ C` (not `𝓝[≠]`); `HasDerivAt.eventually_ne`
  has an arbitrary constant `c` in `f z ≠ c`.
- `set F := cuspMap L 2 Hs` breaks later `rw` with lemmas stated in terms of `cuspMap`; I kept
  `cuspMap L 2 Hs` verbatim throughout P1.1.

## 5. For the assembler / executor

- P1.1 consumes P0.3 EXACTLY as stated (`fun a : Fin n → ℝ => composeFlows n Hs a p`, direction
  `Pi.single i 1`, at `0`).  If the P0 prover keeps the statement, nothing here changes.
- The frozen docstring of P1.1 describes the printed `H₂, H₃` family; the proof uses the
  `χ cos y, χ sin y` family with `n = 2`.  Both give `ParameterAvoidanceHyp 1 n 2 …`; the theorem
  statement is unaffected.  If a docstring/proof match is wanted at porting time, adjust the
  docstring (statement text untouched here by rule).
- `gp1_deriv_y_ne_zero` should be preferred over P1.4 by P3.2 and P5.2 when only
  `GenericFrontHyp`/`Stage1.circle+legendrian` are at hand.
- Size: unit P1 is ~450 added lines (plan estimated 800); P1.1 itself is 140 lines plus ~260 of
  helpers.
