# U_CIRCLE_REPORT — unit CIRCLE (U0), leaf `u_circle : U_circle`

Prover unit of PLAN_FINAL §6 row U0, 2026-09-15.  File: `work/drafts/contact/U_CIRCLE.lean`
(= `Skeleton_FINAL.lean` with the `sorry` of `u_circle` replaced; helper prefix `uc_`).

Check: `cd work/lean && lake env lean ../drafts/contact/U_CIRCLE.lean` — **0 errors**, 10 warnings
"declaration uses `sorry`" (lines 633-651 = the ten other units' leaves `u_sl_radius` … `u_family`).
`grep -c sorry`: 12 before → 11 after (the 11 = 10 remaining leaves + the docstring mention on line 19).
`diff Skeleton_FINAL.lean U_CIRCLE.lean` is one hunk `551,552c551,632`: the two lines
`theorem u_circle : U_circle := by / sorry` became the helper block + the proof.  No definition,
structure, axiom, statement, name or docstring of the skeleton was touched.

`#print axioms SM.u_circle` (on a scratch copy of the full file): `[propext, Classical.choice, Quot.sound]`.

## 1. Leaves

| leaf | status |
|---|---|
| `u_circle : U_circle` (`∀ K : TransverseKnot, TransverseNeighborhoodHyp K.circle`) | **PROVED** |

No leaf of this unit is left; none is false or under-hypothesized.

## 2. Helpers added (all immediately before `u_circle` in §5.4, lines 551-629)

| name | statement | proof idea |
|---|---|---|
| `uc_toE3L : Space →L[ℝ] E3` | `toE3` packaged as a continuous linear map (`LinearMap.toContinuousLinearMap` of the obvious `LinearMap`; `map_add'`/`map_smul'` by `ext i; fin_cases i <;> rfl`) | needed for the chain rule; `toE3` in the skeleton is a plain function |
| `uc_toE3L_apply : uc_toE3L p = toE3 p` | `rfl` | |
| `uc_smooth K : ContDiff ℝ ∞ K.circle` | `contDiff_toE3.comp (K.smooth.comp (contDiff_id.div_const _))` (exactly the plan's term; `K.circle` unfolds by defeq) | |
| `uc_periodic K : Periodic K.circle (2 * π)` | `(θ + 2π)/(2π) = θ/(2π) + 1` (`add_div`, `div_self`), then `K.periodic` | |
| `uc_injective K θ θ' : K.circle θ = K.circle θ' → ∃ k : ℤ, θ' = θ + 2π k` | `congrArg toSpace` + `toSpace_toE3` gives `K.T (θ/2π) = K.T (θ'/2π)`; `K.embedded` gives `SameT`, i.e. `θ'/2π = θ/2π + n`; clear the denominator (`div_eq_iff`, `div_mul_cancel₀`, `ring`) | |
| `uc_hasDerivAt_circle K θ : HasDerivAt K.circle ((1/(2π)) • toE3 (deriv K.T (θ/(2π)))) θ` | `(hasDerivAt_id' θ).div_const`, `K.smooth.differentiable`, `HasDerivAt.scomp`, then `uc_toE3L.hasFDerivAt.comp_hasDerivAt` and `map_smul` | the plan's chain rule `deriv (toE3 ∘ K.T ∘ (·/2π)) = (1/2π) • toE3 (deriv K.T)` |
| `uc_deriv_circle K θ : deriv K.circle θ = (1/(2π)) • toE3 (deriv K.T (θ/(2π)))` | `.deriv` of the above | |
| `uc_alpha_circle K θ : alpha (K.circle θ) (deriv K.circle θ) = (1/(2π)) * (deriv (zOf K.T) (θ/2π) - yOf K.T (θ/2π) * deriv (xOf K.T) (θ/2π))` | `uc_deriv_circle`, `K.deriv_T`, `simp only [alpha, PiLp.smul_apply, toE3_apply0/1/2, yOf_def]`, `ring` | |
| `uc_transverse K : IsPositiveTransverse K.circle` | `uc_alpha_circle`, `mul_pos (positivity) (K.positive _)` | |
| `uc_immersion K θ : deriv K.circle θ ≠ 0` | a zero velocity gives `alpha _ 0 = 0`, contradicting `uc_transverse` (so the immersion clause is a corollary of positivity, as `TransverseKnot.deriv_T_ne_zero` already is on the `Space` side) | |

`u_circle` itself: `fun K => ⟨⟨uc_smooth K, uc_periodic K, uc_injective K, uc_immersion K⟩, uc_transverse K⟩`.
Total ≈ 80 lines (the plan estimated 150).

## 3. Mathlib notes / pitfalls

* `toE3` is a plain function in the skeleton (frozen), so the chain rule through it needs a linear-map
  wrapper; `LinearMap.toContinuousLinearMap` (finite-dimensional domain) gives a `ContinuousLinearMap` whose
  coercion is definitionally `toE3` (`uc_toE3L_apply` is `rfl`), and `ContinuousLinearMap.hasFDerivAt.comp_hasDerivAt`
  does the composition.  `map_smul` rewrites `uc_toE3L (c • v)` to `c • uc_toE3L v`.
* `HasDerivAt.scomp θ (hg : HasDerivAt g g' (h θ)) (hh : HasDerivAt h h' θ) : HasDerivAt (g ∘ h) (h' • g') θ` is
  the right chain-rule lemma for a vector-valued outer function on a scalar inner one (`HasDerivAt.comp` wants a
  scalar outer function).
* `PiLp.smul_apply` + `smul_eq_mul` turn `((c • v) : E3) i` into `c * v i`; the coordinate lemmas
  `toE3_apply0/1/2` of the skeleton are `rfl` and fire under `simp only`.
* `positivity` proves `0 < 1 / (2 * π)` and `2 * π ≠ 0` directly (it knows `Real.pi_pos`).
* `IsEmbeddedCircle.injective` wants `∃ k : ℤ, θ' = θ + 2 * π * k` (period as a real multiplier), while
  `SameT` gives `θ'/(2π) = θ/(2π) + n`; `div_eq_iff` + `add_mul` + `div_mul_cancel₀` + `ring` clears it
  (`linear_combination` alone would not, since `ring` cannot cancel `(2π) * (2π)⁻¹`).
* The compile of the whole file is fast here (~9 s wall) because all imports are prebuilt.

## 4. For the assembler / executor

* Nothing in this unit depends on any other unit's leaf; `u_circle` uses only the skeleton's §0 definitions
  (`toE3`, `toSpace_toE3`, `toE3_apply*`, `contDiff_toE3`, `TransverseKnot.circle`) and the accepted rows
  (`TransverseKnot.{smooth, periodic, embedded, positive, deriv_T}`, `SM.TransverseNeighborhood.alpha`,
  `IsEmbeddedCircle`, `IsPositiveTransverse`, `TransverseNeighborhoodHyp`).  Axiom footprint standard.
* The helper block is self-contained and can be lifted verbatim into `SM/FdContactUnits*.lean` (or wherever
  U0 lands); the only names it introduces are the ten `uc_*` declarations of §2.
* `uc_deriv_circle` / `uc_alpha_circle` may be useful to U6 (`Ψ 1 ∘ L = K.circle` bridging) and to anyone
  needing the velocity of `K.circle` in `E3` coordinates; they are stated for every `θ`, not only on a period.
