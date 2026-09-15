# GF_U_P5_REPORT.md — unit P5 (exact cusp germs) of `GF_Skeleton.lean`

Date: 2026-09-14.  File: `work/drafts/fd/GF_U_P5.lean` (3107 lines; skeleton 625).
Check: `cd work/lean && lake env lean ../drafts/fd/GF_U_P5.lean` — **0 errors**, 19 warnings
`declaration uses sorry` (exactly the 19 leaves of units P0–P4, P6), one linter warning on the frozen
statement of `exactGerm_of_cuspFlow` (unused hypothesis `hf'`, see below).  `grep -c sorry`: 27
(skeleton) → 20 (19 other-unit leaves + the docstring mention on line 15).  ~8 s with a warm cache.

## 1. Leaves: 7 of 7 proved

| leaf | status | depends on (black boxes) | `#print axioms` |
|---|---|---|---|
| P5.1 `hamFlow_of_y_only` | proved | row 86 only | propext, Classical.choice, Quot.sound |
| P5.2 `exists_local_graph` | proved | P1.4 `deriv_y_ne_zero_at_cusp` | + sorryAx (through P1.4) |
| P5.3 `exactGerm_of_cuspFlow` | proved | P1.4 | + sorryAx (through P1.4) |
| P5.4 `exists_small_cusp_hamiltonian` | proved | none | propext, Classical.choice, Quot.sound |
| P5.5 `flow_C2_close` | proved (`C₀ = 100`) | row 86 (`contDiff_uncurry`) | propext, Classical.choice, Quot.sound |
| P5.6 `stage3_stable` | proved | P1.3, P1.4, `step3` (P4.1, P4.2) | + sorryAx |
| P5.7 `exists_germ_isotopy` | proved | P0.1, P1.3, P5.1–P5.6, row 86 `fd_contact_motions.diffeo` | + sorryAx |

No leaf was false as stated; no hypothesis needed changing.  Statements, names and docstrings are
byte-identical to the skeleton (checked mechanically: all 77 declaration headers and all 26 leaf
docstrings of `GF_Skeleton.lean` occur verbatim in this file).

## 2. ONE HEADER CHANGE — the assembler must keep it

```
import Mathlib.Analysis.Calculus.ContDiff.Bounds
```
added as the 5th import (after `SmoothTransition`, before `SM.ContactMotions`).  Reason: the Leibniz
rule `norm_iteratedFDeriv_mul_le`, `norm_iteratedFDeriv_clm_apply_const` and
`ContinuousLinearMap.norm_iteratedFDeriv_comp_left` live in that module, which is **not** in the
import closure of the six skeleton imports, and P5.4 cannot be done without a Leibniz rule.  The
import is cheap (cached olean) and adds only lemma names.  Nothing else in the header changed.

## 3. Helpers added (74, all `gp5_`-prefixed, each immediately before the leaf that first uses it)

Before P5.1: `gp5_hasDerivAt_toLp`, `gp5_hasFDerivAt_y_only`, `gp5_pd_y_only`, `gp5_hamVF_y_only`,
`gp5_isGlobalFlow_cuspFlowMap`, `gp5_exists_lipschitz_hamVF_y_only`.

Before P5.4: `gp5_bump1`, `gp5_bump`, `gp5_bump_contDiff`, `gp5_bump_one`, `gp5_bump_zero`,
`gp5_bump_support`, `gp5_bump_tsupport`, `gp5_bump_hasCompactSupport`, `gp5_bump_bound`,
`gp5_mvt_step`, `gp5_cutoff_bound`, `gp5_hamVF_eq`, `gp5_norm_iteratedFDeriv_hamVF_le`.

Before P5.5: `gp5_exp_le_four`, `gp5_exp_sub_one_le`, `gp5_gronwallBound_le`,
`gp5_hasDerivAt_fderiv_of_time_deriv` (the abstract "∂_s D_p = D_p ∂_s" lemma from
`isSymmSndFDerivAt`), `gp5_hasDerivAt_fderiv_flow`, `gp5_hasDerivAt_fderiv2_flow`.

Before P5.6: `gp5_reduce`, `gp5_periodic_deriv`, `gp5_periodic_int`, `gp5_bounded_of_periodic`,
`gp5_finset_min`, `gp5_sameParam_shift`, `gp5_circDist_shift`, `gp5_circDist_eq_abs`,
`gp5_circDist_bounds`, `gp5_curve_close`, `gp5_C0_close`, `gp5_fderiv_injective`,
`gp5_coord_deriv`, `gp5_cusp_arc_injective_pos`, `gp5_cusp_arc_injective`, `gp5_circDist_le_abs`,
`gp5_circDist_shift_left`, `gp5_not_sameParam_of_bounds`, `gp5_front_sub_norm_le`,
`gp5_front_comp_close`, `gp5_front_periodic`, `gp5_continuous_front`, `gp5_exists_rc`,
`gp5_cusp_margin`, `gp5_triple_margin`, `gp5_cusp_reduce`, `gp5_eventuallyEq_of_far`,
`gp5_deriv_eq_of_eventuallyEq`, `gp5_sign_transfer`, `gp5_exists_arc`, `gp5_new_collar`,
`gp5_new_noCuspOnBranch`, `gp5_new_noTriple`, `gp5_new_noDoubleZero_cuspSet`, `gp5_new_embedded`.

Before P5.7: `gp5_taylor4`, `gp5_cuspHam_props`, `gp5_norm_le_sum_abs`, `gp5_cuspFlow_small`,
`gp5_hamVF_congr`, `gp5_flow_eq_cuspFlow`, `gp5_hamVF_sum`, `gp5_sum_bound`,
`gp5_tsupport_sum_subset`, `gp5_hamVF_eq_zero_of_notMem`, `gp5_hamFlow_fixed`, `gp5_germ_shift`,
`gp5_deriv_x_zero_of_germ`, `gp5_pairwise_dist`.

## 4. Routes actually taken (where they differ from GF_PLAN.md)

* **P5.1** as planned: `X_{ψ(y)} = F ∘ π₁` with `F : ℝ → ℝ³` compactly supported `C¹`, hence Lipschitz
  (`exists_lipschitzWith_of_hasCompactSupport'` from row 86 §9 with `E = ℝ`); explicit flow is a
  global flow; `Classical.epsilon_spec` + `IsGlobalFlow.unique`.
* **P5.2**: 1-D IFT via `HasStrictDerivAt.hasStrictFDerivAt_equiv` →
  `HasStrictFDerivAt.toOpenPartialHomeomorph`, restricted (`restrOpen`) to `{y′ ≠ 0}`, inverse smooth
  on the open target by `OpenPartialHomeomorph.contDiffAt_symm_deriv` at every target point (a single
  `ContDiffAt ∞` does **not** give `ContDiffOn` on a neighbourhood — this is why the restriction to
  the open set where `y′ ≠ 0` is needed); global `f = b · (x ∘ Q.symm)` with a `ContDiffBump` whose
  `tsupport` lies inside the target.  `f′(y₀) = 0` and `f″(y₀) = x″/y′² ≠ 0` from the chain rule on
  the eventual identity `x = f ∘ y`.
* **P5.3**: `x`-identity by FTC (`intervalIntegral.integral_hasDerivAt_right`); `z`-identity by
  constancy of `G := z̃ − (A y₀ u² + ⅔ A u³)` on a ball (`IsOpen.is_const_of_deriv_eq_zero`), the
  derivative computed with `HasDerivAt` chains and closed by `ring` after `z′ = y x′` and
  `x′ = f′(y) y′`.  The frozen hypothesis `hf'` is not needed (the proof starts with `clear hf'`).
* **P5.4**: bump `b_ε(p) = b₁((2/ε)(p − pc))` with `b₁ = ContDiffBump ⟨1,2⟩`; derivative bounds by
  `iteratedFDeriv_comp_add_left` + `ContinuousLinearMap.iteratedFDeriv_comp_right`; Taylor by four
  MVT steps (`gp5_mvt_step`, `Convex.norm_image_sub_le_of_norm_deriv_le` on `uIcc`); Leibniz
  (`norm_iteratedFDeriv_mul_le`).  Instead of bounding `y ∂ᵢH` by Leibniz with the linear factor
  `y`, `X_H` is rewritten through `H` and `yH := y·H`: `X_H = (−∂₁H) e₀ + (∂₀H + ∂₂(yH)) e₁ +
  (2H − ∂₁(yH)) e₂` (`gp5_hamVF_eq`), and the same cutoff bound (`gp5_cutoff_bound`) is applied to
  `χ = ψ` and `χ = y ψ(y)`, both vanishing to order 3 at `y₀`.  Output `ε = min ε₀ 1 (η/K)`.
* **P5.5**: Grönwall twice (`norm_le_gronwallBound_of_norm_deriv_right_le`, `δ = 0`, `K = η`).
  The operator-valued variational equations come from one abstract lemma
  `gp5_hasDerivAt_fderiv_of_time_deriv` (applied to `φ`, then to `D_pφ`); the second one is evaluated
  with `HasFDerivAt.clm_comp`.  `e^η − 1 ≤ 4η` is proved elementarily (`Real.exp_one_lt_d9` is not in
  the import closure).  `C₀ = 100`.
* **P5.6**: no Lebesgue number.  With `S` the finite cusp set in `[0,2π)`: arcs `Icc (θc − 2ρ) (θc + 2ρ)`
  on which `x″`, `y′` keep their sign with margin (continuity at `θc`); `rc` such that
  `dist (L θ) (L θc) ≤ rc ⇒ |θ − 2πk − θc| < ρ` (`gp5_exists_rc`, compactness of the far interval +
  injectivity mod `2π`); `η` so small that `x̃″`, `ỹ′` keep the signs (`gp5_curve_close`: `‖L̃′ − L′‖ ≤
  η‖L′‖`, `‖L̃″ − L″‖ ≤ η(‖L′‖² + ‖L″‖)`), that `2η <` the `NoCuspOnBranch` margin on
  `[θc + δ′, θc + 2π − δ′]`, that `4η <` the `NoTriple` margin on the compact triple set with
  pairwise differences in `[δ′, 2π − δ′]`, and `η < 1` (so `DΨ` is injective).  Collar of the new
  curve of width `δ′ = min δc ρ` (`gp5_new_collar`): close pairs with a moved point lie in one arc
  where the front is injective (`gp5_cusp_arc_injective`: the P2.1 integration-by-parts argument
  `z(θ₂) − z(θ₁) = ∫ y′ (X − x) ≠ 0`, all four sign cases via `(±x, ±y, ±z)`), pairs of fixed points
  use the old collar.  `NoDoubleZero` and `cuspSet` by the two regimes (in an arc / `Ψ = id` near
  the point, `Filter.EventuallyEq.deriv`).  `Stage3` then via `step3` (P4.1/P4.2 black boxes).
* **P5.7**: **one summed Hamiltonian** `H = Σ_{θc ∈ S} H_θc` with pairwise disjoint supports
  (`ε_θc ≤ d/3`, `d` = min distance of distinct cusp points), so `Φ = hamIsotopy 1 (fun _ => H)
  (fun _ => 1)` (P0.1 with `n = 1`), `Φ 1 = hamFlow H 1`, and **no composition estimates** are needed:
  `X_H = Σ X_{H_θc}` (`gp5_hamVF_sum`) and at every point at most one summand is nonzero
  (`gp5_sum_bound`), so the `C²` bound of P5.4 passes to `X_H` and P5.5 gives `‖D^k(Φ 1 − id)‖ ≤ C₀η′
  ≤ η`.  The germ: on the inner ball `H = ψ(y)`; the explicit trajectory `cuspFlowMap ψ s q` starting
  in `ball pc (ε/4)` moves less than `ε/8` (Taylor `|ψ| ≤ M u⁴`, `|ψ′| ≤ M u³`, `ε ≤ 1/((3+|y₀|)M+1)`,
  `gp5_cuspFlow_small`), hence stays where `H = ψ(y)`, hence solves the `X_H`-ODE, hence equals the
  flow by uniqueness (`dist_le_of_trajectories_ODE`, `gp5_flow_eq_cuspFlow`); P5.3 gives the germ,
  `gp5_deriv_x_zero_of_germ` the hypothesis `x̃′(θc) = 0` of P5.6, and P5.6 gives `Stage3` and
  `cuspSet (Φ 1 ∘ L) = cuspSet L`; germs at `θc + 2πk` by `gp5_germ_shift`.  `Φ 1` fixes points at
  distance `≥ rc` from the cusp points since `ε_θc ≤ rc/2` and a zero of `X_H` is fixed
  (`gp5_hamFlow_fixed`).

## 5. Mathlib pitfalls met (this pin)

* `∞` (`ContDiff ℝ ∞`) is `((⊤ : ℕ∞) : WithTop ℕ∞)`, **not** `⊤`: `le_top` fails for `1 ≤ ∞`, `k ≤ ∞`;
  use `(by simp)`.  `ContDiffBump.contDiff` takes `n : ℕ∞`: write `(b.contDiff (n := ⊤))`.
* `!₂[a,b,c]` is `WithLp.toLp 2 ![a,b,c]`; coordinates reduce by `simp`/`rfl` (`(toLp 2 v) i = v i`),
  `HasDerivAt` into `ℝ³` via `hasDerivAt_pi` + `(PiLp.continuousLinearEquiv 2 ℝ _).symm` — finish with
  `exact` (not `simpa`: instance paths differ syntactically).  `ext` on `ℝ³ →L ℝ³` goes down to
  `.ofLp i`; use `ContinuousLinearMap.ext` explicitly.
* `HasDerivAt.mul`/`.add` return Pi-forms (`id * ψ`, `ψ + id * deriv ψ`), `HasDerivAt.comp` returns
  `f ∘ g`; give the `HasDerivAt` an explicit function type before `.deriv`/`rw`.  Same for
  `ContDiff.smul`/`ContDiff.add` (state `ContDiff ℝ ∞ (a + b)` explicitly before
  `iteratedFDeriv_add_apply`).  `fderiv_sub` is stated for `f - g` (Pi): use `HasFDerivAt.sub … .fderiv`.
* `gcongr` recurses into `|·|` and leaves nonnegativity side goals — use `mul_le_mul_of_nonneg_left`.
* Not available/renamed: `Real.exp_one_lt_d9` (not imported), `abs_sub_round_le_abs_self` (absent;
  two-case proof via `round_eq_zero_iff`), `round_sub_int` → `round_sub_intCast`, `round_neg` (absent —
  and `circDist` symmetry was not needed), `pow_le_pow_left` → `pow_le_pow_left₀`, `hasFDerivAt_id'`
  (absent), `Set.setOf_and` → `Set.ofPred_and`, `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`,
  `EuclideanSpace.norm_single` → `PiLp.norm_single`, `push_neg` → `push Not`,
  `ContinuousLinearMap.lipschitz` → `.lipschitzWith`, `add_le_add_right h a : a + b ≤ a + c`
  (left addition in this pin) — use `add_le_add h le_rfl`.
* `norm_zero` inside `rw`/`exact` on operator spaces needs `(E := …)` (instance problem stuck).
* A `?_` inside `obtain … := f ?_` did not produce a goal (`No goals` at the bullet): state the side
  fact with `have` first.
* `1`-D IFT: `HasStrictDerivAt.hasStrictFDerivAt_equiv`, `HasStrictFDerivAt.toOpenPartialHomeomorph`,
  `OpenPartialHomeomorph.restrOpen` (`coe_restrOpen`, `coe_restrOpen_symm` are `rfl`),
  `OpenPartialHomeomorph.contDiffAt_symm_deriv`.

## 6. For the assembler / executor

* Keep the extra import (§2).  Otherwise the file is skeleton + `gp5_*` helpers + the seven bodies.
* The linter warning "Variable name `hf'` is not explicitly referenced" is on the **frozen** statement
  of `exactGerm_of_cuspFlow`; the proof does `clear hf'`.  Harmless; the hypothesis could be dropped
  at porting time (P5.7 passes it anyway).
* P5.7 instantiates P0.1 with `n = 1`, `Hs = fun _ => H`, `a = fun _ => 1`, and uses
  `fd_contact_motions.diffeo` for `ContDiff ℝ ∞ (hamFlow H 1)`; `composeFlows 1 Hs a p = hamFlow (Hs 0)
  (a 0) p` is by `simp [composeFlows]`.
* `flow_C2_close` is proved with the explicit constant `C₀ = 100` (`‖J − 1‖ ≤ 4η`, `‖J‖ ≤ 5`,
  `‖M′‖ ≤ η‖M‖ + 25η`, `e^η − 1 ≤ 4η` for `η ≤ 1`).
* All numerical truth checks of GF_PLAN §0 relevant to P5 ((ii), (iii)) are confirmed by the proofs;
  nothing was found false.
