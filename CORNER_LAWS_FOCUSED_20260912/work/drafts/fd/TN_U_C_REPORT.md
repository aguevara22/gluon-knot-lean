# TN_U_C_REPORT.md — Unit C (the time-dependent Moser flow by suspension), row 84

Date: 2026-09-14.  File: `work/drafts/fd/TN_U_C.lean` (1593 lines; skeleton 959).
Compile: `cd work/lean && lake env lean ../drafts/fd/TN_U_C.lean` — **0 errors**, 32 warnings, all
`declaration uses sorry` (one per remaining leaf).  `grep -c sorry`: 42 before → 34 after
(8 leaf `sorry`s replaced; the other 34 are the 32 leaves of units A, B, D, E, F, the false leaf C2,
and 2 mentions in prose).  `diff TN_Skeleton.lean TN_U_C.lean` removes exactly eight `  sorry` lines;
no statement, definition, name or docstring was changed.

## 1. Leaves proved (8 of 9)

| leaf | name | line | notes |
|---|---|---|---|
| C1 | `contDiff_Yfield` | 548 | pointwise: on `|τ| < 4 ∧ ‖w‖ < 2ρ` product of smooth maps (B5 `contDiffOn_Vf` at the point); elsewhere the second component is eventually `0` (`χ_τ = 0` for `|τ| ≥ 3`, `χ_w = 0` for `‖w‖ ≥ ρ`) |
| C3 | `Theta_fst` | 736 | from `tc3_Theta_fst_gen` (general start `|τ₀| < 2`): ODE uniqueness for `τ′ = χ_τ(τ)` on the open interval, closure by continuity |
| C4 | `hasDerivAt_Phi` | 742 | `hasFDerivAt_snd.comp_hasDerivAt` of the flow ODE, C3, `χ_τ(t) = 1` |
| C5 | `Phi_one_inverse` | 749 | inverse `p′ ↦ pr₂ Θ_{−1}(1, p′)`; `Θ_1(0,p) = (1, Φ₁p)` (C3), `(Θ_{−1}(1,p′)).1 = 0` (`tc3_Theta_fst_gen` with `τ₀ = 1`, `t = −1`), group law `IsGlobalFlow.neg_apply` with the Lipschitz constant from `tc2_exists_lipschitzWith` (NOT from C2) |
| C6 | `exists_aprioriRadius` | 937 | `δ₁ := ρ e^{−2C}/(8(C+1))`, `C` from B6; `tc6_continuation` forward on `[0,2]` and on the reversed curve `s ↦ Φ_{−s}` on `[0,1]` |
| C7 | `Phi_shift` | 975 | the curve `t ↦ (t, Φ_t(θ₀,w₀) + (2π,0))` solves the `Y`-ODE on `(−1,2)` (`cutoff_along`, `Vf_periodic`, `χ_θ = 1` since `|θ| ≤ 2π+1 < 20`); `ODE_unique_Ioo` against `Θ_t(0,(θ₀+2π,w₀))`; endpoints by `tc3_eqOn_Icc` |
| C8 | `Phi_core` | 1025 | constant curve `(s,(θ,0))` solves the `Y`-ODE on `(−2,2)` (`Vf_core`); uniqueness; endpoints by `tc3_eqOn_Icc`.  Does not need `|θ| ≤ 4π` |
| C9 | `hasDerivAt_fderiv_Phi` | 1176 | `tc9_hasDerivAt_fderiv_flow` (CLM-level variational equation for `Θ`), `DΦ_t = snd ∘ DΘ_t(0,p₀) ∘ inr`, `D_p[(Θ_t(0,p)).1] = 0` by C3, and the `p`-slice `p ↦ (Y(t,p)).2` equals `V_t` near `Φ_t p₀` (`cutoff = 1` on the open set `|θ| < 20 ∧ ‖w‖ < ρ/2`, `Filter.EventuallyEq.fderiv_eq`) |

`#print axioms`: the leaves show `sorryAx` only through other units' leaves (B5 `contDiffOn_Vf`, B6
`exists_Vf_bound`) and through C2 via `isGlobalFlow_Theta`.  The unit-independent helpers
`tc2_not_hasCompactSupport_Yfield`, `tc6_continuation`, `tc9_hasDerivAt_fderiv_flow`,
`tc9_contDiff_uncurry_of_bounded` are axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## 2. Leaf left: C2 `hasCompactSupport_Yfield` (line 664) — FALSE AS STATED

`Yfield T ρ q = (chiTau q.1, (chiTau q.1 * cutoff ρ q.2) • Vf T q.1 q.2)`.  The FIRST component
`χ_τ(τ)` does not depend on `p` at all and equals `1` for `|τ| ≤ 2`.  Exact counterexample: for every
`p`, `Yfield T ρ (0, p) = (1, …) ≠ 0`, so `support (Yfield T ρ) ⊇ {0} × ℝ × ℝ²`, unbounded.
This is PROVED in the file: **`tc2_not_hasCompactSupport_Yfield (ρ) : ¬ HasCompactSupport (Yfield T ρ)`**
(line 580; takes a norm bound `C` on `tsupport` and the point `(0, (|C|+1, 0))`).
The plan's claim "support in `Icc (−3) 3 × Icc (−21) 21 × closedBall 0 ρ`" is true only of the second
component (`tc2_hasCompactSupport_Yfield_snd`, line 610).

### Consequences and the fix (for the assembler)

Two PROVED non-leaf theorems of the skeleton are built on C2: `isGlobalFlow_Theta` (existence of `Θ`
via `exists_isGlobalFlow_of_hasCompactSupport'`) and `contDiff_Theta` (joint smoothness via
`ContactMotions.contDiff_uncurry`, which requires compact support).  Everything true is still
available, and the helpers to repair both proofs WITHOUT compact support are in the file:

- `tc2_exists_lipschitzWith (hT) (hρ) : ∃ K, LipschitzWith K (Yfield T ρ)` (line 625): `χ_τ ∘ pr₁`
  and the compactly supported second component are each Lipschitz; `LipschitzWith.prodMk`.
- `tc2_exists_bound (hT) (hρ) : ∃ L : ℝ≥0, ∀ q, ‖Yfield T ρ q‖ ≤ L` (line 639): `|χ_τ| ≤ 1`, second
  component bounded.
- `tc2_exists_isGlobalFlow (hT) (hρ) : ∃ φ, IsGlobalFlow (Yfield T ρ) φ` (line 655), from row 86's
  `ContactMotions.exists_isGlobalFlow hK hL` (bounded + globally Lipschitz).
- `tc9_contDiff_uncurry_of_bounded (hX : ContDiff ℝ ∞ X) (hL : ∀ p, ‖X p‖ ≤ L) (hφ : IsGlobalFlow X φ) :
  ContDiff ℝ ∞ (uncurry φ)` (line 1117; general finite-dimensional `E`, axiom-clean): near `(s₀,q₀)`
  the flow coincides (by `ODE_unique_Ioo`) with the flow of the compactly supported `b • X`, `b` a
  `ContDiffBump` equal to `1` on `closedBall 0 (‖q₀‖ + 1 + L(|s₀|+1) + 1)`, which is jointly smooth
  by `ContactMotions.contDiff_uncurry`.

Recommended edit of the skeleton (statements of `isGlobalFlow_Theta`, `contDiff_Theta` unchanged):
```
theorem isGlobalFlow_Theta … := Classical.epsilon_spec (tc2_exists_isGlobalFlow hT hρ)
theorem contDiff_Theta … := by
  obtain ⟨L, hL⟩ := tc2_exists_bound hT hρ
  exact tc9_contDiff_uncurry_of_bounded (contDiff_Yfield hT hρ) hL (isGlobalFlow_Theta hT hρ)
```
then delete leaf C2 (or replace it by the true `tc2_hasCompactSupport_Yfield_snd`).  For this the
block `section tc9_localization … end tc9_localization` (lines 1106-1172) must be MOVED up before
`isGlobalFlow_Theta` (it depends only on `SM.ContactMotions`, not on anything in this file), and the
`tc2_*` helpers (lines 580-661) already sit before C2, i.e. before `isGlobalFlow_Theta`, and depend
only on C1.  C9 already uses `tc9_contDiff_uncurry_of_bounded` instead of `contDiff_Theta`; C5 uses
`contDiff_Theta` for the smoothness of the inverse (any of the two proofs of `contDiff_Theta` works).
Nothing else in the file mentions `hasCompactSupport_Yfield`.

Do NOT "fix" C2 by also cutting off the first component of `Yfield` (`(χ_τ(τ)·χ_big(p), …)`): then
`τ = t` fails for far-away `p` and C3 (`∀ p`) and C5 (global diffeomorphism) become false as stated.

## 3. Helpers added (all `lemma`, prefix `tc<unit>_`, placed before the leaf that uses them)

Before C1 (522-545): `tc1_contDiff_chiTau`, `tc1_contDiff_chiTheta`, `tc1_contDiff_chiW`,
`tc1_contDiff_cutoff` (smoothness of the cutoffs; `contDiff_norm_sq ℝ` for `‖w‖²`),
`tc1_chiTau_eq_zero (3 ≤ |τ|)`, `tc1_chiTheta_eq_zero (21 ≤ |θ|)`, `tc1_chiW_eq_zero (ρ ≤ ‖w‖)`.

Before C2 (578-661): `tc2_not_hasCompactSupport_Yfield`, `tc2_abs_ge_of_notMem_Icc`,
`tc2_hasCompactSupport_chiTau`, `tc2_hasCompactSupport_Yfield_snd`, `tc2_exists_lipschitzWith`,
`tc2_exists_bound`, `tc2_exists_isGlobalFlow` (see §2).

Before C3 (692-731): `tc3_eqOn_Icc` (continuous maps equal on `Ioo a b` are equal on `Icc a b`;
`Set.EqOn.of_subset_closure`, `closure_Ioo`), `tc3_Theta_fst_gen` (`pr₁Θ_t(τ₀,p) = τ₀ + t` on
`Icc (−2−τ₀) (2−τ₀)` for `|τ₀| < 2`; used with `τ₀ = 0` in C3 and `τ₀ = 1, t = −1` in C5).

Before C6 (777-925): `tc6_bootstrap` (Grönwall `norm_le_gronwallBound_of_norm_deriv_right_le` +
`gronwallBound_ε0` for `w`, mean value `norm_image_sub_le_of_norm_deriv_right_le_segment` for `θ`:
the bounds `ρ/4`, `1` on `[0,t₁)` give the STRICT bounds `ρ/8`, `1/4` on `[0,t₁]`),
`tc6_continuation` (first bad time `sInf B`, `exists_lt_of_csInf_lt`, continuity
`ContinuousAt.eventually_lt` + `Metric.eventually_nhds_iff`).  Both are stated for an abstract curve
`γ` with velocity `γ′` obeying `‖γ′‖ ≤ C‖w‖` at good points — no mention of the flow — so they serve
forward and reversed time alike.

Before C9 (1032-1173): `tc9_fderiv_uncurry_time`, `tc9_fderiv_flow_space` (general-field versions of
row 86's `fderiv_uncurry_time`, `fderiv_flow_space`), `tc9_hasDerivAt_fderiv_flow`
(`∂_s Dφ_s(p) = DX(φ_s p) ∘ Dφ_s(p)` as an equation of CONTINUOUS LINEAR MAPS, for any `C^∞` field
with jointly `C^∞` global flow — row 86's `hasDerivAt_fderiv_flow` generalised from `X_H` and from
"applied to `v`"), `tc9_contDiff_uncurry_of_bounded` (§2).

## 4. Mathlib pitfalls met (v4.34.0-rc2 pin)

- `hasFDerivAt_snd.comp_hasDerivWithinAt x h` fails by higher-order unification when the expected
  function is `fun s => (γ s).2`; give `(hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ²))` explicitly and
  `exact` the result (defeq).  Same for `comp_hasDerivAt`: elaborate `hd.comp_hasDerivAt s hc` in a
  `have` before `.unique`.
- `rw [abs_of_nonneg (by positivity)]` rewrites the FIRST `|·|` it finds (metavariable): write
  `abs_of_nonneg (show (0:ℝ) ≤ … by positivity)`.
- `positivity` needs `0 < ρ` as a HYPOTHESIS in context; `hρ.pos` (a projection) is not found — add
  `have hρ0 := hρ.pos`.
- `norm_fst_le _` / `norm_snd_le _` need the pair written out (`?x.2 =?= (a, b)` is not solved).
- `ContinuousLinearMap.snd_apply`/`fst_apply` do NOT exist; the simp lemmas are
  `ContinuousLinearMap.coe_snd'`, `coe_fst'`, `inr_apply`, `comp_apply`.
- `ext x` on an equality of `ℝ × ℝ² →L[ℝ] ℝ × ℝ²` may not introduce `x` as expected; use
  `refine ContinuousLinearMap.ext fun x => ?_`.
- `LipschitzWith.comp … LipschitzWith.prod_fst` produces the constant `K₁ * 1`; state the witness
  `max (K₁ * 1) K₂` explicitly, and prove `Yfield T ρ = fun x => ((chiTau ∘ Prod.fst) x, (Yfield T ρ x).2)`
  by `funext fun x => rfl` (structure eta) before `exact`.
- `push_neg` is deprecated at this pin (warning) — use `rw [not_lt] at h` / `push Not`.
- `EqOn` obtained from `ODE_unique_Ioo` applied at a point is not beta-reduced; use
  `congrArg Prod.snd (heq ht)` + `simpa`, or `simp only at this`.
- Implicit `{θ₀} {w₀}` of `tc6_continuation` are only fixed by `hγ0`; when `hγ0` is given as `by simp`
  the metavariables leak (`⊢ θ₀ = ?m`).  State `hγ0` as a `have` with its type first.
- `Icc (-1) 2 ⊄ Ioo (-2) 2` (the endpoint `t = 2`): every leaf stated on a CLOSED interval needs the
  closure step `tc3_eqOn_Icc`; `hasDerivAt_Phi` is only on the open `Ioo (-2) 2`.
- `ContDiffBump (0 : E)` on the product `ℝ × (ℝ × ℝ²)` works: the `HasContDiffBump` instance comes
  from `FiniteDimensional ℝ E` (already in the import closure through `SM.ContactMotions`).  The
  field `b.rIn` unfolds by `show` when `b` is a `let`.
- `ContactMotions.contDiff_uncurry` has `{E : Type}` (universe 0) — fine for the concrete spaces.

## 5. For the executor of unit D and the assembler

- Interfaces of my leaves are exactly the frozen ones.  Time domains: `Theta_fst` closed
  `Icc (−2) 2`; `hasDerivAt_Phi` open `Ioo (−2) 2`; `Phi_shift`, `Phi_core` closed `Icc (−1) 2`;
  `hasDerivAt_fderiv_Phi` open `Ioo (−1) 2`.  `AprioriRadius` gives `‖w‖ ≤ ρ/4`, `|θ − θ₀| ≤ 1`; the
  actual bounds are `ρ/8`, `1/4` (`tc6_bootstrap`) if D needs slack.  `δ₁ = ρ e^{−2C}/(8(C+1))`.
- D1 (`hasDerivAt_alphaT_flow`) may reuse `tc9_hasDerivAt_fderiv_flow` directly and the identity
  `fderiv (Phi t) p₀ = snd ∘L fderiv (Theta t) (0,p₀) ∘L inr` (the `hform` step inside C9).
- The `Vf`-slice fact used in C9, `(fun p => (Yfield T ρ (t,p)).2) =ᶠ[𝓝 (Φ_t p₀)] Vf T t`, is proved
  inline (`hev`); D1 needs the analogous `alphaT_Vf`-vanishing near the trajectory on the open set
  `|θ| < 20 ∧ ‖w‖ < ρ/2 ⊆ 2ρ`-tube where `P, N ≠ 0`.
- Unit C never used `hρ.chart_bij`, `hρ.chart_inj`, `hρ.P_pos`, `hρ.N_pos` directly (only through
  B5/B6 as black boxes) — the θ-velocity bound `|2uv/N| ≤ 2‖w‖²` of the plan was replaced by the
  cruder `|θ′| ≤ ‖V‖ ≤ C‖w‖ ≤ Cρ/(8(C+1)) ≤ 1/8`, absorbed into `δ₁`.
- Time: the whole file compiles in ≈ 9 s.
