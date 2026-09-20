# U-LIFT-1 report (prefix `ul1_`) — 2026-09-15

File: `work/drafts/floor/U_LIFT1.lean` (byte-identical copy of `Statements_FINAL.lean` + one inserted block,
lines 650-971, immediately before the docstring of `ul_exists_constants`, inside the frozen `noncomputable section`
of `namespace SM`).  `diff Statements_FINAL.lean U_LIFT1.lean`: one hunk `649a650,971`, zero deletions or changes —
no definition, statement, name or docstring touched.

Check: `cd work/lean && lake env lean ../drafts/floor/U_LIFT1.lean` — **0 errors**, 12 s warm; 23 `declaration uses
sorry` warnings (the other units' leaves and the two stated corollaries, exactly as in `Statements_FINAL.lean`).
`grep -c sorry`: 25 before, 25 after (my block contains no `sorry`).  Clash scan: `ul1_` occurs nowhere in
`work/lean/{SM,CV,Bridge}` nor in any other `U_*.lean`.  `#print axioms` on the exports (probed on the scratch copy):
`[propext, Classical.choice, Quot.sound]` only.

## Leaves

U-LIFT-1 owns no `sorry` leaf (PLAN_FINAL.md §4: "L1-L4 helpers — no leaf of its own; exports helper lemmas").
Proved: none of the 23 leaves is mine; left: none of mine.  The 44 `ul1_` helper theorems below are all proved.

## Helpers added (44), in file order — what U-LIFT-2 / U-LIFT-3 should call

L1 — `v + z′ > 0` (sm-3:4458-4462; DESIGN_B §5 L1):
- `ul1_length_mul_self (u : Plane) : euclideanLength u * euclideanLength u = u.1 * u.1 + u.2 * u.2`
  (local copy of `euclideanLength_mul_self`: SM/TransportLengths.lean is NOT in this file's import closure).
- `ul1_abs_snd_le_length (u) : |u.2| ≤ euclideanLength u`, `ul1_abs_fst_le_length (u) : |u.1| ≤ euclideanLength u`.
- `ul1_normalize_vertical_neg {z} (hz : z < 0) : SM.normalize ((0:ℝ), z) = downDir`.
- **`ul1_length_add_snd_pos {u : Plane} (hu : u ≠ 0) (hd : SM.normalize u ≠ downDir) : 0 < euclideanLength u + u.2`**
  (equality `v = −z′` forces `x′ = 0`, `z′ < 0`, i.e. the downward vertical — excluded).
- **`ul1_denom_pos (γ) (s) (hreg : deriv γ s ≠ 0) (hd : SM.normalize (deriv γ s) ≠ downDir) :
  0 < euclideanLength (deriv γ s) + (deriv γ s).2`** — the denominator of `liftY0`.

L3 — display (*) (sm-3:4463-4466):
- **`ul1_liftY0_identity (γ) (s) (hpos : 0 < euclideanLength (deriv γ s) + (deriv γ s).2) :
  (deriv γ s).2 - liftY0 γ s * (deriv γ s).1 = euclideanLength (deriv γ s)`**.
- **`ul1_liftY0_admissible (γ) (s) (hreg) (hd) : LiftAdmissible γ s (liftY0 γ s)`** (`z′ − y₀ x′ = v > 0`; this is
  the `(1 − b)·v` term of L7).

L2 — `liftY0` smooth and periodic (sm-3:4466-4468):
- `ul1_hasDerivAt_log {x} (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x` (from `exp` by
  `HasStrictDerivAt.of_local_left_inverse`; Mathlib's `Log.Deriv` is not imported here).
- `ul1_contDiff_log_comp {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hpos : ∀ s, 0 < g s) : ContDiff ℝ ∞ (fun s => Real.log (g s))`
  (via `contDiff_infty_iff_deriv`: the derivative `g′/g` is `C^∞` — not circular).
- `ul1_contDiff_sqrt_comp {g} (hg) (hpos : ∀ s, 0 < g s) : ContDiff ℝ ∞ (fun s => Real.sqrt (g s))`
  (`√g = exp (log g · ½)`, `Real.sqrt_eq_rpow`, `Real.rpow_def_of_pos`).  Reusable wherever a square root of a
  positive smooth function appears.
- `ul1_length_deriv_contDiff (γ) (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ s, deriv γ s ≠ 0) :
  ContDiff ℝ ∞ (fun s => euclideanLength (deriv γ s))` — the speed is `C^∞`.
- **`ul1_liftY0_contDiff (γ) (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ s, deriv γ s ≠ 0)
  (hdown : ∀ s, SM.normalize (deriv γ s) ≠ downDir) : ContDiff ℝ ∞ (liftY0 γ)`**.
- **`ul1_liftY0_periodic (γ) (hper : Function.Periodic (deriv γ) 1) : Function.Periodic (liftY0 γ) 1`**,
  `ul1_liftY0_add_one (γ) (hper) (s) : liftY0 γ (s + 1) = liftY0 γ s` (simp-friendly form).
- Loop forms: `ul1_liftY0_contDiff_loop (F : SmoothRegularLoop) (hdown : ∀ s, SM.normalize (deriv F.γ s) ≠ downDir)`,
  `ul1_liftY0_periodic_loop (F : SmoothLoop)`.

L4 — `circBump` (sm-3:4469-4476, FR-FL-C7); all with `δ s₀ s : ℝ`, hypotheses `(hδ : 0 < δ) (hδ' : δ < 1 / 2)` only
where stated:
- `ul1_circBump_contDiff (δ s₀) : ContDiff ℝ ∞ (circBump δ s₀)` (`fun_prop` after `unfold circBump`).
- `ul1_circBump_add_one (δ s₀ s) : circBump δ s₀ (s + 1) = circBump δ s₀ s`,
  `ul1_circBump_periodic (δ s₀) : Function.Periodic (circBump δ s₀) 1`,
  `ul1_circBump_add_int (δ s₀ s) (n : ℤ) : circBump δ s₀ (s + n) = circBump δ s₀ s`.
- `ul1_circBump_nonneg`, `ul1_circBump_le_one`, `ul1_circBump_mem_Icc : circBump δ s₀ s ∈ Set.Icc 0 1` (no hypotheses).
- `ul1_cos_two_pi_mul_lt_one {δ} (hδ) (hδ') : Real.cos (2 * Real.pi * δ) < 1` (the denominator `1 − cos 2πδ > 0`).
- **`ul1_circBump_self (δ s₀) (hδ) (hδ') : circBump δ s₀ s₀ = 1`**,
  **`ul1_circBump_eq_one (δ s₀ s) (hδ) (hδ') (n : ℤ) (hs : s = s₀ + n) : circBump δ s₀ s = 1`** (for L8 `y (τ v) = c_v`
  after `Int.fract` reduction).
- **`ul1_circBump_eq_zero (δ s₀ s) (hδ) (hδ') (h : ∀ n : ℤ, δ ≤ |s - s₀ - n|) : circBump δ s₀ s = 0`** — "vanishes at
  circle distance `≥ δ`"; the circle distance is realised by `n := round (s − s₀)` (`abs_sub_round : |x − round x| ≤ 1/2`),
  `cos (2π(s − s₀)) = cos (2π|d|)` (`Real.cos_add_int_mul_two_pi`, `Real.cos_abs`) and
  `Real.cos_le_cos_of_nonneg_of_le_pi` on `0 ≤ 2πδ ≤ 2π|d| ≤ π`.
- **`ul1_exists_int_of_circBump_ne_zero (δ s₀ s) (hδ) (hδ') (h : circBump δ s₀ s ≠ 0) : ∃ n : ℤ, |s - s₀ - n| < δ`** —
  the contrapositive, the form L6 ("at most one bump nonzero", `Finset.sum_eq_single`) consumes: two nonzero bumps at
  `s` centred at `τ v ≠ τ w` give `|τ v − τ w − m| < 2δ` for some integer `m`, impossible once `δ` is below half the
  minimal circle distance of the `τ`'s.

Bonus (cheap, for U-LIFT-3's L9 fields `smooth`, `periodic`, `immersion`, `positive`):
- `ul1_liftY_contDiff (γ) (hγ) (hreg) (hdown) {ι} [Fintype ι] (τ c : ι → ℝ) (δ) : ContDiff ℝ ∞ (liftY γ τ c δ)`,
  `ul1_liftY_add_one`, `ul1_liftY_periodic (γ) (hper : Function.Periodic (deriv γ) 1) … : Function.Periodic (liftY γ τ c δ) 1`.
- `ul1_xOf_liftT : xOf (liftT γ τ c δ) = fun s => (γ s).1`, `ul1_yOf_liftT : yOf (liftT γ τ c δ) = liftY γ τ c δ`,
  `ul1_zOf_liftT : zOf (liftT γ τ c δ) = fun s => (γ s).2` (all `rfl`), **`ul1_xzOf_liftT : xzOf (liftT γ τ c δ) = γ`**
  (`funext; rfl` — this IS the leaf's conjunct `xzOf K.T = F.γ` and gives `immersion` from `F.regular`).
- `ul1_hasDerivAt_fst/snd (γ) {s} (h : HasDerivAt γ (deriv γ s) s) : HasDerivAt (fun t => (γ t).1) (deriv γ s).1 s` (resp. `.2`),
  **`ul1_deriv_xOf_liftT (γ) (hγ : Differentiable ℝ γ) … (s) : deriv (xOf (liftT γ τ c δ)) s = (deriv γ s).1`**,
  **`ul1_deriv_zOf_liftT … : deriv (zOf (liftT γ τ c δ)) s = (deriv γ s).2`** — so `positive` for `T := liftT F.γ τ c δ`
  reads `0 < (deriv F.γ t).2 − liftY F.γ τ c δ t * (deriv F.γ t).1` after `rw [ul1_deriv_zOf_liftT, ul1_yOf_liftT,
  ul1_deriv_xOf_liftT]` (`Differentiable ℝ F.γ` is `F.smooth.differentiable (by decide)`), i.e. exactly L7.
- `ul1_liftT_contDiff (γ) (hγ) (hreg) (hdown) … : ContDiff ℝ ∞ (liftT γ τ c δ)`,
  `ul1_liftT_periodic (γ) (hγ : Function.Periodic γ 1) (hper : Function.Periodic (deriv γ) 1) … : Function.Periodic (liftT γ τ c δ) 1`,
  loop forms `ul1_liftT_contDiff_loop (F : SmoothRegularLoop) (hdown)`, `ul1_liftT_periodic_loop (F : SmoothLoop)` — the
  `TransverseKnot.smooth` and `.periodic` fields of L9 verbatim.

## Mathlib pitfalls (this pin, Lean v4.34.0-rc2)

- **Import closure.** The frozen imports (`SM.Curl, SM.TransverseFront, SM.CeSmoothingRecord, SM.CornerStateSum,
  SM.LinkPositiveLift, SM.UniformRotation`) do NOT pull in `Mathlib.Analysis.SpecialFunctions.Sqrt` (`ContDiff.sqrt`,
  `Real.hasDerivAt_sqrt`), `Mathlib.Analysis.InnerProductSpace.Calculus` (`ContDiff.norm`, `ContDiffAt.norm`),
  `Mathlib.Analysis.SpecialFunctions.Log.Deriv` (`Real.hasDerivAt_log`, `Real.contDiffAt_log`), nor the `rpow`
  derivative modules — the plan's L2 route "`ContDiff.sqrt` / `ContDiffAt.norm`" is unavailable without new imports (which
  I did not add: the assembler ports with the fixed import list).  Available and used instead: `Real.contDiff_exp`,
  `Real.hasStrictDerivAt_exp`, `Real.exp_log`, `Real.continuousAt_log`, `Real.sqrt_eq_rpow`, `Real.rpow_def_of_pos`,
  `HasStrictDerivAt.of_local_left_inverse`, `contDiff_infty_iff_deriv`, `ContDiff.div/inv/mul/add/sub/neg/fst/snd/prodMk/sum`.
  Also NOT in the closure: `SM.TransportLengths` (`euclideanLength_mul_self`, `planeDot_self_nonneg`) — hence the local
  `ul1_length_mul_self`.  `planeDot_self_pos` (SM/EuclideanPlane.lean) IS available, and `planeDot u u` is definitionally
  `u.1 * u.1 + u.2 * u.2` (`exact` accepts it).
- `HasDerivAt.fst` does not exist: dot-notation falls through to `HasFDerivAtFilter.fst`, which has no `.deriv`.  Use
  `(ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt s h` (Deriv/Comp.lean:389); the result's function
  `⇑(fst ℝ ℝ ℝ) ∘ γ` is accepted for `fun t => (γ t).1` by `exact`.
- `Real.smoothTransition.contDiff {n : ℕ∞}` is stated for `n : ℕ∞` while `ContDiff` takes `n : ℕ∞ω` (`WithTop ℕ∞`);
  `fun_prop` handles the coercion for `∞`; a manual `.comp` would need `(n := ⊤)`.  `ContDiff.differentiable (by decide)`
  discharges `(∞ : ℕ∞ω) ≠ 0` (the accepted `SmoothLoop.differentiable` pattern).
- `ContDiff.div` concludes `ContDiff 𝕜 n (f / g)` (Pi division); `apply ContDiff.div` still unifies with a goal
  `ContDiff ℝ ∞ fun s => a s / b s`.
- `field_simp` on `z − (−x/(v+z))·x = v` leaves a goal closed by `linear_combination (-1 : ℝ) * hsq` with
  `hsq : v * v = x * x + z * z` (coefficient `−1`, not `1`).
- `push_neg` is deprecated in this pin (U-B1 report); `simp only [not_exists, not_lt]` / `rw [not_lt]` used instead.
- `Real.cos_abs` lives in `Mathlib/Analysis/Complex/Trigonometric.lean` (available); `abs_sub_round`,
  `Real.cos_add_int_mul_two_pi`, `Real.cos_le_cos_of_nonneg_of_le_pi`, `Real.cos_lt_cos_of_nonneg_of_le_pi` all available.

## Notes for the assembler / U-LIFT-2 / U-LIFT-3

- Nothing false or under-hypothesised in my scope.  The `circBump` statements need `0 < δ < 1/2` exactly as the plan
  says (`= 1` at the centre needs `cos 2πδ ≠ 1`; the support statement needs `2πδ ≤ π`); U-LIFT-2 choosing `δ < 1/4`
  derives `δ < 1/2` by `linarith`.  `ul1_circBump_nonneg/le_one/contDiff/periodic` need no hypothesis on `δ`.
- The block is self-contained (Mathlib + the frozen defs `downDir`, `liftY0`, `circBump`, `liftY`, `liftT`,
  `LiftAdmissible`, and the accepted `euclideanLength_formula`, `euclideanLength_pos`, `planeDot_self_pos`,
  `SM.normalize`, `SmoothLoop.deriv_periodic`, `xOf/yOf/zOf/xzOf`), so it can be concatenated anywhere after those
  definitions; it sits before `ul_exists_constants` as instructed.
- `ul1_contDiff_sqrt_comp` / `ul1_contDiff_log_comp` / `ul1_hasDerivAt_log` are generic real-analysis facts; if the port
  later adds `Mathlib.Analysis.SpecialFunctions.Sqrt` they can be replaced by `ContDiff.sqrt`, but they are harmless as is.
- Scratch used for iteration: the session scratchpad copy `ul1_scratch.lean` (same imports, frozen defs copied); no
  file under `work/lean` was written.
