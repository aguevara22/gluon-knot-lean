# U-LIFT-2 report — `ul_exists_constants` + helpers L6-L8 (prefix `ul2_`)

File: `work/drafts/floor/U_LIFT2.lean` (copy of `Statements_FINAL.lean`, statements untouched).
Check: `cd work/lean && lake env lean ../drafts/floor/U_LIFT2.lean` — **0 errors, 0 non-sorry warnings**,
22 `declaration uses sorry` (was 23: exactly the leaf of this unit). `grep -c sorry`: 25 → 24 (the two
remaining non-leaf hits are the docstring mentions on lines 30/386). `diff Statements_FINAL.lean U_LIFT2.lean`
deletes ONE line (the leaf's `  sorry`) and inserts 318 (the helpers and the one-line proof). ~14 s warm.
`#print axioms` (probed on a scratch copy): `ul_exists_constants`, `ul2_exists_delta`, `ul2_liftY_tau`,
`ul2_liftY_admissible` = `[propext, Classical.choice, Quot.sound]`.

## Leaves

| leaf | status |
|---|---|
| `ul_exists_constants` (§8.7, line 743) | **PROVED** — `exact ul2_exists_constants_vec _ _ hO hU hdO hdU hdet` |

No leaf of this unit left. No leaf found false; no hypothesis missing. No U-LIFT-1 statement had to be
assumed (nothing with `sorry` was added).

## Route actually taken for the leaf

Vector form `ul2_exists_constants_vec (dO dU : Plane)` (the leaf is its instance at `deriv γ sO`, `deriv γ sU`;
`LiftAdmissible` unfolds definitionally). Case split `by_cases hcase : dO.1 < 0 ∧ 0 < dU.1`:
- **`x′_O < 0 < x′_U`** (the only case using `det`): `m_O := z′_O/x′_O < m_U := z′_U/x′_U` because
  `m_U − m_O = det dO dU / (x′_O x′_U)` (`div_sub_div`, `div_pos_of_neg_of_neg`: numerator `det < 0`, denominator
  `< 0`); `c_O := (2 m_O + m_U)/3`, `c_U := (m_O + 2 m_U)/3`; admissibility from `z′ − c x′ = x′ (m − c)`
  (`linear_combination` with `div_mul_cancel₀`) and `mul_pos_of_neg_of_neg` / `mul_pos`.
- **`0 ≤ x′_O`** (covers `x′_O > 0` and `x′_O = 0`): pick any admissible `c_U` (`ul2_exists_admissible_vec`),
  `c_O := min (c_U − 1) (z′_O/x′_O − 1)`; for `x′_O > 0` the bound `c_O ≤ m_O − 1` gives `z′ − c_O x′ ≥ x′ > 0`;
  for `x′_O = 0` the constraint is void and `z′_O > 0` (`ul2_snd_pos_of_fst_eq_zero`). Note Lean's `z/0 = 0`
  makes the same formula work in both sub-cases.
- **`x′_U ≤ 0`**: symmetric, `c_U := max (c_O + 1) (z′_U/x′_U + 1)` (`mul_le_mul_of_nonpos_right`).
So the printed five cases are three branches (two of them with an inner `lt_or_eq`).

`ul2_snd_pos_of_fst_eq_zero d : d ≠ 0 → normalize d ≠ downDir → d.1 = 0 → 0 < d.2` is the "no downward
vertical tangency" hypothesis in usable form: for `d = (0, z)`, `z < 0`, `euclideanLength d = −z`
(`euclideanLength_formula`, `Real.sqrt_mul_self_eq_abs`) and `normalize d = (0, −1) = downDir`.

## Helpers added (all proved; in §8.7, same section as the leaf)

Before the leaf (used by it):
- `ul2_snd_pos_of_fst_eq_zero`, `ul2_exists_admissible_vec`, `ul2_exists_constants_vec`.

After the leaf, before `ulift_exists_transverse_lift` (for U-LIFT-3):
- bump facts (L4-type, self-contained so this unit does not depend on U-LIFT-1): `ul2_circBump_nonneg`,
  `ul2_circBump_le_one`, `ul2_cos_two_pi_mul_lt_one` (`0 < δ < 1 → cos(2πδ) < 1`),
  `ul2_circBump_self` (`0 < δ < 1 → circBump δ s₀ s₀ = 1`),
  `ul2_circBump_eq_zero` (`0 < δ ≤ 1/2 → (∀ n : ℤ, δ ≤ |s − s₀ − n|) → circBump δ s₀ s = 0`),
  `ul2_exists_int_of_circBump_ne_zero` (contrapositive: `circBump δ s₀ s ≠ 0 → ∃ n : ℤ, |s − s₀ − n| < δ`),
  `ul2_circBump_periodic` (`Function.Periodic (circBump δ s₀) 1`).
- circle gaps: `ul2_gap_of_mem_Ico` (`a, b ∈ [0,1) → min |a−b| (1−|a−b|) ≤ |a − b − n|` for every `n : ℤ`),
  `ul2_gap_pos` (positive when `a ≠ b`), `ul2_exists_pos_le` (a finite family of positive reals has a
  positive lower bound; `Finset.exists_min_image`, empty index handled).
- `ul2_exists_radius` (admissibility is open: `Continuous (deriv γ) → LiftAdmissible γ s₀ c → ∃ r > 0,
  ∀ s, |s − s₀| < r → LiftAdmissible γ s c`; `ContinuousAt.eventually_lt` + `Metric.eventually_nhds_iff`).
- **L6** `ul2_exists_delta γ τ c` : from `τ v ∈ Ico 0 1`, `Injective τ`, `Continuous (deriv γ)`,
  `Periodic (deriv γ) 1`, `∀ v, LiftAdmissible γ (τ v) (c v)`:
  `∃ δ, 0 < δ ∧ δ < 1/4 ∧ (∀ v w, v ≠ w → ∀ n : ℤ, 2δ ≤ |τ v − τ w − n|) ∧
  (∀ v s, (∃ n : ℤ, |s − τ v − n| < δ) → LiftAdmissible γ s (c v))`.
  (`δ := min (min (ε₁/2) ε₂) (1/8)`; the circle-distance hypothesis on `s` is reduced to `s − n` by the
  periodicity of `deriv γ`.)
- `ul2_bump_unique` (with the gap clause and `δ ≤ 1/2`: two nonzero bumps at one `s` have the same index),
  `ul2_liftY_eq_single` (`Finset.sum_eq_single`: `liftY = y₀ + b_v (c v − y₀)` when the other bumps vanish),
  `ul2_liftY_eq_liftY0` (all bumps vanish ⇒ `liftY = liftY0`), `ul2_liftY_periodic` (from `Periodic (liftY0 γ) 1`).
- **L8** `ul2_liftY_tau` : `0 < δ ≤ 1/2` + gap clause ⇒ `liftY γ τ c δ (τ v) = c v`.
- **L7** `ul2_liftY_admissible` : `0 < δ ≤ 1/2` + gap clause + the admissibility clause of L6 +
  `hpos : 0 < z′ − liftY0 γ s · x′` (this is U-LIFT-1's (*), L1+L3, taken as a hypothesis so the two units stay
  independent) ⇒ `0 < z′ − liftY γ τ c δ s · x′`. Proof: `z′ − y x′ = (1 − b)(z′ − y₀x′) + b(z′ − c_v x′)`.

## For U-LIFT-3 (how to consume)

`γ := F.γ`, `ι := X.Γ.Visit`, `τ := c.τ`, `hτ := c.τ_mem`, `hinj := c.τ_inj`, `hcont := F.continuous_deriv`
(`SmoothLoop.continuous_deriv`), `hper := F.deriv_periodic` (FrontSmooth.lean:203); `c v` from
`ul_exists_constants` at `(τ (overVisit x), τ (underVisit x))` (define `c` on visits by the crossing's pair;
`det < 0` from `c.sign_eq` + `hneg`, `hO/hU := F.regular _`, `hdO/hdU := hdown _`). Then
`obtain ⟨δ, hδ0, hδ4, hgap, hadm⟩ := ul2_exists_delta …`, `h1 : δ ≤ 1/2 := by linarith`, and
`ul2_liftY_tau hδ0 h1 … hgap v`, `ul2_liftY_admissible hδ0 h1 … hgap hadm s (L3-positivity)`. For the
`embedded` field, `ul2_liftY_eq_single`/`ul2_exists_int_of_circBump_ne_zero` give the bump-support reduction.
`δ < 1/4` is exported as stated in the plan although `δ ≤ 1/2` suffices for every lemma here.

## Mathlib pitfalls met (v4.34.0-rc2 pin)

- `field_simp` no longer clears `x / x` unless `x ≠ 0` is literally in context, and when it closes the goal a
  following `ring` errors with "no goals" — replaced everywhere by `div_mul_cancel₀ a h : a / b * b = a` +
  `linear_combination`.
- `rw [abs_of_pos (by linarith)]` unifies with the FIRST `|·|` in the goal (here `|a − b|`, not `|a − b − n|`);
  give the argument explicitly (`abs_of_pos (show (0:ℝ) < a − b − n by linarith)`).
- `exact_mod_cast` from `n < 0` to `(n : ℝ) ≤ −1` fails (normalises `−1` to `Int.negSucc 0`); go through an
  integer `n ≤ −1` (`omega`) first.
- `Real.cos_abs : cos |x| = cos x` must be applied after moving the constant inside the absolute value
  (`abs_mul`, `abs_of_pos`); `Real.cos_add_int_mul_two_pi x n : cos (x + n * (2π)) = cos x`.
- `push_neg` and `if_neg` are deprecated (warnings); used `not_lt.mp` / `simp [g, hvw]` instead.
- `abs_sub_round (x) : |x − round x| ≤ 1/2` (Mathlib/Algebra/Order/Round.lean:193) does the `Int.fract`
  reduction in one step.
- `Real.smoothTransition.{nonneg, le_one, one, zero_of_nonpos}` and `Real.cos_eq_one_iff_of_lt_of_lt` are the
  only special-function facts needed.
