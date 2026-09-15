# ER_UB_REPORT — unit U-B (retraction, lift and increment lemmas), row 104 cb:embedded-rotation

Date: 2026-09-14.  Prover: U-B subagent.  File: `work/drafts/pldiscs/ER_UB.lean` (618 lines; started as a
byte-identical copy of `EmbeddedRotation_Skeleton.lean`, 411 lines).  Toolchain: Lean v4.34.0-rc2, Mathlib pin
of `work/lean`.  Compile: `cd work/lean && lake env lean ../drafts/pldiscs/ER_UB.lean` — **0 errors**, 16
warnings `declaration uses sorry` (the 11 U-A leaves, lines 114-169, and the 5 U-C leaves, lines 454-490; none
in U-B), `#print axioms SM.cb_embedded_rotation` = `[propext, sorryAx, Classical.choice, Quot.sound]` with
`sorryAx` entering only through the other units.  `grep -c sorry`: **28 before → 21 after** (7 leaf bodies
replaced; the 21 remaining are the 16 other-unit leaves plus 5 mentions inside comments/docstrings).

## 1. Leaves proved (7 of 7, unit complete)

| leaf | name | line | proof in one line |
|---|---|---|---|
| B1 | `secantRetract_mem` | 176 | `le_max_left`, `max_le`, `min_le_left` on the two clamps, then `linarith`; the `let`s of `secantRetract` are exposed with `show` |
| B2 | `secantRetract_eq_self` | 200 | `min_eq_right`/`max_eq_right` from the four region inequalities, `Prod.ext`, `ring` |
| B3 | `continuous_secantRetract` | 216 | `unfold secantRetract; fun_prop` (Mathlib's `Continuous.max/min` are `@[fun_prop]`) |
| B4 | `increment_eq_principalAngle_of_cone` | 279 | `g s := θ s − principalAngle u (c s)` is continuous on `[a,b]` (`Complex.continuousAt_arg` on `slitPlane` via `regularPair_slitPlane`) and `Circle.exp (g s)` is constant (as a `Real.Angle`, `g s ≡ arg u`), so `IsCoveringMap.constOn_of_comp` on `isPreconnected_Icc` gives `g b = g a`; `principalAngle u (c a) = 0` (`principalAngle_eq_zero_iff`), `principalAngle u (c b) = principalAngle u v` (positive scalar) |
| B5 | `abs_increment_le_pi_of_halfplane` | 391 | `⟪N, c s⟫ = |c s| · |N| · cos (θ s − arg N) ≥ 0`, so `f := θ − arg N` has `cos ∘ f ≥ 0` on `[a,b]`; a continuous such `f` moves by at most `π` (`eb_abs_sub_le_pi_of_cos_nonneg`: IVT `intermediate_value_Icc`/`Icc'` against `eb_exists_cos_neg_of_gt_pi`) |
| B6 | `IsLiftOn.neg` | 410 | `Real.cos_add_pi`, `Real.sin_add_pi`, `ContinuousOn.add`; `-(x, y) = (-x, -y)` is `rfl` |
| B7 | `increment_coe_angle` | 419 | `Real.Angle.coe_sub` and `eb_coe_angle_eq_arg` at `a` and `b` (one line) |

All seven: `#print axioms` = `[propext, Classical.choice, Quot.sound]` (checked on a throwaway copy
`/tmp/ub/ER_UB_axioms.lean`; no `#print` lines were added to the unit file).

## 2. Leaves left

None in U-B.  No leaf was found false or under-hypothesised; every statement was proved exactly as frozen
(no hypothesis strengthened, no statement, name or docstring changed).  Reviewer's-eye items from ER_PLAN §4:
* B4 uses the `RegularPair u v` hypothesis only through `huv.1 : u ≠ 0`, `huv.2.1 : v ≠ 0` and
  `huv.2.2` (no negative multiple) — flat (positively collinear) pairs go through and give increment
  `principalAngle u v = 0`; antiparallel pairs are excluded by `huv.2.2`, which is exactly what makes every
  `c s` in the cone a `slitPlane` partner of `u` (`eb_regularPair_cone`).
* B5 needs `N ≠ 0` only for `euclideanLength N > 0` (to divide it out of the dot product); the path's
  nonvanishing `hc0` is used to recover `c s = |c s| • (cos θ s, sin θ s)` from the lift equation.

## 3. Helpers added (all prefixed `eb_`, all immediately before the leaf that uses them)

Before B4 (lines 220-273):
* `eb_regularPair_cone (huv : RegularPair u v) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hne : α ≠ 0 ∨ β ≠ 0) : RegularPair u (α • u + β • v)`
  — the key: `∀ r ≤ 0, α • u + β • v ≠ r • u` (cases `β = 0` / `β > 0`, `r − α = 0` / `< 0`); gives both
  nonvanishing (`r = 0`) and the no-negative-multiple clause.
* `eb_principalAngle_smul_right (hr : 0 < r) (u v) : principalAngle u (r • v) = principalAngle u v`
  (`planeComplex_smul`, `Complex.real_smul`, `mul_left_comm`, `Complex.arg_real_mul`).
* `eb_arg_planeComplex_normalize (hw : w ≠ 0) : (planeComplex (normalize w)).arg = (planeComplex w).arg`.
* `eb_coe_angle_eq_arg (hθ : IsLiftOn (fun s => normalize (c s)) θ a b) (hs : s ∈ Icc a b) (hcs : c s ≠ 0) :
  ((θ s : ℝ) : Real.Angle) = ((planeComplex (c s)).arg : Real.Angle)` — the lift-to-`arg` bridge, via
  `IsLiftOn.circleExp_coe`, `Real.Angle.toCircle_coe` (rfl: `toCircle ↑x = Circle.exp x`) and
  `Real.Angle.arg_toCircle`.  **U-C may find this useful directly** (it is what B7 is, pointwise).

Before B5 (lines 318-387):
* `eb_exists_cos_neg_of_gt_pi (hx : 0 ≤ cos x) (hy : 0 ≤ cos y) (hxy : π < y − x) : ∃ z ∈ Ioo x y, cos z < 0`
  — reduce `x` to `[−π/2, 3π/2)` with `toIcoMod`, so `x ∈ [2πk − π/2, 2πk + π/2]`; `cos y ≥ 0` forces
  `y > 2πk + π`; `z = 2πk + π` (`Real.cos_int_mul_two_pi_add_pi`).
* `eb_abs_sub_le_pi_of_cos_nonneg (hab) (hf : ContinuousOn f (Icc a b)) (hcos : ∀ s ∈ Icc a b, 0 ≤ cos (f s)) : |f b − f a| ≤ π`.
* `eb_planeDot_cos_sin (N) (t) : planeDot N (cos t, sin t) = euclideanLength N * cos (t − (planeComplex N).arg)`
  (`Complex.norm_mul_cos_arg`, `Complex.norm_mul_sin_arg`, `Real.cos_sub`, `linear_combination`).

## 4. Mathlib pitfalls met (this pin)

* `ContinuousAt.comp_continuousWithinAt` unifies `f x` with the *point* of the `ContinuousAt` argument
  first: with `ContinuousAt arg (cornerRotor u (c s))` it guessed `f := cornerRotor u`, `x := c s`.  Fix:
  pass `(g := Complex.arg) (f := fun s => cornerRotor u (c s))` explicitly.
* `push_neg` is deprecated in this toolchain (warning "Prefer using `push Not`"); `not_le.mp` / `not_lt.mp`
  after `by_contra` avoid the warning.
* Names that exist here: `Complex.norm_mul_cos_arg` / `norm_mul_sin_arg` (not `abs_mul_cos_arg`),
  `Complex.arg_real_mul (x) (hr : 0 < r) : arg (↑r * x) = arg x`, `Complex.real_smul : x • z = ↑x * z`,
  `Real.Angle.toCircle_coe` (rfl), `Real.Angle.arg_toCircle`, `toIcoMod_mem_Ico hp a b`,
  `toIcoMod_add_toIcoDiv_zsmul hp a b`, `Real.cos_add_int_mul_two_pi`, `Real.cos_int_mul_two_pi_add_pi`,
  `Real.cos_neg_of_pi_div_two_lt_of_lt (π/2 < x) (x < π + π/2)`, `intermediate_value_Icc` (for
  `Icc (f a) (f b)`) and `intermediate_value_Icc'` (for `Icc (f b) (f a)`), `mul_nonneg_iff_of_pos_left`.
* The `let`s in `secantRetract` do not unfold under `simp only [secantRetract]` reliably; `show` with the
  fully expanded `max/min` term works and is what B1/B2 do (verbose but robust).
* `Circle.isCoveringMap_exp.constOn_of_comp isPreconnected_Icc hcont (fun s hs s' hs' => ?_) ⟨hab, le_rfl⟩ ⟨le_rfl, hab⟩`
  (the pattern of `IsLiftOn.increment_eq`, TurnLift.lean:55) gives `g b = g a` from
  `Circle.exp (g s) = Circle.exp (g s')`; to prove the latter from a `Real.Angle` identity, rewrite both
  sides with `← Real.Angle.toCircle_coe` and `congr 1`.

## 5. For the assembler / executor

* Merge: take lines 173-426 of `ER_UB.lean` (from the §4 header through B7) in place of skeleton lines
  173-222; nothing else in the file was touched (diff against the skeleton: 7 removed lines, all `  sorry`;
  added lines are the 7 proof bodies and the 7 helper blocks).  Lines 1-173 and everything from
  `/-- B8 (proved)` to `end SM` are byte-identical to the skeleton.
* U-C consumes B4-B7 exactly as stated; nothing changed in their types.  B4's `hcone` wants, for each `s`,
  explicit `α β ≥ 0` not both zero with `c s = α • u + β • v` — A5/A6 deliver this with `α = k+1−s`,
  `β = s−k−½` (both zero only at no point of `[k+½, k+1]`), and A6 after `IsLiftOn.neg` (B6).
* `eb_coe_angle_eq_arg` is a general pointwise bridge (lift value ≡ `arg` of the vector modulo `2π`) that C4
  may use besides B7.
* Time: scratch iteration on `/tmp/ub/scratch.lean` (same four imports) compiles in ≈6 s; the unit file in ≈6 s.
