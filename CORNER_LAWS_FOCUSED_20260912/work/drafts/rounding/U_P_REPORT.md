# U_P_REPORT — Unit P (transition profile `φ = Real.smoothTransition`), 2026-09-14

File: `work/drafts/rounding/U_P.lean` (copy of `Skeleton_FINAL.lean`; only the four Unit P leaf bodies
were filled and two private helpers were added immediately before the leaves that use them, inside
`namespace CornerRounding`, section "Unit P"). No statement, name, docstring, definition or other unit's
`sorry` was touched. Nothing written under `work/lean`.

Check: `cd work/lean && lake env lean ../drafts/rounding/U_P.lean` → **0 errors**, 48 warnings, all of the form
`declaration uses sorry` from the 48 remaining leaves of the other units (A, G1, G2, G3, E, X). No warning
anchored in the Unit P region. `grep -c sorry U_P.lean`: **54 before → 50 after** (the 4 Unit P leaves; the two
remaining non-leaf occurrences are the section-header comment "all `sorry`" and the plan reference, as before).

`#print axioms` (checked on a scratch copy importing the same modules) for all four leaves:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

## Leaves proved (4 / 4)

| leaf | proof idea | lines |
|---|---|---|
| `smoothTransition_strictMonoOn` | for `s < t` in `[0,1]`: `φ s < φ t ⇔ f(s)f(1−t) < f(t)f(1−s)` (`div_lt_div_iff₀` + `linear_combination`). Cases `s = 0` / `t = 1` (one side is `0`, the other a product of positives); `0 < s < t < 1`: unfold `expNegInvGlue` to `exp(−x⁻¹)`, `← Real.exp_add`, `Real.exp_lt_exp`, and `1/t + 1/(1−s) < 1/s + 1/(1−t)` from two `inv_strictAnti₀`. No derivatives, as planned. | ~30 |
| `deriv_smoothTransition_pos` | `P_hasDerivAt_expNegInvGlue` (`f' = x⁻² f`), `g x = f(1−x)` by `HasDerivAt.comp` with `(hasDerivAt_id' t).const_sub 1`, quotient rule `HasDerivAt.fun_div` gives `HasDerivAt Real.smoothTransition _ t` (the function unifies by delta with `fun x => f x /(f x + f (1−x))`); numerator `= f(t) f(1−t) (t⁻² + (1−t)⁻²)` by `ring`, positive; denominator `(f+g)² > 0` by `pos_denom`. | ~25 |
| `iteratedDeriv_eq_zero_of_const_left` | `P_iteratedDeriv_eq_zero_of_eqOn_open` with `s = Iio x`, `closure_Iio`. | 4 |
| `iteratedDeriv_eq_zero_of_const_right` | same with `s = Ioi x`, `closure_Ioi`. | 4 |

## Helpers added (both `private`, prefixed `P_`, placed immediately before the leaf using them)

- `P_hasDerivAt_expNegInvGlue (x : ℝ) : HasDerivAt expNegInvGlue (x⁻¹ ^ 2 * expNegInvGlue x) x`
  — `simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 x` (before `deriv_smoothTransition_pos`).
- `P_iteratedDeriv_eq_zero_of_eqOn_open {f} (hf : ContDiff ℝ ∞ f) {s} (hs : IsOpen s) {c} (h : ∀ t ∈ s, f t = c)
  {m} (hm : 1 ≤ m) {x} (hx : x ∈ closure s) : iteratedDeriv m f x = 0`
  — `Set.EqOn.iteratedDeriv_of_isOpen` (Mathlib, IteratedDeriv/Lemmas.lean:441) gives
  `iteratedDeriv m f = iteratedDeriv m (fun _ => c)` on `s`; both sides continuous
  (`ContDiff.continuous_iteratedDeriv`, `ContDiff.continuous_iteratedDeriv'`), so `Set.EqOn.closure` extends to
  `closure s`; `iteratedDeriv_const` evaluates to `if m = 0 then c else 0`. No induction on `m` was needed
  (before `iteratedDeriv_eq_zero_of_const_left`; also used by `..._right`).

## Mathlib notes (pin 85e3a25e)

- Used, grep-verified: `div_lt_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b < c / d ↔ a * d < c * b`
  (Algebra/Order/GroupWithZero/Basic.lean:1451); `inv_strictAnti₀ (hb : 0 < b) (hba : b < a) : a⁻¹ < b⁻¹` (:1217);
  `HasDerivAt.fun_div` (Deriv/Inv.lean:168 — gives the `fun x => c x / d x` form; `HasDerivAt.div` gives `c / d`
  Pi-form); `HasDerivAt.const_sub`, `hasDerivAt_id'`, `HasDerivAt.congr_deriv`;
  `Filter.EventuallyEq.iteratedDeriv_eq` / `Set.EqOn.iteratedDeriv_of_isOpen` (IteratedDeriv/Lemmas.lean:436/441);
  `iteratedDeriv_const` (IteratedDeriv/Defs.lean:357); `ContDiff.continuous_iteratedDeriv {n : ℕ∞ω} (m : ℕ) (h)
  (hmn : m ≤ n)` — the obligation `(m : WithTop ℕ∞) ≤ ∞` is discharged by `by exact_mod_cast le_top`;
  `Set.EqOn.closure` (Topology/Separation/Hausdorff.lean:505); `closure_Iio`, `closure_Ioi`.
- Not needed after all: `Filter.EventuallyEq.iteratedDerivWithin_eq` / `iteratedDerivWithin_univ` (PLAN §3 route);
  the open-set lemma `Set.EqOn.iteratedDeriv_of_isOpen` is the direct tool.
- Pitfalls hit: `if_neg` is deprecated in this toolchain (use `simp [h]` / `ite_eq_right`); `Set.right_mem_Iic` /
  `Set.left_mem_Ici` do not exist here (use `Set.mem_Iic.mpr le_rfl`); dot-notation `.not_le` on `0 < s : ℝ`
  fails (`Real.lt` structure) — write `not_le.mpr h`; `convert … using 1` on `HasDerivAt`/`<` goals opens
  instance-equality side goals (`Real.instAddCommGroup = …`) — use `HasDerivAt.congr_deriv` / `LT.lt.trans_eq`.

## For the assembler / executor

- All four Unit P statements are true as stated; no hypothesis is missing. Downstream users:
  `liftAt_strictMonoOn/AntiOn` (G3) compose `smoothTransition_strictMonoOn` with an affine map;
  `deriv_liftAt_ne_zero` (G3) uses `deriv_smoothTransition_pos`; the witness fields `flat_ends` (§9) already
  cite `iteratedDeriv_eq_zero_of_const_left/right` with `liftAt_smooth` and `liftAt_const_left/right`.
- `P_iteratedDeriv_eq_zero_of_eqOn_open` is `private`; if Unit X wants it for `iteratedDeriv_curveMap_a/b`
  (flatness of `curveMap` from constancy of `tangentField` on an open interval), the assembler may drop the
  `private` keyword — its statement is more general than the two leaves (any open set, any point of its closure),
  so it also gives flatness at an *interior* endpoint of a straight piece when applied to `deriv curveMap`.
- The proofs are independent of every other unit (Mathlib only), so U_P.lean's Unit P block can be pasted verbatim
  into the merged file.
