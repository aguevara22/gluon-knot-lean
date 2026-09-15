# U_G3 report — Unit G3: the junction lifts `liftAt` (rounding row, Skeleton_FINAL §8, section `global`)

Prover: Claude (Fable 5.1) subagent, 2026-09-14. File: `work/drafts/rounding/U_G3.lean` (copy of
`Skeleton_FINAL.lean` with the four G3 leaves filled). Nothing written under `work/lean`.

## Result

| leaf | status | proof idea |
|---|---|---|
| `liftAt_strictMonoOn` | **proved** | `liftAt j = θu j + ϑ_j · φ ∘ g` with `g t = (t − a j)Λ/ℓ_j` affine, strictly increasing (`Λ, ℓ_j > 0`), `g([a j, b j]) ⊆ [0,1]` (`g (a j) = 0`, `g (b j) = 1` = `junction_arg_b`); Unit P's `smoothTransition_strictMonoOn` on `[0,1]`, then multiply by `ϑ_j > 0` |
| `liftAt_strictAntiOn` | **proved** | same, multiply by `ϑ_j < 0` (`mul_lt_mul_of_neg_left`) |
| `deriv_liftAt_ne_zero` | **proved** | `HasDerivAt (liftAt j) (ϑ_j · φ'(g t) · (1·Λ/ℓ_j)) t` by the chain rule (`HasDerivAt.comp`, `.const_mul`, `.const_add`, differentiability of `φ` from `Real.smoothTransition.contDiff (n := 1)`); on `(a j, b j)` we have `g t ∈ (0,1)`, so `φ'(g t) > 0` by Unit P's `deriv_smoothTransition_pos`; `ϑ_j ≠ 0` from `turn_bounds`; `Λ/ℓ_j > 0` |
| `tangent_injOn_junction` | **proved** | on `[a j, b j]` the unit tangent is `dirOf (liftAt j t)` (`liftAt_isLiftOn`, already proved in the skeleton). Two lift values differ by `ϑ_j·(φ(g s) − φ(g t))`, and `φ ∈ [0,1]` gives `|Δ| ≤ |ϑ_j| < π`; Unit A's `dirOf_injOn_of_lt_pi` gives equal lift values; injectivity of `liftAt j` on `[a j, b j]` from the strict monotonicity/antitonicity above (sign split via `lt_or_gt_of_ne (h.turn_ne j)`, as in the assembly) |

Leaves left in Unit G3: **none**.

## Helpers added (all `theorem`, prefixed `G3_`, placed immediately before the first leaf that uses them, inside `section global`)

- `G3_junction_arg_lt (h : Admissible C D ε) (j : ℕ) {s t : ℝ} (hst : s < t) : (s - a C ε j) * Λ C ε / ℓ C ε j < (t - a C ε j) * Λ C ε / ℓ C ε j`
- `G3_junction_arg_mem_Icc (h) (j) {t} (ht : t ∈ Icc (a C ε j) (b C ε j)) : (t - a C ε j) * Λ C ε / ℓ C ε j ∈ Icc 0 1`
- `G3_junction_arg_mem_Ioo (h) (j) {t} (ht : t ∈ Ioo (a C ε j) (b C ε j)) : (t - a C ε j) * Λ C ε / ℓ C ε j ∈ Ioo 0 1`
- `G3_hasDerivAt_liftAt (j : ℕ) (t : ℝ) : HasDerivAt (liftAt C ε j) (turn C j * (deriv Real.smoothTransition ((t - a C ε j) * Λ C ε / ℓ C ε j) * (1 * Λ C ε / ℓ C ε j))) t` — no `Admissible` hypothesis needed; the derivative is left in the un-simplified chain-rule shape `1 * Λ / ℓ` on purpose (it is what `HasDerivAt.div_const`/`mul_const` produce, so `.deriv` rewrites cleanly). Unit X may find this useful for `deriv`-of-`Θ` facts on the junction (`Θ = liftAt j` there by `Θ_on_junction`).
- `G3_abs_liftAt_sub_lt_pi (h) (j : ℕ) (s t : ℝ) : |liftAt C ε j s - liftAt C ε j t| < Real.pi` — for ALL real `s, t` (not only on the junction), since the profile is bounded in `[0,1]` everywhere.

The first three are the arithmetic of the profile argument `(t − a j)Λ/ℓ_j`; they are the natural companions of the skeleton's `junction_arg_b` and could be reused by Unit G2 (`curveMap_on_junction` substitution) and Unit X.

## Black boxes used (other units' leaves, used as hypotheses)

- Unit P: `smoothTransition_strictMonoOn`, `deriv_smoothTransition_pos`.
- Unit A: `dirOf_injOn_of_lt_pi`.
- Skeleton (proved): `Λ_pos`, `ℓ_pos`, `junction_arg_b`, `turn_bounds`, `liftAt_isLiftOn`.

## Mathlib names (pin) — all as expected, nothing missing or misspelled

`Real.smoothTransition.nonneg`, `.le_one`, `.contDiff {n : ℕ∞}` (differentiability via
`(Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero` — `ContDiff.differentiable` now takes
`n ≠ 0`, not `1 ≤ n`; with the implicit `n` left open, `by simp` cannot discharge `¬?n = 0`, so give `n` explicitly),
`div_lt_div_of_pos_right`, `div_le_div_of_nonneg_right`, `mul_lt_mul_of_pos_right/left`, `mul_lt_mul_of_neg_left`
(`b < a → c < 0 → c * a < c * b`), `HasDerivAt.sub_const` (an `alias` of `hasDerivAt_sub_const_iff`, works with
dot notation), `HasDerivAt.mul_const`, `.div_const`, `.comp`, `.const_mul`, `.const_add`, `StrictMonoOn.injOn`,
`StrictAntiOn.injOn`, `lt_or_gt_of_ne`, `abs_le`, `abs_mul`.
Note: in this pin `add_lt_add_left h c` produces `_ + c < _ + c`-shaped goals in a way that did not match
`θu + _ < θu + _` directly; I used `linarith` after `mul_lt_mul_of_pos_left/neg_left` instead.

## Notes for the assembler / executor

1. **Statements untouched.** Every `theorem/def/structure` line of `Skeleton_FINAL.lean` is byte-identical in
   `U_G3.lean` (checked by `diff` of the declaration headers: only the five `G3_` helper headers are added).
2. **Unused frozen hypothesis.** `deriv_liftAt_ne_zero` carries `(hj : j < C.k)` which the proof does not need
   (`liftAt` is defined and has nonzero derivative on `(a j, b j)` for every `j : ℕ`, given `Admissible`). To keep the
   build free of linter noise without renaming the frozen binder, the proof starts with `have _ := hj`. If the
   assembler prefers, the binder could be renamed `_hj` in a future statement revision; nothing depends on it.
3. `G3_abs_liftAt_sub_lt_pi` holds for all `s t : ℝ` — the junction lift's total range is the closed interval between
   `θu j` and `θu j + ϑ_j`, of length `|ϑ_j| < π`. This is the fact behind (b) "attaining each direction of that arc at
   exactly one parameter" and may be handy for Unit X (`order_τ` / direction arguments).
4. Compile: `cd work/lean && lake env lean ../drafts/rounding/U_G3.lean` → exit 0, **0 errors**, exactly 48
   `declaration uses sorry` warnings (the 52 skeleton leaves minus the 4 G3 leaves), no other warnings (~7 s wall).
   `grep -c sorry U_G3.lean`: 54 before → 50 after (the 4 removed are exactly the G3 leaf bodies; the remaining
   non-leaf hits are the word "sorry" in the §8 header comment and PLAN references).
