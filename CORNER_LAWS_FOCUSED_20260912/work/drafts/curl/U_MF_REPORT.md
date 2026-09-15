# U_MF_REPORT — Unit MF (U1: model + fit algebra) of cf:lem-curl

Prover subagent, 2026-09-14. File: `work/drafts/curl/U_MF.lean` (byte-identical copy of `Skeleton_FINAL.lean`
with the eleven Unit-M/F `sorry` bodies replaced; `diff Skeleton_FINAL.lean U_MF.lean` shows only those
eleven body replacements — no definition, structure, statement, name or docstring touched).

Check: `cd work/lean && lake env lean ../drafts/curl/U_MF.lean` → **0 errors**, 8 s. Remaining warnings are the
`sorry` notes of the other units (all at lines ≥ 676, Unit G onward) plus the skeleton's inherited `<;>` linter note
on `cModel_one` (now line 588, was 567). `grep -c sorry`: **56 → 45** (11 removed; the two non-leaf matches in the
header/§7 comments are untouched). `#print axioms` of each of the eleven leaves: `[propext, Classical.choice,
Quot.sound]` — no `sorryAx`.

## Leaves proved (11 / 11)

| leaf | proof idea |
|---|---|
| `hasDerivAt_cModel` | `HasDerivAt.prodMk` of `((hasDerivAt_pow 2 t).sub_const 1)` and `((hasDerivAt_id' t).sub (hasDerivAt_pow 3 t))`, each fixed up with `.congr_deriv (by norm_num)` |
| `hasDerivAt_bModel` | same pattern: `add_const 7`, `const_mul 3`, `div_const 11`; `const_mul (-3)` of `hasDerivAt_id'` |
| `cModel_double` | `s² = t²` ⇒ `(s−t)(s+t) = 0`; in the case `t = −s`, `s − s³ = −s + s³` ⇒ `s(1−s)(1+s) = 0`; `nlinarith` for the two factorisations, `linarith` for the cases |
| `fitA_add`, `fitA_smul` | `apply Prod.ext <;> simp [fitA] <;> ring` |
| `det_fitA_pos` | `fitA_u₀`, `fitA_v₀` (skeleton), then `det (x•v + y•u) u = x * det v u` by `simp only [det, Prod.*]; ring` |
| `fitA_ray_minus`, `fitA_ray_plus` | unfold everything, `ext <;> simp <;> field_simp <;> ring` with `hden : b*c + a*d ≠ 0` (positivity); identities `qx = H`, `1 + qy = 2bc/(bc+ad)`, `1 − qy = 2ad/(bc+ad)` |
| `yFit_bound` | `q·y = (bc − ad)/(bc + ad)` (field_simp), `abs_div`, `div_lt_one`, `abs_lt`, `linarith` with `0 < bc`, `0 < ad` |
| `xFit_pos` | `unfold xFit qFit; positivity` |
| `orderedRay_condition` | first clause `simp only [det, qFit, u₀, v₀, Prod.*]; norm_num`; second `det(av+bu, −cv+du) = (ad+bc)·det v u` by `ring`, then `hvu` |

All eleven identities were probed numerically first (Python, 2000 random `a,b,c,d > 0` and random orthonormal
`(v,u)` with `det v u = 1`; central-difference derivatives; grid search for `c(s) = c(t)`): all true as stated.
No leaf is false; no hypothesis is missing. (`orderedRay_condition` indeed needs no positivity, as PLAN_FINAL §3 says;
`det_fitA_pos` uses only `det v u = 1` and `0 < x`, `y` arbitrary.)

## Leaves left

None in this unit.

## Helpers added

None. All proofs are self-contained inside the leaf bodies (only the skeleton's already-proved `fitA_u₀` / `fitA_v₀`
are used, in `det_fitA_pos`).

## Mathlib pitfalls (pin 85e3a25e, Lean v4.34.0-rc2)

- `HasDerivAt.prodMk` is the current name (not `.prod`). `hasDerivAt_pow n x` gives the derivative as
  `↑n * x ^ (n - 1)` with a `ℕ`-cast and a `ℕ`-subtraction in the exponent: fix with `.congr_deriv (by norm_num)`
  (add `; ring` after `norm_num` when a rational factor remains, as in `bModel`).
- `HasDerivAt.sub` of `hasDerivAt_id'` and `hasDerivAt_pow` produces the Pi-form function `(fun x => x) - fun x => x ^ 3`
  and an instance path `Real.normedAddCommGroup.toAddCommGroup` / `RCLike.toInnerProductSpaceReal.toModule`;
  `simpa` and `convert … using 1` both fail on it (the latter leaves instance-equality goals). Passing the term to
  `exact`/a typed `have` after `.congr_deriv` works, since the function and instances are defeq.
- `ext` on a `Plane = ℝ × ℝ` goal works (`Prod.ext`); inside a `simp only [fitA, …]`-rewritten goal use
  `apply Prod.ext` to be safe. `Prod.smul_fst/snd`, `Prod.fst_add/snd_add`, `Prod.fst_neg/snd_neg`, `smul_eq_mul`
  are the `simp only` set that reduces `det`/`fitA` expressions to real arithmetic for `ring`.
- `field_simp` needs the denominator hypothesis in context (`hden : b * c + a * d ≠ 0`); `qFit = 4/11` is a numeral
  after `simp only [qFit]` and needs nothing.

## For the assembler / executor

- Unit MF's section of the file is lines 524-669 (`/-! ### Unit M …` to just before `/-! ### Unit G …`); the eleven
  bodies can be spliced into any other unit's copy verbatim — they reference only Mathlib and the skeleton's own
  `cModel`, `bModel`, `u₀`, `v₀`, `qFit`, `xFit`, `yFit`, `fitA`, `fitA_u₀`, `fitA_v₀`, `det`.
- Statement-level observation for Unit G/R consumers: `fitA_ray_minus/plus` are exact vector identities with the
  scalar `2ac/(bc+ad)/a` resp. `/c` written as a division chain; `field_simp`-style consumers will want
  `hden` and `ha.ne'`/`hc.ne'` in context when they rewrite these scalars.
