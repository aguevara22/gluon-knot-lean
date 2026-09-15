# U_G2 report — Unit G2 (`Θ`, curve pieces, integrals)

File: `work/drafts/rounding/U_G2.lean` (copy of Skeleton_FINAL.lean, 1594 lines after edits).
Check: `cd work/lean && lake env lean ../drafts/rounding/U_G2.lean` → **0 errors, 0 non-sorry
warnings, 42 "declaration uses sorry" warnings** (the 52 leaves of the skeleton minus the 10 of this unit).
`grep -c sorry`: 54 before → 44 after (the 2 extra tokens are prose in §8's header/docstrings, as in the skeleton).
`diff Skeleton_FINAL.lean U_G2.lean | grep '^<'` shows exactly the 10 removed `  sorry` lines; every
original declaration header line is still present byte-for-byte; no definition, statement, name or docstring
was touched. Nothing written under work/lean.

## Leaves proved (10/10)
`Θ_smooth`, `Θ_on_junction`, `Θ_on_straight`, `integral_tangentField_junction`,
`integral_tangentField_straight`, `integral_tangentField_period`, `curveMap_a`, `curveMap_b`,
`curveMap_on_junction`, `curveMap_on_straight`.

## Leaves left
none.

## Helpers added (26, all `theorem`, prefix `G2_`, inside `section global`, each placed immediately before the
first leaf that uses it)
Before `Θ_smooth`: `G2_θu_eq` (`θu n = θu 0 + Σ_{j<n} turn j`), `G2_sum_turn` (`Σ_{j<k} turn j = 2π rot`),
`G2_str_pos` (`0 < str j` for every `j : ℕ`, no `j < k` needed since the edge index is read mod `k`),
`G2_a_succ`, `G2_a_strictMono` (`StrictMono (a C ε)` on all of ℕ), `G2_a_nonneg`, `G2_a_le_one` (`j ≤ k`),
`G2_b_le_a` (`i < j → b i ≤ a j`), `G2_b_le_one` (`j < k`), `G2_b_le_b`, `G2_term_of_le` (a summand of `Θ`
with argument `≤ a i` is `0`), `G2_arg_b` (`(b i − a i)Λ/ℓ i = 1`; same content as `junction_arg_b`, which is
declared later in the file and hence unusable here), `G2_term_of_ge` (argument `≥ b i` gives the full turn),
`G2_sum_of_nonpos`, `G2_sum_of_ge` (sum = `2π rot` once `x ≥ b (k−1)`), `G2_sum_junction`
(`Σ_{i<k} = Σ_{i<j} turn i + turn j φ(...)` on `[a j, b j]`), `G2_sum_straight` (`= Σ_{i<j+1} turn i` on
`[b j, a (j+1)]`), `G2_Θ_eq` (**`Θ` on the CLOSED interval `[m, m+1]` equals
`θu 0 + 2π rot m + Σ_i turn i φ((t − m − a i)Λ/ℓ i)`**; at `t = m+1` both readings agree via `G2_sum_turn`),
`G2_G_smooth` (that local expression is `C^∞`).
Before `integral_tangentField_junction`: `G2_tangentField_junction` (`tangentField t = juncDir (θu j) (turn j)
((t − a j)Λ/ℓ j)` on the junction), `G2_integral_junction_upto` (`∫_{a j}^t T = (ℓ j/Λ) • ∫_0^{(t−a j)Λ/ℓ j}
juncDir`, for every `t ∈ [a j, b j]` — the substitution, via `intervalIntegral.integral_comp_mul_sub`).
Before `integral_tangentField_straight`: `G2_tangentField_straight` (`= vDir j` on the straight part),
`G2_integral_straight_upto` (`∫_{b j}^t T = (t − b j) • vDir j`).
Before `integral_tangentField_period`: `G2_curveMap_eq_add` (`curveMap t = curveMap s + Λ • ∫_s^t T`),
`G2_edgeLength_smul_vDir` (`|δ_j| • v_j = δ_j`), `G2_curveMap_a_aux` (`∀ j ≤ k, curveMap (a j) = A0 j`, by
induction along the pieces).

## Proof routes (where they differ from PLAN_FINAL §3)
- `Θ_smooth`: as planned (local case analysis), but organised through `G2_Θ_eq` on closed `[m, m+1]`: at
  `t₀` with `m = ⌊t₀⌋`, `Θ` agrees with the smooth expression `G_m` on the open set
  `(m − (1 − b(k−1)), m + 1)`; on the left piece both sides equal `θu 0 + 2π rot·m` (all profiles `1` resp. `0`).
  `ContDiffAt.congr_of_eventuallyEq` + `contDiff_iff_contDiffAt`.
- `Θ_on_straight` needs no `t = 1` case split: `G2_Θ_eq` with `m = 0` covers `[0, 1]` closed.
- `integral_tangentField_period` is NOT proved by the `2k`-piece telescoping of §3; instead
  `G2_curveMap_a_aux h k : curveMap (a k) = A0 k`, `a k = 1`, `A0 k = A0 0` (`(k : ZMod k) = 0`), and
  `curveMap 1 = A0 0 + Λ • ∫₀¹ T` give `Λ • ∫₀¹ T = 0`. The induction step of `G2_curveMap_a_aux` is exactly one
  telescoping step `A0 j + ε(u_j + v_j) + (|δ_j| − 2ε) v_j = A0 (j+1)` (closed by the `module` tactic after
  `uDir_succ`, `G2_edgeLength_smul_vDir`, `edge`, `Nat.cast_succ`). `sum_edges` / `sum_range_natCast_eq_sum_zmod`
  were therefore not needed.
- `integral_tangentField_junction` reuses `juncArc_one` (already proved in Unit A from `integral_juncDir`,
  `M_pos`) to get `ℓ j • ∫₀¹ juncDir = ε • (u_j + v_j)` by `add_left_cancel`, avoiding a second `field_simp`.
- `curveMap_on_junction` = `curveMap_a` + `G2_integral_junction_upto` + `Λ • (ℓ/Λ) • I = ℓ • I`, then `rfl`
  against `juncArc`. `curveMap_on_straight` = `curveMap_b` + `G2_integral_straight_upto`.

## Black boxes used (other units' sorries, as hypotheses)
Unit G1: `dirOf_θu`, `dirOf_θu_add_turn` (in the integral/curve leaves), `three_mul_lt_edgeLength`
(through `str_pos`/`G2_str_pos`, hence in everything incl. `Θ_smooth`). Unit A: `M_pos`, `integral_juncDir`
(through `juncArc_one`, in `integral_tangentField_junction` and downstream), `juncLen_pos` (through `ℓ_pos`,
everywhere). Unit P: none directly (`smoothTransition_symm` is proved; the strict-monotonicity/derivative
leaves are not needed by G2). `#print axioms` of every G2 leaf: `[propext, sorryAx, Classical.choice, Quot.sound]` — the
`sorryAx` is exactly these black boxes.

## Mathlib names (pin) — what worked / what did not
- `le_or_lt` is gone in this pin: use `le_or_gt`.
- `Finset.sum_range_add_sum_Ico (f) (h : m ≤ n)` (to_additive of `prod_range_mul_prod_Ico`) — works.
- `intervalIntegral.integral_comp_mul_sub (f) (hc : c ≠ 0) (d)` — `f` is EXPLICIT; the integrand must be
  syntactically `f (c * x - d)` (a `integral_congr` + `ring` step to reshape `(s − a)Λ/ℓ` first).
- `Int.floor_eq_iff`, `Int.self_sub_floor`, `Int.floor_add_one`, `Int.floor_intCast`, `Int.fract_add_one`,
  `Int.fract_intCast`, `Int.floor_le`, `Int.lt_floor_add_one` — all present.
- `ContDiff.sum`, `ContDiff.div_const`, `contDiff_iff_contDiffAt`, `ContDiffAt.congr_of_eventuallyEq`,
  `Filter.eventuallyEq_of_mem`, `Ioo_mem_nhds`, `strictMono_nat_of_lt_succ`, `mul_div_cancel₀ (a) (hb) : b * (a / b) = a`,
  `div_le_div_of_nonneg_right`, `intervalIntegral.integral_const`, `uIcc_of_le`, `right_mem_Icc` — all present.
- `module` tactic available and closes the vector identities (`abel` would not: different scalars on `v_j`).
- `simp [euclideanLength]` does not reduce `euclideanLength 0`; use `euclideanLength_formula` + `norm_num`.
- `beta_reduce` needed once (the `congr_of_eventuallyEq` goal shows `(fun t => …) t`).

## Notes for the assembler / executor
- No statement is false or under-hypothesised in this unit; every hypothesis of the 10 leaves is used
  (`hj : j < C.k` bounds the parameter interval inside `[0, 1]` and drives the `range k = range (j+1) ∪ Ico (j+1) k`
  split; `h : Admissible` supplies `Λ, ℓ, str > 0` and `|ϑ_j| < π`).
- `G2_str_pos` shows `str_pos`'s hypothesis `_hj : j < C.k` is unnecessary (the skeleton already marks it unused).
- `G2_arg_b` duplicates `junction_arg_b` (declared ~120 lines later); if the assembler wants to dedupe, move
  `junction_arg_b` up and replace `G2_arg_b` — not done here since statements/order are frozen.
- Unit X may find `G2_Θ_eq`, `G2_sum_of_ge`, `G2_sum_of_nonpos`, `G2_a_strictMono`, `G2_b_le_a`,
  `G2_curveMap_eq_add`, `G2_integral_junction_upto`, `G2_integral_straight_upto` directly useful
  (e.g. for `cover`, `iteratedDeriv_curveMap_a/b`, `curveMap_junction_mem_disc`).
