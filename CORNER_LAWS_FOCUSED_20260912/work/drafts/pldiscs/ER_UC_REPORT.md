# ER_UC_REPORT — unit U-C (boundary increments, supporting vertex), row 104 cb:embedded-rotation

Date: 2026-09-14. File: `work/drafts/pldiscs/ER_UC.lean` (712 lines; skeleton was 411).
Compile: `cd work/lean && lake env lean ../drafts/pldiscs/ER_UC.lean` — **0 errors**, exit 0.
`grep -c sorry`: 28 before → 23 after (the 5 U-C leaf `sorry`s removed; 18 `declaration uses sorry`
warnings remain = 11 U-A leaves + 7 U-B leaves, lines 114-216; the other 5 counted `sorry`s are words in
docstrings/comments). `#print axioms SM.cb_embedded_rotation` still shows `sorryAx`, entering only through
the U-A / U-B leaves.

## Leaves proved (5 of 5)

| leaf | line | proof route | black boxes used (statements only) |
|---|---|---|---|
| C1 `diag_increment` | 316 | induction on `m < n`: `Θ(m, m+½) = Θ(0, ½) + Σ_{k<m} ϑ_{k+1}` via the two step helpers; last constant piece at `k = n−1` (`Nat.cast_pred`); reindex `Σ_{k<n−1} ϑ_{k+1} = Σ_{k<n} ϑ_k − ϑ_0` by `Finset.sum_range_succ'` + `sum_range_natCast_eq_sum_zmod` | A4, A5, B4 |
| C2 `cut_increment` | 358 | cut path in region; A6 gives the negated cone path; `IsLiftOn.neg` (B6) with `neg_neg`; B4 with `hreg 0` (`zero_sub` turns `0 − 1` into `−1`) | A6, B4, B6 |
| C3 `top_increment_eq_left` | 409 | `traversal P n = traversal P 0` (A1 at `x = 0`); `secantDir P (s,n) = −secantDir P (0,s)` by `normalize_neg`/`neg_sub`; B6 on the left lift; `IsLiftOn.increment_eq` | A1, B6 |
| C4 `left_increment` | 469 | `traversal P 0 = P 0` by `simp [traversal, edgePoint]`; nonvanishing from A9 at `(0,t)`; half-plane from the helper below; B5 for `|I| ≤ π`; B7 for the angle, endpoints `½ e_0` (A3, `k = 0`) and `−½ e_{−1}` (A1 at `x = −½`, A3 with `k = −1`, `t = ½`); `Complex.arg_neg_coe_angle`, `Complex.real_smul`, `Complex.arg_real_mul`, `principalTurn_coe_angle`, `abel` | A1, A3, A9, B5, B7 |
| C5 `exists_supporting_vertex_turn_ne_zero` | 530 | lexicographic minimum via `Finset.exists_min_image` on `toLex ((P j).1, (P j).2)` and `Prod.Lex.le_iff`; `N = (1,0)`; zero turn ⇒ `e_i = r e_{i−1}`, `r > 0` (`principalAngle_eq_zero_iff` with `Embedded.edge_ne_zero` — A7 is NOT needed); x-minimality forces both x-components zero, y-minimality among leftmost vertices forces `e_{i−1}` down / `e_i` up, so `e_{i−1} = 0`, contradiction | none (only `Embedded.edge_ne_zero`) |

Leaves left: none in U-C.

## Helpers added (all prefixed `ec_`, placed immediately before the leaf using them, statements of the
leaves untouched — verified by `diff` against `EmbeddedRotation_Skeleton.lean`: the only removed lines are
the five `sorry`s)

| helper | line | statement |
|---|---|---|
| `ec_isLiftOn_congr` | 247 | `IsLiftOn u θ a b → (∀ s ∈ Icc a b, u s = u' s) → IsLiftOn u' θ a b` |
| `ec_diag_lift` | 253 | `0 ≤ a → b ≤ n − ½ → IsLiftOn (fun s => secantDir P (s, s+½)) (fun s => Θ (s, s+½)) a b` |
| `ec_diag_const_step` | 263 | `k < n → Θ (k+½, k+½+½) = Θ (k, k+½)` (A4 + `IsLiftOn.increment_eq_zero_of_const`) |
| `ec_diag_cone_step` | 276 | `k+1 < n → Θ (k+1, k+1+½) − Θ (k+½, k+½+½) = principalTurn P (k+1)` (A5 + B4 with `hreg (k+1)`, `add_sub_cancel_right`) |
| `ec_planeDot_add_right` | 446 | `planeDot N (u + v) = planeDot N u + planeDot N v` |
| `ec_planeDot_traversal_sub_nonneg` | 453 | `IsSupportingVertex P N 0 → 0 ≤ planeDot N (traversal P t − P 0)` (convex combination of `P ⌊t⌋`, `P (⌊t⌋+1)`, straight from the definition of `traversal` — no A3 needed) |

## Hypotheses of the frozen statements that turned out unused (linter warnings, harmless)

* `h : Embedded P` is unused in C1, C2, C3 (the diagonal/cut/top increments need only A1/A4/A5/A6, B4,
  B6 and `hreg`); `hn : 3 ≤ n` is unused in C5. The four `Variable name … is not explicitly referenced`
  warnings at lines 317, 359, 409, 530 are exactly these. Statements are frozen, so they stay.
* C5 does not need `Embedded.regular` (A7): `principalAngle_eq_zero_iff` only needs both edges nonzero.

## Mathlib / toolchain pitfalls met (v4.34.0-rc2, Mathlib pin 85e3a25e)

* `Set.mem_setOf_eq` is deprecated in this pin (suggests `Set.mem_ofPred_eq`). Region membership is
  proved lemma-free: `refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> linarith` (the anonymous constructor
  sees through `secantRegion`; `dsimp only` reduces the `(s, t).1/.2` projections).
* `rw [Int.cast_neg, Int.cast_one]` rewrites only one cast target: with `((−1:ℤ):ℝ)` and
  `((−1:ℤ):ZMod n)` both present, the `ZMod` one survives and `edge P ↑(−1)` never simplifies. Use
  `push_cast at h` (rewrites all).
* `fun_prop` proves all the `Continuous`/`ContinuousOn` side goals (pairs, affine combinations of `•`).
* `module` closes the vector identities (`traversal P t − P 0` as a convex combination; `P(−1) + ½e_{−1}
  − P 0 = −½ e_{−1}` after `simp only [edge, neg_add_cancel]`).
* `Finset.exists_min_image Finset.univ (fun j => toLex (…)) Finset.univ_nonempty` + `Prod.Lex.le_iff` +
  `simpa` gives the lexicographic minimum directly; `Nonempty (ZMod n)` comes from `[NeZero n]`.
* `Complex.arg_real_mul` needs the `(↑r * z)` form: rewrite `planeComplex_smul` then `Complex.real_smul`.
* `linarith` treats `Θ (…)` as atoms; after `push_cast` the `((m+1:ℕ):ℝ)` forms match the step helpers.

## For the assembler / executor

* Merge by leaf: U-C's block is lines 244-588 of `ER_UC.lean` (§5, including the six helpers); §1-§4 and
  §6 are byte-identical to the skeleton. After merging U-A and U-B, `#print axioms` should drop `sorryAx`.
* The helpers are generic (no `Embedded` hypothesis); `ec_diag_lift` / `ec_isLiftOn_congr` may be useful
  to U-B/U-A provers but are not needed by them.
* No leaf was found false or under-hypothesised; nothing was probed numerically because every step is a
  direct instance of the plan's §3 sketch.
