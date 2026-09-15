# ER_UA_REPORT — unit U-A of row 104 cb:embedded-rotation (traversal calculus, embeddedness, shifts, bridges)

Date: 2026-09-14.  File: `work/drafts/pldiscs/ER_UA.lean` (598 lines; was the 414-line skeleton).
Compile: `cd work/lean && lake env lean ../drafts/pldiscs/ER_UA.lean` — **0 errors**, ~6 s.
`grep -c sorry`: 28 before → **17 after** (= 12 `sorry` bodies of U-B/U-C + 5 textual mentions in the
file header and the §3/§4/§5 section comments; none in U-A).
Frozen parts checked byte-identical to `EmbeddedRotation_Skeleton.lean`: everything before the §3 header,
everything from the §4 header on, and each of the 11 U-A docstring+statement blocks (up to `:= by`).

## Leaves proved (11 of 11)

| leaf | name | axioms |
|---|---|---|
| A1 | `traversal_add_nat` | propext, Classical.choice, Quot.sound |
| A2 | `continuous_traversal` | same |
| A3 | `traversal_int_add` | same |
| A4 | `traversal_diag_const` | same |
| A5 | `traversal_diag_cone` | same |
| A6 | `traversal_cut_cone` | same |
| A7 | `Embedded.regular` | same |
| A8 | `Embedded.traversal_injective` | same |
| A9 | `Embedded.traversal_sub_ne_zero` | same |
| A10 | `Embedded.shift` | same |
| A11 | `embedded_of_generic_of_isEmpty_crossing` | same |

(`#print axioms` on each, run on a scratch copy; no `sorryAx`.)  Leaves left: **none**.
`#print axioms SM.cb_embedded_rotation` still shows `sorryAx` — only through the U-B/U-C leaves
(warnings at lines 361-471, all in §4/§5).

## Helpers added (3, all `ea_`-prefixed, placed immediately before the first leaf that uses them)

* `ea_traversal_eq_on_Icc (P) (k : ℤ) {y} (hy0 : (k:ℝ) ≤ y) (hy1 : y ≤ k + 1) :
  traversal P y = P (k : ZMod n) + (y - k) • edge P (k : ZMod n)` — the closed-piece affine formula
  (before A2). This is A3 in "absolute parameter" form; A3 is a one-line corollary, and A4-A6 use it
  directly (two instances each, then `push_cast; module`). The `y = k+1` endpoint is handled by
  `Int.floor_add_one`/`Int.fract_add_one` + `Int.floor_intCast`/`Int.fract_intCast` and `edge`.
  **U-C may find this form handier than A3** (no need to write `s = k + t`).
* `ea_continuous_of_continuousOn_Icc {E} [TopologicalSpace E] {f : ℝ → E}
  (hf : ∀ k : ℤ, ContinuousOn f (Icc (k:ℝ) (k+1))) : Continuous f` — generic gluing lemma (before A2):
  at a non-integer `x`, `Icc ⌊x⌋ (⌊x⌋+1)` is a neighbourhood; at an integer, `Icc (k-1) k ∪ Icc k (k+1)`
  is one and `ContinuousOn.union_of_isClosed` glues. No floor-topology lemmas needed.
* `ea_param_eq_one_of_edgePoint_eq_next {P} {i} (he : edge P i ≠ 0) {t} (ht : edgePoint P i t = P (i+1)) :
  t = 1` (before A8).

## Proof notes (where the proofs differ from the ER_PLAN §3 sketches)

* **A8 is simpler than planned**: no reduction of `x, y` to `[0, n)`. With `i = (⌊x⌋ : ZMod n)`,
  `j = (⌊y⌋ : ZMod n)`, `a = fract x`, `b = fract y`, the common point `edgePoint P i a = edgePoint P j b`
  lies on both segments. Case split on `adjacent i j` (the raw 3-way disjunction, not
  `adjacent_distinct_cases`): `j - i = 0` ⇒ `edgePoint_injective` (Crossings.lean) gives `a = b`, and
  `ZMod.intCast_eq_intCast_iff_dvd_sub` gives `⌊y⌋ - ⌊x⌋ = n·m`; `j - i = ±1` ⇒ the point is in
  `edgeSegment P j ∩ edgeSegment P (j+1) = {P (j+1)}` (`consecutive`), so the parameter on the *earlier*
  edge is `1`, contradicting `fract < 1`; `remote` ⇒ `remote_disjoint`. ~55 lines instead of 250.
* **A7**: with `e_i = r·e_{i−1}`, `r < 0`, the point `edgePoint P i t`, `t = 1/(1−r) ∈ (0,1]`, equals
  `edgePoint P (i−1) (1 + t r)` and `1 + t r = t ∈ [0,1]`, so it lies in the consecutive intersection
  `{P i}`, forcing `t • e_i = 0`.
* **A9**: `t − s = m·n` with `½ ≤ m n ≤ n − ½`, `n ≥ 3`: `m > 0` (real, by `nlinarith`), so `m ≥ 1` (ℤ,
  `omega`), so `m n ≥ n`, contradiction (`nlinarith`).
* **A10**: `remote (i+a) (j+a) ↔ remote i j` is `simpa only [remote, adjacent, add_sub_add_right_eq_sub]`;
  the `consecutive` clause is `h.consecutive (i + a)` after `rw [add_right_comm]`, closed by `exact`
  (the singleton `{shift a P (i+1)}` is *defeq* to `{P (i+1+a)}` but `simp only [shift]` does not unfold it).
* **A11**: `¬Disjoint` → `Set.not_disjoint_iff_nonempty_inter` → the anonymous constructor
  `⟨{i, j}, i, j, rfl, hr, hnd⟩ : Crossing P` → `hc.false`.
* Unused hypotheses: `hk : k < n` in A4/A5 and `hn : 3 ≤ n` in A7/A10 are not needed (the formulas hold
  for every `k`; A7 needs only `consecutive` and `edge_ne_zero`). The statements are frozen, so the file
  carries four `linter.unusedVariables` warnings on those binders — **do not rename them**, they are
  part of the fixed statements. These are the only warnings besides the 12 U-B/U-C `sorry` warnings.

## Mathlib pitfalls (this pin, 85e3a25e / Lean v4.34.0-rc2)

* Floor/fract names: `Int.floor_add_natCast`, `Int.fract_add_natCast`, `Int.floor_add_intCast`,
  `Int.fract_add_intCast`, `Int.floor_intCast_add`, `Int.fract_intCast_add`, `Int.floor_add_one`,
  `Int.fract_add_one`, `Int.floor_intCast`, `Int.fract_intCast`, `Int.self_sub_floor`, `Int.floor_add_fract`,
  `Int.floor_eq_iff`. **Not present**: `Int.floor_add_nat`, `Int.fract_add_int`, `Int.fract_sub_int`,
  `Int.floor_sub_int`, `Int.floor_eq_floor_iff`.
* `tendsto_fract_left'`/`tendsto_fract_right'` are **not** in scope under the four imports
  (Mathlib.Topology.Algebra.Order.Floor is not pulled in); avoided via the gluing helper.
* `push_neg` is deprecated on this pin ("Prefer `push Not`"); used `not_lt.mp` instead.
* `Set.disjoint_left` resolves to the root `disjoint_left` (fine to write either).
* The `module` tactic is available and closes every `Plane = ℝ × ℝ` identity in A4-A7 after `push_cast`
  (no need for coordinate `ext`).
* `push_cast` turns `((k : ℤ) : ZMod n)` into `(k : ZMod n)` and `((-1 : ℤ) : ZMod n)` into `-1`
  (`Int.cast_natCast`, `Int.cast_neg`, `Int.cast_one`), which is what makes the A4-A6 statements match.
* `linear_combination` works on `ZMod n` for the `j - i = ±1` index identities (as in
  `adjacent_distinct_cases`).

## For the assembler / executor

* Merge: take lines from `/-! ## §3 Unit U-A` up to (not including) `/-! ## §4 Unit U-B` of `ER_UA.lean`;
  the rest of the file is byte-identical to the skeleton. The three `ea_` helpers must travel with §3.
* U-C black boxes A1, A3-A6, A9 are now proved; U-C may also use `ea_traversal_eq_on_Icc` directly.
* No leaf was found false or under-hypothesised; the numerical checks of ER_PLAN §4 (A4-A6) are consistent
  with the proofs.  The `[NeZero n]` on A6 and the `hn` on A7/A10 are unused but harmless.
* For the port to `work/lean/SM/EmbeddedRotation.lean`: the four unused-variable warnings will remain
  unless the fixed statements are allowed to drop `hk`/`hn` (a statement change — decide at accept time).
