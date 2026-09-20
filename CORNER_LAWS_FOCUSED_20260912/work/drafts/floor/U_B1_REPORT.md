# U-B1 REPORT — unit B1 of rows 99/100 (PLAN_FINAL.md §4), 2026-09-15

File: `work/drafts/floor/U_B1.lean` (byte-identical copy of `Statements_FINAL.lean` + the two leaf proofs +
two `ub1_` helpers).  Check: `cd work/lean && lake env lean ../drafts/floor/U_B1.lean` → **0 errors**, 10 s warm;
21 `declaration uses sorry` warnings = the 21 leaves of the other units (23 − 2).  `grep -c sorry`: 25 before
(23 leaves + 2 mentions in doc comments) → 23 after.  `diff Statements_FINAL.lean U_B1.lean` removes exactly
the two `sorry` lines; everything else is added text.  `#print axioms` (temp copy): `ub_globalLift`,
`ub_exists_direction`, `ub1_exists_notMem_of_countable`, `ub1_neg_pi_lt_turn` all
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no policy axiom.

## Leaves proved (2 of 2)

| leaf | line | proof |
|---|---|---|
| `ub_globalLift` | 456 | `⟨CornerRounding.normalize_deriv_curveMap h t, fun _ hj ht => CornerRounding.Θ_on_junction h hj ht⟩` — both conjuncts are the accepted lemmas verbatim: `Round C D ε h = roundedWitness h` gives `.T t = normalize (deriv (curveMap C ε) t)`, `.θ = liftAt C ε`, `.a/.b = a/b C ε` by `rfl`, and `tangentField C ε t = dirOf (Θ C ε t)` by `rfl`. |
| `ub_exists_direction` | 482 | countability argument, see below (≈ 40 lines) |

Leaves left: none in this unit.

## Helpers added (prefix `ub1_`, placed immediately before `ub_exists_direction`, same section)

- `ub1_exists_notMem_of_countable {S : Set ℝ} (hS : S.Countable) {α β : ℝ} (hαβ : α < β) : ∃ φ ∈ Set.Ioo α β, φ ∉ S`
  (line 466).  Lebesgue measure: `Set.Countable.measure_zero` + `MeasureTheory.measure_sdiff_null` +
  `Real.volume_Ioo` + `MeasureTheory.nonempty_of_measure_ne_zero`.
- `ub1_neg_pi_lt_turn (C : PolyComp) (j : ZMod C.k) : -Real.pi < CornerRounding.turn C j` (line 476) —
  `Complex.neg_pi_lt_arg _`: `turn C j = principalTurn C.P j = principalAngle … = (cornerRotor …).arg`
  (RegularPairs.lean:54) so the bound holds with NO hypothesis (no `Regular`, no `Admissible`).

## Proof of `ub_exists_direction` (deviates from the PLAN §3 (B) B1 sketch — simpler, weaker hypotheses)

The plan's route ("finitely many classes mod π via `θu (j + k) = θu j + 2π rot`, `θu_last`, `rotationNumber_integer`,
`Set.Infinite.diff`") needs `Regular C.P` (for `rotationNumber_integer`) and `turn_bounds` (needs `Admissible`),
NEITHER of which the frozen statement supplies (it has only `hturn` and `hpos`).  Instead:

1. The first clause's forbidden set is `S := Set.range (fun p : ℕ × ℤ => θu C p.1 − p.2 * π)`, countable by
   `Set.countable_range` (`ℕ × ℤ` is countable) — so `φ ∉ S ⇒ ∀ j n, θu C j ≠ φ + n π` for ALL `j : ℕ`, without any
   periodicity or integrality of `rot`.
2. Case `∀ i, 0 < principalTurn`: the second clause is vacuous (`turn C j < 0` contradicts `hall j`); pick
   `φ ∈ Ioo 0 1 \ S`.
3. Case one negative turn at `i : ZMod C.k`: pick `φ ∈ Ioo (θu i.val) (θu i.val + turn i.val + π) \ S`; the interval
   is nonempty because `turn > −π` (`ub1_neg_pi_lt_turn`).  Any `j < C.k` with `turn C j < 0` has `(j : ZMod C.k) = i`
   (else `hother` gives `0 < turn`), hence `j = i.val` by `ZMod.val_cast_of_lt hj`.  For `n ≥ 0`,
   `φ + nπ ≥ φ > θu j`; for `n ≤ −1`, `φ + nπ ≤ φ − π < θu j + turn j`; either way `∉ Icc (θu j + turn j) (θu j)`
   (`linarith`/`nlinarith` with `Real.pi_pos`).

The hypothesis `hturn` is unused (linter warning at line 482, col 44; the binder name is part of the frozen
statement, so it stays).  `hi : principalTurn C.P i < 0` from `hpos` is also unused.

## Mathlib pitfalls (this toolchain, v4.34.0-rc2 pin)

- `le_or_lt` no longer exists → `le_or_gt`.
- `MeasureTheory.measure_diff_null` is deprecated → `measure_sdiff_null` (same statement).
- `push_neg` is deprecated in favour of `push Not` (not used in the final proof).
- `Cardinal.mk_Ioo_real` (Mathlib/Analysis/Real/Cardinality.lean) is NOT in the import closure of the SM modules;
  the cardinality route to "interval minus countable set" is unavailable — the measure route is.
- `Set.Countable.dense_compl` exists (Topology/Algebra/Module/Cardinality.lean) but needs the module instance
  arguments; the measure route is shorter.

## Notes for the assembler / executor / U-B2, U-B3

- `ub_globalLift` is definitional bookkeeping: U-B2/U-B3 may equally use `normalize_deriv_curveMap` and
  `Θ_on_junction` directly on `Round` (everything is `rfl`-transparent through `roundedWitness`).
- `ub_exists_direction` as stated is TRUE and proved; no counterexample, no missing hypothesis.  The direction
  `φ` is chosen non-constructively (measure/countability), which is what the statement asks (`∃ φ`).
- For U-B3 (`ub_exists_admissibleDirection`, which needs `dirOf φ ≠ uDir i` etc.): the first clause of
  `ub_exists_direction` already covers all `j : ℕ`, so `θu C j ≠ φ + nπ` for `j ≥ C.k` is available without the
  periodicity lemma; the translation `dirOf α = dirOf β ↔ α − β ∈ 2πℤ` is still U-B3's job.
- `ub1_neg_pi_lt_turn` may be useful elsewhere (it is the half of `turn_bounds` that needs no admissibility).
- No new definitions; no statement, name or docstring changed; nothing written under work/lean.
