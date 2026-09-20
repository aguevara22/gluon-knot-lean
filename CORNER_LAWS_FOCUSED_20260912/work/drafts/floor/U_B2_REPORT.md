# U-B2 report — leaf `ub_levelCount` (rows 99/100 floor lane, PLAN_FINAL.md §3 (B) / §4)

Prover: Claude (subagent), 2026-09-15 ~15:30Z.  File: `work/drafts/floor/U_B2.lean` (copy of
`Statements_FINAL.lean`, 1026 lines).  Check used: `cd work/lean && lake env lean ../drafts/floor/U_B2.lean`
— **0 errors**, 22 warnings `declaration uses sorry` (exactly the other units' 22 leaves: 23 − 1), no
other warning.  `grep -c sorry`: 25 before → 24 after (two hits are docstring mentions; 23 declarations
used `sorry` before, 22 now).  `diff Statements_FINAL.lean U_B2.lean` removes ONE line (`  sorry`, the
body of `ub_levelCount`) and adds the helper section + the proof body; no definition, statement, name
or docstring changed.

`#print axioms SM.ub_levelCount` = `[propext, Classical.choice, Quot.sound]` (checked on a scratch
copy; no `sorryAx`: the proof does NOT use the U-B1 black boxes `ub_globalLift` / `ub_exists_direction`,
only accepted Rounding.lean internals and Mathlib).

## Leaves

| leaf | status |
|---|---|
| `ub_levelCount` | **PROVED** |

Left: none in this unit.

## Helpers added (prefix `ub2_`, nested `section ub2` with `open Set CornerRounding`, placed immediately
before the leaf's docstring, inside the file's `noncomputable section`; 265 lines)

| helper | statement (informal) | used by |
|---|---|---|
| `ub2_dirOf_eq_iff` | `dirOf α = dirOf β ↔ ∃ n : ℤ, α = β + n·2π` (`Real.Angle.cos_sin_inj`, `angle_eq_iff_two_pi_dvd_sub`; converse `Real.cos/sin_add_int_mul_two_pi`) | leaf (tangency set = level set of `Θ`) |
| `ub2_level_ne` | `(∀ m : ℤ, x ≠ φ + mπ) → x ≠ φ + n·2π` (`m = 2n`) | junction lemmas |
| `ub2_floor_eq_of_no_level` | pure real: `u ≤ v`, no level `φ + 2πn` in `Icc u v` ⇒ `⌊(v−φ)/2π⌋ = ⌊(u−φ)/2π⌋` | negative junctions |
| `ub2_levelCount_strictMonoOn` | **the pure-real level-counting lemma**: `g` continuous and `StrictMonoOn` on `Icc a b`, `a < b`, `g b` not a level ⇒ `{t ∈ Ioo a b ∣ ∃ n, g t = φ + n·2π}` is finite with `(ncard : ℤ) = ⌊(g b−φ)/2π⌋ − ⌊(g a−φ)/2π⌋` (image under `g` = `lev '' Finset.Ioc ⌊x⌋ ⌊y⌋`, IVT `intermediate_value_Icc`, `InjOn.ncard_image`, `Int.card_Ioc`) | positive junctions |
| `ub2_locate` | `t ∈ Ico (a 0) (a m) → ∃ j < m, t ∈ Ico (a j) (a (j+1))` | leaf (crossing clause) |
| `ub2_level_in_junction` | a level of `Θ` met in `Ico (a j) (a (j+1))` is met in `Ioo (a j) (b j)` and equals `liftAt j t` (`Θ_on_junction`, `liftAt_a`, `Θ_on_straight`, `hφ`) | counts, leaf |
| `ub2_turn_pos_of_level` | a level met in the open junction forces `0 < turn C j` (`liftAt_strictAntiOn` + `harc` exclude the negative case) | counts, leaf |
| `ub2_deriv_liftAt_pos` | `0 < turn C j`, `t ∈ Ioo (a j) (b j)` ⇒ `0 < deriv (liftAt C ε j) t` (`G3_hasDerivAt_liftAt`, `deriv_smoothTransition_pos`, `Λ_pos`, `ℓ_pos`) | leaf (`CrossesPositively`) |
| `ub2_junction_count` | per junction `j < k`: levels of `Θ` in `Ico (a j) (a (j+1))` finite, `(ncard : ℤ) = ⌊x_{j+1}⌋ − ⌊x_j⌋`, `x_j = (θu j − φ)/2π` | cumulative |
| `ub2_cumulative_count` | induction on `m ≤ k`: levels in `Ico (a 0) (a m)` finite, `(ncard : ℤ) = ⌊x_m⌋ − ⌊x_0⌋` (`Set.ncard_union_eq` on the disjoint split at `a m`) | leaf |

Leaf assembly: `tangencySet (Round …) (dirOf φ) = {t ∈ Ico (a 0) (a k) ∣ ∃ n, Θ t = φ + n·2π}`
(`normalize_deriv_curveMap`, `a_zero`, `a_last`, `ub2_dirOf_eq_iff`; `(Round C D ε h).T/a/b/θ` are
`rfl` on `roundedWitness`), then `ub2_cumulative_count` at `m = k`, `θu_last`, `rotationNumber_integer`
(`D.regular`), `Int.floor_add_intCast` ⇒ `(ncard : ℤ) = rot`; the crossing clause from `ub2_locate`,
`ub2_level_in_junction`, `ub2_turn_pos_of_level`, `ub2_deriv_liftAt_pos`.

## Probe

Numerical probe (python, 20 000 random polygons with 3-7 junctions, random sign patterns, `rot ∈
{1,2}`, random `φ` satisfying `hφ`/`harc`): per positive junction the open-arc level count equals
`⌊x_{j+1}⌋ − ⌊x_j⌋`, per negative junction both are `0`, total = `rot` — 0 mismatches.  The leaf is
TRUE as stated, for ANY sign pattern of the turns (not only all-positive / one-dissent): `harc` for
every negative junction is what makes the telescoping work.

## Notes for the assembler / executor

- `hrot : 0 < rotationNumber C.P` is NOT needed by the proof (the count is the telescoped floor
  difference, an integer, automatically `≥ 0`); it is consumed by `have _ := hrot` to silence the
  unused-variable linter.  U-B3 may keep passing it.
- `ub2_levelCount_strictMonoOn` needs only the UPPER end value to be off the levels (the lower end
  is excluded automatically since the counted parameters are `> a`); stated that way.
- Under `open CornerRounding`, the bare name `turn` is AMBIGUOUS with the chirotope `SM.turn`
  (SM/Chirotope.lean:13) and fails to elaborate with `j : ℕ` ("expected ZMod ?m"); write
  `CornerRounding.turn C j` (done in the helpers).  Same hazard for anyone opening `CornerRounding`.
- Mathlib (pin of this repo): `Set.mem_setOf_eq` is deprecated → `Set.mem_ofPred_eq`; `push_neg` is
  deprecated → `not_le.mp` / `push Not`; `Set.ncard_image_of_injOn` does not exist — use
  `Set.InjOn.ncard_image`; `Int.card_Ioc a b : (Finset.Ioc a b).card = (b - a).toNat`;
  `intermediate_value_Icc : a ≤ b → ContinuousOn f (Icc a b) → Icc (f a) (f b) ⊆ f '' Icc a b`;
  `Set.ncard_union_eq` takes the two finiteness proofs as explicit auto-params.
- `θu C (j+1) = θu C j + turn C j` is `rfl` (structural recursion), used silently by `exact` after
  `rw [liftAt_b h]`.
- No black-box leaf is used; the leaf depends only on accepted SM/Rounding.lean + Mathlib.
