# W3S_S1a_REPORT — unit S1a of the U8R sweep (the non-singular cut: the first 8 leaves of PLAN §3/S1)

2026-09-14.  File: `work/drafts/frontrows/W3S_S1a.lean` (15,812 lines) = `W3_U8R_Skeleton.lean` (15,586) + ONE inserted
helper block + the bodies of the 8 leaves of unit S1a.  `diff W3_U8R_Skeleton.lean W3S_S1a.lean` = 9 hunks: the
insertion `14866a14867,14941` (the block `/-! ### S1a helpers -/ section S1aHelpers … end S1aHelpers`, placed
immediately before the docstring of `fibreListBefore_eq_of`, inside `namespace U8R` / `section SweepLeaves`, so
the section variable `F : SmoothFront` is in scope) and 8 one-line-for-many replacements of ` := sorry` by
` := by …` — the 8 removed lines are exactly the statement tails ending in `:= sorry`; every statement, name,
docstring and definition is byte-identical to the skeleton.  No import added, no other unit's `sorry` touched.

Compile: `cd work/lean && lake env lean ../drafts/frontrows/W3S_S1a.lean` — **0 errors, exit 0**, ~45 s;
`grep -c sorry`: **58 before → 50 after** (50 `declaration uses sorry` warnings = the 4 front-move leaves + the 46
sweep leaves of the other units).  `#print axioms` of the 8 leaves on a probe copy (the file truncated after
`exists_eta_fibre_near`): each is `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.  No warning is emitted
inside the inserted block or the 8 proofs (the deprecated `if_neg` / `Set.mem_setOf_eq` were avoided).

## 1. Leaves proved (8/8; line = line of the theorem header in `W3S_S1a.lean`)

| line | leaf | proof |
|---|---|---|
| 14945 | `fibreListBefore_eq_of` | `List.perm_ext_iff_of_nodup` (both nodup, same members) gives `fibreListBefore ~ L`; `List.Perm.eq_of_pairwise` (core: antisymmetry needed only on members of the two lists) with `s1a_beforeLE_antisymm`, `fibreListBefore_pairwise`, `hsort` |
| 14958 | `fibreListAfter_eq_of` | mirror with `s1a_afterLE_antisymm` |
| 14973 | `fibreListAfter_eq_fibreListBefore` | `fibreListAfter_eq_of` applied to `L := fibreListBefore`; the `afterLE`-sortedness from `Pairwise.and` (nodup ∧ `beforeLE`) + `Pairwise.imp_of_mem`: distinct members of the fibre have distinct heights (`snd_injOn_totalFibre`), so `beforeLE` holds through its strict first component (`Prod.Lex.toLex_le_toLex`), which is also `afterLE` |
| 14991 | `cutBefore_eq_map_dirBit` | `s1a_flatMap_eq_map` + `s1a_beforeBits_eq` |
| 14997 | `cutAfter_eq_cutBefore` | the two previous + `s1a_afterBits_eq` |
| 15004 | `entriesBefore_eq_of_notMem_singX` | `s1a_flatMap_eq_map`; `(List.range [b].length).map (fun j => (p, j)) = [(p, 0)]` is `rfl` |
| 15015 | `regular_local_graph` | `δ` from `Metric.continuousAt_iff` on `xvel` (`xvel F i t₀ ≠ 0`: `xvel_ne_zero_of_not_isCusp`; `xvel = 0` at a cusp: `isCusp_iff_xvel_eq_zero`); injectivity by Rolle (`exists_hasDerivAt_eq_zero`, `hasDerivAt_x`) as in `injOn_x_arc`; for `δ' ≤ δ`: `ContinuousOn.strictMonoOn_of_injOn_Icc'` on `[t₀ − δ'/2, t₀ + δ'/2]` gives strict mono or anti, `η := min` of the two gaps to `x(t₀)`, preimage by `intermediate_value_Icc` / `intermediate_value_Icc'` |
| 15090 | `exists_eta_fibre_near` | `U :=` the open set of parameters within `δ` (mod `1`) of a fibre point over `x₀` on the same circle (`isOpen_biUnion`, `isOpen_iUnion`, discrete `Fin c`, `isOpen_lt`); `K := (univ ×ˢ Icc 0 1) \ U` compact (`IsCompact.diff`); `|x − x₀| > 0` on `K` (a zero would put `SameParam.rep q` in the fibre and `q` in `U` with `n = −⌊q.2⌋`); `IsCompact.exists_forall_le'` (handles `K = ∅`) gives `η`; a fibre point over `x` with `|x − x₀| < η` cannot lie in `K`, so it lies in `U` |

The arc machinery of §G (`exists_arc_mem`, `strictMonoOn_x_of_isLeftCusp`) was NOT needed for `regular_local_graph`:
the local statement follows from `x' ≠ 0` near `t₀` + Rolle + the IVT directly.

## 2. Helpers added (block lines 14867-14941, all `theorem`, prefix `s1a_`)

* `s1a_eq_of_ht_slope_eq` — two fibre points over `x₀` with equal `ht` and equal `slope` are equal (`SameParam.eq_of_mem_Ico`, `slope_ne_of_isDouble`).
* `s1a_beforeLE_antisymm`, `s1a_afterLE_antisymm` — antisymmetry of the two comparators on the fibre (`toLex.injective`, `Prod.mk.injEq`, `neg_inj`).
* `s1a_flatMap_eq_map {α β} (L f g) (h : ∀ p ∈ L, f p = [g p]) : L.flatMap f = L.map g` — generic list lemma (induction).
* `s1a_not_isCusp_of_mem_totalFibre (hx : x₀ ∉ singX F) (hp : p ∈ totalFibre F x₀) : ¬ F.IsCusp p` — from `regular_of_notMem_singX`.
* `s1a_beforeBits_eq`, `s1a_afterBits_eq` — `beforeBits p = [dirBit p]`, `afterBits p = [dirBit p]` over a non-singular `x₀`.
* `s1a_continuous_eval : Continuous (fun q : Param F.c => F.eval q)` — joint continuity on `Fin c × ℝ` through the discrete first factor (`ContinuousAt.congr` on the open set `Prod.fst ⁻¹' {i}`).  Reusable by S1b/S2/S3/S6 (there was no such lemma in the file; Mathlib has no `continuous_uncurry_of_discreteTopology` in this pin).

## 3. Pitfalls / notes for the merger and the other units

1. `toLex_le_toLex` lives in `Prod.Lex` (`Prod.Lex.toLex_le_toLex : toLex x ≤ toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 ≤ y.2`); use it with `simp only` so the pair projections reduce.
2. `List.Perm.eq_of_pairwise` (Lean core) takes the antisymmetry hypothesis restricted to members (`∀ a b, a ∈ l₁ → b ∈ l₂ → le a b → le b a → a = b`) as its FIRST explicit argument and the permutation LAST; Mathlib's `Perm.eq_of_pairwise'` needs a global `Std.Antisymm`, which `beforeLE` does not have.
3. `List.Nodup` is not reducible for dot-notation: state `have hnd : L.Pairwise (fun p q => p ≠ q) := fibreListBefore_nodup F x₀` before `hnd.and …`.
4. `if_neg` is deprecated in this toolchain (warning); `simp [beforeBits, hl, hr]` with the two negations discharges the `if`s.  `Set.mem_setOf_eq` is deprecated in favour of `Set.mem_ofPred_eq`.
5. `IsCompact.exists_forall_le' (hs) (hf : ContinuousOn f s) (hf' : ∀ b ∈ s, a < f b) : ∃ a', a < a' ∧ ∀ b ∈ s, a' ≤ f b` covers the empty-set case, so no case split on `K.Nonempty` is needed.
6. The compact set in `exists_eta_fibre_near` uses ALL `n : ℤ` in the "close modulo the period" condition (an open union over `ℤ`), not only `n ∈ {−1, 0, 1}`; the leaf's `∃ n : ℤ` is delivered directly.
7. Iteration recipe used: truncate the file after `exists_eta_fibre_near` (line 14908 of the skeleton) and append `end SweepLeaves / end / end U8R / end Leaves / end FrontRows / end SM`; ~42 s per compile.  Scratch material (patch script, helper and proof texts): `/tmp/s1a/`.

No leaf of this unit needed a changed statement; none of PLAN §6's doubts concerns S1a.
