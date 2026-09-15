# W3S_S4b — unit S4b of the U8R sweep (the last 8 leaves of PLAN §3/S4): REPORT

2026-09-14, prover for unit S4b.  File: **`work/drafts/frontrows/W3S_S4b.lean`** (16,084 lines) = `W3_U8R_Skeleton.lean`
(15,586) + ONE helper block `/-! ### S4b helpers -/ section S4bHelpers … end S4bHelpers` (375 lines, 40 declarations,
all named `s4b_…`, inside `namespace U8R`, `section SweepLeaves`, placed right after the last S4a leaf
`hybridCut_eq_cutBefore` and immediately before my first leaf `cutBefore_first`) + the 8 leaf bodies (122 lines) +
ONE relocation (§1, the merger MUST apply it).  Compile: `cd work/lean && lake env lean ../drafts/frontrows/W3S_S4b.lean`
— **0 errors, exit 0, 42.8 s**; `grep -c sorry`: **58 before → 50 after** (the 50 = 4 front-move leaves + 46 sweep
leaves of the other units; 50 `declaration uses sorry` warnings, no other warning from my code).  Every statement,
name and docstring of the skeleton is byte-identical (checked: the multiset of declaration header lines differs from the
skeleton's only by `:= sorry` → `:=` on exactly my 8 leaves; the docstrings and statements of the 8 leaves and of
`oword`/`oword_letters` are identical strings).  No import added; nothing under `work/lean` touched; no other unit's
sorry touched.

## 0. Verdict

**All 8 leaves of S4b are proved**: `cutBefore_first`, `cutAfter_last`, `run_take_eq_hybrid`, `word_closed`,
`word_ne_nil`, `cuspCount_eq`, `downCountSyn_eq`, `cut_word_colAt`.  Nothing left.  The PLAN §6 doubt about
`cutBefore_first`/`cutAfter_last` ("the min of `x` on the front is a left cusp") is confirmed TRUE and proved; the
compactness argument cost ≈ 90 lines of helpers, not the 450 estimated.  Total ≈ 500 lines against the 1.1k estimate.

`#print axioms` (probe copy `/tmp/s4b/Ax.lean`): `cuspCount_eq`, `s4b_exists_xmin`, `s4b_hybridCut_drop_cusp`,
`s4b_sum_dcont` : `[propext, Classical.choice, Quot.sound]` (no sorry at all).  The other seven leaves:
`[propext, sorryAx, Classical.choice, Quot.sound]` — `sorryAx` ONLY through the black boxes listed in §3
(`word_ne_nil` inherits it through `oword`, whose definition contains `word_closed`).

## 1. THE RELOCATION the merger must apply (structural, statements untouched)

The skeleton states the leaf `word_closed` (L14852) inside `section SweepDefs`, BEFORE every leaf its proof needs
(`run_take_eq_hybrid` L15050, S4a's `step_hybrid`/`hybridCutStrict_eq_cutAfter`, S1's `cutAfter_eq_cutBefore_of_gap`,
my `cutAfter_last`), and `oword` (L14855) is built from it.  Lean has no forward references, so the proof cannot live at
L14852.  In my file the nine skeleton lines 14849-14857 —

```
/-! #### S4 leaves: the word is closed; its counts -/
<blank>
/-- LEAF (S4): the word of the sweep is closed. -/
theorem word_closed : (word F).Closed := sorry
<blank>
/-- the closed word of the sweep -/
def oword : OWord := ⟨word F, word_closed F⟩
<blank>
@[simp] theorem oword_letters : (oword F).letters = word F := rfl
```

— are REMOVED from `section SweepDefs` and re-inserted VERBATIM (only `:= sorry` of `word_closed` replaced by its
proof) inside `section SweepLeaves`, immediately after the leaf `run_take_eq_hybrid` and before the docstring of
`word_ne_nil` (my file L15465-L15485).  Both sections have `variable (F : SmoothFront)`, so the three declarations
elaborate to the same terms (`SM.FrontRows.U8R.word_closed`, `.oword`, `.oword_letters`, same types); the first use of
`word_closed` in the skeleton after L14857 is `word_ne_nil` (L15054) and then `ΦFun` (S5, L15091), both after the new
position, so nothing else moves.  `diff W3_U8R_Skeleton.lean W3S_S4b.lean` = 9 hunks: `14849,14857d` (the removal),
`15038a15030,15404` (the helper block), and one `c` hunk per leaf body, the `run_take_eq_hybrid` hunk
`15051c15451,15485` also carrying the re-inserted block.  If the merger prefers to keep the skeleton's layout, the
alternative is to move the leaf `word_closed` + `oword` + `oword_letters` after `run_take_eq_hybrid` in the merged file
exactly as here; there is no way to prove `word_closed` at L14852.

## 2. The leaves (all in `SM.FrontRows.U8R`; `n := (events F).length`)

| leaf | proof route | black boxes used |
|---|---|---|
| `cutBefore_first` (17 lines) | `s4b_exists_xmin` (compactness on each circle's `Icc 0 1` + `Finset.exists_min_image` over `Fin c`; periodicity through `s4b_eval_fract`) gives a point `p` of `[0,1)` with globally minimal `x`; `s4b_isCusp_of_min` (`IsLocalMin.hasDerivAt_eq_zero` with `hasDerivAt_x`, `isCusp_iff_xvel_eq_zero`) makes it a cusp, hence an event `inl c`; `colX 0 ≤ evX (inl c)` by sortedness (`s4b_colX_le`) and `≥` by minimality, so `colX 0 = x_min`; every fibre point over `x_min` is again a global min, hence a cusp, and a LEFT cusp (`s4b_isLeftCusp_of_min`: a right cusp would have `x` strictly increasing up to it, `rightCusp_x_local`), so all `beforeBits = []` (`List.flatMap_eq_nil_iff`) | S2 `rightCusp_x_local`; S4a `events_pairwise_lt` |
| `cutAfter_last` (19) | mirror with the max (`s4b_exists_xmax`, `s4b_isRightCusp_of_max` via `leftCusp_x_local`); `colX (n−1) = x_max` since `evIdx (inl c) ≤ n − 1` | S2 `leftCusp_x_local`; S4a `events_pairwise_lt` |
| `run_take_eq_hybrid` (11) | induction on `k`; base: `hybridCut_eq_cutBefore` with the vacuous "lowest" hypothesis (`s4b_hbot`) + `cutBefore_first`; step: `List.take_succ_eq_append_getElem`, `run_append`, `letterAt_eq`, `letterAt_word`, `step_hybrid`, then `s4b_hybridCutStrict_eq_next` (§3) | S4a `step_hybrid`, `hybridCut_eq_cutBefore`, `hybridCutStrict_eq_hybridCut`, `hybridCutStrict_eq_cutAfter`, `events_pairwise_lt`; S1 `cutAfter_eq_cutBefore_of_gap` |
| `word_closed` (11) | `word F = take (n−1) ++ [word[n−1]]`, `run_take_eq_hybrid` at `n−1`, `step_hybrid`, `hybridCutStrict_eq_cutAfter` (the last event is topmost at its `x`: `s4b_htop` with a vacuous hypothesis), `cutAfter_last` | as above |
| `word_ne_nil` (3) | `events F ≠ []` from `mem_events (inl (someCusp F))`, `List.map_eq_nil_iff` | none (but `oword` mentions `word_closed`) |
| `cuspCount_eq` (12) | `countP_map`, `Perm.countP_eq` with `mergeSort_perm`, `countP_eq_length_filter`; the filtered `univ.toList` is a permutation of `univ.toList.map Sum.inl` (`perm_ext_iff_of_nodup`, `s4b_isCrossing_letterOf_inl/inr`), `Finset.length_toList`, `card_univ`, `card_cusp` | none — sorry-free |
| `downCountSyn_eq` (7) | `s4b_downCountFrom_drop` at `k = 0` (the run of `downCountFrom` along the hybrid cuts, backward induction on `n − k`) turns the count into `((events F).map s4b_dcont).sum`; `s4b_sum_dcont` evaluates it: `s4b_dcont (inr q) = 0`, `s4b_dcont (inl c) = if cuspDisc c < 0 then 1 else 0` (`s4b_dcont_inl`: left cusp by the `l` bit, right cusp by the head of `beforeBits c` read through `s4b_hybridCut_drop_cusp`), `Fintype.sum_sum_type`, `Finset.sum_coe_sort`, `Finset.card_filter`, `IsDownCusp ↔ cuspDisc < 0` on cusps | S4a `step_hybrid`, `hybridCut_eq_cutBefore`, `hybridCutStrict_eq_hybridCut`, `hybridCutStrict_eq_cutAfter`, `events_pairwise_lt`; S1 `cutAfter_eq_cutBefore_of_gap`; S2 (through `cutBefore_first`) |
| `cut_word_colAt` (42) | `s4b_filter_length_iff` on the sorted events: `j < colAt x ↔ colX j < x` for `j < n`; case `colAt x < n`: `x < colX (colAt x)` (`colX ∈ singX`, `x ∉ singX`), `cut = hybridCut` (`run_take_eq_hybrid`), `= cutBefore (colX k)` (`hybridCut_eq_cutBefore`, `s4b_hbot`), `= cutAfter x` (`cutAfter_eq_cutBefore_of_gap` over the event-free gap `(x, colX k)`), `= cutBefore x` (`cutAfter_eq_cutBefore`); case `colAt x = n`: `cut_length (word_closed F)`, gap `(colX (n−1), x)`, `cutAfter_last` | S4a `hybridCut_eq_cutBefore`, `events_pairwise_lt`; S1 `cutAfter_eq_cutBefore_of_gap`, `cutAfter_eq_cutBefore`; + everything `word_closed` uses |

NOT used from S4a: `evKey_injective`, `colX_mono` (re-derived as `s4b_colX_le` from `events_pairwise_lt`),
`evPt_mem_totalFibre`, `exists_event_of_singular` (re-derived directly as `s4b_exists_event_of_mem_singX` from the
definition of `singX`).  From S1 only the two cut-level lemmas `cutAfter_eq_cutBefore_of_gap`, `cutAfter_eq_cutBefore`.
From S2 only `leftCusp_x_local`, `rightCusp_x_local` (their monotonicity clauses).  S3, S5, S6: nothing.

## 3. The helpers (`section S4bHelpers`, my file L15030-15403; `F` is the section variable)

Generic lists: `s4b_filter_split` (on an `R`-pairwise list, `filter (P ∨ Q) = filter P ++ filter Q` when no `Q`-element
`R`-precedes a `P`-element), `s4b_filter_length_iff` (on an `R`-pairwise list with `P` downward closed along `R`:
`j < (filter P L).length ↔ P L[j]`), `s4b_eq_singleton_of_nodup`.
Events: `s4b_colX_def`/`s4b_colZ_def` (`evX (eventAt k) = colX k`, rfl — needed because `rw [step_hybrid]` does not
see through the `colX` def), `s4b_eventAt_eq` (`eventAt k = events[k]`), `s4b_evX_eq_colX`/`s4b_evZ_eq_colZ`
(`evX e = colX (evIdx e)`), `s4b_events_length_pos`, `s4b_lex_lt` (index order ⇒ lex order, from
`events_pairwise_lt` + `List.pairwise_iff_getElem`), `s4b_colX_le`, `s4b_colZ_lt` (equal `x`, smaller index ⇒ lower).
Singular values: `s4b_evX_mem_singX`, `s4b_exists_event_of_mem_singX` (every singular `x` is an event's `x`;
direct from `singX`'s definition and `mem_crossingPairs_or_swap`), `s4b_notMem_singX_of_no_event` (an
event-free open interval avoids `singX`), `s4b_no_sing_between` (consecutive columns), `s4b_hbot`/`s4b_htop` (the
"lowest/topmost at its x-value" hypotheses of `hybridCut_eq_cutBefore`/`hybridCutStrict_eq_cutAfter` from "no other
column has this x below/above"), **`s4b_hybridCutStrict_eq_next`** (`hybridCutStrict (col k) = hybridCut (col (k+1))`
for `k+1 < n`, tie or gap) — the step of the invariant, reused by `downCountSyn_eq`.
Compactness: `s4b_eval_fract`, `s4b_exists_xmin`/`s4b_exists_xmax`, `s4b_isCusp_of_min`/`_max`,
`s4b_isLeftCusp_of_min`, `s4b_isRightCusp_of_max`.
Letters/counts: `s4b_isCrossing_letterOf_inl/inr`, `s4b_ht_le_of_beforeLE`, **`s4b_filter_le_split`** (on
`fibreListBefore x₀`: `filter (z₀ ≤ ht) = filter (z₀ < ht) ++ filter (ht = z₀)`), **`s4b_filter_eq_cusp`** (at a cusp
event the points at its height are exactly `[c.1]`: `cusp_alone` + `SameParam.eq_of_mem_Ico`),
**`s4b_hybridCut_drop_cusp`** (`(hybridCut (evX (inl c)) (evZ (inl c))).drop (posOf (inl c) − 1) = beforeBits c ++ R`),
`s4b_dcont` (def: the down bit of an event at its hybrid cut), `s4b_downCountFrom_cons_of_step`,
`s4b_downCountFrom_drop`, `s4b_dcont_inr`, `s4b_dcont_inl`, `s4b_sum_univ_toList`, `s4b_sum_cusp`, `s4b_sum_dcont`.

For other units / the merger: `s4b_filter_le_split` + `s4b_filter_eq_cusp` + `s4b_hybridCut_drop_cusp` re-prove the
cusp half of the `A ++ beforeBits c ++ …` split that S4a's `step_hybrid` also needs (S4a's own version is a black box to
me) — a candidate for de-duplication at merge time.  `s4b_no_sing_between`, `s4b_hbot`, `s4b_htop`,
`s4b_hybridCutStrict_eq_next`, `s4b_colX_le`, `s4b_colZ_lt`, `s4b_evX_eq_colX` are exactly the tie-column bookkeeping
the S6 `jump_*` leaves need; `s4b_filter_length_iff` gives `j < colAt x ↔ colX j < x` (in the proof of `cut_word_colAt`,
as `hiff'`), useful for `isSlot_slotAt`/`posAt_const_of_arc`.

## 4. Pitfalls met (Lean 4.34.0-rc2 / this Mathlib)

1. `rw [step_hybrid]` fails against a goal written with `colX F k`/`colZ F k` (`rw` matches at instances transparency
   and does not unfold `colX`); take `have hs := step_hybrid F (eventAt F k)` and `rw [s4b_colX_def, s4b_colZ_def] at hs`
   (rfl lemmas), then `rw [hs]`.  Same for `s4b_dcont (eventAt k)` vs `downBit … (hybridCut (colX k) …)` — `rfl` closes it.
2. `Option.bind_some : (some a).bind f = f a` (there is no `Option.some_bind`); `letterAt_eq` is
   `SM.FrontRealize.letterAt_eq (W) (hk) : letterAt W k = W[k]` (explicit `W`).
3. `if_pos`/`if_neg` are DEPRECATED here (warning "use `ite_eq_left`/`ite_eq_right`", same statements); I use the new
   names.  `ite_cond_eq_true` is deprecated too.
4. `Finset.sum_toList` now says `s.toList.sum = ∑ x ∈ s, x` (no map); for `(s.toList.map f).sum = ∑ x ∈ s, f x` go
   through `Finset.sum_eq_multiset_sum`, `← Multiset.sum_coe`, `← Multiset.map_coe`, `Finset.coe_toList`
   (`s4b_sum_univ_toList`).
5. `∑ c : F.Cusp, g c.1 = ∑ p ∈ F.cuspSet, g p` is `Finset.sum_coe_sort F.cuspSet g` as a TERM (the `Fintype F.Cusp`
   instance `inferInstance` is defeq to the coe-sort one); `simp` does not do it.  `Finset.card_filter` on
   `F.downCount` gives `∑ p ∈ cuspSet, if IsDownCusp p then 1 else 0` with FrontSmooth's classical instance; compare with
   my `if cuspDisc p < 0 …` pointwise by `by_cases h <;> simp [h, SmoothFront.IsDownCusp, hcusp]` (simp handles the
   differing `Decidable` instances).
6. `List.mergeSort_perm (l) (le) : (l.mergeSort le).Perm l`; `List.Perm.countP_eq (p) (h)`; `List.Perm.sum_eq (h)`.
7. `Letter.downBit (r m) c` is a `match` on `c.drop (m − 1)`: after `simp only [Letter.downBit]`, `rw [hR]` with
   `hR : … .drop (posOf … − 1) = [true,false] ++ R` (or `[false,true] ++ R`) reduces the match (rw's closing `rfl`).
8. `IsLocalMin f a` is definitionally `∀ᶠ x in 𝓝 a, f a ≤ f x`, so a global bound gives it by
   `Filter.Eventually.of_forall`; `IsCompact.exists_isMinOn` + `isMinOn_iff` for the compact `Icc 0 1`, then
   `Finset.exists_min_image Finset.univ` over `Fin F.c` (nonempty by `⟨0, F.hc⟩`) — no product-space compactness needed.
9. `F.IsRightCusp (i, t)` vs `F.IsRightCusp p`: destructure `p` first (`obtain ⟨i, t⟩ := q`) before feeding S2's
   `rightCusp_x_local {i t₀}`.  Set-builder membership `hq : q ∈ totalFibre F x₀` projects with `hq.1`/`hq.2`.
10. `simp` normalises `¬ a < 0` to `0 ≤ a`; feed `h.le`, not `not_lt.mpr h.le`, or the goal stays open with an
    "unused simp arg" hint on the other branch.
11. Iteration loop: a scratch copy truncated right after `end SweepLeaves` (+ `end`, `end U8R`, `end Leaves`,
    `end FrontRows`, `end SM`) compiles in 39 s vs 43 s for the whole file — the whole gain is small; the real saver is
    a Mathlib-only probe file (7 s) for generic list lemmas and name checks.  Scratch: `/tmp/s4b/` (`assemble.py`
    splices `helpers.lean` and `bodies/<leaf>.lean` into the skeleton copy; `T1-T3.log`, `Full.log`, `Ax.log`).

## 5. Numbers

Helpers 375 lines / 40 declarations; leaf bodies 122 lines; total ≈ 500 lines (PLAN estimate for S4b: 1.1k).  Full
compile 42.8 s (8 vCPU, lightly loaded).  Sorries 58 → 50.
