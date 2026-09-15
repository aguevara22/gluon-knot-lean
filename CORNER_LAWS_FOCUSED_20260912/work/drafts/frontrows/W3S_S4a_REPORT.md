# W3S_S4a_REPORT — unit S4a of the U8R sweep (events and the word: the local combinatorics)

2026-09-14, prover of unit S4a.  File: `work/drafts/frontrows/W3S_S4a.lean` (16,175 lines) = `W3_U8R_Skeleton.lean`
(15,586) + ONE inserted helper block + the bodies of the nine leaves of S4a.  Compile
`cd work/lean && lake env lean ../drafts/frontrows/W3S_S4a.lean`: **exit 0, 0 errors**, ~64 s; `grep -c sorry`
**58 → 49** (= 4 front-move leaves + 45 leaves of the other units; none of mine).  `diff` against the skeleton:
exactly 10 hunks — the insertion `14996a14997,15452` (the helper block, placed right after the header
`/-! #### S4 leaves: events and the word -/` and immediately before the docstring of `evKey_injective`) and nine
`c` hunks each replacing one `:= sorry` line; every statement line is byte-identical to the skeleton (checked
by grepping each removed line minus ` sorry` back in the file).  No definition, docstring, name or other unit's
leaf was touched.

`#print axioms` (probe `/tmp/s4a/Probe.lean` = the file truncated after `end SweepLeaves`): all nine leaves
depend on `[propext, Classical.choice, Quot.sound]` only — **no `sorryAx`**: the unit turned out fully
self-contained (it does not even consume the S1 statements the plan listed; see §3).

## 1. Leaves proved (9/9) — the first nine of PLAN §3 Unit S4 in table order

| leaf | line | proof (one line each) |
|---|---|---|
| `evKey_injective` | 15455 | `s4a_evKey_injective`: cusp/cusp `cusp_alone`; cusp/cross `cusp_alone` or `not_isCusp_of_isDouble` (if `SameParam`); cross/cross `no_triple` twice + `not_swap_mem_crossingPairs` |
| `events_pairwise_lt` | 15459 | `events_pairwise_le.and events_nodup`, `.imp` with `lt_of_le_of_ne` and `toLex.injective` + injectivity |
| `colX_mono` | 15464 | `s4a_key_lt` (`List.pairwise_iff_getElem` on `events_pairwise_lt`) + `Prod.Lex.toLex_lt_toLex` |
| `evPt_mem_totalFibre` | 15472 | `Cusp.mem_Ico` / `mem_crossingPairs'`; the x-clause is `rfl` |
| `exists_event_of_singular` | 15477 | cusp: `Sum.inl ⟨p, mem_cuspSet⟩`; double: `rep_pair_mem_doubleSet`, `mem_crossingPairs_or_swap`, `SameParam.rep p = p` via `Int.fract_eq_self`, `eval_of_sameParam` for the swapped case |
| `step_hybrid` | 15486 | split `filter (z₀ ≤ ht) = filter (z₀ < ht) ++ filter (ht = z₀)` (before list) and `filter (¬ z₀ < ht) = filter (ht = z₀) ++ filter (¬ z₀ ≤ ht)` (after list); `step_prefix` with the prefix `A` of length `posOf e − 1` (definitional: `unfold posOf; omega`); `act_append`; the core action `s4a_core` |
| `hybridCutStrict_eq_hybridCut` | 15500 | `z₁ < z₂` from `s4a_key_lt`; the points with `z₁ < ht < z₂` are regular (`s4a_regular_of_no_event` + `s4a_no_event_between`); both filters split around the middle band; `s4a_flatMap_before_eq_after` on the band |
| `hybridCutStrict_eq_cutAfter` | 15577 | points above `z₀` regular (`htop`); `s4a_split_self` of the after list at `z₀ < ht`; `s4a_flatMap_before_eq_after` |
| `hybridCut_eq_cutBefore` | 15603 | mirror with `hbot`, the before list split at `z₀ ≤ ht` |

Leaves left: none in S4a.  (S4b — `cutBefore_first`, `cutAfter_last`, `run_take_eq_hybrid`, `word_closed`,
`word_ne_nil`, `cuspCount_eq`, `downCountSyn_eq`, `cut_word_colAt` — untouched, still `sorry`.)

## 2. Helpers (one block `/-! ### S4a helpers -/ section S4aHelpers … end S4aHelpers`, lines 14997-15451, all prefixed `s4a_`)

`s4a_filter_or_split`, `s4a_eq_singleton_of`, `s4a_eq_pair_of`, `s4a_ht_le_of_beforeLE`, `s4a_ht_le_of_afterLE`, `s4a_beforeBits_of_regular`, `s4a_afterBits_of_regular`, `s4a_filter_before_eq_after`, `s4a_flatMap_congr`, `s4a_flatMap_before_eq_after`, `s4a_evPt_mem_totalFibre`, `s4a_exists_event_of_singular`, `s4a_regular_of_no_event`, `s4a_evKey_injective`, `s4a_events_pairwise_lt`, `s4a_eventAt_eq`, `s4a_key_lt`, `s4a_no_event_between`, `s4a_letterOf_inl_left`, `s4a_letterOf_inl_right`, `s4a_idx_letterOf`, `s4a_letterOf_inr`, `s4a_mem_filter_eq_iff`, `s4a_filter_eq_cusp`, `s4a_mem_filter_cross`, `s4a_before_filter_cross`, `s4a_after_filter_cross`, `s4a_core`, `s4a_before_split_le`, `s4a_after_split_not_lt`, `s4a_split_self`.

Grouped:
* **Pure list combinatorics** (no `F`): `s4a_filter_or_split` — for a `Pairwise R` list with `P`, `Q`
  disjoint and no `Q`-element before a `P`-element, `filter (P ∨ Q) = filter P ++ filter Q` (THE tool for all
  the cut splits, used seven times); `s4a_split_self` (`L = filter P ++ filter ¬P`, same hypothesis);
  `s4a_eq_singleton_of` / `s4a_eq_pair_of` (a nodup list with members exactly `{p}` is `[p]`; a nodup
  `Pairwise R` list with members exactly `{o,u}`, `o ≠ u`, `¬ R u o` is `[o,u]`); `s4a_flatMap_congr`.
* **Sort keys and bits**: `s4a_ht_le_of_beforeLE` / `_afterLE` (`beforeLE p q → ht q ≤ ht p`),
  `s4a_beforeBits_of_regular` / `s4a_afterBits_of_regular` (`¬ IsCusp p → bits = [dirBit p]`),
  `s4a_filter_before_eq_after` (if every `P`-point of the fibre is regular — no cusp, no double — the `P`-sublists
  of the two sorted fibre lists coincide: `List.Pairwise.eq_of_mem_iff` with the irreflexive relation
  `ht q < ht p`, strictness from `snd`-injectivity on regular points), `s4a_flatMap_before_eq_after` (their bits).
* **Events**: `s4a_evPt_mem_totalFibre`, `s4a_exists_event_of_singular`, `s4a_evKey_injective`,
  `s4a_events_pairwise_lt` (the real proofs of leaves 1, 2, 4, 5 — the leaves are one-line calls, because the
  helper block sits before all nine leaves and later helpers need these facts), `s4a_regular_of_no_event` (a fibre
  point at whose height no event of its x-value sits is regular), `s4a_eventAt_eq`, `s4a_key_lt` (column keys
  strictly increase), `s4a_no_event_between` (no event key strictly between consecutive column keys).
* **The letter and the points at the event's height**: `s4a_letterOf_inl_left` / `_inl_right` / `_inr`,
  `s4a_idx_letterOf` (`idx = posOf`), `s4a_mem_filter_eq_iff`, `s4a_filter_eq_cusp` (`= [c.1]`, by
  `cusp_alone`), `s4a_mem_filter_cross` (`no_triple`), `s4a_before_filter_cross` (`= [over, under]`) /
  `s4a_after_filter_cross` (`= [under, over]`), `s4a_core` (length = arity and `act` of the letter on the bits
  of the height-`z₀` points: `l` on `[]` gives `[d, !d] = afterBits`, `r` on the two opposite `beforeBits`
  gives `[]`, `σ` swaps `[dirBit o, dirBit u]`), `s4a_before_split_le`, `s4a_after_split_not_lt`.

## 3. Dependencies actually used

None of the other units' leaves.  The plan (§4) listed S1's `cutAfter_eq_cutBefore_of_gap`/`cutAfter_eq_cutBefore`
and `regular_local_graph`/`rightCusp_x_local` for S4 — those are consumed by S4b (`run_take_eq_hybrid`,
`cut_word_colAt`, `cutBefore_first`, `cutAfter_last`), not by S4a.  Accepted vocabulary used: `cusp_alone`,
`no_triple`, `not_swap_mem_crossingPairs`, `mem_crossingPairs'`, `mem_crossingPairs_or_swap`,
`rep_pair_mem_doubleSet`, `isOverUnder_of_mem_crossingPairs`, `not_isCusp_of_isDouble`, `isCusp_iff_of_sameParam`,
`isLeftCusp_or_isRightCusp`, `SameParam.eq_of_mem_Ico`, `eval_of_sameParam`, `Cusp.mem_Ico`, `Cusp.isCusp`,
`mem_cuspSet`; from the skeleton: the `fibreList*_perm/nodup/pairwise`, `mem_fibreList*`, `events_pairwise_le`,
`events_nodup`, `eventAt_evIdx`, `evIdx_lt_length`, `step_prefix`, `act_append`.  Mathlib/core:
`List.Pairwise.eq_of_mem_iff` (needs a `Std.Irrefl` instance, provided inline), `List.pairwise_iff_getElem`,
`List.filter_congr`, `List.filter_eq_self`, `List.filter_eq_nil_iff`, `Prod.Lex.toLex_le_toLex`/`_lt_toLex`.

## 4. Truth of the statements

All nine are true exactly as stated (no counterexample, no missing hypothesis).  Two conventions were confirmed in
the proofs, as PLAN §2 predicted: (i) in `fibreListBefore` the over branch (smaller slope) precedes the under
branch at equal height and in `fibreListAfter` the under branch precedes — this is what makes `σ` on
`[dirBit over, dirBit under]` produce `[dirBit under, dirBit over]` = the after-bits in after-order; (ii) for a
right cusp the two `beforeBits` are opposite (`[true,false]`/`[false,true]`), so `act_r_cons` fires; for a
left cusp `afterBits = [d, !d]` with `d = decide (0 < cuspDisc)` = the bit of `letterOf` (both are read off
the same `if 0 < cuspDisc`).  The `posOf` of the letter is definitionally `|A| + 1` for the prefix
`A = (filter (evZ e < ht) fibreListBefore).flatMap beforeBits`, so `step_prefix` applies with `unfold posOf; omega`.

## 5. Pitfalls for the merger / for S4b, S5, S6

* `letterOf` is a `match`; `unfold letterOf` does NOT reduce it on `Sum.inl c` (`split_ifs`/`rw [ite_eq_left]`
  fail on the un-reduced match).  Use `s4a_letterOf_inl_left` / `s4a_letterOf_inl_right` / `s4a_letterOf_inr`
  (or a `show (if F.IsLeftCusp c.1 then … else …) = _`).  `s4a_idx_letterOf : (letterOf F e).idx = posOf F e`.
* `if_pos`/`if_neg` are deprecated in this toolchain (warnings); `ite_eq_left`/`ite_eq_right` are the names
  the skeleton itself uses.  `push_neg` is deprecated (use `not_or.mp` etc.).  `lt_of_not_le` does not exist
  (`not_le.mp`).
* The Bool predicates in `hybridCutP`: `fun p => !decide (z₀ ≤ ht F p)` etc.  Splitting them needs
  `Bool.not_eq_true'`, `Bool.not_eq_false'`, `decide_eq_false_iff_not`, `Bool.and_eq_false_iff`,
  `Bool.eq_iff_iff` (+ `Bool.or_eq_true`, `decide_eq_true_eq`) — all used in the leaf bodies as templates.
* `s4a_flatMap_before_eq_after F x₀ P hreg` is the workhorse for S4b/S6 whenever a band of strands is regular
  (e.g. for `cut_word_colAt` or the `hybridEntries` bookkeeping): it needs only
  `∀ p ∈ totalFibre F x₀, P p = true → ¬ IsCusp p ∧ ∀ q, ¬ IsDouble p q`, which `s4a_regular_of_no_event` gives
  from "no event of `x₀` at the height of `p`".
* The two unused-variable lint warnings on `hk` in `hybridCutStrict_eq_cutAfter` / `hybridCut_eq_cutBefore` are
  about the frozen hypothesis `hk` (not needed: `htop`/`hbot` already pin the column); harmless.
* The helper block redeclares nothing: it lives inside `section SweepLeaves` and uses its `variable (F : SmoothFront)`;
  the pure-list helpers take `{α : Type*}` and do not mention `F`.
* Compile logs: `/tmp/s4a/full.log` (full file), `/tmp/s4a/probe.log` (axioms), scratch `/tmp/s4a/Trunc.lean`
  (the file truncated after `end SweepLeaves` + closing `end`s, 45 s per iteration).
