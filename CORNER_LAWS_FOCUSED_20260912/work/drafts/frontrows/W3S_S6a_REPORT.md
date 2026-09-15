# W3S_S6a — unit S6a of the U8R sweep (the traversal, first six leaves): REPORT

2026-09-14, prover for unit S6a.  File: `work/drafts/frontrows/W3S_S6a.lean` (18,715 lines = the skeleton
`W3_U8R_Skeleton.lean` 15,586 + ONE inserted helper block + the six leaf bodies).
Compile: `cd work/lean && lake env lean ../drafts/frontrows/W3S_S6a.lean` — **exit 0, 0 errors**, ~60 s (machine
loaded by the other lanes).  `grep -c sorry`: **58 before → 52 after** (= the 48 leaves of the other sweep units +
the 4 L-geo leaves `typeIII_site`, `typeII_move`, `typeI_move`, `crossedCusp_move`, all untouched).
`diff W3_U8R_Skeleton.lean W3S_S6a.lean` = 7 hunks: `15158a15159,17485` (the helper block) and six `c` hunks
(`15161`, `15169`, `15178`, `15187`, `15198`, `15206`) each replacing exactly one `:= sorry` line by a proof body.
Every statement, name and docstring is byte-identical to the skeleton (checked programmatically at splice time).

## 1. Leaves

| leaf | status | lines of proof |
|---|---|---|
| `isSlot_slotAt` | **PROVED** | 10 |
| `slotAt_const` | **PROVED** | 6 |
| `jump_regular` | **PROVED** (both directions) | 143 |
| `jump_cusp` | **PROVED** (left and right cusps) | 331 |
| `jump_cross` | **PROVED** (over/under × rightward/leftward) | 203 |
| `path_no_occ` | **PROVED** (induction on the number of singular parameters) | 115 |

Leaves left: none of S6a.  **PLAN §6 doubt resolved:** the `¬ U2.IsσSlot` clauses on ALL indices `j < m`
(including `j = 0` and the slots at the cuts of the tie columns, for both rightward and leftward strands) are TRUE
as stated and are proved; no weakening to `0 < j` is needed.  The argument is exactly the architect's: a `σ` slot of
column `k'` is `σSlotA`/`σSlotB` of `k'` (`U2.isσSlot_iff` + `σ_facts`), i.e. one of the two positions
`idx, idx+1` of the crossing letter at cut `k'` (rightward) or cut `k'+1` (leftward); a strand whose height differs
from the event's is never at those positions (`s6a_not_σ_right`, `s6a_not_σ_left`, `s6a_not_σ_vertex`,
`s6a_not_σ_letter_right/left`).

## 2. The helper block (`/-! ### S6a helpers -/ section S6aHelpers … end S6aHelpers`, lines 15159-17483)

170 declarations, all prefixed `s6a_`, inside `namespace U8R`, `section Traversal`, immediately before the docstring
of `isSlot_slotAt`.  Sub-sections (each re-declares `variable (F : SmoothFront)`, shadowing the section variable):

* **S6aLists** (generic lists): `s6a_filter_split` / `s6a_filter_split'` (an upward/downward-closed filter of a
  `Pairwise`-sorted list is a prefix/suffix of the filter), `s6a_filter_getElem_iff` (index characterisation),
  `s6a_sorted_split` (split around an element of unique key), `s6a_filter_eq_singleton`, `s6a_filter_eq_pair`
  (the window of a cusp / of a crossing), `s6a_getElem_A/E/R/three` (three-part concatenations).
* **S6aFront**: height order of `beforeLE`/`afterLE`, `s6a_ht_eq_evZ_iff` (the fibre points at an event's height are
  exactly its point(s): `cusp_alone`, `no_triple`), `s6a_filter_ht_cusp/cross` (the sorted windows `[c]`, `[o,u]`,
  `[u,o]`), the `entriesOf` API (`append`, `cons`, `length`, `mem`, `congr`, `nodup`), `s6a_hybridEntriesP_nodup`,
  `s6a_Lb_filter_le`, `s6a_La_filter_not_lt/le`, and **`s6a_hybridEntriesP_eq`** (moving the threshold across regular
  points only does not change the entries list — the entry-level version of `hybridCutStrict_eq_hybridCut`, proved
  here from scratch via `List.Perm.eq_of_pairwise`).
* **S6aColumns**: `s6a_k0 = colAt x₀`, `s6a_K = #{e | evX e ≤ x₀}`; `s6a_evX_lt_iff/le_iff` (column `k` is at `x₀`
  iff `k0 ≤ k < K`), `s6a_colX_eq`, `s6a_colZ_lt/le`, `s6a_evIdx_mem`, `s6a_colAt_eq_k0/K`, `s6a_singX_gap`,
  `s6a_k0_lt_K`, **`s6a_cut_eq`** (`cut W k = hybridCutP x₀ (colZ k ≤ ht)`, from `run_take_eq_hybrid`) and
  **`s6a_cut_succ_eq`** (`cut W (k+1) = hybridCutP x₀ (colZ k < ht)`, from `step_cut` + `step_hybrid`).
* **S6aWindow**: `s6a_A/Eb/Ea/R` (the entries above / in the window before / in the window after / below an event),
  `s6a_hE_le/lt` (`hybridEntriesP = A ++ Eb ++ R` resp. `A ++ Ea ++ R`), `s6a_length_A = idx − 1`,
  `s6a_length_Eb = arity`, `s6a_length_Ea = coarity`, explicit windows `s6a_Eb/Ea_cusp/cross`, `s6a_bit_of_entry`
  (the bit at an entry's index), **`s6a_step_right/left`** (`posR`/`posL` transport of an entry outside the window).
* **S6aNotSigma**: `s6a_σSlotA/B_val`, `s6a_not_σ_right/left/vertex`.
* **S6aWalk**: `s6a_entCol k` (the entries at cut `k` of `x₀`, `k0 ≤ k ≤ K`), `s6a_entCol_k0 = entriesBefore x₀`,
  `s6a_entCol_K_eq = entriesAfter x₀`, `s6a_entCol_succ`, `s6a_regular_between/below/above`,
  **`s6a_next_right_step/left_step`** (one `next` through a column), **`s6a_walk_right/left`** (induction on the
  number of columns; conclusion: endpoint value `(k ± d, J' + 1)`, the entry at `J'`, and `¬IsσSlot` at every index).
* **S6aAnalytic**: `s6a_Free` (no cusp strictly between two parameters), `s6a_Free_join` (across a non-cusp point,
  for ANY position of the point), `s6a_Free_same_side`, `s6a_injOn_x` (Rolle), `s6a_x_inj_of_Free`, periodicity
  (`s6a_xOf_add_int`, `s6a_isCusp_add_int`, `s6a_Free_add_int`), the identification of a `Cont`-continued entry:
  `s6a_cont_start_core/end_core`, **`s6a_cont_start`** (the entry continued by `(i, fract t')` is an entry of
  `(i, fract t)`; for a cusp the arm index is read off the side of `t'`), **`s6a_cont_end`**; the side lemmas
  `s6a_side_pos/neg` (`sign_near_simple_zero`), `s6a_x_cont`, `s6a_no_cusp_near`; `s6a_rep_mem_totalFibre`,
  `s6a_regular_rep`, `s6a_dirBit_rep`; `s6a_card_filter_eq`, **`s6a_posAt_eq`** (`posAt x L[J] = J + 1` off `singX`),
  `s6a_entriesBefore_length/getD`, `s6a_ht_ne_colZ_of_regular`.
* **S6aStartEnd**: `s6a_Free_of_near/local`, `s6a_dist_sub/add`, `s6a_entryBit_regular`, `s6a_colAt_near`,
  **`s6a_start_before/after`** (from the S1 limits: the strand at `x' ≶ x₀` sits at position `J + 1` where `J` indexes
  an entry of `(i, fract t)` in `entriesBefore/After x₀`, with the arm clause for a cusp), **`s6a_end_before/after`**.
* **S6aCusp**: `s6a_afterBits_left`, `s6a_beforeBits_right` (+ `_getD`, `_length`), `s6a_not_σ_letter_right/left`,
  `s6a_cuspVertex_val`, **`s6a_leftCusp_pass`**, **`s6a_rightCusp_pass`** (arrive on one arm at the cusp column,
  `next` = `cuspVertex c`, `next` again = the other arm, with the arm indices `j₁ = 0 ↔ cuspDisc < 0` etc.).
* **S6aCross**: `s6a_crossOf_over/under`, `s6a_evX/evZ_crossOf`, `s6a_ΦFun_val_over/under`, the crossing window
  `s6a_cw_col/col'/A/pos/len/get/bit/index`, **`s6a_cross_pass_right/left`** (the strand of `p` at the crossing
  column IS `ΦFun F p`, and `next` moves it across).
* **S6aPath**: `s6a_params_over_finite`, **`s6a_sing_params_finite`** (finitely many singular parameters in `[t₀,t₁]`),
  `s6a_occ_of_isDouble`.

## 3. Method (what the proofs actually do)

The strand is tracked by its **entry** `a = (q, j)` (a fibre point over `x₀` and an arm index) and its **index** `J`
in the entries list `s6a_entCol k` of each cut line `k0 ≤ k ≤ K` of `x₀`; the slot is `(k, J + 1)`.  At each column the
list is `A ++ Eb ++ R` before and `A ++ Ea ++ R` after (`|A| = idx − 1`, `|Eb| = arity`, `|Ea| = coarity`), so an entry
outside the window moves by `posR`/`posL` (`s6a_step_*`), its bit is read from `s6a_bit_of_entry`, and `nextPair_right/left`
give the `next` step.  The cusp/crossing columns are the only ones whose window contains the strand; they are handled by
the `_pass` lemmas.  At the two ends the S1 limits `entriesBefore_left_limit` / `entriesAfter_right_limit` identify the
entry (`s6a_cont_start`: the continued entry is `(i, fract t)`'s; `s6a_cont_end`: the continuing strand is
`(i, fract t')`) by the one-dimensional fact "cusp-free intervals join across a non-cusp point"
(`s6a_Free_join`) + injectivity of `x` on cusp-free intervals (Rolle).  For a cusp the arm is read from `Cont`'s last
clause (the earlier arm is the upper one iff `cuspDisc < 0`), which matches `beforeBits`/`afterBits` exactly —
**no Taylor input (`cusp_arm_sign`) is needed in S6a.**  `path_no_occ` is an induction on the cardinality of the finite
set of singular parameters in `[t₀, t₁]`, splitting at the smallest one (`slotAt_const` up to it, `jump_regular` or
`jump_cusp` across it — `jump_cusp` transported by the period from `c.1.2 = fract s₁` to `s₁`).

## 4. Dependencies actually used (black boxes of other units)

* S1: `entriesBefore_left_limit`, `entriesAfter_right_limit`, `entriesBefore_eq_of_notMem_singX`,
  `cutBefore_eq_map_dirBit`, `posAt_const_of_arc`.
* S2: `leftCusp_x_local`, `rightCusp_x_local`.
* S4: `run_take_eq_hybrid`, `step_hybrid`, `events_pairwise_lt`, `exists_event_of_singular`, `evPt_mem_totalFibre`,
  `cut_word_colAt`.
* U2: `isσSlot_iff`, `σ_facts`, `σSlotA/B` (unfolded), `nextPair_*`, `posR/posL_*`, `step_cut`, `letterAt_word*`.
* W2 (proved): `xvel*`, `sign_near_simple_zero`, `hasDerivAt_x`, `singX`, `mem_singX_of_*`, `totalFibre*`,
  `snd_injOn_totalFibre`, `fibre_finite`, `isCusp_iff_of_sameParam`, `eq_add_int`, `partner`/`isDouble_partner`.

**Not used by S6a** (so, for S6a, these leaves are not load-bearing): `cusp_arm_sign`, `leftCusp_arms`,
`rightCusp_arms`, `cross_height_order` (all of S3), `regular_local_graph`, `exists_eta_fibre_near`,
`cutBefore_left_limit`, `cutAfter_right_limit`, `cutAfter_eq_cutBefore_of_gap`, `fibreListBefore_eq_of`,
`fibreListAfter_eq_of`, `fibreListAfter_eq_fibreListBefore`, `cutAfter_eq_cutBefore`, `dirBit_of_cont_*`,
`hybridCutStrict_eq_hybridCut`, `hybridCutStrict_eq_cutAfter`, `hybridCut_eq_cutBefore`, S5.

## 5. Pitfalls (for S6b, the merger, and the other lanes)

1. `∃ J' (hJ' : P), Q` does NOT parse in this toolchain; write `∃ J', ∃ hJ' : P, Q`.
2. A `by` block passed as an argument inside `rw [nextPair_right … (by …)]` is elaborated while the position is still
   a metavariable — `rw`/`omega` fail inside it.  State the `posR`/`posL` fact as a separate `have` first.
3. Never `rw … at h` / `rw [Nat.add_zero] at h` into a `getElem` index or list (motive errors); use
   `List.getElem_of_eq` (forward) or state the lemma with the literal index (`|A| + 0`).  `unfold entriesAfter at h`
   also unfolds inside the `getElem`, breaking later rewrites — use a `show … from List.getElem_mem hJ` ascription.
4. Helpers cannot mention `slotAt` (it is defined between leaves 1 and 2): all `slotAt` reasoning is done in the leaf
   bodies via `Subtype.ext` and `show (colAt …, posAt …) = _`.
5. Names absent from this Mathlib: `lt_or_le`, `le_or_lt` (use `Nat.lt_or_ge`, `le_or_gt`), `List.eq_of_perm_of_sorted`
   / `IsAntisymm` (use `List.Perm.eq_of_pairwise`, antisymmetry only on members), `Bool.true_ne_false` (use
   `Bool.noConfusion`), `Finset.not_mem_empty` (use `simp`), `Int.fract_add_int` (use `Int.fract_add_intCast`).
   `push_neg` is deprecated (`push Not` / `not_lt`).
6. Remaining warnings in my block (harmless): 8 deprecation notices for `if_pos`/`if_neg` (in `s6a_cw_index`,
   `s6a_cross_pass_*`; `ite_eq_left/right` are the replacements), 2 unused simp arguments, 1 unused variable `hab`
   (`s6a_filter_eq_pair`).  The other lints in the log are pre-existing (skeleton/W2 code).
7. Fast iteration: compile the skeleton prefix once to an `.olean` (`lean -o S6aPrefix.olean` from a scratch dir
   holding `lean-toolchain`, `LEAN_PATH` from `lake env printenv LEAN_PATH`) and `import` it in a small file: 6 s per
   iteration instead of 60 s.  Scratch in `/tmp/s6a/` (`run.sh`).

## 6. Notes for S6b

`s6a_walk_right/left`, the `_pass` lemmas and the START/END lemmas are directly reusable.  For `path_cusps` the same
induction as `path_no_occ` works with `jump_cusp`'s vertex clause; the clause "every cusp vertex on the path belongs to a
cusp of the circle" needs that the walks/passes visit no cusp vertex except at the cusp itself — the walk lemmas expose
only the endpoint value, but every intermediate slot of `s6a_walk_*` is a cut slot `(k, J+1)` (the induction step gives
`(next u).1 = (k ± 1, J₁ + 1)`), so a variant of `s6a_walk_*` carrying "`∀ j ≤ d, (next^[j] u).1.2 ≠ 0`" is a
10-line change if S6b wants it.  `slotComp_ΦFun`/`ΦFun_cycNext` get `ΦFun F p` on the path from `jump_cross`'s
index `a` and the wrap-around from periodicity (`s6a_xOf_add_int`, `Int.fract_add_intCast`; see the `hsm`/`hsp`
transport in `path_no_occ`).
