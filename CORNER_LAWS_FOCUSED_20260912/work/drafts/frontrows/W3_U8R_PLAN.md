# W3_U8R_PLAN — the leaf skeleton of the sweep (`U8R.SweepStatement`), wave 3

2026-09-14, architect for the sweep of unit U8R (W2_U8R_REPORT.md §2-§3).  Deliverable (1):
**`work/drafts/frontrows/W3_U8R_Skeleton.lean`** (15,587 lines) = `Skeleton_W2.lean` (14,891) + ONE inserted block
`/-! ### U8R sweep … -/ namespace U8R … end U8R` (`diff` = the single insertion hunk `14567a14568,15261`, placed
right before the docstring of the leaf `represent`) + the leaf `represent` PROVED (`diff` hunk `14573c15267,15268`:
` := sorry` → ` :=\n  U8R.represent_of_sweepStatement F (U8R.sweep_proof F)`; the statement line is byte-identical).
Every other line of `Skeleton_W2.lean` is unchanged; the four L-geo leaves stay `sorry`.  Compile:
`cd work/lean && lake env lean ../drafts/frontrows/W3_U8R_Skeleton.lean` — **0 errors**, exit 0, ~40 s; `grep -c sorry`
= 58 = 4 (typeIII_site, typeII_move, typeI_move, crossedCusp_move) + **54 new leaves** (all `theorem … := sorry`, all
in `SM.FrontRows.U8R`).  `#print axioms SM.FrontRows.represent` on a probe copy: `[propext, sorryAx,
Classical.choice, Quot.sound]` — `sorryAx` only through the 54 leaves (see the end of this file for the log).

Line numbers below are lines of `W3_U8R_Skeleton.lean`.  Block layout: header docstring 14568-14590;
`namespace U8R`, `open SM.FrontWord SM.FrontWord.Letter SM.FrontRealize Equiv`, `noncomputable section` 14591-14595;
`section SweepDefs` 14597-14858 (all definitions of S1/S4 and the leaf `word_closed`);
`section SweepLeaves` 14861-15071 (leaves S1, S2, S3, S4); `section SlotMap` 15073-15126 (Φ and S5);
`section Traversal` 15128-15236 (`cuspVertex`, `circleEquiv`, `slotAt`, S6); `section Assembly` 15238-15257
(`recordIso` 15243 — PROVED from the leaves — and `sweep_proof` 15253 — PROVED); `end U8R` 15261.

## 1. The route in the skeleton (definitions; lines)

Coordinates: `xOf F i t = ((F.comp i).γ t).1` (14604), `zOf` (14606), `ht p = (F.eval p).2` (14608),
`dirBit p = decide (0 < xvel F p.1 p.2)` (14610); decidability instances for `IsCusp`/`IsLeftCusp`/`IsRightCusp`
(14618-14622, by `unfold; infer_instance`; NO `open Classical`, per W2_U8R_REPORT §5.2).

**S1 the cut.** `fibreFinset F x₀` (14626) = `(totalFibre_finite F x₀).toFinset`.  Two Bool comparators on fibre
points: `beforeLE` (14633) = lex `(−height, slope)`, `afterLE` (14637) = lex `(−height, −slope)` — height descending
(top to bottom), and at a double point the over branch (smaller slope) FIRST before the crossing, LAST after it.
`fibreListBefore`/`fibreListAfter` (14641/14643) = `List.mergeSort` of `fibreFinset.toList` by them (proved in the
skeleton: `_perm`, `mem_`, `_nodup`, `_pairwise` 14645-14676, via `List.mergeSort_perm`, `List.pairwise_mergeSort`).
`beforeBits p` (14678): `[]` for a left cusp, `[true,false]`/`[false,true]` for a right cusp according to
`cuspDisc < 0`, `[dirBit p]` otherwise; `afterBits p` (14685): `[]` for a right cusp, `[true,false]`/`[false,true]`
for a left cusp according to `0 < cuspDisc`, `[dirBit p]` otherwise (sign conventions checked in §2).
`hybridCutP x₀ P` (14713) = `flatMap beforeBits (filter P fibreListBefore) ++ flatMap afterBits (filter ¬P
fibreListAfter)`; `cutBefore` (14723) / `cutAfter` (14725) are `P ≡ true` / `P ≡ false` (14738-14741, proved);
`hybridCut x₀ z₀` (14732) = `P p := z₀ ≤ ht p` (the cut just BEFORE the event at height `z₀` is processed: strands at
height `≥ z₀` read "before", strands below read "after"); `hybridCutStrict` (14734) = `P p := z₀ < ht p` (just
AFTER).  Strand entries `(p, j)`: `entriesOf`/`entryBit` (14691/14695; `map entryBit (entriesOf bits L) =
flatMap bits L` proved 14697), `entriesBefore`/`entriesAfter`/`hybridEntries` (14727-14736).  `Cont q (p, j)`
(14747): `q` is on the cusp-free arc adjacent to `p`, on the arm fixed by `j` for a cusp (the upper arm `j = 0` is
the EARLIER arm iff `cuspDisc p < 0` — one formula for the two arms before a right cusp and after a left cusp).
`posAt x₀ q` (14754) = 1 + #fibre points strictly above `q`.

**S4 the word.** `Cross F` = `{q // q ∈ F.crossingPairs}` (over-first pairs), `Event F = F.Cusp ⊕ Cross F`
(14759/14761, `Fintype`, `DecidableEq` automatic; a lawful `BEq` instance 14791-14795 because `Sum.instBEq` is
not lawful).  `evPt` (14764; the over branch for a crossing), `evX`, `evZ`, `evLE` = lex `(x, z)` (14768-14772),
`events` (14781) = `mergeSort` of `Finset.univ.toList` (proved: `mem_events`, `events_nodup`, `events_pairwise_le`
14783-14789).  `eventAt k` (14799, `getD` with `someCusp`), `evIdx e = idxOf` (14801; `evIdx_lt_length`,
`eventAt_evIdx`, `evIdx_eventAt` proved 14807-14814), `colX`/`colZ` (14803/14805).  `posOf e` (14816) = 1 +
length of `flatMap beforeBits (filter (evZ e < ht) fibreListBefore (evX e))` — one plus the number of strands
strictly above the event in the hybrid cut before it.  `letterOf` (14822): left cusp `l (posOf e) (decide (0 <
cuspDisc))`, right cusp `r (posOf e)`, crossing `σ (posOf e)`.  `word = events.map letterOf` (14829),
`letterAt_word`, `letterAt_word_evIdx`, `letterAt_word_cross` proved (14833-14845), `colAt x` (14847) = #events with
`evX < x`.  LEAF `word_closed` (14852); `oword` (14855).

**S5 Φ.** `crossOf p` (15081) = the over-first pair of `p`'s double point; `ΦFun p` (15089) = `σSlotA hW hk hℓ` if
`frontOver p` (over = smaller slope = above before, below after = the descending strand) else `σSlotB`;
`isσSlot_ΦFun` proved (15095); `ΦSub` (15101); LEAF `ΦSub_bijective`; `occEquiv = Equiv.ofBijective` (15109).

**S6 traversal.** `cuspVertex c = ⟨(evIdx (inl c), 0), _⟩` (15139; `isSlot_cuspVertex` proved 15132),
`someCuspOn i` (15142), `circleComp i = U2.slotComp hW (cuspVertex (someCuspOn i))` (15148), LEAF
`circleComp_bijective`, `circleEquiv` (15157); LEAF `isSlot_slotAt`, `slotAt i t h = ⟨(colAt (xOf i t), posAt (xOf
i t) (i, fract t)), _⟩` (15164) — the slot of the strand through `(i, t)` at the cut line of its (non-singular)
x-value.

**Assembly (proved).** `recordIso` (15243): `e := circleEquiv`, `Φ := occEquiv`, `comp_eq := slotComp_ΦFun`,
`succ_eq := Subtype.ext (ΦFun_cycNext _)`, `pair_eq := Subtype.ext (ΦFun_partner _)`, `bit_eq := isDesc_ΦFun`,
`sgn_eq := σsgn_ΦFun` (all defeq to the record fields: `Equiv.ofBijective_apply`, `cycSucc_apply`,
`slotRecord_*` are `rfl`).  `sweep_proof F := ⟨oword F, word_ne_nil F, (downCountSyn_eq F).symm, (cuspCount_eq
F).symm, ⟨recordIso F⟩⟩` (15253).  `represent F := U8R.represent_of_sweepStatement F (U8R.sweep_proof F)` (15268).

## 2. Truth checks (conventions against the accepted vocabulary; numerics in `/tmp/u8s/check.py`)

* **Cusp arm sign (leaf `cusp_arm_sign`).**  With `γ'' = (a, c)`, `γ''' = (b, d)` at the cusp and matched arms
  `t₁ < t₀ < t₂`, `x(t₁) = x(t₂)`: `t₂ − |t₁| ≈ −(b/3a)u²`, so `z(t₂) − z(t₁) ≈ u³(ad − bc)/(3a)`, of the sign of
  `a·det(γ'', γ''') = cuspDisc` (`SmoothFront.cuspDisc p = (acc p).1 * det (acc p) (jerk p)`, FrontSmooth L446).
  Numerically: 600 random `C^∞` germs (orders 2-7), arms matched by bisection at `u ∈ {10⁻², 3·10⁻³, 10⁻³}`:
  **0 mismatches of 1692**.  Agrees with the accepted `germFront_later_arm_higher_iff` (later arm higher ↔
  `0 < 16A³ = cuspDisc`).
* **Down bit.**  `IsDownCusp p := IsCusp p ∧ cuspDisc p < 0` (L455) = "traversed from the upper arm to the lower":
  the later arm is lower ↔ `cuspDisc < 0` ✓.  Left cusp letter `l m d`, `d := decide (0 < cuspDisc)`:
  FrontWords `Letter.downBit (l _ d) = if d then 0 else 1` = 1 ↔ `cuspDisc < 0` ↔ `IsDownCusp` ✓; the realization
  convention "the upper new arm travels rightward iff `d`": the leaving arm (later, `t > t₀`) of a left cusp travels
  rightward (`exists_xvel_sign_of_isLeftCusp`) and is the upper arm iff `0 < cuspDisc` ✓ = `afterBits`.  Right
  cusp `r m`: `downBit (r m) c = 1` iff the bit at position `m` (upper arm) is `true`; the arriving arm (earlier)
  travels rightward (`exists_xvel_sign_of_isRightCusp`) and is upper iff the later arm is lower iff `cuspDisc < 0`
  ↔ `IsDownCusp` ✓ = `beforeBits` (`[true,false]` iff `cuspDisc < 0`).  Also `r` needs two OPPOSITE bits
  (`act_r_cons`): `[true,false]`/`[false,true]` ✓.
* **Crossing (leaf `cross_height_order`, `step_hybrid`, `Φ`).**  Over = smaller `dz/dx` (`IsOverUnder`, L505).
  Locally `z_over − z_under ≈ (s_over − s_under)(x − x₀) > 0` for `x < x₀`: the over branch is ABOVE before the
  crossing and BELOW after (300 random slope pairs, 0 mismatches).  Hence in the cut before the crossing the over
  branch is at position `m`, the under at `m+1`; `σ m` exchanges them (`act_σ_cons`), and the over strand is the
  DESCENDING one `pass m (m+1)` = `σSlotA` (`FrontRealizeCorrespondence` L310), with `U2.isDesc_σSlotA = true` =
  `frontOver` ✓ (leaf `isDesc_ΦFun`).  The sort keys: `beforeLE` puts the smaller slope first (over above) and
  `afterLE` the larger slope first (under above) ✓.
* **Sign.**  `U2.σsgnCol` = `+1` iff the two bits of the column agree; `crossSign_eq_one_iff_of_isOverUnder`: the
  over-first sign is `+1` iff the two x-velocities have the same sign ✓ (leaf `σsgn_ΦFun`, through the invariant).
* **Left/right cusps and `x`.**  `IsLeftCusp := IsCusp ∧ 0 < x''`: `x` has a strict local MIN (`x'` negative before,
  positive after: §F `exists_xvel_sign_of_isLeftCusp`), so the two arms lie to the RIGHT (`x > x₀`): `beforeBits = []`,
  and `l` (which creates two strands) is the right letter ✓; a right cusp is the mirror ✓.
* **Ties.**  Events of one x-value are processed bottom to top (`evLE` lex `(x, z)`), positions counted from the top,
  so processing a lower event does not move the positions of the events above it; the intermediate cuts are the
  hybrid cuts.  This is the U8R report's decision (§3 "Ties … handled combinatorially"); no `deform_*` leaf is used.

## 3. The leaves (line; statement in words; sketch; tools; estimate).  β2 calibration ×1.5 applied to analytic ones.

### Unit S1 — the non-singular cut and its one-sided limits (16 leaves, ≈ 2.6k lines)

| line | leaf | statement | sketch / tools | est. |
|---|---|---|---|---|
| 14870 | `fibreListBefore_eq_of` | a nodup list of exactly the fibre points, `Pairwise beforeLE`, IS `fibreListBefore` | `List.Perm.eq_of_pairwise` (needs antisymmetry on the fibre: equal height+slope ⇒ `slope_ne_of_isDouble`), `fibreListBefore_perm/_pairwise`, `List.perm_iff_count`/`List.Perm` from nodup+mem (`List.perm_of_nodup_nodup_toFinset_eq` or `List.Nodup.perm_iff_eq...`) | 80 |
| 14875 | `fibreListAfter_eq_of` | same, "after" order | mirror | 40 |
| 14882 | `fibreListAfter_eq_fibreListBefore` | off `singX` the two orders agree | `regular_of_notMem_singX`, `snd_injOn_totalFibre` (distinct heights ⇒ keys compare by height only), `fibreListAfter_eq_of` | 80 |
| 14885 | `cutBefore_eq_map_dirBit` | off `singX` the cut is the map of `dirBit` over the sorted fibre | every fibre point regular: `beforeBits = [dirBit]`; `List.flatMap_singleton`-style rewriting | 60 |
| 14888 | `cutAfter_eq_cutBefore` | off `singX`, after = before | the two previous | 30 |
| 14890 | `entriesBefore_eq_of_notMem_singX` | off `singX` the entries are `(p, 0)` | `entriesOf` with `(beforeBits p).length = 1` | 50 |
| 14897 | `regular_local_graph` | at a regular parameter: no cusp within `δ`, `x` injective on `(t₀−δ, t₀+δ)`, and every `x` within `η(δ')` of `x(t₀)` has a preimage within `δ' ≤ δ` | `exists_arc_mem` puts `t₀` on a closed arc `[c, arcEnd c]` with `t₀` interior (not a cusp, `not_isCusp_of_mem_arc`); `strictMonoOn_x_of_isLeftCusp`/`strictAntiOn_x_of_isRightCusp` ⇒ injective; IVT (`intermediate_value_Icc`) on `[t₀−δ', t₀+δ']` gives the preimage; `exists_no_cusp_near` | 250 |
| 14906 | `exists_eta_fibre_near` | fibre points over `x` near `x₀` are near (mod 1) fibre points over `x₀` | `K := {(i,t) : t ∈ [0,1], ∀ p ∈ fibre, ∀ n ∈ {−1,0,1}, i ≠ p.1 ∨ δ ≤ |t+n−p.2|}` is compact (closed in `Fin c × Icc 0 1`, `totalFibre_finite`); `|x − x₀|` continuous, never `0` on `K`; `IsCompact.exists_isMinOn` (or `IsCompact.exists_forall_le`) ⇒ `η` | 250 |
| 14914 | `entriesBefore_left_limit` | just left of `a`, entries of the cut = continuations, in order, of `entriesBefore a` | for each fibre point over `a`: regular ⇒ one strand (`regular_local_graph`), right cusp ⇒ two arms (`rightCusp_arms`, `cusp_arm_sign` for their order, `rightCusp_x_local`), left cusp ⇒ none (`leftCusp_x_local`), double point ⇒ two regular strands ordered by `cross_height_order`; `exists_eta_fibre_near` (nothing else); heights of distinct fibre points separated by continuity ⇒ order preserved; build the list `L` of continuations, `fibreListBefore_eq_of` at `x` | 600 |
| 14920 | `entriesAfter_right_limit` | just right of `a`, entries = continuations of `entriesAfter a` | mirror (left cusp ⇒ two arms, `leftCusp_arms`; right cusp ⇒ none) | 400 |
| 14928 | `dirBit_of_cont_before` | a continuation carries its entry's `beforeBit` | `Cont` unfolded; `xvel_mul_pos_of_cuspFree` on the cusp-free arc; `exists_xvel_sign_of_isRightCusp` (arriving arm rightward); case on `j`, `cuspDisc` | 120 |
| 14932 | `dirBit_of_cont_after` | same with `afterBits` | mirror, `exists_xvel_sign_of_isLeftCusp` | 80 |
| 14936 | `cutBefore_left_limit` | just left of `a`: `cutBefore x = cutBefore a` | `entriesBefore_left_limit`, `map_entryBit_entriesOf`, `dirBit_of_cont_before`, `entriesBefore_eq_of_notMem_singX` at `x` (non-singular for `x` close to `a`: `singX` finite) | 60 |
| 14938 | `cutAfter_right_limit` | just right of `a`: `cutBefore x = cutAfter a` | mirror | 60 |
| 14942 | `cutAfter_eq_cutBefore_of_gap` | `a < b`, no singular value between ⇒ `cutAfter a = cutBefore b` | `cutBefore` is locally constant on `Ioo a b` (both limits + `cutAfter_eq_cutBefore`); `IsLocallyConstant.apply_eq_of_isPreconnected` (import present); then the two end limits | 150 |
| 14947 | `posAt_const_of_arc` | along an arc whose x-values avoid `singX`, `posAt` of the strand and `colAt` are constant | `colAt` constant: `evX e < x` is constant on the gap; `posAt`: locally constant in `t` (the entry-level limits at each `x(t)` identify the strand's index), `IsPreconnected.constant`-style on `Icc t₀ t₁` (or the `IsLocallyConstant` route on the parameter interval) | 250 |

### Unit S2 — the cusp local model (5 leaves, ≈ 1.4k)

| line | leaf | statement | sketch / tools | est. |
|---|---|---|---|---|
| 14958 | `cusp_arm_sign` | matched arms `t₁ < t₀ < t₂`, `x(t₁) = x(t₂)` ⇒ `z(t₁) < z(t₂) ↔ 0 < cuspDisc` | Taylor to order 3 with `o(u³)` remainder for `x` and `z` (no `Mathlib.Analysis.Calculus.Taylor` in the import closure — build it from `hasDerivAt_iff_isLittleO` applied to `γ`, `γ'`, `γ''` (all `C^∞`: `contDiff_iteratedDeriv`), or Cauchy MVT `exists_ratio_hasDerivAt_eq_ratio_slope` three times); from `x(t₁) = x(t₂)` derive `t₂ + t₁ = O(u²)` with the explicit coefficient `−b/(3a)·u²`, substitute in `z`; `x'' ≠ 0` (`acc_fst_ne_zero_of_isCusp`), `det ≠ 0` | 900 |
| 14964 | `leftCusp_x_local` | at a left cusp: no other cusp within `δ`, `x` strictly anti on `(t₀−δ, t₀]`, strictly mono on `[t₀, t₀+δ)` | `exists_no_cusp_near`; `t₀` is `c.1.2` of a cusp `c` (rep) and also `arcEnd c'` of the previous cusp `c' = cycPrev`; `strictMonoOn_x_of_isLeftCusp c`, `strictAntiOn_x_of_isRightCusp c'` (`isRightCusp` of the previous cusp by alternation), restricted | 150 |
| 14969 | `rightCusp_x_local` | mirror | mirror | 100 |
| 14975 | `leftCusp_arms` | for `x ∈ (x₀, x₀+η)` both arms have a preimage within `δ'` | IVT on each monotone arm (`intermediate_value_Icc`), `η := min (x(t₀−δ'/2) − x₀) (x(t₀+δ'/2) − x₀)` | 120 |
| 14980 | `rightCusp_arms` | mirror | mirror | 80 |

### Unit S3 — the crossing local model (1 leaf, ≈ 0.3k)

| 14990 | `cross_height_order` | near an over-under pair, at equal `x`: over above for `x < x₀`, below for `x > x₀` | both branches regular (`vel_ne_zero_of_isDouble`, `vel_fst_ne_zero_of_isDouble`); `z − s·x` along each branch has derivative `z' − s x' = 0` at the double point with `s := slope`; the difference `(z_p − z_q)` at equal `x` is `(s_p − s_q)(x − x₀) + o(x − x₀)` via `hasDerivAt_iff_isLittleO` on both branches and the `x`-inverse bound from `regular_local_graph`; `s_p < s_q` | 300 |

### Unit S4 — events, the word, closedness, counts (17 leaves, ≈ 2.3k)

| line | leaf | statement | sketch / tools | est. |
|---|---|---|---|---|
| 14999 | `evKey_injective` | distinct events have distinct `(x, z)` | cusp/cusp: `cusp_alone` (+ `SameParam.eq_of_mem_Ico`); cusp/cross: `cusp_alone` or `vel_ne_zero_of_isDouble`; cross/cross: `no_triple`, `not_swap_mem_crossingPairs` | 80 |
| 15002 | `events_pairwise_lt` | events strictly sorted by lex `(x, z)` | `events_pairwise_le` + `events_nodup` + `evKey_injective` (`List.Pairwise.imp_of_mem` / `Pairwise.and` with nodup) | 60 |
| 15006 | `colX_mono` | `k < k' < n ⇒ colX k ≤ colX k'` | `List.pairwise_iff_getElem` on `events_pairwise_lt`, `Prod.Lex.lt_iff` | 40 |
| 15009 | `evPt_mem_totalFibre` | the event's point is in the fibre over `evX e` | `Cusp.mem_Ico`, `mem_crossingPairs'` | 30 |
| 15013 | `exists_event_of_singular` | a singular fibre point is an event's point | cusp: `Sum.inl ⟨p, mem_cuspSet⟩`; double: `rep_pair_mem_doubleSet`, `mem_crossingPairs_or_swap`, the event's `evZ` equals `ht p` via `IsDouble.eval_eq` | 80 |
| 15021 | `step_hybrid` | `(letterOf e).step (hybridCut (evX e) (evZ e)) = some (hybridCutStrict …)` | split `filter (z ≤ ht)` of the sorted list as `filter (z < ht) ++ filter (ht = z)` (`List.filter_append`-style on `Pairwise`); the points at height `evZ e` over `evX e`: exactly `c` (cusp: `cusp_alone`) or `{over, under}` in that before-order / reverse after-order (`no_triple`, `beforeLE` on equal heights compares slopes); `step_prefix` with `A.length = posOf e − 1` (definitional), `act_l`, `act_r_cons` (bits distinct), `act_σ_cons` | 350 |
| 15026 | `hybridCutStrict_eq_hybridCut` | consecutive events of one x-value: cut after the lower = cut before the upper | points with height strictly between are regular (`exists_event_of_singular` + `events_pairwise_lt` ⇒ no event there): `beforeBits = afterBits`, before/after orders agree on them (distinct heights); list surgery on the filters | 200 |
| 15030 | `hybridCutStrict_eq_cutAfter` | after the topmost event of an x-value the cut is `cutAfter` | strands above are regular ⇒ their "before" bits/order = "after"; `cutAfter_eq_hybridCutP` | 120 |
| 15035 | `hybridCut_eq_cutBefore` | before the lowest event of an x-value the cut is `cutBefore` | mirror | 100 |
| 15042 | `cutBefore_first` | `cutBefore (colX 0) = []` | `x` attains its min on the compact `Fin c × Icc 0 1` (`IsCompact.exists_isMinOn`); at the min `x' = 0` (`IsLocalMin.hasDerivAt_eq_zero`) ⇒ cusp (`isCusp_iff_xvel_eq_zero`) ⇒ an event ⇒ `colX 0 ≤ x_min`, and `colX 0 ≥ x_min`; every fibre point over `x_min` is a left cusp (a regular point / right cusp / double point continues to smaller `x`: `regular_local_graph`, `rightCusp_x_local`) ⇒ all `beforeBits = []` | 250 |
| 15045 | `cutAfter_last` | `cutAfter (colX (n−1)) = []` | mirror with the max | 200 |
| 15050 | `run_take_eq_hybrid` | `run ((word F).take k) [] = some (hybridCut (colX k) (colZ k))` for `k < n` | induction on `k`; `List.take_succ`, `run_append`, `run_singleton`, `letterAt_word`; base: `hybridCut_eq_cutBefore` (event 0 lowest at its x by sortedness) + `cutBefore_first`; step: `step_hybrid`, then `hybridCutStrict_eq_hybridCut` (tie) or `hybridCutStrict_eq_cutAfter` + `cutAfter_eq_cutBefore_of_gap` (no singular value strictly between consecutive distinct `colX`: every singular value is an event's x, `mem_singX` unfolded) + `hybridCut_eq_cutBefore` | 200 |
| 14852 | `word_closed` | `run (word F) [] = some []` | `run_take_eq_hybrid` at `n−1`, `step_hybrid`, `hybridCutStrict_eq_cutAfter` (last event topmost), `cutAfter_last`; `n ≥ 1` | 80 |
| 15054 | `word_ne_nil` | the word is nonempty | `mem_events (Sum.inl (someCusp F))` | 20 |
| 15057 | `cuspCount_eq` | `#cusp letters = #cusps` | `Word.cuspCount = countP`, `List.countP_map`, `isCrossing (letterOf e) = false ↔ e = inl _`; `countP` over a nodup list of all events = `Fintype.card F.Cusp` (`List.Perm.countP_eq`, `Finset.card_univ`, `Fintype.card_sum`), `card_cusp` | 80 |
| 15062 | `downCountSyn_eq` | `downCountFrom (word F) [] = D(F)` | unfold `downCountFrom` along the run (`run_take_eq_hybrid` gives each intermediate cut); per event: `l`: `downBit = 1 ↔ ¬(0 < cuspDisc) ↔ IsDownCusp`; `r`: the bit at position `m` of `hybridCut` is the head of `beforeBits c` = `decide (cuspDisc < 0)` (via the `A ++ L` split of `step_hybrid`); `σ`: 0; sum over events = `#(cuspSet.filter IsDownCusp)` by the bijection cusps ↔ `inl` events | 250 |
| 15067 | `cut_word_colAt` | `x ∉ singX ⇒ cut (word F) (colAt x) = cutBefore x` | `colAt x = k` with `colX (k−1) < x < colX k` (sortedness); `run_take_eq_hybrid` + `hybridCut_eq_cutBefore` + `cutAfter_eq_cutBefore_of_gap` twice (from `colX (k−1)` to `x`, from `x` to `colX k`; `cutAfter_eq_cutBefore` at `x`); edge cases `k = 0`, `k = n` (both sides `[]`: `cut_zero`, `cut_length`, `cutBefore_first`/`cutAfter_last` + gaps) | 150 |

### Unit S5 — `Φ` and the local record clauses (4 leaves, ≈ 0.5k)

| line | leaf | statement | sketch / tools | est. |
|---|---|---|---|---|
| 15106 | `ΦSub_bijective` | `Φ` is a bijection onto the `σ` slots | injective: `U2.σSlotA_spec/σSlotB_spec` give `colOf = evIdx (inr (crossOf p))` and `isDesc`; equal columns ⇒ equal crossings (`evIdx` injective on events) ⇒ `p ∈ {over, under}`; equal `isDesc` ⇒ same branch. Surjective: `U2.isσSlot_iff` ⇒ `u = σSlotA/B hW hk hℓ` with `letterAt (word F) k = σ m` ⇒ `eventAt k = inr q` (`letterAt_word`, `letterOf` of a cusp is not `σ`); take `p := ⟨q.1.1, _⟩` or the under branch; `crossOf p = q` (over-first pair unique: `eq_partner_of`) | 200 |
| 15113 | `ΦFun_partner` | `Φ (partner p) = σtwin (Φ p)` | `crossOf (partner p) = crossOf p` (`partner_partner`, `frontOver_partner`), `U2.σtwin_σSlotA/B` | 60 |
| 15116 | `isDesc_ΦFun` | `isDesc (Φ p) = frontOver p` | `U2.isDesc_σSlotA/B` | 30 |
| 15122 | `σsgn_ΦFun` | `σsgn (Φ p) = frontSgn p` | `U2.coe_σsgnCol`, `σSlotA_spec.1` (column `k`); bits at positions `m`, `m+1` of `cut (word F) k` = `dirBit over`, `dirBit under` (`run_take_eq_hybrid` at `k`, the `A ++ [over-bits, under-bits] ++ …` split of `step_hybrid`, `bit`/`getD`); `frontSgn` unfolded, `crossSign_eq_sign`, `crossSign_eq_one_iff_of_isOverUnder` (`+1` iff `0 < x'_o · x'_u` iff bits agree), `signType_intCast_injective` | 200 |

### Unit S6 — the traversal (11 leaves, ≈ 2.8k)

| line | leaf | statement | sketch / tools | est. |
|---|---|---|---|---|
| 15160 | `isSlot_slotAt` | `(colAt x, posAt x (i, fract t))` is a slot for `x = xOf i t ∉ singX` | `IsSlot` second disjunct: `1 ≤ posAt`, `posAt ≤ (cut (word F) (colAt x)).length` by `cut_word_colAt`, `cutBefore_eq_map_dirBit`, `length = card fibre` and `#{above} < card` (the point itself is not above); `colAt ≤ length` | 80 |
| 15167 | `slotAt_const` | the slot is constant along a regular arc off `singX` | `Subtype.ext`, `posAt_const_of_arc` | 40 |
| 15174 | `jump_regular` | crossing a singular x-value through a regular, non-double point: `slotAt (t+ε') = next^[m] (slotAt (t−ε'))`, no `σ` slot on the way | let the events at `x₀ = xOf i t` occupy columns `k₀..k₀+r`; for a rightward strand `slotAt (t−ε') = (k₀, pos)` (`colAt` just below `x₀`), and each column `k₀+j` maps the strand's position by `posR (letterAt k₀+j)` (`next_cases` case 1, `nextPair_right`, `bit` from `cut_word_colAt`/`run_take_eq_hybrid`; the strand's position in `hybridCut` vs `hybridCutStrict` differs by `coarity − arity` iff it is below the event: `hybridEntries` bookkeeping); `m = r + 1`; no `σ` slot: the strand's position is never `m_e` or `m_e + 1` of a crossing event `e` at `x₀` (it is not a branch: `hd`), so `shapeOf ≠ pass m (m+1)`/`pass (m+1) m`; leftward strand: mirror with `posL`, `nextPair_left`, columns descending | 400 |
| 15182 | `jump_cusp` | through a cusp `c`: the path passes `cuspVertex c`, no `σ` slot | left cusp: arrive leftward at cut `k+1` (`k = evIdx (inl c)`) position `m` or `m+1` (`posL_l_idx`/`_succ = none`: `nextPair_left_none` ⇒ `(k, 0)` = `cuspVertex c`), then `nextPair_cusp_l` ⇒ `(k+1, m or m+1)` rightward; right cusp: `posR_r_idx = none`, `nextPair_right_none`, `nextPair_cusp_r`; the tie columns before/after as in `jump_regular`; which arm is upper: `cusp_arm_sign`/`beforeBits`/`afterBits` and `Cont` | 400 |
| 15193 | `jump_cross` | through an occurrence `p`: the path passes exactly one `σ` slot, `Φ p`, at index `a` | rightward: at cut `k = evIdx (inr (crossOf p))` the strand is at position `m` (over) / `m+1` (under) — this slot IS `σSlotA`/`σSlotB` = `Φ p` (`σSlotA` unfolded with `bit W k m = true`); `posR_σ_idx`/`_succ` ⇒ `(k+1, m+1 / m)`; `IsσSlot` only there (`U2.isσSlot_iff`: a `σ` slot of column `k'` is `σSlotA/B k'`, i.e. one of the two crossing strands of column `k'`; our strand is a crossing strand only at `k`); leftward: enters at cut `k+1` — `σSlotA` is then `(k+1, m+1)` | 400 |
| 15203 | `path_no_occ` | no occurrence of the circle in `(t₀, t₁)` ⇒ a `next`-path from `slotAt t₀` to `slotAt t₁` with no `σ` slot | the parameters in `[t₀, t₁]` over singular x-values form a finite set (fibre over each of the finitely many `singX` values: `fibre_finite`, one period); induction on its size, splitting at the smallest: `slotAt_const` to just before it, `jump_regular` or `jump_cusp` across it (`Function.iterate_add_apply` to concatenate paths; the `¬σ` clauses concatenate) | 350 |
| 15210 | `path_cusps` | a `next`-path from `slotAt t₀` to `slotAt t₁` passing the cusp vertex of every cusp of the circle inside `(t₀,t₁)`, and every cusp vertex on it is a cusp of the circle | same induction with `jump_cusp` (vertex reached) and `jump_regular`/`jump_cross` (no cusp vertex passed — the slots visited are cut slots `(k, p ≥ 1)` except at cusps of the strand: add to the jump leaves' proofs or derive from `next_cases`: a cusp vertex `(k,0)` is entered only from an arm slot of THAT cusp letter, `nextPair_right_none`/`left_none`) | 300 |
| 15219 | `exists_cuspVertex_sameCycle` | every `next`-cycle carries a cusp vertex | a cycle of cut slots only keeps `xsign` (`xsign_next_iff`) and `xcoord2` strictly increases or decreases along it (`xcoord2_next`), contradicting periodicity (`iterate_period`); or geometrically: the slot `(k, p)` is an entry of a fibre point `q` of some circle, `u = slotAt`-like, then `path_cusps` | 120 |
| 15154 | `circleComp_bijective` | circles ↔ cycles | injective: `cuspVertex (someCuspOn i)` and `cuspVertex (someCuspOn i')` on one cycle ⇒ (from `slotAt (c.1.2 − ε)` of circle `i`, `jump_cusp`, `path_cusps` over one period: the cycle of `cuspVertex c` = the path of circle `i`, and every cusp vertex on it is a cusp of circle `i`) `i' = i`; surjective: `exists_cuspVertex_sameCycle` + `path_cusps` (any cusp `c` of circle `i` is on the cycle of `someCuspOn i`) ⇒ `slotComp u = circleComp c.1.1`; `U2.slotComp_eq_iff` | 150 |
| 15224 | `slotComp_ΦFun` | `slotComp (Φ p) = circleComp p.1.1` | `jump_cross` at `p` (Φ p on the path from `slotAt (t_p − ε')`, hence same cycle: `sameCycle_of_iterate`), `path_cusps` from `t_p − ε'` to `t_p − ε' + 1` reaches `cuspVertex (someCuspOn i)`, `U2.slotComp_eq_iff` | 150 |
| 15230 | `ΦFun_cycNext` | `Φ (cycNext p) = firstReturn (nextPerm hW) IsσSlot (Φ p)` | let `p' := cycNext p` (same circle, `comp_cycNext`; `cycNext_no_between` on `occComp`/`occKey`: no occurrence strictly cyclically between; `cycNext_ne_self` / `cycNext_eq_self` for the alone case), `t' :=` the lift of `p'.1.2` in `(t_p, t_p + 1]`; path = `jump_cross p` (Φ p at index `a < m₁`) ++ `path_no_occ` on `(t_p + ε', t' − ε'')` (`hno` from `cycNext_no_between`) ++ `jump_cross p'` (Φ p' at index `a'`); `Function.iterate_add_apply`; `firstReturn_eq_of_path` with `M = (m₁ − a) + m₂ + a' > 0` and the three `¬σ` clauses; `slotAt` is 1-periodic in `t` (`Int.fract_add_one`, periodicity of `xOf`) for the wrap `t' = t_p + 1` | 300 |

**Totals.**  S1 ≈ 2.6k, S2 ≈ 1.4k, S3 ≈ 0.3k, S4 ≈ 2.3k, S5 ≈ 0.5k, S6 ≈ 2.8k — **≈ 9.9k lines** (range 8-11k).

## 4. Units and dependencies

| unit | leaves | depends on (statements only) | size | parallel? |
|---|---|---|---|---|
| **S2 cusp** | `cusp_arm_sign`, `leftCusp_x_local`, `rightCusp_x_local`, `leftCusp_arms`, `rightCusp_arms` | U8R §F-G only | 1.4k | yes, start first (the rock) |
| **S3 crossing** | `cross_height_order` | U8R §F, `regular_local_graph` (S1; may be inlined) | 0.3k | yes |
| **S1 cut** | the 16 leaves of §3/S1 | S2, S3 (the limits at singular `a`); §H | 2.6k | yes (the analytic limits can assume S2/S3 as leaves) |
| **S4 word** | the 17 leaves of §3/S4 | S1 (`cutAfter_eq_cutBefore_of_gap`, `cutAfter_eq_cutBefore`) for `run_take_eq_hybrid`/`cut_word_colAt`; `regular_local_graph`, `rightCusp_x_local` for `cutBefore_first`/`cutAfter_last`; otherwise self-contained list combinatorics | 2.3k | yes; could be split S4a (`evKey_injective`…`hybridCut_eq_cutBefore`, `word_ne_nil`, `cuspCount_eq`: pure combinatorics, 1.2k) / S4b (`cutBefore_first`, `cutAfter_last`, `run_take_eq_hybrid`, `word_closed`, `downCountSyn_eq`, `cut_word_colAt`: 1.1k) |
| **S5 Φ** | `ΦSub_bijective`, `ΦFun_partner`, `isDesc_ΦFun`, `σsgn_ΦFun` | S4 (`run_take_eq_hybrid`, `step_hybrid`) for `σsgn_ΦFun` only | 0.5k | yes |
| **S6 traversal** | the 11 leaves of §3/S6 | S1 (`posAt_const_of_arc`, `cutBefore_eq_map_dirBit`), S4 (`run_take_eq_hybrid`, `cut_word_colAt`, `step_hybrid`, `events_pairwise_lt`), S2 (`leftCusp_x_local`, `cusp_arm_sign`, arms), S3, S5 (`ΦFun` unfolded) | 2.8k | yes; split S6a (`isSlot_slotAt`, `slotAt_const`, `jump_regular`, `jump_cusp`, `jump_cross`: 1.3k) / S6b (`path_no_occ`, `path_cusps`, `exists_cuspVertex_sameCycle`, `circleComp_bijective`, `slotComp_ΦFun`, `ΦFun_cycNext`: 1.4k) |

Every leaf can be attacked immediately (all dependencies are `sorry`'d statements in the same file); the order above
minimises the risk that a false intermediate statement is discovered late: S2/S3 first, then S1, then S4, S5, S6.

## 5. Decisions and readings (where the accepted vocabulary does not pin the choice)

1. **The cut line of an event with ties** is the hybrid cut (`hybridCut`): events of one x-value are processed
   bottom to top; positions are read from the top on the cut before the event.  Different from the printed "separate
   them by small local x translations" only as a proof device (no `deform_*`; U8R report §3).
2. **The slot of an occurrence** is `σSlotA` (over) / `σSlotB` (under) of the crossing's column, NOT `slotAt (t_p ∓ ε)`:
   with tie events below the crossing the latter is an earlier column (a first draft of the skeleton had the leaf
   `ΦFun_eq_slotAt` asserting the equality; it is FALSE and was removed; `jump_cross` places `Φ p` on the path).
3. **`Cont`** fixes the arm of a cusp entry by `(s < t_c) ↔ (j = 0 ↔ cuspDisc < 0)`; this is FR-2 (the later arm is
   the upper one iff `0 < cuspDisc`) and is the same clause for the two arms before a right cusp and after a left cusp.
4. **`events`/`fibreList*` via `List.mergeSort`** with Bool comparators (total, transitive) rather than `Finset.sort`
   with a lifted `LinearOrder`: no injectivity proof is needed inside the definitions (`evKey_injective` is a leaf).
5. **Sort keys at a double point** decide the before/after orders by slope (`beforeLE`: smaller slope first); no
   perturbation.  Two fibre points with equal height and slope cannot exist (`slope_ne_of_isDouble`).
6. **The circle bijection `e`** is `slotComp` of the cusp vertex of a chosen cusp of each circle (`someCuspOn`);
   well-definedness and bijectivity are the leaf `circleComp_bijective`.
7. **No import added**; the Taylor leaf must be done with `hasDerivAt_iff_isLittleO` / `exists_ratio_hasDerivAt_eq_ratio_slope`
   (`Mathlib.Analysis.Calculus.Taylor` is not in the closure).

## 6. Leaves I am not fully sure are true as stated

* `jump_regular` / `jump_cusp` / `jump_cross` (S6): the `¬ IsσSlot` clauses on ALL indices `j < m` (including `j = 0`
  and the slots at cuts of tie columns).  Argument: a `σ` slot of column `k'` is one of the two crossing strands of
  `k'` (`U2.isσSlot_iff`); our strand is a crossing strand only at its own occurrences.  I believe this is right;
  if a prover finds a counterexample with a leftward strand at cut `k+1`, weaken to `0 < j`.
* `exists_cuspVertex_sameCycle`: true (a cycle without cusp vertices would be a strand crossing the finitely many cut
  lines monotonically), but I have not checked that U2/β2 has the monotonicity lemma in a directly usable form
  (`xcoord2_next` exists, FrontRealizeSlots L1119).
* `cutBefore_first`/`cutAfter_last`: rely on "the min of `x` on the front is a cusp" (Rolle-type: `IsLocalMin` ⇒
  `x' = 0` ⇒ cusp by `no_vertical`) and "every fibre point over `x_min` is a LEFT cusp" — a right cusp at `x_min`
  is impossible since its arms lie to the left.  True; the compactness/min argument is the cost.
* `entriesBefore_left_limit` / `entriesAfter_right_limit` at a NON-singular `a` are the local constancy of the cut;
  at a singular `a` they encode all local models at once.  They are true but are the most delicate statements to
  prove (list-level identification); if a unit stalls, `cutBefore_left_limit`/`cutAfter_right_limit` (bits only) and
  `posAt_const_of_arc` are what S4/S6 actually consume — a prover may prove those directly and leave the entry-level
  leaves as the last item.

## 7. Verdict

The route is complete: `sweep_proof` and `represent` are proved from 54 leaves whose statements typecheck against the
accepted vocabulary and U2's slot record, all local statements were checked against `IsDownCusp`/`cuspDisc`/`slope`,
the letter conventions of `FrontWords`/`FrontRealizeSlots`, and "over = smaller slope" (§2).  The U8R report's
**5.5-8k estimate is optimistic**: I estimate **≈ 9.9k lines (8-11k)** for the 54 leaves, the excess coming from
the traversal unit S6 (the three jump leaves and the two path inductions, ≈ 2.8k, vs the report's R6 1.8-2.5k) and
from the entry-level limits of S1 (≈ 1k on top of R3).  Feasible in one wave of 6-8 parallel provers (S2, S3, S1,
S4a, S4b, S5, S6a, S6b), each 0.3-1.5k lines; S1 and S6 are the ones most likely to need a second pass.

## Appendix — compile logs

Full compile of `W3_U8R_Skeleton.lean`: `/tmp/u8s/full2.log`; axioms probe (`/tmp/u8s/W3_ax.lean` = the skeleton +
`#print axioms SM.FrontRows.represent`, `SM.FrontRows.U8R.sweep_proof`, `SM.ng_commutation`): `/tmp/u8s/ax.log`.
Numerical checks: `/tmp/u8s/check.py`.
