# W3S_S1b_REPORT — unit S1b of the U8R sweep (the one-sided limits of the cut, `posAt_const_of_arc`)

2026-09-14, prover for unit S1b (PLAN `W3_U8R_PLAN.md` §3 Unit S1, the last 8 leaves).
File: `work/drafts/frontrows/W3S_S1b.lean` (16,649 lines; skeleton 15,587).
Compile: `cd work/lean && lake env lean ../drafts/frontrows/W3S_S1b.lean` — **0 errors, exit 0, ~39 s**;
`grep -c sorry` **58 before → 52 after** (the 52 are the 4 front-move leaves, the 44 leaves of the other sweep
units, and the two S1b leaves below that are FALSE as stated).  Every statement, name and docstring of the skeleton
is byte-identical (checked by a sorted diff of all declaration lines: the only changes are `:= sorry` → `:= by` on
the six proved leaves, plus the added `s1b_*` declarations).

## 1. Result

| leaf | line (new file) | status |
|---|---|---|
| `entriesBefore_left_limit` | 15939 | **PROVED** |
| `entriesAfter_right_limit` | 15962 | **PROVED** |
| `dirBit_of_cont_before` | 15987 | **left `sorry` — FALSE as stated** (§3); corrected form proved as `s1b_dirBit_of_cont_before` |
| `dirBit_of_cont_after` | 15991 | **left `sorry` — FALSE as stated** (§3); corrected form proved as `s1b_dirBit_of_cont_after` |
| `cutBefore_left_limit` | 15995 | **PROVED** |
| `cutAfter_right_limit` | 16007 | **PROVED** |
| `cutAfter_eq_cutBefore_of_gap` | 16021 | **PROVED** |
| `posAt_const_of_arc` | 16047 | **PROVED** |

The four leaves S4/S6 actually consume (`cutBefore_left_limit`, `cutAfter_right_limit`,
`cutAfter_eq_cutBefore_of_gap`, `posAt_const_of_arc`) are all proved, and so are the two entry-level limits the
architect doubted (PLAN §6, last bullet): they are true as stated and proved in full (at singular `a` included).
The two `dirBit_of_cont_*` leaves are not consumed by any other leaf (PLAN §3 lists them only as tools for
`cutBefore_left_limit`, which is proved without them: the combination lemma carries the bits directly).

## 2. THE MERGER MUST KNOW: file-order dependency, S2/S3 relocated

The S1 limits at a singular `a` use the S2/S3 leaf STATEMENTS (`cusp_arm_sign`, `leftCusp_x_local`,
`rightCusp_x_local`, `leftCusp_arms`, `rightCusp_arms`, `cross_height_order`), exactly as PLAN §4 says
("S1 depends on S2, S3").  In the skeleton those six leaves are declared AFTER the S1 leaves (skeleton lines
14952-14993 vs 14914-14950), so Lean cannot see them from the S1b block placed "immediately before the first S1b
leaf".  Resolution in this file: the S2/S3 block (skeleton lines 14952-14994, header comments included) was
**moved verbatim** to lines 14913-14955 of the new file, right after `exists_eta_fibre_near` and before the S1b
helper block, with a 3-line `/-! … -/` note at 14910-14912 explaining the move.  No character of the six leaves
changed (verified with `cmp` before splicing; the `diff` against the skeleton aligns them as unchanged lines).
Their dependencies (U8R §F-G, and `regular_local_graph` at 14897 for S3) still precede them, so the S2/S3 provers'
bodies drop in unchanged at the new position.

**Rule for the merged file: the S2 and S3 leaves must precede the `S1b helpers` block.**  Equivalently, the
merged order of the sweep leaves should be S1a → S2 → S3 → S1b → S4 → S5 → S6 (the dependency order of PLAN §4).

New-file layout: 14865 `#### S1 leaves` header; 14867-14908 the S1a leaves (untouched); 14910-14955 relocation note
+ S2/S3 block; 14958-15933 `/-! ### S1b helpers -/ section S1bHelpers … end S1bHelpers` (976 lines, 54
declarations); 15935-16070 the eight S1b leaves (docstrings and statements byte-identical, six bodies filled);
16072 `#### S4 leaves` header, everything after unchanged.

## 3. The two false leaves: exact counterexample and the missing hypothesis

`dirBit_of_cont_before {q} {a} (ha : ¬ F.IsLeftCusp a.1) (hj : a.2 < (beforeBits F a.1).length) (h : Cont F q a) :
dirBit F q = entryBit F (beforeBits F) a`.  `Cont F q a` only forbids cusps STRICTLY between the lifted parameter
`s` of `q` and `a.1.2`; `q` itself may be a cusp.  Take `a.1 = (i, t₀)` regular with `0 < xvel F i t₀` (so
`beforeBits F a.1 = [true]`, `a.2 = 0`, `hj` and `ha` hold, `entryBit … = true`) and `q = (i, c)` with `c` the
first cusp parameter after `t₀` (it exists: `exists_arc_mem` puts `t₀` on a closed arc `[c₀, arcEnd c₀]`, and
`c := arcEnd c₀` when `t₀ < arcEnd c₀`; `not_isCusp_of_mem_arc` gives "no cusp strictly between").  Then
`Cont F q a` holds with `s := c`, but `dirBit F q = decide (0 < xvel F i c) = false` since `xvel = 0` at a cusp.
Every front has such configurations (every circle has ≥ 2 cusps and regular points), so the statement fails for
every `F`.  The same for `dirBit_of_cont_after`.  (Not built as a kernel-checked counterexample: constructing a
concrete `SmoothFront` is a separate project; the argument above uses only accepted facts of §F-H.)

**Missing hypothesis:** `¬ F.IsCusp q` (equivalently `xvel F q.1 q.2 ≠ 0`; automatic for `q ∈ totalFibre F x`
with `x ∉ singX F`, which is the only situation the sweep uses).  Proved with it:
```
theorem s1b_dirBit_of_cont_before {q} {a} (hq : ¬ F.IsCusp q)
    (hj : a.2 < (beforeBits F a.1).length) (h : Cont F q a) : dirBit F q = entryBit F (beforeBits F) a
theorem s1b_dirBit_of_cont_after  {q} {a} (hq : ¬ F.IsCusp q)
    (hj : a.2 < (afterBits F a.1).length)  (h : Cont F q a) : dirBit F q = entryBit F (afterBits F) a
```
(`ha : ¬ F.IsLeftCusp a.1` of the frozen statement is redundant — it follows from `hj` — and was dropped.)  If the
architect amends the leaves to add `(hq : ¬ F.IsCusp q)`, the bodies are
`s1b_dirBit_of_cont_before F hq hj h` / `s1b_dirBit_of_cont_after F hq hj h`.

## 4. How the limits are proved (the helper block, 54 declarations, all `s1b_`-prefixed)

The design: one **local model** per fibre point, one **generic combination** lemma, two **wrappers** (left/right
side), then the leaves are short.

* `s1b_Local F p bits δ x l` (def): `l : List ℝ` is the list of the parameters (within `δ` of `p.2`, top to
  bottom) of the strands of `p` over `x`: `l.length = (bits p).length`; every `s ∈ l` has `|s - p.2| < δ` and
  `xOf F p.1 s = x`; complete (every such `t` is in `l`); strictly descending in `z`; and for each index `j`,
  `Cont F (p.1, l[j]) (p, j)` together with `dirBit F (p.1, l[j]) = (bits p).getD j false`.
* Instances: `s1b_local_regular` (one strand, from `regular_local_graph`; both sides; needs only `x ≠ a`),
  `s1b_local_two_arms` (generic two-arm model: arms `t₁ < t₀ < t₂`, the earlier arm carries the bit `b₁`, the later
  `!b₁`, `bits (i,t₀) = if cuspDisc < 0 then [b₁, !b₁] else [!b₁, b₁]`; order from `cusp_arm_sign`, index `j`
  from the `Cont` clause), specialised to `s1b_local_rightCusp_before` (`rightCusp_x_local`, `rightCusp_arms`,
  `exists_xvel_sign_of_isRightCusp`, `b₁ = true`) and `s1b_local_leftCusp_after` (`leftCusp_*`, `b₁ = false`);
  `s1b_local_empty` for `s1b_local_leftCusp_before` / `s1b_local_rightCusp_after` (strict local extremum of `x`).
  `s1b_arms_ne`: two arms at equal height over a non-singular `x` would be a double point (the reason the local
  lemmas take `x ∉ singX F`).
* `s1b_ord_of_lt`: fibre points of different heights stay strictly ordered nearby (continuity of `z`).
* `s1b_combine a I bits P`: from `∀ p ∈ P` a local model (with a shrinkable `δ`) and a pairwise ordering
  hypothesis (`P.Pairwise (∃ δ, ∀ s s' near, xOf equal → x ∈ I → z-order)`), produce, for `x` near `a` on the
  side `I` and off `singX`, the list `L := P.flatMap (fun p => (l p).map (fun s => (p.1, Int.fract s)))` with:
  `q ∈ L ↔ q ∈ totalFibre F x` (⇐ by `exists_eta_fibre_near`: every fibre point over `x` is within `δ` mod 1 of a
  fibre point over `a`, then completeness of the local model), `L.Pairwise (ht desc, strict)`
  (`List.pairwise_flatMap`), `List.Forall₂ (s1b_ContNear F δ) L (entriesOf F bits P)` and
  `L.map dirBit = P.flatMap bits`.  Note: NO separation argument between distinct fibre points is needed — nodup of
  `L` follows from the strict height order.  Radii are uniformised over the finite list by `s1b_uniform` /
  `s1b_uniform_pairwise`.  `s1b_ContNear δ q e := Cont F q e ∧ ∃ s, SameParam q (e.1.1, s) ∧ |s - e.1.2| < δ`
  (the `δ`-information is what `posAt_const_of_arc` needs to identify the strand; the bare `Cont` of the frozen
  leaf statement is too weak for that — see §5).
* `s1b_before a` / `s1b_after a`: the wrappers with `I = Set.Iio a` / `Set.Ioi a`, `P = fibreListBefore a` /
  `fibreListAfter a`, `bits = beforeBits` / `afterBits`; the ordering hypothesis from `fibreListBefore_pairwise`
  (`beforeLE` = lex `(−ht, slope)`: different heights → `s1b_ord_of_lt`; equal heights → a double point, over
  first → `cross_height_order` clause 1) resp. `afterLE` (under first → `cross_height_order` clause 2 with the pair
  swapped).  Output: `∃ δ₀ > 0, ∀ δ ≤ δ₀, ∃ η > 0, ∀ x, |x − a| < η → x < a → x ∉ singX → ∃ L, mem ∧ pairwise ∧
  Forall₂ (ContNear δ) L (entriesBefore a) ∧ L.map dirBit = cutBefore a` (and the mirror with `entriesAfter`,
  `cutAfter`).
* The leaves: `fibreListBefore F x = L` by the S1a black box `fibreListBefore_eq_of` (nodup and `beforeLE`-sorted
  from the strict height order: `s1b_nodup_of_pairwise_lt`, `s1b_beforeLE_of_lt`); `entriesBefore F x =
  L.map (·, 0)` by `entriesBefore_eq_of_notMem_singX`; `cutBefore F x = L.map dirBit` by `cutBefore_eq_map_dirBit`;
  `η` also shrunk so that `(a − η, a)` avoids the finite `singX` (`s1b_exists_eta_left/right`).
  `cutAfter_eq_cutBefore_of_gap`: `cutBefore` is locally constant on `Ioo a b` (both limits + `cutAfter_eq_cutBefore`
  at each interior point), hence constant (`s1b_const_of_locally_const_on`: `IsPreconnected.constant` with the
  discrete topology put on the codomain locally — works for `Cuts = List Bool` and for `ℕ`), then the two end limits.
  `posAt_const_of_arc`: `colAt` by IVT (`intermediate_value_uIcc`) and `s1b_evX_mem_singX` (`s1b_colAt_const`);
  `posAt` by local constancy in the parameter (`s1b_posAt_locally_const`) on `Icc t₀ t₁`: at `t`, take the
  left/right lists `L` at `x = xOf i t'`, locate `(i, fract t')` in `L` at index `j₁`, read its `ContNear` entry
  `(P[j₁], 0)` with `P = fibreListBefore (xOf i t)`, and show `P[j₁] = (i, fract t)` from the `δ`-bound and the
  injectivity of `x` near the regular `t` (`regular_local_graph`), so `j₁` is the index of `(i, fract t)`;
  `posAt = index + 1` on a strictly descending fibre list (`s1b_posAt_eq_index`).

Black boxes used (statements only): S1a `fibreListBefore_eq_of`, `fibreListAfter_eq_fibreListBefore`,
`cutBefore_eq_map_dirBit`, `cutAfter_eq_cutBefore`, `entriesBefore_eq_of_notMem_singX`, `regular_local_graph`,
`exists_eta_fibre_near`; S2 all five; S3 `cross_height_order`.  Not used: `fibreListAfter_eq_of`, `word_closed`,
anything of S4-S6.  From the accepted layer: §F-H of U8R (`xvel_mul_pos_of_cuspFree`, `exists_xvel_sign_of_is*Cusp`,
`mem_singX_of_isCusp/isDouble`, `regular_of_notMem_singX`, `snd_injOn_totalFibre`, `left_right_absurd`, …) and
`FrontSmooth` (`SameParam`, `eval_of_sameParam`, `vel_of_sameParam`, `isCusp_iff_of_sameParam`,
`isOverUnder_of_mem_crossingPairs`, `slope_ne_of_isDouble`, `cuspDisc_ne_zero_of_isCusp`).

## 5. Pitfalls and readings (for the merger and for S6)

1. **File order** (§2) — the only structural change.  The same issue will hit any unit whose helpers use later
   leaves; S4b/S6 provers should check that the leaves they cite precede their blocks.
2. The frozen `Cont` carries no quantitative information (only "no cusp strictly between").  For `posAt_const_of_arc`
   this is NOT enough to identify the continued strand from the frozen `entriesBefore_left_limit`; the proof uses the
   internal `s1b_before/after` (with `s1b_ContNear δ`).  S6 (`jump_*`) will likely want the same: use
   `s1b_before`/`s1b_after` (they are in namespace `SM.FrontRows.U8R`, available after the block) rather than the
   frozen leaves.
3. `dirBit_of_cont_*` are false as stated (§3); the corrected `s1b_dirBit_of_cont_*` are available.
4. Lean/Mathlib names at this pin: `if_neg`/`if_pos` are deprecated in favour of `ite_eq_right`/`ite_eq_left`
   (same signatures); the triangle inequality is `abs_add_le`; `List.filter_toFinset` (not `Finset.…`);
   `List.pairwise_flatMap`, `List.forall₂_iff_get`, `List.rel_append`, `List.flatMap_congr`,
   `List.Nodup.getElem_inj_iff` (implicit index proofs), `Prod.Lex.toLex_le_toLex/lt_toLex`, `Int.fract_add_intCast`,
   `Int.fract_eq_iff`, `intermediate_value_uIcc`, `IsPreconnected.constant`, `Metric.continuous_iff`.
5. `rw` with `L[j]` inside the motive fails ("motive is not type correct") when rewriting `L` itself; generalise the
   element first (`obtain ⟨q, hq⟩ : ∃ q, q = L[j] := ⟨_, rfl⟩; rw [← hq]`), as in `s1b_posAt_eq_index`.
6. `SameParam (i, Int.fract s) (i, s)` is `s1b_sameParam_fract`; the invariance lemmas (`s1b_ht_of_sameParam`,
   `s1b_dirBit_of_sameParam`, `s1b_xOf_of_sameParam`) are stated as `f q = f p` for `SameParam p q`, so rewriting
   `f (i, fract s)` needs `←`.
7. Anonymous constructors work for `Cont`, `s1b_Local` and `s1b_ContNear` (plain `def`s unfolding to `∧`/`∃`).
8. `F.IsCusp p` vs `F.IsCusp (p.1, p.2)`: handled by destructuring `obtain ⟨i, t₀⟩ := p` at the start of the local
   lemmas (gotcha W2_U8R_REPORT §5.3).
9. No import added; no `open Classical`; no `set_option`.  Warnings in the block: none (the linter's `letI → let`
   suggestion was applied).

## 6. Truth of the S1b statements (PLAN §6 check)

* `entriesBefore_left_limit` / `entriesAfter_right_limit`: TRUE as stated, proved.  The `Cont` clause for the two
  arms of a cusp (`j = 0` upper ↔ earlier arm iff `cuspDisc < 0`) matches `cusp_arm_sign` exactly; the ordering at a
  double point matches `beforeLE`/`afterLE` and both clauses of `cross_height_order`; the bit conventions of
  `beforeBits` (right cusp: arriving arm rightward = `true`) and `afterBits` (left cusp: leaving arm rightward) come
  out right from `exists_xvel_sign_of_isRightCusp/LeftCusp`.
* `cutBefore_left_limit`, `cutAfter_right_limit`, `cutAfter_eq_cutBefore_of_gap`, `posAt_const_of_arc`: TRUE, proved.
* `dirBit_of_cont_before/after`: FALSE (§3); true with `¬ F.IsCusp q`.

## Appendix — the S1b declarations (new-file order, all in `SM.FrontRows.U8R`, section `S1bHelpers`)

generic: `s1b_uniform`, `s1b_uniform_pairwise`, `s1b_const_of_locally_const_on`, `s1b_forall₂_flatMap`,
`s1b_decide_pos_eq`, `s1b_entriesOf_eq_map`; periodicity/`SameParam`: `s1b_xOf_add_int`, `s1b_zOf_add_int`,
`s1b_xOf_of_sameParam`, `s1b_ht_of_sameParam`, `s1b_dirBit_of_sameParam`, `s1b_sameParam_fract`,
`s1b_cont_of_sameParam`, `s1b_ht_eq_zOf`, `s1b_xOf_eq_of_mem_totalFibre`, `s1b_mem_totalFibre_fract`; singular
values: `s1b_exists_eta_left`, `s1b_exists_eta_right`, `s1b_evX_mem_singX`; height order: `s1b_nodup_of_pairwise_lt`,
`s1b_beforeLE_of_lt`, `s1b_afterLE_of_lt`, `s1b_fibreListBefore_pairwise_lt`, `s1b_fibreFinset_eq`,
`s1b_posAt_eq_index`; local models: `s1b_Local` (def), `s1b_ContNear` (def), `s1b_bits_regular_before`,
`s1b_bits_regular_after`, `s1b_mem_Ioo_of_abs`, `s1b_abs_of_mem_Ioo`, `s1b_between_abs`, `s1b_local_regular`,
`s1b_local_empty`, `s1b_local_two_arms`, `s1b_arms_ne`, `s1b_local_rightCusp_before`, `s1b_local_leftCusp_after`,
`s1b_local_leftCusp_before`, `s1b_local_rightCusp_after`, `s1b_ord_of_lt`; combination: `s1b_combine`,
`s1b_before`, `s1b_after`; `posAt`/`colAt`: `s1b_colAt_const`, `s1b_posAt_side`, `s1b_posAt_locally_const`;
corrected `dirBit` leaves: `s1b_beforeBits_rightCusp`, `s1b_afterBits_leftCusp`, `s1b_xvel_side`,
`s1b_dirBit_of_cont_cusp_aux`, `s1b_dirBit_eq_of_cuspFree`, `s1b_dirBit_of_cont_before`, `s1b_dirBit_of_cont_after`.

Scratch used for the 15-s iteration loop: `/tmp/s1b/Work.lean` (imports + U8R §A,§F-H + SweepDefs + S1-S3 leaves,
assembled by `/tmp/s1b/assemble.sh`); full-file logs `/tmp/s1b/full.log`, `/tmp/s1b/full2.log`.
