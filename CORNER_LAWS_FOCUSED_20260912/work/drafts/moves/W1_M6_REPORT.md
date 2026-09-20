# W1_M6_REPORT — unit U-M6 of the moves toolkit (Wave 1)

U-M6 (subagent), 2026-09-15 ≈ 20:05 UTC / 4:05pm ET.  File: `work/drafts/moves/W1_M6.lean`
(= `Skeleton_W1.lean` with the five U-M6 bodies filled and `um6_` helpers inserted; 2324 lines).
Compile: `cd work/lean && lake env lean ../drafts/moves/W1_M6.lean` → exit 0, **0 errors**, 1 pre-existing
cosmetic linter warning (`<;>` at line 696, the skeleton's line 565), ≈ 13 s.  Nothing under `work/lean` was written.

## 0. Result

| item | before (Skeleton_W1) | after (W1_M6) |
|---|---|---|
| `declaration uses sorry` | 33 | **28** |
| `grep -c sorry` | 34 | **29** (28 bodies + the frozen header comment, line 17) |
| U-M6 sub-leaves closed | — | **5 / 5**: `BigonData.reducedRecord_counts` (191), `Record.restrictCrossings_switch` (262), `m6_exists_origVisit` (1588), `m6_key_lt_iff` (1873), `m6_succ` (1927) |
| unproved in the unit | — | none |
| statement identity | — | `check_W1_identity.py Statements_FINAL.lean W1_M6.lean`: all **37** Statements_FINAL declarations byte-identical statements ✓; suffix identical except the body of `exists_rii_deletion` ✓; **prefix (lines 1–136) byte-identical: False — unavoidable and expected**: the two frozen record leaves of THIS unit sit at lines 118/132 of the prefix, so their `sorry` bodies (lines 122, 135) had to be replaced and their helpers inserted before them.  Additional checks run: lines 1–113 (up to and including the `### 1b` header) byte-identical ✓; every prefix line except the two `  sorry` bodies appears verbatim and in order in W1_M6 ✓; all **267** skeleton declarations keep byte-identical statements (same `statements()` extractor applied Skeleton_W1 → W1_M6) ✓; the only new declarations are the 30 `um6_` helpers listed in §2 ✓ |

`#print axioms` (scratch copy of the file with the prints appended; standard = `propext, Classical.choice, Quot.sound`):
* `BigonData.reducedRecord_counts` — **standard only**
* `Record.restrictCrossings_switch` — **standard only**
* `m6_exists_origVisit`, `m6_key_lt_iff`, `m6_succ`, `recordIso` — standard + `sorryAx`, inherited ONLY from the
  black boxes of other units they are stated on: `m3_exists_lift` (exists_origVisit), `m3_kind_ne_mid`,
  `m3_crossingParam`, `m2_generic` via `reducedDiagram` (key/succ).  The U-M6 helpers that do not touch those
  (`um6_key_injOn`, `um6_blocks_range`, …) print standard only; `um6_block_i` prints `sorryAx` through
  `m3_kind_ne_mid`/`m3_crossingParam` as expected.

## 1. What was proved, and how (template Smoothing §8 / the record files)

* **`Record.restrictCrossings_switch`** (line 262).  `RecordIso.mk (Equiv.refl _) (Equiv.refl _)` with
  `comp_eq/succ_eq/pair_eq := rfl` (`Record.switch` keeps `M, comp, succ, pair`, and `(ρ.switch v).CrossKeep S`
  is definitionally `ρ.CrossKeep S`, so the two `restrictCrossings` have the same `M` and the same
  `firstReturn`); bits and signs by `um6_restrict_switch_bit/sgn`, stated for an arbitrary retained occurrence
  `x : (ρ.restrictCrossings S).M` and proved by cases `w = x`, `w = pair x`, else, with
  `Record.switch_isOver_self/pair/of_ne` (resp. `switch_sgn_*`) on both records.  (Stating the helper with
  `x` rather than `⟨v, hv⟩` matters: the anonymous constructor elaborates at type `{v // CrossKeep S v}`, not
  syntactically `(restrictCrossings S).M`, and `rw` then fails at instance transparency.)
* **`BigonData.reducedRecord_counts`** (line 191).  `Fintype.card M' + 4 = Fintype.card D.Γ.Visit` via
  `Equiv.subtypeEquivRight` (retained ↔ `¬ v.1 ∈ {y, z}`, `um6_crossKeep_iff_not_mem`),
  `Fintype.card_subtype_compl`, and `um6_card_deleted : card {v // v.1 ∈ {y, z}} = 4`
  (`Equiv.subtypeSigmaEquiv` + `Fintype.card_sigma` + `Finset.card_pair (um6_y_ne_z)`); then
  `two_mul_crossingCount` on both records and `omega`.  Writhe: `two_mul_writhe` on both records,
  `Fintype.sum_subtype_add_sum_subtype`, `um6_sum_deleted : ∑_{deleted} σ = 2 (σ y + σ z)` (same sigma
  equivalence + `Fintype.sum_sigma` + `Finset.sum_coe_sort` + `Finset.sum_pair`), `Fintype.sum_equiv` for the
  retained sum, `omega`.  `um6_y_ne_z` is re-proved directly from `hy, hz, hj, hk` (the §1c.0 `y_ne_z` comes
  after this leaf in the file) and `um6_crossKeep_keep_iff` is a copy of §1c.8's `crossKeep_keep_iff` for the same
  reason.
* **`m6_exists_origVisit`** (line 1588).  `crossKeep_keep_iff` → `x ≠ y, z`; `m3_exists_lift` gives `y'` with
  `origCrossing C y' = x`; `s ∈ x.val = {orig y'.fst, orig y'.snd}` picks the lifted strand; the visit
  `⟨y', ⟨u, hu⟩⟩` maps to `⟨x, ⟨s, hs⟩⟩` by `congrArg` + `Subtype.ext` (no strand lift needed beyond M3's).
* **`m6_key_lt_iff`** (line 1873).  Component `≠ i`: `um6_coord_other` — the reduced coordinate IS the key
  (`kind = old ⟨i', n.val⟩`, `liftParam = id`, `(n.val : ZMod k_{i'}).val = n.val`).  Component `i`:
  `um6_block_i` puts every occurrence in one of three blocks of the reduced coordinate `r = m + θ'`
  (`m` the reduced label, `θ'` the reduced crossing parameter):

  | block | kind | `r ∈` | key `= um6_F C b r` | key range |
  |---|---|---|---|---|
  | 0 | `cutIn` (`m = 0`) | `[0, 1)` | `t_M · r` (`θ = t_M θ'`, `rexB_rot k a.val (a.val + θ) = θ`) | `[0, t_M)` |
  | 1 | `cutOut` (`m = 2`) | `[2, 3)` | `j + t_q + (r − 2)(1 − t_q)` (`θ = t_q + θ'(1 − t_q)`, `um6_rot_val_add j`) | `[j + t_q, j + 1)` |
  | 2 | `old ⟨i, a + (j + m − 2)⟩` (`m ≥ 3`) | `[3, k')` | `r + j − 2` (`um6_rot_val_add (j + m − 2)`) | `[j + 1, k)` |

  `m = 1` (`mid`) is excluded by `m3_kind_ne_mid`; the parameter facts `θ < t_M` / `t_q < θ` come for free from
  `crossingParam_pos/lt_one` of the REDUCED diagram through `m3_crossingParam` (`liftParam ∈ (0,1)`), so no
  `Cut.clear`/`in_iff` argument is needed.  Then `Smoothing.lt_iff_of_blocks 3` with `um6_blocks_lohi/chain/
  mono/range` (the chain `t_M ≤ j + t_q`, `j + 1 ≤ j + 1`, `k' + j = k + 2`).  `um6_rot_val_add` is the
  `τ = 0` variant of Smoothing's `cyclicOffset_val_add` (that lemma needs `0 < τ`; here the rotation base is the
  vertex `M₀`, parameter `0`).
* **`m6_succ`** (line 1927).  Exactly `Smoothing.succ_of_coord`'s argument: the first return `fr` of
  `origVisit v` is on its `visitSucc`-cycle and retained, so `fr = origVisit v'` (`m6_exists_origVisit`);
  `um6_comp_iff_sameCycle` (components of `D'` = `visitSucc`-cycles of `D` under `origVisit`, from
  `compOf_origVisit` + `Record.sameCycle_iff_comp_eq`); if `v` is alone on its component both sides are `v`;
  otherwise `v' ≠ v` (a fixed point of the first return would make its cycle a singleton), no occurrence lies
  between `v` and `v'` (`cycBetween` transported through `m6_key_lt_iff` three times, then
  `firstReturn_no_between D.visitSucc (CrossKeep keep) B.key` with `um6_key_injOn` and
  `um6_key_nextVisit_no_between` — the latter from `rexB_cycBetween_rot` + `nextVisit_no_between`), and
  `cycNext_unique_on` on `D'.visitCoord` identifies `D'.nextVisit v = v'`.

## 2. Helpers added (all `um6_`-prefixed, each immediately before the sub-leaf using it, same section)

Before `reducedRecord_counts` (namespace `BigonData`, after the `### 1b` header): `um6_y_ne_z`,
`um6_crossKeep_keep_iff`, `um6_crossKeep_iff_not_mem`, `um6_card_fiber`, `um6_card_deleted`, `um6_sum_deleted`.
Before `Record.restrictCrossings_switch` (top level of `SM.Link`): `um6_restrict_switch_bit`,
`um6_restrict_switch_sgn`.
Before `m6_key_lt_iff` (section `Construction`, after `key`): `um6_key_of_i`, `um6_key_of_ne`,
`um6_coord_bounds`, `um6_a_bounds`, `um6_rot_val_add`, `um6_kind_mk_i'`, `um6_kind_mk_of_ne'`,
**five `def`s** `um6_lo`, `um6_hi`, `um6_flo`, `um6_fhi`, `um6_F` (the block bounds and affine maps, by
pattern matching on `ℕ` — an `if b = 0 …` form does not reduce under `simp only` after `interval_cases`),
`um6_blocks_lohi`, `um6_blocks_chain`, `um6_blocks_mono`, `um6_blocks_range`, `um6_block_i`, `um6_coord_other`.
Before `m6_succ`: `um6_key_injOn`, `um6_key_cycBetween`, `um6_key_nextVisit_no_between`,
`um6_comp_iff_sameCycle`.  (30 declarations; the five `def`s are data for `lt_iff_of_blocks`, not lemmas —
flagged here in case the executor wants helpers to be theorems only; they could be inlined as lambdas.)

## 3. Notes for the executor / other units

1. **The prefix criterion of `check_W1_identity.py` cannot pass for U-M6** (part 1 of the script), since the
   unit's two record leaves live in the frozen prefix.  Parts 2 and 3 pass; the extra checks of §0 show that
   nothing but the two `sorry` bodies changed there (plus insertions).  Suggest the executor run the script with
   `NPRE = 113` for this file, or accept the §0 evidence.
2. No sub-leaf of U-M6 was false or needed a stronger hypothesis.  In particular `m6_key_lt_iff` needs no
   `Cut.clear`/`in_iff` reasoning: the retained `e_in`-occurrences have `θ < t_M` and the retained
   `e_out`-occurrences `θ > t_q` automatically because the REDUCED crossing parameter lies in `(0,1)`
   (`m3_crossingParam`).
3. Pitfalls met (beyond §4 of W1_SKELETON_REPORT): (a) `rw` on `D'.visitCoord ⟨y', ⟨⟨B.i, n⟩, hn⟩⟩` fails
   ("motive not type-correct at implicit transparency", the `Shadow.Crossing` subtype coercion inside `hn`) —
   use `set v0 := ⟨y', ⟨⟨B.i, n⟩, hn⟩⟩` and rewrite on `v0`, as Smoothing's `mixed_block` does;
   (b) `Fintype.card_congr`/`Fintype.sum_equiv` with `Equiv.subtypeSigmaEquiv` on `D.Γ.Visit` must be applied by
   `refine (…).trans ?_`, not `rw` (`Visit` is a def); (c) `rexB_rot_of_le/lt`, `lt_iff_of_blocks` live in
   namespace `SM.Link.Smoothing`; `firstReturn_no_between`, `cycNext_unique_on` in `SM.Link`;
   (d) `sameCycle_firstReturn_apply` needs its arguments explicit (unifying `↑?m` against `origVisit C v` fails).
4. Depends on (black boxes used): `m3_exists_lift`, `m3_kind_ne_mid`, `m3_crossingParam`,
   `m3_orig_injOn_crossing`/`m3_origCrossing_*` (through the skeleton's `origVisit_injective`, `origVisit_keep`),
   `m2_generic` (through `reducedDiagram`).  Once U-M3 and U-M2 close, `recordIso`/`m6_recordIso` are
   standard-axiom.
