# W2_SGD_REPORT — unit U103-D (prefix `sgd_`), leaf `sg_daughters_products` (wave 2, critical for row 103)

Prover subagent, 2026-09-15 18:22 UTC / 2:22pm ET.  File: `work/drafts/corner/W2_SGD.lean` (sha256
`0fc6100a…1b8b2d`), created by `cp Partial_Assembled.lean W2_SGD.lean` (frozen skeleton sha256 `85312954…081891`) and
changed in exactly two places — `diff Partial_Assembled.lean W2_SGD.lean` = `672a673,838` (pure insertion: the 166-line
`sgd_` helper block, placed in `section Singleton` immediately after U103-C's `sgc_` block and immediately before the
docstring of `sg_daughters_products`, the leaf that consumes it — rule (2)) and `691c857,868` (the ONLY removed line is
`  sorry`, the body of the leaf, replaced by 12 proof lines).  No definition, structure, theorem/lemma statement, name or
docstring of the frozen file was touched; no other unit's `sorry` and no §6 row theorem was touched.
`python3 tools/stmt_check.py W2_SGD.lean`: **49/49 frozen declaration statements byte-identical and unique: PASS**.

Check (mandated): `cd work/lean && lake env lean ../drafts/corner/W2_SGD.lean` — **0 errors**, exit 0, 18.9 s warm
(load ≈ 10.8 on 8 cores); **9 `declaration uses sorry`** warnings (10 before) = exactly the 5 still-open leaves
`s7_sliding_law_at` (4412), `s7_bigon_law_at` (5577), `s7_corner_product` (5736), `sft_same_sign` (7291), `sft_loop`
(7444) + the 4 §6 row theorems `cb_singleton` (7539), `corner_values` (7544), `thm_C_S7` (7549), `thm_C_soft` (7554);
the 14 other warnings are the pre-existing U_SFTA ones (PARTIAL_ASSEMBLY_REPORT §5; lines 5979-6891), none in this
unit's lines 673-868.  `grep -c sorry`: **12 before → 11 after** (10 → 9 sorry bodies; the 2 prose mentions, header
line 25 and §6 header, unchanged).

`#print axioms` (scratch copy of the full file + `#print axioms`, scratchpad `W2_SGD_axioms.lean`):
```
SM.sg_daughters_products      [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]
SM.sgd_daughters              [propext, Classical.choice, Quot.sound]
SM.sgd_blocksOwnedBy_eq       [propext, Classical.choice, Quot.sound, SM.lp_lm]
SM.sgd_carrierPoly_eq         [propext, Classical.choice, Quot.sound, SM.lp_lm]
SM.sgd_carrierCrossingCount_eq[propext, Classical.choice, Quot.sound, SM.lp_lm]
SM.cb_singleton_of_floor      [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]
SM.corner_values_of_floor     [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]
SM.corner_values_of_singleton [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]
```
No `sorryAx` anywhere in the leaf or its helpers.  `lit_homfly` / `lp_lm_uniqueness` enter only through cb:blocks'
`equals_Hplus` (`P_eq_homfly`, def:C's `homfly`), `lp_lm` through `SM.P` / `cb_products` — the policy list PLAN_FINAL §4
expects for the assembly.  **Consequence: `cb_singleton_of_floor` (row 103 conditional on thm:floor) and
`corner_values_of_floor` / `corner_values_of_singleton` (row 105) are now `sorryAx`-free** — the last open leaf of
row 103 was this one (U103-A, U103-E closed in wave 1).

## Proved
- `sg_daughters_products` (U103-D; the whole unit) — all four conjuncts: `Λ₁ ≠ Λ₂`, the owner `↔`,
  `H⁺_A = H⁺_{Λ₁} H⁺_{Λ₂}`, `m_A = m_{Λ₁} + m_{Λ₂} + 1`.

## Unproved
- nothing in this unit.  The leaf is TRUE as stated; no missing hypothesis, no counterexample.

## Helpers added (7, all `sgd_`, all PROVED; section `SgdDaughters`, `variable (hn) {P} (hP) {S} {c}`)

| helper | statement | route |
|---|---|---|
| `sgd_daughters hS A hc hS'` | `∃ Λ₁ Λ₂ : Component (insert c S), Λ₁ ≠ Λ₂ ∧ ∀ m, owner S m = A ↔ owner S' m = Λ₁ ∨ owner S' m = Λ₂` | PLAN §3.1 item 2.  `v := ⟨c, i⟩` (`crossing_visits_exist`), `c ∉ S` and both owners `= A` from `mem_carrierCrossings`; `smoothingSuccessor_insert_child_data hn hP S (independent_inheritsMarkOrder hS) v hv hown` gives `k L₁ L₂`, `hrot : (markList).rotate k = inr v :: (L₁ ++ inr (twin v) :: L₂)` and the two orbit descriptions `owner S' m = owner S' (inr v) ↔ m ∈ inr v :: BL`, `… (inr (twin v)) ↔ m ∈ inr (twin v) :: AL` (`BL/AL = L₂/L₁.filter (owner S · = q)`).  `Λ₁ := owner S' (inr v)`, `Λ₂ := owner S' (inr (twin v))`; `Λ₁ ≠ Λ₂` = `independent_selected_pair_owners_ne hS' v (mem_insert_self)`.  (→): `mem_markList` + `List.mem_rotate` put `m` in the rotated list; the four cases (`= inr v`, `∈ L₁`, `= inr (twin v)`, `∈ L₂`) land in the two children via `List.mem_filter` + `decide_eq_true_eq`.  (←): `owner_insert_eq_imp` (the refinement only splits) + the owners of the two visits. |
| `sgd_blocksOwnedBy_disjoint hS' hne` | `Disjoint (blocksOwnedBy S' Λ₁) (blocksOwnedBy S' Λ₂)` for `Λ₁ ≠ Λ₂` (any `S'`) | `Finset.disjoint_left` + `CB.blockOwner_eq_of_mem` twice |
| `sgd_pieceEmbedding_mem_blocksOwnedBy hcU hiso A hown hH'` | `H' ∈ bo S' Λ₁ ∪ bo S' Λ₂ → sgb_pieceEmbedding H' ∈ bo S A` | `sgb_pieceEmbedding_mem_blocksOwnedBy_iff` (U103-B) + `mem_blocksOwnedBy_iff` at `S'` + the owner `↔` (←) |
| `sgd_exists_preimage hS' hcU hiso A hown hH hHc` | `H ∈ bo S A`, `labels H ≠ {c}` → `∃ H' ∈ bo S' Λ₁ ∪ bo S' Λ₂, sgb_pieceEmbedding H' = H` | `sgb_mem_range_pieceEmbedding_iff` gives `H'`; a label `x` of `H'` (`CV.pieceLabels_nonempty`) is a label of `H` (`sgb_pieceLabels_pieceEmbedding`), so `owner S (inr (someVisit x)) = A`; `one_owner.2` at `S'` (cb:products) makes `blockOwner S' H' = crossingOwner S' x = owner S' (inr (someVisit x))`, which the owner `↔` (→) puts in `{Λ₁, Λ₂}`; `mem_blocksOwnedBy_iff_blockOwner` |
| `sgd_blocksOwnedBy_eq hS' hcU hiso A hc hown` | **the block redistribution**: `bo S A = insert (pieceOf S c _) ((bo S' Λ₁ ∪ bo S' Λ₂).map sgb_pieceEmbedding)` | `ext`; `sgb_pieceLabels_eq_singleton_iff`, `sgb_pieceOf_mem_blocksOwnedBy` (U103-B) and the two helpers above |
| `sgd_carrierPoly_eq hS hS' hcU hiso A hc hne hown` | `carrierPoly hS A = carrierPoly hS' Λ₁ * carrierPoly hS' Λ₂` (eq. cb:singleton-products) | `cb_products.product` at `S`, `S'`; the set equality; `sgb_prod_insert_map`; `sgc_blockPoly_eq_one_of_labels_eq_singleton` on `sgb_pieceLabels_pieceOf` (`P_{c} = 1`); `Finset.prod_union` with the disjointness; `Finset.prod_congr` with `sgc_blockPoly_eq_of_labels_eq hS hS' (subset_insert c S) _ H' (sgb_pieceLabels_pieceEmbedding …)` (U103-C) |
| `sgd_carrierCrossingCount_eq …` (same binder) | `m_A = m_{Λ₁} + m_{Λ₂} + 1` | `cb_products.count` at `S`, `S'`; the set equality; `sgb_sum_insert_map`; `Finset.card_singleton` on `sgb_pieceLabels_pieceOf`; `Finset.sum_union`; `simp only [sgb_pieceLabels_pieceEmbedding]`; `omega` |

Leaf body (12 lines): `sg_isolated_undominated` (U103-A) → `hcU`, `hint`; `sgb_not_interlaces_of_isolated` → the
U103-B-shaped `hiso'`; `hS' := greedy_independent hn hP hS hcU`; `sgd_daughters`; the count conjunct is
`sgd_carrierCrossingCount_eq`; the polynomial conjunct: `rw [← (cb_blocks_definition …).equals_Hplus _ |>.2]` three
times turns `cornerHomfly` into `carrierPoly` (cb:blocks "these polynomials equal the corresponding `H⁺_A`"), then
`sgd_carrierPoly_eq`.

Size: 166 helper lines + 12 body lines = 178 against the 650-line / 9 h estimate; ≈ 25 min of wall time.  The
accepted `smoothingSuccessor_insert_child_data` already carries the whole orbit-splitting content, and U103-B/C left
the block side as a bookkeeping exercise.  Compiled first time with 0 errors and 0 warnings on a scratch prefix
(lines 1-672 of the skeleton + the block + the leaf, 16 s), then the full file.

## Notes for the assembler / executor
- **Route vs PLAN §3.1 item 2**: the PLAN names `component_card_insert`, `owner_insert_iff_of_unaffected`,
  `componentCycle_insert_unaffected`, `smoothingSuccessor_insert_other` and the crossing partition via
  `interlaces_twin_different_slices`; NONE of these was needed.  The owner `↔` follows from the two orbit
  descriptions of `smoothingSuccessor_insert_child_data` alone (+ `mem_markList`), and `m_A = m₁ + m₂ + 1` is read
  off cb:products' `count` through the same block redistribution that gives the product — the crossing partition
  `cc S A = {c} ⊔ cc S' Λ₁ ⊔ cc S' Λ₂` is implied but never stated (available, if a later unit wants it, as
  `carrierCrossings_eq_biUnion` + `sgd_blocksOwnedBy_eq`).  Spectator carriers never enter (the statement speaks
  only of `A` and its daughters).
- `sgd_daughters` is hypothesis-light: it needs `hS` (for `independent_inheritsMarkOrder`), `hS'` (for
  `Λ₁ ≠ Λ₂` only) and `hc`; NOT `hiso` — every self-crossing of every carrier splits it into two daughters with the
  owner `↔`.  Reusable by thm:C-S7's one-newborn rows (U110-J/K, "the daughters of a singleton row are the carriers
  of the support enlarged by the singleton", sm-4:862-864) and by U112-D's "smooth `y` first" step.
- `sgd_blocksOwnedBy_eq` / `sgd_carrierPoly_eq` / `sgd_carrierCrossingCount_eq` take the U103-B-shaped hypotheses
  `hcU : c ∈ supportUnselected hn hP S`, `hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c` and the
  owner `↔` as an explicit `hown` (so they do not depend on how the daughters were produced).
- Lean notes: the `let q := …; let AL := …; let BL := …; (…) ∧ …` conclusion of `smoothingSuccessor_insert_child_data`
  destructs directly with `obtain ⟨-, -, -, h₁, h₂, -, -⟩ := hdata` (no `dsimp`/zeta step needed); the filter
  predicate is `decide (owner … = q)`, discharged by `rw [decide_eq_true_eq, hm, hvA]`.  `insert v.1 S` with
  `v := ⟨c, i⟩` written inline is syntactically `insert c S` after elaboration — no `show`/`change` was needed.
  `CB.crossingOwner hn hP S' x` unfolds to `owner hn hP S' (Sum.inr (CB.someVisit x))` by `exact` (plain def).
  The classical `DecidableEq (CV.Piece …)` instance of `insert`/`∪`/`Finset.map` in the statement of
  `sgd_blocksOwnedBy_eq` matched `sgb_prod_insert_map` / `Finset.prod_union` without any instance massaging.
- No linter warnings in the block (the `[NeZero n]` section variable is used by every helper through
  `Component`/`carrierCrossings`; no `omit` needed).
- Statement as given is true; no counterexample, no missing hypothesis, nothing believed false.  U110-G's GO/NO-GO on
  the RI/RII witnesses is that unit's report.
- Assembly: `python3 tools/partial_assemble.py --units …,W2_SGD` (the file is a clean copy of `Partial_Assembled.lean`
  with one insertion at the U103-C anchor and one leaf body; it should classify as CLEAN under the script's rules), then
  `stmt_check.py` and the compile.
