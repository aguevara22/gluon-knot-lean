# W3_U5 — unit U5 (`typeIII_site`, ng:front-III, row 79) report

2026-09-14, prover for unit U5 (PLAN_FINAL.md §4 "L-geo", §5 "U5 geo III").  File:
`work/drafts/frontrows/W3_U5.lean` = `Skeleton_W2.lean` + ONE inserted block + ONE leaf body.
`diff Skeleton_W2.lean W3_U5.lean` = `11092a11093,13042` (the block, 1,950 lines, 184 declarations) and
`11101c13051,13065` (the leaf's `:= sorry` → `:= by` + 14 lines); the only removed line is the `sorry` line of
`typeIII_site`, whose statement text is kept verbatim.  No definition, structure, statement, name or docstring
touched; the other units' leaves untouched.

* `grep -c sorry`: 5 (Skeleton_W2.lean) → 4 (W3_U5.lean); the 4 left are `typeII_move`, `typeI_move`,
  `crossedCusp_move` (U6) and `represent` (U8R).
* Compile `cd work/lean && lake env lean ../drafts/frontrows/W3_U5.lean`: **0 errors** (55.6 s wall, log
  `/tmp/u5w/final.log`); warnings: exactly 4 `declaration uses sorry` (L13073, L13081, L13090 = U6's leaves,
  L16535 = `represent`) plus the 4 pre-existing linter warnings of the U8R block (L15415, L15436, L16101, L16220 =
  Skeleton_W2.lean L13451, L13472, L14137, L14256, byte-identical lines, not U5 code).  The U5 block itself
  compiles with zero warnings (checked as the standalone module `/tmp/u5w/B5.lean`).
* `#print axioms` (probe copy `/tmp/u5w/ax/W3_U5_ax.lean`, log `/tmp/u5w/ax.log`):
  `SM.FrontRows.typeIII_site` and `SM.FrontRows.U5.Pair.site_of`: `[propext, Classical.choice, Quot.sound]`;
  `SM.FrontRows.P_typeIII` and the row theorem **`SM.ng_front_III`: `[propext, Classical.choice, Quot.sound,
  SM.lp_lm]`** — no `sorryAx`: with U1's `typeIII_counts` already in place, **row 79 is closed** (the first row
  to accept, PLAN_FINAL §5).
* Nothing under `work/lean` was touched.  Scratch: `/tmp/u5w/` (`B1.lean` … `B5.lean` = the block as a module
  importing a compiled copy of the first 11,091 lines, `/tmp/u5/Prefix.olean`; `compile.sh`).

## 1. Leaves

| leaf | status | route |
|---|---|---|
| `typeIII_site` | **proved** | `U5.site₁₂` / `U5.site₂₁` (the two directions of `IsTypeIII`), both instances of the general `U5.Pair.site_of` on the band disc `U5.band X.length m = polygon (U5.bandL …)` = `[x_k, x_{k+3}] × [−(m+2)−¼, −m+¼]` (`k = |X|`); `realize W = realizeAt .std …` by `realize_eq_realizeAt`, then `convert … using 3` to move the `W.letters = X ++ P ++ Y` equation into the `realizeAt` arguments. |

No leaf of U5 left; nothing found false.

## 2. The construction (namespace `SM.FrontRows.U5`, block at W3_U5.lean L11093-13041)

Sections and what they prove (line numbers in W3_U5.lean):

* **A. `bandL`, `band`** (L11101-11196): the four half-planes (`HalfPlane.xge (std.x k)`, `xle (std.x (k+3))`,
  `yge (−(m+2)−¼)`, `yle (−m+¼)`); `mem_band_iff`, `mem_interior_band_iff`, `isDisc_band`; the segment tests
  `segIn_band` (both ends in the closed band `[k,k+3]×[−(m+2),−m]`, not both on one vertical side),
  `segOut_band_above/below` (a segment strictly above/below the band); `std_mid : std.mid c = c + ½`,
  `pt_std_cut`.
* **B. `swp a p`** (L11197-11219): the position map of `σ a` (`posR_σ_eq`, `posL_σ_eq : (σ a).posR/posL p =
  some (swp a p)`), an involution (`swp_swp`, `swp_inj`), preserving the active window `[m, m+2]` when
  `a ∈ {m, m+1}` (`swp_mem`) and the identity off it (`swp_of_not`).
* **C. `Blk V k m a`** (L11220-11433): the single-word block hypothesis — `k+3 ≤ |V|`, `1 ≤ m`,
  `letterAt V (k+i) = σ (a i)` and `a i ∈ {m, m+1}` for `i < 3`, `m+2 ≤ (cut V k).length`.  `bit_swp` (the
  bit of a strand is carried across a `σ` column: `StepDecomp.posR_some`), `step_right`/`step_left` (one step of
  `next` through a `σ` column, with the transported bit), `Blk.cutLen`, `Blk.bit_spec` (spectator bits constant
  across the block), `Blk.cusp_ext` (no cusp slot in the block).  Positions: `pos a p i` (the position after `i`
  columns, `pos_succ`), `Blk.pos_mem`, `Blk.pos_inj`, `Blk.bit_pos` (bit transport along the strand),
  `Blk.isSlot_pos`, `Blk.iterate_right`/`iterate_left` (the three-step passage of an active strand, both
  directions).
* **D. Classification** (L11435-11675): `segIn_band_nat`, `segOut_band_nat`, `mem_interior_band_nat` (the
  band tests on grid points), `colOf_pair`, `colOf_prev_of_true/false` (the column of the piece before a cut
  slot), `Blk.pieceOut_ext` (exterior columns: U4 `pieceOut_of_extCol`), `Blk.pieceIn_right/left`,
  `Blk.pieceOut_spec_right/left`, `Blk.classify`, `Blk.pt_mem_interior_iff` (the open band contains exactly the
  six interior active vertices `(k+1|k+2, m..m+2)`), `Blk.exits` (U4 `exitsMv_of_ext` + `exists_ext_of_no_r`),
  `Blk.exists_out`, **`Blk.clean : Clean (band k m) (realizeAt .std hV hne).diagram`** (U4 `clean_mv`).
* **E. Chains** (L11676-11771): `Blk.cidx`, **`Blk.chain j hj : Chain V`** (strand `j` enters at position
  `m+j`; rightward from `(k, m+j)` if its bit is `true`, else leftward from `(k+3, pos a (m+j) 3)`),
  `chain_n = 3`, `chain_u₀`, `chain_slot` (the `t`-th slot is `(k + cidx b t, pos a (m+j) (cidx b t))`),
  **`Blk.chain_isChain`** (U4 `IsChain`: pieces inside, interior vertices in the open band, `out_prev` via
  `colOf_prev_of_*`, `out_stop` via `pieceOut_ext`).
* **F. Crossings** (L11772-11827): **`Blk.xcol i hi := crossingOf .std hV hne _ (hB.letter i hi)`**, `xcol_ne`
  (`colOfCrossing_crossingOf`), `crossing_cases` (`eq_crossingOf` with the dependence on the crossing forgotten
  through an `∃`), **`Blk.crossingPoint_mem_interior_iff`** (the crossings in the open band are exactly the three
  `xcol i`; `crossingPoint_crossingOf`, `crossingOf_congr_idx`).
* **G. Active slots and the arc cover** (L11830-12082): `Active V k m u`, `pos_surj` (every active position at
  every cut is `pos a (m+j) i` for a unique `j`), `Blk.active_or_out`, `active_of_pieceIn`, `pieceIn_of_active`,
  `active_mem_chain`, `chain_slot_ne` (slots of different chains differ: `pos_inj`), `pt_mem_band`,
  `prev_of_true_σ`/`prev_of_false_σ`, `Blk.touch` (no touching from outside), `Blk.chains`, **`Blk.arcCover`**
  (U4 `arcCover_of`), `arcsOf_chains` (= the set literal `{a, b, c}`).
* **H. Visits** (L12083-12309): `half`, `visitPt_eq` (a visit's traversal point in the `travMv` vocabulary:
  U4 `pt_ext'`), `travMv_congr`, `travMv_inj`, `crossingParam_xcol` (= ½, `crossingParam_eq_half`),
  `visitPt_xcol`, `mkVisit`, **`Blk.overOn_xcol`/`underOn_xcol`** (`overStrand_crossingOf`,
  `underStrand_crossingOf`, `IsChain.mem_of_slot`), **`Blk.beforeOn_xcol_iff`** (`BeforeOn` of two block
  crossings along a chain ↔ the slot indices compare; `IsChain.inner_iff`, `before_iff`, `iterate_injOn`),
  `σSlotA_val`/`σSlotB_val`, **`Blk.σSlotA_eq_chain`/`σSlotB_eq_chain`** (the descending/ascending strand of
  column `k+i` is the chain slot `if b_j then i else 2−i` of the strand `j` at position `a i` / `a i + 1`),
  `Blk.xcol_slots` (the hypotheses of `beforeOn_xcol_iff` from these identifications).
* **I. Two words: `Pair V V' k m a a'`** (L12314-12695): `Blk` for both, equal lengths, equal letters off the
  block, equal cuts at the exterior cuts (`k' ≤ k ∨ k+3 ≤ k'`), and `pos3 : pos a p 3 = pos a' p 3` on the active
  window (the same strand permutation).  `Pair.symm`; `isSlot_iff` (U4 `isSlot_congr`), **`Pair.ψ :=
  sameSlotEquiv`** (identity on pairs), `pt_eq`/`pt₀_ψ` (U4 `pt_congr`), `Out V k m u := pt₀ V u ∉ interior
  (band k m)`, `out_ψ`, `bit_agree_ext`, `bit_agree` (bits agree except at the six interior active slots),
  `posR_agree`/`posL_agree`, **`nextPair_agree`** (`Out u → Out (next u) → nextPair V u.1 = nextPair V' u.1`, via
  U4 `nextPair_congr`), `ψ_next` (U4 `sameSlotEquiv_next`), **`entry_of`** (an outside vertex whose successor is
  inside is `(k, p)` rightward or `(k+3, q)` leftward at an active position), `passage_right/left`, `φ` (the
  induced bijection of the outside vertices, `Equiv.subtypeEquiv`), **`conj_firstReturn`**
  (`firstReturn_apply_of_mem` for a step outside, `firstReturn_apply_of_not_mem₂` for the three-step passage; the
  exit slots agree by `pos3`, leftward via `pos_surj`), `orbitEquiv` (U2 `cycleEquiv`), **`Pair.e : Fin (numComp
  hV) ≃ Fin (numComp hV')`**, **`Pair.he`** (U2 `cycleEquiv_mk`, `slotComp_eq_equivFin`), **`Pair.matchData :
  MatchData (bandL k m) hV hV' (pt₀ V) (pt₀ V') ψ`**, **`Pair.sigmaCorr`/`sigmaCorr'`** (outer `σ` columns are
  exterior — a block `σ` slot is a chain slot, hence `PieceIn`).
* **J. The site** (L12697-12925): `tj V k m j i` (the chain index of column `i` on strand `j`),
  `Blk.chain_u₀_ne`, `Blk.over_chain`/`under_chain`, **`Blk.before_chain_iff`**, `Blk.xcol_three_iff`,
  `Pair.chain_end_pair/chain_end_pt` (entry and exit vertices of the strands agree), `Pair.tj_eq`,
  **`Pair.moveMatch`** (U4 `MatchData.moveMatch` with `K = K' = fun _ => True`, `data = realizeAt_data'`),
  `rev_aux`, **`Pair.site_of`** — the full `RIIIData (band k m) (realizeAt .std hV hne).diagram (realizeAt .std
  hV' hne').diagram` from the columns `iAB iAC iBC` (and primed) of the three crossings, their position tables
  (`pos a (m+0) iAB = a iAB ∧ pos a (m+1) iAB = a iAB + 1` etc.) and the six order reversals `hrevA/B/C`.
* **K. The patterns** (L12927-13040): `a₁ m = (m+1, m, m+1)`, `a₂ m = (m, m+1, m)`, `P₁ m`, `P₂ m`, `blk₁`,
  `blk₂` (U3 `letterAt_block`, `σ_facts`), `shiftIdx_eq_self` (exterior indices only), `sameEffect₁₂`
  (`sameEffect_of_replace` + `run_typeIII_aux` + `run_typeIII_of_split`), `pos3₁₂`, **`pair₁₂`**
  (`letterAt_ext`, `cut_ext`), the tables `tbl₁`, `tbl₂`, **`site₁₂`** (columns `2 1 0 / 0 1 2`: in
  `σ_{m+1}σ_mσ_{m+1}` the crossing `b/c` is at column `k`, `a/c` at `k+1`, `a/b` at `k+2`; in `σ_mσ_{m+1}σ_m`
  the reverse) and **`site₂₁`** (`(pair₁₂ …).symm.site_of` with the columns exchanged).

Reading of the printed proof (sm-3:1995-2003): the strands are named by their entry position `m, m+1, m+2`
(`a` = top = position `m`, over at both its crossings — `σSlotA` is always the descending pass, so the height order
is independent of the orientation bits); "each physical pair crosses on both sides with the same over/under bit"
is `top_ab/top_ac/mid_bc` on both sides through `σSlotA_eq_chain`; "transported arrows" is `MoveMatch` with the
identity slot bijection off the block; the visit orders reverse because the crossing columns are read in the
opposite order (`hrev*`, checked by `omega` on the column indices).

## 3. API consumed

U4 (§6 of MERGE2_REPORT): `HalfPlane.xge/xle/yge/yle` + `f_*`/`b_*`, `polygon`, `mem_polygon_iff`,
`mem_interior_polygon_iff`, `isDisc_polygon`, `SegIn`/`SegOut`, `segOut_of_lt`, `SegOut.left_notMem_interior`,
`right_notMem_interior`, `not_pieceIn_of_pieceOut`, `PieceIn/PieceOut`, `pieceOut_of_extCol`, `Unch`,
`exitsMv_of_ext`, `exists_ext_of_no_r`, `clean_mv`, `realizeAt_data'`, `realizeAt_diagram_eq` (rfl, used
implicitly), `shadowMv`, `travMv`, `slotPtMv_travMv`, `strandMv`, `pt_ext'`, `Chain`, `Chain.slot/slot_succ/
toArc/toArc_ne/eval_startPt/eval_stopPt/IsChain`, `IsChain.n_lt_period/inner_iff/mem_of_slot/before_iff`,
`arcsOf`, `arcCover_of`, `MatchData`, `SigmaCorr`, `MatchData.moveMatch`, `nextPair_congr`, `pt_congr`,
`isSlot_congr`, `sameSlotEquiv`, `sameSlotEquiv_next`.
U2: `colOf_mk`, `nextPerm_pow_apply`, `slotComp_eq_equivFin`, `cycleEquiv`, `cycleEquiv_mk`.  U3:
`letterAt_block`.  Library: `IsSlot`, `isSlot_cut`, `cutSlot_pos`, `nextPair_right/left(_none)`,
`prevPair_right/left(_none)`, `nextPair_cusp_l/r`, `letterAt_of_cusp`, `next_val`, `prev_val`, `bit_eq`,
`decomp`, `StepDecomp.posR_some/posL_some`, `σ_facts`, `σSlotA/σSlotB`, `crossingOf`, `crossingOf_val`,
`overStrand_crossingOf`, `underStrand_crossingOf`, `crossingParam_eq_half`, `crossingPoint_crossingOf`,
`colOfCrossing_crossingOf`, `eq_crossingOf`, `crossingOf_congr_idx`, `slot_mem_crossingOf`,
`slotOf_strandOfSlot`, `iterate_injOn`, `exists_iterate_of_sameCycle`, `Orbit`, `orbitOf`, `pt_injective`,
`pt_cut`, `pt_cusp`, `generic`, `realize_eq_realizeAt`, `posR_σ`, `posL_σ`, `letterAt_ext`, `cut_ext`,
`shiftIdx`, `ExtCol/ExtCut`, `sameEffect_of_replace`, `run_typeIII_aux`, `run_typeIII_of_split`,
`firstReturn_apply_of_mem`, `firstReturn_apply_of_not_mem₂`, the `RIIIData` fields.

## 4. Pitfalls met (for U6 and the merger)

1. **Auto-included section variables.**  Under `include hV`, every lemma of the section takes `hV` explicitly
   whether it uses it or not; unused ones raise linter warnings and shift argument positions.  Every lemma that does
   not use a variable carries `omit … in` (the block compiles with zero warnings).  Dot-notation calls therefore
   read `hB.lemma hV …` (hV first, then the `Blk` argument via dot notation) and `hP.lemma hV hV' …`.
2. **`shadowMv` vs `(realizeAt …).diagram.Γ`** (U4 gotcha 1, confirmed): `rw [Chain.eval_startPt]` fails on the
   `RIIIData` field goals because `Arc.startPt`'s implicit shadow is `(realizeAt …).diagram.Γ`; the fields are
   closed with explicit-argument `have`s and `exact`/`Iff.trans` (defeq).  Same for `cover` (`rw … at h`, then
   `exact h`), `inner_iff`, `OverOn`, `BeforeOn`.
3. **Tactic blocks inside `simp only [...]` arguments** are elaborated before any unification with the goal, so
   `hB.pos_ne_zero ⟨by omega, by omega⟩ 3 le_rfl` fails (the implicit `p` is a metavariable); inside `rw [...]`
   the same term works.  Name the implicit (`(p := m + j)`).
4. **`firstReturn_apply_of_not_mem₂ f p _ h1 h2 h3`** with `_` for the point makes the unifier unfold
   `nextPerm` through `Subtype.val ?m` and time out; pass the point explicitly (`hP.φ hV hV' u`).
5. **`subst h` with `h : k' = k`** (two variables) eliminates `k`, not `k'`; write `have : k = k'` or `rw`.
6. **`bit W k 0 = bit W k 1`** (junk value): the bit-agreement lemma needs `p ≠ 0`; cusp slots are handled
   separately (their column is exterior, so all bits of that cut agree).
7. **`shiftIdx X P P' k = k`** only for exterior indices (`k ≤ |X| ∨ |X|+|P| ≤ k`), even when `|P| = |P'|`.
8. **`omega` fails on goals `True`** left by `simp only` (e.g. after `pos_zero` closes `m + 1 = m + 1`); add
   `and_true` to the simp set.
9. Destructuring a `Visit` (`obtain ⟨x, s, hs⟩ := v`) produces terms whose re-elaboration fails
   (`Crossing` is a `def` wrapping a subtype); instead generalise the crossing and `subst` (`crossingParam_eq_of`),
   and build visits with `mkVisit`.
10. `Set.mem_setOf_eq` is deprecated in this Mathlib (`Set.mem_ofPred_eq`); `push_neg` is `push Not`.

## 5. Notes for the merger

* The block is delimited exactly as required: `/-! ### U5 infrastructure -/` … `namespace U5` … `end U5`, placed
  immediately before the `typeIII_site` docstring; it opens `SM.FrontRealize SM.FrontWord.Letter Equiv U4` and is a
  `noncomputable section`; `open Classical in` is used only on `Pair.φ`, `conj_firstReturn`, `orbitEquiv`,
  `orbitEquiv_orbitOf` (the `DecidablePred (Out …)` of `firstReturn`/`cycleEquiv`).
* `Pair.site_of` is general: any two closed words with three-`σ` blocks at the same columns, the same exterior
  and the same strand permutation give an `RIIIData` on the band, provided the crossing-column tables.  It is
  reusable if the type-III row is ever restated on a different pattern.
* Everything is stated for `Placement.std` (`realize` uses `.std`); `pt₀ V := fun u => pt .std V u.1`.
* Consumers (`P_typeIII`, `ng_front_III`) were not touched; their axioms are checked in section 0 above.
