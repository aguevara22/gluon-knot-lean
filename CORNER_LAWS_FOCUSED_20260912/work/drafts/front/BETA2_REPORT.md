# Lane β, unit β2 — the grid realization `realize : OWord → PLFront` (report)

Written 2026-09-14 by the β2 prover subagent. Design of record: `work/reports/front-block-design-FINAL-20260913.md`
(§2 G1, §4 `realize`, §5, §7 "realize + Generic + nonvertical + letter/singularity correspondence", §8 risk 3,
§9 FR-5/FR-6); β1 report `work/drafts/front/BETA1_REPORT.md` §5 (open items 1-3). Nothing was written under
`work/lean`; no axiom was declared.

## 1. Deliverables and status

| file (work/drafts/front/) | intended home | lines | `lake env lean` | `sorry` | `#print axioms` |
|---|---|---|---|---|---|
| `FrontRealizeSlots.lean` | `SM/FrontRealizeSlots.lean` | 1323 | 0 errors | none | standard |
| `FrontRealize.lean` | `SM/FrontRealize.lean` | 1252 | 0 errors | none | standard (`realize`, `realizeAt`, `generic`) |
| `FrontRealizeCorrespondence.lean` | `SM/FrontRealizeCorrespondence.lean` | 1044 | 0 errors | none | standard for every correspondence lemma; `SM.wordMoves` and its `s`-laws additionally reach the registered interface `SM.lp_lm` through `PLFront.defect`/`P`, exactly as `PLFront.defect` itself (β1 report §5 item 5) |
| `FrontRealizeStandard.lean` | `SM/FrontRealizeStandard.lean` | 636 | 0 errors | none | standard |
| `FrontRealizeBase.lean` | `SM/FrontRealizeBase.lean` | 599 | 0 errors | none | standard; `finiteWordStatement_wordMoves_of` reaches `SM.lp_lm` through `wordMoves` (as above); **nothing cites `SM.ng_finite_word`** |
| `FrontRealizeDeform.lean` | `SM/FrontRealizeDeform.lean` | 240 | 0 errors | none | standard for `deformData`, `planarIsotopic_realizeAt`; `P_realizeAt_eq`, `defect_realizeAt_eq` reach `SM.lp_lm` through `P` |
| `FrontRealizeGeometry.lean` (geometry lane, a fork of this agent) | `SM/FrontRealizeGeometry.lean` | 1646 | 0 errors (re-checked here) | none | standard (`isDisc_rect`, `clean_blockRect`, `BlockSetup.outsideMatch`, `crossingPoint_mem_interior_iff`, `next_ext`) |

Import chain: `FrontRealizeSlots` imports `Mathlib.Data.List.GetD`, `SM.FrontPL`, `SM.FrontWords`;
`FrontRealize` imports `SM.FrontRealizeSlots`; `FrontRealizeCorrespondence` imports `SM.FrontRealize`;
`FrontRealizeStandard`, `FrontRealizeGeometry` import `SM.FrontRealizeCorrespondence`; `FrontRealizeDeform`
imports `SM.FrontRealizeCorrespondence` and the accepted `SM.PolynomialBlock` (for `P_planar`);
`FrontRealizeBase` imports `SM.FrontRealizeStandard` and the library's `SM.FrontInterfaces` (the statement
unit, for `OWord.IsStandardCircleBase`). The seven files total 6,740 lines (FINAL §7 estimate 2,500-3,500 with
tail 5k for realize + Generic + correspondence, which is the 3,616 of the first three files; the rest is the
base bridge, the planarity fact and the shared geometry that FINAL §8 risk 3 and the statement unit assigned to
this unit). A joint import of all seven with the library's `SM.FrontSmooth`, `FrontRecordBridge`,
`FrontGeomModel`, `FrontInterfaces` elaborates without a name clash.

**How the check was run.** `lake env lean` refuses `-o` for files outside `work/lean`, and a module named
`SM.X` is looked up only in the first search-path root that has an `SM/` directory, so a draft cannot be
imported as `SM.FrontRealizeSlots` before it is ported. The files were therefore checked with
`/tmp/fb/check.sh <file> [--olean]`: it copies the file to `/tmp/fbroot/FrontDraft/`, rewrites only the
lines `import SM.FrontRealize…` to `import FrontDraft.FrontRealize…`, and runs
`cd work/lean && lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/fb lean --root=/tmp/fbroot [-o …] <copy>'`
(Lean v4.34.0-rc2, the project's Mathlib pin). Nothing else differs from the files here; after the port to
`work/lean/SM/` the `import SM.…` lines are the right ones and `lake build` needs no change.

## 2. The construction (conventions — the realization is a proof device, FR-5)

A closed word `W = ℓ₀ … ℓ_{n−1}` (`OWord`, β1) is realized on a grid, letter `ℓ_k` in COLUMN `k`, the cut before
it on the CUT LINE `k`. A *placement* `pl : Placement` (strictly increasing column boundaries `pl.x k`;
`Placement.std` is `pl.x k = k`) fixes the x-coordinates; heights are fixed:

* the strand at position `p` (1-based, top to bottom) of cut `k` passes the cut line at `(pl.x k, −p)`;
* the cusp vertex of a cusp letter `ℓ_k` with index `m` sits in the middle of its column at
  `(pl.x k + w_k/2, −(m + 1/2))`, between the heights of the two positions `m`, `m+1` its arms join;
* a strand crossing a column is one straight edge from its left-cut point to its right-cut point (horizontal
  above the letter, sloped by the letter's strand-count change below it — `+2` for `l`, `−2` for `r` — and the
  two strands of `σ_m` exchange heights `m ↔ m+1`, crossing once at the centre `(mid_k, −(m+1/2))`);
* the two arms of a cusp are the two edges from the cusp vertex to `(pl.x (k+1), −m)`, `(pl.x (k+1), −(m+1))`
  (left cusp) or from `(pl.x k, −m)`, `(pl.x k, −(m+1))` to the vertex (right cusp).

The SLOTS (vertices) are the pairs `(k, p)` (position `p ≥ 1` of cut `k`) and `(k, 0)` (the cusp vertex of
column `k`). The oriented traversal is the permutation `next` of the slot set (`FrontRealizeSlots` §3): a
rightward strand at `(k, p)` enters column `k` and reappears at `(k+1, posR p)` unless `r_m` consumes it (then
`→ (k, 0)`); a leftward strand enters column `k−1` (`posL`; `l_m` consumes it, `→ (k−1, 0)`); a left-cusp vertex
sends the traversal out along its rightward arm (position `m` iff `d`), a right-cusp vertex along its leftward
arm. The direction bits are the cut bits of β1: `bit W k p := (cut W k).getD (p−1) false` with
`cut W k := Word.run (W.take k) []`.

Components are the cycles of `next` (`Equiv.Perm.SameCycle`); the vertex tuple of a component is its cycle
in traversal order from a chosen representative, of length `Function.minimalPeriod next rep ≥ 3` (a slot is
never its own successor, and no two slots swap: the x-direction is kept along cut slots and reversed exactly at
cusp vertices, `xsign_next_iff`). Every edge is nonvertical, and the shadow is `Generic` because two pieces of one
column meet only as the two arms of a cusp (at the vertex) or the two strands of a `σ` letter (once, transversally,
at the centre), and pieces of different columns meet only at a common cut slot (`common_point`).

Two conventions to record for the review:
* **the empty word.** `[]` is closed (β1), and `realize` must be total on `OWord`, but a shadow has `c ≥ 1`; `realize
  ⟨[], _⟩ := realize (l₁ r₁)` (the standard circle, `stdCircleWord`). Every correspondence lemma is stated for
  `W.letters ≠ []` (`realize_eq_realizeAt`), and `realize_nil_sCount : sCount = 2`, `realize_nil_isStandardCircles`
  give the empty case. The empty word is isolated under every move (`Pres.source_ne_nil`,
  `IsZigzagDeletion.ne_nil`, …; §4), so this does not affect `wordMoves`.
* **over = smaller slope** is not a convention of ours: at `σ_m` the strand descending from position `m` to `m+1`
  has slope `−1/w_k < 1/w_k` and is the over strand (`overStrand_crossingOf`), the printed rule.

## 3. Declarations

### 3.1 `FrontRealizeSlots.lean` — namespace `SM.FrontRealize` (position maps in `SM.FrontWord.Letter`)

| declaration | what |
|---|---|
| `Letter.posR`, `Letter.posL` (+ `posR_l`, `posR_r`, `posR_σ`, `posL_*`, `posR_eq_none_iff`, `posL_eq_none_iff`) | position of a strand after/before a letter (`none` = consumed by `r`/created by `l`) |
| `cut`, `letterAt`, `bit`, `cutLen`, `cut_zero`, `run_take`, `cut_length`, `cut_eq_nil_of_le`, `letterAt_eq`, `step_cut`, `length_run_le`, `cutLen_le` | the cuts of a closed word; `(letterAt W k).step (cut W k) = some (cut W (k+1))` |
| `StepDecomp` (`A w w' R`), `stepDecomp_of`, `.length_add`, `.getD_above`, `.getD_below`, `.w_l/w_r/w_σ`, `.bits_l/bits_r/bits_σ`, `.posR_some`, `.posL_some` | a typed step decomposed; transport of bits and positions across a column (the "index shift" facts) |
| `IsSlot`, `Slot` (abbrev subtype of `ℕ × ℕ`), `isSlot_bound`, `Finite`/`Fintype` instances | the slots |
| `nextPair`, `prevPair` (+ `nextPair_cusp_l/r`, `nextPair_right/_none`, `nextPair_left/_none`, `prevPair_*`), `bit_succ`, `bit_eq` | the successor/predecessor on pairs, by cases |
| `cutSlot_pos`, `decomp`, `letterAt_zero` (first letter is `l 1 d`), `isSlot_nextPair`, `isSlot_prevPair`, `prevPair_nextPair`, `nextPair_prevPair`, `next`, `prev`, `nextPerm : Equiv.Perm (Slot W)`, `next_injective`, `next_ne` | `next` is a permutation of the slots |
| `next_cases` | the six shapes of a step (pass right / enter `r` / pass left / enter `l` / leave `l` / leave `r`), with all bit and index facts |
| `xsign`, `xsign_cut`, `xsign_cusp_l/r`, `letterAt_of_cusp`, `xcoord2`, `xsign_next_iff`, `xsign_next_of_cut`, `xsign_next_of_cusp`, `next_cusp_cut`, `xcoord2_next`, `next_next_ne` | the x-direction bit of a slot; kept at cut slots, flipped at cusps; no 2-cycles |
| `period`, `period_pos`, `iterate_period`, `iterate_mod_period`, `period_next`, `three_le_period`, `iterate_injOn`, `Orbit`, `orbitOf`, `sameCycle_of_iterate`, `exists_iterate_of_sameCycle`, `numComp`, `rep`, `exists_rep_iterate`, `Idx`, `toSlot`, `toSlot_bijective`, `idxEquiv`, `toSlot_succ`, `toSlot_pred`, `toSlot_fst_eq_iff` | cycles → components; strand indices `Σ i, ZMod (period (rep i))` ≃ slots, with `toSlot ⟨i, j+1⟩ = next (toSlot ⟨i, j⟩)` |

### 3.2 `FrontRealize.lean` — namespace `SM.FrontRealize`, `SM.realize`

| declaration | what |
|---|---|
| `Placement` (`x`, `strictMono`), `.std`, `.w`, `.w_pos`, `.mid`, `.A` (the affine map of the unit column onto column `k`), `.A_injective`, `.A_fst_mem`, `.A_fst_eq_x`, `.A_fst_eq_mid` | column boundaries and the unit-column coordinates |
| `pt`, `pt_cut`, `pt_cusp`, `nat_ne_add_half`, `neg_nat_ne`, `pt_injective`, `pt_inj` | the plane point of a slot; distinct slots have distinct points |
| `Shape` (`pass p q`, `armL m j`, `armR m j`), `.left`, `.right`, `.par` (parametrization), `.Admissible ℓ`, `.par_pass/armL/armR`, `.par_fst_injective`, `.par_injective`, `.par_fst_eq_zero/one`, `.posR_order`, `.posR_inj`, `.pass_armL_absurd`, `.pass_armR_absurd`, `.meet`, `.vec`, `.vec_pass` | the three normalized edge shapes; `Shape.meet`: two distinct admissible pieces of one column meet only as the `σ` pair at the centre (`t = t' = 1/2`) or as the two arms at the cusp vertex; `posR_order`: positions keep their order across a column except for the two strands of `σ` |
| `colOf`, `shapeOf`, `piece_spec`, `ends_eq`, `slot_eq_of_piece_eq` | the piece of a slot: its column, shape, and the two ends (`pt u`, `pt (next u)`) in the order of `xsign`; the piece determines the slot |
| `isSlot_zero`, `nonempty_orbit`, `shadowOf : Shadow`, `slotOf`, `slotOf_injective/surjective`, `slotOf_succ/pred`, `tail_eq`, `head_eq`, `dir_eq`, `dir_pred_eq`, `A_affine`, `piecePt`, `edgePoint_eq`, `mem_seg_iff`, `mem_interior_iff`, `adjacent_iff`, `incidentTail_of` | the shadow; every edge segment is `{A (S.par τ) | τ ∈ [0,1]}`; adjacency of strands = adjacency of slots along `next` |
| `pt_eq_piecePt`, `pt_next_eq_piecePt`, `endpoint_mem`, `common_point_lt`, `common_point`, `dir_slot_eq`, `dir_slot_fst_ne_zero`, `dir_slot_fst_pos_iff`, `cusp_arms`, `regular`, `tail_off`, `transverse`, `interior_meet`, `no_triple`, `generic : (shadowOf …).Generic`, `nonvertical` | the genericity proof: `common_point` classifies every common point of two pieces (same piece / common slot at both ends / the `σ` crossing) |
| `realizeAt pl hW hne : PLFront`, `stdCircleWord`, `SM.realize : OWord → PLFront`, `realize_eq_realizeAt`, `realize_nil` | FINAL §4 `realize` (standard placement; `realizeAt` for the move rows) |

### 3.3 `FrontRealizeCorrespondence.lean` — namespace `SM.FrontRealize`, top-level `SM.*`

| declaration | what |
|---|---|
| `strandOfSlot`, `slotOf_strandOfSlot`, `strandOfSlot_slotOf`, `strandEquiv` | strands ≃ slots |
| `xdir_eq : F.xdir s = xsign (slotOf s)`, `xdir_cut : F.xdir (strand at (k,p)) = bit W k p` | **the xdir bits are the cut bits** |
| `slotOf_prev`, `eIn_eq`, `eOut_eq`, `bit_eq_getElem`, `isCusp_iff`, `arms_l`, `arms_r`, `isLeftCusp_iff`, `isRightCusp_iff`, `isDownCusp_iff` | cusps = cusp vertices; left = `l` letters, right = `r` letters; **down ⇔ `Letter.downBit … = 1`** (β1's letter-tracing rule, checked geometrically) |
| `σ_facts`, `isSlot_cut`, `σSlotA/B` (+ `_spec`, `σSlotA_ne_σSlotB`, `σ_meet`), `colOf_next_ne_of_pass`, `not_adjacent_of_σ`, `crossingOf`, `crossing_char`, `σIdx`, `σIdx_letter`, `colOfCrossing`, `crossingOfIdx`, `crossingEquiv : F.Γ.Crossing ≃ σIdx`, `crossingPoint_crossingOf`, `slope_σSlotA`, `overStrand_crossingOf`, `sign_crossingOf`, `signBit_σ`, `sign_crossingOf_eq_signBit` | **crossings = `σ` letters**; the crossing of column `k` is `{strand of pass m (m+1), strand of pass (m+1) m}`, point `(mid_k, −(m+1/2))`, over = descending strand, sign `+1 ⇔ bit k m = bit k (m+1)` (= β1's `signBit`) |
| `cuspIdx`, `cuspSlotEquiv`, `cuspStrandEquiv`, `card_fin_filter`, `card_cuspIdx`, `card_σIdx`, `crossingCount_eq`, `cuspCount_eq`, `sCount_eq` | `F.crossingCount = W.crossingCount`, `F.cuspCount = W.cuspCount`, **`F.sCount = W.sCount`** |
| `downCountFrom_eq_sum`, `writheFrom_eq_sum`, `downCountFrom_nil_eq_sum`, `writheFrom_nil_eq_sum`, `downBit_eq_ite`, `signBit_eq_zero_of_cusp`, `downCount_eq`, `writhe_eq` | **`F.downCount = W.downCountFrom []`, `F.writhe = W.writheFrom []`** (β1's letter tracing unrolled as `Fin`-sums) |
| `SM.realize_sCount/crossingCount/cuspCount/downCount/writhe`, `realize_nil_sCount`, `realize_sCount_eq_ite` | the same on `SM.realize` (nonempty words) |
| `SM.wordMoves : Moves`, `SM.ng_finite_word_statement := FiniteWordStatement wordMoves`, `wordMoves_s/B/Base/Pres/Del/Skein` | FINAL §4 `wordMoves := wordMovesOf (sCount ∘ realize) (defect ∘ realize) (IsStandardCircles ∘ realize)` (β1 open item 2) |
| `Pres.source_ne_nil`, `Pres.two_le_of_target_nil`, `IsZigzagDeletion.ne_nil`, `wordMoves_pres_s`, `wordMoves_del_s`, `wordMoves_skein_s` | the three `s`-clauses of `Laws` for `wordMoves` (β1's `laws_s_of_syn` could not be used: `s [] = 2 ≠ 0`; the empty word is isolated) |

### 3.4 `FrontRealizeStandard.lean` — namespace `SM.FrontRealize`, top-level `SM.*`

| declaration | what |
|---|---|
| `circleWord d := [l 1 d, r 1]`, `circleWord_closed`, `circle_slots`, `circle_sameCycle`, `circle_numComp`, `circle_no_σ`, `circle_cusp_l/r`, `card_strand_slot`, `circle_isStandardCircles`, `stdCircleWord_isStandardCircles`, `SM.realize_circle_isStandardCircles`, `SM.realize_nil_isStandardCircles` | ng:circle's base: the standard circle "in either orientation" realizes to a union of standard circles |
| `no_σ_of_isEmpty`, `posR_lt_of_not_σ`, `next_cut_right`, `next_cusp_of_right`, `prev_cut_right`, `prev_cusp_of_left`, `run_right`, `run_left`, `run_order`, `first_hit_right`, `first_hit_left`, `downBit_r_iff`, `downBit_l_iff`, `down_iff_not_down`, `IsStandardCircles.card_down_eq_one`, **`IsStandardCircles.downCount_eq_c`**, `SM.realize_downCount_eq_c_of_isStandardCircles` | β1 open item 3, the planarity fact for row 81's `base_B`: with no `σ` letter the vertical order of the rightward arc leaving the left cusp and of the (backwards-traversed) leftward arc is preserved column by column (`posR_order`), so the arc leaving on the upper arm (`d = true`) arrives on the upper arm of the right cusp; exactly one cusp per component is traversed upper → lower |

### 3.5 `FrontRealizeBase.lean` — the syntactic base of `SM/FrontInterfaces.lean` (statement unit, R2)

The statement unit fixed the axiom's base ON WORDS: `Word.IsStandardCircleBase W := labelRun W 0 [] = some []`
(the left cusp at letter index `k` pushes two strands labelled `k`, a right cusp is typed only on two strands of
the same label, a crossing is never typed) and recorded for β2 the obligation
`(realize W).IsStandardCircles ↔ W.IsStandardCircleBase`. The forward direction is proved here (the one the
consumers of `SM.ng_finite_word` need: `base_B` for `wordMovesOf s B IsStandardCircleBase` with
`B = defect ∘ realize` reduces to a crossing-free realization with `D = c`).

| declaration | what |
|---|---|
| `lcut`, `lbl`, `labelRun_append`, `lrun_take`, `lstep_cut`, `no_σ_of_base`, `labelStep_eq_some_iff`, `lcut_decomp`, `lbl_above`, `lbl_below`, `lbl_l`, `lbl_r`, `lbl_posR` | the labelled cuts of a base word and the transport of labels across a column (the two arms of `l` at index `k` carry `k`; the two strands joined by `r` carry the same label; passing strands keep theirs) |
| `lab : Slot W → ℕ`, `lab_cut`, `lab_cusp_l`, `lab_cusp_r`, `lab_next`, `lab_iterate`, `lab_eq_of_sameCycle` | the label of a slot is constant along `next`, hence on every component |
| `next_cusp_of_left`, `hit_r`, `hit_l`, `exists_lcusp` | from a rightward (leftward) cut slot the first cusp along `next` is a right (left) cusp, reached through cut slots of one direction (the x-coordinate is monotone, so a cycle cannot avoid cusps); every component has a left cusp |
| `cycle_cusps` | the cycle of a left cusp `L` of a base word: rightward run to a right cusp `R`, leftward run back to `L` (same label), and `L`, `R` are its only cusps |
| **`isStandardCircles_of_base`**, `downCount_eq_c_of_base`, `SM.realize_isStandardCircles_of_base`, `SM.realize_downCount_eq_c_of_base` | `W.IsStandardCircleBase → (realizeAt pl hW hne).IsStandardCircles`, and `D = c` on the syntactic base |
| `Moves.Chain.mono_base`, **`SM.finiteWordStatement_wordMoves_of`** | a principal chain for a smaller base is one for a larger base; hence `FiniteWordStatement (wordMovesOf (sCount ∘ realize) (defect ∘ realize) OWord.IsStandardCircleBase) → FiniteWordStatement SM.wordMoves` — composed with the statement unit's `ng_finite_word_finiteWordStatement` this is `FiniteWordStatement SM.wordMoves` (not cited here: the axiom is under independent review) |

### 3.6 `FrontRealizeDeform.lean` — changing the placement is a generic deformation

| declaration | what |
|---|---|
| `Placement.lerp pl pl' t ht` (+ `lerp_x`, `lerp_w`, `lerp_mid`), `pt_lerp` | the convex combination of two placements is a placement for `t ∈ [0,1]`; the point of a slot interpolates |
| `vpath`, `vpath_zero`, `continuousOn_vpath`, `withVertices_vpath`, `generic_vpath`, `seg_withVertices_vpath`, `crossings_vpath`, `isCrossing_iff_σ`, `isCrossing_placement_free`, `overStrand_placement_free`, `Diagram.ext'`, `heq_of_subtype_fun` | the straight-line vertex path; every intermediate shadow is the realization with the interpolated placement, hence generic, with the same crossing pairs and the same over strands |
| **`deformData : DeformData (realizeAt pl …).diagram (realizeAt pl' …).diagram`**, `deform_realizeAt`, `planarIsotopic_realizeAt`, **`P_realizeAt_eq`**, `defect_realizeAt_eq`, `SM.P_realizeAt_eq_realize`, `SM.defect_realizeAt_eq_realize` | the accepted `Deform`/`PlanarIsotopic`, and `P`, `defect` are placement-free (via `P_planar`) |

## 4. What the move rows (77-82) can consume

* **Realizations.** `realizeAt pl W.closed h` for any placement; `SM.realize W = realizeAt .std …` for nonempty
  `W` (`realize_eq_realizeAt`). For two words `X ++ P ++ Y`, `X ++ P' ++ Y` realized so that the factor blocks
  occupy the same rectangle, use two placements agreeing on `k ≤ |X|` and with
  `pl.x (|X|+|P|+j) = pl'.x (|X|+|P'|+j)` (`PlAgree`, `plAgree_of` in the geometry module); the counts are
  placement-free (`sCount_eq`, `downCount_eq`, `writhe_eq` hold for every `pl`) and so are `P` and `defect`
  (`P_realizeAt_eq_realize`, `defect_realizeAt_eq_realize`: the straight-line homotopy of placements is a
  `Deform`, §3.6). So a row may realize one side non-standardly, build its `RIData`/`RIIData`/`RIIIData`/
  `OrientedSmoothingData` in the block rectangle, apply `P_reidemeister_*`/`P_skein`, and transport back.
* **Strands and slots.** `slotOf`, `strandOfSlot`, `strandEquiv`; the six-case `next_cases`; the concrete
  `nextPair_*`/`prevPair_*` equations for computing the cycle of a pattern; `piece_spec`, `colOf`, `shapeOf`.
* **Cusps and bits.** `isCusp_iff`, `isLeftCusp_iff`, `isRightCusp_iff`, `isDownCusp_iff`, `xdir_eq`, `xdir_cut`,
  `arms_l`, `arms_r`.
* **Crossings.** `crossingEquiv`, `crossingOf hk hℓ` for `letterAt W k = σ m`, `crossing_char` (every crossing is a
  `σ` letter), `crossingPoint_crossingOf`, `overStrand_crossingOf`, `sign_crossingOf` (`+1 ⇔ bit k m = bit k (m+1)`),
  `sign_crossingOf_eq_signBit`.
* **Counts.** `realize_sCount`, `realize_downCount`, `realize_writhe`; the `s`-laws `wordMoves_pres_s`,
  `wordMoves_del_s`, `wordMoves_skein_s` are done (the rows supply `pres_B`, `del_B`, `skein_B`, `base_B`).
* **Base.** `realize_circle_isStandardCircles`, `IsStandardCircles.downCount_eq_c`, and for the axiom's syntactic
  base `realize_isStandardCircles_of_base`, `realize_downCount_eq_c_of_base` (so `base_B` for
  `wordMovesOf s (defect ∘ realize) OWord.IsStandardCircleBase` reduces to `degAZ (P (realize W).diagram) ≤ c − 1`
  for a crossing-free realization with `c` components: the polynomial block's split-circle facts), and
  `finiteWordStatement_wordMoves_of` to move the axiom's chain onto the geometric `SM.wordMoves`.
* **Grid geometry for the disc-local moves**: §6 — `isDisc_blockRect`, `clean_blockRect` (under `ExitsBlock`),
  `crossingPoint_mem_interior_iff`, and `BlockSetup.outsideMatch`/`agreeOutside` for two words with nonempty
  factors of the same typing effect.

## 5. Corrections and observations recorded for the review (FR-5/FR-6)

* β1 §5 item 1 asked for `(realize W).sCount = W.sCountSyn` for all `W`; it holds for nonempty words, and the empty
  word has `s = 2` (the standard circle). `laws_s_of_syn` is therefore not applicable and the three `s`-clauses
  are proved directly (`wordMoves_*_s`), using that no move starts from `[]` and that only a type-I deletion can
  produce `[]` (then `|W| = 3`). `IsZigzagDeletion.ne_nil` shows the two-letter zigzag words are not typed from the
  empty cut.
* β1's letter-tracing rules for `D` and `w` are confirmed geometrically on the realization
  (`isDownCusp_iff`, `sign_crossingOf`); no change to β1 was needed.
* `Shape.posR_order` is the exact statement of "the index changes track the same physical positions":
  positions keep their order across a column except the two strands of the crossing letter.
* The `cut`/`bit` functions are total (`getD`); every lemma about them is under `W.Closed` (all prefixes typed).

## 6. The shared grid geometry (`FrontRealizeGeometry.lean`, FINAL §8 risk 3)

Written by a fork of this agent with the full β2 context; re-checked here (`lake env lean` 0 errors, no `sorry`,
`#print axioms` standard). Namespace `SM.FrontRealize`.

| group | declarations | what |
|---|---|---|
| rectangles | `rect a b H := Icc a b ×ˢ Icc (−H) H`, `mem_rect_iff`, `interior_rect`, `mem_interior_rect_iff`, `frontier_rect`, `mem_frontier_rect_iff`, **`isDisc_rect (a < b) (0 < H)`** | axis-parallel rectangles are discs; points with `|z| < H` are on the frontier iff on a vertical side |
| blocks and height | `blockRect pl a b H`, `isDisc_blockRect`, `hgt W := 2|W| + 3`, `pt_snd_bounds`, `piecePt_snd_bounds`, `abs_piecePt_snd_lt(')` | the block of columns `a..b−1`; the whole trace has heights in `(−hgt W, hgt W)` |
| inside/outside | `piecePt_fst_mem`, `piecePt_fst_eq_left/right`, `piecePt_fst_le_of_col_lt`, `piecePt_fst_ge_of_col_ge`, `piecePt_notMem_interior_of_ext`, `piecePt_mem_blockRect_of_ext/of_int`, `piecePt_mem_interior_blockRect_of_int`, `piecePt_mem_frontier_iff`, `piecePt_fst_eq_x`; `eval_eq_piecePt`, `travPt`, `strandPt`, `parOf`, `parOf_mem`, `eval_eq_piecePt_parOf`, `parOf_eq_end`, `eval_eq_lin` | a piece of an exterior column is outside the block except at a boundary cut slot; a piece of a block column is inside; traversal points as piece points, an end parameter is the tail point |
| Clean | `frontier_pt`, `frontier_injOn_blockRect`, `ExitsBlock pl hW hne a b`, `midpoint_notMem_blockRect`, **`clean_blockRect (a ≤ b) (hgt W ≤ H) (ExitsBlock …) : Clean (blockRect pl a b H) (realizeAt pl hW hne).diagram`** | the exit criterion: every component has a strand in an exterior column (the rows verify it on their patterns) |
| crossings | `crossingPoint_mem_interior_iff` | the `σ` at column `k` has its point in the open block iff `a ≤ k < b` |
| exterior slot correspondence for `X ++ P ++ Y` vs `X ++ P' ++ Y` | `shiftIdx`, `ExtCut`, `ExtCol`, `SameEffect` (+ `sameEffect_of_replace` from β1's `Closed.replace` hypothesis, `.symm`), `IsExtSlot`, `extPair`, `ExtSlot`, `shiftIdx_*`, `letterAt_ext`, `cut_ext`, `bit_ext`, `isSlot_ext`, `extSlot`, `extPair_inv`, `isExtSlot_extPair`, `PlAgree` (+ `plAgree_of`, `plAgree_symm`), `pt_ext`, `xsign_ext`, `colOf_ext`, **`next_ext`**, `isExtSlot_of_extCol` | with both factors nonempty: exterior slots correspond by the index shift, with the same points (under `PlAgree`), bits, columns, and `next` commutes on exterior pieces |
| the outside match | `BlockSetup` (X P Y P', `P, P' ≠ []`, `SameEffect`, closedness, `pl pl'`, `PlAgree`; `symm`), `U` (`U_eq`, `U_eq'`, `symm_U`), `OutPt`, `notMem_interior_iff_outPt`, `φfun`, `eval_φfun`, `φfun_symm`, `outEquiv`, `StrictOut`, `dir_φfun`, `prev_extSlot`, `dir_before_φfun`, `crossingOf_congr(_idx)`, `eq_crossingOf`, `crossingParam_eq_half`, `underStrand_crossingOf`, `visitPt_over/underVisit_crossingOf`, `extSlot_σSlotA/B`, `ψfunGen`, `outerEquiv`, `φfun_visitPt_over/under`, **`BlockSetup.outsideMatch : OutsideMatch B.U B.F.diagram B.F'.diagram`**, `agreeOutside` | the accepted `OutsideMatch` between the two realizations: outside points (exterior pieces and the tail points of boundary cut slots) correspond with equal points, directions (`l = 1`) and outer crossings with over/under occurrences |

Findings of the geometry lane, for the rows (also in the module docstring): (i) a deletion with an EMPTY factor
(`P' = []`: type I `l_m σ r_m ↦ ∅`, empty zigzag `l_m r_{m+1} ↦ ∅`) is not a literal exterior match of the two
standard realizations — the `Y` columns shift and no letter realizes a straight through-strand — so rows 77 and 80
should compare the pattern with a nonempty crossing-free factor (e.g. the curl with the empty zigzag, both
factors nonempty) and finish with `P`-invariance, or use a padded placement plus `Deform`; (ii) `MoveMatch`'s
component bijection is not built (it needs the hypothesis that the two blocks connect their boundary slots
identically — true for RI/RII/RIII, false for the smoothing — and an orbit-level argument); (iii) the arc tools
(`Arc`, `IsArc`, `ArcCover` of the block) were not started.

## 7. Open items

1. **The converse of the base bridge** `(realize W).IsStandardCircles → W.IsStandardCircleBase` (statement unit R2
   records the `↔`; the forward direction, the one the consumers of `SM.ng_finite_word` need, is proved). Sketch:
   define the geometric label of a slot as the column of the unique left cusp of its component and show by
   induction on the columns that the labelled run produces exactly these labels (at an `r` the two joined slots
   are `prev`/`next` of one cusp, hence one component, hence one label). ~300-400 lines.
2. **`MoveMatch` and arcs** for the disc-local moves (§6 (ii), (iii)); the `P' = []` deletions (§6 (i)).
3. `SM.Pres.source_ne_nil`, `SM.Pres.two_le_of_target_nil`, `SM.IsZigzagDeletion.ne_nil` live in `SM` (not
   `SM.FrontWord`) because they were proved here; the home module may move them next to the β1 patterns.
4. The empty-word convention (§2) should be cited in the docstring of `SM.ng_finite_word`'s consumers (the statement
   unit already notes "the empty word is (vacuously) typed … a chain from it is `base`").
5. `SM.wordMoves` keeps FINAL §4's geometric base; the axiom of `SM/FrontInterfaces.lean` is stated with the
   syntactic base, and `finiteWordStatement_wordMoves_of` bridges the two. If the reviewers prefer one `Moves`, the
   syntactic-base instance `wordMovesOf (sCount ∘ realize) (defect ∘ realize) OWord.IsStandardCircleBase` is the
   one the axiom delivers directly.
