# PLAN_B — marked products block (mp:join, mp:lowest, mp:blocks, lem:homflyrows), Architect B (reuse-first)

Date 2026-09-14.  Fixed statements: `work/drafts/MarkedProducts_statement.lean` (sections A–E and the four
bundles are copied byte-identically into the skeleton; checked by `diff`).  Judge's notes:
`NOTES_FINAL.md` (clause maps, risks R1–R9, proof-lane sketch).  Skeleton of record:
`work/drafts/markedproducts/Skeleton_B.lean` — **compiles** (`cd work/lean && lake env lean
../drafts/markedproducts/Skeleton_B.lean`: no errors, 1501 lines, **34 `sorry`** declarations, all of them
chain lemmas listed in §4; the four row theorems `SM.join`, `SM.lowest`, `SM.blocks`, `SM.homflyrows` are
PROVED from the chain).  Axiom audit (`#print axioms` on a `/tmp` copy): the rows depend on
`propext, Classical.choice, Quot.sound, sorryAx` and the accepted interfaces `SM.lp_lm` (all four),
`SM.lit_homfly`, `SM.lp_lm_uniqueness` (`homflyrows`, through `homfly`/`P_eq_homfly`) — nothing else.

Reading guide: §1 route and the design decisions; §2 the chain row by row (exact Lean statements are in the
skeleton; here the lemma, what it consumes with file:line, the estimate); §3 what is already proved in the
skeleton; §4 unit split for parallel provers; §5 the `realizes` analysis (a structural finding: no clean-join
construction is needed); §6 risks and fallbacks; §7 reuse index.

## 1. Route (one paragraph per row) and the decisions that differ from the judge's sketch

**mp:join.**  `P_addFree` (SM/PolynomialBlock.lean:1036) is the template: a record-level `(N, b)` induction
`skein_induction_based` (:551) on ONE factor with the partner diagram and the join quantified inside the
predicate.  Two inductions: the inner `join_core_right_underFirst` fixes the partner `B` UNDER-first at a
*marked-first* based order and inducts on `A`; the outer `join_core` inducts on `B` with `A` arbitrary.
Decision B1: in the outer induction the inducted factor sits in the `inl` slot of `joinRecord`
(`joinRecord μB μA`), so only the `inl` versions of the two commutations (`joinRecord_switch_inl`,
`joinRecord_smooth_inl`) are ever needed; `joinRecord_comm` is used exactly once (the outer init) and once
more in the final assembly.  Decision B2: one common `join_step` (proved) does the algebra of the printed
step for an ABSTRACT second record `ρ₂` with a value `q : R` — both inductions call it; the marked-first
bookkeeping stays in the inductions.  Decision B3: the smoothing mark `Mark.smoothMark` is defined
uniformly (no four-case split): with `σ = swap x (τx)` the interval after the gap `g` lies after `σ g` on
the reconnected cycles (`s₁ (σ g) = s g`), so the new gap is `lastKeep s₁ (SmoothKeep x) (σ g)` — the last
retained occurrence at or before `σ g` — and the new circle is the `s₁`-cycle of `σ g` (`none`/emptied
circle handled by `lastKeep = none`); a crossing-free marked circle stays crossing-free (`Sum.inr`).  The
printed four cases (sm-3:1462-1472) are then just the case split of ONE permutation lemma,
`firstReturn_mul_swap_of_lastKeep_some/none` (the generalisation of the accepted
`firstReturn_mul_swap`, SM/Stack.lean:345, to an unretained swap point).  Decision B4: the join based order
`RBasing.join` is DATA (defined, `rank_inj` proved) with no hypotheses; marked-first is used only in
`rUnderFirst_join`.

**mp:lowest.**  Corollary of `SM.stack` with singleton blocks.  `blockRestrict D id _ i = D.knotRestrict i`
(`blockRestrict_id`, proved via `restrict_congr`).  The weight `a^{2Λ}[z^{1−c}]P_D` is invariant under a
mixed switch (`lowest_switch_step`, PROVED from the chain: `P_recursion_pos/neg`, `P_support` of a
smoothing with `c−1` components, the proved row algebra `zRow_a_mul`/`zRow_aInv_mul`/
`zRow_z_mul_eq_zero_of_inSupportM`, and `twoLambda_switch`).  Reduction by strong induction on the finset
of *wrong* mixed crossings `wrongCrossings D` (smaller-index component over) — `lowest_reduce` PROVED;
at `wrongCrossings = ∅` the diagram is `BlockOrdered D id`, `stack_formula` gives `δ^{c−1} ∏ P(D_i)`,
`zRow_delta_pow_mul` (proved) extracts the row, `zRow_zero_prod_of_inSupportM_one` (proved, from
`CV.zRow_zero_mul_of_inSupportM_one`) splits `[z^0]` of the product, and `Λ = 0` by
`SM.zero_link.over_constant` (`twoLambda_eq_zero_of_blockOrdered`).  Decision B5: no record-level
reformulation of `Λ`; the switch behaviour of `mixedSignSum` is computed directly on the double sum
(`mixedSignSum_switch_of_mem/of_not_mem`), since `over_constant` is only available in that form anyway.

**lem:homflyrows.**  All three fields PROVED in the skeleton from `join_value_of_cleanMarkedJoin`,
`P_splitUnion` (proved: `SM.stack.split_union` with `blk c := if c ∈ B then 0 else 1`, `restrict_congr`,
`presentations`), `two_component_row_of_lowest` (proved), `P_eq_homfly`, `homfly_descent`,
`CV.zRow_zero_mul_of_inSupportM_one`.

**mp:blocks.**  `writhe_additive` PROVED modulo the partition lemma `sum_restrictCrossings_blocks`;
`sign_preserved` and `product` PROVED modulo the two `JoinForest` inductions (`sign_preserved_of_joinForest`,
`product_of_joinForest`) and — for `product` — the realization.  `realizes` is ANALYSED (§5): its chain is
stated (`restrictCrossings_univ_iso`, `isRealizable_restrictCrossings_of_gapContiguous`,
`restrictCrossings_join_decomp`, `exists_joinForest_of_realizable`, `exists_markedInterval_of_mark`) and the
assembly `realizes_of_blockSupply` is PROVED from them.

## 2. The chain, row by row

Notation: "uses" lists accepted declarations (file:line verified by grep on 2026-09-14) and skeleton lemmas.
Estimates are lines of Lean for the proof body.

### 2.1 mp:join

Record level (namespace `SM.Link.Record`, skeleton §G.1–G.4):

| # | lemma (skeleton) | status | uses | est. |
|---|---|---|---|---|
| J1 | `Mark.switch μ x : (ρ.switch x).Mark` (def), `Mark.switch_comp/gap`, `Mark.map_refl` | proved | `Record.switch` LinkRecord:655 (definitional on `comps`, `M`, `comp`) | — |
| J2 | `joinRecord_switch_inl : Nonempty (RecordIso ((joinRecord μ₁ μ₂).switch (inl a)) (joinRecord (μ₁.switch a) μ₂))` | **proved** | `switch_isOver` :688, `switch_sgn` :692, `joinRecord_pair_inl` :1548 | — |
| J3 | `lastKeep f p u : Option {v // p v}` (def) + `lastKeep_of_mem`, `lastKeep_sameCycle`, `lastKeep_eq_none_iff` | proved | `Perm.SameCycle.exists_nat_pow_eq`, `sameCycle_inv` | — |
| J4 | `Mark.smoothMark μ x : (ρ.smooth x).Mark` (def, both proof fields proved) + spec `smoothMark_of_gap_none/some` | proved | `smooth_comp` LinkRecord:918, `reconnect` :822, `SmoothKeep` :849 | — |
| J5 | `firstReturn_mul_swap_of_lastKeep_some (hb : p b) (ha' : lastKeep f p a = some a') : firstReturn (f * swap a b) p = firstReturn f p * swap a' ⟨b, hb⟩` | sorry | `firstReturn_mul_swap_apply_left` Stack:276, `firstReturn_val_eq_of_pow` :207, `mul_swap_pow_apply_of_forall_ne` :230, `returnTime_min/spec` LinkRecord:64-67 | 120 |
| J6 | `firstReturn_mul_swap_of_lastKeep_none (hb) (ha : lastKeep f p a = none) : firstReturn (f * swap a b) p = firstReturn f p` | sorry | same | 60 |
| J7 | `firstReturn_sumCongr_inl/inr` (first return of `f ⊕ g` to `SumKeep p`), `lastKeep_sumCongr_inl` | sorry | `sumCongr_pow` LinkRecord:258, `firstReturn_val_congr` Stack:382 | 90 |
| J8 | `sumCongr_mul_swap_sameCycle_inl_inl/inr_inr/inl_inr` (cycles of `(f ⊕ g) * swap (inl a) (inr b)`) | sorry | `mul_swap_sameCycle_of_pow_eq` LinkRecord:213, `mul_swap_sameCycle_left/right/self` :235-246, `mul_swap_sameCycle_or` LinkRecordExtras:64, `not_sumCongr_sameCycle_inl_inr` :286, `sumCongr_sameCycle_inl_iff` :266 | 150 |
| J9 | `joinRecord_reconnect_inl : (joinRecord μ₁ μ₂).reconnect (inl a) = sumCongr (ρ₁.reconnect a) ρ₂.succ * gapSwap (μ₁.gap.map (swap a (τa))) μ₂.gap` | sorry | `Equiv.swap_apply_apply` (conjugation), `gapSwap` LinkRecord:1234, `joinSucc` :1279 | 50 |
| J10 | `joinRecord_smooth_inl : Nonempty (RecordIso ((joinRecord μ₁ μ₂).smooth (inl a)) (joinRecord (μ₁.smoothMark a) μ₂))` | sorry | J3–J9, `smooth` LinkRecord:895, `firstReturn_congr_pred` Stack:217, `Equiv.ofBijective`, `Quotient.lift` | 250-300 |
| J11 | `joinRecord_comm : Nonempty (RecordIso (joinRecord μ₁ μ₂) (joinRecord μ₂ μ₁))` | sorry | `Equiv.sumComm`, `Equiv.sumCompl (· = μ.comp)`, `joinComp_inr_of_eq/of_ne` LinkRecord:1300-1304, `joinSucc_*` :1325-1364 | 90 |
| J12 | `RBasing.MarkedFirst B μ` (def), `RBasing.markedFirst_switch` | proved | — | — |
| J13 | `exists_markedFirst_rbasing μ : ∃ B, B.MarkedFirst μ` | sorry | `RBasing.default` PolynomialBlock:326, `Fintype.equivFin`, `Mark.gap_none/gap_comp` | 40 |
| J14 | `RBasing.join B₁ B₂ μ₁ μ₂ : RBasing (joinRecord μ₁ μ₂)` — `rank`, `rank_inj`, `base` DEFINED; `base_comp`, `base_const` sorry | partial | `joinComp_inl/inr_of_eq/of_ne` :1298-1304, `RBasing.base_comp/base_const` :139 | 40 |
| J15 | `RBasing.rUnderFirst_join (h₁ : B₁.MarkedFirst μ₁) (h₂) (u₁ : B₁.RUnderFirst) (u₂) : (B₁.join B₂ μ₁ μ₂).RUnderFirst` | sorry | `RBasing.key/pos/pow_pos_base/pos_le` PolynomialBlock:159-189, `joinSucc_inl_of_ne` LinkRecord:1336, `joinSucc_gap_left/right` :1359-1364, `Function.minimalPeriod` + `iterate_eq_iterate_iff_of_lt_minimalPeriod`, `Prod.Lex.toLex_lt_toLex` | 180-220 |

Polynomial level (namespace `SM`, skeleton §H.2), all PROVED:
`Diagram.markSwitch`, `Diagram.markSmooth` (defs), `Diagram.markedFirst_rbasingSwitch`, `join_switch_record`
(uses `switchRecordIso` LinkDiagramRecord:686, `RecordIso.switch` LinkRecord:778, J2,
`RecordIso.joinRecord` LinkRecordExtras:553, `Mark.map_refl`), `join_smooth_record` (uses
`exists_smoothing_record_visit` Smoothing:8185, `RecordIso.smooth` LinkRecordExtras:432, J10),
`join_isPositive_iff` (`RecordIso.sgn_eq`, `joinRecord_sgn_inl` :1556, `isPositive_iff_sign_eq_one`
LinkDiagram:559), `join_step` (`solvedR_of_skein` PolynomialBlock:120, `solvedR_mul_left` :114, `P_skein`
:638), `join_core_right_underFirst` (`skein_induction_based` :551, `exists_underFirst_of_rUnderFirst` :469,
`RBasing.map`/`rUnderFirst_map` :267/:312, `P_underFirst_init` :683, `componentCount_joinRecord`
LinkRecord:1560, `record_componentCount` LinkDiagramRecord:537, J15), `join_core` (J11, J13),
`join_value_of_cleanMarkedJoin`, and the three fields of `SM.join`.

### 2.2 mp:lowest

| # | lemma | status | uses | est. |
|---|---|---|---|---|
| L1 | `coeffAt_a_mul/aInv_mul/z_mul/zInv_mul`, `coeff_T_mul'`, `zRow_a_mul`, `zRow_aInv_mul`, `zRow_z_mul`, `zRow_zInv_mul`, `zRow_delta_pow_mul`, `zRow_z_mul_eq_zero_of_inSupportM`, `aPow_neg_mul_aPow`, `InSupportM.one_mul_one`, `InSupportM.one_prod`, `zRow_zero_prod_of_inSupportM_one`, `P_knotRestrict_inSupportM_one` | **all proved** | `AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff`, `coeff_zRow` LinkLaurentRing:338, `zRow_sub` :344, `zRow_single` :347, `zRow_eq_zero_iff` :359, `inSupportM_iff` :875, `InSupportM.mul_left` :887, `InSupportM.one` :966, `R.delta` :193, `CV.zRow_zero_mul_of_inSupportM_one` CV/Axioms:154, `P_support` PolynomialBlock:765, `knotRestrict_componentCount` (statement file) | — |
| L2 | `Diagram.restrict_congr`, `Diagram.blockRestrict_id`, `wrongCrossings` (def), `mem_wrongCrossings`, `mixed_of_mem_wrongCrossings`, `knotRestrict_switch_of_mixed`, `exists_smoothing_of_mixed` | proved | `switch_restrict_of_external` LinkDiagramExtras:746, `exists_smoothing_counts` Smoothing:8202, `record_isSelfCrossing_iff` LinkDiagramRecord:583 | — |
| L3 | `blockOrdered_id_of_wrongCrossings_eq_empty (h : D.wrongCrossings = ∅) : BlockOrdered D id` | sorry | `BlockOrdered` Stack:65, `mem_iff` LinkDiagram:519, `eq_under_of_mem_of_ne` :523 | 25 |
| L4 | `wrongCrossings_switch (hx : x ∈ D.wrongCrossings) : (D.switch x).wrongCrossings = D.wrongCrossings.erase x` | sorry | `switch_overStrand_self/of_ne` LinkDiagram:665-669, `switch_underStrand_self/of_ne` :673-680 | 30 |
| L5 | `mixedSignSum_comm D i j : mixedSignSum D i j = mixedSignSum D j i` | sorry | `mixedSignSum` ZeroLink:31, `Shadow.MixedPair` :25, `Finset.pair_comm`, `Finset.sum_comm` | 30 |
| L6 | `mixedSignSum_switch_of_not_mem` (pair not met by `x`: unchanged) | sorry | `switch_sign_of_ne` LinkDiagram:694 (the crossing `⟨{s,t},_⟩ ≠ x` because a strand of `x` has component `∉ {i,j}` or the pair is the wrong way round) | 40 |
| L7 | `mixedSignSum_switch_of_mem (hij) (h : x meets (i,j)) : mixedSignSum (D.switch x) i j = mixedSignSum D i j - 2 * sign x` | sorry | `switch_sign_self` :688, `switch_sign_of_ne` :694, `Fintype.sum_eq_single`/`Finset.sum_erase` twice (exactly one ordered pair `(s,t)` with `{s,t} = x.val`, `s.1 = i`, `t.1 = j`), `crossing_pair_spec` LinkDiagram:291 | 80 |
| L8 | `twoLambda_switch (hx : mixed) : twoLambda (D.switch x) = twoLambda D - 2 * sign x` | sorry | L6, L7 on the double sum `∑ i ∑ j, if i < j` (only the pair `(min, max)` of the two strand components changes) | 60 |
| L9 | `twoLambda_eq_zero_of_blockOrdered (h : BlockOrdered D id) : twoLambda D = 0` | sorry | `SM.zero_link.over_constant` ZeroLink:1325 (second disjunct: for `i < j`, `hord x s t` gives `underStrand = s`, so `overStrand = t` by `eq_over_of_mem_of_ne` LinkDiagram:527), `Finset.sum_eq_zero` | 40 |
| L10 | `twoLambda_two (h2 : c = 2) (hij) : twoLambda D = twoLinking D i j` | sorry | L5, `Fin` case analysis on `Fin D.Γ.c` with `D.Γ.c = 2` (`Fin.sum_univ_two` after `Finset.univ = {i, j}` via `Finset.eq_of_subset_of_card_le`, `Finset.card_pair`) | 50 |
| L11 | `lowest_switch_step`, `lowest_blockOrdered`, `lowest_reduce`, `lowest_value_of_reduce`, `two_component_row_of_lowest`, `SM.lowest` | **proved** | `stack_formula` Stack:1317, `P_recursion_pos/neg` PolynomialBlock:693-697, `componentCount_pos` LinkDiagram:582, L1–L10 | — |

### 2.3 lem:homflyrows — everything PROVED
`P_splitUnion` (`SM.stack.split_union` Stack:1350/1339, `blockRestrict` :58, `restrict_congr`,
`presentations` PolynomialBlock:1177), `SM.homflyrows` (`P_eq_homfly` :667, `homfly_descent`
LinkInterfaces:395, `CV.zRow_zero_mul_of_inSupportM_one`, `two_component_row_of_lowest`,
`join_value_of_cleanMarkedJoin`).

### 2.4 mp:blocks

| # | lemma | status | uses | est. |
|---|---|---|---|---|
| K1 | `RecordIso.crossingEquiv (i) : ρ.Crossing ≃ ρ'.Crossing` (to/inv defined; `left_inv/right_inv` sorry) + `crossingEquiv_crossingOf` | partial | `Crossing.rep` LinkRecordExtras:587, `crossingOf_rep` :603, `eq_rep_or_eq_pair_rep` :607, `RecordIso.crossingOf_eq` LinkRecord:628, `crossingOf_pair` :469 | 50 |
| K2 | `joinCrossingEquiv μ₁ μ₂ : (joinRecord μ₁ μ₂).Crossing ≃ ρ₁.Crossing ⊕ ρ₂.Crossing` (to/inv defined) + `joinCrossingEquiv_sgn` | partial | `joinRecord_pair_inl/inr` :1548-1550, `joinRecord_sgn_inl/inr` :1556-1557, `crossingOf_eq_iff` :485 | 70 |
| K3 | `sum_restrictCrossings_blocks ρ g : ∑ H, ∑ v : (ρ.restrictCrossings H.supp).M, g v.1 = ∑ v, g v` | sorry | `SimpleGraph.ConnectedComponent.mem_supp_iff`, `Finset.sum_fiberwise`, `Finset.sum_subtype`, `CrossKeep` (statement file) | 40 |
| K4 | `writhe_eq_sum_blocks`, `writhe_additive_of_blockSupply` | **proved** (modulo K3) | `two_mul_writhe` LinkRecord:439, `record_writhe` LinkDiagramRecord:578, `RecordIso.writhe_eq` :624 | — |
| K5 | `product_of_joinForest C : JoinForest C S J → ∀ T : Finset ι, ↑T = S → P J = ∏ i ∈ T, P (C i)` | sorry | `JoinForest` induction, `join_value_of_cleanMarkedJoin`, `Finset.prod_singleton`, `Finset.prod_union` (`T₁ := T.filter (· ∈ S₁)`), `Finset.coe_inj`, `Finset.coe_filter` | 50 |
| K6 | `sign_preserved_of_joinForest C : JoinForest C S J → ∀ T, ↑T = S → ∃ φ : (Σ i : T, (C i).Γ.Crossing) ≃ J.Γ.Crossing, ∀ q, J.sign (φ q) = (C q.1).sign q.2` | sorry | K1, K2, a `D.Γ.Crossing ≃ D.record.Crossing` bridge (`crossingOf (overVisit x)` / `c.rep.1`; `record_pair_apply` LinkDiagramRecord:524, `twin` :413), `sign_eq_of_recordIso` PolynomialBlock:829, `Equiv.Set.union`-style split of `T` into `T₁, T₂` (`Equiv.sigmaSumDistrib`, `Equiv.sigmaCongrLeft`, `Finset.disjoint_filter`), `Equiv.sigmaUnique`-type leaf | 120-150 |
| K7 | `sign_preserved_of_blockSupply`, `product_of_blockSupply`, `SM.blocks` | **proved** (modulo K5, K6, realizes) | `presentations`, `Equiv.subtypeUnivEquiv` | — |
| K8 | realization chain (§5): `restrictCrossings_univ_iso`, `exists_markedInterval_of_mark`, `isRealizable_restrictCrossings_of_gapContiguous`, `restrictCrossings_join_decomp`, `exists_joinForest_of_realizable`; `realizes_of_blockSupply` **proved** from them | analysed | see §5 | see §5 |

## 3. Already proved in the skeleton (no `sorry`, ~520 lines of new material)
`Mark.switch`, `Mark.map_refl`, `joinRecord_switch_inl`, `lastKeep` + three lemmas, `Mark.smoothMark` + two
spec lemmas, `RBasing.MarkedFirst`, `markedFirst_switch`, `RBasing.join` (data + `rank_inj`),
`writhe_eq_sum_blocks`, `GapContiguous`, `restrict_congr`, `blockRestrict_id`, `wrongCrossings` API,
`knotRestrict_switch_of_mixed`, `exists_smoothing_of_mixed`, the whole row-algebra unit L1,
`markSwitch`/`markSmooth`/`markedFirst_rbasingSwitch`, `join_switch_record`, `join_smooth_record`,
`join_isPositive_iff`, `join_step`, `join_core_right_underFirst`, `join_core`,
`join_value_of_cleanMarkedJoin`, `lowest_switch_step`, `lowest_blockOrdered`, `lowest_reduce`,
`lowest_value_of_reduce`, `two_component_row_of_lowest`, `product_of_blockSupply`,
`writhe_additive_of_blockSupply`, `sign_preserved_of_blockSupply`, `realizes_of_blockSupply`,
`P_splitUnion`, and the four rows `join`, `lowest`, `blocks`, `homflyrows`.

## 4. Unit split for parallel provers (each provable from the skeleton alone; dependencies noted)

| unit | lemmas | est. lines | depends on |
|---|---|---|---|
| **U1** perm level | J5 `firstReturn_mul_swap_of_lastKeep_some`, J6 `..._none`, J7 `firstReturn_sumCongr_inl/inr`, `lastKeep_sumCongr_inl` | 270 | none (pure `Equiv.Perm`; Stack.lean §U1 helpers) |
| **U2** cycles + reconnect | J8 three `sumCongr_mul_swap_sameCycle_*`, J9 `joinRecord_reconnect_inl` | 200 | none |
| **U3** smoothing iso | J10 `joinRecord_smooth_inl` | 250-300 | U1, U2 (may start with them as hypotheses) |
| **U4** comm + basings | J11 `joinRecord_comm`, J13 `exists_markedFirst_rbasing`, J14 `RBasing.join.base_comp/base_const`, J15 `rUnderFirst_join` | 350-390 | none |
| **U5** lowest bookkeeping | L3, L4, L5, L9, L10 | 175 | none |
| **U6** switch of Λ | L6, L7, L8 | 180 | none (L5 not needed) |
| **U7** crossing equivalences + partition | K1, K2, K3 | 160 | none |
| **U8** forest inductions | K5, K6 | 170-200 | K1, K2 (statements only) |
| **U9** (realization lane, §5) | K8 | see §5 | U1 (J5/J6 style lemmas), U7 |

Closing U1–U8 (≈ 1800 lines) proves `SM.join`, `SM.lowest`, `SM.homflyrows` completely and `SM.blocks` up to
the two fields `realizes`/`product`, which wait on U9.  Independent-review boundary: each unit's statements
are in the skeleton with docstrings naming the printed lines.

## 5. `realizes` — analysis (BlocksData.realizes; D9's tracked sub-obligation)

**What the fixed clause asks.**  `∃ J, JoinForest C Set.univ J ∧ Nonempty (RecordIso J.record ρ)`, where
`JoinForest` nodes are `IsCleanMarkedJoin A B J := Nonempty (RecordIso J.record (joinRecord A.μ B.μ))` for
`A B : MarkedDiagram` (an actual diagram, a printed interval `I` with `IsMarkedInterval`, and the record mark
`μ` it determines), and leaves are the supplied `C H`.  Nothing in the clause requires `J` to be produced by
a cut-and-splice operation: a node is ANY actual diagram whose record is the join record (design D9,
NOTES_FINAL risk 2).

**Structural finding: no clean-join construction is needed.**  (i) The root node can be the supplied
actual diagram itself: `BlockSupply.actual : IsRealizable ρ` gives `D₀` with `D₀.record ≅ ρ`, and the
combinatorial identity `ρ ≅ joinRecord μ₁ μ₂` (sub-records `restrictCrossings S₁`, `restrictCrossings S₂`)
makes `D₀` a clean marked join of ANY realizations of the two sub-records.  (ii) Realizations of the
sub-records are obtained from a realization of `restrictCrossings S` by SMOOTHING AWAY the other block's
crossings and restricting to the surviving circle — accepted geometry only (`exists_smoothing_record_visit`
Smoothing:8185, `Diagram.restrict` LinkDiagram:1082, `restrictRecordIso` LinkDiagramRecord:1454): if the
`S₂`-occurrences lie in one gap of `S₁` (`GapContiguous`), then smoothing at an `S₂`-crossing whose two
occurrences lie on the `S₁`-circle splits off a loop carrying no `S₁`-occurrence (both occurrences are in
the gap, so one of the two arcs `(x A y B) ↦ (x B), (y A)` is inside the gap); smoothing at a crossing with
one occurrence on a loop merges the loop back INTO THE GAP; smoothing at a crossing off the `S₁`-circle
does not touch it (`smooth_succ_val_of_comp_ne` LinkRecord:1104).  In every case the `S₁`-first-return
successor is unchanged (a `firstReturn (f * swap a b) K = firstReturn f K` lemma for `a, b` in one `K`-gap —
the `lastKeep a = lastKeep b` case of U1's J5, plus the loop case) and the `S₁`-points stay on one circle.
After all `S₂`-crossings are gone, `Diagram.restrict` to that circle has record `≅ restrictCrossings S₁`
(the other circles are crossing-free).  Symmetrically for `S₂` (contiguity is symmetric on a circle).
(iii) The leaves are the supplied `C H` with `supplied H`.  (iv) The only genuinely geometric input is
`exists_markedInterval_of_mark : ∀ D μ, ∃ I, IsMarkedInterval D I ∧ I.i = μ.comp ∧ ∀ v, μ.gap = some v ↔
D.IsGapOf I v` — a short clean arc just after the gap occurrence (any arc of a crossing-free marked circle).

Consequently the printed construction 1387-1425 (sphere chart, ribbon to the exterior, affine shrinking) and
the printed nested-insertion 1664-1676 are NOT needed for the formal clause; the judge's estimate "≥ 1500
lines of sphere chart / ribbon / affine shrinking" and NOTES_FINAL risk 6's dependence of `product` on
new geometry both collapse to (iv).  (The geometric existence of clean joins for ARBITRARY marked `A, B`
remains true and would be a fine library fact, but no row consumes it; it is dropped from this chain.)

**Chain (all stated in the skeleton §H.4, `sorry`):**
1. `Record.restrictCrossings_univ_iso ρ : Nonempty (RecordIso (ρ.restrictCrossings Set.univ) ρ)` — as
   `restrictUnivIso` LinkRecord:1190 (`firstReturn` at a full predicate is the permutation,
   `firstReturn_apply_of_mem` :106).  ~30 lines.
2. `exists_markedInterval_of_mark` (geometric).  Construction: `p` = a point of the open edge just after the
   gap visit's parameter (`crossingParam` LinkDiagram:1413, `clampIco` Smoothing:438 for the parameter
   arithmetic), or any edge interior point of a crossing-free circle; `ε` below the clearance of `p` from
   every other strand and from the two vertices of its edge (finitely many compact segments not containing
   `p`; `IsCompact.exists_infDist_eq_dist` or the elementary segment-distance bound used by
   `seg_arc_subset_closedBall` in Smoothing.lean); `U := Metric.closedBall p ε` (`isDisc_closedBall`
   LinkMoves:103); `I` := the traversal interval of that edge inside `U` (a convex set meets a segment in a
   segment); `ArcCover U {I}` (`ArcCover` LinkMoves:208, `Arc` :145, `Arc.Mem` :168), `Clean U D`
   (:342: the two frontier points are traversed once — the segment through the centre of the square is not
   parallel to a side it meets; `exits` since `U` is small), no visit on `I` (clearance), `IsGapOf`: the
   gap occurrence is the last visit of the component before `I.start` (`cycBetween` LinkDiagramRecord:78,
   `nextVisit_no_between` :335).  The smoothing lane's `SpliceModel`/`edgePt`/`SmallEps` lemmas
   (Smoothing.lean §0', §1) are the reusable toolkit.  **~400-600 lines**; this is the single geometric
   unit of the block and it is elementary (one disc, one straight arc).
3. `isRealizable_restrictCrossings_of_gapContiguous (h1 : ρ.componentCount = 1) (hsub : S₁ ⊆ S)
   (hS : IsRealizable (ρ.restrictCrossings S)) (hgap : ρ.GapContiguous S₁ S) :
   IsRealizable (ρ.restrictCrossings S₁)` (record part, with the accepted smoothing gate).  Proof: induction
   on the number of `S \ S₁` crossings inside an actual realization `X` of `restrictCrossings S`; each step
   `exists_smoothing_record_visit`, the three record cases above (`smooth_succ_val_of_comp_ne`,
   `firstReturn_firstReturn` Stack:313 to compose first returns, the U1 lemmas), invariant "the `S₁`-points
   are on one circle, in their `S₁`-first-return order, and the remaining `S \ S₁` points on that circle
   lie in the gap"; finish with `Diagram.restrict` to the circle and `restrictRecordIso`, plus a
   `restrictCrossings_restrictCrossings` composition iso (`firstReturn_firstReturn`).  **~500 lines.**
4. `restrictCrossings_join_decomp` (combinatorics on the circle, one-circle record): (a) `Interlaces` and
   `ArcBetween`/`steps` bookkeeping on a one-circle record (representative independence, symmetry —
   NOTES_FINAL risk 7); (b) "a chord outside a connected block `A` has both ends in one gap of `A`"
   (`SimpleGraph.ConnectedComponent` induction along `Reachable`/`Walk`; sm-3:1638-1645); (c) two
   interlacing chords outside `A` share the gap, hence every other block lies in one gap of `A`
   (1646-1652); (d) existence of an INNERMOST block `B'` (all other blocks of `S` in one gap of `B'`):
   minimise the number of occurrences of a gap `(B, g)` containing a block; (e) `S₂ := B'.supp`,
   `S₁ := S \ S₂`, both `GapContiguous` in `S`; (f) the record identity
   `restrictCrossings S ≅ joinRecord μ₁ μ₂` with `μ₁.gap :=` the `S₁`-occurrence before the gap,
   `μ₂.gap :=` the last `S₂`-occurrence of the gap — a `firstReturn` computation of the same type as J10
   (`firstReturn_mul_swap`, `firstReturn_sumCongr_*`).  **~700-900 lines** ((a)-(e) ≈ 450, (f) ≈ 250).
5. `exists_joinForest_of_realizable` (assembly, induction on the number of blocks of `S`, using 2-4,
   `Mark.map` LinkRecordExtras:478, `RecordIso.joinRecord` :553, `IsRealizable.of_iso`
   LinkDiagramRecord:722).  **~150 lines.**
6. `realizes_of_blockSupply` — PROVED from 1 and 5 in the skeleton.

**Total for `realizes` (and hence `product`): ≈ 1800-2200 lines, of which ≈ 500 geometric.**  Feasible with
the accepted layer; recommended as its own lane (U9) after U1 (its `firstReturn` lemmas are shared).
Fallback if the innermost-block search (4d) proves awkward: recurse instead on "the block containing the
first occurrence after a base gap" exactly as printed (1653-1663), which needs the linear-order
bookkeeping of a cut circle but no minimisation.

## 6. Risks and fallbacks

* **R-B1 (size of J10).**  `joinRecord_smooth_inl` is the largest unit: the circle bijection between
  `SmoothComps (joinRecord) (inl a)` and `(ρ₁.smooth a).comps ⊕ μ₂.Unmarked` needs `Quotient.lift` well
  definedness from J8 and `Equiv.ofBijective`.  Fallback/simplification: a shared helper
  `RecordIso.ofOccurrences` — build a `RecordIso` from an occurrence bijection `Φ` commuting with `succ`,
  `pair`, bits, signs, together with a bijection of the crossing-free circles only (the circle bijection on
  circles carrying occurrences is forced: `comp v ↦ comp (Φ v)`, well defined by `sameCycle_iff_comp_eq`
  LinkRecord:376 and `RecordIso.sameCycle_iff` :603).  ~120 lines, and it would also shorten J11 and 4(f).
* **R-B2 (positions in J15).**  `pos` on the joined marked circle: `A`'s portion first, `B`'s shifted by the
  length of `A`'s marked cycle (`Function.minimalPeriod`).  Fallback: prove the ORDER statement
  `key (inl v) < key (inl w) ↔ key v < key w` via the characterisation "`pos v ≤ n ↔ ∃ m ≤ n,
  succ^m base = v`" (`Nat.find_le`, `pos_le` PolynomialBlock:164) instead of computing `pos` exactly.
* **R-B3 (`match hg : μ.gap` in `Mark.smoothMark`).**  Provers must use the spec lemmas
  `smoothMark_of_gap_none/some` (proved), never unfold the `match`.
* **R-B4 (`twoLambda_switch`).**  The changed pair is `(min, max)` of the two strand components of `x`;
  handle `over.1 < under.1` and `under.1 < over.1` separately (L7 is stated for either order).
* **R-B5 (`product` waits on U9).**  As the judge noted; unchanged, but U9 is now record work plus one
  elementary disc lemma (§5), not the sphere chart.
* **R-B6 (fidelity, inherited).**  NOTES_FINAL risks 1-2 (record marks ⊋ printed marks; `IsCleanMarkedJoin`
  quantifies over every diagram with the join record) are exactly what makes §5 work; nothing here changes
  the fixed statements.
* **R-B7 (Mathlib names).**  Verified on the pin: `AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff`,
  `Equiv.swap_apply_apply`, `Equiv.Set.union`, `Equiv.sigmaSumDistrib`, `Equiv.sigmaCongrLeft`,
  `SimpleGraph.ConnectedComponent.mem_supp_iff`, `Finset.filter_eq'`, `Finset.eq_of_subset_of_card_le`,
  `Finset.prod_pair`, `LaurentPolynomial.T_add/T_zero`, `Perm.SameCycle.exists_nat_pow_eq`,
  `Perm.sameCycle_inv`, `Function.iterate_eq_iterate_iff_of_lt_minimalPeriod`, `Equiv.Perm.iterate_eq_pow`.
  (`if_pos`/`dif_pos` are deprecated on this pin: use `ite_eq_left/right`, `dite_eq_left/right`.)

## 7. Reuse index (accepted declarations consumed, file:line)
PolynomialBlock.lean: `solvedR_mul_left` 114, `solvedR_of_skein` 120, `RBasing` 139, `RBasing.pos` 159,
`key` 174, `IsBad` 189, `RUnderFirst` 192, `RBasing.switch` 221, `RBasing.map` 267, `badCount_map` 298,
`rUnderFirst_map` 312, `RBasing.default` 326, `rbasingSwitch` 365, `exists_underFirst_of_rUnderFirst` 469,
`skein_induction_based` 551, `P_skein` 638, `P_eq_homfly` 667, `P_underFirst_init` 683,
`P_recursion_pos/neg` 693/697, `P_support` 765, `P_knot_support` 815, `sign_eq_of_recordIso` 829,
`P_addFree` 1036 (template), `presentations` 1177.  Stack.lean: `blockRestrict` 58, `BlockOrdered` 65,
`firstReturn_val_eq_of_pow` 207, `firstReturn_congr_pred` 217, `mul_swap_pow_apply_of_forall_ne` 230,
`firstReturn_pow_val_spec` 243, `firstReturn_mul_swap_apply_left` 276, `firstReturn_firstReturn` 313,
`firstReturn_mul_swap` 345, `firstReturn_val_congr` 382, `stack_formula` 1317, `StackData`/`stack`
1339/1350.  LinkRecord.lean: `firstReturn` 100, `mul_swap_apply_of_ne_of_ne` 202,
`mul_swap_sameCycle_*` 213-246, `sumCongr_pow` 258, `sumCongr_sameCycle_inl_iff` 266,
`not_sumCongr_sameCycle_inl_inr` 286, `Record` 309, `sameCycle_iff_comp_eq` 376, `writhe` 437,
`two_mul_writhe` 439, `Crossing` 461, `crossingOf` 467, `crossingOf_pair` 469, `crossingOf_eq_iff` 485,
`RecordIso` 539, `RecordIso.sameCycle_iff` 603, `RecordIso.writhe_eq` 624, `RecordIso.crossingOf_eq` 628,
`switch` 655, `switch_isOver/sgn` 688/692, `RecordIso.switch` 778, `reconnect` 822, `SmoothKeep` 849,
`SmoothComps` 880, `smooth` 895, `smooth_comp` 918, `smooth_comp_eq_iff` 932, `smoothPairIso` 1040,
`IsSelfCrossing` 1069, `smooth_succ_val_of_comp_ne` 1104, `restrict` 1144, `restrictUnivIso` 1190,
`Mark` 1226, `gapSwap` 1234, `sumSucc` 1252, `joinSucc` 1279, `Mark.Unmarked` 1282, `joinComp` 1294,
`joinComp_inr_of_eq/of_ne` 1300/1304, `joinSucc_inl_of_ne` 1336, `joinSucc_gap_left/right` 1359/1364,
`joinRecord` 1513 (+ simp lemmas 1544-1557), `componentCount_joinRecord` 1560, `writhe_joinRecord` 1590.
LinkRecordExtras.lean: `mul_swap_sameCycle_or` 64, `not_mul_swap_sameCycle_of_sameCycle` 76,
`RecordIso.smooth` 432, `RecordIso.restrict` 456, `Mark.map` 478, `RecordIso.joinRecord` 553,
`Crossing.rep` 587, `crossingOf_rep` 603, `eq_rep_or_eq_pair_rep` 607.  LinkDiagramRecord.lean:
`cycBetween` 78, `nextVisit_no_between` 335, `twin` 413, `record` 500, `record_pair_apply` 524,
`record_sgn` 526, `record_componentCount` 537, `record_writhe` 578, `record_isSelfCrossing_iff` 583,
`switchRecordIso` 686, `switch_record` 697, `IsRealizable` 718, `isRealizable_record` 720,
`IsRealizable.of_iso` 722, `restrictRecordIso` 1454.  LinkDiagramExtras.lean: `restrict_isPositive_iff` 585,
`switch_sign` 628, `switch_restrict_of_external` 746.  LinkDiagram.lean: `crossing_pair_spec` 291,
`mem_iff` 519, `eq_under_of_mem_of_ne` 523, `eq_over_of_mem_of_ne` 527, `sign` 552,
`isPositive_iff_sign_eq_one` 559, `componentCount_pos` 582, `switch` 650, `switch_overStrand_self/of_ne`
665/669, `switch_underStrand_self/of_ne` 673/680, `switch_sign_self/of_ne` 688/694, `restrict` 1082,
`restrict_componentCount` 1085, `restrict_sign` 1088, `crossingParam` 1413.  ZeroLink.lean:
`Shadow.MixedPair` 25, `mixedSignSum` 31, `mixedPair_iff` 1153, `sign_mixed_eq` 1223, `zero_link` 1325.
LinkLaurentRing.lean: `coeffAt` 286, `coeffAt_single` 299, `zRow` 335, `coeff_zRow` 338, `zRow_add/sub`
342/344, `zRow_single` 347, `zRow_eq_zero_iff` 359, `InSupportM` 846, `inSupportM_iff` 875,
`InSupportM.mul_left` 887, `InSupportM.one` 966.  LinkInterfaces.lean: `homfly` 131, `homfly_descent` 395.
LinkMoves.lean: `IsDisc` 100, `isDisc_closedBall` 103, `Arc` 145, `Arc.Mem` 168, `ArcCover` 208,
`OutsideMatch` 316, `Clean` 342, `LocalFrame` 348, `Reparam` 370/387, `Deform` 462/478,
`PlanarIsotopic` 516, `IsMarkedInterval` 1107.  Smoothing.lean: `clampIco` 438, `SpliceModel` 1466,
`exists_smoothing` 8170, `exists_smoothing_record` 8178, `exists_smoothing_record_visit` 8185,
`exists_smoothing_counts` 8202.  CV/Axioms.lean: `inSupportM_one_iff` 102,
`zRow_zero_mul_of_inSupportM_one` 154.
