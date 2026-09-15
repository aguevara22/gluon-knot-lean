# PLAN_FINAL — marked products (mp:join, mp:lowest, mp:blocks, lem:homflyrows): the judge's adopted plan

Judge: 2026-09-14.  Inputs: `PLAN_A.md`/`Skeleton_A.lean` (Architect A, record-first, 1072 lines, 29 sorries)
and `PLAN_B.md`/`Skeleton_B.lean` (Architect B, reuse-first, 1501 lines, 34 sorries).  Output:
**`Skeleton_FINAL.lean`** (1616 lines; `cd work/lean && lake env lean ../drafts/markedproducts/Skeleton_FINAL.lean`:
**0 errors, 13 `sorry` warnings**, all chain lemmas of §3; the four row theorems `SM.join` (3 fields),
`SM.lowest` (2), `SM.blocks` (4 — `realizes`/`product` through the analysed chain), `SM.homflyrows` (3) are
PROVED from the chain).  Fixed statements: `work/drafts/MarkedProducts_statement.lean` — sections A-E (lines
106-348) and the four bundles (352-370, 376-395, 401-428, 434-461) are pulled into the skeleton BY SCRIPT from the
statement file (byte-identical; re-verified by substring check after assembly).  Axiom audit (`#print axioms` on a
`/tmp` copy): `SM.join`, `SM.lowest`, `SM.blocks` depend on `propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm`;
`SM.homflyrows` additionally on `SM.lit_homfly`, `SM.lp_lm_uniqueness` (through `homfly`/`P_eq_homfly`); every
lemma the judge closed is sorry-free (`propext, Classical.choice, Quot.sound`).

## 0. Checks on the two deliveries

| | A | B |
|---|---|---|
| `lake env lean` from `work/lean` | 0 errors, **29** sorry warnings (5.9 s) | 0 errors, **34** sorry warnings (12.3 s) |
| fixed defs 106-348 / bundles byte-identical | yes (all five blocks) | yes (all five blocks) |
| rows proved from the chain | all four (realizes via B5+B6+B7) | all four (realizes via K8) |
| new material PROVED | ~130 lines: `weight_switch_of_isMixed`, `lowest_of_blockOrdered`, `lowest_value_aux`, `two_component_row_of_lowest`, `P_join_init/step_left/step_right/of_underFirst/aux`, `join_value_of_iso`, `joinForest_P`, `realizes_aux/of_chain`, algebra glue | ~520 lines: all row algebra (L1), `joinRecord_switch_inl`, `lastKeep` API, `Mark.smoothMark` + specs, `RBasing.join` data, `join_step`, both inductions, `lowest_switch_step/blockOrdered/reduce/value`, `two_component_row_of_lowest`, `P_splitUnion`, `writhe_eq_sum_blocks`, all assemblies |

### Falsity probes (riskiest chain lemma of each)

* **A — `exists_joinRecord_smooth_inl` (J4, existential μ₀) and the geometric `exists_cleanMarkedJoin` (B6).**
  J4: hand-checked the three degenerate cases against the accepted `joinSucc_gap_left/right`, `reconnect`,
  `smooth_emptied_circle`: (i) `μ₁.gap = none` (the marked circle of `A` is free; the smoothed join is
  `sumCongr (reconnect a) s₂` and `μ₀ = ⟨inr ⟨μ₁.comp, _⟩, none⟩`); (ii) `μ₁.gap = some a` (gap AT the smoothed
  occurrence: after smoothing, `B`'s marked cycle is inserted after the last retained occurrence before `τa`,
  which is exactly `lastKeep (reconnect a) keep (τa)`); (iii) `succ a = τa` with `gap = a` (a kink: the interval
  lands on the emptied loop `⟦τa⟧`, `μ₀.gap = none`, and `gapSwap none _ = 1` keeps `B`'s marked cycle
  separate, matching the smoothed join in which `inr g₂ ↦ inl τa ↦ inr (succ g₂)` collapses to `inr g₂ ↦ inr (succ g₂)`).
  All consistent; the existential form is moreover strictly weaker than B's fixed-witness form, so it is at
  least as true.  B6 is NOT adopted (see §5): B's realizes route needs no clean-join construction, so the
  ≥1500-line geometric lemma leaves the chain entirely.
* **B — `firstReturn_mul_swap_of_lastKeep_some` (J5, the heart of `joinRecord_smooth_inl`) and the structural
  claim `isRealizable_restrictCrossings_of_gapContiguous`.**  J5: proved in Lean (probe, /tmp) that when the
  swap point is retained the statement IS the accepted `firstReturn_mul_swap` (SM/Stack.lean:345) via
  `lastKeep_of_mem` — the generalisation is consistent with the accepted lemma; the unretained case was
  hand-checked (from `a'` the walk passes `a`, jumps to `f b`; from `b` to `f a` and back to the return of
  `a'`; other retained points never meet `a` or `b` before returning — `a'` being the LAST retained before `a`
  is exactly what excludes a retained point strictly between).  The realizability claim: hand-checked the
  smoothing-away invariant on a one-circle record with the `S \ S₁` occurrences in one `S₁`-gap: smoothing a
  crossing with both occurrences in the gap splits off a loop carrying no `S₁`-point; a crossing with one
  occurrence on a loop and one in the gap merges the loop INTO the gap; crossings off the `S₁`-circle never
  touch it; hence the `S₁`-first-return successor is invariant and all `S₁`-points stay on one circle.  TRUE;
  the statement needs `Record.restrict` to the `S₁`-circle at the end (the smoothed diagram has extra
  crossing-free circles; `restrictCrossings` alone would keep them) — accounted for in the estimate (§3).
  Also verified: `joinRecord_comm` (B's weak form) by PROVING it (§4).

## 1. Verdict: winner **B**, with grafts from A

Why B is the base: (1) B has ~4× more proved material, in particular the whole row-algebra unit and the
complete mp:lowest and lem:homflyrows lanes (only the `Λ`-bookkeeping was open, and the judge closed most of
it); (2) B's realizes analysis is a genuine structural improvement — the root node of the forest is the
SUPPLIED actual diagram (`BlockSupply.actual`) and sub-records are realized by smoothing away the other block
inside an actual realization, so the ≥1500-line geometric `exists_cleanMarkedJoin` (A's B6, "no precedent in
work/lean") is not needed; the only geometry left is one clean disc around an edge point; (3) B's
`wrongCrossings` (a `Finset`, membership `over.1 < under.1`) is simpler than A's `badMixedCount` (an
existential filter), and B's `joinRecord_switch_inl` is already proved.

Grafts from A (adopted because they are weaker-as-hypotheses or already proved):
* the mp:join DIAGRAM lane (`P_join_init`, `P_join_step_left/right`, `P_join_of_underFirst`, `P_join_aux`,
  `join_value_of_iso`, `RBasing.MarkCompatible` as a structure with named fields) — it consumes the two hard
  record lemmas in **existential** form: `exists_rUnderFirst_joinRecord : ∃ B : RBasing (joinRecord μ₁ μ₂), B.RUnderFirst`
  and `exists_joinRecord_smooth_inl : ∃ μ₀ : (ρ₁.smooth a).Mark, Nonempty (RecordIso … (joinRecord μ₀ μ₂))`.  Both
  inductions quantify the IH over ALL marks / basings, so the existential suffices, and it leaves the prover
  free to pick the witness (B's `RBasing.join`, Skeleton_B.lean:668, and B's `Mark.smoothMark`, kept PROVED
  in the FINAL as the intended witness of J4).  Where A and B agreed on content, A's weaker statement wins.
* `joinRecord_comm` in B's weak form (`Nonempty`) instead of A's `∃ ι, ∀ v, ι.Φ v = Sum.swap v` — the
  consumers only destructure the `Nonempty`; the judge proved it (with `Φ = Sum.swap` anyway).
* `joinForest_P` (A, PROVED, `Set.toFinset` form) replaces B's sorried `product_of_joinForest`.
* `joinForest_sign` (A: `Σ i : S`, Set-indexed, matching the bundle field directly) and
  `IsCleanMarkedJoin.crossingEquiv` (A's single diagram-level node lemma) replace B's `Finset`-indexed
  `sign_preserved_of_joinForest` and B's partially defined `RecordIso.crossingEquiv`/`joinCrossingEquiv`
  (which remain the recommended sub-lemmas, PLAN §4 unit U-B2).
* `exists_markCompatible_rbasing` (A's name/structure; PROVED by the judge).

Dropped: A's `Mark.switchMark` (= B's `Mark.switch`), A's `badMixedCount` lane, A's `exists_peel`/B7 (replaced
by B's `restrictCrossings_join_decomp`), A's B5/B6 geometry (B5 = B's `exists_markedInterval_of_mark`; B6 gone),
B's `RBasing.join`/`rUnderFirst_join`/`exists_markedFirst_rbasing`/`MarkedFirst` (subsumed by the existential J3
and A's `MarkCompatible`), B's `RecordIso.crossingEquiv`/`joinCrossingEquiv` partial defs, B's J7-J9
(`firstReturn_sumCongr_*`, `sumCongr_mul_swap_sameCycle_*`, `joinRecord_reconnect_inl`: sub-lemmas of J4, listed
in §4 as the recommended decomposition, not stated as chain sorries).

## 2. Route per row (as realized in Skeleton_FINAL.lean)

* **mp:join** (`SM.join`, §I:1582, all three fields = `Link.join_value_of_iso`, H.2:1290).  Outer
  `skein_induction_based` on the left factor `A` with `B` quantified (`P_join_aux`:1263), whose init is the
  inner induction on `B` with `A` UNDER-first (`P_join_of_underFirst`:1237); marks carried by
  `RBasing.MarkCompatible` (G.3:564; "marked circle first, based at the gap", sm-3:1440-1441) and re-chosen by
  `exists_markCompatible_rbasing` (573, PROVED) after each smoothing.  Base (`P_join_init`:1141): J3 gives an
  UNDER-first basing of `joinRecord`, transported to `J` by `RBasing.map`, then `P_underFirst_init` three times
  and `componentCount_joinRecord`.  Step (`P_join_step_left`:1164): `switchRecordIso`, `RecordIso.switch`, B's
  proved `joinRecord_switch_inl` (G.1:404) and `RecordIso.joinRecord` for the switch; `exists_smoothing_record_visit`
  twice, `RecordIso.smooth`, J4 and `RecordIso.joinRecord` for the smoothing; `solvedR_of_skein` + `P_skein` on
  `J` and on `A`, `solvedR_mul_left`.  Right step (`P_join_step_right`:1216) = left step after `joinRecord_comm`
  (628, PROVED).
* **mp:lowest** (`SM.lowest`:1588).  `lowest_value_of_reduce` (1380) from `lowest_reduce` (1345): induction on
  `wrongCrossings.card`; each step `wrongCrossings_switch` (852, PROVED), `lowest_switch_step` (1303:
  `P_recursion_pos/neg`, `P_support` of the `c−1`-component smoothing via `exists_smoothing_of_mixed`,
  `zRow_z_mul_eq_zero_of_inSupportM`, `zRow_a_mul`/`zRow_aInv_mul`, `twoLambda_switch`) and
  `knotRestrict_switch_of_mixed`; at zero `blockOrdered_id_of_wrongCrossings_eq_empty` (839, PROVED),
  `lowest_blockOrdered` (1329: `stack_formula` with `blockRestrict_id`, `zRow_delta_pow_mul`,
  `zRow_zero_prod_of_inSupportM_one`) and `twoLambda_eq_zero_of_blockOrdered` (936, PROVED via
  `SM.zero_link.over_constant`).  `two_component_row_of_lowest` (1388) from `twoLambda_two` (959, PROVED via
  `mixedSignSum_comm` 893, PROVED) and `Finset.prod_pair`.
* **lem:homflyrows** (`SM.homflyrows`:1601): `connected_sum` = `join_value_of_iso` + `P_eq_homfly` ×3 +
  `homfly_descent` ×2; `split_union` = `P_splitUnion` (1546, PROVED: `SM.stack.split_union` with
  `blk c := if c ∈ B then 0 else 1`, `restrict_congr`, `presentations`) + the same transfer;
  `two_component_row` = `two_component_row_of_lowest` + `P_eq_homfly` + `CV.zRow_zero_mul_of_inSupportM_one`
  with `P_knotRestrict_inSupportM_one` (1127) + `ring`.
* **mp:blocks** (`SM.blocks`:1594): `writhe_additive` = `writhe_additive_of_blockSupply` (1523, PROVED from
  `writhe_eq_sum_blocks` 769 ← `sum_restrictCrossings_blocks` 750, PROVED); `sign_preserved` =
  `sign_preserved_of_blockSupply` (1533) from `joinForest_sign` (B3) + `sigmaUnivEquiv`; `product` =
  `product_of_blockSupply` (1512) from `realizes_of_blockSupply` + `joinForest_P` (1410, PROVED) + `presentations`;
  `realizes` = `realizes_of_blockSupply` (1495, PROVED from the analysed chain of §5: `restrictCrossings_univ_iso`
  790 PROVED, `exists_joinForest_of_realizable` 1483 ← `restrictCrossings_join_decomp` 1465,
  `isRealizable_restrictCrossings_of_gapContiguous` 1456, `exists_markedInterval_of_mark` 1447).

## 3. The chain: the 13 `sorry` lemmas (exact statements = Skeleton_FINAL.lean at the given line)

All in namespace `SM.Link` (sub-namespace as shown).  "consumes" lists accepted declarations (file:line under
work/lean/, grep-verified by both architects) and FINAL lemmas.

| # | line | statement | consumes | est. lines |
|---|---|---|---|---|
| **J5** | 545 | `Record.firstReturn_mul_swap_of_lastKeep_some (f : Perm α) (p) [DecidablePred p] (a b : α) (hb : p b) {a'} (ha' : lastKeep f p a = some a') : firstReturn (f * swap a b) p = firstReturn f p * swap a' ⟨b, hb⟩` | `firstReturn_mul_swap_apply_left` Stack:276, `firstReturn_val_eq_of_pow` :207, `mul_swap_pow_apply_of_forall_ne` :230, `returnTime_min/spec` LinkRecord:64-67; pattern `firstReturn_mul_swap` Stack:345 (the `p a` case, verified by the judge) | 120 |
| **J6** | 553 | `Record.firstReturn_mul_swap_of_lastKeep_none … (hb : p b) (ha : lastKeep f p a = none) : firstReturn (f * swap a b) p = firstReturn f p` | same; `lastKeep_eq_none_iff` (480, PROVED) | 60 |
| **J3** | 723 | `Record.exists_rUnderFirst_joinRecord (B₁ : RBasing ρ₁) (B₂ : RBasing ρ₂) (μ₁) (μ₂) (h₁ : B₁.RUnderFirst) (h₂ : B₂.RUnderFirst) (hμ₁ : B₁.MarkCompatible μ₁) (hμ₂ : B₂.MarkCompatible μ₂) : ∃ B : RBasing (joinRecord μ₁ μ₂), B.RUnderFirst` | witness: B's `RBasing.join` (Skeleton_B.lean:668-696, `rank_inj` proved there; ranks `inl c ↦ if c = μ₁.comp then 0 else 2·B₁.rank c + 2`, `inr c ↦ 2·B₂.rank c + 1`; base `inl (B₁.base a)`, on the joined circle `μ₁.gap.elim (inr (B₂.base b)) (fun g₁ => inl (B₁.base g₁))`); `RBasing.key/pos/pow_pos_base/pos_le` PolynomialBlock:159-189, `joinSucc_inl_of_ne/inr_of_ne/gap_left/gap_right/inl_of_none/inr_of_none` LinkRecord:1336-1364, `joinRecord_pair_inl/inr` :1548, `Prod.Lex.toLex_lt_toLex`, `Nat.find_min'`.  Positions: `pos (inl a) = B₁.pos a`; `pos (inr b) = |A's marked cycle| + B₂.pos b` on the joined circle (or prove only the order statement `key (inl v) < key (inl w) ↔ key v < key w` via `pos_le`, B's fallback R-B2) | 250 |
| **J4** | 739 | `Record.exists_joinRecord_smooth_inl (μ₁) (μ₂) (a : ρ₁.M) : ∃ μ₀ : (ρ₁.smooth a).Mark, Nonempty (RecordIso ((joinRecord μ₁ μ₂).smooth (Sum.inl a)) (joinRecord μ₀ μ₂))` | witness `μ₁.smoothMark a` (500, PROVED; use `smoothMark_of_gap_none/some` 521/528, never unfold the `match`); occurrences `{v : M₁ ⊕ M₂ // v ∉ {inl a, inl τa}} ≃ {w // w ∉ {a, τa}} ⊕ M₂`; successor: `(joinRecord μ₁ μ₂).reconnect (inl a) = sumCongr (ρ₁.reconnect a) ρ₂.succ * gapSwap (μ₁.gap.map (swap a τa)) μ₂.gap` (conjugation, `Equiv.swap_apply_apply`), then J5/J6 with `b := inr g₂` retained, `lastKeep` of a sum on `inl` = left `lastKeep`, first return of `sumCongr` on `inl`/`inr` (`sumCongr_pow` LinkRecord:258, `firstReturn_val_congr` Stack:382); circles: cycles of `(f ⊕ g) * swap (inl x) (inr y)` (`mul_swap_sameCycle_*` LinkRecord:213-246, LinkRecordExtras:64-76, `sumCongr_sameCycle_inl_iff` :266, `not_sumCongr_sameCycle_inl_inr` :286), `Quotient.lift` + `Equiv.ofBijective`, or the helper `RecordIso.ofOcc` (§4); bits/signs by `Sum` cases, `smooth_isOver/sgn`, `RecordIso.smooth` LinkRecordExtras:432 as the model | 500 (three units) |
| **L6** | 909 | `mixedSignSum_switch_of_not_mem (D) (x) (i j) (h : ¬(over.1 = i ∧ under.1 = j) ∧ ¬(over.1 = j ∧ under.1 = i)) : mixedSignSum (D.switch x) i j = mixedSignSum D i j` | `switch_sign_of_ne` LinkDiagram:694 (`⟨{s,t},_⟩ ≠ x` because a strand of `x` has component `∉ {i,j}` or the order is wrong: `val_eq_pair` :516, `mem_iff` :519), `Finset.sum_congr` twice, `(D.switch x).Γ = D.Γ` rfl | 40 |
| **L7** | 919 | `mixedSignSum_switch_of_mem (D) (x) (i j) (hij : i ≠ j) (h : (over.1 = i ∧ under.1 = j) ∨ (over.1 = j ∧ under.1 = i)) : mixedSignSum (D.switch x) i j = mixedSignSum D i j - 2 * (D.sign x : ℤ)` | `switch_sign_self` :688 at the unique ordered pair `(s,t)` with `{s,t} = x.val`, `s.1 = i`, `t.1 = j` (`crossing_pair_spec` :291, `mixedPair_iff` ZeroLink:1153, `isCrossing_pair_iff_of_fst_ne` :1136); `switch_sign_of_ne` elsewhere; `Finset.sum_erase`/`Fintype.sum_eq_single` twice; `SignType` cast `-σ = σ - 2σ` | 80 |
| **L8** | 928 | `twoLambda_switch (D) {x} (hx : over.1 ≠ under.1) : twoLambda (D.switch x) = twoLambda D - 2 * (D.sign x : ℤ)` | L6, L7 on `∑ i ∑ j, if i < j then twoLinking …`: exactly the pair `(min, max)` of the two strand components is hit (`lt_or_gt_of_ne hx`; both orders of L7's hypothesis), `Finset.sum_ite_eq`/`Finset.sum_sub_distrib` | 60 |
| **B2** | 1431 | `IsCleanMarkedJoin.crossingEquiv {A B} {J} (h) : ∃ φ : A.D.Γ.Crossing ⊕ B.D.Γ.Crossing ≃ J.Γ.Crossing, (∀ x, J.sign (φ (inl x)) = A.D.sign x) ∧ (∀ y, J.sign (φ (inr y)) = B.D.sign y)` | `D.Γ.Crossing ≃ D.record.Crossing` (`x ↦ crossingOf (overVisit x)`, inverse `p ↦ p.rep.1`; `crossingOf_eq_iff` LinkRecord:485, `visit_eq_over_or_under` LinkDiagram:613, `Crossing.rep`/`crossingOf_rep`/`eq_rep_or_eq_pair_rep` LinkRecordExtras:587-607, `record_pair_apply` LinkDiagramRecord:524); `RecordIso.crossingOf_eq` :628 induces `ρ.Crossing ≃ ρ'.Crossing` (B's `RecordIso.crossingEquiv`, Skeleton_B.lean:713); `(joinRecord μ₁ μ₂).Crossing ≃ ρ₁.Crossing ⊕ ρ₂.Crossing` from `joinRecord_pair_inl/inr` (B's `joinCrossingEquiv` :725); signs `record_sgn` :526, `sgn_eq`, `joinRecord_sgn_inl/inr` :1556 | 180 |
| **B3** | 1439 | `joinForest_sign {ι} (C) : ∀ S J, JoinForest C S J → ∃ φ : (Σ i : S, (C i).Γ.Crossing) ≃ J.Γ.Crossing, ∀ q, J.sign (φ q) = (C q.1).sign q.2` | `JoinForest` induction; leaf `Set.uniqueSingleton`/`Equiv.sigmaUnique`; node `Equiv.Set.union hdisj`, `Equiv.sigmaCongrLeft`, `Equiv.sigmaSumDistrib`, `Equiv.sumCongr φA φB`, B2 | 120 |
| **R1** | 1447 | `exists_markedInterval_of_mark (D) (μ : D.record.Mark) : ∃ I : D.Γ.Arc, IsMarkedInterval D I ∧ I.i = μ.comp ∧ ∀ v, μ.gap = some v ↔ D.IsGapOf I v` | GEOMETRIC (the only geometry of the block): a point `p` in the open edge just after the gap visit's parameter (`crossingParam` LinkDiagram:1413, `clampIco` Smoothing:438) or any edge interior point of a crossing-free circle; `ε` below the clearance of `p` from every other segment and the edge's vertices (finitely many compact segments not containing `p`; Smoothing.lean §1 "clearance radius" :679-790 is the template); `U := closedBall p ε` (`isDisc_closedBall` LinkMoves:103); `I` = the traversal sub-interval of that edge inside `U`; `ArcCover U {I}` (:208), `Clean U D` (:342: two frontier points, every component exits), no visit on `I`; `IsGapOf`: `nextVisit_no_between` LinkDiagramRecord:335, `cycBetween` :78 | 400-600 |
| **R2** | 1456 | `isRealizable_restrictCrossings_of_gapContiguous (ρ) (h1 : ρ.componentCount = 1) {S₁ S} (hsub : S₁ ⊆ S) (hS : IsRealizable (ρ.restrictCrossings S)) (hgap : ρ.GapContiguous S₁ S) : IsRealizable (ρ.restrictCrossings S₁)` | induction on `#(S \ S₁)` inside an actual `X` with `X.record ≅ restrictCrossings S'` (`S₁ ⊆ S' ⊆ S`); invariant on `X.record`: the `S₁`-image points lie on one circle `c` in their `S₁`-first-return order and the other `S'`-image points on `c` lie in one `S₁`-gap; step `exists_smoothing_record_visit` Smoothing:8185 + the record lemma "smoothing an unretained crossing whose two occurrences are in one `K`-gap or on `K`-free circles does not change `firstReturn succ K` and keeps the `K`-points on one circle" (variant of J5/J6 with BOTH swap points unretained: `lastKeep a = lastKeep b` or one `= none`; `smooth_succ_val_of_comp_ne` LinkRecord:1104, `firstReturn_firstReturn` Stack:313); finish: `Diagram.restrict` to `c` (LinkDiagram:1082), `restrictRecordIso` LinkDiagramRecord:1454, `RecordIso.restrict` LinkRecordExtras:456, `restrictCrossings_univ_iso` (790) | 600-800 |
| **R3** | 1465 | `restrictCrossings_join_decomp (ρ) (h1) (S) (hS : ∀ H, H.supp ⊆ S ∨ Disjoint H.supp S) (h2 : ∃ H ≠ H', H.supp ⊆ S ∧ H'.supp ⊆ S) : ∃ S₁ S₂, S₁ ∪ S₂ = S ∧ Disjoint S₁ S₂ ∧ S₁.Nonempty ∧ S₂.Nonempty ∧ (∀ H, H.supp ⊆ S₁ ∨ Disjoint H.supp S₁) ∧ (∀ H, H.supp ⊆ S₂ ∨ Disjoint H.supp S₂) ∧ ρ.GapContiguous S₁ S ∧ ρ.GapContiguous S₂ S ∧ ∃ μ₁ μ₂, Nonempty (RecordIso (ρ.restrictCrossings S) (joinRecord μ₁ μ₂))` | COMBINATORIAL (sm-3:1637-1663): (a) `steps`/`ArcBetween` toolbox on a one-circle record (totality via `succ_cycle`, `steps_succ_pow`, trichotomy, representative independence of `Interlaces`); (b) a chord outside a connected block `A` has both ends in one gap of `A` (`SimpleGraph.ConnectedComponent` induction along `Reachable`/`Walk`); (c) two interlacing chords outside `A` share the gap, so every other block is in one gap of `A`; (d) a cyclically consecutive block `T` (A's span-minimal block from a base point, or B's minimal-gap block); `S₂ := T.supp`, `S₁ := S \ S₂`; (e) the join identity: `μ₁.gap :=` the `S₁`-point before the gap, `μ₂.gap :=` the last `S₂`-point of the gap; successor by `firstReturn_val_eq_of_pow` Stack:207, `firstReturn_pow_val_spec` :243, `joinSucc_gap_left/right`; `Unmarked μ₂` empty on one circle | 700-900 (three units) |
| **R4** | 1483 | `exists_joinForest_of_realizable (ρ) (C) (h : BlockSupply ρ C) : ∀ S, (∀ H, H.supp ⊆ S ∨ Disjoint H.supp S) → S.Nonempty → IsRealizable (ρ.restrictCrossings S) → ∃ J, JoinForest C {H \| H.supp ⊆ S} J ∧ Nonempty (RecordIso J.record (ρ.restrictCrossings S))` | strong induction on `(univ.filter (fun H => H.supp ⊆ S)).card`; one block: `S = H₀.supp` (every `x ∈ S` has its block `⊆ S`, hence `= H₀`), leaf `C H₀` with `h.supplied`; several: R3, R2 twice, IH twice, `Mark.map` along the isos (LinkRecordExtras:478), R1 twice for the `MarkedDiagram`s, `RecordIso.joinRecord` :553, and the GIVEN realization `X` of `restrictCrossings S` is the node (`JoinForest.join … ⟨ιX.trans (κ.trans (RecordIso.joinRecord ι₁.symm ι₂.symm μ₁ μ₂))⟩`); index sets `{H \| supp ⊆ S₁} ∪ {H \| supp ⊆ S₂} = {H \| supp ⊆ S}` from the block properties and `Disjoint` from `supp` nonempty (`mem_supp_iff`) | 150 |

Dependencies: J5, J6 → J4 (and their both-unretained variant → R2); R1, R2, R3 → R4 → `realizes` → `product`;
B2 → B3 → `sign_preserved`; L6, L7 → L8 → `lowest_value` (through the PROVED `lowest_switch_step`) →
`two_component_row` → `homflyrows.two_component_row`; J3, J4 → `join_value` → `homflyrows.connected_sum`
and → `product`.  `homflyrows.split_union`, `writhe_additive` are already fully proved (no sorry upstream).

## 4. Units for parallel provers (each provable from Skeleton_FINAL.lean alone)

| unit | lemmas | est. lines | depends on | notes |
|---|---|---|---|---|
| **U-L** | L6, L7, L8 | 180 | — | closes mp:lowest and lem:homflyrows completely.  L7: handle `over.1 < under.1` and `under.1 < over.1` separately; model on `Record.sum_sgn_switch` (LinkRecord:740) and the proved `mixedSignSum_comm` (893) |
| **U-J5** | J5, J6 | 180 | — | pure `Equiv.Perm`; template `firstReturn_mul_swap` Stack:345-380 (the judge's probe shows J5 restricted to `p a` IS that lemma) |
| **U-J3** | J3 | 250 | — | copy B's `RBasing.join` (Skeleton_B.lean:668) as the witness; prove `base_comp`, `base_const` (Skeleton_B:693-696) and `RUnderFirst`.  Only existence is needed: the base of the joined circle may sit at `inl (succ g₁)` or, symmetrically, at `inr (succ g₂)` |
| **U-J4a** | helper `RecordIso.ofOcc` (optional): a `RecordIso` from an occurrence bijection commuting with `succ/pair/isOver/sgn` plus a bijection of the crossing-free circles (`card_comps_eq_cycleCount_add_card_freeComp` LinkRecordExtras:238, `sameCycle_map_iff` :370, `sameCycle_iff_comp_eq` LinkRecord:376) | 120 | — | removes all circle bookkeeping from J4 and R3(e); add above J4 when done |
| **U-J4b** | J4 | 350 | U-J5 (statements), U-J4a | witness `Mark.smoothMark` (500) with `smoothMark_of_gap_none/some`; sub-lemmas as in B's J7-J9 (Skeleton_B.lean:572-622): `firstReturn_sumCongr_inl/inr`, `lastKeep_sumCongr_inl`, `sumCongr_mul_swap_sameCycle_inl_inl/inr_inr/inl_inr`, `joinRecord_reconnect_inl`; fallback for circles: `Quotient.congr` as in `RecordIso.smooth` LinkRecordExtras:432 |
| **U-B2** | B2, B3 | 300 | — | `Equiv` plumbing only; B's `RecordIso.crossingEquiv`/`joinCrossingEquiv`/`joinCrossingEquiv_sgn` (Skeleton_B:713-738) are the natural sub-lemmas |
| **U-R1** | R1 (GEOMETRIC) | 400-600 | — | the single geometric unit of the block; adapt Smoothing.lean §1 (clearance radius) to an edge interior point |
| **U-R2** | R2 | 600-800 | U-J5-type lemma with both swap points unretained | record induction inside an actual diagram; see §5 |
| **U-R3a** | R3 (a)-(c): `steps` toolbox, one-gap lemma | 350 | — | fallback: transport to the actual `D₀` of `BlockSupply.actual` and use `Diagram.VisitBetween` (LinkDiagramRecord:882-974) |
| **U-R3b** | R3 (d)-(e): consecutive block + join identity | 400 | U-R3a, U-J4a | |
| **U-R4** | R4 | 150 | R1-R3 (statements) | set/finset bookkeeping; can be written now against the sorried statements |

Critical path of mp:join: U-J4b (after U-J5, U-J4a).  mp:lowest + lem:homflyrows: U-L alone (≈180 lines) finishes
both rows AND `homflyrows.connected_sum` waits only on mp:join.  mp:blocks: `writhe_additive` DONE; `sign_preserved`
= U-B2; `realizes`/`product` = the realization lane U-R1..R4 (≈ 2000-2500 lines).

### Lemmas closed by the judge (all sorry-free, `#print axioms` = `propext, Classical.choice, Quot.sound`)

`Record.exists_markCompatible_rbasing` (573, J1: rank `μ.comp ↦ 0`/`equivFin + 1`, base `μ.gap.elim v succ` on the
marked circle, `RBasing.default` elsewhere), `Record.joinRecord_comm` (628, J2a: `Φ = Sum.swap`, circle bijection
abstracted behind three spec equations, `hswap` by cases on the two gaps), `Record.sum_restrictCrossings_blocks`
(750, K3: `Finset.sum_subtype` + `Finset.sum_fiberwise` along `connectedComponentMk ∘ crossingOf`, `mem_supp_iff`),
`Record.restrictCrossings_univ_iso` (790, B4: `Equiv.subtypeUnivEquiv`, `firstReturn_apply_of_mem`),
`Diagram.blockOrdered_id_of_wrongCrossings_eq_empty` (839, L3), `Diagram.wrongCrossings_switch` (852, L4:
`Finset.ext_iff` with `y : D.Γ.Crossing` and `Iff.trans` instead of `rw` across `(D.switch x).Γ.Crossing`),
`mixedSignSum_comm` (893, L5: `Finset.sum_comm` + `Finset.pair_comm` + `Subtype.ext`),
`twoLambda_eq_zero_of_blockOrdered` (936, L9: `SM.zero_link.over_constant`, second disjunct, `eq_over_of_mem_of_ne`),
`twoLambda_two` (959, L10: `Finset.eq_of_subset_of_card_le`, `Finset.sum_pair` three times, `lt_or_gt_of_ne`).
Kept PROVED from B: `Mark.switch`, `Mark.map_refl`, `joinRecord_switch_inl`, `lastKeep` + 3 lemmas,
`Mark.smoothMark` + 2 specs, `writhe_eq_sum_blocks`, `restrict_congr`, `blockRestrict_id`, `wrongCrossings` API,
`knotRestrict_switch_of_mixed`, `exists_smoothing_of_mixed`, the row-algebra unit H.1, `lowest_switch_step`,
`lowest_blockOrdered`, `lowest_reduce`, `lowest_value_of_reduce`, `two_component_row_of_lowest`,
`realizes_of_blockSupply`, `product_of_blockSupply`, `writhe_additive_of_blockSupply`, `P_splitUnion`.
From A: `P_join_init`, `P_join_step_left/right`, `P_join_of_underFirst`, `P_join_aux`, `join_value_of_iso`,
`joinForest_P`, `sigmaUnivEquiv`, `optionMap_eq_self`.

## 5. `BlocksData.realizes` — analysis and recommendation (D9's tracked sub-obligation)

**What the fixed clause asks.**  `∀ ρ C, BlockSupply ρ C → ∃ J, JoinForest C Set.univ J ∧ Nonempty (RecordIso J.record ρ)`,
where a `JoinForest` node is `IsCleanMarkedJoin A B J := Nonempty (RecordIso J.record (joinRecord A.μ B.μ))` for
`A B : MarkedDiagram` (an actual diagram with a printed interval `I`, `IsMarkedInterval`, and the record mark it
determines).  Design D9 (NOTES_FINAL risk 2): a node is ANY actual diagram with the join record, not a
cut-and-splice product.

**Adopted route (B's structural finding, verified by the judge).**  No clean-join construction is needed:
1. The ROOT node is the supplied actual diagram: `BlockSupply.actual` gives `D₀` with `D₀.record ≅ ρ ≅ restrictCrossings univ`
   (`restrictCrossings_univ_iso`, PROVED); with the combinatorial identity `restrictCrossings S ≅ joinRecord μ₁ μ₂`
   (R3) `D₀` IS a clean marked join of any realizations of the two sub-records.  The same holds at every internal
   node: the realization of `restrictCrossings S` produced by R2 is the node.
2. Realizations of the sub-records (R2) come from smoothing away the other block's crossings inside an actual
   realization — accepted geometry only (`exists_smoothing_record_visit`, `Diagram.restrict`, `restrictRecordIso`).
   The invariant (judge-verified, §0): with all `S \ S₁` occurrences in one `S₁`-gap, smoothing a crossing with
   both occurrences in the gap splits off a loop with no `S₁`-point; with one occurrence on a loop and one in
   the gap, merges the loop into the gap; off the `S₁`-circle, nothing changes.  So `firstReturn succ (S₁-points)`
   is invariant and the `S₁`-points stay on one circle; at the end restrict the actual diagram to that circle.
   Subtlety the executor must respect: `Record.restrictCrossings` keeps ALL circles (`comps := ρ.comps`), so the
   invariant must be phrased on `(X.record.restrictCrossings K).restrict {c}` (one circle) or directly on the
   first-return permutation of the `K`-points; the smoothed diagram has extra crossing-free circles which
   `Diagram.restrict {c}` removes.
3. The leaves are the supplied `C H` (`BlockSupply.supplied`).
4. The only geometric input is R1 `exists_markedInterval_of_mark` (a clean disc around an edge point, to make
   the sub-realizations `MarkedDiagram`s) — ~400-600 lines, elementary, with Smoothing.lean §1 as the template.

Hence the printed sphere-chart / ribbon / affine-shrinking construction (sm-3:1387-1425) and A's B6
`exists_cleanMarkedJoin` (≥ 1500 lines, no precedent in work/lean) are NOT needed for the formal clause; they
remain true library facts nobody consumes.  A's B5 = R1; A's B7 `exists_peel` ≈ R3.

**Size.**  R1 400-600 (geometric) + R2 600-800 + R3 700-900 + R4 150 ≈ **1900-2450 lines**, of which only R1
is geometry.  Compare A: B5 300-500 + B6 ≥ 1500 (novel geometry) + B7 700-900 ≈ ≥ 2500-2900.

**Fidelity.**  The route relies on exactly the two fidelity choices already recorded (NOTES_FINAL risks 1-2):
record marks ⊋ printed marks (R1 shows every record mark of an actual diagram IS a printed mark, so nothing is
lost) and `IsCleanMarkedJoin` = any diagram with the join record.  `JoinForest` permits arbitrary marks at the
nodes (risk 8), which is what lets the node be the given realization.  No statement changes.

**Recommendation: SEPARATE LANE, and DEFER `product`.**  Run U-R1..U-R4 as its own lane after U-J5/U-J4a
(shared `firstReturn` toolbox); `realizes` and `product` are the only fields waiting on it, and `product` is
not independent of `realizes` in this design (NOTES_FINAL risk 6 stands: the forest's partial joins must be
actual diagrams; there is no record-only argument for `∏_H P_{C_H}`).  Everything else in the four rows —
`join_value` and its two corollaries, both mp:lowest fields, all three lem:homflyrows fields, `sign_preserved`,
`writhe_additive` — is independent of the realization lane.  If the lane stalls, the fallback for R2 is B's
alternative "recurse on the block containing the first occurrence after a base gap, exactly as printed
(1653-1663)" for R3(d), and for R3(a) transport to the actual `D₀` and the accepted `VisitBetween` order.

## 6. Risks and fallbacks

| risk | where | mitigation |
|---|---|---|
| **R-J4** the recombination iso (500 lines) is the critical path of mp:join; circle bookkeeping (`SmoothComps ⊕ FreeComp` vs `(ρ₁.smooth a).comps ⊕ Unmarked μ₂`) is intricate | U-J4b | existential statement (any `μ₀`); `Mark.smoothMark` witness with spec lemmas; `RecordIso.ofOcc` helper; Stack.lean `firstReturn` toolbox (:207-396); fallback `Quotient.congr` as in `RecordIso.smooth` |
| **R-J3** position bookkeeping of the joined circle | U-J3 | existential; witness `RBasing.join`; `pos_le`/`Nat.find_min'` characterisation instead of exact positions |
| **R-R2** the smoothing-away induction mixes diagram existence (`exists_smoothing_record_visit`) with nested-subtype records (`(ρ.smooth x).M = {v // SmoothKeep x v}`) | U-R2 | phrase the invariant on the first-return permutation of the `K`-points and on "all `K`-points on one circle" only; compose first returns with `firstReturn_firstReturn` Stack:313 |
| **R-R3** the `steps`-based cyclic-order toolbox on abstract records is new (the accepted layer measures cyclic order on diagrams) | U-R3a | fallback via `BlockSupply.actual`: transport the graph to `D₀` and use `Diagram.VisitBetween` (LinkDiagramRecord:882-974) |
| **R-R1** no existence lemma for a clean disc around an edge point exists yet in LinkMoves | U-R1 | Smoothing.lean §1 computes the clearance radius around a crossing point; adapt |
| **R-L7** double-sum surgery of `mixedSignSum` under a switch | U-L | model on `Record.sum_sgn_switch` LinkRecord:740; the hit pair is `(overStrand x, underStrand x)` or its swap (`mixedPair_iff`, `isCrossing_pair_iff_of_fst_ne` ZeroLink:1153/1136) |
| **R-types** `rw` across `(D.switch x).Γ.Crossing` vs `D.Γ.Crossing`, `Mark.Unmarked` vs `{c // c ≠ μ.comp}`, `(joinRecord μ₁ μ₂).comps` vs `ρ₁.comps ⊕ μ₂.Unmarked` fails at reducible transparency | everywhere | use `show`/`Iff.trans`/`exact` (defeq) instead of `rw`; give `Equiv`s their explicit `Sum` type and abstract them behind spec equations (see `joinRecord_comm`, `wrongCrossings_switch`) |
| **R-deprecated** `if_pos/dif_pos` deprecated on this pin | everywhere | `ite_eq_left/right`, `dite_eq_left/right` (used throughout) |
| **R-fidelity** record marks ⊋ printed marks; `IsCleanMarkedJoin` over all diagrams with the join record | statements | inherited from NOTES_FINAL risks 1-2 (design D9); exactly what makes §5 work; statements unchanged |

## 7. Files

* `work/drafts/markedproducts/Skeleton_FINAL.lean` — the compiling skeleton (this plan's §2-§3 line numbers).
* `work/drafts/markedproducts/PLAN_A.md`, `Skeleton_A.lean`, `PLAN_B.md`, `Skeleton_B.lean` — the inputs (kept;
  B's `RBasing.join` :668, J7-J9 :572-622, `RecordIso.crossingEquiv`/`joinCrossingEquiv` :713-738 are referenced
  as witness/sub-lemma sketches).
* `work/drafts/markedproducts/NOTES_FINAL.md` — the statement judge's clause maps and risks (unchanged).
