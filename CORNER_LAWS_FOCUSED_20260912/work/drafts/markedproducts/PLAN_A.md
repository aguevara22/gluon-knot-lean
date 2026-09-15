# PLAN_A — marked products (mp:join, mp:lowest, mp:blocks, lem:homflyrows), Architect A (record-first)

Architect A, 2026-09-14.  Skeleton: `work/drafts/markedproducts/Skeleton_A.lean` (1058 lines; `lake env lean`
from `work/lean`: **no errors**, 29 `sorry` warnings = exactly the chain lemmas of its §G; the four row
theorems `SM.join`, `SM.lowest`, `SM.blocks`, `SM.homflyrows` are PROVED from the chain).  Sections A-E and
the four bundles of `work/drafts/MarkedProducts_statement.lean` are copied byte-identically (checked by
substring comparison of the statement file's lines 106-348, 352-370, 376-395, 401-428, 434-461).
`#print axioms` on the row theorems: `propext, sorryAx, Classical.choice, Quot.sound` plus the registered
literature interfaces `SM.lp_lm` (and, for `homflyrows`, `SM.lit_homfly`, `SM.lp_lm_uniqueness`); nothing else.

Judge's inputs honoured: `NOTES_FINAL.md` risks R1-R9 (fidelity risks 1-11 there), proof-lane sketches §1-§4,
the tracked D9 sub-obligation (mp:blocks `realizes`) analysed in §5 below and NOT proved.

## 0. Route in one paragraph per row

* **mp:join** — a NESTED pair of `(N, b)` inductions, both `Diagram.skein_induction_based`
  (SM/PolynomialBlock.lean:551).  Outer on the left factor `A` with the predicate
  `Φ A BA := ∀ μA, BA.MarkCompatible μA → ∀ Bd μB J, J.record ≅ joinRecord μA μB → P J = P A * P Bd`;
  its init (A UNDER-first) is the inner induction on `Bd` with `A` fixed.  The based orders carry the mark
  ("put the marked component first and base it at its marked gap", sm-3:1440-1441) through the new
  predicate `RBasing.MarkCompatible`.  Base: the join of two UNDER-first, mark-compatible based orders is
  UNDER-first (`exists_rUnderFirst_joinRecord`, the record content of sm-3:1443-1451).  Step at a bad
  occurrence `a` of `A`: the occurrence `ι⁻¹(inl a)` of `J`; `record (J^sw) ≅ (joinRecord μA μB).switch (inl a)
  ≅ joinRecord μA' μB` (`joinRecord_switch_inl`), `record J⁰ ≅ (joinRecord μA μB).smooth (inl a) ≅
  joinRecord μ₀ μB` for a re-chosen mark `μ₀` on `A.record.smooth a` (`exists_joinRecord_smooth_inl`);
  `solvedR_of_skein` on `J` and on `A`, `solvedR_mul_left` factors `P Bd`.  The right-factor step is the left
  step after `exists_joinRecord_comm` (the join is symmetric), so no `inr` lemma is needed.  Marks are
  transported along the accepted `switchRecordIso` / `exists_smoothing_record_visit` isomorphisms by
  `Mark.map` (SM/LinkRecordExtras.lean:478) and `RecordIso.joinRecord` (:553).
* **mp:lowest** — `W D := a^{2Λ(D)} [z^{1−c}] P_D` is invariant under a mixed switch
  (`weight_switch_of_isMixed`: the smoothed term has `c−1` components, `P_support` puts it in `M_{c−1}`, so
  `z·P_{D⁰}` has no `z^{1−c}` row; the switched term is `a^{∓2}` times; `2Λ` moves by `∓2`).  Strong
  induction on `badMixedCount D` (mixed crossings where the smaller-index component is over) down to
  `BlockOrdered D id`; there `SM.stack.stack` with singleton blocks, `blockRestrict D id _ i = knotRestrict`,
  `SM.zero_link.over_constant` (`Λ = 0`) and the row extraction `[z^{−(c−1)}] (δ^{c−1} F) = (a−a⁻¹)^{c−1} [z^0] F`
  with `[z^0]` multiplicative on `M_1` (`CV.zRow_zero_mul_of_inSupportM_one`).  `two_component_row` is
  `lowest_value` at `c = 2` with `Λ = ℓ_ij` (`mixedSignSum_comm`).
* **lem:homflyrows** — `connected_sum`: `join_value` + `P_eq_homfly` ×3 + `homfly_descent` ×2;
  `split_union`: `SM.stack.split_union` with `blk c := if c ∈ B then 0 else 1` + `presentations` +
  `P_eq_homfly` + `homfly_descent`; `two_component_row`: `lowest.two_component_row` + `P_eq_homfly` +
  `CV.ax_homfly.knot_parity` + `CV.zRow_zero_mul_of_inSupportM_one`.  Proved in the skeleton modulo one
  unit (`P_split_union`).
* **mp:blocks** — `writhe_additive` and `sign_preserved` are record bookkeeping (`writhe_eq_sum_restrictCrossings`,
  `joinForest_sign`); `product` = `realizes` + `joinForest_P` (a `JoinForest` induction on `join_value`) +
  `presentations`, as printed (sm-3:1675-1677; NOTES_FINAL risk 6: `product` is not independent of
  `realizes`).  `realizes` is ASSEMBLED in the skeleton (`realizes_aux`, `realizes_of_chain`, both compile)
  from one combinatorial record lemma `Record.exists_peel`, the universe iso `restrictCrossings_univ_iso`,
  and two GEOMETRIC lemmas `exists_markedInterval`, `exists_cleanMarkedJoin` — analysed in §5, not proved.

## 1. Accepted declarations consumed (grep-verified, file:line, all under work/lean/)

| declaration | file:line | used by |
|---|---|---|
| `Diagram.skein_induction_based` | SM/PolynomialBlock.lean:551 | both join inductions |
| `Diagram.exists_underFirst_of_rUnderFirst` | :469 | `P_join_init` |
| `Diagram.rbasingSwitch` | :365 | (implicit) IH shape of the inductions |
| `Record.RBasing`, `RUnderFirst`, `IsBad`, `key`, `pos` | :139, :192, :189, :174, :159 | `MarkCompatible`, `exists_rUnderFirst_joinRecord` |
| `Record.RBasing.map`, `rUnderFirst_map`, `key_map` | :267, :312, :281 | `P_join_init` |
| `Record.RBasing.default` | :326 | J1 (base on unmarked circles) |
| `P_underFirst_init` | :683 | `P_join_init` |
| `P_recursion_pos`, `P_recursion_neg` | :693, :697 | `weight_switch_of_isMixed` |
| `solvedR`, `solvedR_mul_left`, `solvedR_of_skein` | :109, :114, :120 | `P_join_step_left` |
| `P_skein` | :638 | `P_join_step_left` |
| `P_support`, `P_knot_support` | :765, :815 | L1/L3 (knot rows), `weight_switch` |
| `P_eq_homfly` | :667 | `homflyrows` |
| `presentations` | :1177 | `blocks.product`, `P_split_union` |
| `Record`, `RecordIso` (+`refl/symm/trans`, `sgn_eq`, `componentCount_eq`, `writhe_eq`, `crossingOf_eq`) | SM/LinkRecord.lean:309, :539, :559-632 | everywhere |
| `Record.switch` (+ `switch_isOver`, `switch_sgn`, `switch_comps/M/comp/succ/pair`) | :655-713 | J2b |
| `RecordIso.switch` | :778 | `P_join_step_left` |
| `Record.reconnect`, `SmoothKeep`, `SmoothComps`, `smoothSucc`, `smooth`, `smooth_succ_val_*`, `smooth_emptied_circle` | :822-1031 | J4 |
| `Record.IsSelfCrossing`, `reconnect_sameCycle_*` | :1069-1101 | J4, L2 |
| `Record.restrict`, `restrictUnivIso` | :1144, :1190 | model for B4 |
| `Record.Mark`, `gapSwap`, `sumSucc`, `joinSucc`, `joinComp`, `joinSucc_inl_of_ne/inr_of_ne/gap_left/gap_right/inl_of_none/inr_of_none`, `joinSucc_sameCycle_*`, `joinRecord`, `joinRecord_*` simp lemmas, `componentCount_joinRecord`, `writhe_joinRecord` | :1226, :1234, :1252, :1279, :1294, :1336-1366, :1398-1445, :1513, :1544-1557, :1560, :1590 | J2a, J2b, J3, J4, B2 |
| `Record.Crossing`, `crossingOf`, `crossingOf_pair`, `crossingOf_eq_iff`, `crossingOf_surjective` | :461-485 | B1, B2, B7 |
| `Record.writhe`, `two_mul_writhe`, `writhe_eq_sum_over`, `sum_eq_two_mul_sum_over` | :437-448, :405 | B1 |
| `firstReturn`, `firstReturn_apply`, `firstReturn_apply_of_mem`, `firstReturn_apply_of_not_mem`, `returnTime_*` | :100-134, :59-70 | J4, B7 |
| `RecordIso.smooth`, `RecordIso.restrict`, `freeCompEquiv`, `firstReturn_map_val`, `sameCycle_map_iff` | SM/LinkRecordExtras.lean:432, :456, :419, :394, :370 | `P_join_step_left`, J4a |
| `Record.Mark.map` (+ `map_comp`, `map_gap`), `RecordIso.joinRecord`, `unmarkedEquiv`, `joinCompsEquiv` | :478-495, :553, :520, :526 | step lemmas, `realizes_aux`, J2a |
| `Record.componentCount_smooth`, `componentCount_smooth_of_mixed`, `card_comps_eq_cycleCount_add_card_freeComp` | :333, :320, :238 | L2, J4a |
| `Record.Crossing.rep`, `crossingOf_rep` | :587, :603 | B2 |
| `Diagram.record` (+ `record_comp/succ/pair_apply/sgn`, `record_componentCount`, `record_writhe`, `record_isSelfCrossing_iff`) | SM/LinkDiagramRecord.lean:500-583 | everywhere |
| `Diagram.switchRecordIso`, `switch_record` | :686, :697 | `P_join_step_left` |
| `IsRealizable` | :718 | `BlockSupply.actual` (unused by proofs) |
| `Diagram.restrictRecordIso` | :1454 | `P_split_union` |
| `Diagram.switch`, `switch_Γ`, `switch_sign_self`, `switch_sign_of_ne`, `switch_underStrand_self`, `switch_underStrand_of_ne` | SM/LinkDiagram.lean:650-694 | L2, L4 |
| `Diagram.restrict`, `restrict_componentCount`, `restrict_sign` | :1082-1088 | L3, H1 |
| `Diagram.sign`, `IsPositive`, `isPositive_iff_sign_eq_one`, `sign_eq_neg_one_iff`, `eq_over_of_mem_of_ne`, `eq_under_of_mem_of_ne`, `overVisit/underVisit`, `visit_eq_over_or_under` | :547-613, :523-527 | L2, L3, L4, B2 |
| `Diagram.switch_restrict_of_external`, `restrict_isPositive_iff` | SM/LinkDiagramExtras.lean:746, :585 | L2, H1 |
| `exists_smoothing_record_visit`, `exists_smoothing_counts` | SM/Smoothing.lean:8185, :8202 | step lemma, L2 |
| `blockRestrict`, `BlockOrdered`, `blockSet`, `SM.stack` (`StackData.stack`, `.split_union`) | SM/Stack.lean:58, :65, :70, :1350 | L3, H1 |
| `Shadow.MixedPair`, `mixedSignSum`, `SM.zero_link` (`over_constant`), `mixedPair_iff`, `isCrossing_pair_iff_of_fst_ne`, `sign_mixed_eq` | SM/ZeroLink.lean:25, :31, :1325, :1153, :1136, :1223 | L2, L3, L5 |
| `zRow`, `coeff_zRow`, `zRow_single`, `zRow_add/sub`, `zRow_eq_zero_iff`, `coeffAt`, `coeffAt_single`, `InSupportM`, `inSupportM_iff`, `InSupportM.mul_left`, `InSupportM.one`, `R.delta`, `R.a/aInv/z/zInv` | SM/LinkLaurentRing.lean:335-359, :286-299, :846-887, :966, :193, :159-165 | L1 |
| `CV.zRow_zero_mul_of_inSupportM_one`, `CV.inSupportM_one_iff`, `CV.ax_homfly.knot_parity` | CV/Axioms.lean:154, :102, :223 | L1, `homflyrows` |
| `homfly`, `homfly_descent` | SM/LinkInterfaces.lean:131, :395 | `homflyrows` |
| `LinkEquiv`, `IsOrientedSmoothing`, `IsSkeinTriple`, `IsMarkedInterval`, `IsDisc`, `Clean`, `ArcCover`, `Arc`, `OrientedSmoothingData` | SM/LinkMoves.lean:760, :743, :751, :1107, :100, :342, :208, :145, :713 | statements; §5 |
| Mathlib: `LaurentPolynomial.T_add/T_zero` (Algebra/Polynomial/Laurent.lean:164/161), `Finset.filter_eq'` (Data/Finset/Basic.lean:414), `Equiv.Set.univ` (Logic/Equiv/Set.lean:199), `Equiv.Set.union` (:226), `Equiv.sigmaSumDistrib` (Logic/Equiv/Sum.lean:339), `Equiv.sigmaUnique` (Logic/Equiv/Prod.lean:178), `Set.uniqueSingleton` (Data/Set/Insert.lean:263), `SimpleGraph.ConnectedComponent.mem_supp_iff` / `supp_injective` (Combinatorics/SimpleGraph/Connectivity/Connected.lean:568/552) | | B3, B7, assemblies |

## 2. Chain of lemmas (exact Lean statements = Skeleton_A.lean §G; skeleton line numbers in brackets)

Every statement below is in namespace `SM.Link` (sub-namespaces as shown).  "PROVED" = proved in the
skeleton from the other chain lemmas; otherwise `sorry`.

### 2.1 Laurent-row algebra (§G.1)

| # | statement | consumes | est. lines |
|---|---|---|---|
| L1a [298] | `zRow_a_mul (k : ℤ) (f : R) : zRow k (R.a * f) = aPow 1 * zRow k f` | `coeff_zRow`, `AddMonoidAlgebra.single_mul_apply_aux` (or `ext d; coeffAt` shift), `LaurentPolynomial.T` | 25 |
| L1b [302] | `zRow_aInv_mul (k : ℤ) (f : R) : zRow k (R.aInv * f) = aPow (-1) * zRow k f` | same | 20 |
| L1c [306] | `zRow_zInv_mul (k : ℤ) (f : R) : zRow k (R.zInv * f) = zRow (k + 1) f` | same | 20 |
| L1d [313] | `zRow_z_mul_eq_zero_of_inSupportM {c : ℕ} (hc : 1 ≤ c) {f : R} (hf : InSupportM (c - 1) f) : zRow (1 - (c : ℤ)) (R.z * f) = 0` | `zRow_eq_zero_iff`, `inSupportM_iff`, the `z`-shift of `coeffAt`; arithmetic `−c ≠ 2 − c + 2j` | 30 |
| L1e [319] | `zRow_delta_pow_mul (n : ℕ) (k : ℤ) (f : R) : zRow (k - n) (R.delta ^ n * f) = (aPow 1 - aPow (-1)) ^ n * zRow k f` | induction on `n`; `R.delta = (R.a - R.aInv) * R.zInv`; L1a-c, `zRow_sub`, `mul_sub`, `pow_succ` | 40 |
| L1f [328] | `InSupportM.one_mul_one {f g : R} (hf : InSupportM 1 f) (hg : InSupportM 1 g) : InSupportM 1 (f * g)` | `InSupportM.mul_left` with `hg` unfolded by `CV.inSupportM_one_iff` (`1 − 1 + 2j = 2j`) | 15 |
| PROVED | `zRow_one`, `inSupportM_one_prod`, `zRow_zero_prod_of_inSupportM_one` | `CV.zRow_zero_mul_of_inSupportM_one`, `InSupportM.one` | — |

### 2.2 Mixed crossings and the weight (§G.2)

| # | statement | consumes | est. lines |
|---|---|---|---|
| def | `Diagram.IsMixed (D) (x : D.Γ.Crossing) : Prop := (D.overStrand x).1 ≠ (D.underStrand x).1` | | — |
| L2a [371] | `Diagram.knotRestrict_switch_of_isMixed {x} (hx : D.IsMixed x) (i : Fin D.Γ.c) : (D.switch x).knotRestrict i = D.knotRestrict i` | `switch_restrict_of_external` with `B = {i}` (`¬ ∀ s ∈ x.val, s.1 ∈ {i}`: `val_eq_pair`, one of over/under strand is off `i`) | 20 |
| L2b [377] | `Diagram.exists_smoothing_of_isMixed {x} (hx : D.IsMixed x) : ∃ D₀, IsOrientedSmoothing D x D₀ ∧ D₀.componentCount + 1 = D.componentCount` | `exists_smoothing_counts`, `record_isSelfCrossing_iff` (`¬ IsSelfCrossing (overVisit x)` ⇔ `IsMixed`), `Record.componentCount_smooth`, `record_componentCount` | 25 |
| L2c [387] | `twoLambda_switch_of_isMixed (D) {x} (hx : D.IsMixed x) : twoLambda (D.switch x) = twoLambda D - 2 * (D.sign x : ℤ)` | `(D.switch x).Γ = D.Γ` (rfl); `mixedSignSum` termwise: `switch_sign_self` at the unique `(s, t)` with `{s, t} = x.val`, `switch_sign_of_ne` elsewhere; exactly one pair `i < j` (the two strand components) is hit; `Finset.sum_ite_eq`, `mixedPair_iff` | 120 |
| PROVED | `weight_switch_of_isMixed` | L1b-d, L2b, L2c, `P_recursion_pos/neg`, `P_support`, `aPow_add` | — |

### 2.3 The block-ordered case (§G.3)

| # | statement | consumes | est. lines |
|---|---|---|---|
| L3a [426] | `twoLambda_eq_zero_of_blockOrdered (D) (h : BlockOrdered D id) : twoLambda D = 0` | for `i < j`: `SM.zero_link.over_constant D i j (ne_of_lt) (Or.inr _)`: from `MixedPair i j s t`, `h x s t hs ht (i<j)` gives `underStrand = s`, so `overStrand = t` (`eq_over_of_mem_of_ne`, `s ≠ t` from `s.1 ≠ t.1`); `Finset.sum_eq_zero` | 35 |
| L3b [432] | `blockRestrict_id_eq_knotRestrict (D) (i) : blockRestrict D id Function.surjective_id i = D.knotRestrict i` | `blockRestrict_eq`, `blockSet`, `Finset.filter_eq'` (`univ.filter (· = i) = {i}`), congruence `∀ B B' hB hB', B = B' → D.restrict B hB = D.restrict B' hB'` by `subst` | 20 |
| PROVED | `lowest_of_blockOrdered` | `SM.stack.stack`, L3b, L1e, `zRow_zero_prod_of_inSupportM_one`, `P_support`, `knotRestrict_componentCount` | — |

### 2.4 Reduction by mixed switches (§G.4)

| # | statement | consumes | est. lines |
|---|---|---|---|
| def | `Diagram.badMixedCount (D) : ℕ := (univ.filter (fun x => ∃ s ∈ x.val, ∃ t ∈ x.val, s.1 < t.1 ∧ D.underStrand x ≠ s)).card` | | — |
| L4a [465] | `Diagram.blockOrdered_id_of_badMixedCount_eq_zero (h : D.badMixedCount = 0) : BlockOrdered D id` | `Finset.card_eq_zero`, `Finset.filter_eq_empty_iff`; unfold `BlockOrdered` (`blk s.1 < blk t.1` is `s.1 < t.1` for `id`) | 20 |
| L4b [470] | `Diagram.exists_badMixed (h : D.badMixedCount ≠ 0) : ∃ x, D.IsMixed x ∧ (D.switch x).badMixedCount + 1 = D.badMixedCount` | `Finset.card_pos`; the filter set of the switch is the old one with `x` erased (`switch_underStrand_self`, `switch_underStrand_of_ne`; at `x` the bad witness `(s, t)` has `underStrand x = t ≠ s`, after the switch `underStrand = s`; `IsMixed` from `s.1 < t.1`) — same shape as `badCount_switch` (PolynomialBlock:229) | 90 |
| PROVED | `lowest_value_aux : ∀ n D, D.badMixedCount = n → zRow (1 - c) (P D) = aPow (-(twoLambda D)) * (aPow 1 - aPow (-1))^(c-1) * ∏ i, zRow 0 (P (D.knotRestrict i))` | `Nat.strong_induction_on`, L4a, L4b, `weight_switch_of_isMixed`, `lowest_of_blockOrdered`, L3a, L2a | — |

### 2.5 The two-component row (§G.5)

| # | statement | consumes | est. lines |
|---|---|---|---|
| L5a [517] | `mixedSignSum_comm (D) (i j) : mixedSignSum D i j = mixedSignSum D j i` | `Finset.sum_comm`; `MixedPair i j s t ↔ MixedPair j i t s` (`Finset.pair_comm`); the two `dite` branches give the same crossing (`Subtype.ext (Finset.pair_comm s t)`) | 30 |
| L5b [521] | `twoLambda_eq_twoLinking_of_two (D) (i j) (hc : D.componentCount = 2) (hij : i ≠ j) : twoLambda D = twoLinking D i j` | `Finset.univ = {i, j}` (`Finset.eq_univ_of_card` / `Finset.card_eq_two`), `Finset.sum_pair`, `lt_or_gt_of_ne`, L5a | 50 |
| L5c [526] | `prod_univ_eq_of_componentCount_two {M} [CommMonoid M] (D) (i j) (hc) (hij) (f : Fin D.Γ.c → M) : ∏ k, f k = f i * f j` | `Finset.univ = {i, j}`, `Finset.prod_pair` | 20 |
| PROVED | `two_component_row_of_lowest` | `lowest_value_aux`, L5b, L5c | — |

### 2.6 Record level for mp:join (§G.6)

| # | statement | consumes | est. lines |
|---|---|---|---|
| def | `Record.RBasing.MarkCompatible (B : RBasing ρ) (μ : ρ.Mark) : Prop` — fields `rank_lt : ∀ c, c ≠ μ.comp → B.rank μ.comp < B.rank c`, `base_gap : ∀ g, μ.gap = some g → B.base g = ρ.succ g` | | — |
| J1 [558] | `Record.exists_markCompatible_rbasing (μ : ρ.Mark) : ∃ B : RBasing ρ, B.MarkCompatible μ` | rank `c ↦ if c = μ.comp then 0 else (Fintype.equivFin ρ.comps c).val + 1`; base `v ↦ if comp v = μ.comp then (match μ.gap with some g => succ g \| none => v) else (RBasing.default ρ).base v`; `base_const` via `Mark.gap_none` in the `none` branch, `succ_comp`, `Mark.gap_comp` | 60 |
| PROVED | `Record.Mark.map_refl (μ) : μ.map (RecordIso.refl ρ) = μ`; `Record.Mark.switchMark (μ) (x) : (ρ.switch x).Mark := ⟨μ.comp, μ.gap, μ.gap_comp, μ.gap_none⟩` (+ two `rfl` simp lemmas) | | — |
| J2a [578] | `Record.exists_joinRecord_comm (μ₁ : ρ₁.Mark) (μ₂ : ρ₂.Mark) : ∃ ι : RecordIso (joinRecord μ₁ μ₂) (joinRecord μ₂ μ₁), ∀ v, ι.Φ v = Sum.swap v` | `Φ := Equiv.sumComm`; `e : comps₁ ⊕ Unmarked₂ ≃ comps₂ ⊕ Unmarked₁` with `inl c ↦ if c = μ₁.comp then inl μ₂.comp else inr ⟨c, _⟩`, `inr ⟨c, _⟩ ↦ inl c`; `comp_eq` by `joinComp_inl/inr_of_eq/inr_of_ne`; `succ_eq`: `Sum.swap ∘ sumSucc ρ₁ ρ₂ = sumSucc ρ₂ ρ₁ ∘ Sum.swap` and `Sum.swap ∘ swap (inl g₁) (inr g₂) = swap (inl g₂) (inr g₁) ∘ Sum.swap` (`Equiv.swap_apply_apply`/`map_swap_apply` LinkRecordExtras:365); bits/signs by `Sum` cases | 80 |
| J3 [589] | `Record.exists_rUnderFirst_joinRecord (B₁ : RBasing ρ₁) (B₂ : RBasing ρ₂) (μ₁) (μ₂) (h₁ : B₁.RUnderFirst) (h₂ : B₂.RUnderFirst) (hμ₁ : B₁.MarkCompatible μ₁) (hμ₂ : B₂.MarkCompatible μ₂) : ∃ B : RBasing (joinRecord μ₁ μ₂), B.RUnderFirst` | see §3.1 | 250 |
| J2b [597] | `Record.joinRecord_switch_inl (μ₁) (μ₂) (a : ρ₁.M) : Nonempty (RecordIso ((joinRecord μ₁ μ₂).switch (Sum.inl a)) (joinRecord (μ₁.switchMark a) μ₂))` | `e := Equiv.refl`, `Φ := Equiv.refl`; `comp_eq/succ_eq/pair_eq` are `rfl` (`switch_comp/succ/pair`, `joinRecord_comp/succ`); `bit_eq`, `sgn_eq`: `Record.switch_isOver`, `switch_sgn`; `v = inl w`: `inl w ∈ {inl a, inl (τa)} ↔ w ∈ {a, τa}` (`joinRecord_pair_inl`, `Sum.inl.injEq`); `v = inr w`: not in the pair set, both sides `ρ₂.isOver w` | 45 |
| J4 [608] | `Record.exists_joinRecord_smooth_inl (μ₁) (μ₂) (a : ρ₁.M) : ∃ μ₀ : (ρ₁.smooth a).Mark, Nonempty (RecordIso ((joinRecord μ₁ μ₂).smooth (Sum.inl a)) (joinRecord μ₀ μ₂))` | see §3.2 | 500 (two units) |

### 2.7 Diagram level for mp:join (§G.7) — ALL PROVED in the skeleton

`P_join_init` (base), `P_join_step_left` (left step), `P_join_step_right` (right step via J2a),
`P_join_of_underFirst` (inner induction), `P_join_aux` (outer induction), `join_value_of_iso`; consumers:
`skein_induction_based`, `exists_underFirst_of_rUnderFirst`, `RBasing.map`, `rUnderFirst_map`,
`P_underFirst_init`, `componentCount_joinRecord`, `record_componentCount`, `switchRecordIso`,
`RecordIso.switch`, `RecordIso.smooth`, `RecordIso.joinRecord`, `Mark.map`, `exists_smoothing_record_visit`,
`solvedR_of_skein`, `P_skein`, `solvedR_mul_left`, `isPositive_iff_sign_eq_one`, `RecordIso.sgn_eq`.
`multi_component_factors` and `crossing_free_marked_component` are the same theorem (no component-count or
gap hypothesis is used anywhere; the crossing-free marked circle is the `gap = none` branch of J1/J3/J4).

### 2.8 lem:homflyrows (§G.8)

| # | statement | consumes | est. lines |
|---|---|---|---|
| H1 [781] | `P_split_union (K J D : Diagram) (h : IsSplitUnion K J D) : P D = R.delta * (P K * P J)` | `SM.stack.split_union D (fun c => if c ∈ B then 0 else 1) hsurj hno`; `hsurj` from `hB`, `hB'` (`Fin 2` cases); `hno` from the first conjunct; `blockRestrict … 0 = D.restrict B hB` and `… 1 = D.restrict Bᶜ hB'` (`blockRestrict_eq`, `Finset.filter` congruence: `(if c ∈ B then 0 else 1) = 0 ↔ c ∈ B` by `split_ifs; decide`); `presentations` along the two `RecordIso`s; `mul_assoc` | 70 |
| PROVED | `homflyrows` (all three fields) | `join_value_of_iso`, H1, `two_component_row_of_lowest`, `P_eq_homfly`, `homfly_descent`, `CV.ax_homfly.knot_parity`, `CV.zRow_zero_mul_of_inSupportM_one`, `knotRestrict_componentCount`, `ring` | — |

### 2.9 mp:blocks (§G.9)

| # | statement | consumes | est. lines |
|---|---|---|---|
| B1 [790] | `Record.writhe_eq_sum_restrictCrossings (ρ) : ρ.writhe = ∑ H : ρ.interlacementGraph.ConnectedComponent, (ρ.restrictCrossings H.supp).writhe` | `Finset.sum_fiberwise` (or `Finset.sum_comp`/`Finset.sum_partition`) along `v ↦ connectedComponentMk (crossingOf v)`; `mem_supp_iff`; `Fintype.sum_subtype`-style rewriting of `∑ v : {v // CrossKeep S v}`; `two_mul_writhe` on each block and on `ρ`, then `Int` cancellation (`mul_right_injective₀ two_ne_zero`) | 70 |
| B2 [796] | `IsCleanMarkedJoin.crossingEquiv {A B} {J} (h) : ∃ φ : A.D.Γ.Crossing ⊕ B.D.Γ.Crossing ≃ J.Γ.Crossing, (∀ x, J.sign (φ (inl x)) = A.D.sign x) ∧ (∀ y, J.sign (φ (inr y)) = B.D.sign y)` | `D.Γ.Crossing ≃ D.record.Crossing` (`x ↦ crossingOf (overVisit x)`, inverse `p ↦ p.rep.1`, `crossingOf_eq_iff`, `visit_eq_over_or_under`); `RecordIso.crossingOf_eq` induces `ρ.Crossing ≃ ρ'.Crossing`; `(joinRecord μ₁ μ₂).Crossing ≃ ρ₁.Crossing ⊕ ρ₂.Crossing` from `joinRecord_pair_inl/inr` (`{inl v, inl τv} = image of {v, τv}`); signs by `record_sgn`, `sgn_eq`, `joinRecord_sgn_inl/inr` | 180 |
| B3 [804] | `joinForest_sign {ι} (C : ι → Diagram) : ∀ S J, JoinForest C S J → ∃ φ : (Σ i : S, (C i).Γ.Crossing) ≃ J.Γ.Crossing, ∀ q, J.sign (φ q) = (C q.1).sign q.2` | `JoinForest` induction; leaf: `Set.uniqueSingleton`, `Equiv.sigmaUnique`-style; node: `Equiv.Set.union hdisj`, `Equiv.sigmaCongrLeft`, `Equiv.sigmaSumDistrib`, `Equiv.sumCongr φA φB`, B2 | 120 |
| PROVED | `joinForest_P`, `sigmaUnivEquiv`, `blocks.product/sign_preserved/writhe_additive` | `join_value_of_iso`, `Set.toFinset_union`, `Finset.prod_union`, `record_writhe`, `writhe_eq`, `presentations` | — |
| B4 [827] | `restrictCrossings_univ_iso (ρ) : Nonempty (RecordIso (ρ.restrictCrossings Set.univ) ρ)` | copy of `restrictUnivIso` (LinkRecord:1190): `Φ := Equiv.subtypeUnivEquiv (fun _ => Set.mem_univ _)`, `e := Equiv.refl`, `succ_eq` by `firstReturn_apply_of_mem` | 30 |
| B5 [835] | `exists_markedInterval (D) (μ : D.record.Mark) : ∃ I : D.Γ.Arc, IsMarkedInterval D I ∧ I.i = μ.comp ∧ ∀ v, μ.gap = some v ↔ D.IsGapOf I v` | GEOMETRIC — §5.2 | 300-500 |
| B6 [841] | `exists_cleanMarkedJoin (A B : MarkedDiagram) : ∃ J, IsCleanMarkedJoin A B J` | GEOMETRIC — §5.3 (D9's sub-obligation) | ≥ 1500 |
| B7 [848] | `Record.exists_peel (ρ) (h1 : ρ.componentCount = 1) (S : Finset ρ.interlacementGraph.ConnectedComponent) (hS : 2 ≤ S.card) : ∃ T ∈ S, ∃ (μU : (ρ.restrictCrossings (⋃ H ∈ S.erase T, H.supp)).Mark) (μT : (ρ.restrictCrossings T.supp).Mark), Nonempty (RecordIso (ρ.restrictCrossings (⋃ H ∈ S, H.supp)) (joinRecord μU μT))` | COMBINATORIAL — §5.1 | 700-900 (three units) |
| PROVED | `realizes_aux`, `realizes_of_chain` | B4-B7, `RecordIso.joinRecord`, `Mark.map`, `JoinForest.join/leaf`, `Finset.card_erase_add_one`, `Set.sdiff_union_of_subset`, `mem_supp_iff` | — |

## 3. Design notes on the two hard record lemmas

### 3.1 J3 `exists_rUnderFirst_joinRecord` (the base case, sm-3:1443-1451)

Define `RBasing.join B₁ B₂ μ₁ μ₂ : RBasing (joinRecord μ₁ μ₂)` (inside the proof):
* `rank (inl c) := B₁.rank c`, `rank (inr ⟨c, _⟩) := B₂.rank c + K` with `K := (Finset.univ.sup B₁.rank) + 1`
  (so every circle of `A`, including the joined one, ranks below every unmarked circle of `B`); injective
  because the two ranges are separated and `B₁.rank`, `B₂.rank` are injective.
* `base (inl a) := inl (B₁.base a)`; `base (inr b) := if ρ₂.comp b = μ₂.comp then (match μ₁.gap with
  | some g₁ => inl (ρ₁.succ g₁) | none => inr (B₂.base b)) else inr (B₂.base b)`.  `base_comp`: `joinComp_inl`,
  `joinComp_inr_of_eq/ne`, `succ_comp`, `Mark.gap_comp`; `base_const`: the `inl a`/`inr b` mixed case forces
  `comp a = μ₁.comp`, `comp b = μ₂.comp`, and `hμ₁.base_gap` gives `B₁.base a = ρ₁.succ g₁` (with
  `B₁.base_const` and `Mark.gap_comp`); `gap = none` with an occurrence on the marked circle is `Mark.gap_none`.
* Positions.  Let `n₁ := #{a // ρ₁.comp a = μ₁.comp}` (0 iff `μ₁.gap = none`).  Lemmas:
  (i) `joinSucc^n (inl a) = inl (ρ₁.succ^n a)` for every `n` if `comp a ≠ μ₁.comp` or `μ₂.gap = none`
  (`joinSucc_inl_of_ne`, `joinSucc_inl_of_none`); for `a` on the marked circle and both gaps present, for
  `n ≤ B₁.pos g₁` when starting from the base `ρ₁.succ g₁` (no intermediate is `inl g₁`: the iterates
  `succ^m (succ g₁)`, `m < B₁.pos g₁`, differ from `g₁` by minimality of `pos`);
  (ii) `joinSucc^(B₁.pos g₁ + 1) (inl (succ g₁)) = inr (ρ₂.succ g₂)` (`joinSucc_gap_left`), then
  `joinSucc^m (inr (succ g₂)) = inr (ρ₂.succ^m (succ g₂))` for `m ≤ B₂.pos g₂`.
  Hence `(B.join).pos (inl a) = B₁.pos a` (both `≤` by the witness and `≥` by injectivity of `inl` and
  minimality) and `(B.join).pos (inr b) = (B₁.pos g₁ + 1) + B₂.pos b` for `b` on `B`'s marked circle
  (iterates `< B₁.pos g₁ + 1` are `inl _`), `= B₂.pos b` for `b` unmarked.
* UNDER-first: for an over occurrence `inl a`, `pair = inl (τ a)`; `h₁ a` gives `key₁ (τa) < key₁ a`; if the
  ranks differ, ranks in the join are `B₁.rank` (monotone); if equal, same circle, positions equal to the
  factor positions.  For `inr b`: ranks of unmarked circles are `B₂.rank + K` (monotone); the marked circle of
  `B` has rank `B₁.rank μ₁.comp < K ≤` every unmarked rank of `B`, consistent with `hμ₂.rank_lt` (this is
  where "marked component first" is needed — without it the joined circle could outrank an unmarked circle of
  `B` whose partner occurrence lies on the marked one); equal circles: positions shifted by the same constant.
  Use `Prod.Lex.toLex_lt_toLex`, `RBasing.key`, `RBasing.pos_le`, `RBasing.pow_pos_base`.
Fallback if the `pos` bookkeeping is too heavy: state `RUnderFirst` via `visitBetween`-free "first
encounter" and prove it directly with `Nat.find` minimality lemmas (`Nat.find_min'`, `Nat.find_spec`) — the
skeleton only needs existence, so any UNDER-first based order of the join works (e.g. one could also take
the base of the joined circle at `inr (succ g₂)` if that is more convenient; both are valid).

### 3.2 J4 `exists_joinRecord_smooth_inl` (the recombination, sm-3:1458-1472)

Split into two units.

**J4a `RecordIso.ofOcc` (helper, ~120 lines, reusable by B7).**
```
def RecordIso.ofOcc {ρ ρ' : Record} (Φ : ρ.M ≃ ρ'.M) (hsucc : ∀ v, Φ (ρ.succ v) = ρ'.succ (Φ v))
    (hpair : ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v)) (hbit : ∀ v, ρ'.isOver (Φ v) = ρ.isOver v)
    (hsgn : ∀ v, ρ'.sgn (Φ v) = ρ.sgn v) (f : ρ.FreeComp ≃ ρ'.FreeComp) : RecordIso ρ ρ'
```
Components carrying occurrences are `Quotient (SameCycle succ)` (`card_comps_eq_cycleCount_add_card_freeComp`'s
equivalence, LinkRecordExtras:238, made into a `def`), transported by `Φ` (`sameCycle_map_iff` :370); free
components by `f`; `e := (nonfree ⊕ free) ≃ …`.  This removes all component bookkeeping from J4 and B7.

**J4b the mark and the occurrence bijection (~350 lines).**  Write `y := τa`, `t := ρ₁.succ g` when
`μ₁.gap = some g`.  Define `μ₀ : (ρ₁.smooth a).Mark`:
* `μ₁.gap = none`: `comp := inr ⟨μ₁.comp, free⟩` (the marked circle is a `FreeComp` of `ρ₁` and stays one),
  `gap := none`; `gap_none` since `smooth.comp v = inl _`.
* `μ₁.gap = some g`: `comp := inl ⟦t⟧` (the `reconnect`-cycle of `t = succ g`, the occurrence just after the
  interval — the interval keeps lying immediately before `t` after the recombination, also when `g ∈ {a, y}`);
  `gap := if h : ∃ n, SmoothKeep a (reconnect^n t) then some ((smoothSucc a).symm ⟨reconnect^(Nat.find h) t, _⟩)
  else none` — the retained occurrence whose smoothed successor is the first retained occurrence on the
  `reconnect`-orbit from `t`; when `g` is retained this is `g` itself (`smooth_succ_val_of_not_mem`);
  `gap_comp` by `sameCycle_firstReturn_apply`; `gap_none` by `Perm.SameCycle.exists_nat_pow_eq` (an emptied
  circle, e.g. `smooth_emptied_circle` when `succ a = y`).  The four printed cases (self/mixed × marked/unmarked,
  sm-3:1462-1472) are all instances of this one definition.
* Occurrences: `Φ : {v : M₁ ⊕ M₂ // v ∉ {inl a, inl y}} ≃ {w : M₁ // w ∉ {a, y}} ⊕ M₂` (`Equiv.subtypeSum`-style,
  `joinRecord_pair_inl`).  `hpair`, `hbit`, `hsgn`: `Sum` cases, `smooth_pair_val`, `smooth_isOver`, `smooth_sgn`.
* `hsucc` (the content): both successors are first returns of a reconnected permutation to a retained set:
  `(joinRecord μ₁ μ₂).smooth (inl a)` uses `firstReturn (joinSucc μ₁ μ₂ * swap (inl a) (inl y)) keep`, while
  `joinRecord μ₀ μ₂` uses `sumSucc (ρ₁.smooth a) ρ₂ * gapSwap μ₀.gap μ₂.gap` with `(ρ₁.smooth a).succ =
  firstReturn (ρ₁.succ * swap a y) keep₁`.  Case split: (1) `v = inr b`, `μ₂.gap ≠ some b`: both give
  `inr (ρ₂.succ b)` (`joinSucc_inr_of_ne`, `firstReturn_apply_of_mem`, `mul_swap_apply_of_ne_of_ne`);
  (2) `v = inr g₂` (the gap of `B`): LHS = first retained on the orbit `inl (succ g₁), …`; RHS = `inl (μ₀-gap's
  successor)`… — here use `joinSucc_gap_right` and the definition of `μ₀.gap`: `(smoothSucc a) (μ₀.gap) =` first
  retained iterate from `t`; the two orbits coincide (`reconnect` of the join restricted to `inl` is `inl ∘
  reconnect a`: `(joinSucc * swap (inl a) (inl y)) (inl w) = inl ((succ * swap a y) w)` for `w ≠ g₁`, by
  `joinSucc_inl_of_ne`); (3) `v = inl w`, `w ≠ g₁`, `succ w ∉ {a, y}`: both `inl (succ w)`; (4) `v = inl w`,
  `w ≠ g₁`, `succ w ∈ {a, y}`: both are the first return of `inl ∘ reconnect a` — the join's orbit stays
  inside `inl` until it meets `inl g₁` (only possible if the orbit passes through `g₁`), and if it does, the
  first retained element is reached before or at `g₁`… unless `g₁ ∈ {a, y}` — sub-case: then LHS jumps to
  `inr (succ g₂)` after `inl g₁`, and RHS: `μ₀.gap` is exactly the retained `w'` whose smoothed successor is the
  first retained iterate from `t = succ g₁`; `gapSwap μ₀.gap μ₂.gap (inl w') = inr g₂`, then `sumSucc` gives
  `inr (succ g₂)` ✓; (5) `v = inl g₁` retained (`g₁ ∉ {a, y}`): LHS `inr (succ g₂)` (`joinSucc_gap_left`), RHS
  `μ₀.gap = some g₁` so `gapSwap … (inl g₁) = inr g₂` ✓.  The general tool: `firstReturn_val_eq_of_pow`
  (Stack.lean:207), `firstReturn_pow_val_spec` (:243), `firstReturn_mul_swap_apply_left` (:276),
  `firstReturn_firstReturn` (:313) — the same toolbox that proved `restrictSmoothIso`.
* Free components: `f : ((joinRecord μ₁ μ₂).smooth (inl a)).FreeComp ≃ (joinRecord μ₀ μ₂).FreeComp` — emptied
  `reconnect`-cycles of the join (`inl ⟦inl w⟧` with no retained element ↔ emptied cycle of `ρ₁.smooth a`,
  or — when the emptied circle is the marked one — `μ₀.comp` itself, which is `inl ⟦t⟧` and NOT an `Unmarked`;
  careful: in that case `joinRecord μ₀ μ₂`'s joined circle `inl μ₀.comp` carries `B`'s marked occurrences unless
  `μ₂.gap = none` too) plus the free circles of `ρ₁` (as `inr`) and the unmarked free circles of `ρ₂`.  This is
  the fiddliest bookkeeping; if it stalls, FALLBACK: prove `∃ μ₀, Nonempty (RecordIso …)` only up to
  `componentCount` and use `lmF`-level uniqueness … NO — the statement needs a genuine `RecordIso`.  Second
  fallback: replace J4a by constructing `e` directly with `Quotient.congr` on `reconnect`-cycles as in
  `RecordIso.smooth` (LinkRecordExtras:432) and `Equiv.sumCongr`.

## 4. Unit split for parallel provers (each provable from Skeleton_A.lean alone)

| unit | lemmas | est. lines | depends on |
|---|---|---|---|
| **U-L1** | L1a, L1b, L1c, L1d, L1e, L1f | 150 | Mathlib only (`AddMonoidAlgebra`, `LaurentPolynomial`) |
| **U-L2** | L2a, L2b, L3b, L4a | 90 | accepted library |
| **U-L3** | L2c `twoLambda_switch_of_isMixed`, L3a, L5a, L5b, L5c | 250 | `Finset` sums, ZeroLink |
| **U-L4** | L4b `exists_badMixed` | 90 | pattern of `badCount_switch` |
| **U-J1** | J1, J2a, J2b | 190 | LinkRecord |
| **U-J3** | J3 `exists_rUnderFirst_joinRecord` | 250 | LinkRecord, PolynomialBlock §1 |
| **U-J4a** | `RecordIso.ofOcc` (helper; add to the skeleton above J4 when done) | 120 | LinkRecordExtras |
| **U-J4b** | J4 `exists_joinRecord_smooth_inl` | 350 | U-J4a, Stack.lean firstReturn toolbox |
| **U-H1** | H1 `P_split_union` | 70 | Stack, LinkDiagramRecord |
| **U-B1** | B1, B4 | 100 | LinkRecord |
| **U-B2** | B2 `IsCleanMarkedJoin.crossingEquiv`, B3 `joinForest_sign` | 300 | LinkRecord, Mathlib `Equiv` |
| **U-B7a** | one-gap combinatorics (§5.1 (P1)) | 350 | statement file §D (`steps`, `ArcBetween`, `Interlaces`) |
| **U-B7b** | span-minimal block + `exists_peel` assembly (§5.1 (P2)) | 200 | U-B7a, U-B7c |
| **U-B7c** | `restrictCrossings_union_joinRecord` (§5.1 (P3)) | 300 | U-J4a |
| **U-B5** | `exists_markedInterval` (GEOMETRIC, §5.2) | 300-500 | LinkMoves discs |
| **U-B6** | `exists_cleanMarkedJoin` (GEOMETRIC, §5.3) | ≥ 1500 | out of this panel |

Critical path for mp:join = U-J4b (after U-J4a); everything else in mp:join is short.  mp:lowest and
lem:homflyrows are fully independent of the join units except `homflyrows.connected_sum` (needs
`join_value`).  mp:blocks `writhe_additive`/`sign_preserved` need only U-B1/U-B2; `product` and `realizes` wait
on U-B5/U-B6/U-B7.

## 5. The realization clause (`BlocksData.realizes`) — analysis only (D9 sub-obligation)

### 5.0 What exactly is needed

`realizes : ∀ ρ C, BlockSupply ρ C → ∃ J, JoinForest C Set.univ J ∧ Nonempty (RecordIso J.record ρ)`.  The
skeleton's `realizes_aux` (compiles) reduces it, by strong induction on `S.card`, to three lemmas:
* B7 `Record.exists_peel` — pure record combinatorics (§5.1);
* B5 `exists_markedInterval` — geometric, small (§5.2);
* B6 `exists_cleanMarkedJoin` — geometric, large (§5.3);
* B4 `restrictCrossings_univ_iso` — trivial.
The induction peels one block `T` off `S` at a time (`S = (S.erase T) ∪ {T}`), joins the inductively built
`J_U` (record `restrictCrossings (⋃ S∖T)`) with the supplied `C T`, transports the two record marks to the
diagrams along the record isomorphisms (`Mark.map`, `RecordIso.joinRecord`), makes them `MarkedDiagram`s by
B5, and realizes the join by B6.  NOTE (matches NOTES_FINAL risk 8): the forest's marks are the ones produced
by the combinatorics, not the printed "successively smaller intervals"; `JoinForest` allows any marks, so the
printed clause is met.

### 5.1 B7 — the combinatorics (sm-3:1637-1663), record level, ~800 lines in three units

Fix `ρ` with one circle.  Write `occ S := {v // crossingOf v ∈ S}` for a crossing set `S`.

**(P1) One-gap lemma (U-B7a, ~350 lines).**  For blocks `A ≠ B` of `ρ.interlacementGraph`, all occurrences of
`B` lie in one cyclic gap of `A`:
```
theorem Record.exists_gap_of_ne (ρ) (h1 : ρ.componentCount = 1) (A B : ρ.interlacementGraph.ConnectedComponent)
    (hAB : A ≠ B) : ∃ g : ρ.M, ρ.crossingOf g ∈ A.supp ∧
      ∀ w, ρ.crossingOf w ∈ B.supp → ∀ n, 0 < n → n ≤ ρ.steps g w → ρ.crossingOf ((ρ.succ ^ n) g) ∉ A.supp
```
("`g` is an `A`-occurrence and no `A`-occurrence lies strictly after `g` up to and including any `B`-occurrence",
i.e. all of `B` is in the forward gap of `A` starting at `g`).  Proof: (a) a chord `b ∉ A` not interlacing any
chord of `A` has both ends in one gap of `A`: by `Interlaces` (statement file §D) with `x ∈ A`: `¬ Xor
(ArcBetween v w τv) (ArcBetween v τw τv)` — both ends of `b` are on the same side of every chord of `A`;
connectivity of `A` (induction on `SimpleGraph.Walk`/`Reachable` between chords of `A`) shows all `A`-ends are on
one side of `b`, i.e. `b`'s ends are in one gap of `A`.  (b) two interlacing chords `b, b'` outside `A` share the
gap (distinct gaps are disjoint arcs, alternation impossible).  (c) induction along a walk in `B`.  The cyclic
arithmetic is on `steps` (a `Nat.find`), which needs a toolbox: `steps_succ_pow`, `steps_lt_card`, "`w` is on the
circle ⇒ `succ^(steps g w) g = w`", `ArcBetween` transitivity/trichotomy on one circle (~120 lines of it).  The
one-circle hypothesis makes every `steps` total (`succ_cycle`).

**(P2) Consecutive block (U-B7b, ~200 lines).**  Cut the circle at a base occurrence `v₀`; linear order by
`steps v₀ ·`.  Span of a block `T` := `steps v₀ (last T) − steps v₀ (first T)`.  A span-minimal `T ∈ S` has no
other block of `S` inside its span (else that block, lying in one gap of `T` by (P1), would be inside an internal
gap and have strictly smaller span), so every other block lies in the outer gap of `T` (the one containing `v₀`),
i.e. `T` is cyclically consecutive among the `S`-occurrences.  Output: `T ∈ S`, `g_U :=` the last
`(S∖T)`-occurrence before `first T`, `g_T := last T`, with the gap property of (P3).

**(P3) Union restriction = join (U-B7c, ~300 lines).**
```
theorem Record.restrictCrossings_union_joinRecord (ρ) (h1 : ρ.componentCount = 1) (U T : Set ρ.Crossing)
    (hUT : Disjoint U T) (hU : ∃ x, x ∈ U) (hT : ∃ x, x ∈ T) (g : ρ.M) (hg : ρ.crossingOf g ∈ U)
    (hgap : ∀ w, ρ.crossingOf w ∈ T → ∀ n, 0 < n → n ≤ ρ.steps g w → ρ.crossingOf ((ρ.succ ^ n) g) ∉ U) :
    ∃ (μU : (ρ.restrictCrossings U).Mark) (μT : (ρ.restrictCrossings T).Mark),
      Nonempty (RecordIso (ρ.restrictCrossings (U ∪ T)) (joinRecord μU μT))
```
`μU := ⟨comp g, some ⟨g, hg⟩, …⟩`, `μT := ⟨comp g, some ⟨g_T, _⟩, …⟩` with `g_T` the last `T`-occurrence in the
gap (the `T`-occurrence whose `firstReturn`-successor within `T` is the first `T`-occurrence after `g`).
Occurrences `occ (U ∪ T) ≃ occ U ⊕ occ T` (disjointness).  Successor: for `u ∈ U`, `u ≠ g`: the next
`(U∪T)`-occurrence after `u` is the next `U`-occurrence (no `T` in between — `T` sits in the gap after `g`);
`g ↦ inr (first T)` = `joinSucc_gap_left`; `t ∈ T`, `t ≠ g_T ↦` next `T`-occurrence; `g_T ↦ inl (next U after g)`
= `joinSucc_gap_right`.  All by `firstReturn` characterisations (`firstReturn_val_eq_of_pow`, Stack.lean:207,
`firstReturn_pow_val_spec` :243).  Components: one circle everywhere; `Unmarked μT` is empty
(`Fintype.card_subtype_compl`), so `e : ρ.comps ≃ ρ.comps ⊕ Unmarked μT` is `Equiv.sumEmpty`-like; with
`RecordIso.ofOcc` (J4a) nothing else is needed.

`exists_peel` := (P2) + (P3) + `⋃ H ∈ S, H.supp = (⋃ H ∈ S.erase T, H.supp) ∪ T.supp` (`Finset.set_biUnion_insert`
on `insert T (S.erase T) = S`) + pairwise disjointness of `supp` (`SimpleGraph.ConnectedComponent.supp_injective`
/ `mem_supp_iff`) + nonemptiness of `supp` (each component is `connectedComponentMk x`, `x ∈ supp`).

Feasibility: HIGH (pure finite combinatorics on `succ`/`pair`, same toolbox as Stack.lean §6.3); cost ~800
lines; risk: the `steps`-based cyclic-order toolbox is new (the accepted layer measures cyclic order on
diagrams by `visitCoord`/`cycBetween`, not on abstract records) — fallback: work on the one-circle record
through `Perm.SameCycle`/`zpow` exponents modulo `card M` (`Equiv.Perm.IsCycle`-style) or, since
`BlockSupply.actual` gives an actual `D₀` with record `ρ`, transport the graph to `D₀` and use the accepted
diagram-level cyclic order (`Diagram.VisitBetween`, `visitBetween_ent_iff`, LinkDiagramRecord:882-974) — B's
route; the statement of `exists_peel` is unchanged.

### 5.2 B5 — a printed marked interval at a record gap (GEOMETRIC, small)

`IsMarkedInterval D I := (∀ v, ¬ I.Mem (visitPt v)) ∧ ∃ U, IsDisc U ∧ Clean U D ∧ D.Γ.ArcCover U {I}`
(LinkMoves:1107; `Clean`:342 = frontier injectivity + every component leaves `U`; `ArcCover`:208 = the trace of
`D` in `U` is exactly the given arcs).  Construction: on the circle `μ.comp`, take the open parameter interval
between the traversal parameter of `μ.gap` and that of `D.nextVisit g` (or the whole circle minus one point if
`gap = none`); pick a point `p` in the interior of an edge strictly inside it and away from every crossing
point; the polygonal trace is a finite union of segments, so `p` has positive distance to every other segment
and to every vertex; a closed ball `U` of radius below that distance and below the edge's clearance meets `D`
exactly in a sub-segment through `p` (`IsDisc` by `isDisc_closedBall`:104).  `I` := that sub-segment (an `Arc`
with `start ≠ stop` inside one edge); `Clean`: frontier meets the edge in two points (convexity of the ball and
of the segment), every component exits (`U` is small); `IsGapOf`: no occurrence of the circle lies between `g`
and `I.start` by the choice of the parameter interval (`nextVisit_no_between`, LinkDiagramRecord:335).  The
accepted layer has the disc predicates but NO existence lemma of a clean disc around an interior edge point
(grep: only `isDisc_closedBall`, `Clean.*` transport lemmas); Smoothing.lean §1 ("The clearance radius `r₁`",
:679-790) computes exactly such a clearance around a crossing point and can be adapted to an edge point.
Estimate 300-500 lines.  Feasible.

### 5.3 B6 — existence of a clean marked join (GEOMETRIC, large; D9's tracked sub-obligation)

Needed: for `A B : MarkedDiagram` an actual polygonal `J` with `RecordIso J.record (joinRecord A.μ B.μ)`.
Printed construction (sm-3:1387-1425): (1) change of chart so that `I_A` is adjacent to the unbounded face
(sphere trick), (2) a simple polygonal path from beside `I_A` to outside a rectangle containing `A` in the
unbounded face, thickened to a thin ribbon, (3) extend the two cut ends of `I_A` along the ribbon to the
exterior, (4) shrink the rectangle affinely into the clean disc of `I_B` and match the ends to the collars of
`I_B`.  Step (1) is NOT available in the accepted layer (no sphere chart, no inversion-type map on `Diagram`;
`PlanarIsotopic` = `Deform`/`Reparam`, LinkMoves:516, is a plane isotopy) and steps (2)-(3) need a face/path
argument (connectedness of the complement of a compact polygonal set in the plane) that exists nowhere in
work/lean.  What the accepted layer DOES have that is reusable: (i) `OrientedSmoothingData` (LinkMoves:713) and
the whole Smoothing.lean construction (`SpliceModel`, `mixedModel` :4975, `selfModel` :5632, `toDiagram` :3626,
the genericity/clean-disc/outside-match proofs §6, and the record bridge `recordIsoOfCoord` §8) — this is a
worked example of "cut two arcs inside a disc, reconnect their ends crosswise, get a `Diagram` whose record is a
prescribed record operation", i.e. exactly the LOCAL half of a marked join; (ii) `Diagram.pullback`/`StrandMap`
(LinkDiagram:752-966) for re-indexing components, `restrict` for dropping components.
A record-first route that avoids the sphere trick: realise `joinRecord μA μB` as an ORIENTED SMOOTHING of a
mixed crossing of a diagram `D'` obtained by placing an affinely shrunken copy of `A` inside the clean disc of
`I_B` and letting the shrunken `I_A` cross `I_B` once transversally: then `D'.record ≅ (joinRecord-like record
with one extra mixed crossing between the two marked circles)`, and its smoothing at that crossing has record
`joinRecord μA μB` — provided the copy of `A` (all of it, not just `I_A`) is placed inside the disc of `I_B`.
That requires: (α) an affine image of a `Diagram` is a `Diagram` with the same record (`StrandMap` with an affine
map: `pullback`-style, ~300 lines; orientation preserving so signs are kept), (β) disjoint union of two diagrams
with disjoint traces is a `Diagram` with record the disjoint-union record (~300 lines; the Shadow is `Fin (c₁+c₂)`
indexed), (γ) a single transverse crossing between two edges inside a clean disc, i.e. move the shrunken `I_A`
until it crosses `I_B` exactly once (~400 lines: choose the affine map so that the image of `I_A` is a short
segment crossing `I_B`'s segment transversally, everything else of the image far from `I_B`'s segment — needs
the shrunken copy to fit in a small ball around the crossing point except for … no: the copy of `A` is compact
and can be shrunk into a ball around a point of `I_B` off the segment; then `I_A` must be dragged to `I_B` —
this reintroduces a path/ribbon argument unless the copy is placed so that the image of `I_A` itself contains
the crossing point, i.e. shrink `A` into a ball centred on a point of `I_B`, which puts ALL of `A` on both sides
of `I_B`'s segment, creating many crossings).  So the honest estimate stands at ≥ 1500 lines, consistent with
NOTES_FINAL risk 6, and the shape of the argument (a path in a face + ribbon) has no precedent in work/lean.
Recommendation: keep `exists_cleanMarkedJoin` as the one tracked geometric `sorry` of the block; `product` and
`realizes` are provable the moment it lands; everything else in the four rows is independent of it.

### 5.4 Fidelity record for `realizes`

The skeleton proves `realizes` from B4-B7 (assembly `realizes_aux` compiles), so the only open geometric
content of the whole block is B5 + B6.  `BlockSupply.actual` is not used by any proof (as predicted by the
judge); it would be used by the B-route fallback for (P1) in §5.1.

## 6. Risks and fallbacks

| risk | where | mitigation |
|---|---|---|
| **R-J4** the recombination iso J4 is large (500 lines) and the free-component matching is intricate | mp:join step | J4a helper `RecordIso.ofOcc`; the definition of `μ₀` is uniform (first retained iterate from `succ g`); Stack.lean's `firstReturn` toolbox (:207-396) already handles first returns of `mul_swap` permutations; fallback: construct `e` with `Quotient.congr` as in `RecordIso.smooth` |
| **R-J3** position bookkeeping of the join basing | mp:join base | only existence of an UNDER-first basing is needed; base the joined circle at `inl (succ g₁)`; `pos` lemmas via `Nat.find_min'`/`Nat.find_spec`; fallback base at `inr (succ g₂)` (symmetric) |
| **R-MC** `MarkCompatible.rank_lt` ("marked circle first") is stronger than the join basing needs for `A`, but needed for `B` (§3.1); the skeleton's inductions supply it for both through J1 and the transports (already compiled), so no statement change is needed | — | none |
| **R-L1** Laurent-row shifts (`AddMonoidAlgebra.single_mul_apply_aux` for `ℤ × ℤ`) | mp:lowest | alternatively prove by `ext d` + `coeff_zRow` + `Finsupp` support reasoning as in `CV.zRow_zero_single_mul_single` (CV/Axioms.lean:139) |
| **R-L2c** `twoLambda_switch` double-sum surgery (120 lines) | mp:lowest | model on `Record.sum_sgn_switch` (LinkRecord:740); the unique hit pair is `(overStrand x, underStrand x)` or its swap (`mixedPair_iff`, `isCrossing_pair_iff_of_fst_ne`) |
| **R-B2** crossing bijections `Γ.Crossing ≃ record.Crossing` | mp:blocks sign | `crossingOf_eq_iff`, `visit_eq_over_or_under`, `Crossing.rep`; 180 lines of `Equiv` plumbing, no mathematics |
| **R-B7** `steps`-based cyclic order toolbox is new | mp:blocks realizes | fallback via `BlockSupply.actual` and the accepted diagram-level `VisitBetween` (§5.1) |
| **R-B6** geometric existence of clean joins (≥ 1500 lines, no precedent) | mp:blocks realizes/product | tracked D9 sub-obligation; keep as the single geometric `sorry`; all other clauses of all four rows are independent |
| **R-def** `blockRestrict D id _ i` vs `knotRestrict` uses `Finset.filter_eq'` + `restrict` congruence along a finset equation with a dependent proof | mp:lowest | `subst`-lemma `∀ B B' hB hB', B = B' → D.restrict B hB = D.restrict B' hB'` |

## 7. What the skeleton proves outright (no `sorry`), for the record

`aPow_add`, `aPow_zero`, `aPow_neg_mul_aPow`, `zRow_one`, `inSupportM_one_prod`,
`zRow_zero_prod_of_inSupportM_one`, `Diagram.componentCount_switch`, `weight_switch_of_isMixed`,
`lowest_of_blockOrdered`, `lowest_value_aux`, `two_component_row_of_lowest`, `Record.Mark.map_refl`,
`Record.Mark.switchMark` (+ simp lemmas), `optionMap_eq_self`, `P_join_init`, `P_join_step_left`,
`P_join_step_right`, `P_join_of_underFirst`, `P_join_aux`, `join_value_of_iso`, `joinForest_P`,
`sigmaUnivEquiv`, `realizes_aux`, `realizes_of_chain`, and the four row theorems `SM.join` (all three fields),
`SM.lowest` (both), `SM.blocks` (all four — `realizes`/`product` through B5-B7), `SM.homflyrows` (all three).
