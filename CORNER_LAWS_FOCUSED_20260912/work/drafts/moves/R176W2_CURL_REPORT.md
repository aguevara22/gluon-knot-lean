# R176W2_CURL_REPORT — unit CURL: `r176s_curl_removal` PROVED (record-level R-I)

CURL prover (subagent), 2026-09-15 22:34–23:00 UTC / 6:34–7:00pm ET.  File: `work/drafts/moves/R176W2_CURL.lean`
= `R176_Port_draft.lean` (6339 lines, byte-identical prefix) + the appended section `R176C_Curl` (lines 6337–6706,
inside `namespace RProof` / `noncomputable section`, before the final `end`).  Compile: `cd work/lean && lake env lean
../drafts/moves/R176W2_CURL.lean` → **exit 0, 0 errors, 26 s**; the only warning is the pre-existing LEDGER
`unusedSectionVars` note at `r176l_selectedPart_eq` (line 5154); **no warning from the appendix**.  `grep -c sorry`:
before **1**, after **1** — the single hit is the assembler's header comment on line 1 (the word "sorry" in prose); no
`sorry` term anywhere, before or after.  Nothing under `work/lean` written; no `lake build`; no `import`, `set_option`
or global `attribute` added (`open Classical` is section-local).  Scratch files (the iteration copies and the
`#print axioms` copy) live in the session scratchpad only.

## 0. Result

| item | result |
|---|---|
| **`r176c_curl_removal_proof : r176s_curl_removal`** (line 6672) | **PROVED** — the frozen Prop, untouched, applied to its binders |
| general form `r176c_curl_removal_general` (line 6586) | `∀ ρ, ρ.componentCount = 1 → ∀ K w (hw : ρ.CrossKeep K w), ((ρ.restrictCrossings K).succ ⟨w, hw⟩).1 = ρ.pair w → ∀ X X', X.record ≅ ρ|K → X'.record ≅ ρ|(K ∖ {ρ.crossingOf w}) → P X = P X'` — no `r ∈ K` binder (it is `hw`), conclusion in `P` (= `homfly` by `P_eq_homfly`) |
| the row | **`r176c_extreme_transport_of_outer_mixed (hout : r176_outer_carriers_L) (hmixed : r176_mixed_bridge) : RowShape @ExtremeTransportData`** (line 6701) — the composition with `hcurl` discharged; the row is now open in exactly the two remaining Props (#2, #3 of R176_ASSEMBLY_REPORT §5) |
| `r176c_homfly_of_liftBlock_curl` (line 6681) | the kinked exact owner map `r176s_homfly_of_liftBlock_curl` with `hcurl` discharged |
| `#print axioms` (scratch copy) | `r176c_isRealizable_block_of_union`, `r176c_exists_blockSupply`, `r176c_restrictRestrictIso`: `[propext, Classical.choice, Quot.sound]`; `r176c_P_eq_one_of_iso_single`, `r176c_curl_removal_general`: standard + `SM.lp_lm`; `r176c_curl_removal_proof`, `r176c_homfly_of_liftBlock_curl`: standard + `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` (the `P_eq_homfly` footprint); `r176c_extreme_transport_of_outer_mixed`: standard + the six registered axioms of `CV.carrierSlotFloor` (`SM.lit_homfly, lit_homfly_descent, lp_lm, lp_lm_uniqueness, ng_finite_word, src_contact`) — **no `sorryAx`** anywhere |
| size | 370 lines appended, 14 declarations, all `r176c_`-prefixed; no frozen declaration edited; no other unit's Prop touched |
| black boxes added | **none** (no new `sorry` Prop was needed) |

## 1. Why the "obvious" route needed one more library fact

`SM.blocks.product` (`product_of_blockSupply`) needs a `BlockSupply σ C`: an actual diagram per interlacement block of
`σ = ρ|K`.  The frozen Prop supplies only `X ≅ ρ|K` and `X' ≅ ρ|(K∖{r})` — no diagram for any single block, and in
particular none for the kink block `{r̂}` (an actual one-crossing one-circle diagram is nowhere constructed in the
library).  Geometric R-I (`SM.LinkMoves.RIData`/`RI`, `P_reidemeister_I`) needs a disc and arcs — not available from a
record.  The missing fact is **realizability of every block of a realizable one-circle record**, which the library's
mp:blocks realization chain proves implicitly but never states: `exists_joinForest_of_realizable` (MarkedProducts:4705)
splits a realizable block-union `S` by `restrictCrossings_join_decomp` and gets both halves realizable by
`isRealizable_restrictCrossings_of_gapContiguous`, but at a single block it uses the supplied leaf.  §C1 runs the same
strong induction down to single blocks without leaves.  With it, a `BlockSupply` for `σ` exists by choice — including
the kink block, whose diagram is then a one-circle one-crossing diagram by the record isomorphism (`P = 1` by
lc:single-crossing).  So the frozen Prop is TRUE and PROVED as stated; rule (3) was not needed.

## 2. The appended declarations (all PROVED)

| § | declaration (line) | statement | proof |
|---|---|---|---|
| C1 | `r176c_isRealizable_block_of_union` (6363) | one-circle `ρ`, `S` a union of blocks, `IsRealizable (ρ|S)` ⇒ every block `H ⊆ S` has `IsRealizable (ρ|H.supp)` | strong induction on the number of blocks in `S` (the `hlt` count of `exists_joinForest_of_realizable`); ≥ 2 blocks: `restrictCrossings_join_decomp` + `isRealizable_restrictCrossings_of_gapContiguous`, `H` lies in the part it meets; 1 block: `S = H.supp` |
| C1 | `r176c_exists_blockSupply` (6445) | realizable one-circle `ρ` with `Nonempty ρ.M` ⇒ `∃ C, BlockSupply ρ C` | §C1 at `S = univ` through `restrictCrossings_univ_iso`; `C H := Classical.choose` |
| C2 | `r176c_not_adj_of_succ_eq_pair` (6464) | `ρ.succ v = ρ.pair v` ⇒ `crossingOf v` is isolated in `interlacementGraph` | `adj_iff_alternates` at `v`; `steps v (pair v) = 1` (`steps_eq_iff`), so neither `ArcBetween v _ (pair v)` holds; `omega` |
| C2 | `r176c_supp_eq_singleton_of_succ_eq_pair` (6479) | its block has `supp = {crossingOf v}` | `ConnectedComponent.exact` + `Walk` cases |
| C3 | `r176c_crossingOf_restrict_eq_iff` (6496) | on `ρ|K`: `crossingOf m = crossingOf ⟨w,hw⟩ ↔ ρ.crossingOf m.1 = ρ.crossingOf w` | `crossingOf_eq_iff`, `mem_val_iff`, `Subtype.ext` |
| C3 | `r176c_crossKeep_restrict_iff` (6512) | `(ρ|K).CrossKeep {x ≠ r̂} m ↔ ρ.CrossKeep (K ∖ {r}) m.1` | from the previous |
| C3 | `r176c_restrictRestrictEquiv` (6522), `_val` | the occurrence bijection `((ρ|K)|{x ≠ r̂}).M ≃ (ρ|(K∖{r})).M`, value-preserving (`rfl`) | `Equiv.subtypeEquivRight` + `Equiv.subtypeSubtypeEquivSubtype` |
| C3 | **`r176c_restrictRestrictIso`** (6535) | `RecordIso ((ρ|K)|{x ≠ r̂}) (ρ|(K ∖ {r}))` | `succ_eq` by `firstReturn_congr_pred` (predicate read on `ρ`) + `restrictCrossings_firstReturn_val`; the other fields `rfl` |
| C4 | `r176c_P_eq_one_of_iso_single` (6558) | `D.record ≅ σ|{crossingOf v}` (σ one-circle) ⇒ `P D = 1` | `Γ.c = 1` from `componentCount_eq`; `card Crossing = 1` from `record_crossingCount`, `crossingCount_eq` and `card {m // CrossKeep {r̂} m} = 2` (`= {v, pair v}`); `single_crossing.one_crossing` |
| C4 | **`r176c_curl_removal_general`** (6586) | see §0 | `product_of_blockSupply` for `X`, `Finset.mul_prod_erase` at the kink block, `P(C_{r̂}) = 1`; `S₁ := {x ≠ r̂}` is a block-union (`block_eq_of_mem_supp`); if `S₁` nonempty: `exists_joinForest_of_realizable` (its realizability from `X'` via §C3), `presentations`, `joinForest_P`, `{H | H.supp ⊆ S₁}.toFinset = univ.erase H_r`; else every block is `H_r`, both sides `1` (`X'` crossing-free: `record_card_M`, `card_M_eq`, `single_crossing.crossing_free`) |
| C4 | **`r176c_curl_removal_proof`** (6672) | `r176s_curl_removal` | `subst`, `P_eq_homfly`, the general form |
| C4 | `r176c_homfly_of_liftBlock_curl` (6681), **`r176c_extreme_transport_of_outer_mixed`** (6701) | the SMOOTH owner map and the row composition with `hcurl` discharged | one-line applications |

Reassessment rule: no lemma took two failed attempts; the whole unit compiled on the third scratch iteration (the
three fixes were a `push_neg` shape, an anonymous-constructor type ascription needed for `DecidablePred` synthesis on
`(ρ.restrictCrossings K).M`, and `m.1` vs `m` in the `restrictCrossings_firstReturn_val` call).

## 3. Generalisation (rows 174 and 110)

`r176c_curl_removal_general` is the record-level R-I in the most general form the frozen Prop allows: any one-circle
record `ρ`, any crossing set `K`, any occurrence `w` retained by `K` whose `ρ|K`-successor is its partner; the removed
crossing is `ρ.crossingOf w` (the Prop's `r ∈ K` binder is redundant and dropped).  Rows 174/110 apply it with their
own `K` and kink; if a consumer has the kink as `r` with `crossingOf w = r`, `subst` first (as in
`r176c_curl_removal_proof`).  Two by-products are general library material with no row data: **`r176c_exists_blockSupply`**
(a `BlockSupply` for ANY realizable one-circle record with a crossing — the hypothesis every mp:blocks consumer has had to
build geometrically, e.g. `CV.GroupedKnot.blockSupply`) and **`r176c_restrictRestrictIso`** (restriction of a
restriction, with the removed crossing a single kink; the same construction works verbatim for `{x | x ∈ S}` in place of
`{x ≠ r̂}` — only `r176c_crossKeep_restrict_iff` changes).

## 4. What the composition needs changed

Nothing in any statement.  At assembly, replace `r176_extreme_transport_of_curl_outer_mixed hcurl hout hmixed` by
`r176c_extreme_transport_of_outer_mixed hout hmixed`, i.e. `RProof.extreme_transport :=
r176c_extreme_transport_of_outer_mixed <outer> <mixed>` once #2 and #3 are proved.  `r176s_curl_removal` stays as a
`def … : Prop` (frozen) with `r176c_curl_removal_proof` as its proof; at port time the two can be merged into one theorem.

## 5. Port notes

* §C1 (`r176c_isRealizable_block_of_union`, `r176c_exists_blockSupply`) → `SM/MarkedProducts.lean` next to
  `exists_joinForest_of_realizable` (it is that theorem's induction without leaves; a cleaner port makes the existing
  theorem call it).  §C2 → the `Record.adj_iff_alternates` neighbourhood.  §C3 → next to `restrictCrossings_firstReturn_val`.
  §C4 → `SM/BigonDeletion.lean` §5 beside `curl_block_value` (which this supersedes for consumers with no supply).
* Deprecation-clean: uses `Set.mem_ofPred_eq`, `Set.mem_sdiff`, `Set.sdiff_subset`; no `push_neg`.
* The `open Classical` is needed for `Set.toFinset` in `joinForest_P` and `Finset.filter`; it is section-local.
