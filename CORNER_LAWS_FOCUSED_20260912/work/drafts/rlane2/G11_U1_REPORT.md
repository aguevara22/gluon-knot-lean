# G11_U1_REPORT — unit U1 (A-carrier: carrier edges and the R-LOC-2 adjacency)

Written 2026-09-14 by the U1 prover (G11 wave, row 173 R:generic_transport). File:
`work/drafts/rlane2/G11_U1.lean` (1339 lines; the skeleton was 1086). Plan of record: `G11_PLAN.md` §3 unit A
and §7 row **U1**.

## Result

**All 7 leaves of U1 are PROVED.** Nothing else in the file was touched: `diff G11_Skeleton.lean G11_U1.lean`
removes exactly the seven `  sorry` lines and adds 260 lines (7 proof bodies + 5 helpers with docstrings).
No statement, name, docstring or definition changed; no other unit's `sorry` touched; `G11_two_crossings_absurd`
(X2) untouched.

Compile: `cd work/lean && lake env lean ../drafts/rlane2/G11_U1.lean` — exit 0, **0 errors**, ~10 s.
Warnings: 42 × `declaration uses sorry` (= 49 − 7, the other units' leaves) plus two linter notes, see §Pitfalls (2).
`grep -c sorry`: 50 → 43 (the remaining 43 = 42 leaf bodies + the word "sorry" in the header docstring, line 7).

Axioms (checked on a copy of the file with `#print axioms`): every U1 leaf and every helper depends only on
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `SM.lit_*` / `SM.lp_*` axioms.

| leaf | line | proof size | what it uses |
|---|---|---|---|
| `G11_carrierEdge_spec` (A2) | 553 | 4 lines + helper `gu1_carrierEdge_block` (27) | `geo_mark_block` (choose_spec), `GeoBlockInterior.visit_edge`, `geoCornerPolygon_edge_smul`, `geoMarkPosition_evaluation_visit`, `isTrueCorner_geoCornerMark` |
| `G11_carrierEdge_eq_of_adjacent` (A3) | 650 | 7 lines + helpers `gu1_markSuccessor_eq_of_adjacent` (55), `gu1_carrierEdge_eq_of_lt` (26) | `geoMarkSuccessor_position_cases`, `geoMarkSuccessor_no_mark_between`, `traversalKey_lt_iff`, `zmod_val_add_one_of_lt`, `zmod_add_one_eq_zero_of_val`, `geoSmoothingSuccessor_visit_of_not_mem`, `geo_block_mark_eq`, `geometricVisitPosition_injective` |
| `G11_carrierEdge_isCrossing` (A4) | 693 | 6 lines + helper `gu1_carrierEdge_remote` (24) | A2, `geo_consecutive_meet`, `geo_carrier_selfIntersection_not_corner` (clause 4), `visitTwin_edge_ne` |
| `G11_carrierEdge_crossingPoint` (A4') | 704 | 9 lines | A2, `gu1_carrierEdge_remote`, `geoCornerPolygon_transverse`, `transverse_segments_unique`, `crossingPoint_mem` |
| `G11_carrierSign` (A6) | 721 | 4 lines | A2, `ccp_det_smul_smul`, `sign_mul`, `sign_pos` |
| `G11_no_visit_between` (A7) | 763 | 50 lines + helper `gu1_visit_eq_of_mem` (20) | `ExactTriangleVisitOrders` (both clauses), `visit_eq_or_twin`, `crossing_card_two`, `Finset.eq_of_subset_of_card_le` |
| `G11_param_ne` (F0) | 1126 | 15 lines | `crossingParameter_spec`, `crossingPoint_injective_of_geometry`, `crossing_card_two`, `Finset.pair_eq_singleton` |

Leaves left in U1: **none**.

## Helpers added (all `gu1_`-prefixed, each immediately before the leaf that uses it, statements only new)

* `gu1_carrierEdge_block` (L525, before A2): unpacks the `Classical.choose` of `G11_carrierEdge`: `∃ r, 1 ≤ r ∧
  ρ_T^r c_k = Sum.inr v ∧ GeoBlockInterior k r ∧ (geoOutSlot c_k).1 = v.2.val ∧ crossingPoint v.1 ∈ edgeSegment X k`.
  `r ≥ 1` because `r = 0` would make the unselected visit `v` a true corner. **U2/U6 may find this useful** (it is
  the one place where the `choose` is opened; everything else in U1 goes through it).
* `gu1_markSuccessor_eq_of_adjacent` (L567, before A3, `include hn in`): for `v, w` on one edge with `t_v < t_w` and
  no visit strictly between, `geoMarkSuccessor hP (Sum.inr v) = Sum.inr w`. Proof: `geoMarkSuccessor_position_cases`
  (same edge further on, or the next vertex) + `geoMarkSuccessor_no_mark_between`; the "next vertex" branch needs the
  wrap-around case split `e.val + 1 < n` vs `e.val + 1 = n` (then `e + 1 = 0` and the third disjunct of
  `traversalBetween` applies).
* `gu1_carrierEdge_eq_of_lt` (L623, before A3): the ordered A3; extends the block of `v` by one `ρ_T`-step
  (`GeoBlockInterior k (r+1)`) and closes with `geo_block_mark_eq`.
* `gu1_carrierEdge_remote` (L668, before A4): `¬ adjacent (ce v) (ce (visitTwin v))` — the three adjacency cases as
  in the library's `geo_carrierCrossing_edges` (equal ⇒ both visits on one original edge; consecutive ⇒ the double
  point is a corner point, excluded by `geo_carrier_selfIntersection_not_corner`).
* `gu1_visit_eq_of_mem` (L740, before A7, `omit [NeZero n] in`): a visit `y` on `e` with `g ∈ y.1.val` (`e ≠ g`,
  `IsCrossing P {e,g}`) IS the visit `⟨xPair hceg, ⟨e, _⟩⟩` — by `card = 2` its support is `{e, g}`, and the twin is on `g`.

## Truth / statement findings

* Every leaf is true as stated; no missing hypothesis. A7 in particular needs no `hcfg` and no `¬ IsAlternating`:
  `ExactTriangleVisitOrders` alone gives it (pairs `(a,y)`, `(y,b)` carried since their unions are not `{e,f,g}`
  unless `y ∈ {a, b}`; pair `(a,b)` reversed; `<`-transitivity contradicts). Both orientations (`a < y < b` and
  `b < y < a`) are handled by applying `hX` with the arguments in the order matching each inequality — no
  injectivity of `visitTransport` needed.
* `G11_param_ne` does not need `e ≠ f`/`e ≠ g`: `{e,f} = {e,g}` with `f = e` contradicts `crossing_card_two`.
* `G11_carrierEdge_crossingPoint`'s `hc` argument is never needed as data beyond `xPair hc` (the point is pinned by
  `transverse_segments_unique` with `det ≠ 0` from `geoCornerPolygon_transverse`).

## Pitfalls (Lean / library)

1. **Dependent `rw` on the `Classical.choose` term.** `rw [geoMarkPosition_evaluation_visit] at hmem` fails with
   "motive is not type correct" because the `choose` term's *type* mentions `traversalEvaluation P (geoMarkPosition
   (Sum.inr v))`. Rewrite the goal in the other direction instead (`rw [← geoMarkPosition_evaluation_visit hG.cg v]`)
   after `unfold G11_carrierEdge`. Anyone opening the `choose` (U2's `G11_cfg_*` should not need to — use
   `gu1_carrierEdge_block` / `G11_carrierEdge_spec`) will hit the same thing.
2. **Two linter warnings from the frozen statements**: `G11_no_visit_between` (L763) and `G11_param_ne` (L1126)
   auto-include the top-level `[NeZero n]`, which neither `ExactTriangleVisitOrders` (checked: its signature has no
   `NeZero`) nor `crossingParameter` needs; a `sorry` body masked this in the skeleton. Silencing it needs
   `omit [NeZero n] in` before each theorem — a signature-level edit I did NOT make (rule 1, statements frozen).
   **Assembler**: add the two `omit`s if a warning-free file is wanted; callers are unaffected (instance argument).
3. `GeoBlockInterior.visit_edge` returns `w.2.val = (geoOutSlot …).1` (visit on the left); `geoCornerPolygon_edge_smul`
   wants the slot edge — orient with `.symm`.
4. `adjacent i j` is `j - i = -1 ∨ j - i = 0 ∨ j - i = 1` (note the order: the second index minus the first);
   `linear_combination ±h` converts to `j = i ± 1` in `ZMod k` as in the library's `geo_carrierCrossing_edges`.
5. `rcases h : e with …` does not substitute in other hypotheses; use `obtain ⟨b, hb⟩ : ∃ b, e = b := ⟨_, rfl⟩;
   rw [hb] at …; cases b` to case on `geoMarkSuccessor hP (Sum.inr v)`.
6. `sign_mul` here is `Mathlib.Data.Sign.Basic.sign_mul` (the `SignType.sign` one), found by name resolution over
   the `Int.sign_mul` of core since the argument is real; `sign_pos (mul_pos hc₁ hc₂)` then `one_mul`.
7. Section variables: helpers whose statements do not mention `hn` need `include hn in` (Lean 4 inclusion rule),
   otherwise `geoMarkSuccessor_position_cases hn …` has no `hn`.

## For the assembler / U2 / U6

* U2's `G11_cfg_hmp/hmq/hpq/order/trans` can be built exactly as the plan says from the five U1 lemmas; the useful
  extra facts exposed by `gu1_carrierEdge_block` are `(geoOutSlot c_k).1 = v.2.val` and the block index `r ≥ 1`.
* For `G11_cfg_order` (U2): `G11_carrierEdge_spec` gives `edge X m = c • edge P e` and `X m = edgePoint P e t₀`
  is available through `geo_evaluation_eq_outSlot`/`geoCornerPolygon_apply` + `gu1_carrierEdge_block`'s slot equality
  (`X m = traversalEvaluation P (geoMarkPosition hG.cg c_m)`, `c_m`'s out-slot edge is `e`).
* Nothing under `work/lean` was written. Scratch files live in `/tmp/gu1/` (T1.lean = the standalone development,
  U1_axioms.lean = the axiom audit copy).
