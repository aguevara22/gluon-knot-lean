# U_SGC_REPORT — unit U103-C (helper unit, prefix `sgc_`), 2026-09-15

File: `work/drafts/corner/U_SGC.lean` (byte-identical copy of `Statements_FINAL.lean` plus one inserted block,
lines 217-286, immediately before the docstring of `sg_daughters_products`, the first leaf that consumes these
helpers; `diff Statements_FINAL.lean U_SGC.lean` = `216a217,286`, pure insertion, no frozen statement touched).
Check: `cd work/lean && lake env lean ../drafts/corner/U_SGC.lean`: **0 errors**, 14 `declaration uses sorry` warnings =
exactly the other units' leaves and the §6 row theorems (lines 208, 293, 313, 528, 546, 561, 569, 690, 700, 711,
806, 811, 816, 821); 13.7 s warm. `grep -c sorry`: 16 before, 16 after (this unit owns no leaf; the 16 = 14
declarations + 2 mentions in comments).

## Content (PLAN_FINAL §3.1 item 3(b), §4 row U103-C): "blockPoly determined by labels across S ⊆ S'; blockPoly {c} = 1"

All six helpers PROVED (no sorry, no new axioms):

| helper | statement | route |
|---|---|---|
| `sgc_isBlockCarrierDiagram_of_subset` | `S ⊆ S'`, `pieceLabels S H = pieceLabels S' H'`, `IsBlockCarrierDiagram hS' H' D` ⇒ `IsBlockCarrierDiagram hS H D` | unfold: the witness `T ⊇ S' ⊇ S` and `carrierCrossings T q = labels` transfer verbatim |
| `sgc_blockRecord_iso_of_labels_eq` | same hypotheses ⇒ `Nonempty (RecordIso (blockRecord hS H) (blockRecord hS' H'))` | `block_diagram` at `S'`, `polynomial_independent` (.1) on both sides, `ι.symm.trans κ` |
| `sgc_blockPoly_eq_of_labels_eq` | same hypotheses ⇒ `blockPoly hS H = blockPoly hS' H'` — the `blockPoly_eq_of_labels_eq` promised at CBBlocks.lean:105 | `block_diagram` at `S'` gives `D`; `polynomial_independent` (.2) at `S'` and (via the first helper) at `S` both pin `SM.P D` |
| `sgc_P_positiveLift_eq_one_of_count_one` | `carrierCrossingCount T q = 1` ⇒ `SM.P (positiveLift hn hP T q hT) = 1` | `card_carrierShadow_crossing` (LinkPositiveLift.lean, via `carrierCrossingEquiv` :799) + `Fintype.card_eq_one_iff` give the unique crossing; `single_crossing.one_crossing` (SingleCrossing.lean:152-165) with `D.Γ.c = 1` by `rfl` (`positiveLift_componentCount`) |
| `sgc_blockPoly_eq_one_of_card_one` | `(pieceLabels S H).card = 1` ⇒ `blockPoly hS H = 1` | `exists_blockCarrier` (CBProducts.lean:1740) + `polynomial_independent` (.2) + previous helper (`carrierCrossingCount` unfolds to `(carrierCrossings …).card` by `show`) |
| `sgc_blockPoly_eq_one_of_labels_eq_singleton` | `pieceLabels S H = {c}` ⇒ `blockPoly hS H = 1` — the printed "`P_{\{c\}} = 1`" | `Finset.card_singleton` |

Sizes: ~70 lines total (the plan budgeted 250 / 3 h; the accepted `polynomial_independent` already carries the whole
"independent of the further smoothings" content, so the before/after split is a two-line argument).

## Axioms (`#print axioms` on the scratch copy, same statements)

```
'SM.sgc_isBlockCarrierDiagram_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'SM.sgc_blockRecord_iso_of_labels_eq' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lp_lm]
'SM.sgc_blockPoly_eq_of_labels_eq' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lp_lm]
'SM.sgc_P_positiveLift_eq_one_of_count_one' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lp_lm]
'SM.sgc_blockPoly_eq_one_of_card_one' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lp_lm]
'SM.sgc_blockPoly_eq_one_of_labels_eq_singleton' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lp_lm]
```
i.e. standard + `SM.lp_lm` (through `SM.P` / `cb_products` / `single_crossing`) — no `SM.lit_homfly`, `SM.lp_lm_uniqueness`
needed here; the row assembly's expected list [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm,
SM.lp_lm_uniqueness] is unaffected.

## For the assembler / U103-D (the consumer)

- Namespaces: the frozen file opens only `Link Carrier`, so the helpers name `CB.cg`, `CB.blockPoly`, `CB.blockRecord`,
  `CB.IsBlockCarrierDiagram`, `CB.exists_blockCarrier` explicitly (namespace `SM.CB`); `cb_products`, `single_crossing`,
  `positiveLift`, `card_carrierShadow_crossing` resolve as is.
- U103-D's use: for `S' = insert c S` take `hSS' := Finset.subset_insert c S`; the label equality is U103-B's
  label-preservation of `Piece (insert c S) ≃ {H : Piece S // labels ≠ {c}}`, in either direction (`hlab.symm`). The
  block of `c` at `S` (labels `{c}`, by U103-A/B: `c` is isolated in `G_P[U(S)]`) contributes the factor `1` via
  `sgc_blockPoly_eq_one_of_labels_eq_singleton`; the count identity `m_A = m₁ + m₂ + 1` needs no polynomial input
  (`cb_products.count` + `Finset.card_singleton` on the same block).
- `sgc_P_positiveLift_eq_one_of_count_one` is a general library fact (lc:single-crossing on any carrier with one
  self-crossing), reusable by thm:C-S7's one-newborn rows (U110-J) if a carrier value `1` at `m = 1` is ever needed.
- Nothing believed false; no missing hypothesis; no Mathlib pitfalls hit (`Fintype.card_eq_one_iff` has the shape
  `∃ x, ∀ y, y = x`, exactly `single_crossing.one_crossing`'s hypothesis; the `Fintype` instance on
  `(positiveLift …).Γ.Crossing` unifies with the carrier shadow's by `positiveLift_Γ : … = … := rfl`).
- U110-G GO/NO-GO: not this unit's content (no RI/RII witnesses touched).

## Left

Nothing of this unit. Not touched (other units): `sg_isolated_undominated` (U103-A), `sg_daughters_products` (U103-D),
`sg_daughters_rotation` (U103-E), the `s7_*` and `sft_*` leaves, the §6 row theorems.
