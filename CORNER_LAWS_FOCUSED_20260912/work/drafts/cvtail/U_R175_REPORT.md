# U-175 REPORT — leaf `cvt_pair_row_zero_of_singleton` (row 175 `pair_row_zero` from row 165)

Prover unit U-175 (prefix `cvt175_`), 2026-09-15 ≈16:00 UTC / 12:00pm ET.
File: `work/drafts/cvtail/U_R175.lean` (byte-identical copy of `Statements_FINAL.lean` + the two
additions below; `diff Statements_FINAL.lean U_R175.lean` shows nothing else).

## Result

* **PROVED**: `RProof.cvt_pair_row_zero_of_singleton (h165 : CV.SingletonDiData) (hn) (E) (e f g) (δ)
  (hPar : ParityData E e f g δ) : ∀ t ht hef heg hfg, EmptyLocal … → ∀ Q ∈ outsideSupports …, FullAvail … →
  ∀ J ⊆ triangleCrossings …, J.card = 2 → rowTerm hn (genericAt E t ht.1) (Q ∪ J) = 0` — statement
  untouched, `sorry` body replaced by a 21-line proof.  Consequently `extreme_pair_zero_of_singleton :
  RowShape @ExtremePairZeroData` (already assembled in the FINAL) is now fully proved from `h165`, and the
  fixed-name row `RProof.extreme_pair_zero` depends only on `CV.singleton_D_i` (rows 165 ← U-SPLIT + row 99 (C)).
* **Helper added** (immediately before the leaf, same section `namespace RProof`, after `cvt_exists_owner`):
  `RProof.cvt175_exists_third (hef heg hfg) {J} (hJ2 : J.card = 2) : ∃ z ∈ triangleCrossings P e f g, z ∉ J`
  — `P1.triangleCrossings_card` (`|T| = 3`) + `Finset.exists_mem_notMem_of_card_lt_card`.  It does NOT need
  `J ⊆ T` (the pigeonhole works for any two-element `J`), so that hypothesis was dropped to avoid an
  unused-variable lint.
* **Interface Props stated**: none — the leaf needed no move / diagram identification (RA-free, as PLAN §3
  FR-R-174..177 says: 175's `pair_row_zero` is the only field of 174–177 whose proof needs no 155 (C)).
* **Unproved / left**: nothing of this unit.  The other 9 `sorry`s in the file are untouched black boxes:
  placeholders `SM.cf_thm_carrierfloor` (:160), `SM.thm_C_S7` (:194), `SM.thm_C_soft` (:198),
  `SM.cor_C_inherits` (:968); leaves `CV.carrier_slot_floor_of_C` (U-SLOT, :600), `CV.cvt_singleton_split`
  (U-SPLIT, :693); fixed-name rows `RProof.generic_selected` (:738), `extreme_transport` (:821),
  `extreme_selected` (:834).

## Compile

`cd work/lean && lake env lean ../drafts/cvtail/U_R175.lean` → exit 0, **0 errors**, exactly 9
"declaration uses `sorry`" warnings (the lines above), ~20 s wall clock.
`grep -c sorry`: 11 before → 10 after (the count includes the docstring mention at line 33; `sorry`
BODIES 10 → 9).
Axioms (checked on a scratch copy of the leaf with the same imports and the FINAL's copies of
`SingletonPieceOn`/`SingletonDiData`/`cvt_exists_owner`):
`cvt_pair_row_zero_of_singleton` : `[propext, Classical.choice, Quot.sound, lit_homfly]` (standard + the
authorised `SM.lit_homfly`, no `sorryAx`; `lit_homfly` enters through the accepted `PRE_175_*`/X1 layer, not
through anything new); `cvt175_exists_third` : `[propext, Classical.choice, Quot.sound]`.

## Proof route (exactly PLAN §4 175)

1. `hS : Q ∪ J ∈ Ind` from the accepted `PRE_175_pair_present_on_empty` (X1Rows.lean:1548).
2. `rowTerm_of_mem_Ind hn (genericAt E t ht.1) hS` (X1Rows.lean:168): `rowTerm = wind * ∏ q, Omega1 q`.
3. `by_cases hw : wind = 0`.  Zero: `zero_mul`.  Nonzero: `(CV.wind_ne_zero_imp _ _ hw).2 : ∀ q,
   CarrierUniform …` (CV/Carriers.lean:485 — packages `Finset.prod_eq_zero` + `weight_ne_zero_iff` :468, so
   neither had to be invoked by hand).
4. Third crossing `z ∈ T`, `z ∉ J` by `cvt175_exists_third`; `PRE_175_third_singleton_piece hPar …`
   (X1Rows.lean:1566) gives `hzU : z ∈ U (Q ∪ J)` and `pieceLabels (pieceOf z hzU) = {z}`.
5. Owner `q` with `pieceOf z hzU ∈ piecesOn q` by the FINAL's PROVED `cvt_exists_owner` (needs `hS`).
6. `⟨hzU, hlab, hq⟩ : CV.SingletonPieceOn … (Q ∪ J) q z`; `h165.factor_zero hn (genericAt …) hS q (huni q) z _`
   gives `Omega1 … q = 0`; `Finset.prod_eq_zero (Finset.mem_univ q) hΩ`, `mul_zero`.

## Pitfalls / notes for the assembler and executor

* `geomAt E t ht` is a `theorem` (Prop-valued: `CrossingGeometry P : Prop`, SM/CrossingGeometry.lean:11) equal
  by definition to `(genericAt E t ht).crossingGeometry`; since both are proofs of a Prop, every
  `GeoComponent (geomAt …) S` / `Ind (geomAt …)` / `CarrierUniform (geomAt …)` unifies with the
  `hG.crossingGeometry` form of `SingletonDiData` by proof irrelevance — no casts, no `show`, no `convert`.
* `triangleCrossings_card` is `RProof.P1.triangleCrossings_card` (namespace `P1`, RProof/Cores.lean:1245),
  not `RProof.triangleCrossings_card` — the PLAN's citation omits the namespace.
* Mathlib (this pin): the pigeonhole lemma is `Finset.exists_mem_notMem_of_card_lt_card` (renamed from
  `exists_mem_not_mem_of_card_lt_card`); the hypothesis is `#s < #t`, proved by `omega` from the two cards.
* `CV.wind_ne_zero_imp` already exists (Carriers.lean:485) and returns both `∀ q, weight q ≠ 0` and
  `∀ q, CarrierUniform q`; the PLAN's `Finset.prod_ne_zero_iff` + `weight_ne_zero_iff` route is subsumed.
* `h165.factor_zero` needs `hS : S ∈ Ind hG.crossingGeometry` explicitly (the `SingletonDiData` binders); the
  same `hS` from step 1 serves for `rowTerm_of_mem_Ind`, `cvt_exists_owner` and `factor_zero`.
* No statement, name, docstring or definition was changed; no file under work/lean was written; the
  scratch copy lives in the session scratchpad only.
* Port-readiness: the leaf + helper + `cvt_exists_owner` + `extreme_pair_zero_of_singleton` form a ~60-line
  block that can be ported to `RProof/X1Rows*.lean` (or a new `RProof/ExtremePairZero.lean`) as soon as
  `CV.SingletonDiData`/`SingletonPieceOn` (row 165's module) are ported; `RProof.extreme_pair_zero` itself
  becomes a theorem the moment `CV.singleton_D_i` is (no-`sorry` rule).
