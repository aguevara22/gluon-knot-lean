# U_SGB_REPORT — unit U103-B (prefix `sgb_`), helper unit: `Piece (insert c S) ≃ {H : Piece S // pieceLabels H ≠ {c}}`

Prover subagent, 2026-09-15 ~15:50Z / 11:50am ET. File: `work/drafts/corner/U_SGB.lean` (copy of
`Statements_FINAL.lean` with ONE pure insertion: `diff Statements_FINAL.lean U_SGB.lean` = `216a217,559`, the
343-line `sgb_` block placed in section `Singleton` immediately after the leaf `sg_isolated_undominated` and
immediately before the docstring of `sg_daughters_products`, the first leaf that consumes it — rule (2)). No
statement, name, docstring or definition of the frozen file was touched; no other unit's `sorry` was touched.

Check: `cd work/lean && lake env lean ../drafts/corner/U_SGB.lean` — **0 errors**, 15 s warm; exactly 14
`declaration uses sorry` warnings = the 10 unit leaves of PLAN_FINAL §4 (incl. `sg_isolated_undominated`, U103-A's, left
as the black box it is in this copy) + the 4 §6 row theorems; NO other warning (unused-section-variable linter satisfied
with one `omit [NeZero n] in`). `grep -c sorry`: 16 before → 16 after (helper unit: no leaf of its own).
`#print axioms` (scratch copy) of `sgb_pieceEquiv`, `sgb_pieceEquiv_labels`, `sgb_pieceLabels_pieceOf`,
`sgb_univ_pieces_eq`, `sgb_pieceOf_mem_blocksOwnedBy`, `sgb_prod_insert_map` = `[propext, Classical.choice, Quot.sound]`.

## Proved (all helpers of this unit; nothing left)

The content of PLAN_FINAL §3.1 (3a) / §4 U103-B — the label-preserving equivalence — is
```
def sgb_pieceEquiv (hn) (hP) (hcU : c ∈ supportUnselected hn hP S)
    (hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c) :
    CV.Piece (CB.cg hn hP) (insert c S) ≃ {H : CV.Piece (CB.cg hn hP) S // CV.pieceLabels (CB.cg hn hP) S H ≠ {c}}
theorem sgb_pieceEquiv_labels … (H') :
    CV.pieceLabels (CB.cg hn hP) S (sgb_pieceEquiv hn hP hcU hiso H').1 = CV.pieceLabels (CB.cg hn hP) (insert c S) H'
```
Hypotheses = "`c` isolated in `G_P[U(S)]`": `c ∈ U(S)` (conjunct 1 of `sg_isolated_undominated`) and no undominated
label interlaces `c` (from conjunct 2 + the printed `hiso`, via `sgb_not_interlaces_of_isolated`). Neither `hS` nor
`hS'` is needed. Primary route of the PLAN (Mathlib `ConnectedComponent` / `induce`); the §6.5 fallback (mp:blocks on
the record of `D_A`) was NOT needed.

Generic graph part (section `SgbGraph`; `G : SimpleGraph V`, `s t : Set V`, `c`, hypotheses `hc : ∀ x ∈ s, ¬ G.Adj x c`,
`hcs : c ∈ s`, `ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c` — `t = s ∖ {c}` given membership-wise, which AVOIDS any transport
across an equality of vertex sets):
- `sgb_not_reachable_of_isolated` — an isolated vertex of `G[s]` reaches no other vertex (one `cases` on the walk).
- `sgb_reachable_descend` — a walk of `G[s]` between vertices `≠ c` never visits `c`, so reachability descends to
  `G[t]` (walk induction; the only "real" argument of the unit, 15 lines).
- `sgb_compMap` (`ConnectedComponent.map` of Mathlib's `G.induceHomOfLE`), `sgb_compMap_mk` (`rfl`),
  `sgb_compMap_injective`, `sgb_mem_range_compMap_iff` (range = components `≠ mk ⟨c, hcs⟩`).
- `sgb_compEquiv : (G.induce t).ConnectedComponent ≃ {C // C ≠ (G.induce s).connectedComponentMk ⟨c, hcs⟩}`
  (`Equiv.ofInjective` + `Equiv.subtypeEquivRight`), `sgb_compEquiv_apply_val` (`rfl`), `sgb_compEquiv_mem_iff`
  (vertex-by-vertex membership: the label-preservation statement at graph level).

SM part (section `SgbPieces`, `variable (hn) {P} (hP) {S} {c}`):
- `sgb_not_interlaces_of_isolated A hiso hint : ∀ x ∈ U(S), ¬ Interlaces x c` — glue from U103-A's conjunct 2.
- `sgb_mem_unselected_insert_iff hiso x : x ∈ U(insert c S) ↔ x ∈ U(S) ∧ x ≠ c` (`greedy_step` + `hiso`; needs no
  `[NeZero n]`, hence the `omit`).
- `sgb_mem_U hcU : c ∈ (↑(CV.U (cg hn hP) S) : Set _)`, `sgb_mem_U_insert_iff`, `sgb_adj_isolated` — the three
  hypotheses of the generic part at `G = geometricInterlacementGraph (cg hn hP)`, `s = ↑(CV.U … S)`,
  `t = ↑(CV.U … (insert c S))` (bridge `CV.U_eq_generic hn hP`; `Adj` is `Interlaces` by rfl).
- `sgb_pieceLabels_pieceOf : pieceLabels S (pieceOf S c _) = {c}` — the block `{c}` (what U103-C's `blockPoly {c} = 1`
  takes as its piece); `sgb_pieceLabels_eq_singleton_iff : pieceLabels S H = {c} ↔ H = pieceOf S c _`;
  `sgb_pieceLabels_pieceOf_ne` (labels of the block of `x ≠ c` are not `{c}`).
- `sgb_pieceEquiv`, `sgb_pieceEquiv_pieceOf` (`(e (pieceOf S' x hx)).1 = pieceOf S x _`, `rfl`),
  `sgb_pieceEquiv_symm_pieceOf` (`e.symm ⟨pieceOf S x hx, _⟩ = pieceOf S' x _` for `x ≠ c`), `sgb_pieceEquiv_labels`.
- Finset-level conveniences for U103-D: `sgb_pieceEmbedding : Piece S' ↪ Piece S` (= `Subtype.val ∘ e`),
  `sgb_pieceEmbedding_apply` (`rfl`), `sgb_pieceLabels_pieceEmbedding`, `sgb_mem_range_pieceEmbedding_iff`
  (`(∃ H', emb H' = H) ↔ pieceLabels S H ≠ {c}`), `sgb_univ_pieces_eq`
  (`univ = insert (pieceOf S c _) (univ.map emb)`), `sgb_pieceOf_notMem_map`, `sgb_prod_insert_map` /
  `sgb_sum_insert_map` (`∏ H ∈ insert (pieceOf c) (T.map emb), f H = f (pieceOf c) * ∏ H' ∈ T, f (emb H')`, any
  `T : Finset (Piece S')` — the shape `blocksOwnedBy S A` takes after the split), `sgb_pieceOf_mem_blocksOwnedBy`
  (the block `{c}` is owned by `A`, from `hc : c ∈ carrierCrossings A` via `mem_carrierCrossings` /
  `mem_blocksOwnedBy_iff`), `sgb_pieceEmbedding_mem_blocksOwnedBy_iff` (membership of an image block in
  `blocksOwnedBy S A`, read on the labels of the source block).

Consumption check (scratch copy of the file + an `example`, compiled): from the leaf's hypotheses
`hS A hc hiso`, `obtain ⟨hcU, hint, -⟩ := sg_isolated_undominated hn hP hS A hc hiso`,
`hiso' := sgb_not_interlaces_of_isolated hn hP A hiso hint`, then `greedy_independent hn hP hS hcU`,
`sgb_pieceEquiv hn hP hcU hiso'`, `sgb_pieceEquiv_labels hn hP hcU hiso'` typecheck directly.

## Unproved
- nothing in this unit.

## Notes for the assembler / executor / U103-C / U103-D
- Size: 343 lines against the 450 estimate; ~1.5 h against 6 h. The Mathlib bookkeeping was light because `t` is
  given by a membership iff (`ht`) rather than as `s \ {c}`: no `Iso.induce`/`setCongr` transport, and all
  application lemmas (`sgb_compMap_mk`, `sgb_compEquiv_apply_val`, `sgb_pieceEquiv_pieceOf`, `sgb_pieceEmbedding_apply`)
  are `rfl` — `ConnectedComponent.map_mk`, `induceHomOfLE_apply`, `Set.inclusion`, `Equiv.ofInjective_apply`,
  `Equiv.subtypeEquivRight_apply` are all definitional.
- Naming: `CV.Piece hP S` is an `abbrev` for `(residualGraph hP S).ConnectedComponent` and `residualGraph` an `abbrev`
  for `(geometricInterlacementGraph hP).induce ↑(CV.U hP S)`, so the generic `sgb_compEquiv` unifies with the
  `Piece` types without any `show`; `CV.pieceOf` is a `def` (unfolds under `exact`/`unfold CV.pieceOf`, which the SM
  lemmas do once each).
- For U103-C: the piece whose labels are `{c}` is `CV.pieceOf (CB.cg hn hP) S c (sgb_mem_U hn hP hcU)`
  (`sgb_pieceLabels_pieceOf`); a block of `S` with labels `≠ {c}` is `sgb_pieceEmbedding hn hP hcU hiso H'` for a unique
  `H' : Piece S'` with the SAME labels (`sgb_mem_range_pieceEmbedding_iff`, `sgb_pieceLabels_pieceEmbedding`) — the
  "equal labels across `S ⊆ S'`" input of `blockPoly_eq_of_labels_eq`.
- For U103-D: the owner side is untouched here (needs `hown`). The natural route: show
  `blocksOwnedBy S A = insert (pieceOf S c _) ((blocksOwnedBy S' Λ₁ ∪ blocksOwnedBy S' Λ₂).map emb)` via
  `sgb_pieceOf_mem_blocksOwnedBy`, `sgb_pieceEmbedding_mem_blocksOwnedBy_iff`, `sgb_mem_range_pieceEmbedding_iff`,
  `mem_blocksOwnedBy_iff` at `S'`, `one_owner` at `S'` (a block has ONE owner, so "`∀ labels, owner S' = Λ₁ ∨ = Λ₂`"
  splits into "owned by `Λ₁`" or "owned by `Λ₂`"), and `hown`; then `sgb_prod_insert_map` + `Finset.prod_union`
  (disjointness from `Λ₁ ≠ Λ₂`) give `P_A = P_{c} · P₁ · P₂` with `P_{c} = 1` (U103-C), and `sgb_sum_insert_map` gives
  `m_A = 1 + m₁ + m₂` (`Finset.card_singleton` on `sgb_pieceLabels_pieceOf`).
- Hypothesis shape: everything takes `hcU : c ∈ supportUnselected hn hP S` and
  `hiso : ∀ x ∈ supportUnselected hn hP S, ¬ Interlaces hn hP x c` (NOT the carrier-level `hiso` of the leaves; convert
  with `sgb_not_interlaces_of_isolated`). Proof-irrelevance makes the `sgb_mem_U hn hP hcU` argument of `pieceOf`
  interchangeable with any other proof of `c ∈ CV.U (cg hn hP) S`.
- Mathlib pitfalls: `rw` with an `↔` whose LHS is `… = {c}` does not fire under `≠` (it is `¬(… = {c})`, no syntactic
  `Eq` at the head) — use `intro h; (iff).mp h`. `CV.U_eq_generic` needs `hn hP` explicit in `rw`. `induction p` on a
  `Walk` with hypotheses depending on the endpoints: `revert` them first (done in `sgb_reachable_descend`). Outside
  `namespace SM`'s `attribute [local instance] Classical.propDecidable`, `insert c S` on `Finset (Crossing P)` needs a
  `DecidableEq` — consumers writing scratch tests must sit inside the namespace/section as the file does.
- Not applicable to this unit: no leaf believed false, no missing hypothesis; U110-G's GO/NO-GO on the RI/RII
  witnesses is that unit's report.
