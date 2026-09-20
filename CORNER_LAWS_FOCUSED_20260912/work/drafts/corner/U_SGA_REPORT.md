# U_SGA_REPORT — unit U103-A (prefix `sg_`), leaf `sg_isolated_undominated`

Prover subagent, 2026-09-15 ~16:10Z / 12:10pm ET. File: `work/drafts/corner/U_SGA.lean` (byte-identical copy of
`Statements_FINAL.lean` except for the body of the one leaf below; `diff Statements_FINAL.lean U_SGA.lean` shows only
line 215 `sorry` → 43 proof lines).

Check: `cd work/lean && lake env lean ../drafts/corner/U_SGA.lean` — **0 errors**, 17 s warm; 13 `declaration uses
sorry` warnings = the 9 other-unit leaves (`sg_daughters_products`, `sg_daughters_rotation`, `s7_sliding_law_at`,
`s7_bigon_law_at`, `s7_universal_extraction`, `s7_corner_product`, `sft_same_sign`, `sft_mixed`, `sft_loop`) + the 4 §6
row theorems (`cb_singleton`, `corner_values`, `thm_C_S7`, `thm_C_soft`). `grep -c sorry`: 16 before → 15 after (the
count includes the header comment's mention of `sorry`).
`#print axioms SM.sg_isolated_undominated` = `[propext, Classical.choice, Quot.sound]` (standard only).

## Proved
- `sg_isolated_undominated` (U103-A; the whole unit). No statement, name, docstring or definition changed.

## Helpers added
- none. The route of PLAN_FINAL §3.1 item 1 closes with accepted lemmas alone (43 lines, well under the 300 estimate),
  so no `sg_` helper was needed.

## Unproved
- nothing in this unit.

## Route actually used (accepted declarations, grep-verified)
Conjunct 1, `c ∈ U(S)`: `Carrier.mem_carrierCrossings` (CarrierCrossings.lean:74) gives `c ∉ S` and "both visits owned
by `A`"; `mem_supportUnselected` (InterlaceSupports.lean:69) reduces to `c ∉ N(S)`; contrapositive of
`Carrier.neighbor_visit_owners_ne` (CarrierNeighborSeparation.lean:197; lem:carriers (iii) first half), with the visit
`⟨c, i⟩` from `crossing_visits_exist` (CrossingPair.lean:9) and its `visitTwin` (CarrierVisitTwin.lean:34,
`(visitTwin v).1 = v.1` is `rfl`).
Conjunct 2, `x ∈ U(S) ∧ Interlaces x c → x ∈ carrierCrossings A`: `Interlaces` (Interlacement.lean:16) unfolds to
`x ≠ c ∧ ∃ x₀ x₁ c₀ c₁, … ∧ crossingVisitBetween x x₀ x₁ c c₀ ∧ crossingVisitBetween x x₁ x₀ c c₁`, and
`crossingVisitBetween … = traversalBetween (crossingVisitPosition …) …` with `crossingVisitPosition hn hP.1 x x₀ =
visitPosition hn hP.1 ⟨x, x₀⟩` DEFINITIONALLY (CrossingPair.lean:47) — so the two alternation facts are literally the
`h123`/`h341` hypotheses of `Carrier.carriers_noncrossing_owner_eq` (CarrierNoncrossing.lean:426, the owner-equality
form of lem:carriers (iv); NO distinctness side conditions needed). Its `h13` is
`Carrier.unselected_nonneighbor_both_visits_one_carrier` (CarrierCrossings.lean:337) at `x ∈ U(S)`; its `h24` is the
two owners of `c` (both `A`). Then `Carrier.unselected_nonneighbor_mem_carrierCrossings` (:349) puts `x` in the crossings
of `owner ⟨x, x₀⟩ = owner ⟨c, c₀⟩ = A`.
Conjunct 3, `U(insert c S) = U(S).erase c`: `greedy_step hn hP S c` (CBProducts.lean:1917; explicit args `hn hP T c`),
then `Finset.mem_sdiff/mem_erase/mem_insert`, `mem_supportNeighbors` (:56); the only content is `y ∈ U(S) → Interlaces y c
→ False` for `y ≠ c`: conjunct 2 puts `y ∈ carrierCrossings A`, `hiso y _ hyc` forbids `Interlaces c y`, and
`interlaces_symm` (Interlacement.lean:26) flips `Interlaces y c`.

## Notes for the assembler / executor
- `IsDecomposition hn hP S` is by definition `S ∈ independentSupports hn hP` (DecompositionDefinition.lean:15), so `hS`
  is passed directly wherever the Carrier lane asks for `S ∈ independentSupports`; no conversion lemma.
- `greedy_independent hS hcU` (CBProducts.lean:1911) is available at once from conjunct 1 for whoever needs
  `IsDecomposition hn hP (insert c S)` (U103-D builds `hS'` this way). `greedy_step` (:1917) takes NO independence
  hypothesis.
- The `hiso` hypothesis is used ONLY in conjunct 3 (through conjunct 2); conjuncts 1 and 2 hold for every self-crossing
  `c` of every carrier of every decomposition. If a later unit wants those two facts without `hiso`, they can be
  re-proved verbatim (each is ≤ 12 lines) — I did not add separate helpers, to keep the file byte-identical outside the
  leaf body per rule (2).
- `Visit P` is an `abbrev` for `Σ c : Crossing P, {i // i ∈ c.val}` (GaussVisits.lean:17); anonymous constructors
  `⟨c, i⟩ : Visit P` and `rfl : (⟨c, i⟩ : Visit P).1 = c` work everywhere.
- Mathlib pitfalls: none hit. Deliberately avoided `simp only` on the `∃ x ∈ {c}, …` membership (normal form of
  `exists_eq_left` vs. `Finset.mem_singleton` is fragile) — the three `rw`s + `rintro (h | ⟨x, hx, hyx⟩)` are stable.
- Not applicable to this unit: no leaf believed false, no missing hypothesis; U110-G's GO/NO-GO on the RI/RII witnesses
  is that unit's report.
