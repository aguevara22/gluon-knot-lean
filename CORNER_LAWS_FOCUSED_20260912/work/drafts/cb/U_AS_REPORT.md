# U_AS_REPORT — unit AS (assembly leaves) of PLAN_FINAL §4

Prover, 2026-09-14. File: `work/drafts/cb/U_AS.lean` (copy of Skeleton_FINAL.lean; diff against the skeleton is
exactly the two leaf bodies below — no statement, name, definition or docstring changed).
Compile: `cd work/lean && lake env lean ../drafts/cb/U_AS.lean` → exit 0, **0 errors**; 12 `declaration uses sorry`
warnings, all other units' leaves (KL0 ×6: `gaussSucc`, `gaussSucc_val`, `gaussPair`, `gaussPair_val`, `gaussRecord`,
`label_crossingOf`; KL1 ×2; KL2, KL3, T1, GL ×1). `grep -c sorry`: 18 before → 16 after (the 16 = 15 leaf sorries of other
units + the word in the header docstring, line 10).

## Leaves proved (2 / 2 of unit AS)

| leaf | lines | proof |
|---|---|---|
| `SM.CB.mem_blockRecordCrossings_crossingOf` | 15 | `←`: witness `v` itself. `→`: from `crossingOf v = crossingOf w`, `Record.crossingOf_eq_iff` (LinkRecord:485) gives `v ∈ {w, τ w}`; `simp only [Record.crossingOf, Finset.mem_insert, Finset.mem_singleton]` + `rcases … rfl | rfl`; in the twin case `(D.record.pair w).1 = w.1` is `Diagram.twin_fst` (LinkDiagramRecord:415, `rfl`-level since `record.pair = pairPerm`, `pairPerm w = twin w`). Then rewrite `v.1 = w.1`. |
| `SM.CB.exists_visit_of_mem_carrierCrossings` | 5 | `x := (carrierCrossingEquiv hn hP S A hS).symm ⟨c, hc⟩ : (carrierShadow …).Crossing`; `x.val.Nonempty` from `Finset.card_pos` + `Shadow.crossing_card_two` (LinkDiagram, `= 2`); the visit is `⟨x, ⟨s, hs⟩⟩` (anonymous constructor works through the `def Visit := Σ …`, as `Diagram.twin` does; `positiveLift_Γ` is `rfl` so no rewrite is needed). |

Leaves left in unit AS: none. Helpers added: none (both leaves are ≤ 15 lines; no `as_*` lemma was needed).

## Notes for the assembler / executor

* Both proofs are fully generic in the shadow: they use only `Record.crossingOf_eq_iff`, `Diagram.twin_fst`,
  `Shadow.crossing_card_two`, `carrierCrossingEquiv` — nothing from KL0–GL, so unit AS has no dependency on other units.
* `mem_blockRecordCrossings_crossingOf` is consumed as a `rw` rule in the glue `record_iso_blockRecord`
  (`rw [mem_blockRecordCrossings_crossingOf, Set.mem_setOf_eq, label_crossingOf …]`); it still rewrites after the
  proof (compiled).
* When porting to `SM/CBProducts.lean`: `Record.crossingOf_eq_iff (ρ : Record) (v) (x)` takes `ρ` EXPLICITLY (it is a
  `variable (ρ : Record)` of `namespace Record`). Passing `_` for it fails with a postponed-metavariable type mismatch
  (`?m ∈ ↑?x` vs `v ∈ ↑(D.record.crossingOf w)`); use dot notation `D.record.crossingOf_eq_iff v x` with `x` spelled out
  (as MarkedProducts.lean:3871 does). Everything else is `rfl`-level.
* Residual warnings in the file are frozen skeleton text, not mine: unused binder `hT` in the `∃` of
  `exists_blockCarrier` (PC leaf statement, line 410) and deprecated `Set.mem_setOf_eq` in the glue (line 482;
  Mathlib now prefers `Set.mem_ofPred_eq`). Both are harmless; the assembler may rename/replace them when porting if
  the statement freeze is lifted for the module file.
* Mathlib pitfalls hit: only the explicit-`ρ` one above. `Finset.card_pos : 0 < s.card ↔ s.Nonempty` used right-to-left.
