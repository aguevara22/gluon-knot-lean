# U_GL_REPORT — unit GL (record blocks of `D_A` = blocks owned by `A`)

Prover report, 2026-09-14. File: `work/drafts/cb/U_GL.lean` (copy of Skeleton_FINAL.lean; only the GL leaf body
replaced, helpers inserted immediately before it). Compile: `cd work/lean && lake env lean ../drafts/cb/U_GL.lean`
→ **0 errors**; `grep -c sorry`: 18 before → **17 after** (the 17 remaining are other units' leaves, see §3).

## 1. Leaves

| leaf | status |
|---|---|
| `SM.CB.exists_blockGraphEquiv` | **PROVED** (statement untouched; `diff Skeleton_FINAL.lean U_GL.lean` removes exactly the one `:= sorry` line). |

`#print axioms SM.CB.exists_blockGraphEquiv` (checked with a temporary `#print`, removed again):
`[propext, sorryAx, Classical.choice, Quot.sound]` — the `sorryAx` is inherited ONLY from the black boxes used
(KL0: `gaussPair_val`, `label_crossingOf`, the `gaussRecord` laws; KL1: `positiveLiftRecordIso`,
`positiveLiftRecordIso_val`; KL2: `gaussRecord_adj_iff`). The generic part (`gl_adj_map`) prints
`[propext, Classical.choice, Quot.sound]`.

## 2. Route actually taken (PLAN_FINAL §4 unit GL, slightly simplified)

No `SimpleGraph.Iso`/`connectedComponentEquiv` chain through `residualGraph.induce` was needed. Instead:

1. **Transport of record interlacement along a `RecordIso`** (generic, `{ρ ρ' : Record} (ι : RecordIso ρ ρ')`):
   `gl_steps_map` (`steps` via `RecordIso.Φ_pow` + `Nat.find_min'`/`Nat.find_spec`), `gl_arcBetween_map`,
   the induced crossing map `gl_crossingMap ι x := ρ'.crossingOf (ι.Φ x.rep)` with `gl_crossingMap_crossingOf`,
   `gl_crossingMap_inj`, `gl_mem_crossingMap_iff`, `gl_forall_mem_crossingMap`, then `gl_interlaces_map`
   (`ρ'.Interlaces (cm x) (cm y) ↔ ρ.Interlaces x y`) and `gl_adj_map` (same for `interlacementGraph.Adj`).
   These are reusable by anyone needing "a `RecordIso` induces an isomorphism of interlacement graphs".
2. **Label map** `gl_lbl hS A p := label hc X (gl_crossingMap (positiveLiftRecordIso hn hP hS A) p)`,
   `X = carrierCrossings hn hP S A`. Facts: `gl_lbl_mem` (∈ X), `gl_lbl_crossingOf`
   (`gl_lbl (crossingOf v) = (carrierCrossingEquiv v.1).val`, from KL1's spec + KL0's `label_crossingOf`),
   `gl_adj_iff` (`D_A.record` adjacency ↔ `Interlaces hn hP` of labels, from `gl_adj_map` + KL2),
   `gl_lbl_injective` (via `gl_label_inj`: two chords of `gaussRecord` with one label coincide —
   `visit_eq_or_twin` + `gaussPair_val`), `gl_exists_lbl_eq` (surjective onto `X`, via `someVisit` and `Φ.symm`),
   `gl_mem_blockRecordCrossings_iff` (`p ∈ blockRecordCrossings A H ↔ gl_lbl p ∈ pieceLabels H`).
3. **Components.** `gl_carrierCrossings_eq_biUnion` (re-proof of the glue lemma, which sits AFTER the leaf),
   hence `gl_lbl p ∈ CV.U`; `gl_piece p := CV.pieceOf … (gl_lbl p) _`; adjacency ⇒ same piece
   (`gl_piece_eq_of_adj`, residualGraph adjacency is `Interlaces` by `Iff.rfl`); `gl_pieceOfComp` by
   `SimpleGraph.ConnectedComponent.lift`; `gl_reachable_of_walk` = the `owner_eq_of_walk` pattern: a
   `residualGraph` walk between two labels of `D_A` lifts to `Reachable` in `D_A.record.interlacementGraph`
   (each vertex stays in the block owned by `A` by `CV.mem_pieceLabels_of_interlaces`, whose labels are in `X`);
   injectivity (`ConnectedComponent.ind₂` + `exact`/`sound`), surjectivity from `CV.pieceLabels_nonempty`;
   `gl_blockEquiv := Equiv.ofBijective …`. The `supp` identity: `mem_supp_iff`, `gl_mem_blockRecordCrossings_iff`,
   `CV.mem_pieceLabels`, and injectivity of `gl_pieceOfComp`.

## 3. Helpers added (all `SM.CB`, prefix `gl_`, in a nested `section GLHelpers` placed immediately before the leaf;
the leaf itself is in the same section/namespace as before)

`gl_steps_map`, `gl_arcBetween_map`, `gl_crossingMap` (def), `gl_crossingOf_Φ_eq_iff`, `gl_crossingMap_crossingOf`,
`gl_crossingMap_inj`, `gl_mem_crossingMap_iff`, `gl_forall_mem_crossingMap`, `gl_interlaces_map`, `gl_adj_map`,
`gl_label_inj`, `gl_carrierCrossings_eq_biUnion`, `gl_exists_block_of_mem`, `gl_pieceLabels_subset`,
`gl_mem_U_of_mem`, `gl_lbl` (def), `gl_lbl_mem`, `gl_lbl_mem_U`, `gl_lbl_crossingOf`, `gl_adj_iff`,
`gl_lbl_injective`, `gl_exists_lbl_eq`, `gl_mem_blockRecordCrossings_iff`, `gl_piece` (def), `gl_piece_mem`,
`gl_piece_eq_of_adj`, `gl_piece_eq_of_walk`, `gl_pieceOfComp` (def), `gl_pieceOfComp_mk`, `gl_pieceOfComp_mem`,
`gl_reachable_of_walk`, `gl_pieceOfComp_injective`, `gl_pieceOfComp_surj`, `gl_blockEquiv` (def), `gl_blockEquiv_val`.

Remaining `sorry` (17, none GL): KL0 `gaussSucc`, `gaussSucc_val`, `gaussPair`, `gaussPair_val`, `gaussRecord`
(4: `succ_cycle`, `pair_ne`, `pair_invol`, `bit_pair`), `label_crossingOf`; KL1 `positiveLiftRecordIso`,
`positiveLiftRecordIso_val`; KL2 `gaussRecord_adj_iff`; KL3 `gaussRecord_restrict_iso`; T1
`restrictCrossings_iso_of_recordIso`; AS `mem_blockRecordCrossings_crossingOf`, `exists_visit_of_mem_carrierCrossings`.

## 4. Mathlib / library pitfalls met

* `Record.Crossing` is a `def` (not `abbrev`) of a Subtype: `rw` whose motive abstracts a term of type `ρ.Crossing`
  sitting under `Subtype.val` (`↑x`) fails with "motive is not type correct". Go through
  `Record.crossingOf_eq_iff` / `Record.crossingOf_rep` instead of `RecordIso.crossingOf_eq` + `Finset.mem_map'`.
* `rw [(h : a = b ↔ c = d).not]` does not find `a ≠ b` (the `Ne`); use `and_congr (not_congr h) _`.
* `Record.steps` is a `dite` on `∃ n, (succ ^ n) v = w`; `dif_pos`/`dif_neg` are deprecated — use
  `dite_eq_left h` / `dite_eq_right h` (as MarkedProducts does). The `Nat.find` instances unified without trouble
  in this file's classical context.
* `(gaussRecord hc T).M` must be given the ascription `({v : Visit P // v.1 ∈ T})` for anonymous constructors /
  `Subtype.ext` (as `occVisit` already does); `(gaussRecord hc T).pair x = gaussPair hc T x` is `rfl`.
* `CV.pieceOf c hc` carries a membership proof: rewriting `c` needs `subst` (or a proof-irrelevance `exact`), not `rw`.
* `SimpleGraph.ConnectedComponent.mem_supp_iff` gives `connectedComponentMk v = C` (component on the RIGHT).

## 5. For the assembler / executor

* The leaf's proof uses ONLY: KL0 `gaussPair_val`, `label_crossingOf`, the `gaussRecord` structure (pair = `gaussPair`
  by rfl); KL1 `positiveLiftRecordIso`, `positiveLiftRecordIso_val`; KL2 `gaussRecord_adj_iff`; plus accepted
  `CV.*` (pieces, `mem_pieceLabels_of_interlaces`, `biUnion_pieceLabels_piecesOn`), `geoCarrierCrossings_eq_generic`,
  `visit_eq_or_twin`, `Record.*` from LinkRecord/LinkRecordExtras/MarkedProducts. No other unit's leaf.
* Merge: copy the `section GLHelpers … end GLHelpers` block and the leaf body verbatim into Skeleton_FINAL.lean
  (they sit between the T1 leaf and the GL leaf docstring). For the port to `SM/CBBlockGraph.lean`, the
  generic `RecordIso` transport (`gl_steps_map` … `gl_adj_map`, `gl_label_inj`) can go to a small
  `SM/CBRecordIsoInterlacement.lean` and be reused by T1/KL3 if wanted.
* `gl_carrierCrossings_eq_biUnion` duplicates the glue lemma `carrierCrossings_eq_biUnion` (same 3-line proof);
  on merge the glue lemma can be moved before the leaf and the duplicate dropped.
