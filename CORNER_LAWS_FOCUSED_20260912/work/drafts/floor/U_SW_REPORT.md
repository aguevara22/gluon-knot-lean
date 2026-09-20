# U-SW report — `Diagram.switchAll` transport (rows 99/100, PLAN_FINAL §3 (C) step 2, §4 unit U-SW)

File: `work/drafts/floor/U_SW.lean` (byte-identical copy of `Statements_FINAL.lean` + the U-SW proofs).
Check: `cd work/lean && lake env lean ../drafts/floor/U_SW.lean` — **0 errors**, ~10 s warm; the only
warnings are the `declaration uses sorry` of the other units' leaves. `grep -c sorry`: 25 before → **21 after**
(the 4 U-SW leaves; `diff Statements_FINAL.lean U_SW.lean | grep '^<'` shows exactly the four removed `sorry`
lines — no statement, name, definition or docstring changed; 487 lines added, file 730 → 1213 lines).
`#print axioms` of all four leaves: `[propext, Classical.choice, Quot.sound]`.

## Leaves proved (4 / 4)

| leaf | proof |
|---|---|
| `usw_switchAll_sign` | `unfold sign`; `switchAll_overStrand` (rfl), `usw_switchAll_underStrand`, `det_swap`, `Left.sign_neg` (template `switch_sign_self`, LinkDiagram.lean 688) |
| `usw_switchAll_writhe` | restate the sums over `D.Γ.Crossing` (`show`), `Finset.sum_neg_distrib`, `sum_congr`, `usw_switchAll_sign`, case split `sign_eq_one_or_neg_one`, `rfl` on the casts |
| `usw_carried_switchAll` | the same record (`one τ τ_mem τ_inj τ_eval doubles transverse order` are literally `c`'s: `twin`, `visitPt`, `visitCoord`, `crossingPoint` depend on the shadow only); `sign_eq` by `usw_underVisit`, `usw_overVisit` (rfl), `det_swap`, `Left.sign_neg`, `c.sign_eq`, `usw_switchAll_sign` |
| `usw_switchAllCarries` | `SwitchAllCarriesUnit` assembled from the helpers below: `planar` (`eqvGen_carries` on `Reparam ∨ Deform`), `ri/rii/riii` (site transports), `circle` (shadow-only, `⟨h.1, h.2⟩`), `skein` (`usw_skein`) |

## Leaves left

None of U-SW. (`usw_P_switchAll` is U-EQ's leaf, untouched.)

## Helpers added (all `usw_`-prefixed, placed immediately before the leaf that uses them, same section)

Before `usw_switchAll_sign`: `usw_switchAll_underStrand` (`D.switchAll.underStrand x = D.overStrand x`, via `eq_other_of_mem_of_ne`).
Before `usw_carried_switchAll`: `usw_overVisit` (rfl), `usw_underVisit` (`Sigma.ext`).
Before `usw_switchAllCarries` (after the `SwitchAllCarriesUnit` structure):
- `usw_exists_visit_of_eval_eq` — **the under-visit lemma's geometric core** (PLAN_FINAL §3 (C) "a lemma that a
  reparametrisation carries the PAIR of visits", risk 5): a traversal point `p` of a generic diagram with
  `eval p = crossingPoint x` is `visitPt w` for an occurrence `w` of `x`. Proof: the edge parameter is `> 0`
  (`t = 0` makes the point the tail vertex of `⟨i, j⟩`; `Generic.tail_off` forces both strands of `x` incident to
  that vertex, hence adjacent — contradiction with the crossing's non-adjacency, 4 cases on `incident`, `ring` in
  `ZMod`); the strand `⟨i, j⟩` belongs to `x` (else `no_triple` with the two strands of `x`,
  `Generic.crossingPoint_mem_interior`); the parameter is `crossingParam` (`edgePoint_injective` with
  `Shadow.edge_ne_zero`).
- `usw_mapPt_injective`, `usw_reparam_under` (over-visit correspondence ⇒ under-visit correspondence: the image of
  the under visit evaluates to `crossingPoint x'`, so it is a visit of `x'`; not the over one by injectivity of
  `mapPt` and `visitPt_injective`), `usw_reparamData` (same `e`, `φ`, `between`, `eval_eq`).
- `usw_deform_underStrand`, `usw_switchAll_deform` (switch and re-vertexing commute, `mk_eq_of_overStrand_eq`),
  `usw_deformData`, `usw_planar`.
- `usw_clean`, `usw_localFrame`, `usw_outsideMatch` (`over_eq := m.under_eq` definitionally; `under_eq` through
  `usw_underVisit`), `usw_moveMatch`.
- `usw_overOn` (rfl), `usw_underOn`, `usw_separates`, `usw_beforeOn` (rfl), `usw_underOn_of_overOn` (from
  `Separates` + `ArcCover.disjoint`), `usw_triple_comm` (`{c, b, a} = {a, b, c}`).
- `usw_riData`, `usw_ri_carries`; `usw_riiData` (`same_over` swaps `a' ↔ b'` via `usw_underOn_of_overOn`),
  `usw_rii_carries`; `usw_riiiData` (relabel `(a, b, c) ↦ (c, b, a)`, `xab ↔ xbc`, `top_*/mid_*` from
  `Separates` + disjointness, `rev_a/b/c` flipped with the ACCEPTED `Diagram.beforeOn_swap_iff`
  LinkMoves.lean 3022 exactly as `RIIIData.reverse` 3190-3225 does), `usw_riii_carries`.
- `usw_orientedSmoothingData` (arcs exchanged, template `OrientedSmoothingData.switch` 1955),
  `usw_isOrientedSmoothing`, `usw_switchAll_eq_switch` (`Dp.switchAll = (Dp.switch x).switchAll.switch x`),
  `usw_skein` (`IsSkeinTriple Dp Dm D0 → IsSkeinTriple Dm.switchAll Dp.switchAll D0.switchAll`; the crossing is
  positive in `D̄₋` by `usw_switchAll_sign` + `switch_sign_self`).

Data-valued helpers (`usw_reparamData`, `usw_deformData`, `usw_outsideMatch`, `usw_moveMatch`, `usw_riData`,
`usw_riiData`, `usw_riiiData`, `usw_orientedSmoothingData`) are `def`s (the structures live in `Type`, as the
accepted `RIData.mirror` etc.); everything else is a `theorem`.

## Pitfalls met (Lean / Mathlib / this library)

1. **`rw` and `switchAll`-typed variables.** `D.switchAll.Γ` is `D.Γ` only after unfolding `switchAll`
   (semireducible). `rw` matches at `instances` transparency, so a lemma whose bound variable is
   `x : D.Γ.Crossing` does NOT rewrite a target whose `x` was introduced with type `D.switchAll.Γ.Crossing` (and
   vice versa: `switch_overStrand_self` with `D := (Dp.switch x).switchAll` will not match `x : Dp.Γ.Crossing`).
   Symptoms: "did not find an occurrence of the pattern … not type-correct under the `implicit` transparency
   level". Cure used throughout: fix the binder types with `show ∀ x : D.Γ.Crossing, …` / `show` before `rw`, or
   use term-mode `Eq.trans` chains (defeq at default transparency) as the accepted mirror proofs do.
2. `Finset.sum_congr` under `unfold writhe` hits the same problem — restate both sums over `D.Γ.Crossing` first.
3. Multi-line `{ f := …, g := … }` structure instances: continuation lines must be indented at least to the column
   of the first field (`sepByIndent`), otherwise "expected '}'" + "fields missing". Positional `⟨…⟩` avoids it.
4. `first | exact Or.inl (by ring) | …` does not backtrack on `ring` failure (the `by` block is elaborated after
   `exact` succeeds); enumerate the cases with bullets instead.
5. Name clash: bare `Reparam` in `namespace SM` resolves to an unrelated `SM.Reparam : Type`; write
   `Link.Reparam`, `Link.Deform` (the other move names `RI`, `RII`, `RIII`, `PlanarIsotopic`, `IsSkeinTriple`,
   `ReparamData`, `DeformData` resolve correctly with `open Link`).
6. `Set`-literal rewriting (`rw [usw_triple_comm]`) fails on a goal typed `Set D.switchAll.Γ.Arc` holding
   `D.Γ.Arc`-typed elements (same cause as 1); `(congrArg (D.Γ.ArcCover U) (usw_triple_comm …)).mpr h.cover` works.

## Notes for the assembler / executor

- No leaf of U-SW is false or needs a stronger hypothesis; every field of `SwitchAllCarriesUnit` is proved as
  stated. The fallback `X.reverse.mirror` route (PLAN_FINAL §3 (C) step 2) is NOT needed.
- The two accepted lemmas that made RIII cheap: `Diagram.beforeOn_swap_iff` (LinkMoves.lean 3022) and
  `Diagram.exists_visit_on_arc` / `visit_on_arc_unique` (2960-2985); the RIII relabelling is ~90 lines instead of
  the feared fresh cyclic-order development.
- `usw_exists_visit_of_eval_eq` is a general fact about generic diagrams (no `switchAll`); if the library ever
  needs "traversal points at a crossing point are visit points" elsewhere (e.g. a `Reparam` record clause), it can
  be ported to SM/LinkDiagram.lean as is.
- U-EQ (`usw_P_switchAll`) can consume `usw_switchAllCarries.planar/ri/rii/riii/circle/skein` directly as the
  `RCompetitor` inputs, and `usw_switchAll_sign`/`usw_switchAll_writhe` for step 2 of U-C; `usw_carried_switchAll`
  gives the `Carried` record for `D̄` on the rounded curve (step 3).
- Nothing was written under `work/lean`; no `lake build` run; only `lake env lean` on the draft.
