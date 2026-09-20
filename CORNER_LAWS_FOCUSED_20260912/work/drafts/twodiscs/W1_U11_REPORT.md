# Row 57 — unit U11 (57d on the convex model) — REPORT

Written 2026-09-19 by the U11 agent.  File: `work/drafts/twodiscs/W1_U11.lean` (1 550 lines; from
`Skeleton_FINAL.lean`, 1 039 lines).  Typecheck: `cd work/lean && lake env lean ../drafts/twodiscs/W1_U11.lean`
→ **0 errors**, 88 `declaration uses sorry` warnings (skeleton: 92), one linter warning (the frozen hypothesis
`hD'` of `U11_boundary_homeo_of_lift` is not needed by the proof).  `python3 check_57_identity.py W1_U11.lean`
→ `IDENTITY OK`.  `grep -c sorry`: 95 before, 91 after (the 3 extra over the leaf count are the word in comments,
unchanged).  No frozen statement, leaf statement or docstring was changed.

## Closed (all four U11 leaves)

| leaf | axioms (`#print axioms`, scratch copy) | route |
|---|---|---|
| `U11_frontier_eq_gauge_one` | propext, Classical.choice, Quot.sound | Mathlib `gauge_eq_one_iff_mem_frontier`, `gauge_le_one_iff_mem_closure` + `IsCompact.isClosed.closure_eq`; `D ∈ 𝓝 0` from `0 ∈ interior D`. |
| `U11_radial_extension` | propext, Classical.choice, Quot.sound | Alexander trick in gauge coordinates (sm-3:537-542).  Translate both discs by interior points `c, c'` (`u11h_translate`: preimage under `x ↦ x + c`, convex/compact/`0 ∈ interior`, frontier transported); `u11h_rad A b x = gauge A x • b ((gauge A x)⁻¹ • x)` with `b y = β (y + c) − c'`; `u11h_rad_rad` (inverse via `b' y = β⁻¹ (y + c') − c`, `β⁻¹ := u11h_homeoInv e`), `u11h_continuous_rad` (global continuity: off `0` by `continuous_gauge` and `gauge_pos`, at `0` by the radial bound `‖rad x‖ ≤ gauge A x · M`, `squeeze_zero_norm`); the homeomorphism `D ≃ₜ D'` is built as an explicit structure with `F x = rad (x − c) + c'`.  Frontier condition by `gauge = 1` on the frontier. |
| `U11_boundary_homeo_of_lift` | + **sorryAx** (via `u11h_circle_subset_closure`) | `u11h_boundary_homeo_aux` (sorry-free, abstract sets `S ⊇ sphereCircle P`, `S' ⊇ sphereCircle P'`) applied with `sphereCircle P ⊆ closure (regionOf P s)`. |
| `U11_top_extension` | + **sorryAx** (via `U4_exists_insideModel`, `U7_pl_discs_inner`, `U8_pl_discs_outer`) | `F = f'⁻¹ ∘ A ∘ f` with the 57b witnesses `(D, f)`, `(D', f')` at `L, L'` from `U4_exists_insideModel`, `β` from leaf 3, `A` from leaf 2; homeomorphism `e.trans (eA.trans e'.symm)`; boundary clause from `A = β` on `frontier D` and `e'.symm_apply_apply`. |

### `u11h_boundary_homeo_aux` (the FR-TD-10 conjugation), sorry-free
`q x := f ↑(traversal P x)` is continuous, lands in and covers `frontier D`, and `q x = q y ↔ traversal P x =
traversal P y` (`u11h_param_facts`; needs `sphereCircle P ⊆ S`, `f '' sphereCircle P = frontier D`, `InjOn f S`,
and `range (traversal P) = polygonImage P`, proved here as `u11h_range_traversal` rather than consuming
`U4_range_traversal`).  The lift: `u11h_lift_facts` extracts `ε = ±1` with `φ (x + n) = φ x + ε n'`, injectivity
(strict mono/anti) and surjectivity (`u11h_surj_of_period`: IVT on `[m n, (m+1) n]`, `m = ⌊(y − φ 0)/n'⌋`).
`u11h_traversal_congr` / `_inv`: `traversal P x = traversal P y ⟺ traversal P' (φ x) = traversal P' (φ y)`
(`Embedded.traversal_injective`, `u11h_traversal_add_int`, `u11h_lift_add_int`).  `β₀ : frontier D → frontier D'`
is `⟨q x, _⟩ ↦ ⟨q' (φ x), _⟩` via `Classical.choose`; well defined by `_congr`, injective by `_congr_inv`,
surjective by surjectivity of `φ`; continuous because `Q : Icc 0 n → frontier D` is a quotient map
(`Continuous.isClosedMap.isQuotientMap`, compact → T2, surjective by `u11h_exists_reduce`) and `β₀ ∘ Q` is
visibly continuous; homeomorphism by `Continuous.homeoOfEquivCompactToT2` (`frontier D` compact).

## Open / black boxes

* No U11 leaf is open.  Nothing of another unit's statement was changed; no new `u11h_` Prop with `sorry` was added.
* Consumed (still `sorry`) leaves: `U4_exists_insideModel` (leaves 3, 4), `U7_pl_discs_inner`,
  `U8_pl_discs_outer` (leaves 3, 4, through `u11h_pl_disc` / `u11h_circle_subset_closure`).  Leaf 3 uses U7/U8
  **only** for `sphereCircle P ⊆ closure (regionOf P s)` (the `B ⊆ S` clause of 57b); if U6 provides that fact
  directly, `u11h_circle_subset_closure` can be re-pointed and leaf 3 becomes independent of U7/U8.

## Notes

* FR-TD-5: the proof of 57d uses `hφ` only for continuity, strict monotonicity/antitonicity (injectivity) and the
  degree-one periodicity; the orientation *sign* is not used (both sign cases are handled symmetrically), so the
  positivity hypothesis is "kept as printed and unused" in the sense of the reading.
* Leaf 3's frozen hypothesis `hD'` is unused by the proof (linter warning only).
* Helpers (35 `u11h_`/`U11_` declarations) sit immediately before the leaf that first uses them: gauge basics
  before leaf 1; radial map, translation and `u11h_homeoInv` before leaf 2; traversal/lift lemmas, the abstract
  construction, `u11h_pl_disc`, `u11h_circle_subset_closure` before leaf 3.  `open Classical in` /
  `open Classical Topology in` are scoped to the two declarations that need them.
* Mathlib names under the pin worth recording: `gauge_eq_one_iff_mem_frontier`, `gauge_le_one_iff_mem_closure`,
  `gauge_pos (Absorbent) (IsVonNBounded)` with `IsCompact.isVonNBounded ℝ`, `continuous_gauge`,
  `Convex.translate_preimage_left` (this is the `x ↦ x + c` form), `Homeomorph.preimage_interior/_frontier`,
  `continuousOn_iff_continuous_domRestrict`, `IsClosedMap.isQuotientMap`, `Continuous.homeoOfEquivCompactToT2`.
* Reassessment discipline: no lemma needed a second method; every compile error was a one-shot fix (cast forms in
  `Int.induction_on`, `dif_pos` → `↓reduceDIte`, `Set.restrict` → `domRestrict`).
* Scratch files (private): `/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/u11/{S1,S2,Axioms}.lean`.
