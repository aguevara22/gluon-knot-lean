# G11_U2_REPORT — unit U2 (A-config + relabelling + provable branches)

Written 2026-09-14 by the U2 prover on Mark's RunPod home pod. Plan of record: `G11_PLAN.md` §3 (A8–A15, X1, X3),
§7 (unit table). File: **`work/drafts/rlane2/G11_U2.lean`** (2 098 lines; the skeleton was 1 086).

## Compile

```
cd work/lean && lake env lean ../drafts/rlane2/G11_U2.lean
```
exit 0, **0 errors**, 37 × `declaration uses sorry` (= 49 − 12), plus linter warnings only (unused section
variables / unused binders of the frozen statements), ~10 s. `grep -c sorry`: **50 before → 38 after** (one
occurrence is the word in the header docstring). `diff G11_Skeleton.lean G11_U2.lean | grep '^<'` prints exactly
twelve `  sorry` lines: no definition, structure, statement, name or docstring was changed. Nothing under
`work/lean` was written.

**Two imports were added at the top of the file** (lines 2–3), needed for the barycentric-coordinate description
of the triangle that the plan itself cites (`AffineBasis.interior_convexHull`, §3 D1/A8), neither of which is
imported transitively by `RProof.X1Rows3`:
```
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
```
Both `.olean`s exist in the pinned Mathlib build. **The assembler must keep them when merging the units** (U3's
`disc_isDisc` / `triangle_sub_interior` will need the first one too).

## Leaves — 12 of 14 proved

| leaf | status | proof (one line) |
|---|---|---|
| `G11_alt_swap` (A9) | **PROVED** | `strandSign = crossingSign` (rfl), `crossingSign_swap`, `decide` over `SignType³` |
| `G11_exact_swap` (A10) | **PROVED** | `{e, g, f} = {e, f, g}` (`Finset.pair_comm`), unfold |
| `G11_triangleCrossings_swap` | **PROVED** | `triangleSupports e g f = triangleSupports e f g` by `ext`/`pair_comm`/`tauto` |
| `G11_alt_crossingSign` (A11) | **PROVED** | `exact hne` (definitional) |
| `G11_cfg_hmp` (A12) | **PROVED** | A4 at `x_ef` + `visitTwin (vef) = vfe` (`visitTwin_unique`) |
| `G11_cfg_hmq` (A12) | **PROVED** | `by_cases f = g` (then it is `hmp` by proof irrelevance); else A3 on `e` with `hadj` from A7, then A4 at `x_eg` |
| `G11_cfg_hpq` (A12) | **OPEN — missing hypothesis** | see below; provable form `gu2_cfg_hpq` (L1452) PROVED |
| `G11_cfg_order` (A13) | **PROVED** | double points identified (`gu2_xmp_eq`, `gu2_xmq_eq`), `edge X m = c • edge P e` (A2), `edgePoint_injective` ⇒ `(s₂−s₁)c = t₂−t₁` |
| `G11_cfg_trans` (A14) | **PROVED** | A6 ×3 + A11 |
| `G11_cfg_clear_frontier` (A15) | **PROVED** | see "A15" below |
| `G11_cfg_clear_vertex` (A15) | **PROVED** | `gu2_cfg_clear_vertex` (helper placed before `clear_frontier`, which needs it) |
| `G11_clear` (A8) | **OPEN — FALSE as stated** | see below; the intended statement `gu2_clear` (L1063) PROVED |
| `G11_le_one_crossing` (X1) | **PROVED** | `EXT_homfly_wall` + `AV_key_lt_of_gauss` (`Finset.card_le_one`) + `visit_crossing_val_eq_pair`; axioms: `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` — no `sorryAx` |
| `G11_card_cases` (X3) | **PROVED** | a non-crossing support bounds the card by 2 (`Finset.card_le_card_of_injOn` into `triangleSupports.erase s₀`), `omega` |

`#print axioms`: `G11_card_cases`, `G11_alt_swap`, `gu2_triBasis`: standard axioms only. `gu2_clear`,
`G11_cfg_order`, `G11_cfg_clear_frontier`: `sorryAx` only through the U1 black boxes (`G11_no_visit_between`,
`G11_carrierEdge_*`) and — for the two `clear_*` leaves and `G11_configOf` — through the open `G11_cfg_hpq`.

### The two open leaves: a section-variable scoping problem in the skeleton (not a mathematical one)

In this Lean version a theorem's proof sees a section `variable` only if the **statement** mentions it (or it is
`include`d). Two frozen statements do not mention hypotheses their proofs need:

1. **`G11_clear` (L1146) does not have `hG : CarrierGeometry P` in scope** (section `G11Triangle` declares
   `(hn) {P P'} (hG) (hs) {e f g}`; the statement mentions only `hs`). **Without `hG` the statement is false.**
   Counterexample (numerically checked by `G11_U2_probe.py`, all assertions pass): `n = 8`, `P' = P`,
   `P 0 = (−1,0), P 1 = (1,0), P 2 = (0,1), P 3 = (0,−1), P 4 = (−1,−1), P 5 = (1,1), P 6 = (1,−1), P 7 = (−1,1)`,
   `e, f, g = 0, 2, 4`: the four remote edges `0, 2, 4, 6` all pass through the origin (a quadruple point, which
   `CarrierGeometry` forbids). `{e,f}, {e,g}, {f,g}` are crossings; `ExactTriangleVisitOrders P P e f g (fun _ => Iff.rfl)`
   holds because every same-edge visit pair with union `{e,f,g}` has **equal** parameters (both `<` false, the
   reversed clause is `False ↔ False`) and all other pairs are carried trivially; the triangle
   `conv{x_ef, x_eg, x_fg} = {0}` has frontier `{0}` in `ℝ²`; the foreign edge `h = 6` contains `0`. So clause (i)
   fails. **Fix for the executor**: `include hG in` before `G11_clear` (its signature becomes
   `G11_clear hG hs hef heg hfg hcef hceg hcfg hX`, exactly the signature of `gu2_clear`), body
   `:= gu2_clear hG hs hef heg hfg hcef hceg hcfg hX`. Nothing in the skeleton calls `G11_clear`.

2. **`G11_cfg_hpq` (L1443) does not have `hcfg : IsCrossing P {f, g}` (nor `hfg : f ≠ g`) in scope** — its statement
   mentions `hn hG hs hT q hcef hceg htri` and the explicit `hX` only. Its conclusion **implies** `f ≠ g ∧
   IsCrossing P {f, g}` (`gu2_hcfg_of_hpq`, L1374, PROVED: the double point of `{p, q}` in `X` is a common point of
   sub-segments of `f` and `g`; adjacent `f, g` meet only at a vertex, which is never a double point of a retained
   crossing, `geo_nonadjacent_meet_crossing`). So proving the frozen leaf would derive the crossing `{f, g}` of `P`
   from `hX, hcef, hceg, htri` alone — a Gauss-parity statement about `P'` (X2-type; `P'` carries no geometric
   hypothesis at all in this section), not available in the library and, for degenerate `P'`, presumably false.
   **Fix**: `include hfg hcfg in` (or explicit binders) before `G11_cfg_hpq`; then the body is `gu2_cfg_hpq … hfg hcfg hX`
   (`gu2_cfg_hpq hn hG hs hT q hcef hceg htri hfg hcfg hX`, L1452, PROVED by A3 on `f` and on `g` with the
   permuted `ExactTriangleVisitOrders` (`gu2_exact_of_eq`) and A4 at `x_fg`). The downstream call sites
   `G11_cfg_hpq hn hG hs hT q hcef hceg htri hX` (in the **statements** of `G11_cfg_clear_frontier` and
   `G11_cfg_clear_vertex`, and in `G11_configOf`) must then receive the two extra arguments (they are section variables already in scope there: `hfg` is a binder of the two `clear_*` leaves,
   `hcfg` is `_hcfg` in `G11_configOf`). My proofs of the two `clear_*` leaves recover `hcfg` from `hpq` through
   `gu2_hcfg_of_hpq`, so they keep working under either signature.

   Consequence today: `G11_cfg_clear_frontier`, `G11_cfg_clear_vertex` and hence `G11_configOf` / the row depend on
   the `sorry` of `G11_cfg_hpq`; U6 uses `G11_cfg_hpq` as a black box as planned. Everything else of the
   configuration is closed.

## How A8/A15 are actually proved (differs from the plan in two places)

* **A8 (`gu2_clear`).** Clause (i): a frontier point of the triangle lies on one of the three sides
  (`gu2_frontier_subset_sides`: barycentric coordinates of the affine basis `![x_ef, x_eg, x_fg]`, some coordinate
  vanishes; `gu2_tri_det` gives the non-collinearity from `det(edge e, edge f) ≠ 0` at `x_ef` and the distinct
  parameters); each side is cleared by **one** lemma `gu2_side_clear` applied in the three labellings
  `(e,f,g), (f,e,g), (g,e,f)` — the permuted `ExactTriangleVisitOrders` is `gu2_exact_of_eq` (the predicate depends on
  `e f g` only through `{e,f,g}`), the permuted crossings are `gu2_isCrossing_comm`/`gu2_xPair_comm`, the permuted
  visits `gu2_visit_congr`. `3 ≤ n` (needed for `adjacent_edges_meet`) is **derived** from a remote pair
  (`gu2_three_le_of_remote`, `decide` on `ZMod 1`, `ZMod 2`) since `hn` is not in scope either. Clause (ii): the
  tails `P e, P f, P g` are off the triangle — a point of the triangle on the line of a side is on the side
  (`gu2_line_e/f/g_mem_segment`: the opposite coordinate vanishes on the line, `AffineMap.apply_lineMap`), and
  the tail has parameter `0 < t(x)` — then the walk `gu2_no_vertex_of_walk` (`Nat.find` on the first step
  leaving `Δ` from a vertex inside; the edge before it meets the frontier by `G11_preconnected_meets_frontier`;
  its tail is in `Δ`, so it is foreign). The walk is stated in the general form "if every edge whose tail is in
  `Δ` misses the frontier and some vertex is off `Δ`, no vertex is in `Δ`".
* **A15 without block machinery.** The plan's route through `geo_mark_block`/`GeoBlockInterior` is not needed. Two
  facts replace it: (a) `gu2_edgeSegment_sub` — every edge `k` of `X` is a sub-segment of the original edge
  `(geoOutSlot (geoCornerMark k)).1` (both corners lie on it: `geo_evaluation_eq_outSlot`,
  `geoCornerPolygon_outEdge_eq_inEdge_of_independent` + `geoMarkSuccessor_on_edge`; convexity); (b)
  `gu2_carrierEdge_label` — the carrier edge of a retained visit `v` lies inside `v.2.val` (its double point is
  interior to that edge; a second original edge through it is adjacent — meeting only at a vertex,
  `cg_crossingPoint_ne_vertex` — or remote and transverse, while the carrier edge is a positive multiple of
  both, `geoCornerPolygon_edge_smul` + A2). Hence `edgeSegment X m ⊆ edgeSegment P e` etc. (`gu2_mE_sub`,
  `gu2_pE_sub`, `gu2_qE_sub`) and the **double points of the configuration are those of `P`** by
  `crossingPoint_unique_of_geometry` (`gu2_xmp_eq`, `gu2_xmq_eq`, `gu2_xpq_eq`; no use of
  `G11_carrierEdge_crossingPoint`). Then `clear_frontier`: for an edge `h ∉ {m,p,q}` of `X` inside the original
  edge `h₀`: if `h₀ ∉ {e,f,g}`, A8 (i) directly (frontier form, no side decomposition needed); if `h₀ = e`, a
  point of `Δ` on the line of `e` is on `[x_ef, x_eg] ⊆ edgeSegment X m`, so `h` and `m` — two distinct edges of
  `X` both parallel to `edge P e` — meet: non-adjacent ⇒ transverse (`geoCornerPolygon_transverse`) contradiction,
  adjacent ⇒ at a corner (`meet_next_eq_corner_of_vertex_off` with `geoCornerPolygon_tail_off`) — a vertex of `X`
  in `Δ`, against `clear_vertex` (`gu2_parallel_meet_vertex`); `h₀ = f, g` likewise with `p, q`. `clear_vertex`:
  a corner of `X` is a vertex of `P` (A8 (ii)) or the double point of a selected crossing `v.1 ∈ T`, which is not
  a triangle crossing (those are retained, `htri`), so one of its two edges is foreign
  (`gu2_pair_mem_triangleSupports`) and the closed clearance `gu2_clear_closed` applies.

## Helpers added (all `gu2_`-prefixed, in namespace `RProof`; line numbers in `G11_U2.lean`)

Section `G11Triangle` (before `G11_clear`, L592–L1144):
`gu2_det_smul_smul`, `gu2_det_smul_right`, `gu2_det_self`, `gu2_det_self_smul` (plane determinants);
`gu2_affineIndependent` (`det (b−a) (c−a) ≠ 0 → AffineIndependent ℝ ![a,b,c]`), `gu2_finrank_plane`,
**`gu2_triBasis`** (`AffineBasis (Fin 3) ℝ Plane`), `gu2_triBasis_coe/range/zero/one/two`,
**`gu2_mem_tri_iff`** (`x ∈ convexHull ℝ {a,b,c} ↔ ∀ i, 0 ≤ coord i x`), **`gu2_mem_interior_iff`**
(`↔ ∀ i, 0 < coord i x`), `gu2_tri_isClosed`, `gu2_frontier_coord`, `gu2_mem_segment_of_coord0/1/2`,
`gu2_coord_eq_zero_of_line`, `gu2_frontier_subset_sides`, `gu2_mem_segment_ab/ac/bc_of_line`;
`gu2_three_le_of_remote`, `gu2_remote_of_isCrossing`, `gu2_isCrossing_comm`, `gu2_xPair_comm`, `gu2_visit_congr`,
`gu2_exact_of_eq`, `gu2_triple_perm_feg`, `gu2_triple_perm_gef`, `gu2_edgePoint_sub`, `gu2_edgePoint_comb`,
`gu2_segment_edgePoint`, `gu2_edgeSegment_convex`, `gu2_xpt`, `gu2_tail_not_mem_segment`,
`gu2_param_ne_of_xPair_ne`, `gu2_ne_e/f/g`, `gu2_tri_det`, `gu2_line_e/f/g_mem_segment`, **`gu2_side_clear`**,
**`gu2_no_vertex_of_walk`**, **`gu2_clear`** (A8 with `hG`), **`gu2_clear_closed`** (closed-triangle form).
Section `G11ConfigOf` (before `G11_cfg_hmp`, L1258–L1418; before `G11_cfg_order`; before `G11_cfg_clear_frontier`):
**`gu2_edgeSegment_sub`**, **`gu2_carrierEdge_label`**, `gu2_mE_sub`, `gu2_pE_sub`, `gu2_qE_sub`, `gu2_xmp_eq`,
`gu2_xmq_eq`, `gu2_xpq_eq`, **`gu2_hcfg_of_hpq`**, `gu2_carrierEdge_congr`, `gu2_visitTwin_vef/veg/vfg`;
**`gu2_cfg_hpq`** (L1452); `gu2_pair_mem_triangleSupports`, `gu2_parallel_meet_vertex`, **`gu2_cfg_clear_vertex`**.
Top level (before `G11_card_cases`): `gu2_card_le_two`. Probe: `G11_U2_probe.py` (the `G11_clear` counterexample).

Reusable by other units: `gu2_triBasis`, `gu2_mem_tri_iff`, `gu2_mem_interior_iff`, `gu2_tri_isClosed`,
`gu2_frontier_coord` give U3's D1/D2 (`disc_isDisc`, `triangle_sub_interior`) the interior/frontier of
`G11_triangle` directly (the basis is `![x_mp, x_mq, x_pq]` with `gu2_tri_det`-type non-collinearity; for a
`G11_Config` the determinant follows from `hpq`/`hmp` transversality the same way). `gu2_xmp_eq`, `gu2_xmq_eq`,
`gu2_xpq_eq` identify the configuration's double points with `x_ef, x_eg, x_fg` (U6's F2 needs this for
`G11_liftVisit_σD`).

## Mathlib / library pitfalls met

* **Section variables are included by statement only** (this Lean): `hG` absent in `G11_clear`, `hcfg` in
  `G11_cfg_hpq`, `hn`/`hT` absent in helpers whose statements do not mention them — use `include … in` (done for
  `gu2_edgeSegment_sub`, `gu2_parallel_meet_vertex`, `gu2_tail_not_mem_segment`, `gu2_*_mem_segment`, `gu2_side_clear`,
  `gu2_clear`, `gu2_clear_closed`). Included variables appear in declaration order; the exact signatures of the
  frozen leaves are as in `G11_configOf`'s calls (`G11_cfg_hmq hn hG hs hT q hcef hceg htri hX`, …).
* `G11_carrierEdge_eq_of_adjacent … rfl …` with implicit `{v w}`: the bare `rfl` for `he : v.2.val = w.2.val`
  unifies `w := v`; pass `(v := …) (w := …)`.
* `rw [lemma … _]` with a `_` for a **proof** argument does not match the target's proof term — give it explicitly
  (`gu2_mE_sub` etc.).
* `gu2_edgePoint_comb`'s `P` is not determined by its explicit arguments: call it as `(P := P)`.
* `AffineBasis.interior_convexHull` (Mathlib `Analysis/Normed/Affine/AddTorsorBases.lean`) and
  `affineIndependent_iff_not_collinear_set` (`LinearAlgebra/AffineSpace/FiniteDimensional.lean`) need the two
  imports above; `AffineBasis.convexHull_eq_nonneg_coord` is in `Analysis/Convex/Combination.lean` (imported).
  `Set.Finite.isClosed_convexHull` takes `𝕜` explicitly (`(Set.toFinite _).isClosed_convexHull ℝ`).
  `Module.finrank_prod` + `Module.finrank_self` give `finrank ℝ Plane = 2`; `Matrix.range_cons`,
  `Matrix.range_empty` for `Set.range ![a,b,c]`; `Set.insert_empty_eq` does not exist in this pin (use `ext; simp only`).
* `push_neg` is deprecated → `push Not`. `Finset.card_le_card_of_injOn` (not `Finset.image`, whose `Crossing P`
  vs `{s // IsCrossing P s}` mismatch breaks `rw [Finset.mem_image]`). `Finset.card_le_one`,
  `Finset.card_le_three`, `Finset.card_erase_of_mem`, `Finset.insert_comm`, `Finset.pair_comm`, `segment_eq_uIcc`,
  `Set.mem_uIcc`, `Fin.sum_univ_three`, `AffineMap.lineMap_apply_module'`, `AffineMap.apply_lineMap`,
  `AffineMap.lineMap_same_apply`, `mul_pos_iff_of_pos_right`, `add_sub_cancel : a + (b − a) = b` all as used.
* `decide` on `adjacent i j` for `ZMod 1`, `ZMod 2` needs the definition unfolded
  (`j − i = −1 ∨ j − i = 0 ∨ j − i = 1`); `interval_cases n` works with `i j : ZMod n` in context after `clear`ing
  the hypotheses that mention them.
* `rcases ha with rfl | rfl | rfl` substitutes the **section** variables `e f g` away (the theorem's own `a b`
  survive) — proofs after such a `subst` must not refer to `e f g` by name (`gu2_pair_mem_triangleSupports`).
* Library names used (all exist, namespaces `SM`, `SM.GeoCarrier`, `SM.Carrier`, `RProof.P1`, `RProof.F1`):
  `crossingParameter_spec/_interior_of_geometry`, `crossingPoint_unique_of_geometry`,
  `crossingPoint_injective_of_geometry`, `crossingPoint_mem`, `isCrossing_pair`, `edgePoint_injective`,
  `edgePoint_zero/one`, `edgeInterior_subset_edgeSegment`, `adjacent_distinct_cases`, `remote_symm`,
  `CarrierGeometry.adjacent_edges_meet`, `meet_next_eq_corner_of_vertex_off`, `cg_crossingPoint_ne_vertex`,
  `visitTwin_unique`, `visitTwin_edge_ne`, `visit_crossing_val_eq_pair`, `geoCornerPolygon_apply`,
  `geo_evaluation_eq_outSlot`, `geoCornerPolygon_outEdge_eq_inEdge_of_independent`, `geoMarkSuccessor_on_edge`,
  `geoCornerPolygon_edge_smul`, `geoCornerPolygon_tail_off`, `geoCornerPolygon_transverse`,
  `geo_nonadjacent_meet_crossing`, `three_le_geoCornerCount`, `isTrueCorner_geoCornerMark`, `isTrueCorner_visit`,
  `geoMarkPosition_evaluation_vertex/visit`, `mem_geoCarrierCrossings`, `P1.ne_of_isCrossing_pair`,
  `P1.xPair_ef_ne_eg/ef_ne_fg/eg_ne_fg`, `F1.mem_triangleCrossings`, `EXT_homfly_wall`, `AV_key_lt_of_gauss`.

## Verification log

* `cd work/lean && lake env lean ../drafts/rlane2/G11_U2.lean`: exit 0, 0 errors, 37 `declaration uses sorry`
  (the 49 skeleton leaves minus the 12 proved here), ~10 s.
* `diff G11_Skeleton.lean G11_U2.lean | grep '^<'` → `12 <   sorry` only.
* `grep -c sorry`: 50 → 38.
* `#print axioms` (scratch copy): `G11_le_one_crossing` — `[propext, Classical.choice, Quot.sound, SM.lit_homfly,
  SM.lp_lm, SM.lp_lm_uniqueness]`; `G11_card_cases`, `G11_alt_swap`, `gu2_triBasis` — standard axioms;
  `gu2_clear`, `G11_cfg_order`, `G11_cfg_clear_frontier` — `sorryAx` only via the U1 black boxes (and
  `G11_cfg_hpq` for the `clear_*` leaves).
* `python3 G11_U2_probe.py` → the `G11_clear` counterexample passes all checks.
