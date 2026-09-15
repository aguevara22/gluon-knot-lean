# G11_PLAN — proof plan and skeleton for `GT_G11` (row 173 R:generic_transport, the open fact G11)

Written 2026-09-14 by the G11 architect on Mark's RunPod home pod. Files:

* **`work/drafts/rlane2/G11_Skeleton.lean`** (~1090 lines): `import RProof.X1Rows3`; 49 leaves (`sorry`), assigned to 6 prover units (§7) plus the optional X2;
  three PROVED glue lemmas (`G11_preconnected_meets_frontier`, `G11_edgeSegment_isPreconnected`, `G11_Config.clear_edge`);
  the assembled theorems `RProof.GT_G11_strong_proof : GT_G11_strong`, `RProof.GT_G11_proof : GT_G11` and the row
  theorem `RProof.generic_transport` (fixed name, statement shape of the sibling rows `exterior` /
  `availability_zero_one`: `hn E e f g h3 h4e h4f h4g hE → ∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTransportData hn E e f g δ`)
  are PROVED from the leaves. Compile: `cd work/lean && lake env lean ../drafts/rlane2/G11_Skeleton.lean` — exit 0,
  **0 errors, 0 warnings other than the 49 `declaration uses sorry`**, ~15 s. Nothing under `work/lean` was written.
* this plan.

Verdict: **HARD but FEASIBLE** for `GT_G11_strong` and the row; one branch of the literal `GT_G11` (leaf X2) needs
Gauss parity, which is not in the library — see §0. Realistic size: **3 500–5 500 lines** for the strong statement
(the wave-3 estimate of 1 500–3 000 was optimistic by about ×1.7; the accepted kink insertion of SM/Curl.lean, one
arc and four new vertices, is 4 000 lines, and the smoothing splice of SM/Smoothing.lean 4 600).

---

## §0. Statement finding: `GT_G11` is stronger than what the printed proof (and its consumer) uses

`GT_G11` (work/lean/RProof/X1Rows3.lean:3137) quantifies over `e f g` with `e ≠ f, e ≠ g, f ≠ g`,
`ExactTriangleVisitOrders P P' e f g hs`, the carried divide signs, `¬ IsAlternating`, corresponding retained
crossings and `triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q` — but it has **no hypothesis that
`{e,f}, {e,g}, {f,g}` are crossings of `P`**. Its only consumer, `GT_empty_groupedPoly_eq` (X1Rows3.lean:3247), has
`hef' heg' hfg' : IsCrossing (E.curve t) {e,f} / {e,g} / {f,g}` in scope at the point of use. Consequences:

* If exactly **two** of the three pairs are crossings (say `{e,g}`, `{f,g}`), `ExactTriangleVisitOrders` reverses
  exactly ONE same-edge pair of two distinct crossings (`x_eg`, `x_fg` on `g`) and carries every other same-edge
  order: the Gauss words of `P` and `P'` differ by one adjacent transposition of occurrences of two distinct
  symbols. For a closed generic plane curve the number of occurrences between the two occurrences of any symbol is
  even (Gauss's parity condition); one transposition flips that parity for both symbols, so one of `P`, `P'` is not
  planar — the hypotheses are contradictory and `GT_G11` is vacuously true in this branch. **Gauss parity is not in
  `work/lean`** (grep `parity`: only the R-lane `ParityData` of Cores.lean and `ax_homfly_knot_parity_coeffAt`),
  and it is a global (Jordan-curve-type) theorem: 800–1 500 lines if done from scratch. This is leaf **X2**
  (`G11_two_crossings_absurd`, Skeleton L872) — the one leaf we are **not sure can be closed with the library**
  (it is true).
* If at most **one** pair is a crossing, no same-edge pair is reversed, `AV_key_lt_of_gauss` (X1Rows2.lean:3448)
  carries every key order and `EXT_homfly_wall` (X1Rows2.lean:1395) gives the result directly: leaf **X1**
  (`G11_le_one_crossing`, L848), ~60 lines.
* If all **three** pairs are crossings: the RIII route — the content of this plan.

Therefore the skeleton introduces **`GT_G11_strong`** (L803) = `GT_G11` with the three `IsCrossing` hypotheses
inserted after `f ≠ g`, proves it by the RIII route (`GT_G11_strong_proof`, L835, PROVED from leaves), and:

* re-derives the **row** from `GT_G11_strong` alone by copying the accepted 60-line assembly of X1Rows3 with the strong
  hypothesis threaded through `GT_empty_groupedPoly_eq` (`G11_empty_groupedPoly_eq` L905, `G11_173_empty_row` L945,
  `G11_genericTransportData` L975, **`generic_transport` L988** — no `sorry` of its own, and NOT depending on X2);
* proves the literal **`GT_G11_proof : GT_G11`** (L888) from `GT_G11_strong_proof` + X1 + X2 + the counting leaf X3
  (`G11_card_cases`, L882), and `generic_transport_of_GT_G11` (L1009) through the accepted
  `GT_generic_transport_of_G11` (this path uses X2).

**Recommendation for the port:** either (a) accept `GT_G11_strong` as the library fact and use the re-derived row
(the accepted `def GT_G11` stays as is, unproved but unused), or (b) amend `def GT_G11` in X1Rows3 by the three
hypotheses (a statement-level change of a `def` that is used nowhere else; `GT_empty_groupedPoly_eq`'s call site
already has them) — the executor's decision, to be recorded in work/AUTHOR_NOTES.md. Neither touches
`GenericTransportData` (§6).

---

## §1. The route (Option A: move ONE flat vertex)

Objects, for the distinguished carrier `q` of `T` on `P` (`hG : CarrierGeometry P`, `hT : GeoIndependent hG.cg T`):

* `X := geoCornerPolygon hG.cg T q : LabelledTuple k`, `k = geoCornerCount hG.cg T q ≥ 3`;
  `D₀ := geoPositiveLift hn hG hT q = (Shadow.single ⟨k, _, X⟩).positiveDiagram _` (definitionally,
  `G11_configOf_D₀` L704 is `rfl`). Its three local strands are three edges `m, p, q` of `X` (the carrier edges of
  `x_ef` on `e`, `x_ef` on `f`, `x_eg` on `g`), pairwise crossing at `x_mp = x_ef`, `x_mq = x_eg`, `x_pq = x_fg`,
  with `p` met before `q` along `m` (WLOG, by the symmetry `f ↔ g` at the top level). **The moved strand is `m`
  (= `e`).** Naming the two fixed strands by their order along `m` makes the apex construction case-free (§3, C2).
* `Δ := conv{x_mp, x_mq, x_pq}` (`G11_triangle`, L52). Clearance: `Δ` meets `X` only along `m, p, q`
  (`G11_Config.clear_edge/clear_vertex`), a consequence of R-LOC-2's adjacency (A7): an edge entering `Δ` would
  cross a side strictly between two local visits, or pass through a vertex of `Δ` (a triple point).
* `X₀ := G11_subdiv X m t₁ t₂ t₃` (L146): `m` subdivided by the flat vertices `p_in, m₀, p_out` at
  `t₁ < t(x_mp) < t₂ < t(x_mq) < t₃`; labels `≤ m` unchanged, the new vertices `m+1, m+2, m+3`, labels `> m` shifted by
  3 (`G11_lab`, L155). The four pieces of `m`: `mA=[X m, p_in]`, `mB=[p_in, m₀]`, `mC=[m₀, p_out]`, `mD=[p_out, X(m+1)]`.
  `M₀ := positiveDiagram X₀`. `P(M₀) = P(D₀)` by the accepted flat subdivision (B2).
* `X₁ := Function.update X₀ mid w` with the **apex** `w := m₀ + λ (x_pq − m₀)`, `λ > 1` (L219–L223): the bent strand
  `[p_in, w] ∪ [w, p_out]` passes on the far side of `x_pq`. `M₁ := positiveDiagram X₁`. Only ONE vertex moves, so
  the traversal labels of `M₀` and `M₁` coincide and the outside match is the identity on traversal points (D6).
* `U := G11_discOf C r` (L165): the homothetic enlargement of `Δ` about its centroid with ratio `1+r`
  (`AffineMap.image_convexHull`, `Set.Finite.isCompact_convexHull`, `AffineBasis.interior_convexHull`). It hugs
  `Δ` (every point of `U` is within `r·diam Δ` of `Δ`), so a small `r` keeps it clear of the other edges even when
  they pass close to the sides of `Δ` — a sup-metric square about a point, as in Smoothing.lean, would NOT work
  here (a fat square around a thin triangle contains foreign edges).
* `RIIIData U M₀ M₁` (D8) ⇒ `P(M₁) = P(M₀)` by `homfly_reidemeister_III`.
* The record of `M₁` is the record of `M₀` (= of `D₀`) twisted by the three transpositions `σ` (E1); the record of
  `D_E = geoPositiveLift hn hG' hT' q'` is the record of `D₀` twisted by `σ_P` (F1, from `ExactTriangleVisitOrders`);
  the two twists agree under `liftVisit` (F2); hence `M₁ ≅ D_E` (F3, `CV.recordIsoOfData`) and
  `CV.gausscode_polynomial` closes `P(D_E) = P(M₁) = P(M₀) = P(D_P)`.

Why the six-vertex/two-vertex translation of the W3 report was dropped: with a translated middle segment the two
new crossings sit on a segment that must span from `x_mp'` to `x_mq'`, which for `s → 0` collapses to `x_pq`, while
the connectors must clear `p, q` — this forces either a long segment leaving the clearance region or a case split
on where `x_mp, x_mq` sit relative to the middle piece. The single apex needs 3 flat vertices, gives deterministic
crossing assignments and sign preservation without smallness conditions on `λ` (§3, C4), and its only smallness
clauses are `Θ ⊆ interior U` and the clearance of `U`.

Coordinates used in all truth checks below (`G11_Params` in these terms): `m` = the `x`-axis oriented `+x`,
`x_mp = (0,0)`, `x_mq = (1,0)`, `x_pq = (u,h)` with `h > 0`, `m₀ = (μ,0)`, `0 < μ < 1`, `p_in = (−ε,0)`, `p_out = (1+ε,0)`,
`w = (μ + λ(u−μ), λh)`. Numerical probe `/tmp/g11_probe.py` (20 000 random `u ∈ [−3,4], h, μ, λ ∈ (1,3], ε`):
**0 violations** of C2 (which bent edge each of `p, q` crosses), C4 (sign preservation), D9 (`x_pq` strictly between
the old and new crossing along `p` and along `q`; `x_pq ∈ interior Θ`).

---

## §2. Unit table

| unit | leaves (Skeleton lines) | content | est. lines | risk |
|---|---|---|---|---|
| **A** carrier → configuration | A2–A4, A6, A7–A11, A12–A15 (`G11_cfg_hmp/hmq/hpq/order/trans/clear_frontier/clear_vertex`) | carrier edges of the local visits, adjacency ⇒ same carrier edge, crossings of `X`, signs, clearance; the six swap lemmas | 700–1 000 | medium (block machinery of GeoPositiveLift) |
| **B** flat subdivision | B1 `X₀_generic` L233, B2 `homfly_M₀` L243, B3 `X₀_cross_*` L248–254, B4 `exists_Ψ₀` L275 | `Reindexed` + `appendVertex` ×3; record of `M₀` = record of `D₀` | 500–700 | low–medium (CS3 toolkit exists; B4 needs a visit bijection from `subdivPt`) |
| **C** moved polygon | C1 `X₁_generic` L292, C2 `X₁_cross_pC/qB` L303/306, C3 `X₁_cross_iff` L311, C4 `X₁_sign_*` L320/323 | genericity of `X₁`, its crossings, the over bits | 700–1 100 | medium (as K2 §"Genericity of the new shadow", 400 lines, ×1.5 for two bent edges vs two fixed strands) |
| **D** disc and RIII site | D1–D2 L330/334, D3–D4 L339/351 (+`X₁_cross_pq` L347), D5 L360/363, D6 L370, D7 L376, D8 `riii` L390 | `IsDisc U`, inner crossings, `Clean`, `MoveMatch`, `ArcCover`s, `RIIIData` (height naming, `Separates`, `OverOn`, `BeforeOn` reversals) | 1 200–1 800 | medium–high (largest unit; Smoothing §5–6e and K2 are the templates) |
| **E** record of `M₁` | E1 `exists_Ψ₁` L407 | occurrence bijection `M₀ ≃ M₁`, twins/bits/signs, the `σ`-twisted cyclic order (gap argument) | 400–600 | medium |
| **P** parameters | `G11_exists_params` L444 | clearance radius `ρ > 0`, then `t₁, t₃, λ−1, r` small | 200–300 | low |
| **F** assembly | F0 `G11_param_ne` L823, F1 `G11_twisted_key_lt` L726, F2 `G11_liftVisit_σD` L736, F3 `G11_recordIsoData` L755 | the twisted key transport, `liftVisit ∘ σD = σ_P ∘ liftVisit`, CV:def:record (a)–(d) | 350–500 | low–medium |
| **X** branches of the literal `GT_G11` | X1 L848, X2 L872, X3 L882 | `≤ 1` crossing (record iso), `= 2` (Gauss parity — FLAGGED), counting | X1 60, X3 40, **X2 800–1 500 or unprovable in-library** | X2 high |
| assembled (PROVED) | `core_of_params` L420, `G11_core` L448, `G11_configOf` L678, `G11_strong_case` L776, `GT_G11_strong_proof` L835, `GT_G11_proof` L888, `G11_*_row` L905–L975, `generic_transport` L988 | — | done | — |

Total for `GT_G11_strong` + row: **3 500–5 500 lines**, 5–7 prover units of the wave size. Dependencies:
B, C, D, E, P depend only on `G11_Config`/`G11_Params` (pure plane geometry, reusable for the RII moves G10 of rows
174/176 with a two-strand analogue); A and F depend on the carrier layer; X on nothing else.

---

## §3. Leaves

Format: **name** (line) — statement in words — proof sketch — tools — estimate — truth check.

### Unit A — from the distinguished carrier to a triangle configuration

* **A2 `G11_carrierEdge_spec`** (L469) — the carrier edge `G11_carrierEdge v` (L462: the corner index `k` chosen by
  `geo_mark_block`) carries `crossingPoint v.1` and is a positive multiple of `edge P v.2.val`. Sketch: unfold the
  `Classical.choose`; `geo_mark_block` (SM/GeoPositiveLift.lean:296) gives `k, r` with the block membership and
  `traversalEvaluation P (geoMarkPosition hP (Sum.inr v)) ∈ edgeSegment X k`; that evaluation is `crossingPoint v.1`
  (`geometricVisitPosition_evaluation`, SM/GeometricVisits.lean:19); the direction from `geoCornerPolygon_edge_smul`
  (SM/GeoCornerPolygon.lean:400) and `GeoBlockInterior.visit_edge` (GeoPositiveLift.lean:160: the out-slot edge of
  the block is `v.2.val`). 80–120 lines. True by construction.
* **A3 `G11_carrierEdge_eq_of_adjacent`** (L477) — two retained visits on one original edge with no visit of `P`
  strictly between them lie on one carrier edge. Sketch: a corner strictly between them along the traversal would be
  a `T`-visit (a crossing of `P` on that edge between them — excluded) or a vertex of `P` (not in the open edge:
  `crossingPoint_interior`, SM/Crossings.lean:52, and `CarrierGeometry.vertex_not_mem_edge`); so the two marks are in
  one block: `geo_prevCorner_unique`/`geo_block_mark_eq` (GeoPositiveLift.lean:200–240) with the smoothing successor
  stepping along the edge (`geoSmoothingSuccessor_visit_of_not_mem`, FlatCarriersDefs.lean:250). 150–250 lines.
  True (block structure of a carrier edge = maximal run of the traversal without corner).
* **A4 `G11_carrierEdge_isCrossing`**, **`G11_carrierEdge_crossingPoint`** (L487, L493) — the carrier edges of the
  two visits of a retained crossing cross in `X` at the same double point. Sketch: `geoCarrierCrossingEquiv`
  (GeoPositiveLift.lean:698) + `crossingPoint_geoCarrierCrossingEquiv` (:705), `single_crossingPoint`
  (LinkDiagram.lean:1703), `Shadow.single_isCrossing_iff`; the strands of the lift crossing are the block edges of the
  two visits (A2), and `crossingPoint_unique` (Crossings.lean:63) with `CarrierGeometry`-genericity of `X`
  (`geoCarrierShadow_generic`) identifies the point. 100–150 lines. True.
* **A6 `G11_carrierSign`** (L502) — `crossingSign X (ce v) (ce w) = crossingSign P v.2.val w.2.val`. Sketch: A2's
  positive multiples, `det` bilinear (`det_smul_smul_plane`, CS3.lean:1053), `sign_mul`, `sign_pos`. 30 lines. True.
* **A7 `G11_no_visit_between`** (L518) — no visit `y` of `P` on `e` has its parameter strictly between those of
  `x_ef` and `x_eg` on `e`. Sketch: `ExactTriangleVisitOrders` (SM/TripleVisitExchanges.lean:18) on the pairs
  `(x_ef, y)` and `(y, x_eg)` — unions `≠ {e,f,g}` since `y.1.val ∪ {e,f}` would have to equal `{e,f,g}`, forcing
  `y.1.val = {e,g}`, i.e. `y = x_eg` — carries both orders to `P'`, while the pair `(x_ef, x_eg)` is reversed;
  transitivity of `<` contradicts. 60–100 lines (Finset bookkeeping on the unions). **True** (this is exactly why
  R-LOC-2 (2b) speaks of "adjacent" visits).
* **A8 `G11_clear`** (local form, as adopted) — (i) no edge of `P` other than `e, f, g` meets the **frontier** of
  the closed triangle `conv{x_ef, x_eg, x_fg}`; (ii) no vertex of `P` lies in the closed triangle. Sketch (i): the
  frontier of the triangle is the union of its three sides (`AffineBasis.interior_convexHull` +
  `convexHull_eq_nonneg_coord`: frontier = some barycentric coordinate `= 0`), the side `[x_ef, x_eg]` lies in the
  open edge `e`; a point of a foreign closed edge `h` on it is a common point of `h` and `e`: if `remote h e` it
  is THE double point of `{h, e}` (`crossingPoint_unique`), a visit on `e` with parameter in `[t(x_ef), t(x_eg)]`
  — strictly inside excluded by A7, an endpoint excluded by `crossingPoint_injective_of_geometry`; if `h` is
  adjacent to `e` the common point is a shared vertex, not on the open edge (`CarrierGeometry.vertex_not_mem_edge`
  for the other endpoint, `edgePoint_injective` for the parameter). (ii): a vertex on the frontier is on a side ⊆
  a closed edge `e` — a non-incident vertex is excluded by `vertex_off`, the endpoints `P e, P (e+1)` have parameters
  `0, 1 ∉ [t(x_ef), t(x_eg)] ⊆ (0,1)`; a vertex `P i` strictly inside: the endpoints of `e, f, g` are on the lines of
  the sides and off the sides, hence outside the triangle, so `i`'s incident edges are foreign; walk forward
  from `i`: `Nat.find` the least `k ≥ 1` with `P (i + k) ∉ Δ` (exists: `k = (e − i).val` reaches `P e`); the edge
  `i + k − 1` has its tail in `Δ` and head outside, so it meets the frontier (`G11_preconnected_meets_frontier`,
  proved in the skeleton) — a foreign edge (its tail is in `Δ`, the tails of `e, f, g` are not), contradicting (i).
  No IVT along the polygon; the only topology is the proved segment lemma. 250–350 lines. **True**.
* **A9 `G11_alt_swap`** (L542), **A10 `G11_exact_swap`** (L547), **`G11_triangleCrossings_swap`** (L551), **A11
  `G11_alt_crossingSign`** (L556) — relabelling `f ↔ g` and the two sign notations. Sketch: `IsAlternating sa sb sc
  ↔ sa = sc ∧ sb = −sa` (Cores.lean:490) with `crossingSign_swap` (Crossings.lean:82) and `strandSign = sign (CV.G5)`
  (`= crossingSign` by `rfl`, W3 report); `decide` over `SignType` after `cases`; `{e,g,f} = {e,f,g}` as Finsets
  (`Finset.insert_comm`/`pair_comm`); `triangleSupports e g f = triangleSupports e f g`. 20–40 lines each. True.
* **A12 `G11_cfg_hmp`, `G11_cfg_hmq`, `G11_cfg_hpq`** (L623–L631) — `{m,p}`, `{m,q}`, `{p,q}` are crossings of `X`.
  Sketch: A4 for `x_ef` (`m, p` are the carrier edges of its two visits); for `{m,q}`: A3 puts `x_eg` on `e` on the
  carrier edge `m` (A7 gives the adjacency hypothesis), A4 for `x_eg`; for `{p,q}`: A3 on `f` (`x_ef, x_fg`) and on
  `g` (`x_eg, x_fg`), A4 for `x_fg`. 60–100 lines. True.
* **A13 `G11_cfg_order`** (L638) — parameter of `x_mp` on `m` `<` parameter of `x_mq` on `m`. Sketch: A2 gives
  `edge X m = c • edge P e`, `c > 0`, and `X m = edgePoint P e t₀`; a point `edgePoint P e t` on the carrier edge has
  carrier parameter `(t − t₀)/c`, increasing in `t`; `crossingParameter_spec` (Crossings.lean:75) and
  `edgePoint_injective` (Crossings.lean:87) identify the parameters; `hord`. 80–120 lines. True.
* **A14 `G11_cfg_trans`** (L648) — `¬ IsAlternating` on the three crossing signs of `X`. Sketch: A6 ×3 + A11. 20 lines.
* **A15 `G11_cfg_clear_frontier`, `G11_cfg_clear_vertex`** (L~700, L~710) — the local clearance for `X`. Sketch:
  every edge of `X` is a sub-segment of an edge of `P` (`geoCornerPolygon_edgeSegment` GeoCornerPolygon.lean:731,
  `geo_mark_block`, `geoSmoothingSegment_incoming_mem_edgeSegment` GeoCarrierCrossings.lean:161); an edge of `X`
  other than `m, p, q` is a sub-segment of `h ∉ {e,f,g}` (A8 (i)) or of `e` (resp. `f, g`) disjoint from the local
  side (its block is cut off by a corner; by A3 the block of `m` contains both local visits, and the line of `e`
  meets `Δ` only in the side), so it misses the frontier; the double points of `X` are those of `P` (A4). Vertices of
  `X` are vertices of `P` (A8 (ii)) or `T` double points (not in `Δ`: on `e` between the local visits excluded by
  A7, elsewhere by A8 (i) and `crossingPoint_injective_of_geometry`). 200–300 lines. True. The closed-triangle
  form `G11_Config.clear_edge` used by units P, C, D is PROVED glue in the skeleton (segment preconnectedness).

### Unit B — the flat subdivision

* **B1 `X₀_generic`** (L233) — `single ⟨k+3, _, X₀⟩` is generic. Sketch: `X₀` is `Reindexed` to
  `appendVertex (appendVertex (appendVertex (shift r X) u₁) u₂) u₃` (put `m` last, `shift`; then the three new points
  in the order `p_in`, then `m₀` on `[p_in, X(m+1)]`, then `p_out` on `[m₀, X(m+1)]`, with rescaled parameters);
  `single_generic_shift` (CS3.lean:526), `single_generic_appendVertex` (CS3.lean:613) ×3 with `hoff` (the new point
  is on `m` only: `X₀` clearance from `G11_Config.clear_edge` is not even needed — a point of the open edge `m` is on
  no other closed edge by genericity `tail_off`/transversality: `Generic.common_point_unique`), then
  `single_generic_of_reindexed` (CS3.lean:533). The `Reindexed` identity is the label arithmetic of `G11_subdiv` vs
  `insertIndex`/`insertedIndex` (SM/InsertionIndices) — the tedious part. 250–350 lines. True.
* **B2 `homfly_M₀`** (L243) — `P(M₀) = P(D₀)`. Sketch: `homfly_positiveDiagram_single_of_reindexed` (CS3.lean:543)
  and `homfly_positiveDiagram_single_appendVertex` (CS3.lean:1262) ×3 along the same chain. 60–100 lines given B1's
  chain (factor the chain out as a shared lemma). True.
* **B3 `X₀_cross_mp/mq/pq`** (L248–L254) — the three local crossings of `X₀`: `{mB, p'}` (since
  `t₁ < t(x_mp) < t₂`, `x_mp ∈ edgeSegment X₀ mB`), `{mC, q'}`, `{p', q'}`. Sketch: `IsCrossing` = remote labels +
  segments meet (Crossings.lean:12); `edgeSegment X₀ mB = [edgePoint X m t₁, edgePoint X m t₂]`; remoteness in
  `ZMod (k+3)` from remoteness in `ZMod k` (`remote_insertIndex_of_remote`, CS3.lean:902, or direct `ZMod.val`
  arithmetic on `G11_lab`). 80–120 lines. True.
* **B4 `exists_Ψ₀`** (L275) — an occurrence bijection `D₀ ≃ M₀` carrying twins, over bits, signs, cyclic order,
  and mapping the six local occurrences to the six named ones. Sketch: the CS3 toolkit `subdivPt` (CS3.lean:644,
  bijective :708), `traversalKey_subdivPt` (:821) / `traversalBetween_subdivPt` (:886),
  `traversalEvaluation_subdivPt` (:869), `det_edge_subdivPt_pos_iff` (:1067), `exists_crossing_overVisit_eq`
  (:1083) — composed three times along B1's chain, or (cleaner) a direct one-shot version for `G11_subdiv`: the
  traversal-point map `(i, s) ↦` (`(G11_lab i, s)` for `i ≠ m`; on `m`: piecewise rescaling to `mA..mD`) is a
  strictly increasing re-coordinatization of the circle (a 4-piece `subdivKeyMap`), evaluation-preserving; visits
  correspond through their traversal points (`visitPt`, `eval_visitPt`, `Generic.common_point_unique`); over bits
  because both diagrams are positive and directions are positive multiples; signs all `1`. 300–450 lines. True
  (`reparam_positiveDiagram_single_appendVertex`, CS3.lean:1166, is the accepted precedent).

### Unit C — the moved polygon `X₁`

* **C1 `X₁_generic`** (L292) — `single ⟨k+3, _, X₁⟩` is generic. Sketch via `Shadow.single_generic_of`
  (LinkPositiveLift.lean:160): `regular`: edges `mB' = w − p_in`, `mC' = p_out − w` nonzero (`λh > 0`) and not
  antiparallel to `mA`, `mD` (their `y`-components are `±λh ≠ 0`) nor to each other (`det(mB', mC') = −λh(1+2ε) ≠ 0`
  in the coordinates of §1); every other consecutive pair as in `X₀`. `tail_off`: `w ∉` any closed edge — `w ∈ Θ°
  ⊆ interior U`, and `U` meets no other edge (`disc_clear_edge`), while the edges `mA, mD, p', q'` meet `Θ` only on
  the base or at the two new crossing points (C2), none equal to `w`; old vertices are not on `mB', mC'` (they lie
  in `U`; `disc_clear_vertex`). `transverse`: `mB'`/`mC'` against `p'`, `q'`: the explicit determinants of C4
  (nonzero); against any other edge `h`: `edgeSegment h ∩ U = ∅` so the segments do not meet; against `mA`/`mD`:
  adjacent or (for `mB'` vs `mD`) disjoint (`mD ∩ Θ = {p_out}` is not on `mB'` since `mB'`'s points have `y ≥ 0`
  with `y = 0` only at `p_in ≠ p_out`). `no_triple`: interiors of three distinct edges meeting: the only points of
  `interior mB'`, `interior mC'` on other edges are the two new crossings (C2) and `w` is on nothing; a triple
  point among unmoved edges is one of `X₀`. 500–800 lines (template: Curl.lean K2 §"Genericity of the new shadow"
  L5154–L5565, 400 lines for 4 new edges). True (probe: the two bent edges each cross exactly one of `p, q`).
* **C2 `X₁_cross_pC`, `X₁_cross_qB`** (L303, L306) — `p'` crosses `[w, p_out]` and `q'` crosses `[p_in, w]`.
  Sketch (coordinates of §1): the line `p` through `(0,0)` and `(u,h)` meets the segment from `w = (μ+λ(u−μ), λh)`
  to `p_out = (1+ε, 0)` at the parameter `s = (λh·(…))` — solve the 2×2 system; `0 < s < 1` follows from `μ < 1`,
  `λ > 1`, `ε > 0` (numerically confirmed on 20 000 samples). Concretely `p ∩ [w, p_out]` at height
  `y = λh(1+ε−μ)/((1+ε−μ)+λ(1−μ)) ∈ (0, λh)`. Remoteness of the labels `p'` vs `mC` (and `q'` vs `mB`) from
  `remote p m` in `X` (`p ≠ m±1`) — note `p'` may be adjacent to `mA` or `mD` in `X₀` if `p = m ± 1` in `X`; but
  `IsCrossing X {m,p}` already gives `remote m p`, so `p'` is at distance `≥ 2` from all of `mA..mD`... **check:**
  `p = m + 2` in `X` gives `p' = m + 5` and `mD = m + 3`, distance 2 ✓; `p = m − 1` is excluded by `remote`. 150–250
  lines. **True** (probe).
* **C3 `X₁_cross_iff`** (L311) — for a pair not containing `mB`, `mC`: crossing of `X₁` iff crossing of `X₀`.
  Sketch: `X₁ i = X₀ i` for `i ≠ mid`, so `edgeSegment X₁ i = edgeSegment X₀ i` for `i ∉ {mB, mC}`
  (`Function.update_of_ne`); `IsCrossing` depends only on the two segments and the labels. 60–100 lines. True.
* **C4 `X₁_sign_pC`, `X₁_sign_qB`** (L320, L323) — the new crossing signs equal the old ones. Sketch (coordinates
  of §1, `d_m = (1,0)`, `d_p = (u,h)`, `d_q = (u−1,h)`): `det(d_p, d_m) = −h`; `det(d_p, p_out − w) =
  −h(1 + ε − μ + λμ) < 0`; `det(d_q, d_m) = −h`; `det(d_q, w − p_in) = −h(λ(1−μ) + μ + ε) < 0`. Both signs are the
  sign of `−h`, for ALL `λ > 1, ε > 0, 0 < μ < 1`, independent of `u`. In Lean: express `w − p_in`, `p_out − w` as
  combinations of `d_m`, `d_p`, `d_q` (`x_pq = x_mp + t_p d_p = x_mq + t_q d_q`) and use bilinearity; avoid
  coordinates by working with `det(d_p, ·)` linear. 100–150 lines. **True** (probe, and the closed forms above).

### Unit D — the disc and the Reidemeister-III site

* **D1 `disc_isDisc`** (L330) — `IsDisc U`. Sketch: `U = h '' Δ` with `h` the homothety (an affine map);
  `AffineMap.image_convexHull` (Mathlib Analysis/Convex/Hull.lean:192) gives `U = convexHull (h '' {3 pts})`;
  convex (`convex_convexHull`), compact (`Set.Finite.isCompact_convexHull`, Analysis/Convex/Topology.lean:347);
  nonempty interior: the three points are affinely independent (the three double points are not collinear:
  `det(d_p, d_q) ≠ 0` and they are on the three distinct lines) ⇒ an `AffineBasis (Fin 3) ℝ Plane`
  (`AffineBasis` from `AffineIndependent` + `affineSpan = ⊤` via `finrank ℝ (ℝ × ℝ) = 2`), and
  `AffineBasis.interior_convexHull` (Mathlib Analysis/Normed/Affine/AddTorsorBases.lean:57): `interior = {x | ∀ i,
  0 < b.coord i x}` contains the centroid. 150–250 lines. True.
* **D2 `triangle_sub_interior`** (L334) — `Δ ⊆ interior U`. Sketch: for `y ∈ Δ`, `y = h(z + (y−z)/(1+r))` with the
  pre-image strictly inside (its barycentric coordinates are `(β_i + r/3)/(1+r)·…` — all `> 0` when `β_i ≥ 0`,
  `r > 0`); by the interior formula. 60–100 lines. True.
* **D3 `inner_M₀`** (L339) — the double points of `M₀` in `interior U` are exactly the three local ones. Sketch:
  `⇐`: D2. `⇒`: a double point of `X₀` lies on two edges; if one of them is not `mA..mD, p', q'`, it is off `U`
  (`disc_clear_edge`); the pairs among `{mA, mB, mC, mD, p', q'}` that cross are exactly `{mB,p'}, {mC,q'}, {p',q'}`
  (collinear `m`-pieces do not cross; `mA`, `mD` meet `p'`/`q'` nowhere since `p` meets the line of `m` only at
  `x_mp ∈ mB`). `single_crossingPoint` (LinkDiagram.lean:1703) to pass between shadow and polygon. 150–250 lines. True.
* **`X₁_cross_pq`** (L347) — from C3. 10 lines.
* **D4 `inner_M₁`** (L351) — the double points of `M₁` in `interior U` are `x_pq`, `x_mp'`, `x_mq'`. Sketch: as D3
  with C2/C3; a double point on a bent edge is one of the two new ones (C1's `no_triple` analysis). 150–250 lines. True.
* **D5 `clean_M₀`, `clean_M₁`** (L360, L363) — `Clean U D`: frontier injectivity and `exits`. Sketch (template
  `Smoothing.clean_D`, Smoothing.lean:2029–2075): a traversal point evaluating to `∂U` lies on `p'`, `q'` or an
  `m`-piece (`disc_clear_edge`); two such points with the same plane point are on the same strand (then
  `edgePt_injective`, `Pt_ext` Smoothing.lean:1955) or on two different strands meeting at a double point — which is
  in `interior U` (D3/D4), not on `∂U`. `exits`: the vertex `X 0`... use any vertex (`disc_clear_vertex`). 150–250
  lines. True.
* **D6 `exists_moveMatch`** (L370) — `MoveMatch U M₀ M₁`. Sketch: `φ := Equiv.subtypeEquiv (Equiv.refl _) (fun p
  => …)` on `Outside U` — the same traversal point is outside on both sides: if its strand is `mB` or `mC`, its
  evaluation on either side lies in `Θ ⊆ interior U` (`theta_sub`; `[p_in, m₀] ∪ [m₀, p_out]` = the base of `Θ`,
  `[p_in, w] ∪ [w, p_out]` the two other sides — all in `Θ`), so it is not outside on either side; otherwise
  `eval` agrees (`Function.update_of_ne`). `eval_eq`: same argument. `dir_pos`/`dir_pos_before`: the strand (and
  the arriving strand) of a point strictly outside `U` is unmoved — a point on `mA` at its head `p_in` is on `∂U`?
  No: `p_in ∈ Θ ⊆ interior U`, so a point of `mA` strictly outside `U` has parameter `< 1` and its strand-before is
  `mA` or the previous edge, both unmoved; take `l = 1`. `ψ`: outer crossings are the pairs not involving `mB, mC`
  (D3/D4 + C3), `Equiv.subtypeEquiv` on `Finset`-valued crossings with `X₁_cross_iff`; `over_eq/under_eq`: both
  diagrams positive, unmoved directions equal ⇒ same over strand (`positiveDiagram_det_pos`, LinkPositiveLift.lean:
  103, uniqueness of the positive strand by `det_swap`). `e := Equiv.refl (Fin 1)`. 300–450 lines (template:
  Smoothing.lean:4319–4600 `origPt/outsideEquiv/outerEquiv/outsideMatch`, 280 lines, and Curl.lean:6719–7195). True.
* **D7 `exists_arcCovers`** (L376) — the three arcs on each side, disjoint, covering the trace inside `U`, with
  matching ends. Sketch: the line of `p'` meets `U` (convex compact, `p'`'s endpoints outside by
  `disc_clear_vertex`) in a closed parameter interval `[θ_in, θ_out]` with the ends on `∂U` and the open interval in
  `interior U` — for the triangle `U` the barycentric coordinates along `p'` are affine in the parameter, each either
  constant (`p'` parallel to a side — here the side of `U` parallel to `p`; its coordinate is then the constant
  margin `> 0`) or strictly monotone; so `{θ | all ≥ 0}` is an interval whose interior maps to `{all > 0}` =
  `interior U` (D1's formula). Same for `q'`. The `m`-arc: start on `mA` at the entry parameter, stop on `mD` at the
  exit parameter, inner points: the rest of `mA`, all of `mB, mC` (in `Θ ⊆ interior U`) and the beginning of `mD`
  (convexity of `interior U`: `p_in, m₀ (or w), p_out ∈ interior U`, and a segment from a frontier point to an
  interior point is interior except at its end — `Convex.openSegment_interior_closure_subset_interior`). `IsArc`
  (LinkMoves.lean:216), `ArcCover.mem_iff`: a traversal point evaluating into `U` is on `p', q'` or an `m`-piece
  (`disc_clear_edge`) within the intervals; `disjoint`: different strands or disjoint parameter intervals.
  `Arc.Inner`/`Mem` through `traversalBetween` across several edges: no accepted helper spans several edges
  (`arc_inner_iff_of_same_edge`, Smoothing.lean:1970, is one-edge) — write `arc_mem_iff_of_key` via
  `traversalKey_lt_iff` (Traversal.lean:57). The six end equalities: identical traversal points and unmoved strands.
  400–600 lines. True.
* **D8 `riii`** (L390) — `RIII M₀ M₁`. Sketch: `⟨U, Or.inl ⟨data⟩⟩` with `RIIIData` (LinkMoves.lean:639): `frame :=
  ⟨disc_isDisc, clean_M₀, clean_M₁⟩`, `out := moveMatch`; the arcs of D7 named by HEIGHT: from `G11_Config.trans`
  the over-relation on `{m,p,q}` (positive diagram: `i` over `j` iff `0 < det(edge i, edge j)`, LinkPositiveLift.lean:
  103) is a strict total order — six cases on the permutation (a helper `riiiData_of_arcs` taking the three arcs, the
  three crossings and the pairwise data indexed by `Fin 3` plus a permutation, instantiating the 60 fields once);
  `inner_iff/inner_iff'` from D3/D4; `sep_*`: each local crossing joins the right two arcs (its two strands carry
  the arcs: `OverOn`/`UnderOn` via `visitPt` of the over/under visit on the arc — `arc_mem_iff_of_key`);
  `top_*`/`mid_*` from the signs (`X₁_sign_pC/qB` for the `M₁` side, the same `det` for the unmoved pair `{p',q'}`);
  `rev_a/rev_b/rev_c` (`BeforeOn`, LinkMoves.lean:299): along `p'` the parameters of `x_mp`, `x_pq`, `x_mp'` satisfy
  `x_pq` strictly between the other two (the line `p` enters `Θ` at `x_mp` on the base and leaves at `x_mp'` on the
  side `[w, p_out]`, and `x_pq ∈ Θ°` — `Θ` convex, so the parameter interval of `p ∩ Θ` is `[t(x_mp), t(x_mp')]`),
  hence `BeforeOn p' x_mp x_pq ↔ ¬ BeforeOn p' x_mp' x_pq`, i.e. exactly the reversal `rev` (in either orientation
  of `p`); same for `q'`; along the `m`-arc: in `M₀` `x_mp` (on `mB`) precedes `x_mq` (on `mC`), in `M₁` `x_mq'` (on
  `mB`) precedes `x_mp'` (on `mC`) — by the edge order `mB < mC` of the traversal keys. 350–500 lines. **True**
  (probe D9: `x_pq` strictly between along both `p` and `q`, 20 000 samples).

### Unit E — the record of `M₁`

* **E1 `exists_Ψ₁`** (L407) — `Ψ₁ : M₀ ≃ M₁` on occurrences: twins, over bits, signs carried; and for all
  `u v w : D₀`-occurrences, `M₁.VisitBetween (Ψ₁ (Ψ₀ u)) … ↔ D₀.VisitBetween (σD u) …`. Sketch: crossings of `M₁`
  ↔ crossings of `M₀`: identity off `mB, mC` (C3), `{mB,p'} ↦ {mC,p'}`, `{mC,q'} ↦ {mB,q'}`; visits: keep the strand
  `p'` (resp. `q'`), send the `m`-piece visit to the other bent edge. Twins: by construction. Over bits: C3 (same
  `det`) and C4. Signs: all `1` (`positiveDiagram_sign`). Cyclic order — the **gap argument** on traversal keys
  (`visitCoord`, LinkDiagramRecord.lean:181, both on the circle `[0, k+3)`): (i) an occurrence off the six local
  ones has the same key on both sides (same strand, same crossing point ⇒ same `crossingParam` by
  `edgePoint_injective`); (ii) the two occurrences on `p'` (`x_mp` and `x_pq` in `M₀`; `x_pq` and `x_mp'` in `M₁`)
  lie in the parameter interval of `p' ∩ U`, which contains no other occurrence (D3/D4), and their order is reversed
  (D8's `rev`); likewise on `q'`; (iii) on the `m`-arc the piece `mB` carries exactly one occurrence on each side
  (`x_mp` in `M₀`, `x_mq'` in `M₁`), and `mC` likewise (`x_mq`, `x_mp'`) — keys in `[mB.val, mB.val+1)` resp.
  `[mC.val, mC.val+1)`. Hence for every pair `(x, y)` of `M₀`-occurrences, `key₀ (σ₀ x) < key₀ (σ₀ y) ↔ key₁ (Ψ₁ x) <
  key₁ (Ψ₁ y)` where `σ₀ = Ψ₀ ∘ σD ∘ Ψ₀⁻¹` (case analysis: both off the six — equal keys; one on `p'`'s gap and the
  other outside it — the gap is an interval free of other keys so the comparison is the same for both members of
  the pair; both in the same gap — the reversal; different gaps/pieces — fixed order of disjoint intervals). Then
  `GT_cyc_congr_of_lt` (X1Rows3.lean:1767) turns pairwise `<`-agreement into `cycBetween`-agreement, and `Ψ₀`'s
  cyclic-order clause and the six named images (to identify `σ₀` with the swaps of the `w_*`) finish. The
  commutation `Ψ₀ ∘ σD = σ₀ ∘ Ψ₀` is `Equiv.swap` conjugation (`Equiv.swap_apply_apply` /
  `Equiv.symm_trans_swap_trans`). 400–600 lines (precedent: Smoothing.lean §8 "record bridge" and Curl.lean:7211
  "strictly increasing coordinate map"; our gap argument avoids an explicit monotone map). True.

### Unit P — the parameters

* **`G11_exists_params`** (L444) — `Nonempty (G11_Params C)`. Sketch: `K := ⋃_{h ∉ {m,p,q}} edgeSegment X h ∪
  {X i}` is compact (finite union of segments/points), disjoint from `Δ` (`clear_edge/clear_vertex`), `Δ` compact ⇒
  `∃ ρ > 0, ∀ x ∈ K, ∀ y ∈ Δ, ρ < dist x y` (`exists_pos_forall_lt_edist`, Mathlib
  Topology/MetricSpace/HausdorffDistance.lean:236, converted from `edist`). `U = h_r '' Δ` satisfies `∀ y ∈ U, ∃ δ ∈
  Δ, dist y δ ≤ r · D` with `D := max_i dist(centroid, vertex_i)` (`y = z + (1+r)(δ − z)`, `y − δ = r(δ − z)`,
  `‖δ − z‖ ≤ D` on `Δ` by convexity of the norm ball); choose `r := ρ/(2D)` ⇒ `disc_clear_*`. Then `t₁ := (t(x_mp)
  + 0)/2`-type choices are not enough — need `p_in, p_out, w ∈ interior U`: `interior U ⊇ Δ` (D2) is open, so a
  neighbourhood of `Δ` of some radius `η > 0` is inside (`IsCompact.exists_thickening_subset_open`, Mathlib); choose
  `t₁ ∈ (0, t(x_mp))` with `dist(p_in, x_mp) < η`, `t₃` likewise, `λ ∈ (1, 1 + η/‖x_pq − m₀‖)`, `t₂` the midpoint
  of `t(x_mp), t(x_mq)`; `Θ = conv{p_in, w, p_out} ⊆ interior U` by convexity of `interior U` (`Convex.interior`).
  200–300 lines. True.

### Unit F — assembly

* **F0 `G11_param_ne`** (L823) — `t(x_ef) ≠ t(x_eg)` on `e`. Sketch: equal parameters ⇒ equal double points
  (`crossingParameter_spec`) ⇒ equal crossings (`crossingPoint_injective_of_geometry`) ⇒ `{e,f} = {e,g}` ⇒ `f = g`.
  20–30 lines. True.
* **F1 `G11_twisted_key_lt`** (L726) — `key (σ_P u) < key (σ_P v) ↔ key' (τ u) < key' (τ v)` for ALL visits `u v`
  of `P`. Sketch: `geometricVisitKey = traversalKey (edge label, parameter)` (GeometricVisits.lean:39,
  Traversal.lean:15), `traversalKey_lt_iff` (Traversal.lean:57): different edges compare by `ZMod.val` of the label —
  `σ_P` and `τ` (`visitTransport_edge`, CrossingTransport.lean:36) preserve labels; same edge: `ExactTriangleVisitOrders`
  carries the parameter order except on the three local pairs (`= {e,f,g}` unions), which `σ_P` exchanges (so
  `key (σ_P u) < key (σ_P v)` is `key v' < key u'` for the partners — the reversed clause); a local visit `u` on `e`
  against a non-local `v` on `e`: `σ_P u` is the other local visit `u'` on `e`, adjacent to `u` (A7), so `u' < v ↔
  u < v`, and `u < v ↔ τu < τv` (non-local pair). Reuse `AV_key_lt_of_gauss` (X1Rows2.lean:3448) for every
  non-reversed pair. 150–250 lines. True.
* **F2 `G11_liftVisit_σD`** (L736) — `liftVisit (σD v) = σ_P (liftVisit v)` on the occurrences of the lift.
  Sketch: `σD` is the conjugate of three swaps of the occurrences `v_mp …` (L111–L116); `liftVisit` is injective and
  its values on the six local occurrences are the six `G11_v**` (their crossings: `geoCarrierCrossingEquiv` sends
  `{m,p}` to `x_ef` by the double point, `liftVisit_fst` (PieceIntrinsic.lean:598) / `parentCrossing`; their edges: the
  block edge of `m` is `e` (A2)); off the six, both sides are `liftVisit v` (`Equiv.swap_apply_of_ne_of_ne`). 150–200
  lines. True.
* **F3 `G11_recordIsoData`** (L755) — from the core's output and F1/F2, a bijection `Φ : D₁ ≃ D_E` with
  `CV.IsRecordIsoData`. Sketch: `Λ : D₀ ≃ D_E` := `liftVisitEquiv` (PieceIntrinsic.lean:715) ∘ `visitTransport`
  on the retained subtype (`hcarr`, as in `EXT_homfly_wall` X1Rows2.lean:1395) ∘ `liftVisitEquiv'⁻¹`; `Φ := Ψ.symm.trans
  Λ`. (a) `PreservesCyclicOrder`: `D₁.VB (Ψu)(Ψv)(Ψw) ↔ D₀.VB (σu)(σv)(σw)` (core) `↔ cycBetween (key (liftVisit (σu)))…`
  (`visitBetween_iff_key`, PieceIntrinsic.lean:777) `= cycBetween (key (σ_P (liftVisit u)))…` (F2) `↔ cycBetween (key'
  (τ (liftVisit u)))…` (F1 + `GT_cyc_congr_of_lt`) `↔ D_E.VB (Λu)(Λv)(Λw)` (`visitBetween_iff_key'`, `liftVisit_symm`).
  (b) `carriesDoublePoints_iff` (RecordHomfly.lean:178): `htw`, `liftVisit_twin` (:666), `visitTransport_visitTwin`
  (FlatCarriers.lean:119). (c) `carriesOverUnder_iff` (:205): `record_isOver = overBit`; `hbit`; on the lifts the over
  bit is the divide sign of the parent pair (`det_dir_eq`, PieceIntrinsic.lean:752, and `hdet`). (d) `record_sgn`
  (LinkDiagramRecord.lean:526): all `1` (`hsgn`, `geoPositiveLift_sign`). 120–200 lines (the accepted
  `GT_homfly_wall_gen`, X1Rows3.lean:716, is the same assembly with `ψ` in place of `Λ ∘ Ψ⁻¹`). True.

### Unit X — the branches of the literal `GT_G11`

* **X1 `G11_le_one_crossing`** (L848) — `EXT_homfly_wall hn hG hG' hs hT hT' q q' hcarr hkey hdet'` with `hkey` from
  `AV_key_lt_of_gauss` (its `¬(local pair)` hypothesis holds: two distinct members of a triangle of card `≤ 1` do not
  exist) and `hdet'` from `hdet` (`visit_crossing_val_eq_pair`). 40–60 lines. True.
* **X2 `G11_two_crossings_absurd`** (L872) — see §0. **Flagged**: true, but its proof needs Gauss parity for
  generic closed polygons (not in the library; global). Not used by `generic_transport`.
* **X3 `G11_card_cases`** (L882) — `card ≤ 1 ∨ card = 2 ∨ (all three crossings)`: `triangleCrossings` is the filter
  of the crossings with support in `{{e,f},{e,g},{f,g}}` (card 3 for distinct `e f g`); `card = 3` iff all three
  supports are crossings. 40–60 lines. True.

---

## §4. Feasibility probes (honest)

* **"Agree outside a disc" for the two lifts?** NOT achievable for `D_P` vs `D_E` directly (every corner moved with
  `t`), confirmed. Achievable for `M₀` vs `M₁` by construction: they share the label set `ZMod (k+3)` and all vertices
  but `m₀ ↦ w`; both bent edges lie in `Θ ⊆ interior U`; so the outside match is the identity (D6). This is the
  decisive simplification relative to the W3 sketch (six vertices, two translated), and it is exact, not approximate.
* **Which disc?** A homothetic enlargement of `Δ` (§1). A sup-metric square about a centre (Smoothing/K2 style) fails
  in general because foreign edges may pass arbitrarily close to the sides of `Δ`. The triangle's interior/frontier are
  available in Mathlib via `AffineBasis.interior_convexHull`; `Set.Finite.isCompact_convexHull`, `convex_convexHull`,
  `AffineMap.image_convexHull` cover `IsDisc`. Checked names exist in the pinned Mathlib.
* **Are the RIIIData fields checkable from the generic-orbit data?** Yes: the crossing pattern inside `U` (three arcs
  pairwise crossing once) is the triangle configuration; the height bits are the three crossing signs, transitive by
  `¬ IsAlternating`; the three reversals are the explicit parameter facts D9 (probe: 0/20 000 violations); the
  `Separates`/`OverOn` facts are the positive-diagram over strands (divide convention) at the named crossings.
  The naming `a, b, c` by height is a 6-case instantiation (D8), the only case split of the geometric core; the
  apex construction itself is case-free thanks to naming `p, q` by their order along `m`.
* **Is `¬ IsAlternating` used?** Only in D8 (one strict height order). Everything else in the geometric core is
  independent of the heights. The order hypothesis `hord` (which of `f, g` is met first along `e`) is handled by the
  `f ↔ g` symmetry at the top (`GT_G11_strong_proof`, A9–A10).
* **Record-level RIII invariance in the accepted library?** None: `SM.homfly_reidemeister_III` needs a geometric
  `RIII` site (LinkInterfaces.lean:378, LinkMoves.lean:700); `CV.gausscode_polynomial` (Axioms.lean:260) and
  `SM.record_polynomial` (PolynomialBlock.lean:1108) cover record isomorphisms only; `Deform` (LinkMoves.lean:462)
  keeps crossings. Verified by grep (`RIIIData` occurs only in LinkMoves.lean and X1Rows3's docstring).
* **Size.** The two accepted precedents for "one polygonal local move with full `LocalFrame`/`MoveMatch`/arc data" are
  K2 (Curl.lean:3518–7519, ~4 000 lines, one arc, 4 new vertices, 1 new crossing) and the smoothing splice
  (Smoothing.lean §§1–6, ~4 600 lines, two arcs). Our move has three arcs, 3 new vertices (flat, handled by accepted
  lemmas), 1 moved vertex, 2 new crossings, plus the carrier-to-configuration layer and the record twist. 3 500–5 500
  lines is the honest range; the single-apex design and the identity outside match are what keep it below K2 × 1.5.

## §5. What I am unsure is TRUE (as opposed to hard)

* **X2** (`G11_two_crossings_absurd`): true by Gauss parity, but that theorem is outside the library; if the executor
  prefers not to prove it, the literal `GT_G11` stays open while `GT_G11_strong` and the row close (§0).
* Every geometric leaf was probed numerically (C2, C4, D8/D9) or is a direct consequence of the configuration
  (`clear_*`). **A8/A15 are now stated in the local form** ("no foreign edge meets the frontier of `Δ`" + "no vertex
  in `Δ`"); the closed-triangle form consumed by the geometric units is the PROVED glue `G11_Config.clear_edge`
  (via the proved `G11_preconnected_meets_frontier`, `G11_edgeSegment_isPreconnected`). Correction to the first
  version of this note: the vertex clause (ii) is not purely local either — a vertex strictly inside `Δ` is excluded
  by a finite walk along the polygon (`Nat.find` on the first step leaving `Δ`, then the segment lemma), not by an
  IVT; see A8. Both clauses are true and the walk is a 60–80-line discrete argument.
* No leaf was found false. No counterexample.

## §6. Fidelity

G11 is a **proof step** of the printed proof (R_GENERIC_COMMON_TRANSPORT_PROOF.md:109–117), not a statement. The row
statement `GenericTransportData` (X1Rows.lean:1324–1400, fixed and used by the accepted panel) is **not affected in any
way**: `generic_transport` (Skeleton L988) has exactly the sibling rows' shape and the bundle's fields are consumed
verbatim through the accepted `PRE_173_canonical_branch`, `GT_173_endpoint_rows_*` and the re-derived
`G11_173_empty_row` (identical statement to `GT_173_empty_row`). `GT_G11_strong` is a new `def` of the draft, not a
change to any accepted declaration; the printed proof's own hypotheses ("the distinguished carriers on both sides
bear the three undominated local crossings") are exactly the three added `IsCrossing` clauses. The literal `GT_G11`
of X1Rows3 is stronger than the printed step and than its consumer needs (§0).

## §7. FINAL unit assignment (6 prover units; exact leaf names; black-box leaves of other units each may use)

Leaf totals: 48 assigned + X2 (optional, not on the row's path) = 49. Every unit may use as black boxes the accepted
library, the skeleton's definitions, its PROVED glue (`G11_Config.clear_edge`, `G11_preconnected_meets_frontier`,
`G11_edgeSegment_isPreconnected`, `G11_configOf_D₀`, `core_of_params`, `G11_strong_case`, …) and the leaves listed in
its "may use" column (statements only). Units 3–6 are pure plane geometry on `G11_Config`/`G11_Params` and are
independent of units 1–2.

| unit | leaves (exact names) | est. lines | may use (black box) |
|---|---|---|---|
| **U1 — A-carrier** (carrier edges and the R-LOC-2 adjacency) | `G11_carrierEdge_spec`, `G11_carrierEdge_eq_of_adjacent`, `G11_carrierEdge_isCrossing`, `G11_carrierEdge_crossingPoint`, `G11_carrierSign`, `G11_no_visit_between`, `G11_param_ne` (7) | 500–750 | — (GeoPositiveLift / GeoCornerPolygon / TripleVisitExchanges only) |
| **U2 — A-config + relabelling + provable branches** | `G11_clear`, `G11_alt_swap`, `G11_exact_swap`, `G11_triangleCrossings_swap`, `G11_alt_crossingSign`, `G11_cfg_hmp`, `G11_cfg_hmq`, `G11_cfg_hpq`, `G11_cfg_order`, `G11_cfg_trans`, `G11_cfg_clear_frontier`, `G11_cfg_clear_vertex`, `G11_le_one_crossing`, `G11_card_cases` (14) | 800–1 100 | all of U1 |
| **U3 — B subdivision + P parameters + disc D1–D2** | `X₀_generic`, `homfly_M₀`, `X₀_cross_mp`, `X₀_cross_mq`, `X₀_cross_pq`, `exists_Ψ₀`, `G11_exists_params`, `disc_isDisc`, `triangle_sub_interior` (9) | 900–1 250 | — |
| **U4 — C moved polygon + inner crossings D3–D4** | `X₁_generic`, `X₁_cross_pC`, `X₁_cross_qB`, `X₁_cross_iff`, `X₁_cross_pq`, `X₁_sign_pC`, `X₁_sign_qB`, `inner_M₀`, `inner_M₁` (9) | 1 000–1 400 | U3: `X₀_generic`, `X₀_cross_mp`, `X₀_cross_mq`, `X₀_cross_pq`, `disc_isDisc`, `triangle_sub_interior` |
| **U5 — D5–D7 clean, move match, arcs** | `clean_M₀`, `clean_M₁`, `exists_moveMatch`, `exists_arcCovers` (4) | 900–1 300 | U3: `X₀_generic`, `X₀_cross_*`, `disc_isDisc`, `triangle_sub_interior`; U4: all nine |
| **U6 — D8 site + E record twist + F assembly** | `riii`, `exists_Ψ₁`, `G11_twisted_key_lt`, `G11_liftVisit_σD`, `G11_recordIsoData` (5) | 1 100–1 600 | U3, U4, U5: all; U1: `G11_carrierEdge_spec`, `G11_carrierEdge_crossingPoint`, `G11_no_visit_between`; U2: `G11_cfg_hmp`, `G11_cfg_hmq`, `G11_cfg_hpq` |
| **X2 (optional, NOT ON THE ROW'S PATH)** | `G11_two_crossings_absurd` (1) | 800–1 500 or left open (needs Gauss parity) | — |

Balance note: U1/U2 are shorter in lines but sit on the carrier layer (block machinery), which is the conceptually
harder API; U4–U6 are longer but follow the accepted templates (Smoothing.lean §§5–6e, Curl.lean K2). If a further
split is wanted, U6 divides as U6a = `riii` + `exists_Ψ₁` (geometry) and U6b = `G11_twisted_key_lt` +
`G11_liftVisit_σD` + `G11_recordIsoData` (records), U6b depending on U6a only through the skeleton's glue.

Row path: `generic_transport` ← `G11_genericTransportData` ← `G11_173_empty_row` ← `G11_empty_groupedPoly_eq` ←
`GT_G11_strong_proof` ← `G11_strong_case` (+ `G11_param_ne`, `G11_exact_swap`, `G11_alt_swap`,
`G11_triangleCrossings_swap`) ← `G11_core` (units 3–6) + `G11_configOf` (units 1–2) + F1–F3 (U6). Independence
from X2 verified by compiling a scratch copy with X2, `GT_G11_proof` and `generic_transport_of_GT_G11` deleted:
`generic_transport` still compiles (see §8).

## §8. Verification log

* `cd work/lean && lake env lean ../drafts/rlane2/G11_Skeleton.lean`: exit 0, 0 errors, 49 × `declaration uses sorry`,
  no other message (after the local reformulation of A8/A15 and the proved glue).
* `#print axioms RProof.G11_empty_groupedPoly_eq` (the re-derived row assembly, `GT_G11_strong` as hypothesis):
  `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` — no `sorryAx`.
* Scratch copy without X2 / `GT_G11_proof` / `generic_transport_of_GT_G11`: 0 errors — the row does not depend on X2.
* `python3 work/drafts/rlane2/G11_probe.py`: `violations: 0 of 20000` (re-run after the edit; no geometric leaf
  changed).
