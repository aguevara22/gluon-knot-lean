# W3_GT_REPORT — unit U-GT, row 173 R:generic_transport (`RProof.generic_transport`, bundle `GenericTransportData`)

Written 2026-09-14 (wave 3, R lane part 2) on Mark's RunPod home pod. Plan of record: `NOTES_FINAL.md` §5 (clause
map), §10 (row 173 consumes R:generic_table, R:exterior, cor:groupedknot, lem:turnlift (ii), ax:homfly RIII
invariance + **an actual RIII move on the grouped diagram (G11)**, 156), unit sketch "U-GT … row 173 empty row
(grouped polynomial via an actual RIII move + record iso) and endpoint rows (c→b, a→b residual-graph
isomorphisms)".

## Files

* **`work/drafts/rlane2/W3_GT.lean`** (10 009 lines) = `RLaneX1_Assembled2.lean` (6 684) + the import line
  `import CV.GroupedKnot` (line 7; CV:cor:groupedknot, accepted row 158, needed for `P_{S,L} = P(D(W))`) + the
  unit (lines 5041–8365, inserted between the frozen field lemma `PRE_173_canonical_branch` and the row theorem).
  `diff RLaneX1_Assembled2.lean W3_GT.lean | grep '^<'` prints **nothing**: no statement, definition, name,
  docstring or existing import was changed, and — see "Unproved" — the placeholder `sorry` of
  `RProof.generic_transport` is NOT replaced (its field `empty_row` needs the open fact G11).
* **`work/drafts/rlane2/RLaneX1Rows3.lean`** (3 354 lines): the portable module, `import RProof.X1Rows2` +
  `import CV.GroupedKnot` + ONLY the new material (268 declarations, all `GT_`-prefixed or inside the namespace
  `RProof.GT_Endpoint`), with `namespace RProof`, `open SM SM.GeoCarrier`, `variable {n : ℕ} [NeZero n]`. It
  contains **no `sorry`** (the one occurrence of the word is in the header docstring) and compiles with plain
  `cd work/lean && lake env lean ../drafts/rlane2/RLaneX1Rows3.lean` — exit 0, **0 errors, 0 warnings**, ~11 s.
* This report.

Compile of the unit file: `cd work/lean && lake env lean ../drafts/rlane2/W3_GT.lean` — exit 0, **0 errors**, exactly
**six** `declaration uses sorry` warnings at the six still-open row theorems (`generic_transport` L8366,
`generic_selected` L8427, `extreme_pair_zero` L8578, `extreme_transport` L8718, `extreme_selected` L8804, `cv_R`
L8884), no other warning; ~18 s. Nothing under `work/lean` was written; no `lake build`.

`#print axioms` (scratch copies `/tmp/gt/ax/Rows3_axioms.lean`, `/tmp/gt/ax/W3_axioms.lean`):
* `GT_173_endpoint_rows_canonical`, `GT_173_endpoint_rows_relabelled`, `GT_endpoint_rowTerm_eq`,
  `GT_173_empty_row`, `GT_generic_transport_of_G11`, `GT_homfly_wall_gen`, `GT_groupedPoly_eq_homfly` —
  `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]`: exactly the axiom set of
  the accepted `CV.gausscode_polynomial` / `CV.pieceHomflyTransported` (the three literature interfaces of
  work/lean/axiom-policy.json), the same as rows 168 and 170. No new axiom, no `sorryAx`.
* The X₁-free toolkit — `GT_cyc_carried`, `GT_owner_arc`, `GT_carrierEquiv` — `[propext, Classical.choice,
  Quot.sound]`.
* `RProof.generic_transport` (unchanged placeholder): `[propext, sorryAx, Classical.choice, Quot.sound,
  SM.lit_homfly]`. `PRE_173_canonical_branch`: standard axioms only.

## Proved

| field of `GenericTransportData` | status | lemma (portable module) |
|---|---|---|
| `canonical_branch` | PROVED (unit PRE, wave 1) | `PRE_173_canonical_branch hG` |
| `empty_row` | PROVED **modulo G11** | `GT_173_empty_row (hG11 : GT_G11) hn hL hG hR hef heg hfg` — exactly the field's type |
| `endpoint_rows_canonical` | **PROVED** | `GT_173_endpoint_rows_canonical hn hL hG hR hef heg hfg` — exactly the field's type |
| `endpoint_rows_relabelled` | **PROVED** | `GT_173_endpoint_rows_relabelled hn hL hG hR hef heg hfg` — exactly the field's type |

Binders of the field lemmas: `hL : LocalizationData E e f g δ` (row 164), `hG : GenericTableData E e f g δ` (row
172-table), `hR : AV_EventRadius E δ` (the accepted sign radius of unit AV: turns, crossing signs, a common ray),
`hef heg hfg : e ≠ f, e ≠ g, f ≠ g` (from `h3` via `AV_ne_of_remote`).

Assembly modulo G11: `GT_genericTransportData (hG11) hn hL hG hR hef heg hfg : GenericTransportData hn E e f g δ`
and **`GT_generic_transport_of_G11 (hG11 : GT_G11) hn E e f g h3 h4e h4f h4g hE : ∃ δ, 0 < δ ∧ δ ≤ E.radius ∧
GenericTransportData hn E e f g δ`** — the row theorem word for word with the one extra hypothesis, radius
`min δ_L (min δ_G δ_R)` (accepted `localization`, `generic_table`, `AV_exists_eventRadius`), the bundles shrunk by
`F1.localizationData_mono`, `SEL_genericTableData_mono`, `AV_eventRadius_mono`. When G11 is proved, the row
closes as `generic_transport … := GT_generic_transport_of_G11 <proof of G11> hn E e f g h3 h4e h4f h4g hE`.

## Unproved — the row theorem and its field `empty_row`: the missing fact G11

**Nothing in the statement is false**; no field needs a stronger hypothesis. The field `empty_row` is true as
frozen, but its proof needs a fact the accepted library does not provide, stated in the module as

```
def GT_G11 : Prop := ∀ (n) [NeZero n] (hn : 3 ≤ n) {P P'} (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (e f g), e ≠ f → e ≠ g → f ≠ g →
  ExactTriangleVisitOrders P P' e f g hs →
  (∀ i j, IsCrossing P {i, j} → (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j))) →
  ¬ IsAlternating (strandSign P e f) (strandSign P e g) (strandSign P f g) →
  ∀ {T T'} (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG'.cg T') (q) (q'),
    geoCarrierCrossings hG'.cg T' q' = (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding →
    triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q →
    homfly (geoPositiveLift hn hG' hT' q') = homfly (geoPositiveLift hn hG hT q)
```

i.e. **the HOMFLY polynomial of the grouped diagram is invariant across the RIII wall**: two carriers on the two
sides of a simple RIII wall in the generic orbit (transitive divide over-order, `¬ IsAlternating`), with
corresponding retained crossings, both retaining the whole triangle, whose six triangle visits are exchanged
pairwise on their edges (R-LOC-2 (2)–(3), `ExactTriangleVisitOrders`) and whose divide signs are carried, have
positive lifts with the same polynomial. This is the printed sentence "Apply the corresponding ordinary oriented
Reidemeister III move to `D_P`, obtaining `D'`; `ax:homfly` gives `P(D') = P(D_P)`. … an orientation-preserving
`def:record` isomorphism from `D'` to `D_E` … `ax:gausscode` identifies their oriented links. Hence their grouped
polynomials agree" — in the form in which §1 consumes it. It is the only place where the row leaves the record
level: everything else in `empty_row` (carrier correspondence, corner lists, turns, rotation, retained crossings,
`P_{Q,L} = P(D(W))`, the triangle-disjoint carriers) is proved (`GT_empty_*`, see below).

**Why it is missing.** RIII invariance in the library is `SM.homfly_reidemeister_III : RIII D D' → homfly D = homfly D'`
with `SM.Link.RIII D D' := ∃ U, Nonempty (RIIIData U D D') ∨ …` a *geometric disc-local replacement*: a disc `U`,
an `OutsideMatch` (identical traced points, directions and crossings outside `U`), three arcs per side covering
`U`, three inner crossings with the height order and the reversed orders. No `RIIIData` is constructed anywhere in
`work/lean` (only transported by `mirror`/`reverse`), and the two lifts `geoPositiveLift q`, `geoPositiveLift q'` do
not agree outside any disc (every corner moved with the parameter). The record-level replacement of
CV:ax:gausscode (`CV.gausscode_polynomial`, from `SM.record_polynomial`) covers record *isomorphisms*; there is no
record-level Reidemeister III invariance (and `SM.P` is defined through the `lmF` witness, not as a function of the
record). The alternative "transport the grouped polynomial of the empty row through the record isomorphism of
the pieces as W2_EXT did" does not apply to the distinguished carrier: its pieces change across the wall (on the
path side `a, b, c` lie in one piece; on the edge side `b` is not interlaced with `a, c`, and each piece polynomial
changes — only the product is invariant, by the RIII move).

**Recommended route for G11 (no `Deform` needed).** `P(D_P) = P(D_E)` by the chain `D_P ≃_Reparam M₀ –RIII→ M₁ ≅_record D_E`:
(i) subdivide the corner polygon of the distinguished carrier at t (a one-component polygon,
`carrierDiagram = positiveDiagram (single (geoCornerPolygon …))` by `CS3.positiveLift_eq_geo`) by six flat
vertices near the triple point — the accepted `SM.CS3` flat subdivision `homfly_positiveDiagram_single_appendVertex`
gives `P(M₀) = P(D_P)`; (ii) `M₁` := `M₀` with the two inner vertices of the middle strand translated across the
opposite crossing (a straight-line move inside a disc `U`; the divide convention gives the same over data since
directions are unchanged); (iii) `RIIIData U M₀ M₁` field by field; (iv) `M₁.record ≅ D_E.record` by the record
isomorphism of `GT_homfly_wall_gen` with the visit bijection exchanging the three pairs (its `hcyc` clause is
exactly the carried-with-three-adjacent-transpositions order that `ExactTriangleVisitOrders` gives). Steps (i)–(iii)
are geometric (estimated 1 500–3 000 lines); (iv) is ~150 lines on the toolkit of this unit. Alternatively a
record-level RIII invariance would have to reproduce Lickorish–Millett Prop. 4 by the `(N, b)` skein induction of
SM/PolynomialBlock — out of scope for the R lane.

## How the printed proof is rendered

Notation as in the unit: `T = triangleCrossings P e f g`, `τ = markTransport hs`, `ρ_S = geoSmoothingSuccessor`,
`P = E.curve t`, `P' = E.curve t'`, keys = `geometricVisitKey`/`geoMarkKey`.

**§0 Corner-level wall transport at full availability (`GT_Wall`, `GT_Good`, `RLaneX1Rows3.lean`
L75–L580).** The AV toolkit's next-corner machinery (`AV_nextCorner`, `AV_cornerSucc`, `AV_NCSpec`/`AV_CSSpec`,
reused as accepted) is rebuilt on wall data **without the availability-`≤ 1` clause `dominated`**: `GT_Rev T v w`
(two same-edge visits of distinct `T`-crossings, R-LOC-2 (2)), `GT_Wall` = independence of `S` and of `τS`,
visit-key orders carried off the reversed pairs (`key_lt`), turns, signs, ray, and `corners_apart` — no two
corners form a reversed pair (true for every support with at most one triangle crossing: rows `∅, a, b, c`).
`GT_Good m` = no reversed partner of `m` is a corner; `GT_good_key_lt` (good mark vs corner) replaces
`AV_good_key_lt`, and the chain `GT_ncspec_transport → GT_nextCorner_transport → GT_csspec_transport →
GT_cornerSucc_transport → GT_carrierEquiv` (the carrier bijection) `→ GT_owner_transport` (ownership of good
marks) `→ GT_cornerList_eq, GT_cornerPolygon_eq, GT_turn_tcp, GT_selector_eq, GT_geoWind_eq` (lem:guardconst turns
and signs; "constant corner counts and signs preserve its weight by def:wind") `→ GT_edge_tcp,
GT_rotationNumber_tcp, GT_carrierR_eq` (CV:def:rot's ray formula — the accepted `rot_eq_rotRay`, no path across
the wall; renders "`lem:turnlift(ii)` preserves its signed and absolute rotation") is the AV proof verbatim with
the new goodness. This is the "successor lift (2a)" of the printed proof at the level of corners.

**§1 Empty row (`GT_empty_*`, L3136–L3321).** `S = Q`, no triangle visit is a corner, so every mark is good
(`GT_empty_good`) and `GT_geoCarrierCrossings_eq_of_good` carries the retained crossings of every carrier
(including the three local crossings, undominated by full availability: `GT_empty_tri_mem_U`). "On the path side
they form a connected residual subgraph, so lem:carriers(iv) puts all six local visits on one distinguished
carrier": `GT_empty_tri_subset` — a carrier owning one triangle visit retains all three triangle crossings
(`CV.owner_eq_of_mem_U` for the twin, `GT_owner_eq_of_adjacent` for the adjacent unselected visits on the shared
edge, `GT_shared_label`). "By cor:groupedknot (A),(B) the product of their piece polynomials is the HOMFLY
polynomial of the one knot diagram … In the piece-free case … `P_{S,L} = 1`": `GT_groupedPoly_eq_homfly`
(`CV.groupedknot.grouped_polynomial` and `.no_piece`). Per carrier: triangle-disjoint → `EXT_homfly_wall` ("no
residual-component bijection is asserted": the whole lift is compared, not the pieces); distinguished → G11.
`w_{S,L}` = number of retained crossings (`groupedWrithe_eq_card_geoCarrierCrossings`). Assembly by
`SummandTransport` + `AV_rowTerm_eq_of_summandTransport` (`GT_173_empty_row`). The wall data
(`GT_empty_wall`) come from `gauss_words`, the sign radius, and `Q ∈ outsideSupports` on both sides
(`GT_outsideSupports_transport`, R-LOC-2 (4) off `T`).

**§2–§3 Endpoint rows (`GT_Endpoint`, namespace `RProof.GT_Endpoint`, L1196–L2187; X₁ objects L2190–L2410; the arc lemma `GT_owner_arc` L1133, `GT_homfly_wall_gen` L715, `GT_cyc_carried` L859).**
The abstract configuration of a row `x` of the selected pair `{x, w}` with centre `m` (edge labels `ℓ₁ = x∩m`,
`ℓ₂ = x∩w`, `ℓ₃ = w∩m`; canonical branch row `a`: `x = a, w = c, m = b`), on side `P` the two-edge side:
* "`R-PAR sharpens the outside masks after selecting a: every outside survivor meets neither b,c or meets
  both`": field `twins`, from `GenericTableData.mask_sharpening` (`GT_twins_of_mask`).
* "`The map fixing every outside label and sending c to b is an isomorphism of the two undominated induced graphs
  and carries residual components bijectively`": `GT_φ hs w m = swap(w', m') ∘ τ` (`GT_Endpoint.φ_*`), the
  relabelling data `GT_Relabel` (`GT_Endpoint.relabel`: `retained` — the retained crossings of every carrier are
  carried along `φ`, `w ↦ m'` through the adjacent unselected `ℓ₃`-pair `w₃, m₃` on the far side
  (`owner'_m₃`) and `w ∈ U(S)` (`owner_w₂_eq_w₃`); `mem_U` — `U(S)` carried (`w ∈ U`, `m ∉ U` on the path side,
  `m' ∈ U'`, `w' ∉ U'` on the edge side, outside crossings by R-LOC-2 (4)); `adj` — residual interlacement
  carried, the twins for the pairs `(y, w)`), whence `GT_residualIso`, `GT_pieceEquiv`, `GT_pieceLabels_eq`,
  `GT_piecesOn_eq` (via `GT_mem_piecesOn_iff_subset`: a piece is on a carrier iff its labels are retained by it).
* "`The same map preserves the signed cyclic records … P-c is first visited on u2 and second on u3, while E-b is
  first visited on u1 and second on u3. The divide designation is therefore preserved because sgn det(u2,u3) =
  sgn det(u1,u3) = sigma`": the visit relabelling `ψ₀ = swap(τw₂, τm₁) ∘ swap(τw₃, τm₃) ∘ τ` (`GT_Endpoint.ψ₀_*`),
  the field `sgn : crossingSign P ℓ₂ ℓ₃ = crossingSign P ℓ₁ ℓ₃` (= (4)/(6)), `ψ₀_det` (divide signs carried,
  outside visits by lem:guardconst `sign_eq`), `ψ₀_twin` (double points), and the cyclic order (below); then
  `GT_homfly_wall_gen` — `EXT_homfly_wall` generalized to an arbitrary visit bijection compatible with the twin
  pairing, carrying the cyclic key order and the divide signs (def:record (a)–(d), `recordIsoOfData`,
  `gausscode_polynomial`) — gives `GT_endpoint_pieceHomfly_w`; the pieces without `w` use `EXT_pieceHomfly_wall`
  (`GT_endpoint_pieceHomfly_out`). "`Component cardinalities agree, so grouped writhes agree`":
  `GT_endpoint_groupedWrithe_eq`.
* The cyclic order of the relabelled record (the printed "arbitrary-Q lift of (3) preserves cyclic order on the
  matched BC and A carriers"): **the arc lemma** `GT_owner_arc` — for an independent support and a selected
  visit `x₁` with twin `x₂`, the carrier of `x₂` lies in the arc from `x₁` to `x₂` (the set "arc ∪ {x₂}" is
  closed under `ρ_S`: `GT_arc_closed`, `GT_arc_succ`, using the key-based interlacement criterion
  `L.interlaces_iff_xor` for the other selected crossings, which do not interlace `x`); the carrier of `w` is the
  carrier of `x₂` or of `x₁` (`qw_eq`, from the adjacency of `x₂, w₂`), so all visits of the piece of `w` lie in
  one arc cut by the two visits of `x`; within that arc `w₂` is the last visit before `x₂` (or the first after),
  and on the far side `m₁'` is the first after `x₁'` (or the last before) — `rot_of_owner_x₂`, `rot_of_owner_x₁`
  (`GT_adj_empty`: adjacency with a witness in the other arc; `GT_cyc_arc_step`, `GT_cyc_total`); the other visits'
  base-point orders are carried (`key_lt_ψ₀`, `key_lt_w₃_iff`, `GT_adj_lt_iff`: adjacent same-edge visits are
  indistinguishable from any other position). The real-number lemma **`GT_cyc_carried`** (a bijection carrying
  the base-point order on all pairs but one element, which keeps its place or moves from last to first, carries
  the cyclic order of every triple; via `GT_cyc_base`, cyclic betweenness read from a base point) closes clause
  (a). This is the precise content of "the successor lift (2a) preserves cyclic order" for a relabelled visit.
* "`Both local carriers move geometrically … lem:turnlift(ii) gives equal signed and absolute rotations, and
  def:wind gives equal carrier weights`": §0 on `GT_Endpoint.wall` (the corners are vertices, `Q`-visits and the
  two `x`-visits, whose reversed partners `m₁, w₂` are not corners: `good_of_edge`, `x₁_corner`).
* Assembly: `GT_endpoint_summandTransport`, `GT_endpoint_rowTerm_eq : rowTerm hn hG (Q ∪ {x}) = rowTerm hn hG'
  (transportSupport hs (Q ∪ {x}))`.

**Event level (`GT_endpointData` L2624, `GT_endpoint_transport_*` L2660–L2790; the six rows L2841–L3020 and the two fields
L3022–L3134).** The configuration is built from `LocalizationData` (`gauss_words`, `interlace_toggle`,
`complement_on_triangle`, `adjacent` — `GT_adjacent_of_shared`: any two triangle crossings are adjacent on their
shared edge, either order), `GenericTableData.mask_sharpening` and `AV_EventRadius`. Which side is the two-edge
side is read from `selected_is_graph_selected` (+ "not all three edges" in the generic orbit,
`GT_not_all_edges*`); when `t` is the one-edge side the two-edge case is applied to the pair `(t', t)`
(`GT_endpoint_transport_edge`: `Q' = τQ` is an outside support with full availability by
`GT_outsideSupports_transport`, `GT_fullAvail_transport` (`F1.avail_same`), the local edges by
`complement_on_triangle`, the sign identity by `sign_eq`, and `transportSupport hs' (transportSupport hs S) = S`,
`EXT_transportSupport_symm`). The six (branch, row) cases and their labels, all checked against the six-case
table of R_GENERIC_NONSELECTED_SELECTOR_PROOF.md / `selected_is_graph_selected`:

| branch (signs) | row `x` | `w` | `m` | `ℓ₁ ℓ₂ ℓ₃` | sign identity used | lemma |
|---|---|---|---|---|---|---|
| `ac`: `s_a = s_b = s_c` | `a` | `c` | `b` | `e f g` | `s_b = s_c` | `GT_row_a_of_AC` |
| `ac` | `c` | `a` | `b` | `g f e` | `s_a = s_b` | `GT_row_c_of_AC` |
| `ab`: `s_a = −s_b` (⇒ `s_b = s_c`, nonalternating: `GT_signs_of_selectedAB`) | `a` | `b` | `c` | `f e g` | `s_b = s_c` | `GT_row_a_of_AB` |
| `ab` | `b` | `a` | `c` | `g e f` | `s_a = −s_c` | `GT_row_b_of_AB` |
| `bc`: `s_b = −s_c` (⇒ `s_a = s_b`: `GT_signs_of_selectedBC`) | `b` | `c` | `a` | `e g f` | `s_a = −s_c` | `GT_row_b_of_BC` |
| `bc` | `c` | `b` | `a` | `f g e` | `s_a = s_b` | `GT_row_c_of_BC` |

(`s_a = strandSign e f`, `s_b = strandSign e g`, `s_c = strandSign f g`; the identity needed is
`crossingSign ℓ₂ ℓ₃ = crossingSign ℓ₁ ℓ₃`, `strandSign = crossingSign` by `rfl`, `crossingSign_swap`.) The words
themselves are never used: only adjacency of the three bundle pairs (both sides), the local edges and the arcs.

## Statement check (rule 4)

* `canonical_branch`, `endpoint_rows_canonical`, `endpoint_rows_relabelled`: true as frozen and proved.
* `empty_row`: true as frozen (mathematically: the two grouped diagrams differ by an oriented RIII move with
  transitive heights and a record isomorphism), proved modulo `GT_G11`, which is a true statement about the
  library's objects (for one-component lifts the three adjacent transpositions of the Gauss code with unchanged
  over data and all-positive signs are realized by an actual RIII move through the triangular face). No
  counterexample; the missing fact is G11 exactly as `NOTES_FINAL.md` §10 lists it ("G11 open").
* The fields' hypotheses actually used: `endpoint_rows_*` use `¬ ExtremeLocal` (through
  `selected_is_graph_selected` and "not all three edges"), the sign hypotheses (only for the divide-sign identity
  and the selected pair), `Q ∈ outsideSupports`, `FullAvail Q` (for `x ∈ U`, the twins, and the far-side full
  availability); `empty_row` uses `¬ ExtremeLocal` only inside G11 (transitive heights).

## Helpers added (all in `RLaneX1Rows3.lean`; 268 declarations)

Definitions: `GT_Rev`, `GT_Wall`, `GT_Good`, `GT_carrierMap`, `GT_carrierInv`, `GT_carrierEquiv`, `GT_tcp`,
`GT_Relabel`, `GT_residualIso`, `GT_pieceEquiv`, `GT_S` (reducible `Q ∪ {x}`), `GT_φ`, `GT_Endpoint` (+ `x₁ x₂ w₂ w₃
m₁ m₃`, `β`, `qw`, `ψ₀` in its namespace), `GT_G11`.
Theorems: the §0 chain (`GT_good_*`, `GT_mark_key_lt`, `GT_ncspec_transport`, `GT_nextCorner_transport`,
`GT_csspec_transport`, `GT_cornerSucc_transport`, `GT_carrierMap_*`, `GT_carrierInv_*`, `GT_carrierEquiv_owner`,
`GT_owner_transport(_corner)`, `GT_owner_iff`, `GT_cornerList_eq`, `GT_cornerCount_eq`, `GT_cornerMark_eq(')`,
`GT_cornerPolygon_eq`, `GT_tcp_eq`, `GT_turn_tcp(_eq_turn_cast)`, `GT_selector_eq`, `GT_geoWind_eq`,
`GT_edge_tcp`, `GT_rotationNumber_tcp`, `GT_carrierR_eq`, `GT_weight_eq`, `GT_wind_eq`); retained crossings and
pieces (`GT_geoCarrierCrossings_eq_of_good`, `GT_residualIso_apply_val`, `GT_pieceEquiv_pieceOf`,
`GT_pieceLabels_eq`, `GT_pieceWrithe_eq`, `GT_mem_piecesOn_iff_subset`, `GT_piecesOn_eq`,
`GT_card_geoCarrierCrossings_eq`, `GT_groupedPoly_eq_homfly`, `GT_homfly_wall_gen`); the real-number cyclic
lemmas (`GT_cyc_gt_gt/gt_lt/lt_gt/lt_lt`, `GT_cyc_base`, `GT_cyc_arc_step`, `GT_cyc_rotate`, `GT_cyc_total`,
`GT_cyc_carried`, `GT_cyc_congr_of_lt`, `GT_det_pos_iff_of_sign`); one polygon (`GT_markKey_visit`,
`GT_traversalBetween_iff`, `GT_adj_empty(')`, `GT_succ_of_adjacent`, `GT_owner_eq_of_adjacent`,
`GT_key_lt_of_edge_val_lt`, `GT_key_ne_of_ne`, `GT_markKey_ne_of_ne`, `GT_markKey_visit_pos`, `GT_arc_succ`,
`GT_arc_closed`, `GT_owner_arc`, `GT_owner_twin_ne`, `GT_key_lt_iff_of_edge_ne`, `GT_edge_of_between`,
`GT_adj_lt_iff`, `GT_forall_visit_owner_iff`, `GT_retained_of_not_mem_U`, `GT_mem_S_iff`); the endpoint namespace
(`GT_Endpoint.*`: names, twins, `xval/wval/mval`, `S_ind`, `S'_ind`, `w_mem_U`, `m_not_mem_U`, `m'_mem_U`,
`w'_not_mem_U`, `mem_U_iff_of_outside`, `wall`, `good_*`, `owner_*`, `φ_*`, `retained`, `mem_U_iff`, `adj`,
`relabel`, `ψ₀_*`, `key_lt_w₃_iff`, `key_lt_ψ₀`, `qw_eq`, `mem_arc(')_of_owner_x₁/x₂`, `owner'_ψ₀`,
`rot_of_owner_x₁/x₂`, …); the X₁ objects (`GT_endpoint_pieceHomfly_out/_w`, `GT_endpoint_owner_of_mem_piece`,
`GT_endpoint_groupedPoly_eq`, `GT_endpoint_groupedWrithe_eq`, `GT_endpoint_Omega1_eq`,
`GT_endpoint_summandTransport`, `GT_endpoint_rowTerm_eq`); the event (`GT_adjacent_symm`, `GT_val_eq_pair`,
`GT_isCrossing_of_mem`, `GT_S_eq_insert`, `GT_adjacent_of_shared`, `GT_tri_cases`, `GT_twins_of_mask`,
`GT_triangleCrossings_map`, `GT_outsideSupports_transport`, `GT_fullAvail_transport`, `GT_endpointData`,
`GT_transportSupport_S`, `GT_endpoint_transport_path/_edge`, `GT_endpoint_transport`); the fields
(`GT_signs_of_selectedAB/BC`, `GT_mem_pair_l/r`, `GT_tri_ef/eg/fg`, `GT_not_all_edges(')('')`, `GT_row_*`,
`GT_173_endpoint_rows_canonical`, `GT_173_endpoint_rows_relabelled`); the empty row (`GT_shared_label`,
`GT_empty_wall`, `GT_empty_good`, `GT_empty_tri_mem_U`, `GT_empty_tri_subset`, `GT_empty_groupedPoly_eq`,
`GT_173_empty_row`); the bundle and row (`GT_genericTransportData`, `GT_generic_transport_of_G11`).

## Notes for the assembler and the next waves

* **Import added**: `import CV.GroupedKnot` (line 7 of `W3_GT.lean`, line 2 of the portable module) — cor:groupedknot
  (row 158) is accepted and built in `work/lean`; it must be kept when the file moves.
* Inside `W3_GT.lean` the unit uses `AV_transportSupport_union` (section AV, before the row), not
  `A2_transportSupport_union` (section A2, after the row theorems); the two are the same statement.
* The endpoint transport is stated on the abstract configuration `GT_Endpoint` (two `CrossingGeometry` polygons,
  no event) and is reusable for rows 176 (`transport_x/y/z`: the same relabelling with `w, m` the two other
  crossings) once the analogous wall data are supplied; `GT_Wall`/`GT_Good` cover every support with at most one
  triangle crossing (rows `∅, a, b, c`), and the corner-level chain also holds for the pair rows `ac`, `ab`, `bc`
  of rows 174–177 whenever no two corners form a reversed pair — for a pair support both members of a bundle pair
  are corners, so those rows need a further extension (a corner exchanged with a corner).
* `GT_homfly_wall_gen` (any twin-compatible visit bijection carrying the cyclic key order and the divide signs)
  and `GT_cyc_carried` are the tools for the record isomorphism `M₁ ≅ D_E` in the recommended route for G11
  above, and for the RII moves G10 of rows 174 and 176.
* Row 178's `A2_cvRNear_of_rows` can consume `GT_generic_transport_of_G11 hG11` for its `h173` argument once G11
  is available; nothing else in the file refers to row 173.
