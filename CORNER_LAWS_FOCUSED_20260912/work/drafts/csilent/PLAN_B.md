# PLAN_B — prop:C-silent (silence) `C(P₊) = C(P₋)` at a simple (E) or (C) wall

Architect B (reuse-first), 2026-09-14. Target `SM.prop_C_silent : CSilentData`, statement FIXED in
`work/drafts/CSilent_statement.lean` (bundle and theorem header copied byte-identically into the skeleton,
verified by string comparison). Source: reference/SM/sm-4-knotlaws.tex:101-152.
Skeleton: `work/drafts/csilent/Skeleton_B.lean` — **1150 lines, 80 declarations, 6 sorried**, checked with
`cd work/lean && lake env lean ../drafts/csilent/Skeleton_B.lean` (no errors; only `declaration uses
'sorry'` warnings). `#print axioms SM.prop_C_silent` = `propext, sorryAx, Classical.choice, Quot.sound,
SM.lit_homfly`. **`prop_C_silent` is PROVED from the chain**; the six `sorry`s are all leaves of ONE
section (§3 of the skeleton, the centre-genericity geometry), i.e. the single genuinely new geometric input
of this row.

## 0. Route decision

**R2 (hybrid), the route of prop:C-chamber / thm:C-S3**, chosen over R1 (RecordIso → `SM.presentations`).

* R2: for one side parameter `t` below the radius `δ` of lem:wall-sides (E),(C) (`silent_sides`,
  SM/SilentSides.lean:26), build a `Carrier.MarkTransport hn hP₊ hP₋` between `P₊ = g.curve (sideTime true t)`
  and `P₋ = g.curve (sideTime false t)` exactly as `Carrier.pathTransport` (SM/CChamber.lean:953) is built,
  and close with the accepted **`MarkTransport.cornerStateSum_transport`** (SM/CChamber.lean:503). Its two
  hypotheses are (i) uniformity of corresponding carriers and (ii) equality of corresponding corner
  coefficients. (ii) needs equal `m_Q`, equal `|rot|` and equal HOMFLY of the positive lifts; the last two are
  obtained along the family of corner polygons through the centre, `u ↦ silentCornerFamily … (silentPath g t u)`
  (`(2u−1)t`), with lem:rot (ii) (`rotationNumber_family_constant`) and lit:homfly's planar clause
  (`Link.homfly_positiveDiagram_single_of_family`, SM/CS3.lean:592, the general form of
  `deform_positiveLift_path`). This is what the printed proof does (lines 118-140): carrier geometry only at
  the centre, and the state sums evaluated on the generic sides. At every `u ≠ ½` the family polygon is the
  re-indexed accepted carrier polygon of a generic side point (`single_geo_generic`, SM/CS3.lean:1429); at
  `u = ½` (the centre) genericity of the one-component shadow is the NEW lemma `single_generic_of_weak`
  (skeleton §3), the formal content of printed lines 118-131.
* Why not R1: it needs a `RecordIso` between the records of the two positive lifts, i.e. that the cyclic
  visit order along a corner polygon is the carrier's mark-cycle order — a block-parametrisation argument
  (~400-600 lines on the generic layer) PLUS the record-level plumbing, and it still needs the family through
  the centre for `|rot|` (regularity at the centre). R2 needs the block argument once (at the centre) and
  nothing else new; every other step is an instance of accepted CChamber / CS3 / FlatCarriers machinery.
* Differences from thm:C-S3 that make silence EASIER: no deletion copy, no flat subdivision (`appendVertex`,
  `Reparam`), no selector table; the two sides have the same carrier combinatorics (`GeometricRecordsAgree`
  on both sides against the centre). What is HARDER: the centre is not a re-indexing of any generic
  configuration, so genericity of the centre corner polygon cannot be borrowed as in `centre_shadow_generic`
  (SM/CS3.lean); it must be proved from `WeakGeneric`/`CrossingGeometry` + the block structure — this is §3.
* (E) vs (C): the two cases share every step; the only inputs are `WallGerm.Silent` (`Or.inl`/`Or.inr`,
  SM/SilentCenter.lean:23), `silent_center_weak`, `silent_curve_weak` and `silent_sides`. The degenerate
  incidence of (E) (`μ_M` outside the closed base segment) and the non-adjacent (C) triple are exactly what
  make the centre `WeakGeneric` (SM/SilentCenter.lean:29-38) — which is all §3 uses.

## 1. The chain (skeleton section by section; every cited declaration verified by grep, file:line)

Notation: `cCG := silentCentreCG hn g h : CrossingGeometry g.center` (= `weak_crossingGeometry
(g.silent_center_weak hn h)`), `sCG s := silentCurveCG hn g h s`, `g.sideGeneric b t : Generic (g.curve
(g.sideTime b t))`, `hsb := hF.side_crossing_iff b t ht`, `T_b := transportSupport hsb S₀`,
`q_b := geoOwner … T_b (markTransport hsb a₀)`.

### §0 Silent germ data (PROVED, ~110 lines)
* `WallGerm.extension_silent`, `WallGerm.pureCut_silent` — `g.Silent` from the named predicates
  (NamedWallPredicates.lean:38,46; SilentCenter.lean:23).
* `SilentFamilyData hn g h δ` — the clauses of `SilentSidesData` (SilentSides.lean:15) minus the redundant
  `CrossingGeometry`; `exists_silentFamilyData` from `silent_sides` (SilentSides.lean:26).
* Accessors (all PROVED): `crossing_iff`, `side_crossing_iff` (the ∃-witness of `GeometricRecordsAgree`,
  GeometricRecords.lean:55), `marks` (`geoMarkList_map_transport`, FlatCarriers.lean:236),
  `interlaces_iff` (`geometric_interlaces_transport`, GeometricInterlacement.lean:69), `crossingSign_eq`
  (sign clause of `GeometricRecordsAgree`), `turn_eq` (`ChirotopesOutsideZerosAgree`, GermChiStability.lean:13,
  with `turnSupport i ∉ Z_pt` because the centre's turns are nonzero — `WeakGeneric.2.1`, `mem_pointZeroTriples`
  ZeroTriples.lean:44, `pointZeroTriple_iff` ZeroTriples.lean:29, `prev_ne_self`/`next_ne_self`/`prev_ne_next`
  Segment.lean:70-78), `exists_silent_sideParameter_lt`.

### §1 Mark points, the path, the corner family (PROVED, ~150 lines)
* `silentMarkPoint g s : Mark g.center → Plane` (= `markPointOn`, FlatCarriers.lean:4435, for `WallGerm n`);
  `silentMarkPoint_zero`, `silentMarkPoint_eq` (= `markPointOn_side` on the whole interval, via
  `visitParameter_eq_of_support_pair_of_geometry` GeometricParameters.lean:36), `continuousAt_silentMarkPoint`
  (= `continuousAt_markPointOn_of`, CS3.lean:1978; `continuousAt_edgeParameter_of_geometry`
  GeometricParameters.lean:58).
* `silentPath g t u := (2u−1)·t`: `silentPath_zero/one` (= `sideTime false/true t`), `continuous_silentPath`,
  `abs_silentPath_le`, `silentPath_eq_zeroParameter`.
* `silentCornerFamily hn g h S q s := fun k => silentMarkPoint g s (geoCornerMark cCG S q k)` (= `cornerFamily`,
  FlatCarriers.lean:4505); `silentCornerFamily_zero`; **`silentCornerFamily_eq`**: at any `s` on the interval
  the family is `recastTuple (geoCornerCount_markTransport …) (geoCornerPolygon (sCG s) (T_s) (q_s))`
  (`geoComponentCornerList_markTransport` FlatCarriers.lean:1631, `geoCornerCount_markTransport` :1646,
  `getElem_congr_lists` CS3.lean:75, `zmod_val_cast` CChamber.lean:82) — through the helper
  `geoCornerMark_markTransport`; `continuous_silentCornerFamily_path`.

### §2 General transport lemmas (PROVED, ~60 lines)
* `geoCarrierCrossings_markTransport` / `card_geoCarrierCrossings_markTransport` — the retained crossings
  are carried (the side clause of `same_retained_crossings_of_marks` FlatCarriers.lean:2452, made general;
  `mem_transportSupport_iff` :1533, `geoOwner_markTransport_iff` :1593).
* `geoIndependent_transport_iff` (`geoIndependent_map_iff`, FlatCarriers.lean:146),
  `geoOwner_twin_ne_transport_iff` (`visitTransport_visitTwin`, FlatCarriers.lean:119).

### §3 Centre genericity — THE NEW GEOMETRY (6 sorries; ~600-700 lines to write)
Stated for ANY `hW : WeakGeneric P` with `hinj : Injective crossingPoint`, `hnv : crossingPoint c ≠ P k`
(the centre's clauses of `SilentFamilyData` at `s = 0`), a carrier `q` with `htr : TracedSuccessor
(weak_crossingGeometry hW) S q` (FlatCarriers.lean:3147) and `htwin : ∀ v, v.1 ∈ S → geoOwner (inr v) ≠
geoOwner (inr (visitTwin v))` — both transported from a generic side in §4.
* PROVED: `regular_of_weakGeneric` (`nonzero_turns_regular` NonFlatCenter.lean:14);
  `crossing_edges_det_ne_zero_of_geometry` (`CrossingGeometry.2.1`, `remote_symm` Segment.lean:106,
  `crossingPoint_mem` Crossings.lean:44); `vertex_injective_of_weakGeneric` (`WeakGeneric.1`, `.2.2.1`,
  `incident` Polygon.lean:60); **`geoCornerPolygon_regular_of_weak`** (`regular_iff_edges` RegularLocus.lean:18,
  `geoCornerPolygon_edge_ne_zero` FlatCarriers.lean:3336, `geoCornerPolygon_not_antiparallel_of_det` :3344,
  `geoInEdge_vertex` :3032, `geoOutSlot_vertex` :3017, `geoInEdge_visit` :3036, `geoOutSlot_selected` :3020,
  `turn_det` Chirotope.lean:87, `visitTwin_edge_ne` CarrierCrossings.lean:209); `single_generic_of_weak`
  (`Shadow.single_generic_of` LinkPositiveLift.lean:160 with the four facts below).
* SORRY `geoCornerPolygon_injective_of_weak` (~50 lines): corner marks distinct (`geoCornerMark_injective`
  FlatCarriers.lean:4904); vertex/vertex `vertex_injective_of_weakGeneric`; vertex/visit `hnv`
  (`geoMarkPosition_evaluation_visit` FlatCarriersDefs.lean:95); visit/visit: `hinj` ⇒ same crossing ⇒
  `visit_eq_or_twin` (CarrierVisitTwin.lean:47) ⇒ twins, contradicting `htwin` with `geoOwner_geoCornerMark`
  (FlatCarriers.lean:4895).
* SORRY `exists_geoBlock` (~250 lines) — `∃ t, GeoBlock hP S q k t`, the block of the edge `k` on the parent
  edge `e = (geoOutSlot c_k).1` from `s = (geoOutSlot c_k).2` to `t`. Geometric fields (`start_lt`, `le_one`,
  `corner_eq`, `next_eq`, `mem_segment_iff`, `mem_interior_iff`, `exists_param`): from
  `geoCornerPolygon_edge_data` (FlatCarriers.lean:3253) / `geo_block_compression` (:3080) /
  `geo_evaluation_eq_outSlot` (:3049) and `edgePoint_injective` (Crossings.lean:88) — the edge segment of `Q`
  at `k` is `{edgePoint P e u : s ≤ u ≤ t}`. Mark fields: `start_mark` is `geoMarkPosition_injective`
  (FlatCarriersDefs.lean:108) since `geoOutSlot c_k = geoMarkPosition (selectedMarkPerm S c_k)` by
  definition (:3000); `end_mark`/`end_vertex` from `geoMarkSuccessor_position_cases` (:2729) on the last
  step `ρ_S^{m−1} c_k` (`geoSmoothingSuccessor_apply` FlatCarriersDefs.lean; `geoOutSlot_unselected` :3026);
  **`interior_mark`** (the hard field, ~120 lines): the block marks `selectedMarkPerm c_k, ρ_S c_k, …,
  ρ_S^{m−1} c_k, c_{k+1}` are consecutive in the sorted marked circle (`ρ_S b = geoMarkSuccessor
  (selectedMarkPerm b)`, unselected interior marks have `selectedMarkPerm b = b`), with strictly increasing
  parameters on `e` (`geoMarkSuccessor_position_cases`); by `geoNextMark_no_mark_between` (:2698, on
  `traversalBetween` Traversal.lean:73 — same edge, parameters strictly between) no other mark has its position
  in the open range; induction on `r < m`. Template: the accepted block lemmas `BlockInterior`,
  `edgeSegment_param`, `block_mark_eq` of SM/LinkPositiveLift.lean:251-435 (generic layer) and
  `geoMarkSuccessor_on_edge` (FlatCarriers.lean:1338) for the `traversalBetween` bookkeeping.
* SORRY **`geoCornerPolygon_meet_of_weak`** (~200 lines), the analogue of `nonadjacent_meet`
  (LinkPositiveLift.lean:443): two distinct closed edges `a ≠ b` of `Q` meet (1) at a common corner, `b = a+1
  ∧ x = Q b` or `a = b+1 ∧ x = Q a`, or (2) at the crossing point of an UNSELECTED crossing whose two edges
  carry the two blocks (`(geoOutSlot c_a).1 ∈ c.val`, `(geoOutSlot c_b).1 ∈ c.val`, distinct) with `x`
  interior to both edges of `Q`. Proof by `exists_geoBlock` at `a` and `b`, `x = edgePoint P e_a u_a =
  edgePoint P e_b u_b`:
  - `e_a = e_b`: `u_a = u_b` (`edgePoint_injective`); WLOG `s_a ≤ s_b`; `s_a < s_b < t_a` is impossible
    (`interior_mark` at the true-corner mark `selectedMarkPerm c_b`); `s_a = s_b` ⇒ `a = b` (`start_mark`,
    `geoCornerMark_injective`); so `u = t_a = s_b` and `end_mark`/`start_mark` give `c_{a+1} =
    selectedMarkPerm c_b`, which is `c_b` (vertex corner ⇒ `b = a+1`) or its twin (selected ⇒ contradicts
    `htwin`).
  - `e_b = e_a ± 1`: `regular_adjacent_meet` (CS3.lean:84) on `P` (regular by `regular_of_weakGeneric`)
    gives `x = P (e_a+1)`, so `t_a = 1` (`end_vertex`: `c_{a+1} = inl (e_a+1)`) and `s_b = 0` (`start_mark`:
    `selectedMarkPerm c_b = inl (e_a+1)`, a visit having parameter in `(0,1)` —
    `crossingParameter_interior_of_geometry` CrossingGeometry.lean:52) ⇒ `c_b = c_{a+1}` ⇒ `b = a+1`.
  - `e_a`, `e_b` remote: `x` lies on both closed segments ⇒ `IsCrossing P {e_a, e_b}` (Crossings.lean:12), the
    crossing `c`, `x = crossingPoint c` (`crossingPoint_unique_of_geometry` CrossingGeometry.lean:41); its
    visits `w_a, w_b` sit at `(e_a, u_a)`, `(e_b, u_b)` (`geometricVisitPosition`, `edgePoint_injective`).
    If `c ∈ S` both are true corners ⇒ endpoints of the blocks (`interior_mark`) ⇒ by `start_mark`/`end_mark`
    each is `selectedMarkPerm c_a`/`c_{a+1}` resp. `selectedMarkPerm c_b`/`c_{b+1}`; the four combinations give
    `b = a+1` / `a = b+1` with `x` the shared corner, or two twins among the corners of `q` (`htwin`). If
    `c ∉ S` both are non-corners ⇒ strictly interior (`start_mark`/`end_mark` would make them corners) ⇒ (2)
    with `mem_interior_iff`.
* SORRY `geoCornerPolygon_tail_off_of_weak` (~50): `Q a ∈ edgeSegment Q b`, `¬ incident a b`: `Q a ∈
  edgeSegment Q a` too; `a ≠ b`; case (1) forces `Q a = Q (a+1)` or `Q a = Q b` with `a ≠ b`, against
  `geoCornerPolygon_injective_of_weak`; case (2) makes the corner point `Q a` (a vertex — `hnv` — or a
  SELECTED crossing point — `hinj`) an unselected crossing point.
* SORRY `geoCornerPolygon_transverse_of_weak` (~40): non-adjacent ⇒ case (2); `edge Q a = c_a • edge P e_a`,
  `edge Q b = c_b • edge P e_b` (`geoCornerPolygon_edge` FlatCarriers.lean:3290, `ccp_det_smul_smul`
  CarrierCornerPolygon.lean:530), `crossing_edges_det_ne_zero_of_geometry`.
* SORRY `geoCornerPolygon_no_triple_of_weak` (~60): interior points are never corners
  (`edgePoint_injective`, `mem_interior_iff`), so all three pairs are in case (2) with ONE crossing (`hinj`);
  its two edges cannot carry three pairwise distinct parent edges (each pair's parent edges are distinct).

### §4 The silent germ at one side parameter (PROVED, ~330 lines)
* `side_marks`, `isDecomposition_iff`, `side_isDecomposition_iff` (`geoIndependent_iff_isDecomposition`
  FlatCarriers.lean:164), `centre_tracedSuccessor` (`traced_successor_of_transport` :1658 with
  `geoCarrierSpec_of_generic` :434 on the positive side), `centre_twin_ne` (`geoOwner_twin_ne_transport_iff` +
  `independent_selected_pair_owners_ne` CarrierIndependentOrder.lean:97, `geoComponentEquivGeneric_owner`
  FlatCarriersDefs.lean:683), `centre_geoCornerCount_ge_three` (`geoCornerCount_ge_three_generic` CS3.lean:1411).
* `centre_single_generic` := `single_generic_of_weak` at the centre; `centre_regular`.
* `family_generic_side` / `family_regular_side` (`silentCornerFamily_eq`, `polyComp_recastTuple`
  CChamber.lean:108, `single_geo_generic` CS3.lean:1429, `regular_recastTuple` CChamber.lean:95,
  `geoCornerPolygon_eq_generic` CS3.lean:1400, `ccpCornerPolygon_regular` CarrierCornerPolygon.lean:679);
  `family_path_generic` / `family_path_regular` (case `silentPath u = 0`).
* **`homfly_family`** (`Link.homfly_positiveDiagram_single_of_family` CS3.lean:592, `positiveDiagram_congr`
  CChamber.lean:567) and **`rotationNumber_family`** (`rotationNumber_family_constant`
  RotationContinuity.lean:45).
* `card_geoCarrierCrossings_sides`, `rotationNumber_geoCornerPolygon_sides` (`rotationNumber_recastTuple`
  CChamber.lean:91), `homfly_geoCornerPolygon_sides` (quantified over the genericity proofs).

### §5 The mark transport and the assembly (PROVED, ~200 lines)
* `sides_crossing_iff`, `sides_crossingParameterOrderAgrees`, `sides_turn_eq`;
  **`sideTransport : MarkTransport hn (g.sideGeneric true t) (g.sideGeneric false t)`** (fields as
  `Carrier.pathTransport` CChamber.lean:953: `markList_transport` :908, `geometric_interlaces_transport`);
  `sideTransport_support`, `sideTransport_toMark` (`rfl` after `Finset.map_map`), `transportSupport_surjective`.
* (i) `sides_markTurn_eq` (`markTurn` CX1.lean:44; `crossingSign_eq` on both sides), `sides_carrierUniform_iff`
  (`MarkTransport.exists_ccpCornerMark_transport` CChamber.lean:350, `turn_ccpCornerPolygon_eq_markTurn`
  CX1.lean:65 on both sides), `sides_huni` (`MarkTransport.carrierUniform_iff_transported` CChamber.lean:413).
* (ii) **`cornerCoefficient_sides`** (centre-indexed, supports/carriers generalised by equations so that
  `subst` applies it to `τ.support S`, `τ.component S q`; `cornerCoefficient_eq_geo` CS3.lean:1494 on both
  sides + the three §4 equalities), `sides_hcoef` (`owner_surjective` CarrierSmoothing.lean:155,
  `MarkTransport.component_owner` CChamber.lean:249).
* **`cornerStateSum_sides`** := `(sideTransport …).cornerStateSum_transport sides_huni sides_hcoef`.

### §6-7 Reduction and the row (PROVED)
* `cornerStateSum_silent_side_const` (prop:C-chamber along a side: `labelledSide_eq_at` GermSides.lean:39,
  `sideTuple_mem_labelledSide` :29, `cornerStateSum_eq_of_mem_labelledChamber` CChamber.lean:1366);
  `cornerStateSum_silent` (both parameters moved to one `t < δ`); `prop_C_silent` (bundle verbatim).

## 2. Faithfulness to the printed proof
* "state sums evaluated only on the generic sides": `cornerStateSum` is only ever applied to `g.sideGeneric b t`
  / `(g.sideTuple b t).property`; the centre enters only through `silentCornerFamily … g.zeroParameter =
  geoCornerPolygon cCG S q` (carrier geometry) — no generic-polygon lemma is applied at the centre: §3 uses only
  `WeakGeneric`, `CrossingGeometry`, `TracedSuccessor` (transported combinatorics) and `htwin` (transported).
* "same finite crossing records and independent supports … identified through the entire small interval":
  `SilentFamilyData` at every `|s| < δ`; `isDecomposition_iff`.
* "nonzero segments, no antiparallel corner": `geoCornerPolygon_regular_of_weak`; "transverse and interior,
  distinct crossings have distinct points": `hinj`, `hnv`, `CrossingGeometry` in §3.
* "lem:rot (ii)": `rotationNumber_family`; "turn signs constant": `sides_markTurn_eq`; "all `m_Q`":
  `card_geoCarrierCrossings_sides`; "over/under designation constant": absorbed in `positiveDiagram` along the
  `Deform` (the lifts are positive at every time, `isPositive_deform_of_family` inside
  `deform_positiveDiagram_single_of_family`); "lc:presentations + lp:core" is replaced, as in prop:C-chamber
  and thm:C-S3, by lit:homfly's planar clause along the family (equal HOMFLY of the two positive lifts).
* "prop:C-chamber makes them independent of the representatives": `cornerStateSum_silent_side_const`.

## 3. Unit split for provers (each unit is provable from the skeleton alone; only §3 is open)

| unit | declarations to prove (all in Skeleton_B.lean §3) | est. lines | inputs |
|---|---|---|---|
| **U3a** | `geoCornerPolygon_injective_of_weak`, `exists_geoBlock` | 300-350 | FlatCarriers.lean §U3 (2694-3360): `geo_block_compression`, `geoCornerPolygon_edge_data`, `geoMarkSuccessor_position_cases`, `geoNextMark_no_mark_between`, `geoOutSlot_*`, `geoSmoothingSuccessor_apply`; the accepted generic-layer model LinkPositiveLift.lean:237-435 |
| **U3b** | `geoCornerPolygon_meet_of_weak`, `_tail_off_of_weak`, `_transverse_of_weak`, `_no_triple_of_weak` | 300-350 | `GeoBlock` (fields only — U3b does not need U3a's proofs), `regular_adjacent_meet` (CS3.lean:84), `crossingPoint_unique_of_geometry`, `geoCornerPolygon_edge`, `ccp_det_smul_smul`, `edgePoint_injective`; model `nonadjacent_meet` … `ccpCornerPolygon_no_triple` LinkPositiveLift.lean:443-578 |

U3a and U3b are independent (U3b consumes `GeoBlock` through `exists_geoBlock`'s statement). If a prover finds
`GeoBlock` under- or over-specified, the contract is: change only the STRUCTURE FIELDS of `GeoBlock` together
with `exists_geoBlock` and the four §3 consumers; nothing outside §3 refers to `GeoBlock`.

Everything in §0-2, §4-7 is already proved (74 declarations); an assembler needs only to paste U3a/U3b in
place of the six `sorry`s.

## 4. Risks and fallbacks
1. **`interior_mark` of `exists_geoBlock`** (the block's marks are exactly the consecutive marks on `e`):
   the `traversalBetween` bookkeeping when the block ends at the vertex `e+1` (position `(e+1, 0)`) and the
   induction over the block. Fallback: weaken `interior_mark` to what the meeting lemma actually uses — "no
   TRUE CORNER mark has its position strictly inside the range" — and prove it by contradiction from
   `geoNextMark_no_mark_between` at the unique step `r` with `param(ρ_S^r c_k) < u < param(ρ_S^{r+1} c_k)`
   (or `< t`); the field is already stated in this weak form.
2. **Case analysis size of `geoCornerPolygon_meet_of_weak`**: 3 parent-edge cases × block-endpoint
   sub-cases. Mitigation: prove the two symmetric helper lemmas `meet_same_edge` and `meet_remote_edges` first
   and derive the meeting lemma; the adjacent-edge case is 20 lines with `regular_adjacent_meet`.
3. `visitTwin`-position identifications (`w_a`, `w_b` are `⟨c, e_a⟩`, `⟨c, e_b⟩`; `visitTwin w_a = w_b`):
   `visitTwin_unique` (CarrierVisitTwin.lean:60), `visitParameter_eq_of_support_pair_of_geometry`; low risk.
4. Statement-level risks: none — the fixed bundle and theorem header are byte-identical to the statement file
   and `prop_C_silent` is closed. The permitted axiom set is exactly that of `prop_C_chamber`/`thm_C_S3`
   (`SM.lit_homfly`) plus `sorryAx` until U3a/U3b land.
5. If U3 stalls entirely (not expected): the only alternative is R1 (RecordIso through `record_of_single_polygon`
   LinkDiagramRecord.lean §F and `SM.presentations` PolynomialBlock.lean:1177) — strictly more work, since it
   needs the same block combinatorics on the generic sides plus the record plumbing.

## 5. Verification
```
cd work/lean && lake env lean ../drafts/csilent/Skeleton_B.lean      # no errors, 6 × "declaration uses 'sorry'"
# axioms (append to a copy):  #print axioms SM.prop_C_silent
#   → propext, sorryAx, Classical.choice, Quot.sound, SM.lit_homfly
```
