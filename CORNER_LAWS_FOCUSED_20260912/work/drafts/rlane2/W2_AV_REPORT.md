# W2_AV_REPORT — unit AV: row 170 `R:availability_0_1` (`RProof.availability_zero_one`) PROVED

Written 2026-09-14 by the AV unit (R lane part 2, wave 2; plan of record `NOTES_FINAL.md` §3, §11 "U-AV",
§12 item 4). File: `work/drafts/rlane2/W2_AV.lean` (4734 lines = `RLaneX1_Assembled.lean` (3079) + one import
line + the inserted unit, 1635 + 20 lines).

Compile: `cd work/lean && lake env lean ../drafts/rlane2/W2_AV.lean` → exit 0, **0 errors**, exactly **seven**
`declaration uses sorry` warnings — the seven still-open row theorems, untouched: L516 `exterior` (168),
L3091 `generic_transport` (173), L3152 `generic_selected` (174), L3303 `extreme_pair_zero` (175), L3443
`extreme_transport` (176), L3529 `extreme_selected` (177), L3609 `cv_R` (178); no other warning; ~12 s.
`diff RLaneX1_Assembled.lean W2_AV.lean | grep '^<'` → exactly `<   sorry` (the row-170 body). Hunks: `5a6`
(the import `CV.PieceHomflyTransport`, the library the task names for the transport across the wall),
`659a661,2295` (the unit, inserted directly before the row-170 theorem, after `PRE_170_fibre_correspond`),
`668c2304,2323` (the proof replacing the `sorry`). **No definition, structure, theorem statement, name or
docstring of the frozen file was changed.** Nothing under `work/lean` was written; no `lake build`.

`#print axioms RProof.availability_zero_one` (scratch copy with the print appended):
`[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` — exactly the axiom
set of the accepted `CV.gausscode_polynomial` and `CV.pieceHomflyTransported` (the three declared literature
interfaces of `SM/LinkInterfaces.lean`, reached through `homfly` and CV:ax:gausscode); no `sorryAx`. The
X₁-free part of the toolkit is standard-axiom only: `AV_carrierEquiv`, `AV_rotationNumber_tcp`,
`AV_wall_of_event`, `AV_exists_eventRadius` → `[propext, Classical.choice, Quot.sound]`.

## 1. What is proved (the three X₁ fields; the presupposition fields are unit PRE's)

| field | lemma (line) | content |
|---|---|---|
| `summand_transport` | `AV_170_summand_transport` (L2236) | `SummandTransport` at every `J` of an availability-`≤ 1` fibre: `wind` equal, a carrier bijection `AV_carrierEquiv` with `wt`, `R(L)`, `w_{S,L}`, `P_{S,L}`, `Ω₁` matched (`AV_summandTransport`, L2226) |
| `summands_agree` | `AV_170_summands_agree` (L2254) | both rows present (`F1.compose_geom`; independence carried by the wall data) and `rowTerm_of_mem_Ind` + `Fintype.prod_equiv` along the carrier bijection (`AV_rowTerm_eq_of_summandTransport`, L2214) |
| `fibre_identity` | `AV_170_fibre_identity` (L2274) | the far fibre is the `supportEmb` image (`PRE_170_fibre_correspond`), `Finset.sum_map`, `transportSupport` distributes over `∪`, then `summands_agree` term by term |

Row theorem (L2297): radius `min δ_L (min δ_F δ_R)` of the accepted rows 164 (`localization`), 171
(`fibre_partition`) and the sign data `AV_exists_eventRadius hE`; `fibre_zero/one/correspond` from the PRE
field lemmas; `e ≠ f`, `f ≠ g`, `e ≠ g` from `h3` (`AV_ne_of_remote`).

## 2. The transport across the wall (the "U-EXT toolkit", built here since U-EXT was not available)

The library's `GeoMarkTransport` (SM/GeoMarkTransport.lean) needs the sorted mark list carried *literally*;
across the RIII wall it is not (R-LOC-2 (2): three adjacent same-edge visit pairs reverse), so a new transport
was built. At availability `≤ 1` the support `S = Q ∪ J` contains at most one triangle crossing and the other
triangle crossings are dominated by `Q`; every reversed pair therefore consists of at most one corner, so the
**corner cycles are carried** while non-corner marks (the visits of the dominated triangle crossings) may
change carrier. The development is generic, on two `CrossingGeometry` polygons with the same crossing supports:

* **`AV_Wall hP hP' hs T S`** (L689) — wall data: `S` independent; visit-key order carried except for
  same-edge pairs of distinct `T`-crossings (`key_lt`); interlacement carried off `T × T` (`interlaces_iff`);
  of two distinct `T`-crossings one is dominated by `S` through a crossing outside `T` (`dominated`;
  `AV_Dom`, L678); vertex turns and crossing signs equal (`turn_eq`, `sign_eq`); a common reference vector
  seeing every edge direction with the same nonzero sign (`ray`). `AV_Wall.mono` passes the data to any larger
  independent support (used for `S ∪ K_H`); `indep'` carries independence.
* **Next corner / corner successor** (L850, L930): `AV_nextCorner hP S m` = the first `ρ`-iterate of `m`
  that is a corner (`Nat.find`); it lies on the carrier of `m` (`AV_nextCorner_owner`), is `m` at a corner,
  and is unchanged by `ρ` at a non-corner. Its order-theoretic specification `AV_NCSpec` (least corner with
  key `≥ key m`, or the vertex `0` when none — `AV_succ_spec`, L977, from the sorted `geoMarkList`) is unique
  (`AV_ncspec_unique`) and is carried for **good** marks (`AV_Good`, L795: every mark except the visits of
  dominated `T`-crossings): `AV_nextCorner_transport` (L1176). The corner successor
  `AV_cornerSucc c = AV_nextCorner (ρ_S c)` (the first corner strictly after the outgoing slot of `c`) has
  the analogous specification on corners only and is carried at every corner: `AV_cornerSucc_transport` (L1216).
* **`AV_carrierEquiv`** (L1301): the carrier of `P'` through the transported next corner (`Quotient.lift`,
  constant on `ρ_S`-cycles by `AV_carrierMap_aux`), with the inverse built from the forward transport only
  (no symmetric wall data needed). Ownership of good marks is carried (`AV_owner_transport`, L1328).
* **Literal carriage of the corner list** (`AV_cornerList_eq`, L1348: both lists are strictly sorted by the
  key, nodup, with the same members — `List.Perm.eq_of_pairwise`), hence `geoCornerCount`, `geoCornerMark`,
  the corner polygon up to `geoRecast` (`AV_cornerPolygon_eq`, L1409), the corner turns (`AV_turn_tcp`,
  L1435: vertex corners by `turn_eq`, smoothing corners by `sign_eq`, through
  `geoCornerPolygon_turn_vertex/visit`), uniformity, `wt` (`AV_selector_eq`) and `wind` (`AV_geoWind_eq`,
  L1487) — the accepted §2d–2e proofs of SM/GeoMarkTransport.lean on the wall bijection.
* **Retained crossings and pieces**: `AV_geoCarrierCrossings_eq` (L1522; a dominated crossing is retained
  by no carrier on either side, `geo_neighbor_not_mem_geoCarrierCrossings`; the visits of an undominated
  crossing are good), `AV_mem_U_iff` (L1554), the residual-graph isomorphism `AV_residualIso` (L1583),
  `AV_pieceEquiv` (L1604), `AV_pieceLabels_eq`, `AV_pieceWrithe_eq`, `AV_piecesOn_transport_eq` (L1659) —
  CV/ChamberInvII.lean §5 on the wall bijection.
* **HOMFLY of the positive lift** (`AV_homfly_lift_eq`, L1696): the occurrence bijection
  `AV_liftEquiv` (parent visits, `CV.liftVisitEquiv` ∘ `visitTransport`) is a record isomorphism —
  (a) cyclic order by `CV.visitBetween_iff_key` and the carried visit keys (no two retained crossings form a
  reversed pair, since retained crossings are undominated), (b) double points by `visitTransport_visitTwin`,
  (c) over/under by `CV.overBit_eq_true_iff_parent` and `sign_eq`, (d) all signs `+1` — assembled by
  `CV.recordIsoOfData` and closed by `CV.gausscode_polynomial`. Then `AV_pieceHomfly_eq` (L1889): at `P'` the
  carrier of `S' ∪ K'` (the support chosen at `P'`) and the wall copy of the carrier of `S ∪ K_H` retain
  exactly the labels of the piece (`pieceCarrier_geoCarrierCrossings`, `AV_pieceLabels_eq`), so
  `CV.homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq` (row 156) and `AV_homfly_lift_eq` at `S ∪ K_H`
  (wall data by `AV_Wall.mono`) give `P_{H'} = P_H`; `AV_groupedPoly_eq` follows.
* **Rotation** (`AV_rotationNumber_tcp`, L1800; `AV_carrierR_eq`, L1925): no path exists across the wall
  (the centre is not a `CrossingGeometry`), so CV:def:rot's ray formula is used instead — `rot = Σ_i ε_i(r)`
  for any admissible `r` (`CV.rot_eq_rotRay`, `CV.rotRay_eq_rotationNumber`), each `ε_i` a function of three
  determinant signs (`CV.epsRot_eq_epsOfSigns`): the corner turn (carried, `AV_turn_tcp`) and the signs of
  `det(r, ·)` at the two corner-polygon edges. Both corner polygons run along the same original edges
  (`geoCornerPolygon_edge_smul`, positive multiples of `edge P (geoOutSlot …)`, the slot label carried by
  `AV_outSlot_transport`), and the wall datum `ray` says `r` sees each original edge with the same nonzero
  sign on both sides. `w_{S,L}` is the number of retained crossings (`groupedWrithe_eq_card_geoCarrierCrossings`),
  so `AV_groupedWrithe_eq`, `AV_slot_eq`, `AV_Omega1_eq` (L1947) follow.

## 3. The event data (`AV_EventRadius`, L1976; `AV_exists_eventRadius`, L2013)

lem:guardconst in the filter form `G1.eventually_sign_eq_of_not_mem`: the `G1` members (`turn P i =
sign (G1 P i)`, `turn_det`) are unconditional and outside `Z` (`hE.1`), so the vertex turns are constant
near the centre; a `G5` member `det(d_a, d_b)` active at some punctured parameter (`Generic.crosses_iff`) is
outside `Z` (`G1.g5_not_mem_zeroSet`), so the crossing signs of every crossing pair are constant near the centre
(both orders, `det_swap`); a reference vector admissible at the centre (`CV.exists_admissible E.center_polygon`)
keeps its signs near the centre by continuity of `E.curve` (`AV_continuous_det`, `ContinuousAt.eventually_lt`).
Finite intersections by `Filter.eventually_all`, one radius by `E.eventually_center_iff_radius`.
`AV_wall_of_event` (L2162) then assembles the wall data of a fibre: `Q ∪ J` independent (`F1.compose_geom`);
`key_lt` from `hL.gauss_words` (`ExactTriangleVisitOrders`; `AV_key_lt_of_gauss`, L2126, with
`AV_triangle_of_union`: two same-edge visits whose supports cover `{e,f,g}` are visits of distinct triangle
crossings); `interlaces_iff` from `hL.interlace_toggle` (`L.xor_iff_of_not_right`); `dominated` from
`|𝓐(Q)| ≤ 1` (`Finset.card_le_one`, `F1.mem_avail`: the unavailable triangle crossing interlaces a member of
`Q`, outside `T` by `Disjoint Q T`); turns, signs, ray from `AV_EventRadius`.

## 4. Readings checked against the frozen texts (no statement changed; none found false)

* R_ASSEMBLY_SPEC.md "At availability zero or one the local supports themselves correspond, but that does
  **not** prove their summands agree. Prove the required carrier/record, selector, rotation and coefficient
  transport": rendered by NOTES_FINAL §3 as `SummandTransport`; the proof is exactly the carrier-by-carrier
  transport of the scout report's G7 reading — the three adjacent transpositions of R-LOC-2 (2) move only
  unselected marks (availability 0) or one selected `T`-visit past an unselected dominated one (availability
  1), so the corner cycles, the retained crossings, the pieces, the piece records and the rotation are carried.
* The only wall-dependent inputs are the accepted R-LOC-2 clauses (`gauss_words`, `interlace_toggle`,
  `crossing_set_constant`), R-PAR's availability set, lem:guardconst (through the CV-DOM `G1` unit), CV:def:rot
  (ii) and CV:lem:pieceintrinsic (row 156, `homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`) — as
  NOTES_FINAL §10 lists for row 170 (R:fibre_partition, the transport of all carriers, 156).
* `summands_agree` needs no presence hypothesis on the far side: independence of `Q ∪ J` is carried by the
  wall data (`AV_Wall.indep'`), as the field's docstring ("absent rows on both sides being `0`") allows.

## 5. Helpers added (all prefixed `AV_`, section `AV` L669–L2208, plus the four field/assembly lemmas)

Definitions: `AV_Dom`, `AV_Wall` (+ namespace lemmas `mono`, `not_dom_of_mem`, `dom_transport`, `indep'`,
`mark_key_lt`), `AV_Good`, `AV_nextCorner`, `AV_cornerSucc`, `AV_NCSpec`, `AV_CSSpec`, `AV_carrierMap`,
`AV_carrierInv`, `AV_carrierEquiv`, `AV_tcp` (the corner polygon read at `P'`), `AV_residualIso`,
`AV_pieceEquiv`, `AV_liftEquiv`, `AV_EventRadius`. Theorems: the next-corner theory (`AV_exists_corner_pow`,
`AV_nextCorner_corner/of_corner/succ/owner`, `AV_find_succ`, `AV_smoothing_of_not_corner`,
`AV_owner_pow_of_not_corner`, `AV_cornerSucc_corner/owner`, `AV_key_nonneg`, `AV_key_inl_zero`,
`AV_geoMarkList_pairwise_lt`, `AV_geoMarkList_key_lt_iff`, `AV_succ_spec`, `AV_ncspec_unique`,
`AV_nextCorner_spec(_aux)`, `AV_csspec_unique`, `AV_nextCorner_succ_spec`), the transports
(`AV_good_vertex/of_corner/of_not_dom/of_mem_U`, `AV_good_key_lt`, `AV_corner_transport`,
`AV_ncspec_transport`, `AV_nextCorner_transport`, `AV_csspec_transport`, `AV_corner_selectedMarkPerm`,
`AV_cornerSucc_transport`, `AV_carrierMap_aux/pow/owner`, `AV_carrierInv_aux/pow/owner`,
`AV_carrierEquiv_owner`, `AV_owner_transport(_corner)`), the corner data (`AV_cornerList_pairwise`,
`AV_cornerList_eq`, `AV_cornerCount_eq`, `AV_cornerMark_eq(')`, `AV_cornerPolygon_eq`, `AV_tcp_eq`,
`AV_turn_tcp_eq_turn_cast`, `AV_turn_tcp`, `AV_turn_cornerPolygon_eq`, `AV_carrierUniform_iff`,
`AV_selector_eq`, `AV_geoWind_eq`), retained crossings and pieces (`AV_not_dom_of_retained`,
`AV_not_mem_U_of_dom`, `AV_geoCarrierCrossings_eq`, `AV_card_geoCarrierCrossings_eq`, `AV_mem_U_iff`,
`AV_residualIso_apply_val`, `AV_pieceEquiv_pieceOf`, `AV_pieceLabels_eq`, `AV_pieceWrithe_eq`,
`AV_mem_piecesOn_transport_iff`, `AV_piecesOn_transport_eq`), the lift (`AV_liftVisit_liftEquiv`,
`AV_homfly_lift_eq`), the rotation (`AV_edge_geoRecast`, `AV_outSlot_transport`, `AV_edge_tcp`,
`AV_sign_det_smul_left/right`, `AV_sign_det_swap`, `AV_rotationNumber_tcp`), the def:X1 objects
(`AV_transportSupport_union`, `AV_subset_union_left'`, `AV_groupedWrithe_eq`, `AV_pieceHomfly_eq`,
`AV_groupedPoly_eq`, `AV_carrierR_eq`, `AV_slot_eq`, `AV_Omega1_eq`, `AV_weight_eq`, `AV_wind_eq`), the
event (`AV_eventRadius_mono`, `AV_g1_not_mem_zeroSet`, `AV_turn_eq_sign_G1`, `AV_continuous_det`,
`AV_exists_eventRadius`, `AV_card_triple`, `AV_pair_mem_triangleSupports`, `AV_triangle_of_union`,
`AV_key_lt_of_gauss`, `AV_fibrePartitionData_mono`, `AV_wall_of_event`), and the row
(`AV_rowTerm_eq_of_summandTransport`, `AV_summandTransport`, `AV_170_summand_transport`,
`AV_170_summands_agree`, `AV_170_fibre_identity`, `AV_ne_of_remote`). 120 declarations.

## 6. Notes for the assembler and the next waves

* **Import added**: `import CV.PieceHomflyTransport` (line 6) — the only change outside the inserted ranges;
  it brings CV/PieceIntrinsic.lean (`liftVisitEquiv`, `visitBetween_iff_key`, `overBit_eq_true_iff_parent`,
  `det_smul_left'`) and CV/RecordHomfly.lean (`recordIsoOfData`). The portable library file must add it too.
* **Instance friction (NOTES_FINAL §12 risk 13) met and resolved**: the CV library's `S ∪ pieceSupport …` is
  elaborated with the classical `DecidableEq`, the R lane's `Q ∪ J` with `instDecidableEqCrossing`. In
  `AV_pieceHomfly_eq` the unions are never written; they are inferred from the library terms, and the one
  subset proof passes the instance explicitly (`AV_subset_union_left'`). `Finset.mem_filter` fails on the
  filters of SM/FlatCarriersDefs.lean for the same reason — use `mem_geoCarrierCrossings`.
* **Reuse by U-EXT (row 168) and the other wall rows**: the toolkit is generic in `(hP, hP', hs, T, S)`; only the
  clause `dominated` is specific to availability `≤ 1`. At full availability (rows 168, 173, 176, 177) the
  triangle crossings are undominated, so `AV_Wall` does not hold as stated; the corner-cycle/next-corner
  machinery (`AV_nextCorner`, the specifications, `AV_cornerList_eq`, `AV_homfly_lift_eq`,
  `AV_rotationNumber_tcp`) still applies to every carrier whose corner order is carried, and the event data
  `AV_EventRadius` (turns, signs, ray) are row-independent. A weaker replacement of `dominated` — "no two
  reversed visits are both corners of the carrier in question" — would give the triangle-disjoint carriers of
  R-EXTERIOR-1 directly.
* `AV_fibrePartitionData_mono` duplicates `A2_fibrePartitionData_mono` (which sits after the row theorem);
  `AV_transportSupport_union` duplicates `A2_transportSupport_union` likewise. Either copy may be dropped when
  the file is placed.
* `A2_cvRNear_of_rows` can now consume `availability_zero_one` (row 170 PROVED) together with
  `generic_selector` (row 172 PROVED); rows 173–177 remain.
