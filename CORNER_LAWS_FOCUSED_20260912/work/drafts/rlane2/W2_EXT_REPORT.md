# W2_EXT_REPORT — unit EXT, row 168 R:exterior (WHOLE row), 2026-09-14 08:30 UTC / 4:30am ET

File: `work/drafts/rlane2/W2_EXT.lean` (5015 lines) = `RLaneX1_Assembled.lean` (3079 lines) + one import line
(`import CV.PieceHomflyTransport`, line 4: the transport library named in the task; it pulls in
`CV.PieceIntrinsic`) + the inserted `section EXT` (lines 551–2440, 96 declarations prefixed `EXT_`)
placed between the frozen bundle `ExteriorData` and the row theorem + the proof body of `RProof.exterior`
(line 2443). `diff RLaneX1_Assembled.lean W2_EXT.lean | grep '^<'` prints exactly one line, `  sorry`
(the placeholder body of `exterior`); no definition, structure, theorem statement, name or docstring was
touched; the other seven row theorems keep their placeholders.

Compile: `cd work/lean && lake env lean ../drafts/rlane2/W2_EXT.lean` — exit 0, **0 errors**, no warnings other
than exactly seven `declaration uses sorry` at the seven other row theorems (`availability_zero_one`,
`generic_transport`, `generic_selected`, `extreme_pair_zero`, `extreme_transport`, `extreme_selected`, `cv_R`);
~13 s. Nothing under `work/lean` was written; no `lake build`.

`#print axioms` (scratch copy `/tmp/ext/W2_axioms.lean`): `RProof.exterior`, `EXT_168_independent_of_A`,
`EXT_168_wall_invariant`, `EXT_168_factorization`, `EXT_exteriorFactor_eq_base`, `EXT_exteriorFactor_wall`,
`EXT_homfly_wall` — `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]`;
`EXT_rotation_wall`, `EXT_exists_guardRadius`, `EXT_markSucc_wall`, `EXT_block` — `[propext, Classical.choice,
Quot.sound]`. The three literature interfaces are the accepted ones of work/lean/axiom-policy.json
(`lit:homfly`, `lp:lm`, `lp:lm-uniqueness`); they enter only through the accepted CV:ax:gausscode replacement
`CV.gausscode_polynomial` (row 163) — the same axiom list as the accepted `CV.chamberinv_ii`,
`CV.pieceHomflyTransported` and `CV.homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq` (checked in
`/tmp/ext/Ax2.lean`). No new axiom, no `sorryAx`.

## Proved

* **`RProof.exterior`** (row 168, whole): `∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ ExteriorData hn E e f g δ` with
  `δ := min δ_L δ_G`, `δ_L` the radius of the accepted `localization` (row 164, shrunk by
  `F1.localizationData_mono`) and `δ_G` the guard radius `EXT_exists_guardRadius` (lem:guardconst for the `G1`
  and `G5` members, uniformly over the finitely many members, `Filter.eventually_all` +
  `Event.eventually_center_iff_radius`).
* The three fields as standalone lemmas (statement = the field with the row's binders; hypotheses
  `hL : LocalizationData E e f g δ`, `hguard : ∀ u, |u| < δ → EXT_GuardAt E u`, `hE` where used):
  `EXT_168_independent_of_A hn E e f g δ` (line 1415; needs no hypothesis at all — it is a
  one-polygon statement), `EXT_168_wall_invariant hn E e f g hL hguard hE` (line 2368),
  `EXT_168_factorization hn E e f g hL hguard hE` (line 2401).

## How the printed proof is rendered (R_ATTACHMENT_WARRANTS.md R-EXTERIOR-1 §1–§4; NOTES_FINAL §2)

Notation: `P = E.curve t`, `P' = E.curve t'`, `τ = markTransport hs` (vertices fixed, visits through
`visitTransport hs`), `φ = crossingTransport hs`, `ρ_S = geoSmoothingSuccessor hP S`, the bad marks
`EXT_TriVisit e f g` = the six triangle visits (line 1104; `TriangleDisjoint ↔ EXT_Avoids (¬TriVisit)`,
`EXT_triangleDisjoint_iff`).

1. **Carrier correspondence (one engine for §1 and §4).** `EXT_sameCycle_of_conj_on` (line
   561): for permutations `f`, `g` and an equivalence `e`, on an `f`-invariant set `U` on which
   `g ∘ e = e ∘ f`, the `g`-cycle of `e a` is the image of the `f`-cycle of `a` (from the accepted
   `sameCycle_congr_of_eqOn_bijOn` and `sameCycle_of_equiv_conj`). `EXT_block` (line 593) applies it to
   `f = ρ_S`, `g = ρ_S'`, `U` = the marks of a good-avoiding carrier `q` (invariant by
   `geoSmoothingSuccessor_bijOn_owner`), under the hypothesis `hcomm : ∀ a, Good a → Good (ρ_S a) → ρ_S' (e a) =
   e (ρ_S a)`. `EXT_corr q := geoOwner S' (e a₀)` for any mark `a₀` of `q` is the corresponding carrier;
   `EXT_corr_iff` (the block of `corr q` is the image of the block of `q`), `EXT_corr_avoids`, `EXT_corr_corr`
   (inverse, given `hcomm` in both directions).
2. **Mark and corner lists.** `EXT_markList_map` (line 671): both lists are the strictly increasing
   enumerations of corresponding sets of marks, so `(markList q).map e = markList' (corr q)` once the key
   order of the marks of `q` is carried (`List.Perm.eq_of_pairwise`); `EXT_cornerList_map` (corners correspond),
   `EXT_cornerCount_eq`, `EXT_cornerMark_eq`, `EXT_cornerPolygon_eq` (line 768: the corner polygon
   of `corr q` is the polygon of the images of the corner marks of `q`, recast along the equal corner counts —
   the `GeoMarkTransport.geoCornerPolygon_eq` pattern, but for one carrier instead of the whole mark list).
3. **Retained crossings and pieces (§2).** `EXT_carrierCrossings_map` (line 799):
   `geoCarrierCrossings' (corr q) = (geoCarrierCrossings q).map φ`. Pieces: `EXT_walk_transfer` (line
   831) carries a walk of `G[U(S)]` starting in a closed set `X` to a walk of `G'[U'(S')]`; with the
   closure `EXT_closed` (line 1055: lem:carriers (iv), `owner_eq_of_interlaces_mem_U` — "no available
   triangle crossing interlaces an undominated crossing carried by `L`", the insulation argument of §2, in the
   form "an undominated crossing interlacing a retained crossing of `q` is retained by `q`") this gives
   `EXT_mem_labels_iff` (line 878): the labels of the piece of `c ∈ X` correspond under `φ`. The
   bundle `EXT_PieceSetting` (line 866) collects the hypotheses; `EXT_pieceSetting` (line
   1072) builds it at `X = geoCarrierCrossings q` from the crossing correspondence and the agreement of
   interlacement on `X`. `EXT_piecesOn_prod`/`_sum` (line 998) reindex `∏/∑_{H ∈ piecesOn q}` along
   the piece maps `EXT_pieceMap`/`EXT_pieceMapRev` (`Finset.prod_bij'`; pieces are determined by their labels,
   `EXT_piece_eq_of_labels_eq`).
4. **The per-carrier data (§3).** `EXT_weight_eq` (line 1134: `wt` from the turn sequence,
   `cornerSelector_congr_turn`/`_geoRecast`), `EXT_carrierR_eq` (line 1147: `R = |rot|` from the rotation
   number, `rot_eq_rotationNumber`), `EXT_groupedWrithe_eq`, `EXT_groupedPoly_eq`, `EXT_Omega1_eq` (line
   1193); `EXT_pieceHomfly_eq_of_labels` (line 1206: two pieces of one polygon with the
   same labels have the same `P_H`, the accepted choice independence
   `homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq` of lem:pieceintrinsic applied to the two
   `pieceCarrier`s); `EXT_exteriorFactor_eq` (line 1217): the exterior factor is reindexed along
   `EXT_corr` (`Finset.prod_nbij'`) given `hcomm`, `hcomm'` and the per-carrier equality of `wt · Ω₁`.
5. **Same polygon, `Q ∪ A` vs `Q` (§1–§3; field `independent_of_A`).** `EXT_succ_union` (line
   1312): `ρ_{Q∪A} a = ρ_Q a` at every non-triangle mark (`geoSmoothingSuccessor_union_of_disjoint`,
   `selectedVisitTwin_of_not_mem`; the union's `DecidableEq` instance is aligned by `convert`).
   `EXT_exteriorFactor_eq_base` (line 1332): `C_{Q,σ}(∅) = C_{Q,σ}(A)` for every `A ⊆ T` with `Q ∪ A`
   independent (identification `hs := fun _ => Iff.rfl`, `markTransport_self`). `independent_of_A` is two
   instances.
6. **The wall (§4).** `EXT_key_lt_wall` (line 1556): the traversal order of two marks is carried by `τ`
   unless they are the two visits of a bundle pair on their common edge (`traversalKey_lt_iff` +
   `ExactTriangleVisitOrders` clause 2 = `LocalizationData.gauss_words`, R-LOC-2 (2)–(3); a good mark is never in a
   bundle pair, `mem_triangleSupports_of_union`). `EXT_not_between_succ` (line 1531: no mark lies
   strictly between a mark and its `ρ`-successor, by indices in the sorted list) and
   `EXT_sorted_next_of_no_cyclic_between` (line 1446, a verbatim `EXT_`-named copy of the SEL
   port of `SM.sorted_next_of_no_cyclic_between`, needed before `section SEL`) give `EXT_markSucc_wall` (line
   1657): `ρ' (τ a) = τ (ρ a)` for a good `a` with good `ρ a` — "erasing the six `T` visits gives the
   same marked traversal word on both sides"; `EXT_geoMarkSuccessor_ne` (`ρ` has no fixed point, `n ≥ 3`).
   `EXT_succ_wall` (line 1702) adds the selected exchange (`selectedMarkPerm_markTransport`), giving `hcomm`
   for the base row `Q` and, through `hs.symm` (`EXT_markTransport_symm_eq`, `EXT_transportSupport_symm`), `hcomm'`.
   `EXT_turn_wall` (line 1727): the corner turns are carried — at a vertex corner `τ_i` of the polygon
   (`turn_vertex_of_traced`), at a `Q`-smoothing corner the crossing sign (`turn_visit_of_traced`), both
   wall-invariant by the guard radius (`EXT_turn_eq_of_guard`, `EXT_G5_sign_eq_of_guard`); the carriers are traced
   by `carrierword_traced`. The guard: `EXT_GuardAt` (line 1766), `EXT_exists_guardRadius` (line
   1813); `EXT_crosses_all` (line 1788: a crossing pair of one side is an active pair at every
   parameter, the centre included — the four `G2` members are unconditional and outside `Z`).
7. **HOMFLY across the wall (§4, "ax:gausscode … ax:homfly").** `EXT_homfly_wall` (line 1872): two
   carriers on the two sides with corresponding retained crossings have positive lifts with the same HOMFLY
   polynomial when the visit order (`hkey`) and the divide signs `det(d_v, d_{twin v}) > 0` (`hdet`) of the
   retained crossings are carried: the identity on parent visits (`liftVisitEquiv`, `visitTransport`) satisfies
   CV:def:record (a)–(d) — (a) `visitBetween_iff_key` on both sides + `hkey`; (b) `liftVisit_twin` +
   `visitTransport_visitTwin`; (c) `overBit_eq_true_iff_parent` + `hdet`; (d) all signs `+1` — and
   `recordIsoOfData` + `gausscode_polynomial` conclude. This is the two-polygon analogue of the accepted
   `exists_recordIso_of_geoCarrierCrossings_eq` (CV/PieceIntrinsic.lean). `EXT_pieceHomfly_wall` (line
   1929) applies it to the two `pieceCarrier`s of corresponding pieces with triangle-free labels (the
   retained crossings of a triangle-disjoint carrier are triangle-free, `EXT_carrierCrossings_triFree`); `hkey`
   from `EXT_key_lt_wall`, `hdet` from the guard (`EXT_det_pos_iff_of_guard`). Note: `pieceSupport` (a
   `Classical.choose`) is NOT transported — the record isomorphism compares the two chosen piece carriers directly.
8. **Rotation across the wall (§4, "for rotation …").** `EXT_rotation_wall` (line 2218): along the
   affine parameter path `EXT_seg t t'` (line 1980) through the wall, the corner polygon of the exterior
   carrier, read on `P(u)` at the (fixed) corner marks (`geoMarkPoint`, the accepted `geoCornerFamily` shape), is
   continuous (`EXT_family_continuous`, line 2184: vertices by projection, `Q`-crossing points by Cramer's
   rule at `G5 ≠ 0` on the guard radius) and regular at every `u` including the wall (`EXT_family_regular`, line
   2151): `EXT_familyEdge` (line 2056) writes every edge as `(p_b(u) − p_a(u)) • d_h(u)` along the
   polygon edge `h` of the corner's outgoing slot (`geoCornerPolygon_outEdge_eq_inEdge_of_independent`,
   `edgeParameters_intersection`), `EXT_pa_lt_pb_all` (line 2098) keeps `p_a(u) < p_b(u)` at every `u` (a
   vertex vs a crossing: the Cramer parameter of an active pair is interior; two `Q`-crossings on one edge: their
   order is wall-invariant at every parameter, `TripleEventData.other_orders_persist`, R-LOC-2 (3), with the sign at
   `t` from `geoCornerPolygon_edge_smul`), and consecutive edges meet at `G1 ≠ 0` (vertex) or `G5 ≠ 0`
   (`Q`-crossing), both nonzero on the guard radius (`EXT_regularPair_of_det`). Then `rotationNumber_family_constant`
   (SM/RotationContinuity.lean, the accepted lem:rot machinery) gives the same rotation number at `u = 0` (`P`) and
   `u = 1` (`P'`, recast by `EXT_cornerPolygon_eq`). Tier 1 is NOT needed at the wall polygon: only continuity and
   regularity of the corner family are used, as the printed §4 says ("the carrier avoids the triple-point visits,
   so its incident directions have common limits at the wall; nonvanishing `G1/G5` prevents a principal turn from
   meeting the branch boundary").
9. **Assembly.** `EXT_exteriorFactor_wall` (line 2271): `C_{Q',+}(∅) = C_{Q,−}(∅)` for the base row —
   steps 1–8 at `S = Q`, `S' = transportSupport hs Q`, interlacement on the retained crossings by
   `F1.graph_on_W_same hL`. `wall_invariant` = base reduction on each side (step 5) + the wall step;
   `factorization` = `rowTerm_eq_exterior_mul_touching` (the accepted split) + the same two reductions.

## Unproved

Nothing in this unit. The whole row `RProof.exterior` is proved; no field lemma is left open and no statement had
to be changed or strengthened. (Every hypothesis used is one of the row's own — `hE`, the accepted `localization`
row, `hn` — or the accepted library.)

## Statement check (rule 4)

All three fields are true as frozen. Two remarks for the reviewer, not defects:
* `independent_of_A` and `factorization` quantify `hA : Q ∪ A ∈ Ind` with `A ⊆ T` arbitrary; the proof never
  uses full availability nor `Q ∈ outsideSupports` beyond `Q ∈ Ind` and `Q ∩ T = ∅` (the printed "arbitrary
  exterior geometry"). `independent_of_A` holds on any generic polygon (`EXT_exteriorFactor_eq_base`).
* `wall_invariant` is proved for any `A`, `A'` with `Q ∪ A`, `Q' ∪ A'` independent (`Q' ∈ Ind'` is derived from
  `hA'` by `PRE_mem_Ind_of_subset`), on the punctured radius `min δ_L δ_G` — the row's `δ` may be smaller than
  `localization`'s because the `G1`/`G5` sign constancy (lem:guardconst) is a separate radius; both are
  `≤ E.radius`.

## Library used (all accepted / ported)

RProof/Cores.lean (`localization`, `LocalizationData.gauss_words`, `F1.graph_on_W_same`, `F1.localizationData_mono`,
`G1.eventually_sign_eq_of_not_mem`, `G1.g2/g5_not_mem_zeroSet`, `G1.exists_punctured_parameter`,
`L.mem_triangleSupports_of_union`, `P1.mem_triangleCrossings`, `F1.mem_outsideSupports`); the assembled file's
`PRE_mem_Ind_of_subset`, `rowTerm_eq_exterior_mul_touching`, `mem_Ind_of_mem_outsideSupports`;
SM/FlatCarriersDefs, SM/FlatCarriers (`markTransport`, `selectedMarkPerm_markTransport`, `isTrueCorner_markTransport`,
`mem_transportSupport_iff`, `geoOutSlot_*`, `geoInEdge_*`, `geoCornerMark_mem`), SM/GeoCarrierCount
(`geoSmoothingSuccessor_union_of_disjoint`, `geoMarkSuccessor_getElem`), SM/GeoMarkTransport (`geoRecast` toolkit,
`geo_getElem_congr`), SM/GeoPathTransport (`geoMarkPoint*`), SM/GeoCornerPolygon (`geoCornerPolygon_edge_smul`,
`geoCornerPolygon_outEdge_eq_inEdge_of_independent`), SM/GeoCarrierCrossings (`geoCarrierCrossings_subset_U`,
`mem_geoCarrierCrossings`), SM/RotationContinuity (`rotationNumber_family_constant`), SM/CuspParameters
(`continuousAt_edgeParameter_of_det`, `edgeParameters_intersection/of_intersection`), SM/TripleVisitExchanges
(`ExactTriangleVisitOrders`), CV/TripleEvents (`IsSimpleRIII.tripleEventData`: `crossing_set_constant`,
`other_orders_persist`), CV/Events (`guardconst`, `eventually_center_iff_radius`), CV/Setup (`Crosses`, `crosses_iff`,
`crosses_of_meet`, `crossParam_eq_edgeParameter`, `Generic.g2`, `rep_lt_or_lt`), CV/Carriers
(`turn_vertex_of_traced`, `turn_visit_of_traced`, `det_visit_twin_ne_zero`, pieces), CV/CarriersLemma
(`owner_eq_of_interlaces_mem_U`, `carrierword_traced`), CV/X1 (`carrierR`, `Omega1`, …), CV/ChamberInvII
(`X1Summand`), CV/PieceCurve (`pieceSupport_geoIndependent`, `pieceCarrier_geoCarrierCrossings`), CV/PieceIntrinsic
(`liftVisitEquiv`, `liftVisit_symm/twin/mem/injective`, `overBit_eq_true_iff_parent`, `visitBetween_iff_key`),
CV/PieceHomflyTransport (`homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`), CV/RecordHomfly (`IsRecordIsoData`,
`recordIsoOfData`, `carriesDoublePoints_iff`, `carriesOverUnder_iff`), CV/Axioms (`gausscode_polynomial`),
CV/Rotation (`rot_eq_rotationNumber`).

## Notes for the assembler / next waves

* The added import `CV.PieceHomflyTransport` (and hence `CV.PieceIntrinsic`) must be kept when the file moves;
  it is in `work/lean` already.
* `EXT_sorted_next_of_no_cyclic_between` duplicates `SEL_sorted_next_of_no_cyclic_between` (declared later in the
  file); when the file is placed as a library module, replace both by `SM.sorted_next_of_no_cyclic_between`
  (SM/GaussNextFromEmptyArc.lean) if that import is added.
* Reusable for U-AV (row 170) and the other transport rows: `EXT_block`/`EXT_corr*` (any pair of supports and any
  identification of marks with a commutation hypothesis), `EXT_homfly_wall` (any two carriers with corresponding
  retained crossings whose visit order and divide signs are carried), `EXT_rotation_wall` (any carrier of a
  triangle-free support with a corresponding carrier across the wall), `EXT_exists_guardRadius`,
  `EXT_piecesOn_prod/sum`, `EXT_exteriorFactor_eq`.
