# PLAN A — thm:C-S3 (the flat law) `C(P_right) − C(P_left) = C(P(0) ∖ j)`

Target: `SM.thm_C_S3 : CS3Data`, statement fixed in `work/drafts/CS3_statement.lean` (copied
verbatim at the end of the skeleton). Source: reference/SM/sm-4-knotlaws.tex:153-229 (statement
153-159, proof 160-229). Skeleton: `work/drafts/cs3/Skeleton_A.lean` (1070 lines) — typechecks
with `cd work/lean && lake env lean ../drafts/cs3/Skeleton_A.lean` (no errors; only
`declaration uses sorry` warnings, **11 sorried declarations**, listed in §3);
`#print axioms SM.thm_C_S3` = `propext, sorryAx, Classical.choice, Quot.sound, SM.lit_homfly`.
`thm_C_S3` is PROVED from the chain; every `sorry` is inside the chain; the selector algebra, the
state-sum reindexing, the carrier bijections, the slot agreement and the reduction to one side
parameter are already CLOSED (≈ 60 declarations proved). Emphasis of this plan (tag A): maximal
reuse of the accepted `FlatCarriers` correspondences and of the C-chamber lane
(`Deform.of_family`, `isPositive_deform_of_family`, `reparam_positiveDiagram_single_shift`,
`recastTuple`, `positiveDiagram_congr`); the new geometry is confined to two general link-layer
lemmas on the flat subdivision of a one-component shadow and one point-avoidance lemma at `μ_j`.

## 0. What the printed proof does, and what replaces the two unproved inputs

Printed route (sm-4:160-229): (1) rewrite `C` through the selectors `W(Q)` — the accepted lem:C-X1
(`SM.C_X1.selector_form`, SM/CX1.lean:269: `cornerStateSum = Σ_{S ∈ Ind} wind(S) ∏ c(Q)`);
(2) `D = P(0) ∖ j` is generic and its crossings, interlacement graph and independent supports are
identified with those of both sides (lem:flat-sides (ii)/(iii): `independent_supports_of`,
SM/FlatCarriers.lean:510); (3) for a fixed support, corresponding carriers have the same retained
crossings, signs and rotations (cor:flat-carriers (ii), fields `same_retained_crossings`,
`same_rotation` of `FlatCarriersData`); (4) "Lemma lc:presentations and Theorem lp:core identify the
`H` polynomials of their actual positive lifts" — **not proved in the library**; replaced by the
accepted lit:homfly clause `homfly_planar` on a `PlanarIsotopic = EqvGen (Reparam ∨ Deform)`
chain (the device of the accepted prop:C-chamber, work/drafts/cchamber/PLAN_FINAL.md): the
positive lift of a side copy is `Deform`-related to the positive diagram of the *centre* corner
polygon (a continuous family of generic one-component shadows through the flat centre — the
accepted `cornerFamily` of SM/FlatCarriers.lean U4), and the positive lift of the deletion copy is
`Reparam`-related to it (a cyclic re-indexing for every carrier not through `μ_j`; the flat
subdivision at `μ_j` for the carrier through `μ_j`); (5) `m_Q` and `|rot Q|` agree so `d_Q` and
`c(Q)` agree; (6) the selector identity `W(Q*_R) − W(Q*_L) = W(Q*_D)` (field `selector_identity`)
and `other_selectors_agree` close the sum term by term; (7) prop:C-chamber makes the side values
independent of the representative (`cornerStateSum_eq_of_mem_labelledChamber` +
`WallGerm.sideTuple_mem_labelledSide`).

Fixed-statement reading. `n + 1 ≥ 4` vertices, the hypotheses of lem:flat-sides; the statement
quantifies over TWO side parameters `tR`, `tL` (and side bits `bR`, `bL`) with
`IsRightSide g j bR tR`, `IsLeftSide g j bL tL`, while cor:flat-carriers is stated at ONE `t`.
Reduction (§I of the skeleton, closed): the turn at `j` is constant along one side
(`generic_family_turn_constant` on the connected `g.SideParameter`), so
`IsLeftSide g j bL tL → IsLeftSide g j bL tR`; and `C` is constant along one side
(`cornerStateSum_side_const`). So the law at `t := tR` suffices (`flat_law_at`, closed).

## 1. The route in detail (dependency order = skeleton order; ✓ = proved in the skeleton)

### A. Link-layer lemmas on one-component shadows (general, new)

| lemma | statement | sketch | status / est. |
|---|---|---|---|
| `Reindexed.trans`, `Reindexed.symm`, `reindexed_recastTuple`, `edgeSegment_recastTuple`, `getElem_congr_lists` | composition / inverse / recast of the accepted `Reindexed` (FlatCarriers:4015) | `subst`, shifts add through `ZMod.natCast_zmod_val` | ✓ |
| `Link.single_generic_shift` | `(single ⟨k,hk,X⟩).Generic → (single ⟨k,hk,shift r X⟩).Generic` | `StrandMap.generic_pullback (shiftStrandMap ⟨k,hk,X⟩ r)` | ✓ |
| `Link.single_generic_of_reindexed`, `Link.homfly_positiveDiagram_single_of_reindexed` | genericity / equal `homfly` along `Reindexed` | `subst`, `reindexed_eq_shift`, `reparam_positiveDiagram_single_shift`, `homfly_planar` | ✓ |
| `Link.deform_positiveDiagram_single_of_family` | `Φ : unitInterval → LabelledTuple k` continuous, every `single (Φ u)` generic ⇒ `Deform (pd (Φ 0)) (pd (Φ 1))` | crossing sets locally constant (`crossing_support_persists_of_geometry`, `crossingGeometry_of_single_generic`), `Deform.of_family`, `isPositive_deform_of_family`, `eq_positiveDiagram_of_isPositive` | ✓ |
| `Link.homfly_positiveDiagram_single_of_family` | `homfly (pd (Φ 0)) = homfly (pd (Φ 1))` | `homfly_planar`, `PlanarIsotopic.of_deform` | ✓ |
| `Link.single_generic_appendVertex` | `single X` generic, `0<u<1`, the new point `edgePoint X (-1) u` on no other closed edge (`hnew : ∀ e ≠ -1, … ∉ edgeSegment X e`) ⇒ `single (appendVertex X u)` generic | `Shadow.single_generic_of` (LinkPositiveLift:160) with: `regular_appendVertex`; `tail_off`: an old vertex on a half-edge lies on the old closing edge (`appendVertex_old/new`, `edge_appendVertex_last/new`: half-edge segments ⊆ old segment), excluded by `hX.tail_off` unless incident; the new vertex on an old edge is excluded by `hnew`; `transverse`: half-edge directions are positive multiples of the old direction, a meeting of two non-adjacent new edges is a meeting of two non-adjacent old edges except for a half-edge against an edge adjacent to the old closing edge, excluded because adjacent regular edges meet only at the shared vertex; `no_triple`: interiors of the half-edges lie in the old interior and are disjoint | **sorry**, 160 |
| `Link.reparam_positiveDiagram_single_appendVertex` | `Reparam (pd (single X)) (pd (single (appendVertex X u)))` | `ReparamData` with `e = Equiv.refl (Fin 1)`; `φ : TraversalPoint m ≃ TraversalPoint (m+1)`: `(i, s) ↦ (insertIndex i, s)` for `i ≠ -1`, `(-1, s) ↦ (insertIndex (-1), s/u)` if `s < u`, else `(insertedIndex m, (s-u)/(1-u))`; `between`: `traversalKey` strictly increasing under `φ` (piecewise affine); `eval_eq`: `appendVertex_old`, `edge_appendVertex_last` (`u • edge`) / `edge_appendVertex_new` (`(1-u) • edge`); `over_map`/`over_surj`: a crossing `{a, b}` of `single X` corresponds to the crossing of `appendVertex X u` in which `-1` is replaced by the half-edge containing the crossing point (its parameter by `crossingParam_spec` + `edgePoint_injective` on a nonzero edge); over strands agree since both diagrams are positive (`Shadow.positiveDiagram_isPositive`) and the half-edge direction is a positive multiple of the old one — the pattern of `shiftReparamData`/`shiftPullback_overVisit_snd` (CChamber:762-846) | **sorry**, 250 |
| `Link.homfly_positiveDiagram_single_appendVertex` | equal `homfly` | `homfly_planar`, `PlanarIsotopic.of_reparam` | ✓ |
| `exists_appendVertex_of_erase_flat` | list form: `∃ Q u, 0<u<1 ∧ Reindexed (markPolygon f' L') Q ∧ Reindexed (appendVertex Q u) (markPolygon f L) ∧ edgePoint Q (-1) u = f x` under the hypotheses of `rotationNumber_erase_flat` | the structure of the accepted `rotationNumber_erase_flat` (FlatCarriers:4164), verbatim: rotate `L` to `M ++ [x]` (`M = L₂ ++ L₁`); its `h1 h2 h3 h4` give `Reindexed (markPolygon f' L') (markPolygon f M)` (with `Reindexed.trans/symm`), its `h5 h6` give `Reindexed (appendVertex (markPolygon f M) (1/(1+s))) (markPolygon f L)`, its `hx'` is the last clause; `Q := recastTuple hlenL' (markPolygon f M)` (`reindexed_recastTuple`) | **sorry**, 110 |

### B. On a generic polygon the geo data are the accepted data — all ✓

`geoCornerCount_eq_generic`, `geoCornerPolygon_eq_generic` (recast along
`geoComponentCornerList_eq_generic`, `geoMarkPosition_eq_generic`, `zmod_val_cast`),
`geoCornerCount_ge_three_generic`, `carrierShadow_eq_single_geo` (`polyComp_recastTuple`),
`single_geo_generic`, `positiveLift_eq_geo`, `cornerSelector_recastTuple`,
`carrierWeight_eq_cornerSelector` (`unfold; split_ifs <;> rfl`), `carrierWeight_eq_geoCarrierSelector`,
`wind_eq_prod_geoCarrierSelector`, `carrierCrossings_eq_geo`, `carrierCrossingCount_eq_geo`,
`carrierRotation_eq_geo`, `cornerCoefficient_eq_geo` (`c(Q)` as `coeffAt (1 − #retained − |round rot|) 0
(homfly (pd (single geoCornerPolygon)))`).

### C. The carrier bijections at one `t` — all ✓

`sideCarrierEquiv hF b : GeoComponent C S ≃ GeoComponent (T b) (S_T b)` (`Quotient.congr
(markTransport (hs b))`, `(hF.correspond_sides b).2`), `_owner`/`_central` (`rfl`);
`deletionCarrierEquiv hF : GeoComponent D S_D ≃ GeoComponent C S` (`Equiv.ofBijective` of
`Quotient.lift (geoOwner C S ∘ fusionMark)`, `hF.correspond_deletion.2`), `_owner` (`rfl`),
`deletionCarrierEquiv_deletionCopy` / `_symm_central` (`fusionMark_delMark`,
`central_vs_deletion_through_mu_j.1`, `geoOwner_successor`); slots:
`card_geoCarrierCrossings_side/deletion` (`same_retained_crossings` as `Finset.map` +
`Finset.card_map`), `rotationNumber_side/deletion` (`same_rotation`). Deletion-side lemmas are
indexed by the CENTRE carrier `q` through `(deletionCarrierEquiv hF).symm q`.

### D. The centre corner polygons

| lemma | sketch | status / est. |
|---|---|---|
| `geoCornerCount_side`, `geoCornerCount_ge_three_centre` | `geoCornerCount_markTransport` with `identify_sides_marks_of`; side count ≥ 3 | ✓ |
| `reindexed_deletion_other` | `Reindexed (geoCornerPolygon D (e_D.symm q)) (geoCornerPolygon C q)` for `q ≠ q*`: the three steps of `rotationNumber_others_unchanged` composed with `Reindexed.trans` | ✓ |
| `exists_appendVertex_central` | `∃ Q u, 0<u<1 ∧ Reindexed (geoCornerPolygon D q*_D) Q ∧ Reindexed (appendVertex Q u) (geoCornerPolygon C q*) ∧ edgePoint Q (-1) u = μ_j` | `exists_appendVertex_of_erase_flat` applied exactly as `rotationNumber_erase_flat` is applied in `rotationNumber_deletionCopyThroughJ` (FlatCarriers:4324): `f` = centre mark point, `L` = centre corner list of `q*`, `x = Sum.inl j`, `hflat` from `flat_of_turn_eq_zero` (regularity from `hF.nonzero_segments.2.1`, `hF.no_antiparallel.1`; zero turn from `hF.turns_nonzero.1`), `g = delMark`, `f'` = deletion mark point, `hf' = deletion_mark_point`, `hL' = Cycle.coe_eq_coe.mp hF.central_vs_deletion_through_mu_j.2.2.1`; `L'.length` is `geoCornerCount D q*_D` by `rfl`; `f x = g.center j` by `geoMarkPosition_evaluation_vertex` | **sorry**, 40 |
| `mu_j_unique_edge` | `μ_j` on two closed edges `e, e'` of `geoCornerPolygon D q*_D` ⇒ `e = e'` | rewrite through `geoCornerPolygon_eq_generic` + `edgeSegment_recastTuple` to the accepted `ccpCornerPolygon` of the deletion carrier; `¬ adjacent`: `nonadjacent_meet_crossing` (LinkPositiveLift:520) makes `μ_j` a deletion crossing point, `crossingPoint_fusion` (FusionCrossings:42) a centre crossing point, contradicting `(flat_germ_spatial_data (by omega) g hz hb hc g.zeroParameter).2.2`; adjacent: `consecutive_meet` (LinkPositiveLift:698) makes `μ_j` a deletion corner point, i.e. the point of `delMark a` with `a ≠ Sum.inl j` a centre corner (from `hF.central_vs_deletion_through_mu_j.2.2.1` via `Cycle.coe_eq_coe`, `List.mem_map`, `List.mem_erase_of_ne`), equal to the centre point of `a` (`deletion_mark_point`): a vertex `g.center k`, `k ≠ j` (contradiction with `(flat_center_geometry (by omega) hz hb).1`) or a crossing point (spatial data again) | **sorry**, 90 |
| `centre_shadow_generic` | `(single ⟨geoCornerCount C q, _, geoCornerPolygon C q⟩).Generic` | `by_cases q = q*`: (≠) `single_generic_of_reindexed (reindexed_deletion_other …)` from `single_geo_generic` on `D` (`hS_D` from `independent_supports_of`); (=) `exists_appendVertex_central`; `single Q` generic by `single_generic_of_reindexed`; `single (appendVertex Q u)` generic by `single_generic_appendVertex` with `hnew` from `mu_j_unique_edge` transported along the re-indexing (`reindexed_eq_shift`, `edgeSegment_shift`, `edgePoint Q (-1) u = μ_j ∈ edgeSegment Q (-1)`); then `single_generic_of_reindexed` again | **sorry**, 70 |
| `homfly_deletion_eq_centre` | `homfly (pd (single (geoCornerPolygon D (e_D.symm q)))) = homfly (pd (single (geoCornerPolygon C q)))` (the LHS is the deletion positive lift by `positiveLift_eq_geo`, exactly as `cornerCoefficient_eq_geo` reads it) | (≠ q*) `homfly_positiveDiagram_single_of_reindexed (reindexed_deletion_other …)`; (= q*) `deletionCarrierEquiv_symm_central`, `exists_appendVertex_central`, `homfly_positiveDiagram_single_of_reindexed` around `homfly_positiveDiagram_single_appendVertex` (genericity of `appendVertex Q u` from `centre_shadow_generic` through `single_generic_of_reindexed … .symm`) | **sorry**, 60 |

### E. The deformation through the flat centre

| lemma | sketch | status / est. |
|---|---|---|
| `FlatFamilyData δ`, `exists_flatFamilyData` | `0<δ≤radius`; for `|s|<δ`: `CrossingGeometry (g.curve s)` and the centre's supports (`FlatSidesData` last conjunct, `GeometricRecordsAgree`'s `hs`); `SideRecordData` at every `t<δ` (`flat_side_records`) | ✓ |
| `continuousAt_markPointOn_of` | `ContinuousAt (markPointOn g · a) s₀` on the record domain with the centre's supports (the accepted proof at `s₀`) | ✓ |
| `sideParamPath`, `_zero`, `_one`, `continuous_`, `abs_sideParamPath_lt`, `sideParamPath_eq_sideTime` | the affine path `u ↦ u·(±t)`; `= sideTime b ⟨u·t, _⟩` for `u > 0` | ✓ |
| `geoCornerPolygon_side_eq_cornerFamily` | side corner polygon of `geoOwner T (markTransport a)` = `recastTuple` of `cornerFamily S (geoOwner C a) (sideTime b t)` | `funext k`; the side corner list is literally `(centre corner list).map (markTransport (hs b))` (`geoComponentCornerList_markTransport` with `identify_sides_marks_of`); `getElem_congr_lists`, `List.getElem_map`, `zmod_val_cast`; points by `markPointOn_side` (FlatCarriers:4460) | **sorry**, 30 |
| `cornerFamily_side_generic` | `single (cornerFamily … (sideTime b t))` generic | choose `a` with `geoOwner C S a = q`; `hs := flat_common_supports … hsd`; rewrite by the previous lemma (`recastTuple` both ways, `polyComp_recastTuple`, `PolyComp` proofs irrelevant); `single_geo_generic` on the side with `hS_T` from `independent_supports_of` | **sorry**, 30 |
| `geoDiagram_side_eq_cornerFamily` | `pd (single (geoCornerPolygon T (e_b q))) = pd (single (cornerFamily (sideTime b t)))` | `positiveDiagram_congr` along `geoCornerPolygon_side_eq_cornerFamily` + `polyComp_recastTuple` | **sorry**, 20 |
| `homfly_side_eq_centre` | `homfly (pd (single (geoCornerPolygon T (e_b q)))) = homfly (pd (single (geoCornerPolygon C q)))` | `Φ u := cornerFamily S q (sideParamPath b t u)`; `Continuous Φ` from `continuous_iff_continuousAt`, `continuousAt_pi`, `continuousAt_markPointOn_of` at `sideParamPath u` (inside the family radius by `abs_sideParamPath_lt`) composed with `continuous_sideParamPath`; `hgen u`: `u = 0` → `centre_shadow_generic` (`sideParamPath_zero`, `cornerFamily_zero`); `u > 0` → `sideParamPath_eq_sideTime`, `cornerFamily_side_generic` at the side parameter `u·t < δ` (its `SideRecordData` from `hδ.2.2.2`); then `homfly_positiveDiagram_single_of_family` and the two endpoint identifications (`cornerFamily_zero`, `geoDiagram_side_eq_cornerFamily`, `positiveDiagram_congr`) | **sorry**, 90 |

### F. Corresponding coefficients agree — all ✓

`cornerCoefficient_side_eq_deletion`: `cornerCoefficient_eq_geo` twice, then `rw` with
`card_geoCarrierCrossings_side/deletion`, `rotationNumber_side/deletion`, `homfly_side_eq_centre`,
`homfly_deletion_eq_centre` (the `flatSideCG`/`generic_crossingGeometry` proof terms are matched by
`rw` through proof irrelevance — verified). `cornerProduct_side_eq_deletion`: `Fintype.prod_equiv`
along `geoEq_D.symm ≫ deletionCarrierEquiv ≫ sideCarrierEquiv ≫ geoEq_T`.

### G. The selector algebra — all ✓

`wind_side_eq_prod`, `wind_deletion_eq_prod`, `selector_other` (`hF.other_selectors_agree` read on
centre carriers), `selector_central` (`hF.selector_identity`, `sideCarrierEquiv_central`,
`deletionCarrierEquiv_symm_central`), `wind_law` (`Fintype.prod_eq_mul_prod_compl q*` thrice,
`Finset.prod_congr` on `{q*}ᶜ`, `← sub_mul`).

### H. The state sums — all ✓

`stateTerm`, `stateTerm_of_not/of_decomposition`, `cornerStateSum_eq_sum_stateTerm`
(`C_X1.selector_form`, `Finset.sum_attach`, `Finset.sum_subset`), `finsetMapEquiv`,
`sum_finsetMapEquiv` (`Equiv.finsetCongr` does NOT exist in this Mathlib), `stateTerm_law`
(`independent_supports_of` for the vanishing off `GeoIndependent`; `cornerProduct_side_eq_deletion`
twice, `← sub_mul`, `wind_law`), `flat_law_at` (three reindexings along `crossingTransport (hs bR)`,
`crossingTransport (hs bL)`, `fusionCrossingEquiv`; `Finset.sum_sub_distrib`).

### I. Reduction and the theorem — all ✓

`cornerStateSum_side_const`, `side_turn_const`, `isLeftSide_of_side`, `thm_C_S3` (radius
`min δC δF`, `δC ≤ g.radius` from `flat_carriers`).

## 2. Reuse list (names and line numbers verified in work/lean)

- SM/CX1.lean: `carrierWeight` (:24), `wind` (:31), `C_X1` (:269, field `selector_form`).
- SM/CornerStateSum.lean: `cornerStateSum` (:166), `cornerProduct` (:158), `cornerCoefficient`
  (:110), `cornerCoefficient_eq_coeffAt` (:114), `cornerSlot` (:82), `carrierRotationInt` (:61),
  `cornerHomfly` (:96).
- SM/FlatCarriersDefs.lean: `GeoComponent` (:258), `geoOwner` (:262), `geoOwner_eq_iff` (:266),
  `geoOwner_successor` (:270), `geoOwner_surjective` (:278), `geoComponentCornerList` (:367),
  `geoCornerCount` (:387), `geoCornerPolygon` (:402), `geoCarrierCrossings` (:451),
  `GeoIndependent` (:457), `cornerSelector` (:466), `geoCarrierSelector` (:471), `flat_hn1` (:488),
  `flatCentreCG` (:494), `flatDeletionCG` (:502), `flatSideCG` (:511), `CommonSupports` (:519),
  `IsRightSide`/`IsLeftSide` (:525/:529), `markTransport` (:536), `transportSupport` (:541),
  `deletionSupport` (:547), `fusionMark` (:557), `delMark` (:566), `delMark_fusionMark` (:573),
  `fusionMark_delMark` (:582), `centralCarrierThroughJ` (:604), `deletionCopyThroughJ` (:614),
  `geoMarkPosition_eq_generic` (:101), `geoComponentEquivGeneric` (:676),
  `geoComponentEquivGeneric_owner` (:683), `geoComponentCornerList_eq_generic` (:713),
  `FlatCarriersDefinitionData` (:809), `FlatCarriersData` (:969) with fields `correspond_sides`,
  `correspond_deletion`, `central_vs_deletion_through_mu_j`, `others_unchanged`,
  `nonzero_segments`, `no_antiparallel`, `turns_nonzero`, `same_retained_crossings`,
  `same_rotation`, `selector_identity`, `other_selectors_agree`.
- SM/FlatCarriers.lean: `WallGerm.sideTime_val_abs` (:72), `SideRecordData` (:83),
  `flat_side_records` (:93), `flat_common_supports` (:108), `geoIndependent_iff_isDecomposition`
  (:164), `identify_sides_marks_of` (:480), `independent_supports_of` (:510),
  `geoComponentCornerList_markTransport` (:1631), `geoCornerCount_markTransport` (:1646),
  `Reindexed` (:4015), `reindexed_refl` (:4018), `reindexed_eq_shift` (:4022),
  `reindexed_of_cast` (:4043), `markPolygon` (:4050), `geoCornerPolygon_eq_markPolygon` (:4070),
  `reindexed_markPolygon_of_isRotated` (:4091), `reindexed_markPolygon_map` (:4098),
  `markPolygon_congr` (:4108), `reindexed_appendVertex_markPolygon` (:4127),
  `rotationNumber_erase_flat` (:4164, structure to copy), `deletion_mark_point` (:4285),
  `fusion_mark_point` (:4303), `flat_of_turn_eq_zero` (:4312),
  `rotationNumber_deletionCopyThroughJ` (:4324, application pattern), `markPointOn` (:4435),
  `visit_point_eq_edgePoint` (:4443), `markPointOn_zero` (:4452), `markPointOn_side` (:4460),
  `continuousAt_markPointOn` (:4486), `cornerFamily` (:4505), `cornerFamily_zero` (:4511),
  `cornerFamily_eq_markPolygon` (:4518), `geoCarrierSelector_eq_cornerSelector` (:4878),
  `exists_sideParameter_lt` (:5527), `flat_carriers` (:5617).
- SM/FlatSides.lean: `FlatSidesData` (:17), `flat_sides` (:47).
- SM/FlatSpatial.lean: `flat_germ_spatial_data` (:23) (no vertex is a crossing point);
  SM/FlatCenter.lean: `flat_center_geometry` (:30) (injectivity of the centre vertices);
  SM/FusionCrossings.lean: `crossingPoint_fusion` (:42).
- SM/CChamber.lean: `recastTuple` (:76), `zmod_val_cast` (:82), `rotationNumber_recastTuple`
  (:91), `polyComp_recastTuple` (:108), `positiveDiagram_congr` (:567),
  `single_isCrossing_iff_of_forall` (:573), `crossingGeometry_of_single_generic` (:582),
  `Deform.of_family` (:601), `Diagram.isPositive_deform_of_family` (:625),
  `positiveDiagram_single_recast` (:666), `shiftStrandMap` (:685), `shiftReparamData` (:819),
  `reparam_positiveDiagram_single_shift` (:846), `generic_family_turn_constant` (:940),
  `isCrossing_transportedCornerPolygon_path` (:1110, pattern), `deform_positiveLift_path` (:1152,
  pattern), `cornerStateSum_eq_of_mem_labelledChamber` (:1366).
- SM/LinkDiagram.lean: `Shadow.Generic` (:394), `StrandMap.generic_pullback` (:856),
  `Shadow.single` (:1589), `single_generic_of_generic` (:1715); SM/LinkPositiveLift.lean:
  `Shadow.positiveDiagram` (:93), `eq_positiveDiagram_of_isPositive` (:128), `single_generic_of`
  (:160), `carrierShadow` (:218), `carrierShadow_generic` (:580), `positiveLift` (:596),
  `edgeSegment_param` (:353), `nonadjacent_meet_crossing` (:520), `consecutive_meet` (:698).
- SM/LinkMoves.lean: `ReparamData` (:370), `Reparam` (:387), `Deform` (:478), `PlanarIsotopic`
  (:516), `.of_reparam/.of_deform` (:519/:522); SM/LinkInterfaces.lean: `homfly_planar` (:382).
- SM/GermSides.lean: `sideParameter_connectedSpace` (:12), `WallGerm.sideTuple_mem_labelledSide`
  (:29), `labelledSide_eq_at` (:39); SM/WallGerm.lean: `zeroParameter` (:28), `sideTime` (:34),
  `sideTuple` (:49), `continuous_sideTuple` (:52).
- SM/InsertedTuple.lean: `appendVertex` (:11), `appendVertex_old/new` (:14/:18),
  `edge_appendVertex_old/last/new` (:30/:35/:40); SM/AppendRotation.lean: `regular_appendVertex`
  (:26); SM/RegularLocus.lean: `regular_shift` (:61).
- SM/GeometricParameters.lean: `continuousAt_edgeParameter_of_geometry` (:58);
  SM/GeometricCrossingStability.lean: `crossing_support_persists_of_geometry` (:35);
  SM/DecompositionDefinition.lean: `IsDecomposition` (:15, definitionally membership in
  `independentSupports`).
- Mathlib: `Fintype.prod_eq_mul_prod_compl`, `Fintype.prod_equiv`, `Fintype.sum_equiv`,
  `Quotient.congr`, `Quotient.lift`, `Equiv.ofBijective`, `Cycle.coe_eq_coe`,
  `IsLocallyConstant.iff_eventually_eq`, `IsLocallyConstant.apply_eq_of_preconnectedSpace`,
  `Finset.sum_sub_distrib`, `Finset.sum_subset`, `Finset.sum_attach`, `Finset.mem_map_equiv`.

## 3. Estimated lines

Skeleton as delivered: 1070 lines, ≈ 60 declarations proved, **11 sorried**:

| sorried lemma | est. lines |
|---|---|
| `Link.single_generic_appendVertex` | 160 |
| `Link.reparam_positiveDiagram_single_appendVertex` | 250 |
| `exists_appendVertex_of_erase_flat` | 110 |
| `exists_appendVertex_central` | 40 |
| `mu_j_unique_edge` | 90 |
| `centre_shadow_generic` | 70 |
| `homfly_deletion_eq_centre` | 60 |
| `geoCornerPolygon_side_eq_cornerFamily` | 30 |
| `cornerFamily_side_generic` | 30 |
| `geoDiagram_side_eq_cornerFamily` | 20 |
| `homfly_side_eq_centre` | 90 |

Remaining proof text ≈ **950 lines**; finished module ≈ **2000 lines** in total (a quarter of it is
the two general link-layer lemmas on the flat subdivision, reusable by later rows).

## 4. The three riskiest steps, with fallbacks

1. **The Deform across the flat centre — is the centre corner polygon a generic shadow with the
   same crossing pairs as the side copies?** Regularity at the centre is accepted
   (`nonzero_segments`, `no_antiparallel`; zero turns are allowed by `Regular`), but `tail_off`,
   `transverse`, `no_triple` of `Shadow.Generic` are NOT accepted at the nongeneric centre, and
   `Deform.of_family` needs genericity at every time. The plan avoids re-doing lem:carriers (iii)
   at the centre: the centre corner polygon of every carrier not through `μ_j` is a re-indexing of
   its deletion copy's (accepted cycle identity `others_unchanged.2`; `reindexed_deletion_other`
   is PROVED), hence generic (`single_generic_of_reindexed`, proved); the carrier through `μ_j` is
   the flat subdivision of its deletion copy (`exists_appendVertex_central`, the structure of the
   accepted `rotationNumber_erase_flat`), hence generic by the ONE new geometric lemma
   `single_generic_appendVertex` once `μ_j` is on no other edge of the deletion carrier
   (`mu_j_unique_edge`, from the accepted `nonadjacent_meet_crossing`/`consecutive_meet` of
   LinkPositiveLift and the flat-centre spatial data). The constancy of the crossing pairs along
   the family is then automatic (`deform_positiveDiagram_single_of_family`, PROVED: locally
   constant by `crossing_support_persists_of_geometry` on the connected interval), and it shows as
   a by-product that the centre corner polygon has the same crossing pairs as both side copies.
   *Fallback:* prove `Shadow.Generic` of the centre corner polygon directly from the flat-centre
   ambient geometry by porting `ccpCornerPolygon_tail_off/_transverse/_no_triple`
   (LinkPositiveLift:251-580) to `CrossingGeometry` with U3's `geo_corner_chain`/
   `geoCornerPolygon_edge_data` (FlatCarriers:3185-3300) as the block parametrization (~400
   lines, uniform over carriers).

2. **The Reparam for the flat subdivision** (`reparam_positiveDiagram_single_appendVertex`): a
   hand-built `ReparamData` with a piecewise-affine circle bijection and the crossing
   correspondence `over_map`/`over_surj` (~250 lines; the accepted `shiftReparamData` is the
   template, but its strand map was a bijection of strands, which a subdivision is not — the two
   half-edges both map to the old closing edge, so `StrandMap`/`pullback` cannot be used and the
   over-visit bookkeeping (`visitPt`, `crossingParam_spec`) has to be done by hand).
   *Fallback (a):* build a general `ReparamData.ofSingleMonotone` for one-component positive
   diagrams from a `TraversalPoint` bijection preserving `traversalBetween` and `eval`, deriving
   `over_map`/`over_surj` from positivity + `crossingPoint` matching (same content, reusable).
   *Fallback (b):* if a subdivision Reparam exists in the library under another name (grep
   `subdiv`, `insertVertex`, `ReparamData` in LinkMoves/LinkRecord*/Smoothing), use it.
   *Fallback (c):* replace the deletion↔centre step by a side-level construction (subdivide the
   side copy's deletion carrier at a point of the fused block and `Deform`) — this isolates the
   Reparam from the flat centre but does not remove it.

3. **Dependent-type bookkeeping across the four configurations.** Corner polygons live in
   `LabelledTuple (geoCornerCount hP S q)` with four different `hP`; `Component` vs
   `GeoComponent`; `PolyComp`/`Generic` proof arguments inside `Shadow.single`/`positiveDiagram`.
   Resolved in the skeleton by: the accepted `geoComponentEquivGeneric` (the types
   `GeoComponent (flatSideCG …)` and `GeoComponent (generic_crossingGeometry …)` coincide by proof
   irrelevance — verified, and `rw` matches such terms), `recastTuple` + `polyComp_recastTuple` +
   `positiveDiagram_congr` (every identification is an equality of `LabelledTuple`s up to recast,
   never a `HEq`), `Reindexed` (with the new `trans`/`symm`) for rotations, the equivs
   `sideCarrierEquiv`/`deletionCarrierEquiv` whose `_owner` lemmas are `rfl`, and indexing every
   deletion-side statement by the centre carrier `q` through `(deletionCarrierEquiv hF).symm q`.
   The consumer-facing shape is fixed by `cornerCoefficient_eq_geo` (PROVED): `c(Q)` on the geo
   data of the carrier, so `homfly_side_eq_centre`/`homfly_deletion_eq_centre` are stated on the
   geo positive diagram (`Shadow.single ⟨geoCornerCount, _, geoCornerPolygon⟩`), and
   `cornerCoefficient_side_eq_deletion` is already closed by `rw`. What remains here is the
   `recastTuple` identity `geoCornerPolygon_side_eq_cornerFamily` (`funext k`, `getElem_congr_lists`,
   `zmod_val_cast`). *Fallback:* if a recast identity resists, restate it as `Reindexed` (r = 0)
   and use `homfly_positiveDiagram_single_of_reindexed`/`single_generic_of_reindexed`, which
   absorb any rotation.

Secondary: `exists_flatFamilyData` reads the exact shape of `FlatSidesData`'s last conjunct
(FlatSides.lean:17-36) — PROVED. `cornerStateSum_eq_sum_stateTerm` relies on
`IsDecomposition hn hP S` being definitionally `S ∈ independentSupports hn hP` — PROVED.
