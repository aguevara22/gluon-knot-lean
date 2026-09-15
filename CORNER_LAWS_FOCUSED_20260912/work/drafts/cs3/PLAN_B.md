# PLAN_B — thm:C-S3 (the flat law), route B: one transport lemma, three instantiations

Written 2026-09-13/14 by a Claude Code proof-architect subagent (tag B). Target: `SM.thm_C_S3 :
CS3Data`, the FIXED statement of `work/drafts/CS3_statement.lean` (reference/SM/sm-4-knotlaws.tex:153-229,
frame SM15). Companion: `work/drafts/cs3/Skeleton_B.lean` (1082 lines, 75 declarations), checked with
`cd work/lean && lake env lean ../drafts/cs3/Skeleton_B.lean`: **no errors; 11 declarations use `sorry`**
(all inside the chain; `thm_C_S3` itself is proved from the chain). Everything not listed in §7 is already
proved in the skeleton, so the dependent-type bookkeeping (carrier correspondences as `Equiv`s onto the
accepted `Carrier.Component`s, the reindexing of the three sums, the three instantiations of the transport
lemma, the assembly with prop:C-chamber) is machine-checked.

## 0. Summary of the route

Printed proof (sm-4:161-229), clause by clause, and its Lean rendering:

| printed step | Lean |
|---|---|
| "rewrite the state sum using only the corner signs", eq. ccf:selector-sum | accepted lem:C-X1 `C_X1.selector_form` (SM/CX1.lean:269): `C(P) = Σ_{S ∈ Ind} wind(S) · ∏ c(L)` |
| "lem:flat-sides identifies the three interlacement graphs and all independent supports" | `FlatCarriersDefinitionData.independent_supports` (SM/FlatCarriersDefs.lean:809 ff.): `GeoIndependent C S ↔ IsDecomposition side (transportSupport (hs b) S)` and `↔ IsDecomposition del (deletionSupport S)`; the three sums are reindexed over `centreSupports := univ.filter (GeoIndependent C)` (§4, F7) |
| "cor:flat-carriers gives corresponding oriented carriers with the same retained crossing records and signed rotations" | `FlatCarriersData.correspond_sides/.correspond_deletion` give the carrier bijections `sideEquiv b`, `delEquiv : GeoComponent C S ≃ Component …` (§1b, F1); `same_retained_crossings` → equal `m_Q` (F3), `same_rotation` → equal `r_Q` (F4) |
| "lc:presentations and lp:core identify the H polynomials of their positive lifts" (NOT proved) | replaced by lit:homfly `homfly_planar` along a `PlanarIsotopic`: side lift → (re-indexing) → corner family `u ↦ P(±u·t)` (a `Deform`, L0.6) → centre corner polygon → (`Q ≠ Q_*`: re-indexing; `Q_*`: subdivision `Reparam` L0.8 + shift) → deletion lift (§3c, F6) |
| "the numbers m_Q and \|rot(Q)\| agree, so each corresponding coefficient c(Q) is the same" | the abstract transport lemma T2 `cornerProduct_eq_of_carrier_data`: `∏ c = ∏ refCoefficient (m_Q, r_Q, H⁺_Q)` with reference data read at the centre / on the deletion copy, instantiated for right, left, deletion (I1 `cornerProduct_side_eq_del`) |
| "exactly one carrier Q_* passes through μ_j; all other selectors agree; W(Q_*^R) − W(Q_*^L) = W(Q_*^D)" | T3 `wind_eq_of_weights` (`wind = wt(Q_*) · U`) three times with `other_selectors_agree` (F5.1) and `selector_identity` (F5.2); I2 `wind_side_sub_side_eq_del` |
| eq. ccf:term-difference, sum over the common supports | `flat_law_at`: `Σ_S (wind_R − wind_L) · B_S = Σ_S wind_D · B_S` (`Finset.sum_sub_distrib`, `sub_mul`) |
| "prop:C-chamber supplies the well-defined side values" | the statement has two side parameters `tR`, `tL`; `cornerStateSum_sideTuple_eq` (chamber constancy along one side) and `turn_sideTuple_eq` bring the left side to `t = tR` (§4b, F11); assembly `thm_C_S3` |

Tag-B emphasis realised: §2 states the transport of the def:C data ONCE for an abstract carrier bijection
`e : ι ≃ Component hm hP S'` with the reference data `(m_Q, r_Q, H⁺_Q)` and `w_Q` as functions on `ι`
(`cornerCoefficient_eq_ref`, `cornerProduct_eq_of_carrier_data`, `wind_eq_of_weights`), and §3d
instantiates it with `ι = GeoComponent (flatCentreCG …) S` for the right side, the left side and the
deletion; the selector algebra is the standalone `flat_term_identity` / the `sub_mul` step of I2.

## 1. Notation (all accepted, SM/FlatCarriersDefs.lean unless said)

`n ≥ 3`, parent size `n+1`; `g : WallGerm (n+1)`, flat vertex `j`, `hz hb hc hsc` the hypotheses of
lem:flat-sides. `C = g.center` with `flatCentreCG` (l.494), `D = deleteVertex g.center j` with
`flatDeletionCG` (l.502) and `generic_deleteVertex` (SM/DeletionGeneric.lean:32), side `T_b(t) =
(g.sideTuple b t).val` with `flatSideCG` (l.511); `hs : CommonSupports g t` (l.519); supports
`S_T = transportSupport (hs b) S` (l.541), `S_D = deletionSupport S` (l.547); marks `markTransport`
(l.536), `fusionMark`/`delMark` (l.557/566); `Q_* = centralCarrierThroughJ` (l.604),
`deletionCopyThroughJ` (l.614); geo carriers `GeoComponent`/`geoOwner` (l.258/262), corner data
`geoCornerCount/geoCornerMark/geoCornerPolygon` (l.387-402), `geoCarrierCrossings` (l.451),
`cornerSelector`/`geoCarrierSelector` (l.466/471); generic bridge `geoComponentEquivGeneric` (l.676),
`geoComponentEquivGeneric_owner` (l.683, rfl), `geoComponentCornerList_eq_generic` (l.713),
`geoMarkPosition_eq_generic` (l.101). Bundles `FlatCarriersDefinitionData` (l.809),
`FlatCarriersData` (l.969); row theorems `flat_carriers_definition` (SM/FlatCarriers.lean:5596),
`flat_carriers` (l.5617): `∃ δ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t < δ, ∃ hs, ∀ S, GeoIndependent C S → Data`.
Note `CrossingGeometry P` is a Prop, so `GeoComponent (flatSideCG …) S_T` and
`GeoComponent (generic_crossingGeometry …) S_T` are the same type by proof irrelevance — used
throughout; the geo↔accepted bridge lemmas are therefore stated for an arbitrary `hP' : CrossingGeometry P`.

## 2. The chain, lemma by lemma (names as in Skeleton_B.lean; ✔ = proved there, ◻ = `sorry`)

### §0 Diagram layer (`namespace SM.Link`)

| # | lemma | statement (abridged) | sketch | est. |
|---|---|---|---|---|
| L0.1 ✔ | `single_generic_shift` | `(single ⟨k,hk,Q⟩).Generic → (single ⟨k,hk,shift r Q⟩).Generic` | `(shiftStrandMap ⟨k,hk,Q⟩ r).generic_pullback hΓ (regular_shift)` | 4 |
| L0.2 ✔ | `planarIsotopic_positiveDiagram_single_shift` | `PlanarIsotopic (positiveDiagram (single Q)) (positiveDiagram (single (shift r Q)))` | `PlanarIsotopic.of_reparam (reparam_positiveDiagram_single_shift …)` | 3 |
| L0.3 ✔ | `single_generic_of_reindexed` | `Reindexed Q Q' → (single Q).Generic → (single Q').Generic` | `subst` the size equality, `reindexed_eq_shift`, L0.1 | 6 |
| L0.4 ✔ | `planarIsotopic_positiveDiagram_single_of_reindexed` | `Reindexed Q Q' → PlanarIsotopic …` | as L0.3 with L0.2 | 6 |
| L0.5 ✔ | `isCrossing_single_family_constant` | `Φ : unitInterval → LabelledTuple k` continuous, all `single (Φ s)` generic ⇒ `IsCrossing (Φ s) x ↔ IsCrossing (Φ 0) x` | `IsLocallyConstant` via `crossing_support_persists_of_geometry ∘ crossingGeometry_of_single_generic`, `apply_eq_of_preconnectedSpace` (copy of `isCrossing_transportedCornerPolygon_path`) | 10 |
| L0.6 ✔ | `planarIsotopic_positiveDiagram_single_family` | same hypotheses ⇒ `PlanarIsotopic (positiveDiagram (single (Φ 0))) (positiveDiagram (single (Φ 1)))` | `Deform.of_family` with `V u _ := Φ u`; positivity `Diagram.isPositive_deform_of_family`; endpoint `Shadow.eq_positiveDiagram_of_isPositive` (copy of `deform_positiveLift_path`) | 20 |
| L0.7a ◻ | `regular_adjacent_meet` | `Regular Q → x ∈ E_i → x ∈ E_{i+1} → x = Q (i+1)` | `det ≠ 0`: `intersection_parameters_unique` (as `Link.consecutive_meet`); collinear positive: `edge Q (i+1) = s • edge Q i`, parameters force `s' = 1, u = 0` | 40 |
| L0.7 ◻ | `single_generic_appendVertex` | `0<t₀<1`, `(single Q).Generic`, `p := edgePoint Q (-1) t₀ ∉ edgeSegment Q i` for `i ≠ -1` ⇒ `(single ⟨k+1, _, appendVertex Q t₀⟩).Generic` | `Shadow.single_generic_of` (label form). Labels by `insertion_indices_exhaust`: `insertIndex i` (`i ≠ -1`) keeps `edge`/`edgeSegment` (`edge_appendVertex_old`), `insertIndex (-1)` = `[Q_{k-1}, p]` (dir `t₀ • E_{-1}`, `edge_appendVertex_last`), `insertedIndex` = `[p, Q_0]` (dir `(1-t₀) • E_{-1}`, `edge_appendVertex_new`). `regular`: `regular_appendVertex`. `tail_off`: old vertex / old edge from `hΓ.tail_off`; old vertex on a piece of `E_{-1}` from `hΓ.tail_off` at `-1` unless the vertex is `Q_0` or `Q_{k-1}` (then parameter comparison, `edgePoint_injective`); `p` on an old edge excluded by `hoff`. `transverse`: pairs of old edges as in `Q` (adjacency in `ZMod (k+1)` vs `ZMod k` agrees off `-1`), pairs (piece, old edge) reduce to `(-1, i)` in `Q` unless `i ∈ {0, k-2}`, where the pieces `[Q_{k-1},p]`, `[p,Q_0]` do not meet `E_0`, `E_{k-2}` by L0.7a. `no_triple`: map the three edges to `Q`; two pieces of `E_{-1}` have disjoint interiors. | 200 |
| L0.8 ◻ | `reparam_positiveDiagram_single_appendVertex` | same hypotheses + `hΓ'` ⇒ `Reparam (positiveDiagram (single Q)) (positiveDiagram (single (appendVertex Q t₀)))` | `ReparamData`: `e = Equiv.refl`, `φ : TraversalPoint k ≃ TraversalPoint (k+1)`, `(i,u) ↦ (insertIndex i, u)` for `i ≠ -1`, `(-1,u) ↦ (insertIndex (-1), u/t₀)` if `u < t₀`, `(insertedIndex, (u-t₀)/(1-t₀))` else; inverse by the two affine maps back. `between`: `traversalKey ∘ φ = ψ ∘ traversalKey` with `ψ` strictly increasing piecewise linear `[0,k) → [0,k+1)`, so the three key-comparison disjuncts of `traversalBetween` transport. `eval_eq`: `edgePoint` scalings. `over_map`/`over_surj`: a crossing `{a,b}` of `Q` ↦ the pair with `-1` replaced by the piece containing the crossing point (`≠ p` by `hoff`), non-adjacent in `ZMod (k+1)` (adjacency in `Q` excludes `b ∈ {0,k-2}`), directions positive multiples so the positive over strand is preserved and `visitPt` maps to the rescaled parameter (`edgePoint_injective` on a nonzero edge); conversely every crossing of the subdivision avoids the non-meeting pairs `(k-1,0)`, `(k,k-2)` (L0.7a) hence comes from `Q`. Model: `shiftReparamData` (SM/CChamber.lean:819). | 280 |

### §1a Geo ↔ accepted bridge on a generic polygon (`hm : 3 ≤ m`, `hP : Generic P`, `hP' : CrossingGeometry P`, `S'`)

| # | lemma | statement | sketch | est. |
|---|---|---|---|---|
| F2.1 ◻ | `geoCarrierCrossings_eq_generic` | `geoCarrierCrossings hP' S' q = carrierCrossings hm hP S' (geoComponentEquivGeneric hm hP S' q)` | `Finset.ext`; both are `univ.filter (x ∉ S' ∧ ∀ v, v.1 = x → owner = q)`; rewrite `owner` as `geoComponentEquivGeneric (geoOwner …)` (`geoComponentEquivGeneric_owner`, rfl) and use injectivity of the `Equiv` | 20 |
| F2.2 ✔ | `geoCornerCount_eq_generic` | `geoCornerCount hP' S' q = ccpCornerCount hm hP S' (e q)` | `congrArg List.length (geoComponentCornerList_eq_generic …)` | 2 |
| F2.3 ◻ | `reindexed_ccpCornerPolygon_geoCornerPolygon` | `Reindexed (ccpCornerPolygon hm hP S' (e q)) (geoCornerPolygon hP' S' q)` | `show` the goal with `generic_crossingGeometry hm hP` (defeq), `reindexed_of_cast (geoCornerCount_eq_generic …).symm`; pointwise: `geoMarkPosition_eq_generic`, `geoComponentCornerList_eq_generic`, `getElem_idx_congr` with `ZMod.val_natCast_of_lt` | 25 |
| F2.4 ✔ | `cornerSelector_of_reindexed` | `Reindexed Q Q' → cornerSelector Q' = cornerSelector Q` | subst, `reindexed_eq_shift`, `cornerSelector_congr` with `turn_shift` | 10 |
| F2.5 ✔ | `carrierWeight_eq_cornerSelector` | `carrierWeight hm hP S' q = cornerSelector (ccpCornerPolygon …)` | `by_cases` on all-right / all-left, `C_X1.weight_right/left/mixed`, `cornerSelector_of_all_right/left/mixed` | 8 |
| F2.6 ✔ | `geoCarrierSelector_eq_carrierWeight` | `geoCarrierSelector hP' S' q = carrierWeight hm hP S' (e q)` | F2.3 + F2.4 + F2.5 | 3 |

### §2 The abstract transport (Tag B centrepiece; `e : ι ≃ Component hm hP S'`, `hS'`)

| # | lemma | statement | sketch | est. |
|---|---|---|---|---|
| — ✔ | `refCoefficient mC rC HC := coeffAt (1 - mC - \|round rC\|) 0 HC` | | | 2 |
| T1 ✔ | `cornerCoefficient_eq_ref` | `m(e q) = mC → r(e q) = rC → homfly (positiveLift (e q)) = HC → c(e q) = refCoefficient mC rC HC` | unfold def:C, rewrite | 4 |
| T2 ✔ | `cornerProduct_eq_of_carrier_data` | `cornerProduct hm hP S' hS' = ∏ q : ι, refCoefficient (mC q) (rC q) (HC q)` | `Fintype.prod_equiv e` + T1 | 5 |
| T3 ✔ | `wind_eq_of_weights` | `(∀ q ≠ q₀, wt(e q) = wC q) → wind = wt(e q₀) * ∏_{q ∈ univ.erase q₀} wC q` | `Fintype.prod_equiv`, `Finset.mul_prod_erase`, `prod_congr` | 8 |
| T4 ✔ | `flat_term_identity` | `aR − aL = aD → aR·U·B − aL·U·B = aD·U·B` | `ring` | 3 |

### §1b The flat configurations (`hn g j hz hb hc t hs S`; `hD : FlatCarriersDefinitionData`, `hF : FlatCarriersData`)

| # | lemma | statement | sketch | est. |
|---|---|---|---|---|
| — ✔ | `centreSupports`, `mem_centreSupports` | `univ.filter (GeoIndependent C)` | `simp` | 5 |
| F1.1 ✔ | `sideCarrierEquiv hF b : GeoComponent C S ≃ GeoComponent (flatSideCG b t) S_T`; `_owner` (rfl) | `Quotient.congr (markTransport (hs b))` with `correspond_sides.2` through `geoOwner_eq_iff` | 10 |
| F1.2 ✔ | `delToCentre`, `delToCentre_bijective`, `delCarrierEquiv`, `delCarrierEquiv_owner` | `Quotient.lift (geoOwner C S ∘ fusionMark)` well defined / injective by `correspond_deletion.2.1`, surjective by `.2.2`; `Equiv.ofBijective … .symm`, `Equiv.symm_apply_eq` | 30 |
| F1.3 ✔ | `sideEquiv hF b`, `delEquiv hF`, `sideEquiv_owner` (rfl), `delEquiv_owner`, `sideEquiv_central` (rfl), `delEquiv_central` | compose with `geoComponentEquivGeneric`; `Q_* ↦ owner (inl j)` since `markTransport` fixes vertices; `delEquiv Q_* = e (deletionCopyThroughJ)` by `central_vs_deletion_through_mu_j.1`, `fusionMark_delMark`, `geoOwner_successor` | 30 |
| F1.4 ✔ | `side_isDecomposition`, `del_isDecomposition` | from `hD.independent_supports` | 4 |
| F1.5 ✔ | `three_le_geoCornerCount_centre` | `3 ≤ geoCornerCount C S q` | `geoCornerCount_markTransport` (with `identify_sides_marks`), F2.2, `ccpCornerCount_ge_three` | 8 |

### §3a-b Slots and selectors from the cor fields

| # | lemma | statement | sketch | est. |
|---|---|---|---|---|
| F3.1 ✔ | `carrierCrossingCount_side` | `m(sideEquiv b q) = (geoCarrierCrossings C S q).card` | `q = geoOwner a`; F2.1 (explicit carrier), `same_retained_crossings.1` as `Finset.ext` with `crossingTransport` surjective, `Finset.card_map` | 20 |
| F3.2 ✔ | `carrierCrossingCount_del` | `m(delEquiv q) = (geoCarrierCrossings C S q).card` | `q = geoOwner (fusionMark b')` (`correspond_deletion.2.2`, `subst`), `delEquiv_owner`, `same_retained_crossings.2`, `fusionCrossingEquiv` | 20 |
| F4.1 ✔ | `carrierRotation_side` | `r(sideEquiv b q) = rotationNumber (geoCornerPolygon C S q)` | F2.3 + `rotationNumber_of_reindexed`, `same_rotation.1` | 12 |
| F4.2 ✔ | `carrierRotation_del` | `r(delEquiv q) = rotationNumber (geoCornerPolygon C S q)` | as F4.1 with `same_rotation.2` | 12 |
| F5.1 ✔ | `carrierWeight_side_eq_del` | `q ≠ Q_* → wt(sideEquiv b q) = wt(delEquiv q)` | F2.6 both sides, `other_selectors_agree` | 20 |
| F5.2 ✔ | `carrierWeight_central` | `wt(sideEquiv bR Q_*) − wt(sideEquiv bL Q_*) = wt(delEquiv Q_*)` | `selector_identity` rewritten by F2.6 three times, `delEquiv_central` | 12 |

### §3c The HOMFLY values (the geometric heart)

| # | lemma | statement | sketch | est. |
|---|---|---|---|---|
| — ✔ | `SidePathData t := ∀ s ≤ t, ∃ hs, ∀ S indep, FlatCarriersDefinitionData … s hs S` | the definition data along `(0,t]` (from `flat_carriers_definition`) | | 4 |
| F6a ✔ | `continuousAt_markPointOn_of_geometry g s hC hcr a` | `ContinuousAt (fun s => markPointOn g s a) s` for `hC : CrossingGeometry (g.curve s)`, `hcr` : the centre's crossing pairs persist at `s` | copy of `continuousAt_markPointOn` (FlatCarriers 4486) at `s` | 14 |
| — ✔ | `famParam g t b u`, `_zero`, `_one`, `_pos`, `continuous_famParam` | the parameter `±(u·t) : g.Parameter` | `Subtype.ext`, `simp` | 30 |
| F6a'' ◻ | `famParam_crossings hpath b u c` | `IsCrossing g.center c → IsCrossing (g.curve (famParam u)) c` | `u = 0`: `famParam_zero`; `u > 0`: `famParam_pos` and `(hpath ⟨u·t,_,_⟩ _).choose b c` | 15 |
| — ✔ | `sideFamily t S q b u := cornerFamily … S q (famParam u)`, `_zero` (= `geoCornerPolygon C S q`), `_one` | | | 10 |
| F6a' ✔ | `continuous_sideFamily` | `Continuous (sideFamily …)` | F6a at every `famParam u` with `flat_germ_spatial_data` (`CrossingGeometry (g.curve s)` for every `s`), `continuous_pi` | 15 |
| F6b ◻ | `reindexed_cornerFamily_side s hs' hD' b a` | `Reindexed (ccpCornerPolygon side_s S_T (e (geoOwner (flatSideCG b s) S_T (mT a)))) (cornerFamily S (geoOwner C S a) (sideTime b s))` | `geoComponentCornerList_markTransport … (hD'.identify_sides_marks b)` gives the side corner list as the mapped centre list; `reindexed_markPolygon_map`, `markPolygon_congr` with `markPointOn_side`, then F2.3 and transitivity of `Reindexed` (device of `rotationNumber_cornerFamily_side`, FlatCarriers 4533) | 40 |
| F6b' ✔ | `single_generic_cornerFamily_side` | the family's single shadow is generic at every side parameter | L0.3 with F6b and `carrierShadow_generic` | 8 |
| F6c ◻ | `reindexed_del_centre_of_ne hF q hq` | `q ≠ Q_* → Reindexed (ccpCornerPolygon del S_D (delEquiv q)) (geoCornerPolygon C S q)` | `q = geoOwner (fusionMark b')`; `others_unchanged.2.1` (corner cycles), `reindexed_markPolygon_of_isRotated`, `reindexed_markPolygon_map`, `markPolygon_congr` with `fusion_mark_point`, then F2.3 (device of `rotationNumber_others_unchanged`, FlatCarriers 4383) | 40 |
| F6d ◻ | `flat_vertex_subdivision hF` | `∃ r t₀, 0<t₀<1 ∧ (∀ i ≠ -1, edgePoint (shift r Q_D) (-1) t₀ ∉ edgeSegment (shift r Q_D) i) ∧ Reindexed (appendVertex (shift r Q_D) t₀) (geoCornerPolygon C S Q_*)` with `Q_D := ccpCornerPolygon del S_D (delEquiv Q_*)` | Corner list `L` of `Q_*` at the centre contains `x = inl j`; rotate `L` to `M ++ [x]`, then `geoCornerPolygon = markPolygon f L` is `Reindexed` to `markPolygon f (M ++ [x])`; by `turns_nonzero.1` + `flat_of_turn_eq_zero` (regularity from `nonzero_segments.2`, `no_antiparallel.1`) `f x = edgePoint (markPolygon f M) (-1) t₀` with `0<t₀<1`; `reindexed_appendVertex_markPolygon`; `M.map delMark ~r` the deletion corner list (`central_vs_deletion_through_mu_j.3`, `delEquiv_central`) and `deletion_mark_point` identify `markPolygon f M` with a shift of `Q_D` (F2.3). Off-edge clause: `μ_j` in a closed edge `i ≠ -1` of `shift r Q_D` would be, by `Link.consecutive_meet` (adjacent) a corner point of `Q_D` = a mark point of `D` (a vertex of `D` ≠ `μ_j` by injectivity of `g.center`, or a crossing point of `D` = a crossing point of `C` by `crossingPoint_fusion`, ≠ `μ_j` by `flat_germ_spatial_data`), or by `Link.nonadjacent_meet_crossing` a crossing point, same contradiction. This is the list surgery of `rotationNumber_erase_flat` (FlatCarriers 4164) redone for the polygon itself. | 160 |
| F6e ✔ | `single_generic_centre` | the centre corner polygon of every carrier is a generic single shadow | `Q_*`: F6d + L0.1 + L0.7 + L0.3; else F6c + L0.3 + `carrierShadow_generic` | 15 |
| F6e' ✔ | `single_generic_sideFamily` | genericity along the whole family | `u = 0`: F6e; `u > 0`: F6b' at `s = u·t` from `hpath` | 15 |
| F6f ✔ | `planarIsotopic_side_centre` | side lift ≃ `positiveDiagram (single (geoCornerPolygon C S q))` | L0.4 (F6b at `s = t`) then L0.6 backwards, `positiveDiagram_congr` at `u = 0` | 35 |
| F6g ✔ | `planarIsotopic_centre_del` | centre diagram ≃ deletion lift | `Q_*`: L0.4 (F6d) ⁻¹ ∘ L0.8 ⁻¹ ∘ L0.2 ⁻¹; else L0.4 (F6c) ⁻¹ | 20 |
| F6 ✔ | `homfly_side_eq_del` | `homfly (side lift (sideEquiv b q)) = homfly (deletion lift (delEquiv q))` | `homfly_planar (F6f.trans F6g)` | 3 |

### §3d The three instantiations

| # | lemma | statement | sketch | est. |
|---|---|---|---|---|
| I1 ✔ | `cornerProduct_side_eq_del` | `cornerProduct side S_T = cornerProduct del S_D` | T2 for the side with `mC q := (geoCarrierCrossings C S q).card`, `rC q := rotationNumber (geoCornerPolygon C S q)`, `HC q := homfly (deletion lift (delEquiv q))` (F3.1, F4.1, F6); T2 for the deletion with the same reference data (F3.2, F4.2, `rfl`) | 25 |
| I2 ✔ | `wind_side_sub_side_eq_del` | `wind sideR S_TR − wind sideL S_TL = wind del S_D` | T3 three times with `wC q := wt(delEquiv q)`, `q₀ := Q_*` (F5.1; `rfl` for the deletion), `sub_mul`, F5.2 | 20 |

### §4 The sums, the one-parameter law, chamber constancy, assembly

| # | lemma | statement | sketch | est. |
|---|---|---|---|---|
| F7.1 ◻ | `cornerStateSum_side_eq hD b` | `C(side b t) = Σ_{S ∈ centreSupports.attach} wind side (S_T) * cornerProduct side (S_T) (side_isDecomposition …)` | `C_X1.selector_form`; pass to total functions of the underlying set (the `dite` device of `cornerStateSum_transport`, CChamber 503), then `Finset.sum_nbij (transportSupport (hs b))`: maps into `independentSupports side` by `independent_supports.1`, `InjOn` by `Finset.map_injective`, `SurjOn` by `S := S'.map (crossingTransport (hs b)).symm` and `independent_supports.1` backwards | 60 |
| F7.2 ◻ | `cornerStateSum_del_eq hD` | the same for the deletion with `deletionSupport` | as F7.1 with `fusionCrossingEquiv` and `independent_supports.2` | 60 |
| F10 ✔ | `flat_law_at hD hF hpath bR bL hR hL` | `C(side bR t) − C(side bL t) = C(D)` | F7 ×3, `Finset.sum_sub_distrib`, per `S`: I1 twice, `sub_mul`, I2 | 12 |
| F11 ✔ | `instance : PreconnectedSpace g.SideParameter`; `turn_sideTuple_eq`; `sideTuple_mem_labelledChamber`; `cornerStateSum_sideTuple_eq` | turn constancy and `C` constancy along one side | `Subtype.preconnectedSpace isPreconnected_Ioo`; `Carrier.generic_family_turn_constant (g.continuous_sideTuple b)`; `(isPreconnected_range …).subset_connectedComponent`; `cornerStateSum_eq_of_mem_labelledChamber` | 12 |
| F12 ✔ | `thm_C_S3` | | `δ := min δ₁ δ₂` from `flat_carriers_definition` / `flat_carriers`; at `t = tR` take `hs`, `hF`, `hD` (proof irrelevance of `CommonSupports`), `hpath` from `δ₁`; `IsLeftSide bL tR` by `turn_sideTuple_eq`; `C(bL, tL) = C(bL, tR)` by F11; `flat_law_at` | 25 |

## 3. Dependency order (a topological order for prover units)

1. §0: L0.1 → L0.2 → L0.3 → L0.4; L0.5 → L0.6; L0.7a → L0.7 → L0.8 (independent of the flat layer).
2. §1a: F2.2 → F2.3 → F2.4/F2.5 → F2.6; F2.1 (independent).
3. §2: T1 → T2; T3; T4 (independent of everything else).
4. §1b: F1.1, F1.2 → F1.3; F1.4; F1.5 (needs F2.2).
5. §3a-b: F3 (F2.1, F1), F4 (F2.3, F1), F5 (F2.6, F1).
6. §3c: F6a → famParam → F6a'' → F6a'; F6b (F2.3) → F6b'; F6c (F2.3, F1); F6d (F2.3, F1, FlatCarriers list surgery); F6e (F6c, F6d, L0.1, L0.3, L0.7) → F6e' (F6b') → F6f (L0.4, L0.6, F6b) ; F6g (L0.2, L0.4, L0.8, F6c, F6d) → F6.
7. §3d: I1 (T2, F3, F4, F6); I2 (T3, F5).
8. §4: F7.1, F7.2 → F10 (I1, I2) ; F11 → F12.

Suggested prover units: **U1** L0.7a/L0.7/L0.8 (pure polygon/diagram geometry, ~520 lines, the long pole);
**U2** F6b/F6c/F6d + F6a'' (flat corner-list geometry, ~255 lines); **U3** F2.1/F2.3 + F7.1/F7.2 (bridge and
sums, ~165 lines). Everything else is already proved in the skeleton.

## 4. Reuse list (verified names; file:line in work/lean)

Accepted rows used as black boxes: `SM.flat_carriers_definition` (SM/FlatCarriers.lean:5596),
`SM.flat_carriers` (5617), `SM.C_X1` (SM/CX1.lean:269), `SM.prop_C_chamber`'s engine
`cornerStateSum_eq_of_mem_labelledChamber` (SM/CChamber.lean:1366), `SM.flat_sides` (SM/FlatSides.lean:47,
inside the two row theorems), `generic_deleteVertex` (SM/DeletionGeneric.lean:32), `homfly_planar`
(SM/LinkInterfaces.lean:382, the `lit_homfly` planar clause).

SM/CornerStateSum.lean: `cornerSlot` 82, `cornerCoefficient` 110, `cornerProduct` 158, `cornerStateSum` 166,
`cornerStateSum_eq_sum_independentSupports` 174; `carrierRotationInt` 61.
SM/CX1.lean: `carrierWeight` 24, `wind` 31, `CX1Data` 245 (fields `weight_right/left/mixed`, `selector_form`).
SM/FlatCarriersDefs.lean: `geoMarkPosition_eq_generic` 101, `GeoComponent` 258, `geoOwner` 262,
`geoOwner_eq_iff` 266, `geoOwner_successor` 270, `geoOwner_surjective` 278, `geoComponentCornerList` 367,
`geoCornerCount` 387, `geoCornerMark` 396, `geoCornerPolygon` 402, `geoCarrierCrossings` 451,
`GeoIndependent` 457, `cornerSelector` 466, `geoCarrierSelector` 471, `flat_hn1` 488, `flatCentreCG` 494,
`flatDeletionCG` 502, `flatSideCG` 511, `CommonSupports` 519, `IsRightSide` 525, `IsLeftSide` 529,
`markTransport` 536, `transportSupport` 541, `deletionSupport` 547, `fusionMark` 557, `delMark` 566,
`fusionMark_delMark` 582, `centralCarrierThroughJ` 604, `deletionCopyThroughJ` 614,
`geoMarkList_eq_generic` 644, `geoComponentEquivGeneric` 676, `geoComponentEquivGeneric_owner` 683,
`geoComponentCornerList_eq_generic` 713, `FlatCarriersDefinitionData` 809 (fields `identify_sides_marks`,
`independent_supports`), `FlatCarriersData` 969 (fields `correspond_sides`, `correspond_deletion`,
`central_vs_deletion_through_mu_j`, `others_unchanged`, `nonzero_segments`, `no_antiparallel`,
`turns_nonzero`, `same_retained_crossings`, `same_rotation`, `selector_identity`, `other_selectors_agree`).
SM/FlatCarriers.lean: `mem_transportSupport_iff` 1533, `markTransport_vertex/visit` 1540/1544,
`geoComponentCornerList_markTransport` 1631, `geoCornerCount_markTransport` 1646, `Reindexed` 4010,
`reindexed_eq_shift` 4019, `rotationNumber_of_reindexed` 4028, `regular_of_reindexed` 4034,
`reindexed_of_cast` 4043, `markPolygon` 4050, `getElem_idx_congr` 4057, `geoCornerPolygon_eq_markPolygon`
4070, `reindexed_markPolygon_of_rotate` 4086, `reindexed_markPolygon_of_isRotated` 4091,
`reindexed_markPolygon_map` 4098, `markPolygon_congr` 4108, `reindexed_appendVertex_markPolygon` 4127,
`rotationNumber_erase_flat` 4164 (model for F6d), `deletion_mark_point` 4285, `fusion_mark_point` 4303,
`flat_of_turn_eq_zero` 4312, `rotationNumber_deletionCopyThroughJ` 4324, `rotationNumber_others_unchanged`
4383 (model for F6c), `markPointOn` 4435, `visit_point_eq_edgePoint` 4443, `markPointOn_zero` 4452,
`markPointOn_side` 4460, `continuousAt_markPointOn` 4486 (model for F6a), `cornerFamily` 4505,
`cornerFamily_zero` 4511, `cornerFamily_eq_markPolygon` 4518, `rotationNumber_cornerFamily_side` 4533
(model for F6b), `cornerSelector_of_all_right/left/mixed` 4856/4862/4872,
`geoCarrierSelector_eq_cornerSelector` 4878, `cornerSelector_congr` 4946, `selector_table` 4978.
SM/CChamber.lean: `positiveDiagram_congr` 567, `single_isCrossing_iff_of_forall` 573,
`crossingGeometry_of_single_generic` 582, `Link.Deform.of_family` 601,
`Link.Diagram.isPositive_deform_of_family` 625, `positiveDiagram_single_recast` 666, `shiftStrandMap` 685,
`shiftReparamData` 819 (model for L0.8), `reparam_positiveDiagram_single_shift` 846,
`Carrier.generic_family_turn_constant` 940, `isCrossing_transportedCornerPolygon_path` 1110 (model for
L0.5), `deform_positiveLift_path` 1152 (model for L0.6), `cornerStateSum_transport` 503 (model for F7).
SM/LinkMoves.lean: `ReparamData` 370, `Reparam` 387, `DeformData` 462, `Deform` 478, `PlanarIsotopic` 516,
`PlanarIsotopic.of_reparam/of_deform/symm/trans` 519-534.
SM/LinkDiagram.lean: `Shadow.Generic` 394, `Diagram` 490, `StrandMap` 752, `StrandMap.generic_pullback`
856, `Diagram.pullback` 910, `Shadow.single` ~1580, `single_isCrossing_iff` 1641, `crossingParam_spec`
1416, `visitPt` 1435.
SM/LinkPositiveLift.lean: `Shadow.positiveDiagram` 93, `Shadow.eq_positiveDiagram_of_isPositive` 128,
`Shadow.single_generic_of` 160, `carrierPolyComp` 211, `carrierShadow` 218, `Link.nonadjacent_meet_crossing`
520, `carrierShadow_generic` 580, `positiveLift` 596, `eq_positiveLift_of_isPositive` 633,
`Link.consecutive_meet` 698.
SM/WallGerm.lean: `WallGerm` 13, `SideParameter` 26, `zeroParameter` 28, `sideTime` 34, `sideTuple` 49,
`continuous_sideTuple` 52. SM/Chambers.lean: `GenericTuple` 14, `labelledChamber` 24.
SM/FlatSpatial.lean: `flat_germ_spatial_data` 23. SM/DeletionInteriors.lean:
`deleted_middle_not_on_unchanged` 12. SM/FusionCrossings.lean: `crossingPoint_fusion` 42,
`fusionCrossingEquiv` 91. SM/CrossingTransport.lean: `crossingTransport` 12, `visitTransport` 18.
SM/InsertedTuple.lean: `appendVertex` 11, `appendVertex_old` 14, `appendVertex_new` 18,
`edge_appendVertex_old` 30, `edge_appendVertex_last` 35, `edge_appendVertex_new` 40.
SM/AppendRotation.lean: `regular_appendVertex` 26, `rotationNumber_appendVertex` 54.
SM/InsertionIndices.lean: `insertIndex` 11, `insertedIndex` 13, `insertion_indices_exhaust` 43.
SM/RegularLocus.lean: `Regular` 12, `regular_iff_edges` 18, `regular_shift` 61. SM/Polygon.lean: `shift`
22, `edge` 49, `edgePoint` 51, `edgeSegment` 54, `edgeInterior` 57, `incident` 60, `adjacent` 63,
`edgePoint_shift` 77, `edgeSegment_shift` 81. SM/Chirotope.lean: `turn_det` 87, `turn_shift` 103.
SM/RotationNumber.lean: `rotationNumber` 10, `rotationNumber_shift` 53.
SM/GeometricCrossingStability.lean: `crossing_support_persists_of_geometry` 35.
SM/GeometricParameters.lean: `continuousAt_edgeParameter_of_geometry` 58. SM/CrossingGeometry.lean:
`CrossingGeometry` 11, `generic_crossingGeometry` 24. SM/CarrierCrossings.lean: `carrierCrossings` 56,
`carrierCrossingCount` 62, `mem_carrierCrossings` 66, `carrierCrossingCount_eq_card` 113.
SM/UniformDefinition.lean: `CarrierUniform` 27, `UniformDecomposition` 37, `carrierRotation` 42.
SM/CarrierCornerPolygon.lean: `ccpCornerList` 317, `ccpCornerCount` 341, `ccpCornerMark` 350,
`ccpCornerPolygon` 357, `ccpCornerCount_ge_three` 691. SM/CarrierSmoothing.lean: `Component` 124, `owner`
130. SM/InterlaceSupports.lean: `independentSupports` 27, `mem_independentSupports_iff` 39.
SM/DecompositionDefinition.lean: `IsDecomposition` 15.
Mathlib: `Quotient.congr`, `Equiv.ofBijective`, `Equiv.symm_apply_eq`, `Fintype.prod_equiv`,
`Finset.mul_prod_erase`, `Finset.sum_nbij`, `Finset.sum_sub_distrib`, `Finset.mem_map_equiv`,
`Finset.card_map`, `IsLocallyConstant.iff_eventually_eq`, `IsLocallyConstant.apply_eq_of_preconnectedSpace`,
`Subtype.preconnectedSpace`, `isPreconnected_Ioo`, `isPreconnected_range`,
`IsPreconnected.subset_connectedComponent`, `mul_le_of_le_one_left`.

## 5. Estimated lines

Skeleton as delivered: 1082 lines (75 declarations, 64 sorry-free). Remaining `sorry`s and estimates:
L0.7a 40, L0.7 200, L0.8 280, F2.1 20, F2.3 25, F6a'' 15, F6b 40, F6c 40, F6d 160, F7.1 60, F7.2 60 —
**≈ 940 lines of new proof**, total file ≈ 1900-2000 lines (the skeleton's docstrings and statements are
kept). Compile time of the skeleton: ~40 s (imports SM.FlatCarriers, SM.CX1, SM.CChamber).

## 6. Design decisions worth recording

1. **Reference data at the centre / on the deletion, never a state sum at the centre.** `m_Q` is
   `(geoCarrierCrossings C S q).card`, `r_Q` is `rotationNumber (geoCornerPolygon C S q)` (both read at the
   flat centre, where cor:flat-carriers (ii) puts them), while `H⁺_Q` is read on the *deletion copy*
   (`homfly (positiveLift del (delEquiv q))`), so that the deletion instantiation of T2 is `rfl` and the two
   side instantiations carry the whole geometric content (F6). No value of `C` is assigned at the centre,
   as the printed closing sentence demands.
2. **Where the wall is crossed.** The printed proof identifies the H polynomials via lc:presentations +
   lp:core (unproved). Here the positive lifts are compared through the corner polygon family
   `u ↦ cornerFamily S q (±u·t)` (the accepted U4 object of SM/FlatCarriers.lean), which is a continuous
   family of one-component shadows, generic at every `u` — at `u > 0` because it is (a re-indexing of) an
   accepted carrier polygon of a generic side polygon, at `u = 0` because the centre corner polygon is a
   re-indexing (F6c) or a positive-flat subdivision (F6d) of the deletion copy's polygon. So the
   deformation stays inside generic one-component shadows even though the *parent* polygon at `u = 0` is
   not generic, and `Deform.of_family` applies; the vertex-count change of `Q_*` is a `Reparam` (L0.8).
3. **Bridge over an arbitrary `CrossingGeometry` proof.** `flatSideCG`/`flatDeletionCG` are theorems, so
   `rw` cannot unify them with `generic_crossingGeometry`; the bridge lemmas take `hP' : CrossingGeometry P`
   and the carrier `q` explicitly (an underscore here makes `exact` time out — observed and fixed).
4. **Two side parameters.** The statement lets `tR ≠ tL`; cor:flat-carriers lives at one `t`. The left
   value is moved to `tR` by chamber constancy along the side (`g.sideTuple bL` is a continuous family of
   generic polygons on the connected `SideParameter`), and `bL` stays the left side there by turn constancy.
   `CommonSupports` is a Prop, so the witnesses `hs` of the two row theorems agree by proof irrelevance.
5. `SidePathData` packages what the deformation needs at intermediate side parameters: only the
   *definition* data (`identify_sides_marks`, `independent_supports`) of `flat_carriers_definition`, whose
   radius covers all `s < δ₁`.

## 7. The three riskiest steps and fallbacks

1. **L0.7 / L0.8 — genericity and `Reparam` of the edge subdivision `appendVertex` (~480 lines, new
   geometry; "the Reparam for the flat subdivision").** Risk: the `ReparamData.between` clause needs a
   strictly increasing piecewise-linear circle map on `traversalKey`s and the `over_map`/`over_surj`
   clauses need the crossing correspondence of the subdivided polygon; the label case analysis
   `insertIndex`/`insertedIndex` is fiddly (`ZMod (k+1)` vs `ZMod k` adjacency). Mitigations: the
   accepted `shiftReparamData` (CChamber 819) is the template for `over_map` via `crossingParam_spec` and
   `edgePoint_injective`; `regular_adjacent_meet` (L0.7a) isolates the one genuinely geometric fact (the
   pairs `(k-1,0)`, `(k,k-2)` do not meet). Fallback A: prove L0.8 through a general "monotone
   reparametrization of one component preserving the trace is a `Reparam`" lemma (φ given by any
   strictly increasing bijection of keys with `eval` compatibility), then specialise. Fallback B: state
   L0.7/L0.8 for `insertVertex Q i t₀` (SM/VertexInsertion.lean:11, = `appendVertex (shift (i+1) Q) t₀`) if the
   list surgery of F6d turns out to produce that normal form more naturally; the two are interchangeable
   through L0.1/L0.2.
2. **F6d `flat_vertex_subdivision` (~160 lines; "is the centre corner polygon of `Q_*` a generic shadow
   with the same crossing pairs?").** Answer: yes, and it is proved *without* redoing the carrier geometry
   at the non-generic centre — the centre corner polygon of `Q_*` is exhibited as a positive-flat
   subdivision of the deletion copy's accepted corner polygon (a generic single shadow by
   `carrierShadow_generic`), so L0.7 gives genericity and L0.5 the constancy of crossing pairs along
   the family. Risk: the list surgery (rotate the corner list to `M ++ [inl j]`, identify `M.map delMark`
   with the deletion corner list as cycles, transport the mark points by `deletion_mark_point`) and the
   off-edge clause (μ_j lies on no other closed edge of the deletion polygon: `Link.consecutive_meet`,
   `Link.nonadjacent_meet_crossing`, `crossingPoint_fusion`, `flat_germ_spatial_data`, injectivity of
   `g.center` from `FlatSidesData.1`). Fallback: split into (i) the `Reindexed` clause, which is exactly
   the proof of `rotationNumber_erase_flat` (FlatCarriers 4164-4283) with `rotationNumber_of_reindexed`
   removed — copy that proof and stop at the `Reindexed` statement; (ii) the off-edge clause as a
   separate lemma on the generic deletion polygon (`μ_j ∈ edgeInterior D (-1)` by
   `central_vs_deletion_through_mu_j.4/.5`, `deleted_middle_not_on_unchanged` for the other edges of `D`,
   then the corner-polygon edges are sub-segments of edges of `D` — `ccpCornerPolygon_edgeSegment`
   (CarrierCornerPolygon 762) — and the sub-segments of `E_{-1}(D)` other than the one through μ_j are
   excluded because μ_j is not a mark point).
3. **F6b / F7 — the dependent-type bookkeeping across the four configurations (~200 lines).** F6b must
   produce `Reindexed` between the *accepted* corner polygon of the side copy at an intermediate `s` and
   `cornerFamily S q (sideTime b s)`; the ingredients (`geoComponentCornerList_markTransport`,
   `markPointOn_side`, F2.3) exist and `rotationNumber_cornerFamily_side` shows the exact `Reindexed`
   chain, but the side copy is named through `geoOwner (flatSideCG …) … (markTransport a)` and the
   `geoComponentEquivGeneric`, so all carriers must be passed explicitly (see §6.3). F7 reindexes the
   `attach`ed sums with dependent summands: use the total-function `dite` device of
   `cornerStateSum_transport` (CChamber 503-557) verbatim, then `Finset.sum_nbij` with
   `transportSupport (hs b)` / `deletionSupport`; `SurjOn` needs the inverse support
   `S'.map (crossingTransport (hs b)).symm.toEmbedding` and `independent_supports` backwards. Fallback:
   prove F7 through a general lemma "`Finset.sum` over `independentSupports hQ` equals the sum over
   `centreSupports` for any support bijection `σ` with `σ S ∈ Ind(Q) ↔ GeoIndependent C S`", stated
   once and used twice.

Lesser risks (already discharged in the skeleton): the `Equiv`s `sideEquiv`/`delEquiv` and their
computation rules (`sideEquiv_owner` is `rfl`; `delEquiv_owner` needs `Equiv.symm_apply_eq`), the
`Q_*` computations (`sideEquiv_central` rfl, `delEquiv_central` from `central_vs_deletion_through_mu_j.1`),
the instantiations I1/I2, the selector algebra, the assembly with two side parameters.

## 8. What the skeleton proves right now

`thm_C_S3` is proved from the chain; `#print axioms` should list `propext, Classical.choice, Quot.sound,
SM.lit_homfly, sorryAx` (the `sorryAx` from the 11 open lemmas: L0.7a, L0.7, L0.8, F2.1, F2.3, F6a'',
F6b, F6c, F6d, F7.1, F7.2 at Skeleton_B.lean lines 132, 144, 160, 180, 193, 649, 697, 726, 754, 968, 982).
No other axioms; nothing is stated at the flat centre except carrier geometry.
