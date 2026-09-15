# PLAN_FINAL — prop:C-silent (silence) `C(P₊) = C(P₋)` at a simple (E) or (C) wall

Written 2026-09-14 by the judge of the two independent plans (PLAN_A.md / Skeleton_A.lean, PLAN_B.md /
Skeleton_B.lean). Target `SM.prop_C_silent : CSilentData`, statement FIXED in `work/drafts/CSilent_statement.lean`
(bundle `CSilentData` and the header `theorem prop_C_silent : CSilentData := by` copied byte-identically at the
end of the skeleton; checked by string comparison). Source: reference/SM/sm-4-knotlaws.tex:101-105 (statement),
106-152 (proof). Skeleton: `work/drafts/csilent/Skeleton_FINAL.lean` — **1491 lines, 88 declarations, 2 sorried**,
checked with `cd work/lean && lake env lean ../drafts/csilent/Skeleton_FINAL.lean` (0 errors; the only warnings are
the two `declaration uses 'sorry'`); `#print axioms SM.prop_C_silent` = `propext, sorryAx, Classical.choice,
Quot.sound, SM.lit_homfly` — exactly the axiom set of the accepted `prop_C_chamber` and `thm_C_S3`.
**`prop_C_silent` is PROVED from the chain**; both `sorry`s are leaves of one section (§3, centre genericity).

## 0. Judgement

| | Plan A (R1, record-first) | Plan B (R2 hybrid, chamber/S3 route) |
|---|---|---|
| (a) correctness against the fixed statement | 9 — bundle byte-identical, theorem proved from the chain, no added hypothesis | 9 — same |
| (b) provability with the existing library | 6 — 22 leaves, ~1160 new lines in 4 units; U4 (`liftVisitEquiv_visitCoord_lt`, 180 lines of `singleVisitEquiv`/`visitPt`/`recastTuple` bookkeeping) and U3 (`isCrossing_ccp_iff`, block witnesses) are long poles; depends on SM/PolynomialBlock (under review) | 8 — 6 leaves, all in one section; every accepted input exists (verified by grep, see §0.2); the judge closed 4 of the 6 and half of the 5th |
| (c) minimality / fidelity | 7 — no `Deform`, no centre corner polygon, but a full record isomorphism and the extra axioms `SM.lp_lm`, `SM.lp_lm_uniqueness` through `P_eq_homfly`/`presentations` | 8 — one new geometric input (genericity of the centre carrier polygon, the formal content of printed lines 118-131); axiom set = the accepted wall rows |
| **winner** | — | **B** (base route, all of §0-2, §4-7 kept verbatim) |

Both routes are sound. Both read the state sums only on the generic sides, both reduce the two side
parameters `(tp, tm)` of the fixed statement to one by prop:C-chamber along a side, both build the same
`Carrier.MarkTransport` between `P(−t)` and `P(+t)` from `silent_sides` and close with the accepted
`MarkTransport.cornerStateSum_transport`. They differ only in how the two per-carrier coefficient inputs are
obtained:

* **rotation** — A: an intermediate-value argument on the angle sum `Σ ∠(d_in, d_out)` of parent directions
  through the centre (needs six new leaves: `eq_of_continuous_int_valued_off_point`,
  `carrierRotation_eq_sum_principalAngle`, continuity, integrality, interval bookkeeping). B: the accepted
  `rotationNumber_family_constant` along `u ↦ silentCornerFamily … (silentPath g t u)`, regular at every time —
  the centre regularity `geoCornerPolygon_regular_of_weak` is PROVED in B (turns nonzero by `WeakGeneric`,
  crossing pairs transverse by `CrossingGeometry`). B's is what the printed proof says (lem:rot (ii) along the
  germ, "every carrier tuple is continuous, has nonzero segments, and has no antiparallel corner").
* **`H⁺`** — A: `SM.presentations` + `P_eq_homfly` on a `RecordIso` of the two positive lifts built on the
  generic sides (printed lines 137-141 literally), costing the block-witness characterisation of the crossings
  of a corner polygon (U3) plus twin/over-bit/visit-order preservation (U4) and the `lp_lm` axioms. B:
  `Link.homfly_positiveDiagram_single_of_family` (lit:homfly's planar clause) along the same family, costing
  genericity of the one-component shadow of the centre corner polygon (`single_generic_of_weak`). This is the
  substitution already made by the accepted prop:C-chamber and thm:C-S3, and it stays inside the printed
  proof's own constraint: it applies no generic-polygon lemma at the centre — §3 uses only `WeakGeneric`,
  `CrossingGeometry`, the transported `TracedSuccessor`/`htwin` combinatorics and the block parametrisation.

A's claim that R2 "would need Shadow.Generic of the carrier polygon at the non-generic centre, i.e. re-deriving
the generic-parent self-intersection lane" is correct in substance but overestimates the cost: on the geometric
record domain the accepted SM/FlatCarriers.lean already supplies the block chain (`geoCornerPolygon_edge_data`
:3253, `geo_block_compression` :3080), the position cases (`geoMarkSuccessor_position_cases` :2729), the
successor gap (`geoMarkSuccessor_no_mark_between` :361) and mark-position injectivity
(`geoMarkPosition_injective` FlatCarriersDefs.lean:108); what remains is one block structure and one meeting
lemma, and the judge closed the meeting lemma's assembly and two of its three cases in under an hour.

**Grafts from A.** None are needed structurally (A's `SilentPairData` is B's `SilentFamilyData` read at two
parameters; A's `regularPair_of_det_ne_zero`/`weak_regularPair_turn`/`geometry_regularPair_crossing` are B's
`geoCornerPolygon_regular_of_weak`). A's `cornerStateSum_side_const` is B's `cornerStateSum_silent_side_const`
(identical proofs). A's observation that `hinj` follows from `CrossingGeometry` alone
(`crossingPoint_injective_of_geometry`, CrossingGeometry.lean:61) is recorded here: §3 keeps `hinj` as an
explicit hypothesis (it is supplied by `SilentFamilyData` anyway), so a prover may use either.

**Judge's additions (all in §3).** The meeting lemma is split into its three parent-edge cases with the block data
passed explicitly (`GeoBlock … a ta`, `GeoBlock … b tb`), so the cases are independent of `exists_geoBlock`'s
proof and of each other; `geoCornerPolygon_meet_of_weak` is PROVED from the three cases (`adjacent` split:
`e_b − e_a ∈ {−1, 0, 1}` by `linear_combination`, else `remote`). Closed by the judge: `geoCornerPolygon_meet_same_edge`
(via the directed `_aux`, `le_total` on the block starts), `geoCornerPolygon_meet_next_edge`,
`geoCornerPolygon_injective_of_weak`, `_tail_off_of_weak`, `_transverse_of_weak`, `_no_triple_of_weak`, and the
helpers `self_not_mem_edgeInterior`, `next_not_mem_edgeInterior`, `isTrueCorner_selectedMarkPerm`.

### 0.1 Probe of A's riskiest leaf (`liftVisitEquiv_visitCoord_lt`, with `isCrossing_ccp_iff` behind it)
True as stated: `visitCoord` on a one-component shadow is `traversalKey (visitPt v).2 = label.val + crossingParam`
(`traversalKey_lt_iff` Traversal.lean:46 orders by label first); labels are preserved by
`singleVisitEquiv ∘ visitTransport ∘ singleVisitEquiv⁻¹`; on one corner edge `a` the parameter of an occurrence is
`(μ − λ_a)/c_a` with `μ` the parent parameter of its block witness, and `SilentPairData.ho` preserves the order of
the `μ`'s. No counterexample; the cost is the dependent-type bookkeeping (A estimates 180 lines) plus
`isCrossing_ccp_iff` (⇒), whose accepted input `nonadjacent_meet` (LinkPositiveLift.lean:443) exports only the
parent edges, not the block index (A's fallback: `ccpCornerPolygon_no_triple` :556). Provable, but ~650 lines
of U3+U4 for what B obtains from one centre-genericity lemma.

### 0.2 Probe of B's riskiest leaf (`exists_geoBlock`, especially `interior_mark`)
Every input exists and says what PLAN_B claims (read in full): `geoCornerPolygon_edge_data` (FlatCarriers.lean:3253)
returns `m ≥ 1`, `ρ_S^m c_k = c_{k+1}`, `∀ 1 ≤ r < m, ¬ IsTrueCorner S (ρ_S^r c_k)`, the positive edge multiple and
`e_k = geoInEdge c_{k+1}`; `geo_block_compression` (:3080) returns `∀ r < m, (geoOutSlot (ρ_S^r c_k)).1 = e` and
`t > s`, `t ≤ 1`, `point (ρ_S^m c_k) = edgePoint P e t`; `geo_evaluation_eq_outSlot` (:3049) gives `corner_eq`;
`edgePoint_injective (hP.1 e)` gives `mem_segment_iff`/`mem_interior_iff`/`exists_param` from `next_eq`;
`geoMarkPosition_injective` gives `start_mark` (since `geoOutSlot a = geoMarkPosition (selectedMarkPerm S a)` by
`rfl`); `geoMarkSuccessor_position_cases` (:2729) on the last step gives `end_mark`/`end_vertex` (a visit successor
lies on the same edge at a parameter `< 1`, so `t = 1` forces the vertex `inl (e+1)`; conversely a mark at `(e, t)`
has `t < 1`); `interior_mark` is `geoMarkSuccessor_no_mark_between` (:361) along the consecutive chain marks
`selectedMarkPerm S c_k, ρ_S c_k, …, ρ_S^{m−1} c_k, c_{k+1}` (whose positions on `e` are strictly increasing by
`geo_incoming_visit_position` :3063 and `geoOutSlot_unselected` :3026), the strictly interior chain marks being
unselected visits (`ccp_not_trueCorner` CarrierCornerPolygon.lean:123). The `traversalBetween` bookkeeping
(Traversal.lean:73; same-edge keys `e.val + u`, wrap through the vertex `e+1` handled by the cyclic disjuncts) is the
only fiddly part. The judge's closure of the two meeting cases exercised every `GeoBlock` field except
`start_lt`/`next_eq`/`mem_interior_iff` (used by the remote case as designed), confirming the structure is neither
under- nor over-specified for its consumers.

## 1. The chain (skeleton order; ✓ proved in Skeleton_FINAL.lean, ◻ sorried leaf with its unit)

Notation: `cCG := silentCentreCG hn g h : CrossingGeometry g.center` (= `weak_crossingGeometry (g.silent_center_weak hn h)`),
`hP := weak_crossingGeometry hW`, `Q := geoCornerPolygon hP S q`, `c_k := geoCornerMark hP S q k`,
`e_k := (geoOutSlot hP S c_k).1`, `s_k := (geoOutSlot hP S c_k).2.val`.

### §0 Silent germ data — all ✓ (B verbatim)
`WallGerm.extension_silent`, `WallGerm.pureCut_silent`; `silentCentreCG`, `silentCurveCG`, `WallGerm.sideGeneric`;
`SilentFamilyData hn g h δ : Prop` (= `0 < δ ∧ δ ≤ g.radius ∧ ∀ s, |s| < δ → ChirotopesOutsideZerosAgree ∧ WeakGeneric ∧
Injective crossingPoint ∧ (crossingPoint c ≠ vertex) ∧ CrossingParameterOrderAgrees ∧ GeometricRecordsAgree`);
`exists_silentFamilyData` (from `silent_sides`, SilentSides.lean:26); accessors `crossing_iff`, `side_crossing_iff`,
`marks` (`geoMarkList_map_transport`), `interlaces_iff`, `crossingSign_eq`, `turn_eq` (turn support ∉ `Z_pt`);
`exists_silent_sideParameter_lt`.

### §1 Mark points, the path, the corner family — all ✓ (B verbatim)
`silentMarkPoint g s : Mark g.center → Plane`; `visit_point_eq_edgePoint_of_geometry`; `silentMarkPoint_zero`,
`silentMarkPoint_eq`, `continuousAt_silentMarkPoint`; `silentPath g t u := ⟨(2u−1)t, _⟩` with `_zero`, `_one`,
`continuous_`, `abs_…_le`, `_eq_zeroParameter`; `silentCornerFamily hn g h S q s : LabelledTuple (geoCornerCount cCG S q)`;
`silentCornerFamily_zero`; `geoCornerMark_markTransport`; **`silentCornerFamily_eq`** (family at any interval parameter
= `recastTuple _ (geoCornerPolygon (sCG s) (transportSupport hc S) (geoOwner … (markTransport hc a)))`);
`continuous_silentCornerFamily_path`.

### §2 General geo-transport lemmas — all ✓ (B verbatim)
`geoCarrierCrossings_markTransport`, `card_geoCarrierCrossings_markTransport`, `geoIndependent_transport_iff`,
`geoOwner_twin_ne_transport_iff`.

### §3 Centre genericity (variables `P`; the section's two ◻ are the whole open work)
| declaration | statement | status |
|---|---|---|
| `regular_of_weakGeneric (hW) : Regular P` | | ✓ |
| `crossing_edges_det_ne_zero_of_geometry (hP) (c) (hi : i ∈ c.val) (hj) (hij : i ≠ j) : det (edge P i) (edge P j) ≠ 0` | | ✓ |
| `vertex_injective_of_weakGeneric (hW) : Injective P` | | ✓ |
| `self_not_mem_edgeInterior (he : edge Q a ≠ 0) : Q a ∉ edgeInterior Q a`; `next_not_mem_edgeInterior … : Q (a+1) ∉ edgeInterior Q a` | judge | ✓ |
| `isTrueCorner_selectedMarkPerm (hm : IsTrueCorner S m) : IsTrueCorner S (selectedMarkPerm S m)` | judge | ✓ |
| `geoCornerPolygon_regular_of_weak (hn) (hW) (S) (q) (htr : TracedSuccessor hP S q) : Regular Q` | | ✓ |
| `geoCornerPolygon_injective_of_weak (hW) (hinj) (hnv) (S) (q) (htwin) : Injective Q` | judge | ✓ |
| `structure GeoBlock (hP) (S) (q) (k) (t : ℝ) : Prop` — fields `start_lt : s_k < t`, `le_one : t ≤ 1`, `corner_eq : Q k = edgePoint P e_k s_k`, `next_eq : Q (k+1) = edgePoint P e_k t`, `mem_segment_iff : ∀ u, edgePoint P e_k u ∈ edgeSegment Q k ↔ s_k ≤ u ∧ u ≤ t`, `mem_interior_iff : … ↔ s_k < u ∧ u < t`, `exists_param : ∀ x ∈ edgeSegment Q k, ∃ u, x = edgePoint P e_k u`, `interior_mark : ∀ m, (pos m).1 = e_k → s_k < (pos m).2 → (pos m).2 < t → ¬ IsTrueCorner S m`, `start_mark : ∀ m, (pos m).1 = e_k → (pos m).2 = s_k → m = selectedMarkPerm S c_k`, `end_mark : ∀ m, (pos m).1 = e_k → (pos m).2 = t → m = c_{k+1}`, `end_vertex : t = 1 → c_{k+1} = inl (e_k + 1)` (`pos := geoMarkPosition hP`) | | def |
| **`exists_geoBlock (hn) (hP : CrossingGeometry P) (S) (q) (htr : TracedSuccessor hP S q) (k) : ∃ t, GeoBlock hP S q k t`** | | **◻ U3a** |
| `geoCornerPolygon_meet_same_edge_aux (hP) (S) (q) (htwin) (hab : a ≠ b) (ha : GeoBlock … a ta) (hb : GeoBlock … b tb) (he : e_a = e_b) (hle : s_a ≤ s_b) (hxa : x ∈ edgeSegment Q a) (hxb) : b = a + 1 ∧ x = Q b` | judge | ✓ |
| `geoCornerPolygon_meet_same_edge … (he : e_a = e_b) … : (b = a+1 ∧ x = Q b) ∨ (a = b+1 ∧ x = Q a)` | judge | ✓ |
| `geoCornerPolygon_meet_next_edge (hP) (hreg : Regular P) (S) (q) (ha) (hb) (he : e_b = e_a + 1) (hxa) (hxb) : b = a + 1 ∧ x = Q b` | judge | ✓ |
| **`geoCornerPolygon_meet_remote_edge (hP) (hnv) (S) (q) (htwin) (ha) (hb) (he : remote e_a e_b) (hxa) (hxb) : (b = a+1 ∧ x = Q b) ∨ (a = b+1 ∧ x = Q a) ∨ ∃ c, c ∉ S ∧ x = crossingPoint c ∧ e_a ∈ c.val ∧ e_b ∈ c.val ∧ e_a ≠ e_b ∧ x ∈ edgeInterior Q a ∧ x ∈ edgeInterior Q b`** | | **◻ U3b** |
| `geoCornerPolygon_meet_of_weak (hn) (hW) (_hinj) (hnv) (S) (q) (htr) (htwin) (hab : a ≠ b) (hxa) (hxb) : (same three-way disjunction, on hP := weak_crossingGeometry hW)` | judge (assembly) | ✓ |
| `geoCornerPolygon_tail_off_of_weak … (hab : ¬ incident a b) : Q a ∉ edgeSegment Q b` | judge | ✓ |
| `geoCornerPolygon_transverse_of_weak … (hab : ¬ adjacent a b) (hmeet : (edgeSegment Q a ∩ edgeSegment Q b).Nonempty) : det (edge Q a) (edge Q b) ≠ 0` | judge | ✓ |
| `geoCornerPolygon_no_triple_of_weak … : ¬ ∃ a b c, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ (edgeInterior Q a ∩ edgeInterior Q b ∩ edgeInterior Q c).Nonempty` | judge | ✓ |
| `single_generic_of_weak … (hk : 3 ≤ geoCornerCount hP S q) : (Shadow.single ⟨_, hk, Q⟩).Generic` | `Shadow.single_generic_of` | ✓ |

### §4 The silent germ at one side parameter — all ✓ (B verbatim)
`side_marks`, `isDecomposition_iff`, `side_isDecomposition_iff`, `centre_tracedSuccessor` (from the positive side,
`traced_successor_of_transport` + `geoCarrierSpec_of_generic`), `centre_twin_ne` (`independent_selected_pair_owners_ne`),
`centre_geoCornerCount_ge_three`, `centre_single_generic` (= `single_generic_of_weak` at `s = 0`), `centre_regular`,
`family_generic_side`, `family_regular_side`, `family_path_generic`, `family_path_regular`, **`homfly_family`**
(`Link.homfly_positiveDiagram_single_of_family`), **`rotationNumber_family`** (`rotationNumber_family_constant`),
`card_geoCarrierCrossings_sides`, `rotationNumber_geoCornerPolygon_sides`, `homfly_geoCornerPolygon_sides`.

### §5 The mark transport and the assembly — all ✓ (B verbatim)
`transportSupport_surjective`; `sides_crossing_iff`, `sides_crossingParameterOrderAgrees`, `sides_turn_eq`;
**`sideTransport : MarkTransport hn (g.sideGeneric true t) (g.sideGeneric false t)`**; `sideTransport_support`,
`sideTransport_toMark`; (i) `sides_markTurn_eq`, `sides_carrierUniform_iff`, `sides_huni`; (ii) `cornerCoefficient_sides`,
`sides_hcoef`; **`cornerStateSum_sides`** (= `MarkTransport.cornerStateSum_transport`).

### §6-7 Reduction and the row — all ✓
`cornerStateSum_silent_side_const` (prop:C-chamber along a side), `cornerStateSum_silent`, `CSilentData` (verbatim),
`prop_C_silent`.

## 2. Units for provers (independent; each provable from Skeleton_FINAL.lean alone)

| unit | declaration | est. lines | inputs (all accepted, file:line under work/lean/SM/) |
|---|---|---|---|
| **U3a** | `exists_geoBlock` | 250 | FlatCarriers.lean: `geoCornerPolygon_edge_data` :3253, `geo_block_compression` :3080, `geo_evaluation_eq_outSlot` :3049, `geo_incoming_visit_position` :3063, `geoOutSlot_unselected` :3026, `geoMarkSuccessor_position_cases` :2729, `geoMarkSuccessor_no_mark_between` :361, `geoCornerMark_add_one` :3170; FlatCarriersDefs.lean: `geoMarkPosition_injective` :108, `geoMarkPosition_vertex/visit` :82/:86, `geoSmoothingSuccessor_apply` :239; CarrierCornerPolygon.lean: `ccp_not_trueCorner` :123; Crossings.lean: `edgePoint_injective` :88; Traversal.lean: `traversalBetween` :73, `traversalKey_same_edge`, `traversalKey_lt_iff` :46; G1Consequences.lean: `edgePoint_one` :16; CarrierAffineSegments.lean: `edgePoint_sub_edgePoint` :56. Model: LinkPositiveLift.lean:251-435 (`BlockInterior`, `edgeSegment_param`, `block_mark_eq`, generic layer). Fallback for `interior_mark`: prove it by contradiction at the unique chain step `r` with `param(chain_r) < u < param(chain_{r+1})` using `geoMarkSuccessor_no_mark_between` once. |
| **U3b** | `geoCornerPolygon_meet_remote_edge` | 200 | `GeoBlock` fields only (no `exists_geoBlock`); Crossings.lean: `IsCrossing` :12 (`⟨e_a, e_b, rfl, he, ⟨x, _, _⟩⟩`), `crossingPoint_mem` :44, `crossingParameter_spec` :74, `edgePoint_injective` :88; CrossingGeometry.lean: `crossingPoint_unique_of_geometry` :41, `crossingParameter_interior_of_geometry` :52; GeometricVisits.lean: `geometricVisitPosition` :12; CarrierVisitTwin.lean: `visit_eq_or_twin` :47, `visitTwin_unique` :60; CarrierSmoothing.lean: `selectedMarkPerm_visit` :45, `selectedMarkPerm_involutive` :48; CarrierVisitTwin.lean: `selectedVisitTwin_of_mem/_not_mem` :83/:87; Segment.lean: `remote_endpoints` :90 (`.1.symm : e_a ≠ e_b`); FlatCarriers.lean: `geoOwner_geoCornerMark` :4895, `isTrueCorner_geoCornerMark` :4899, `geoCornerMark_injective` :4904; this skeleton: `isTrueCorner_selectedMarkPerm`, and the two proved cases as templates (`geoCornerPolygon_meet_same_edge_aux` shows the `obtain ⟨ea, hea⟩ … rw … at` generalisation pattern for the `geoOutSlot` expressions and the `c_b` case split). |

Assembly: paste U3a and U3b in place of the two `sorry`s; nothing else changes. Finished module ≈ 1900 lines
(prop:C-chamber's accepted module is 1387; the geo layer of FlatCarriers is reused, not duplicated).

Proof sketch for U3b (the judge's design, following PLAN_B §1 with the case data now explicit): generalise
`e_a, e_b, s_a, s_b` as in `_aux`; `x = edgePoint P e_a u_a = edgePoint P e_b u_b` with `s_a ≤ u_a ≤ t_a`,
`s_b ≤ u_b ≤ t_b` (so `0 ≤ u ≤ 1`); `hc : IsCrossing P {e_a, e_b}`, `c := ⟨_, hc⟩`, `x = crossingPoint c`
(`crossingPoint_unique_of_geometry`, membership of `x` on both closed parent segments); `w_a := ⟨c, ⟨e_a, _⟩⟩`,
`w_b := ⟨c, ⟨e_b, _⟩⟩`, `w_b = visitTwin w_a` (`visitTwin_unique`; `w_b ≠ w_a` as `e_a ≠ e_b`);
`(geoMarkPosition hP (inr w_a)).1 = e_a` (`rfl`) and `.2.val = u_a` (`crossingParameter_spec` + `edgePoint_injective`);
`u_a ≠ 1` (else `x = P (e_a+1)`, `hnv`), hence `u_a = t_a → t_a < 1`. Case `c ∈ S`: `interior_mark` at `inr w_a`
(a true corner) forces `u_a = s_a ∨ u_a = t_a`, and likewise for `b`; `start_mark` gives `inr w_a = selectedMarkPerm S c_a`,
i.e. `c_a = inr w_b` (`selectedMarkPerm_involutive`, `selectedMarkPerm_visit`, `selectedVisitTwin_of_mem`);
`end_mark` gives `inr w_a = c_{a+1}`; the four combinations: `(s_a, s_b)`: `c_a = inr w_b`, `c_b = inr w_a`, so
`geoOwner (inr w_a) = q = geoOwner (inr w_b)`, against `htwin w_a`; `(s_a, t_b)`: `c_a = inr w_b = c_{b+1}`, so
`a = b + 1` and `x = Q a` (`corner_eq`, `u_a = s_a`); `(t_a, s_b)`: `c_{a+1} = inr w_a = c_b`, so `b = a + 1`, `x = Q b`;
`(t_a, t_b)`: `c_{a+1} = inr w_a`, `c_{b+1} = inr w_b`, against `htwin` (`geoOwner_geoCornerMark` at `a+1`, `b+1`).
Case `c ∉ S`: `inr w_a` is not a true corner, so `u_a ≠ s_a` (`start_mark` would make it `selectedMarkPerm S c_a`,
a true corner by `isTrueCorner_selectedMarkPerm`) and `u_a ≠ t_a` (`end_mark` would make it `c_{a+1}`), hence
`s_a < u_a < t_a` and `x ∈ edgeInterior Q a` (`mem_interior_iff`); likewise `b`; `e_a ≠ e_b` by `(remote_endpoints _ _ he).1.symm`.

## 3. Lemmas closed by the judge (beyond Skeleton_B)
`self_not_mem_edgeInterior`, `next_not_mem_edgeInterior`, `isTrueCorner_selectedMarkPerm`,
`geoCornerPolygon_injective_of_weak`, `geoCornerPolygon_meet_same_edge_aux`, `geoCornerPolygon_meet_same_edge`,
`geoCornerPolygon_meet_next_edge`, `geoCornerPolygon_meet_of_weak` (assembly), `geoCornerPolygon_tail_off_of_weak`,
`geoCornerPolygon_transverse_of_weak`, `geoCornerPolygon_no_triple_of_weak` — 11 declarations, ~230 lines; B's
sorry count 6 → 2.

## 4. Fidelity to the printed proof, and risks

* "By lem:wall-sides (E),(C) the remote crossings and their cyclic visit order agree on both sides and at the
  centre … the same finite crossing records and independent supports are identified through the entire small
  interval" → `SilentFamilyData` at every `|s| < δ`, `isDecomposition_iff`, `sideTransport`.
* "exchange the same successors to identify its carriers … every carrier tuple is continuous, has nonzero
  segments, and has no antiparallel corner … They do not apply a generic-polygon lemma outside its hypothesis"
  → `centre_tracedSuccessor` (transported successors), `continuous_silentCornerFamily_path`,
  `geoCornerPolygon_regular_of_weak` (from `WeakGeneric`/`CrossingGeometry` only). §3 additionally proves
  genericity of the centre carrier polygon as a one-component *shadow* (tail-off, transversality, no triple
  point) — from the printed centre facts "vertices are distinct, … no vertex lies on a nonincident closed edge,
  every actual crossing is transverse and interior, and distinct crossings have distinct points" (`hnv`, `hinj`,
  `CrossingGeometry`, `WeakGeneric.2.2.1`) — which the printed proof does not state explicitly; it is what
  lit:homfly's planar clause needs and it is proved without any generic-parent lemma. **Fidelity risk 1 (accepted
  deviation):** the `H⁺` equality is obtained by lit:homfly's planar clause along the family instead of
  lc:presentations + lp:core on the two sides (lines 137-141); this is the same substitution as in the accepted
  prop:C-chamber and thm:C-S3, and it removes the dependence on SM/PolynomialBlock (`SM.lp_lm`,
  `SM.lp_lm_uniqueness`).
* "lem:rot (ii) … each carrier's signed rotation is the same on both sides" → `rotationNumber_family`;
  "every original and smoothing turn sign is constant" → `sides_markTurn_eq`; "all `m_Q`" →
  `card_geoCarrierCrossings_sides`; "its positive over/under designation is also constant" → absorbed in
  `positiveDiagram` along the family (the lifts are positive at every time inside
  `homfly_positiveDiagram_single_of_family`).
* "the state sums are evaluated on the generic sides; prop:C-chamber makes them independent of the chosen
  representatives" → `cornerStateSum` is applied only to `g.sideGeneric b t` / `(g.sideTuple b t).property`;
  `cornerStateSum_silent_side_const`, `cornerStateSum_silent`.
* **Risk 2:** `interior_mark` of `exists_geoBlock` (the `traversalBetween` bookkeeping when the block ends at the
  vertex `e+1`, whose key may wrap). Fallback in §2. **Risk 3:** the remote case's four-way endpoint analysis is
  long but mechanical; the two proved cases are its templates. **Risk 4 (none at statement level):** the bundle and
  header are byte-identical to the statement file and `prop_C_silent` is closed; the axiom set is the accepted one.
* Statement-side note (both plans, kept): all side statements are written on `g.curve (g.sideTime b t)` and
  `generic_crossingGeometry hn (g.sideGeneric b t)` rather than `(g.sideTuple b t).val` so that instance search
  (`NeZero (geoCornerCount …)`) never has to unfold `sideTuple`; the bridge to `(g.sideTuple b t).property` is by
  defeq in `cornerStateSum_silent`.

## 5. Verification
```
cd work/lean && lake env lean ../drafts/csilent/Skeleton_FINAL.lean
#   → 0 errors; warnings: exactly two "declaration uses 'sorry'" (exists_geoBlock, geoCornerPolygon_meet_remote_edge)
#   → last line: 'SM.prop_C_silent' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, SM.lit_homfly]
python3 - <<'PY'   # bundle / header byte-identity against the fixed statement
s=open('work/drafts/CSilent_statement.lean').read(); f=open('work/drafts/csilent/Skeleton_FINAL.lean').read()
i=s.index('/-- prop:C-silent as printed'); j=s.index('theorem prop_C_silent : CSilentData := by')
print(s[i:j] in f, 'theorem prop_C_silent : CSilentData := by' in f)
PY
```
