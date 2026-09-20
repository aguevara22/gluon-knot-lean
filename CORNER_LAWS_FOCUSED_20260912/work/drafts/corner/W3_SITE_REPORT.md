# W3_SITE_REPORT — unit S7-SITE (I-110; prefix `s7s_`; corner wave 3, audit A-110-1), 2026-09-15 21:55Z

File: `work/drafts/corner/W3_SITE.lean` = `W3_Skeleton.lean` (97 lines) + ONE inserted block (lines 37-1105, 1069 lines),
placed inside `section VertexEdge` immediately BEFORE the docstring of `s7_bigon_law_at` (the leaf this unit serves).
`diff W3_Skeleton.lean W3_SITE.lean` = `36a37,1105`: pure insertion, **0 deleted lines**; the five frozen declarations
(`s7_sliding_law_at`, `s7_bigon_law_at`, `thm_C_S7_of`, `thm_C_S7_of_floor`, `thm_C_S7`) are byte-identical; both leaf
bodies still `sorry` (this unit does NOT close the leaf; it delivers bigon (2) of PLAN_FINAL §3.3 — the I-110 site and
the value identity — and reduces the record identification `hrec` to its unswitched form).
Check: `cd work/lean && lake env lean ../drafts/corner/W3_SITE.lean` — **0 errors, 0 non-sorry warnings**, exactly
**4** `declaration uses sorry`: line 26 (`s7_sliding_law_at`, frozen), 1050 (`s7s_clear_local`, black box, §2.1),
1096 (`s7s_wallTriangleData_of_bigon`, black box, §2.2), 1114 (`s7_bigon_law_at`, frozen). 15-22 s warm.
`grep -c sorry`: **5** (the 4 bodies at lines 34, 1059, 1101, 1123 + the skeleton's header prose at line 4).
Nothing under `work/lean` was written; probes only in the session scratchpad. **No import added** (everything used is
reachable from the skeleton's four imports; the G11 toolkit `RProof.GenericTransport` comes through `SM.BigonDeletion`,
`SM.FlatCarriers` / `SM.GeoPositiveLift` through `SM.CornerChainUnits`).
Axioms (`#print axioms` on a scratch copy): `s7s_core`, `s7s_site`, `s7s_contact_sign`, `s7s_rii_witnesses`,
`s7s_hrec_of_unswitched`, `s7s_hrec_prop_of_unswitched`, `s7s_restrictCrossings_switch_deleted`,
`s7s_liftGen_eq_carrierCrossingEquiv`, `s7s_geoPositiveLift_eq`, `s7s_cornerMark_of_wall`, `s7s_cornerPolygon_of_wall`,
`s7s_markSuccessor_vertex_first`, `s7s_jout_of_wall` = `[propext, Classical.choice, Quot.sound]`;
`s7s_switch_value`, `s7s_switch_value_positiveLift` `+ SM.lp_lm` (through `s7g_switch_value_of_rii` =
`P_reidemeister_II` + `presentations`); `s7s_cornerHomfly_skein` `+ SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness`
(through `s7g_cornerHomfly_skein`) — the policy set; `s7s_carrier_data_of_wall`, `s7s_siteData_of_wall` carry `sorryAx`
(through the black box `s7s_clear_local`), as intended.
Reassessment rule: not triggered — no lemma took two failed attempts; the seven compile rounds each fixed one
elaboration issue (three were the implicit-transparency `rw` motive failure, Site_176_REPORT §6 item 1; one
`include hS in`; one `haveI` linter; one syntactic `Sum.inl ((pos).1 + 1)` vs `Sum.inl (M + 1)`).

## 0. What the unit delivers, in one paragraph

**I-110 is built and its wall inputs are almost all discharged.** On the positive lift `D_H = geoPositiveLift hn hG hS q`
of a carrier `q` of an independent support `S` of the bigon-side polygon `P` that RETAINS the two contact crossings
`x = x_{M−1,a}`, `y = x_{a,M}` (the "full contact carrier" through the vertex `M`), the switch of `D_H` at (the lift
of) `x` carries a `BigonData` whose bigon is `{x, y}` and whose region is the closed contact triangle
`K = conv{x, P M, y}` — `s7s_core` / `s7s_site`, through the ported `exists_bigonData_of_triangle`, following
`s174_core` (work/drafts/moves/Site_174.lean) with the corner at a polygon VERTEX instead of a selected crossing. The
wall data enter in CARRIER form as the five fields of `s7s_SiteData` (`jout`, `corner`, `adj_s`, `sgn`, `clear`):
`sgn` is PROVED from planar geometry alone (`s7s_contact_sign`), `corner` and `jout` are PROVED from the `P`-level window
clauses (2), (3) by the block/mark-successor argument (`s7s_cornerPolygon_of_wall`, `s7s_jout_of_wall`), `adj_s` is
window clause (4) verbatim, and `clear` is PROVED for every carrier edge on a non-local `P`-edge, leaving as this unit's
black box only the clearance of the carrier edges on the three local edges `M−1, M, a` (`s7s_clear_local`, §2.1). The
`P`-level wall data themselves (`s7s_WallTriangleData`: (1) the closed triangle clear of the other edges, (2)-(4) the
window clauses) are the second black box, U110-A/B content (`s7s_wallTriangleData_of_bigon`, §2.2). From the site and
the record identification `hrec` (STATED as `s7s_hrec_prop`) the two hypotheses of the accepted glue
`s7g_switch_value_of_rii` are PROVED (`s7s_rii_witnesses`), hence `P (D_H.switch x) = P D_L` (`s7s_switch_value`),
transported to the accepted `positiveLift` / `cornerHomfly` (`s7s_switch_value_positiveLift`, `s7s_cornerHomfly_skein`:
`H⁺_Q = a⁻² P(D_L) + a⁻¹ z P(D_A)`, the input of U110-H/K). Finally `hrec` is REDUCED to the UNSWITCHED identification
`D_H.record − {x, y} ≅ D_L.record` (`s7s_hrec_of_unswitched`, `s7s_hrec_prop_of_unswitched`): the switch sits on the
DELETED crossing `x`, so the record side is exactly U110-A's persistent-visit transport, with no switch bookkeeping.

## 1. PROVED (all `s7s_`; inside `section VertexEdge` → nested `section S7Site`, `open GeoCarrier RProof`)

### 1.1 Generic helpers (s7s.1, lines 61-163) — standard axioms
`s7s_pos_over_iff` (64), `s7s_switch_over_self_iff` (91), `s7s_over_other_iff` (105), `s7s_pos_iff_of_sign_eq` (116),
`s7s_neg_pos_iff_of_sign_eq` (121), `s7s_not_pos_iff` (126), `s7s_det_smul_pos_iff` (131), `s7s_adjacent_zmod3` (137),
`s7s_four_le` (148), `s7s_strand_ne_of_not_adjacent` (157) — the site-174 helpers re-proved under this prefix (they live
in a draft, not the library).

### 1.2 The lifted crossings of a carrier (s7s.2, lines 167-255)
`s7s_lift hn hG hS q c hc : (geoCarrierShadow hn hG hS q).Crossing` (173; `geoCarrierCrossingEquiv.symm`),
`s7s_lift_crossingPoint` (177), `s7s_lift_injective_pt` (183), **`s7s_lift_val`** (193: the strands of the lifted crossing
are the two carrier edges `G11_carrierEdge` of the visits of `c`), `s7s_four_le_cornerCount` (223),
`s7s_det_ne_zero_of_isCrossing` (230), **`s7s_pos_over_lift_iff`** (238: the over strand of the positive lift at a lifted
crossing is decided by the sign of `det` of the two original edges).

### 1.3 The wall bigon site — `s7s_core` (s7s.3, lines 257-437) — standard axioms
```
theorem s7s_core (hn : 3 ≤ n) (hG : CarrierGeometry P) (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
    (hx : IsCrossing P {M - 1, a}) (hy : IsCrossing P {a, M})
    (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q) (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q)
    (hjout : G11_carrierEdge … (G11_vgf hy) hyq = G11_carrierEdge … (G11_vef hx) hxq + 1)
    (hcorner : geoCornerPolygon hG.cg S q (G11_carrierEdge … (G11_vef hx) hxq + 1) = P M)
    (hadj_s : ∀ w : Visit P, w.2.val = a → ¬ (x_a < w < y_a) ∧ ¬ (y_a < w < x_a))      -- visit parameters on `a`
    (hsgn : crossingSign P (M - 1) a = crossingSign P a M)
    (hclear : ∀ h : ZMod (geoCornerCount hG.cg S q), h ≠ j_in → h ≠ j_in + 1 → h ≠ j_s →
      Disjoint (edgeSegment (geoCornerPolygon hG.cg S q) h) (s7s_K hx hy))
    (xs) (hxs : xs = s7s_lift … (xPair hx) hxq ∨ xs = s7s_lift … (xPair hy) hyq) :
    ∃ B : BigonData ((geoPositiveLift hn hG hS q).switch xs),
      B.i = ⟨0, Nat.one_pos⟩ ∧ B.y = s7s_lift … (xPair hx) hxq ∧ B.z = s7s_lift … (xPair hy) hyq
```
`s7s_K hx hy := convexHull ℝ {crossingPoint (xPair hx), P M, crossingPoint (xPair hy)}` (263; the closed contact
triangle, sm-4:618-620). Visits: `G11_vef hx` = `x` on `M−1`, `G11_vfe hx` = `x` on `a`, `G11_vfg hy` = `y` on `a`,
`G11_vgf hy` = `y` on `M`; `j_in := G11_carrierEdge (G11_vef hx)`, `j_s := G11_carrierEdge (G11_vfe hx)`.
How the five inputs of the frozen leaf `exists_bigonData_of_triangle` are discharged:

| leaf input | discharge |
|---|---|
| `hk : 4 ≤ k` | `s7s_four_le_cornerCount` (a retained crossing has non-adjacent carrier edges, `gu1_carrierEdge_remote`) |
| `hy : y.val = {⟨0, j_in⟩, ⟨0, j_s⟩}` | `s7s_lift_val` at `G11_vef hx` + `gu2_visitTwin_vef` |
| `hz : z.val = {⟨0, j_in + 1⟩, ⟨0, j_s⟩}` | `s7s_lift_val` at `G11_vgf hy`; twin by `SEL_visitTwin_visitOn`; the `a`-edges agree by `G11_carrierEdge_eq_of_adjacent` from `hadj_s` (derived inside the core); the `M`-edge is `j_in + 1` by `hjout` |
| `same_over` | `s7s_pos_over_lift_iff` at both crossings, `s7s_switch_over_self_iff` / `s7s_over_other_iff` / `Diagram.switch_overStrand_of_ne`, and `hsgn` through `s7s_pos_iff_of_sign_eq` / `s7s_neg_pos_iff_of_sign_eq`; both switch positions handled |
| `clear` (CLOSED `K`) | `hclear` read on strands (`Subsingleton.elim` on the component index); `K` rewritten by `s7s_lift_crossingPoint` ×2 + `hcorner` |

`x ≠ y` inside the core: `M − 1 ∈ {a, M}` is impossible (`P1.ne_of_isCrossing_pair`; `(1 : ZMod n) ≠ 0` from
`ZMod.one_eq_zero_iff` + `3 ≤ n`).

### 1.4 Bundled data, R-II witnesses, the value identity (s7s.4, lines 441-522)
* `s7s_reducedRecordOf D y₀ z₀` (449), `s7s_reducedRecord_eq` (454: `B.reducedRecord = s7s_reducedRecordOf D B.y B.z`).
* `structure s7s_SiteData hn hG hS q hx hy hxq hyq : Prop` (465) with fields `jout corner adj_s sgn clear`.
* `s7s_site (W : s7s_SiteData …) : ∃ B : BigonData (D_H.switch (lift x)), …` (478; switch at `x`, the PLAN's choice).
* `def s7s_hrec_prop … (DL : Diagram) : Prop := Nonempty (RecordIso (s7s_reducedRecordOf (D_H.switch (lift x)) (lift x) (lift y)) DL.record)` (493) — STATED (§3).
* **`s7s_rii_witnesses (W) (DL) (hrec : s7s_hrec_prop …) : ∃ Dred, RII Dred (D_H.switch (lift x)) ∧ Nonempty (RecordIso Dred.record DL.record)`** (503) — exactly `hR`, `hrec` of `s7g_switch_value_of_rii` (via `s7_rii_witnesses`, SM.BigonDeletion).
* **`s7s_switch_value (W) (DL) (hrec) : SM.P (D_H.switch (lift x)) = SM.P DL`** (515) — sm-4:600-606 (`+ lp_lm`).

### 1.5 Transport to the accepted `positiveLift` (s7s.5, lines 524-612)
`s7s_castCrossing` (532), `s7s_switch_castCrossing` (536), `s7s_castCrossing_crossingPoint` (541);
`s7s_cg hn hP := CarrierGeometry.ofGeneric hn hP` (549), `s7s_geoIndependent` (553; `geoIndependent_iff_isDecomposition`),
`s7s_geoComp hn hP S q := (geoComponentEquivGeneric hn hP S).symm q` (557),
**`s7s_geoPositiveLift_eq : geoPositiveLift hn (s7s_cg hn hP) _ (s7s_geoComp hn hP S q) = positiveLift hn hP S q hS`** (560);
`s7s_liftGen hn hP S hS q c hc : (positiveLift hn hP S q hS).Γ.Crossing` (569), `s7s_liftGen_crossingPoint` (575);
**`s7s_switch_value_positiveLift : SM.P ((positiveLift hn hP S q hS).switch (s7s_liftGen … (xPair hx) hxq)) = SM.P DL`** (583);
**`s7s_cornerHomfly_skein … (v) (hv : v.1 = s7s_liftGen …) : ∃ D₀, IsOrientedSmoothing (positiveLift …) (lift x) D₀ ∧
Nonempty (RecordIso D₀.record ((positiveLift …).record.smooth v)) ∧ cornerHomfly hn hP S q hS = R.aInv * R.aInv * SM.P DL
+ R.aInv * R.z * SM.P D₀`** (598) — eq. s7c:universal-skein with the R-II step done: the input of U110-H/K.

### 1.6 Record side and the `carrierCrossings` reading (s7s.7, lines 614-684)
* **`s7s_restrictCrossings_switch_deleted (ρ) (S) (v) (hv : ¬ ρ.CrossKeep S v) : Nonempty (RecordIso ((ρ.switch v).restrictCrossings S) (ρ.restrictCrossings S))`** (654) — the DELETED-case companion of the library's `Record.restrictCrossings_switch` (Site_174_REPORT §3 item 1, estimated there at 80-150 lines; 40 here).
* `s7s_mem_geoCarrierCrossings_iff` (665: `c ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q) ↔ c ∈ carrierCrossings hn hP S q`);
  `s7s_liftGen_eq_carrierCrossingEquiv` (673: `s7s_liftGen … c hc = (carrierCrossingEquiv hn hP S q hS).symm ⟨c, _⟩`) — U110-K can name the switched crossing in the accepted vocabulary.

### 1.7 `hrec` reduced to the UNSWITCHED record (s7s.8, lines 686-760) — standard axioms
`s7s_keepOf D y₀ z₀ : Set D.record.Crossing` (694), `s7s_crossingOf_eq_iff_fst` (699; U-M6's `key`),
**`s7s_hrec_of_unswitched (D) (x y) (v) (hv : v.1 = x) (DL) : Nonempty (RecordIso (D.record.restrictCrossings (s7s_keepOf D x y)) DL.record) → Nonempty (RecordIso (s7s_reducedRecordOf (D.switch x) x y) DL.record)`** (713)
(`Diagram.switchRecordIso` is the identity on occurrences — `rfl`, probed; `CB.restrictCrossings_iso_of_recordIso`; then the deleted-case lemma),
**`s7s_hrec_prop_of_unswitched : Nonempty (RecordIso (D_H.record.restrictCrossings (s7s_keepOf D_H (lift x) (lift y))) DL.record) → s7s_hrec_prop …`** (750).

### 1.8 The `corner` and `jout` fields from the window clauses (s7s.9, lines 762-962) — standard axioms
* `s7s_visit_ext` (774: a visit is determined by crossing and edge), `s7s_smoothingSuccessor_of_not_mem` (784: the smoothing
  successor of an unselected visit is its mark successor), **`s7s_markSuccessor_last`** (791: the mark successor of the LAST
  visit on its edge is the next vertex — `geoMarkSuccessor_position_cases`, the same-edge alternative excluded).
* **`s7s_cornerMark_of_wall (h2 : window clause (2)) (hxq) : geoCornerMark hG.cg S q (j_in + 1) = Sum.inl M`** (821): `x`'s
  leg visit is the `r`-th mark of block `j_in` (`gu1_carrierEdge_block`); block `j_in` ends at corner `j_in + 1` after `m`
  steps (`geoCornerPolygon_block`); the smoothing successor of the leg visit is the vertex `inl M` (unselected + last on
  `M−1`); a vertex is a true corner, so `r + 1 = m`. **`s7s_cornerPolygon_of_wall : geoCornerPolygon (j_in + 1) = P M`** (857).
* **`s7s_markSuccessor_vertex_first (h3 : window clause (3)) : geoMarkSuccessor hG.cg (Sum.inl M) = Sum.inr (G11_vgf hy)`**
  (867): by `position_cases` the successor is a visit `u` on `M` with parameter `> 0` or the vertex `M+1`; if not `y`'s
  visit `w`, then `w` (parameter in `(0,1)`, `< param u` by (3)) lies strictly between `inl M` and the successor
  (`traversalBetween_of_key_lt`; key arithmetic incl. the wrap `(M+1).val = 0` via `ZMod.val_add`, `ZMod.val_one`) —
  against `geoMarkSuccessor_no_mark_between`.
* **`s7s_jout_of_wall (h2) (h3) (hxq) (hyq) : G11_carrierEdge (G11_vgf hy) hyq = G11_carrierEdge (G11_vef hx) hxq + 1`**
  (938): `GeoBlockInterior (j_in + 1) 1` from the two lemmas above; `geo_block_mark_eq` against `gu1_carrierEdge_block`
  at `y`'s `M`-visit.

### 1.9 The contact sign condition and the assembly (s7s.10, lines 964-1087)
* `s7s_WallTriangleData P M a hx hy : Prop` (975): (1) every edge other than `M−1, M, a` misses the closed triangle `K`;
  (2) `x`'s visit is the LAST on `M−1`; (3) `y`'s visit is the FIRST on `M`; (4) no visit strictly between the contact visits on `a`.
* **`s7s_contact_sign (hP : CrossingGeometry P) (hx) (hy) : crossingSign P (M - 1) a = crossingSign P a M`** (994) — PROVED
  from planar geometry, no wall data: `det(E_a, P M − x) = det(E_a, P M − y)` (`x, y` on the line of `a`), i.e.
  `(1 − t_x) det(E_a, E_{M−1}) = −t_y det(E_a, E_M)` with `0 < 1 − t_x`, `0 < t_y` (`crossingParameter_interior_of_geometry`);
  `sign_mul`, `sign_pos`. (`same_over` of the site is exactly this fact.)
* `s7s_carrier_data_of_wall (hW) (hxq) (hyq) : clear` (1063) — PROVED for carrier edges whose out-slot `P`-edge is not
  `M−1, M, a` (`gu2_edgeSegment_sub` + (1)); the local edges are the black box `s7s_clear_local` (§2.1).
* **`s7s_siteData_of_wall (hW : s7s_WallTriangleData P M a hx hy) (hxq hyq) : s7s_SiteData hn hG hS q hx hy hxq hyq`**
  (1077) — `⟨s7s_jout_of_wall, s7s_cornerPolygon_of_wall, hW.2.2.2, s7s_contact_sign, s7s_carrier_data_of_wall⟩`.

## 2. NOT proved — the two black boxes (`sorry`; what this unit consumes)

### 2.1 `s7s_clear_local` (line 1050; THIS UNIT's own remaining content)
```
theorem s7s_clear_local (hW : s7s_WallTriangleData P M a hx hy) (hxq) (hyq) (h : ZMod (geoCornerCount hG.cg S q))
    (h1 : h ≠ j_in) (h2 : h ≠ j_in + 1) (h3 : h ≠ j_s)
    (he : outSlotEdge h = M - 1 ∨ outSlotEdge h = M ∨ outSlotEdge h = a) :
    Disjoint (edgeSegment (geoCornerPolygon hG.cg S q) h) (s7s_K hx hy)
```
(`outSlotEdge h := (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1`, the `P`-edge carrying the carrier edge `h`.)
Route, per edge: a point of the carrier edge `h` in `K` lies on the `P`-edge (`gu2_edgeSegment_sub`) and on a side line
of the triangle, hence on that side (`RProof.gu2_mem_segment_ab_of_line` and the `um7_edgePt_*` chord lemmas of
SM.BigonDeletion, as in `exists_bigonData_of_triangle`), i.e. at a parameter in `[t_x, 1]` (edge `M−1`), `[0, t_y]` (edge
`M`), between `r_x, r_y` (edge `a`). The block `h = [c_h, c_{h+1}]` (`geoCornerPolygon_block`: a positive multiple of
`edge P e`, incoming edge `e` at `c_{h+1}`) has true-corner ends that are SELECTED visits on `e` — a vertex end would
force `h = j_in` (end `inl M`: `geoCornerMark_injective` + `s7s_cornerMark_of_wall`) or `h = j_in + 1` (start `inl M`) —
whose parameters window clause (2) puts below `t_x` (edge `M−1`) / (3) above `t_y` (edge `M`), so the whole block is
outside the local parameter range; on edge `a` the block's parameter range cannot straddle `(r_x, r_y)` without a mark
strictly between the two contact visits (4) or containing both (then the contact visits are marks of block `h`, so
`h = j_s` by `geo_block_mark_eq`). Estimate **300-450 lines** (edges `M−1`, `M`: 80-120 each; edge `a`: 150-200).

### 2.2 `s7s_wallTriangleData_of_bigon` (line 1096; U110-A/B content)
```
theorem s7s_wallTriangleData_of_bigon (hn) (g : WallGerm n) (M a) (h : g.BigonAt M a) :
    ∃ δ > 0, ∀ (b : Bool) (t : g.SideParameter), t.val < δ →
      ∀ (hx : IsCrossing (g.sideTuple b t).1 {M - 1, a}) (hy : IsCrossing (g.sideTuple b t).1 {a, M}),
        s7s_WallTriangleData (g.sideTuple b t).1 M a hx hy
```
(on the side whose polygon carries BOTH contact crossings — the `H` side of `VertexCrossingData`.) Content: (2)-(4) are
the window clauses `VertexLocalData.visit_windows` / `InContactVisitWindow` of the accepted `vertex_sides`
(`s7a_exists_sideLocal`, U_S7A_REPORT §1.7), read at the contact visits (`ContactParameterWindows`: the contact visits
within `η` of `r` / of the vertex, every persistent visit further than `3η`); (1) is the printed emptiness
sm-4:618-620 — the closed triangle shrinks to the point `P M`-on-`a` as `t → 0` while every other edge stays at positive
distance (`contact_persistent_parameters_approach`, ContactWindows.lean; U_S7B_REPORT §2 item 1(iii) notes it is an `∀ᶠ`
statement not yet a field of `VertexLocalData`). Estimate **300-500 lines** on the accepted `vertex_sides`.

Nothing believed false. The frozen statement of `s7_bigon_law_at` needs no change for this unit's content.

## 3. `hrec` — STATED (`s7s_hrec_prop`), REDUCED to the unswitched identification; cost

What remains is exactly `Nonempty (RecordIso (D_H.record.restrictCrossings (s7s_keepOf D_H (lift x) (lift y))) D_L.record)`
(`s7s_hrec_prop_of_unswitched`): the record of the full contact carrier's lift with the four occurrences of `x, y`
deleted is the record of the `L`-side lift `D_L = positiveLift hn hP' S' (e q) hS'` (U110-A's `s7a_sideComponentEquiv`).
Route (G11 Unit-F / Site_174 §3 pattern; the switch step is now FREE):
1. Crossing correspondence: `c ∈ geoCarrierCrossings q ∧ c ≠ x, y ↔ s7a_cross hs c ∈ geoCarrierCrossings (e q)` —
   `s7a_mem_carrierCrossings` (persistent crossings; U_S7A §1.6) read through `geoCarrierCrossings_eq_generic`
   (`s7s_mem_geoCarrierCrossings_iff`); 200-350 lines.
2. Cyclic order of the retained visits: the visit order of a positive lift is the inherited mark order on the carrier;
   after deleting the contact occurrences no contact mark remains among the record visits, and the persistent order is
   carried by `VertexLocalData.visit_order` / `s7a_between_map`; 300-500 lines.
3. Over bits and signs: both lifts positive; the over strand at `c` is decided by `sign det` of the two visited edges
   (`s7s_pos_over_lift_iff`), carried by `s7a_side_sgn` + `s7d_positiveOverBit_eq_of_crossingSign`; 100 lines.
4. Assembly against `restrictCrossings` (successor = `firstReturn`; `RecordIso.ofOcc` / `firstReturn_no_between` pattern
   of U-M6, or `CV.recordIsoOfData` on a one-circle record); 400-700 lines — the risk item.
Total **1,000-1,650 lines**.

## 4. Remaining estimate for the bigon leaf, as seen from this unit
| item | owner | lines |
|---|---|---|
| `s7s_clear_local` (§2.1) | S7-SITE | 300-450 |
| `s7s_wallTriangleData_of_bigon` (§2.2) | U110-A/B | 300-500 |
| `hrec` unswitched (§3) | U110-A (+ K assembly) | 1,000-1,650 |
| `D_A` two-component row, curl `BlockSupply`, U110-J floor branches, `B = (1−ε)J`, rotation ledger, K assembly | S7-BLOCK / S7-K | per WAVE1/PLAN (not re-estimated here) |
Everything in this file that is not one of the two black boxes is proved with the policy axiom set.

## 5. How U110-K consumes this unit
1. On the `H` side `P := (g.sideTuple b t).1`, `hP := (g.sideTuple b t).2`, a support `S` with `x, y ∉ S` both retained
   by the carrier `q` (`hxq hyq` via `s7s_mem_geoCarrierCrossings_iff` from `carrierCrossings`).
2. `hW := s7s_wallTriangleData_of_bigon … hx hy` (black box 2.2);
   `W := s7s_siteData_of_wall hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) hx hy hW hxq hyq`.
3. `hrec` from U110-A's transport via `s7s_hrec_prop_of_unswitched`.
4. `s7s_cornerHomfly_skein hn hP S hS q hx hy hxq hyq W D_L hrec v hv` gives `H⁺_Q = a⁻² P(D_L) + a⁻¹ z P(D_A)` with
   `D_A`'s record `D_H.record.smooth v`; then `s7h_extraction_two_component` / `two_component_row_of_recordIso` on `D_A`
   (the curl `y` accounted as a self crossing of writhe +1, WAVE1 §7 — no `RIData`). The switched crossing is
   `s7s_liftGen … (xPair hx) hxq = (carrierCrossingEquiv …).symm ⟨xPair hx, _⟩` (`s7s_liftGen_eq_carrierCrossingEquiv`).

## 6. Pitfalls met (v4.34.0-rc2; for the K / BLOCK provers)
1. `rw` with a lemma stated on `(positiveLift …).Γ.crossingPoint`, `Diagram.switch ?D (s7s_castCrossing …)`, or
   `(D.switch x).record.crossingOf w = … ((D.switch x).overVisit x)` against a goal whose term has a defeq-but-different
   type (`(carrierShadow …).Crossing`, `(geoCarrierShadow …).Crossing`, `x : D.Γ.Crossing` vs `(D.switch x).Γ.Crossing`)
   fails with "motive is not type correct at implicit transparency": use `exact (lemma …).trans …`, `congrArg SM.P (…)`,
   `and_congr (not_congr (….trans ….symm)) …` (three compile rounds).
2. A section `variable (hS : IsDecomposition hn hP S)` not mentioned in a statement is not included: `include hS in`
   (else "Unknown identifier" in the proof and downstream "expected `Crossing P`" mismatches at call sites).
3. `Diagram.switchRecordIso D x v hv` has `Φ w = w` by `rfl`; `(D.switch x).record.crossingOf w = D.record.crossingOf w`,
   `(D.record.switch v).crossingOf w = D.record.crossingOf w`, `(D.switch x).record.M = D.record.M` are `rfl`.
4. `geoMarkPosition hP (Sum.inr v)` has `.1 = v.2.val` and `.2.val = visitParameter v` by `rfl`; `geoMarkPosition hP
   (Sum.inl i) = (i, ⟨0, _⟩)` by `rfl`; `traversalKey` unfolds under `show` to `((·).1.val : ℝ) + (·).2.val`.
5. `geoMarkSuccessor_position_cases` returns the vertex case as `Sum.inl ((geoMarkPosition hP a).1 + 1)`, syntactically
   not `Sum.inl (M + 1)`: rewrite `(geoMarkPosition hP (Sum.inl M)).1 = M` (`rfl`) first.
6. `geoIndependent_iff_isDecomposition hn hP S` is stated with `generic_crossingGeometry hn hP`; accepted for
   `(CarrierGeometry.ofGeneric hn hP).cg` by proof irrelevance (no transport). `CB.restrictCrossings_iso_of_recordIso`
   lives in namespace `SM.CB` (the BigonDeletion docstring names it unqualified).
7. `haveI` on a `Fact` in a proof triggers the `haveILetI` linter — use `have`. `Visit P` destructures as
   `⟨c, i, hi⟩` (a `Sigma` over a subtype); `change c = c' at h1` after `rcases` makes `subst` work.
