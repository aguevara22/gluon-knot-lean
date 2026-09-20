# U-177 REPORT — leaf `RProof.extreme_selected` (row 177, R:extreme_selected)

Prover unit U-177 (prefix `esc_`), 2026-09-15 ≈17:30 UTC / 1:30pm ET.
File: `work/drafts/cvtail/U_R177.lean` (1700 lines) = byte-identical copy of `Statements_FINAL.lean` + one
inserted block (`section ESC … end ESC`, lines 799–1506, immediately before the row-177 docstring, inside
`namespace RProof`) + the leaf's `sorry` line replaced.  `diff Statements_FINAL.lean U_R177.lean` prints exactly
`798a799,1506` (the block) and `810c1518` (the one `sorry` line of the leaf → the `exact esc_ledger …` line);
no statement, definition, name, docstring or import changed; nothing written under `work/lean`.

## Result in one paragraph

The leaf is NOT closed: the `couple` field of `ExtremeSelectedData` needs two Reidemeister-move
realisations on the grouped contact diagrams and the carrier split of `Q ∪ T` (G11-scale, PLAN §7 risk 2).
Following D-F11 the unit (a) states these as explicit interface Props (`esc_switch_riii`,
`esc_rii_after_smoothing`, `esc_three_components`, bundled per configuration in `esc_MoveData`; the carrier
split `esc_FullSplitData`; the event-level `esc_interface`), (b) PROVES the whole RA ledger from them and from
`CV.CarrierSlotFloor`: `esc_ledger (hI : esc_interface) (hF : CV.CarrierSlotFloor) : RowShape @ExtremeSelectedData`,
and (c) realises everything of the printed proof that is not a move or the split: the reduction of the row to
the single contact carrier (§1), the two skein steps (5)/(7), knot parity (8), the three-component lowest row
(12) from mp:lowest, the selector/rotation/writhe/floor ledger (13)–(20) and the final identity (2).  The leaf
body is now `exact esc_ledger (by sorry) (CV.carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC) n hn E e f g
h3 h4e h4f h4g hE` — the single `sorry` is the interface `esc_interface`; `grep -c sorry` 11 → 11 (the leaf's
one `sorry` moved into the interface hole; the count includes the docstring mention at line 33).

## Compile

`cd work/lean && lake env lean ../drafts/cvtail/U_R177.lean` → exit 0, **0 errors**, exactly 10 "declaration
uses `sorry`" warnings (the FINAL's 10: placeholders `SM.cf_thm_carrierfloor` :160, `SM.thm_C_S7` :194,
`SM.thm_C_soft` :198, `SM.cor_C_inherits` :1645; leaves `CV.carrier_slot_floor_of_C` :600,
`CV.cvt_singleton_split` :693; rows `generic_selected` :738, `extreme_transport` :790; row 175's leaf
`cvt_pair_row_zero_of_singleton` :757; and `extreme_selected` :1511 through the interface hole), ~21 s wall clock.

Axioms (scratch copy of the file with `#print axioms` appended):
* `esc_ledger`, `esc_couple`, `esc_contact_identity`, `esc_coefficient_identity`, `esc_three_component_row`:
  `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` — standard + the
  authorised literature interfaces (the same footprint as `RProof.generic_transport`); **no `sorryAx`**.
* `esc_smoothing_outer`, `esc_lift_crossing`, `esc_contact_unique`, `esc_coeffAt_corner`: standard only.
* `extreme_selected`: the above + `sorryAx` (the interface hole).

## What is PROVED (all `esc_`-prefixed, section ESC; line numbers of `U_R177.lean`)

**Ledger and its consumers**
* `esc_ledger` :1491 — `RowShape @ExtremeSelectedData` from `esc_interface` and `CarrierSlotFloor`; fields
  `full_present_on_empty`/`full_absent_on_complete` are the accepted `PRE_177_*`; the radius is
  `min δL (min δR δG)` of `localization` (row 164), `AV_exists_eventRadius`, `EXT_exists_guardRadius`.
* `esc_couple` :1438 — the `couple` field at the accepted data: the three row terms are factored by
  `rowTerm_eq_exterior_mul_touching` (X1Rows.lean:461) and the exterior factor `C_Q` is the same for all three
  (`EXT_exteriorFactor_wall` X1Rows2.lean:1794 across the wall, `EXT_exteriorFactor_eq_base` :855 from `Q'` to
  `Q' ∪ T'`), so (2) ⇐ the contact identity ("No exterior scalar … was divided out": `congr 1` on `C_Q * _`).
* `esc_contact_identity` :1251 — `τ_H(Q) − τ_L(Q') = τ_L(Q' ∪ T')` on touching factors: (i) exactly one
  triangle-touching carrier per side (`esc_contact_exists`, `esc_contact_unique`), the empty-side one being
  `GT_carrierEquiv W q₀` for the wall `W := GT_empty_wall` (X1Rows3.lean:3175) — with `wt`, `R(L)`, `w_{S,L}`
  transported by `GT_weight_eq`/`GT_carrierR_eq`/`GT_geoCarrierCrossings_eq_of_good` + `card_map` (the
  `G11_173_empty_row` pattern), hence a common slot `d`; (ii) `F = P(D(W))` by `GT_groupedPoly_eq_homfly`;
  (iii) the crossings `x, y` on both grouped contact diagrams (`esc_lift_crossing`), the smoothings at `x`
  (`exists_smoothing_record_visit`), `y` carried through them (`esc_smoothing_outer`), the smoothings at `y`;
  (iv) (13) by `esc_coefficient_identity`; (v) the three selector branches: mixed (`weight_of_mixed`, the
  interface's `mixed`), live and dead (the interface's `uniform`, `outer_alternative`), with (18) by `omega` on
  `slot`, (19) by `esc_coeffAt_corner`, the floor by `esc_quadrant_groupedPoly` (= `CarrierSlotFloor` +
  `cvt_groupedPoly_inSupportM` + `mindegAZ_spec`), the central `Ω₁ = 1` from `central_no_piece`, `central_rot`,
  `groupedPoly_of_piecesOn_eq_empty`, `coeffAt_one`.
* `esc_coefficient_identity` :1220 — (7) and (13): from the four skein equations (`CV.ax_homfly.skein` at
  `x_H, x_L, y_H, y_L`, all positive), the move identities (4), (6), knot parity (8)
  (`esc_knot_coeff_neg_two`) and the lowest row (12): `[a^d z^0](F_H − F_L) = −[a^{d+2+2Λ} z^0]((a−a⁻¹)² K)`;
  one `linear_combination` for (7) (`a⁻²z² = single (−2,2) 1`, `esc_aInv_aInv_z_z`).
* `esc_three_component_row` :1087 — **(12) PROVED from mp:lowest** (`SM.lowest.lowest_value` at `c = 3`,
  `P_eq_homfly`, `Equiv.prod_comp` + `Fin.prod_univ_three` for the component indexing, `coeff_T_mul'` for the
  `a^{−2Λ}` shift, `zRow_a_mul`/`zRow_aInv_mul` and `CV.zRow_zero_mul_of_inSupportM_one` with
  `P_knotRestrict_inSupportM_one` for the `[z^0]` row of `(a−a⁻¹)² K`), given the diagram identification
  `esc_three_components` (below).  So the "3-component lowest z-row" of the unit brief is no longer an interface:
  only the identification of the three components with the outer grouped knots is.

**Contact carrier (§1 of the text)**
* `esc_not_triangleDisjoint_iff` :909, `esc_contact_exists` :939 (owner of the `e`-visit of `x_ef`),
  `esc_contact_unique` :923 and `esc_contact_owns` :947 (both from `GT_empty_tri_subset` X1Rows3.lean:3216, which
  is orbit-free: adjacency of the bundle pairs + `owner_eq_of_mem_U`; works on both sides),
  `esc_touchingFactor_eq_of_unique` :957, `esc_touchingFactor_eq_of_four` :970 (`Finset.prod_congr` onto
  `{q₀}` / `{A, B, C, Z}` — robust against the classical `DecidablePred` instance of `touchingFactor`'s filter).

**Diagram helpers**
* `esc_lift_crossing` :999 — every retained crossing `c` of a carrier is a positive crossing of `D(W)` at
  `crossingPoint c` (`geoCarrierCrossingEquiv`, `crossingPoint_geoCarrierCrossingEquiv`,
  `geoPositiveLift_isPositive`).
* `esc_smoothing_outer` :1016 — a crossing `y ≠ x` of `D` is carried by ANY oriented smoothing `D₀` at `x` to
  a crossing of `D₀` at the same double point with the same sign (`OrientedSmoothingData.inner_iff`, the outside
  match `ψ`, `over_eq`/`under_eq`, `dir_pos` at the crossing point, which is outside `U` by
  `Clean.crossingPoint_not_mem_frontier` + `closure_eq_interior_union_frontier`; `det_smul_smul`,
  `mul_pos_iff_of_pos_left`).  This is what lets the interface identify `y` in the smoothing by its double point.

**Laurent algebra** (`CV/FullTwist.lean` is not imported by the FINAL, so two of its lemmas are re-proved)
* `esc_coeffAt_single_mul` :820, `esc_a_mul_a`, `esc_aInv_mul_aInv`, `esc_aInv_aInv_z_z` :834,
  `esc_sq_expand` :838, `esc_coeffAt_sq_mul` :845 ("Expand `(a−a⁻¹)² = a² − 2 + a⁻²`": samples at `m−2, m, m+2`),
  `esc_Quadrant` :855 (support in `a`-degree `≥ m`, `z`-degree `≥ 0`) with `coeffAt_eq_zero`, `esc_quadrant_mul`
  (`support_coeff_mul_subset`), `esc_coeffAt_corner` :872 (`coeff_mul_add_of_uniqueAdd`: the corner coefficient
  of a product of quadrant elements is the product — (19) without any nonvanishing hypothesis, so the "zero `z⁰`
  component row" remark of the text is automatic), `esc_knot_coeff_neg_two` :887, `esc_quadrant_groupedPoly` :895.

## Interface Props (stated, consumed, NEVER mapped — D-F11)

* `esc_switch_riii D_H D_L x_H x_L : Prop := homfly (D_H.switch x_H) = homfly (D_L.switch x_L)` :1058 — (4).
* `esc_rii_after_smoothing D_H0 D_L0 y_H y_L : Prop := homfly (D_H0.switch y_H) = homfly (D_L0.switch y_L)`
  :1065 — (6).
* `esc_three_components J Λ fA fB fC : Prop := J.componentCount = 3 ∧ twoLambda J = 2Λ ∧ ∃ σ : Fin 3 ≃ Fin J.Γ.c,
  homfly (J.knotRestrict (σ 0)) = fA ∧ … = fB ∧ … = fC` :1077 — (9)–(11): the three components of `D_L^{xy}` are
  the outer grouped knots, `Λ = lk(J)`.
* `structure esc_MoveData (D_H D_L) (pxH pyH pxL pyL : Plane) (Λ) (fA fB fC) : Prop` :1118, fields
  `switch_riii`, `rii_after_smoothing`, `knot_after_two` ("`D_H^{xy}` is a knot", §2), `three_components`; the
  crossings are identified by their double points (`Γ.crossingPoint _ = crossingPoint (xPair hef)` etc.), the
  smoothings are the library's relational `IsOrientedSmoothing` (quantified over every smoothing site).
* `structure esc_FullSplitData (hn) (hG) (e f g) (hQ) (hS : Q ∪ T ∈ Ind) (q₀) (A B C Z) (Λ) : Prop` :1146 —
  the carrier split of the full row on the empty side: `touching_iff` (the touching carriers are exactly
  `A, B, C, Z`), `distinct`, `central_no_piece`, `central_rot : carrierR Z = 1` (uniformrot (i) with three
  corners), `writhe` (17), `mixed` (§4 first paragraph), `outer_alternative` (`UniformOrOneDissentCV` of the
  three outer corner polygons when the parent is uniform — the hypothesis under which `CarrierSlotFloor` is
  read), `uniform` (the two exhaustive branches: live (16)+(14) `R_A+R_B+R_C = R+1 ∧ W_full = −W`; dead (16)
  `R_A+R_B+R_C+1 = R ∧ W_full = 0`).
* `esc_interface : Prop` :1188 — at every configuration of the `couple` field (`t` the `K3` side, `t'`
  opposite, `Q` outside at full availability, `q₀`/`q₀'` triangle-touching carriers of the empty row on the two
  sides, characterised by `¬ TriangleDisjoint`), `∃ A B C Z Λ, esc_FullSplitData … ∧ esc_MoveData
  (carrierDiagram_H q₀) (carrierDiagram_L q₀') (points of x, y on both sides) Λ f_A f_B f_C`.

The leaf then reads `extreme_selected := esc_ledger ⟨esc_interface⟩ (carrier_slot_floor_of_C
SM.cf_thm_carrierfloor.clauseC) …`; when the interface is realised, replace `(by sorry)` by its proof term (the
`CarrierSlotFloor` argument is U-SLOT's leaf at the row-99 placeholder, exactly as row 165 consumes it).

## What remains (the realisation; sizes are estimates against the accepted G11 = 11k lines for one RIII site)

1. **(4) `switch_riii`** — the matched switch + RIII through the wall on the two grouped contact knot diagrams:
   the G11 toolkit applies almost verbatim (`G11_Config` on the corner polygon of the contact carrier; here the
   three local strands' over-order is cyclic (K3 orbit, (1b)) and becomes transitive after switching `x`, so the
   RIII site is built on `D_H.switch x_H`; the record isomorphism `M₁ ≅ D_L.switch x_L` needs the
   `ExactTriangleVisitOrders` transpositions as in G11 Unit F).  ~8–11k lines.
2. **(6) `rii_after_smoothing`** — after smoothing `x` and switching `y`: an actual `RIIData` (SM/LinkMoves.lean)
   for the empty bigon `y, z` on each side (the `IsOrientedSmoothing` site gives `D_H0` only relationally, so the
   bigon must be located through the outside match) and an ambient isotopy through the wall of the two-component
   remainders (a record isomorphism as in G11's Unit F, without the triangle).  G10-scale, ~5–8k lines.
3. **`knot_after_two` / `three_components`** — record-level: `componentCount_smooth_of_self/mixed`
   (SM/LinkRecordExtras.lean:316/320) with `exists_smoothing_record_visit`'s `RecordIso D₀.record (D.record.smooth
   v)` give the counts once "`y` is mixed in `D_H^x`" / "self in `D_L^x`" is known, i.e. once the RECORD
   interlacement of `x_H, y_H` in `D(W)` is identified with the geometric interlacement `EdgeAB` on the polygon
   (K3: interlaced; empty: not).  The bridge record-interlacement ↔ `GeometricInterlaces` for retained crossings
   of a carrier is not in the library as a lemma (cor:groupedknot (A) `tree`/`blockEquiv` is the closest);
   ~300–600 lines.  The identification of the three components with the outer grouped knots (`knotRestrict` ≃
   `carrierDiagram` of `A, B, C`, and `twoLambda = 2Λ`) is part of the split below.
4. **`esc_FullSplitData`** — the carrier split of `Q' ∪ T'` relative to the contact carrier of `Q'`: three
   smoothings; lem:turnlift (ii) for (15)/(16), `uniformrot` (i) (central triangle, three same-sign corners, `R = 1`)
   and (ii) (dead branch), `selector_A` (each outer carrier has ≥ 3 corners), the sign table (1c)
   `s_o = −σ` from `GenericTableData.extreme_iff_alternating`, the writhe count (17) (`groupedWrithe_eq_card_
   geoCarrierCrossings` + the crossings between outer gap strings).  This is U-SPLIT's geometry three times over;
   U-SPLIT's (a)–(e) are the template.  ~3–5k lines.

Nothing of 1–4 is consumed by any other unit; the ledger is final and independent of how they are realised.

## Findings for the assembler / executor

* **Statement check**: the `couple` field is stated with `t` the `K3` side and the identity
  `rowTerm_H Q − rowTerm_L Q' = rowTerm_L (Q' ∪ T')` — the sides named by their graphs, no coorientation; the
  proof route confirms every clause is needed and none is missing (FullAvail is used for `GT_empty_wall`,
  `GT_empty_tri_subset` and `PRE_177_full_present_on_empty`; `CompleteLocal` for `EmptyLocal` on `t'` via
  `PRE_176_graphs_complementary` and, in the realisation, for the K3 over-order).  No stronger hypothesis is
  needed for the ledger; nothing false was found.
* **Which side carries the selector branch**: the text's `W = wt(empty contact carrier)` is read on the EMPTY side
  (`q₀'`); `GT_weight_eq` identifies it with the `K3`-side weight.  The interface fields `mixed`/`uniform` are
  therefore on `q₀'` — the realiser should keep it that way (the K3-side carrier has the same weight but the
  outer carriers live on the empty side).
* **`CarrierSlotFloor` enters only through `esc_quadrant_groupedPoly`**, on the three outer carriers, under the
  interface's `outer_alternative` (uniform or one-dissent after reversal) — exactly the text's "after a possible
  orientation reversal, `thm:carrierfloor` applies … if `f_i = 0` it is vacuous"; the quadrant form handles the
  vacuous case with no side condition.
* **`GT_empty_tri_subset` is orbit-free** (it never reads `ExtremeLocal`/genericity), so the uniqueness of the
  contact carrier is available in the extreme orbit for free; likewise `GT_empty_wall`, `GT_empty_good`,
  `GT_outsideSupports_transport`, `GT_fullAvail_transport` (X1Rows3).  U-174/U-176 can reuse
  `esc_contact_*`/`esc_touchingFactor_eq_of_*` verbatim (rename the prefix).
* **mp:lowest is in the library as `SM.lowest.lowest_value`** (SM/MarkedProducts.lean:4941, the general `c`) —
  the RA texts' "two-component switch argument … repeated at the one lower row" needs no new induction; only the
  identification of the components is geometric.  `coeff_T_mul'` (MarkedProducts.lean:2136) converts the
  `aPow` shift to a `coeffAt` shift.

## Mathlib / library pitfalls met

* `-/` inside a docstring: the phrase "one-/three-component" terminated the module docstring (`unexpected identifier;
  expected command` far away) — write "one- or three-component".
* Superscript `⁰` is not an identifier character (`D_H⁰` fails to parse); use `D_H0`.
* `push_neg` is deprecated in this toolchain (prefer `push Not`); `esc_not_triangleDisjoint_iff` is proved by hand.
* `coeff_mul_add_of_uniqueAdd` (Mathlib `MonoidAlgebra/NoZeroDivisors.lean`) takes `UniqueAdd f.coeff.support
  g.coeff.support a0 b0` and needs NO attainment (unlike the library's `coeffAt_mul_of_max_weight`), which is what
  makes (19) unconditional.
* `Finset.prod_congr (s₂ := {q₀}) ?_ fun _ _ => rfl` + `ext; simp only [Finset.mem_filter, …]` avoids the
  `DecidablePred` instance mismatch of `touchingFactor`'s `open scoped Classical` filter (a direct `rw` of the
  filter fails).
* `geoIndependent_of_mem_Ind` is `CV.geoIndependent_of_mem_Ind`; `homfly` is `SM.homfly`; `coeffAt`, `R`, `zRow`,
  `aPow`, `twoLambda`, `coeff_T_mul'`, `InSupportM.one_mul_one` are in `SM.Link` (the section opens `SM.Link
  AddMonoidAlgebra`); `P_eq_homfly` is `SM.P_eq_homfly`.
* `Diagram.eval_visitPt` rewrites `eval (visitPt v) = crossingPoint v.1`; after `outerOverPt_val` the crossing is
  `(D.overVisit y).fst`, which is `y` only by `rfl` — use `rw … ; exact` rather than `simpa`.
* `esc_smoothing_outer` needs the crossing point OUTSIDE `U` (not just outside `interior U`) for `dir_pos`:
  `Clean.crossingPoint_not_mem_frontier` + `closure_eq_interior_union_frontier` + `subset_closure`.
* The wall transport of the contact weight must be rewritten TOWARDS the empty side (`← hw`) before the branch
  case split, since the interface's selector facts are on `q₀'`.
