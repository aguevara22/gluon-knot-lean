# Site_176_REPORT — row 176 (R:extreme_transport), the `j`-corner bigon site of `carrierDiagram q₀'` switched at `y`

I-176 prover (subagent), 2026-09-15.  Inputs: PLAN_FINAL.md §4.3 / §3 F-176-1 / §6 R5, W1_SKELETON_REPORT.md §1 (the
`BigonData` API, the frozen leaf `exists_bigonData_of_triangle`), Statements_FINAL.lean (`est_port_weak`,
`est_port_weak_of_bigon`, `fulltwist_coefficient_of_port_weak`), RProof/RALedgers.lean section `EST` (the consumer:
`est_PortData`, `est_omega1_eq_of_port`, `est_port_relation`, `est_row_H`, `est_row`, `est_extremeTransportData`,
`est_ledger`, `est_extreme_transport_of`, and the helpers `est_retained_u_iff`, `est_retained_affected`,
`est_not_retained_H`, `est_wall`, `est_S_ind`, `est_S'_ind`, `est_liftCrossing`), U_R176_REPORT.md §3/§5,
RProof/GenericTransport.lean 8780–10263 (G11 Unit A: `G11_carrierEdge*`, `gu1_*`, `gu2_*`, `G11_clear`,
`gu2_clear_closed`, `gu2_parallel_meet_vertex`, `gu2_line_*_mem_segment`), SM/GeoPositiveLift.lean
(`geoPositiveLift`, `geoCarrierCrossingEquiv`, `geo_mark_block`, `geo_block_mark_eq`, `GeoBlockInterior`),
SM/GeoCornerPolygon.lean (`geoCornerPolygon_block`), SM/FlatCarriersDefs.lean (marks, `geoSmoothingSuccessor`,
`geoOwner`, `geoCornerMark`), RProof/Cores.lean (`LocalizationData`, `visitOn`, `triangleSupports`),
SM/TripleVisitExchanges.lean (`ExactTriangleVisitOrders`), SM/LinkDiagram*.lean (`Diagram.switch`, `IsPositive`,
`record`, `switch_overBit_of_ne`), SM/LinkRecord.lean (`RecordIso`, `Record.switch`), SM/MarkedProducts.lean
(`restrictCrossings`, `CrossKeep`).

## 0. Deliverables and checks

| item | result |
|---|---|
| `work/drafts/moves/Site_176.lean` | 4143 lines = `Skeleton_W1.lean` (1866 lines, byte-identical) with `import RProof.RALedgers` added after `import RProof.GenericTransport` + an APPENDIX of 2276 lines (module comment + §A–§H, all names `s176_`, namespace `RProof`) |
| compile `cd work/lean && lake env lean ../drafts/moves/Site_176.lean` | exit 0, **0 errors**, ≈ 18 s; warnings: exactly the skeleton's **33** `declaration uses sorry` (the 4 frozen leaves + 29 `m*_` sub-leaves) and the skeleton's own `<;>` style warning at line 566; **no new `sorry`** (`grep -c sorry` = 34 = skeleton) |
| statement identity `python3 check_W1_identity.py Statements_FINAL.lean Site_176.lean` | "declarations in Statements_FINAL: 37; changed/missing: **0**" (every frozen statement byte-identical).  Its checks 1 and 3 report `False` MECHANICALLY: check 1 compares lines 1–136 (shifted by the one added import line), check 3 requires the file to END with the Statements_FINAL suffix (an appendix cannot pass it).  Own check: `Site_176.lean` with the import line removed and the appendix cut is byte-identical to `Skeleton_W1.lean` (`True`) |
| `#print axioms` | all geometric `s176_` theorems (`det_mul_det_neg`, `same_over_switch₁/₂`, `s176_four_le_of_crossing`, `s176_cyclic`, `s176_corner_case1`, `s176_clear_case1`, `s176_cornerSite_of_carrier`, `s176_event_site_core`, `s176_site_of_event`, `s176_site_of_event'`, `s176_switchRestrictIso`, `s176_hrec_of_unswitched`, `s176_wallΦ`, `s176_hrec_unswitched_of_succ`, `s176_hX_event`, `s176_hrec_wall_of_succ`): `[propext, Classical.choice, Quot.sound]`; the ledger (`s176_est_omega1_eq_of_port_weak`, `s176_est_ledger_weak`): standard + `SM.lit_homfly` (the accepted `est_ledger` footprint); `s176_CornerSite.exists_bigon_switch`, `s176_port_weak_of_event`, `s176_port_weak_of_event'`, `s176_est_port_relation_weak_of`, `s176_est_port_relation_weak_of'`: additionally `sorryAx` THROUGH THE FROZEN LEAF `exists_bigonData_of_triangle` only (black box, expected) |
| written under `work/lean` | nothing |

## 1. What is PROVED (the site theorems; exact statements in the file)

### §A. The abstract `j`-corner site (`structure s176_CornerSite (D : Diagram)`)
Fields: `i`, `a`, `hk : 4 ≤ k`, `s`, `y₁ y₂`, `hy₁ : y₁.val = {⟨i, a⟩, s}`, `hy₂ : y₂.val = {⟨i, a+1⟩, s}`,
`pos₁ pos₂ : D.IsPositive y₁/y₂`, `clear : ∀ u ≠ ⟨i,a⟩, ⟨i,a+1⟩, s, Disjoint (seg u) (convexHull {pt y₁, P (a+1), pt y₂})`.
* `s176_CornerSite.det_mul_det_neg : det (dir e_in) (dir s) * det (dir e_out) (dir s) < 0` — **the corner identity**
  `(1 − t₁)·det(e_in, s) + t₂·det(e_out, s) = 0` (the two crossing points of the straight strand `s` with the two
  edges of the corner `M₁` are `M₀ + t₁ e_in` and `M₁ + t₂ e_out`, both on `line(s)`); with `t₁ < 1`, `t₂ > 0` and
  transversality the two determinants have opposite signs.  This is the whole content of sm-4:614-618's sign table.
* `over₁_eq_s_iff`, `over₂_eq_s_iff`, `over₁_iff_not_over₂` (on the positive `D` exactly one of `y₁, y₂` has `s` over).
* **`same_over_switch₁ : ((D.switch y₁).overStrand y₁ = s ∧ (D.switch y₁).overStrand y₂ = s) ∨ (… ≠ s ∧ … ≠ s)`**,
  **`same_over_switch₂`** (the frozen `BigonData.same_over` field, verbatim, for either switched crossing).
* **`exists_bigon_switch₁ : ∃ B : BigonData (D.switch y₁), B.i = i ∧ B.y = y₁ ∧ B.z = y₂`**,
  **`exists_bigon_switch₂ : ∃ B : BigonData (D.switch y₂), B.i = i ∧ B.y = y₁ ∧ B.z = y₂`**,
  **`exists_bigon_switch (y₀) (h : y₀ = y₁ ∨ y₀ = y₂) : ∃ B : BigonData (D.switch y₀), B.i = i ∧ (B.y = y₀ ∨ B.z = y₀)`**
  — through the frozen leaf `exists_bigonData_of_triangle` (black box).
* `s176_four_le_of_crossing : x.val = {⟨i,a⟩, ⟨i,b⟩} → 4 ≤ k` (`hk` for a one-component site: crossings pair
  NON-adjacent strands and on `ZMod 3` every pair is adjacent).

### §C. The carrier-level realisation (a carrier `q` of an independent `T` on a `CarrierGeometry` polygon `P`; the
other side `P'` enters only through `hX : ExactTriangleVisitOrders P P' a b c hs`)
Hypotheses: labels `a b c` pairwise distinct; crossings `j u v` with `j.val = {a,b}` (`j ∈ T`, the corner),
`u.val = {a,c}`, `v.val = {b,c}` both retained (`∈ geoCarrierCrossings hG.cg T q`); `hQT : ∀ x ∈ T, x ≠ j → ∃ ℓ ∈ x.val,
ℓ ≠ a ∧ ℓ ≠ b ∧ ℓ ≠ c` (every other selected crossing is foreign).
* `s176_no_visit_between` (the labelled form of `G11_no_visit_between`), `s176_succ_of_lt` (`ρ_T` of an unselected
  visit is the next visit on its edge), `s176_cornerPolygon_inj` (distinct corners of a carrier sit at distinct
  points: `tail_off` + nonzero edges), `s176_lift_val` (the strands of the lift of a retained crossing are the carrier
  edges of its two visits), `s176_next_corner` (the `ρ`-successor of the last block mark is `c_{k+1}`, from
  `geoCornerPolygon_block`), `s176_carrierEdge_of_succ` (the carrier edge of the first block mark after a corner),
  `s176_no_two_corners` (no carrier has both visits of a selected crossing as corners).
* **`s176_cyclic : (u <_a j) ↔ (j <_b v)`** — cyclicity of the corner FROM RETENTION: in either non-cyclic case both
  visits of `j` become `ρ`-successors of visits owned by `q`, hence two corners of `q` at one point.  No
  `sign_branch` / `GenericTableData` is needed (which matters: `est_port_relation` has no `hGT` binder).
* **`s176_corner_case1 (hlt_a : u <_a j) : c_{kA+1} = (j, a) ∧ P_Q (kA+1) = pt j ∧ kB = kA + 1 ∧ kC' = kC`**
  (`kA, kC` the carrier edges of `(u,a)`, `(u,c)`; `kB, kC'` of `(v,b)`, `(v,c)`).
* **`s176_corner_mem_K`**: the only corner of the carrier inside the closed triangle is the `j`-corner.
* **`s176_clear_case1`**: every carrier edge other than `kA`, `kA+1`, `kC` misses `conv{pt j, pt u, pt v}` (foreign
  edges by `gu2_clear_closed`; edges inside `a`/`b`/`c` meet the triangle on one side, share a corner with
  `e_in`/`e_out`/`s` by `gu2_parallel_meet_vertex`, that corner is the `j`-corner, and an edge through it is
  `e_in` or `e_out` by `geoCornerPolygon_tail_off`).
* **`s176_cornerSite_case1`**, **`s176_cornerSite_of_carrier : ∃ Tsite : s176_CornerSite (geoPositiveLift hn hG hT q),
  Tsite.i = 0 ∧ ((Tsite.y₁ = lift u ∧ Tsite.y₂ = lift v) ∨ (Tsite.y₁ = lift v ∧ Tsite.y₂ = lift u))`** — case 2 is
  case 1 on the relabelled data `(b, a, c), (j, v, u)`.

### §D. The event-level site (the binders of `est_port_relation`)
* **`s176_event_site_core`** (labels fixed): `hv'` — the third crossing `v'` is retained by `q₀'` too
  (`est_retained_u_iff` both ways; the two `c`-visits of `u, v` are `ρ_S`-adjacent on `H`, so one owner) — and the
  carrier corner site on `carrierDiagram q₀'`.
* **`s176_site_of_event … (hu : u ∈ T) (hju : j ≠ u) (hu' : u' retained by q₀') : ∃ Tsite : s176_CornerSite
  (carrierDiagram hn hG' hS' q₀'), y = Tsite.y₁ ∨ y = Tsite.y₂`** with `y = est_liftCrossing … hu'` — six relabellings
  (`GT_tri_cases` on `j` and `u`).  This is item (a) of the task.

### §B, §E, §F, §G, §H. Composition, ledger re-base, `hrec`
* `s176_PortDataWeak` (= `est_PortData` with `port : est_port_weak D₊ D₀ y`), `s176_PortDataRest` (= `est_PortData`
  minus `port`), `s176_PortDataWeak.mk'`, `.ofPortData`.
* **`s176_est_omega1_eq_of_port_weak`** = `est_omega1_eq_of_port` with the ONE call replaced (F-176-1), rest byte-identical.
* `s176_est_port_relation_weak : Prop` (= `est_port_relation` with `s176_PortDataWeak`),
  `s176_est_port_relation_weak_of_strong`, **`s176_est_row_H_weak`, `s176_est_row_weak`,
  `s176_est_extremeTransportData_weak`, `s176_est_ledger_weak : CarrierSlotFloor → s176_est_port_relation_weak →
  RowShape @ExtremeTransportData`**, `s176_est_extreme_transport_of_weak`, `s176_est_ledger_of_strong`.
* `s176_port_weak_of_bigon`, `s176_port_weak_of_cornerSite`, `s176_reducedRecord_eq`
  (`B.reducedRecord = D.record.restrictCrossings {c ≠ crossingOf (overVisit B.y), ≠ … B.z}`, `rfl`).
* **`s176_port_weak_of_event (hrec : s176_hrec_of_site …) : est_port_weak D₊ D₀ y`** — (a) + (b) + `est_port_weak_of_bigon`
  (item (c)).
* **`s176_est_port_relation_weak_of (hrec : ∀ …, s176_hrec_of_site …) (hrest : ∀ …, Nonempty (s176_PortDataRest …)) :
  s176_est_port_relation_weak`** — the weak interface from the site, `hrec`, and the non-move port data.
* **`s176_switchRestrictIso (hK : crossingOf (overVisit x₀) ∉ K) : RecordIso ((D.switch x₀).record.restrictCrossings K)
  (D.record.restrictCrossings K)`** (identity on occurrences), `s176_keep_switch_eq`, **`s176_hrec_of_unswitched`**,
  **`s176_hrec_of_site_of_unswitched : s176_hrec_unswitched … → s176_hrec_of_site …`**: the switch drops out of `hrec`.
* §G (carrier level, hypotheses `hX : retained q' = (retained q).map transport ∪ {u', v'}`, `hu_not`, `hv_not`,
  `hdet`): **`s176_wallΦ : {v : D₊.Γ.Visit // CrossKeep (s176_wallKeep u' v') v} ≃ D₀.Γ.Visit`** (the occurrence
  bijection across the wall: `liftVisitEquiv` → drop `{u', v'}` → `visitTransport hs.symm` → `liftVisitEquiv⁻¹`),
  `s176_wallΦ_liftVisit` (its parent visit is the transport of the parent visit), `s176_crossKeep_iff`,
  **`s176_hrec_unswitched_of_succ (hsucc : ∀ v, Φ (succ v) = D₀.record.succ (Φ v)) : Nonempty (RecordIso
  (D₊.record.restrictCrossings (s176_wallKeep u' v')) D₀.record)`** — `comp_eq`, `pair_eq`, `bit_eq`, `sgn_eq` PROVED.
* §H (event level): `s176_hX_event` (= `est_retained_affected`), `s176_not_mem_map_event` (= `est_not_retained_H`),
  `s176_hdet_event` (= `hR.sign_eq`); the Prop **`s176_hrec_wall`** (the identification for the SPECIFIC deleted
  crossings `lift u', lift v'`, for every third crossing `v` with `v'` retained); **`s176_hrec_wall_of_succ`**
  (from the successor clause alone); **`s176_site_of_event'`** (the site with `v`, `hv'` and `{y₁, y₂} = {lift u',
  lift v'}`); `s176_wallKeep_comm`; **`s176_port_weak_of_event' (hrec : s176_hrec_wall …) : est_port_weak D₊ D₀ y`**;
  **`s176_est_port_relation_weak_of'`** (the weak interface from `s176_hrec_wall` and `s176_PortDataRest`).

## 2. Pre-review verification: every frozen `BigonData` field is supplied at the 176 site (no change needed)

| field | at the 176 site | how |
|---|---|---|
| `i` | `0 : Fin 1` | one-component `geoPositiveLift` |
| `a` | `kA = G11_carrierEdge (u', a)` (case 1) / `kB` (case 2) | the entering edge is the carrier edge of the retained visit of `u'`/`v'` on the label shared with `j'` |
| `hk : 1 + 3 ≤ k` (`4 ≤ k` for the leaf) | `s176_four_le_of_crossing` | `s` and `e_in` are non-adjacent strands of ONE component |
| `s` | `⟨0, kC⟩`, `kC = G11_carrierEdge (u', c)` | `s176_corner_case1.4`: the two `c`-visits share the carrier edge (`G11_carrierEdge_eq_of_adjacent`) |
| `y, z, hy, hz` | `lift u', lift v'` (or swapped); `hy₁ : (lift u').val = {⟨0,kA⟩, ⟨0,kC⟩}`, `hy₂ : (lift v').val = {⟨0,kA+1⟩, ⟨0,kC⟩}` | `s176_lift_val` + `s176_corner_case1.3` (`kB = kA + 1`) |
| `run_free`, `no_io` | vacuous / `no_io_of_succ` | inside the frozen leaf (`j = 1`) |
| `same_over` | `s176_CornerSite.same_over_switch₁/₂` | the corner identity `det_mul_det_neg` + positivity + `switch_overStrand_self/of_ne` |
| `ty tz tsy tsz`, specs | inside the frozen leaf (`crossingParam`) | — |
| `K`, convex, compact | `convexHull ℝ {pt y₁, P (kA+1), pt y₂}` inside the frozen leaf | `P (kA+1) = pt j'` (`s176_corner_case1.2`) |
| `run_mem`, `in_iff`, `out_iff`, `s_iff` | inside the frozen leaf (barycentric side lemmas) | — |
| `clear` (CLOSED `K`) | `s176_clear_case1` → `s176_clear_of_indices` | PLAN §3 last bullet's derivation, adapted: the corner vertex `P (kA+1)` IS in `K`, so the vertex clause becomes "the only corner in `K` is the `j`-corner" (`s176_corner_mem_K`) and the incidence at that corner excludes exactly `e_in, e_out` |

Two facts the pre-review did not state that the site NEEDS and that are proved here: (i) the carrier `q₀'` has ONE corner
at `pt j'` (both visits of `j'` cannot be corners of one carrier, `s176_no_two_corners`) — this is what makes `clear`
hold for the other half-edges of `a`, `b` at `j'` (they belong to a different carrier, hence are not strands of `D₊`);
(ii) the orientation of the corner is forced (`s176_cyclic`), so `y = lift u'` is `B.y` or `B.z` according to the case —
the frozen glue is indifferent (`est_port_weak_of_bigon` takes any `B : BigonData (D₊.switch y)`).

## 3. `hrec` (item (b)) — reduced to ONE clause, not closed

Chain (all PROVED except the last hypothesis): `hsucc` → `s176_hrec_wall_of_succ` → `s176_hrec_wall` →
`s176_port_weak_of_event'` → `est_port_weak D₊ D₀ y` → `s176_est_port_relation_weak_of'` → `s176_est_ledger_weak`.
* `s176_hrec_of_site` (§E, STATED, the switched form as `B.reducedRecord` presents it) reduces to the UNSWITCHED
  form by `s176_switchRestrictIso` (§F: the switched crossing `y` is deleted, so the two restricted records are
  literally identified on occurrences; bits/signs differ only at the deleted occurrences).
* `s176_hrec_wall` (§H): for the specific deleted crossings `lift u', lift v'`,
  `Nonempty (RecordIso (D₊.record.restrictCrossings (s176_wallKeep u' v')) D₀.record)`.  By
  `s176_hrec_unswitched_of_succ` its `e`, `Φ`, `comp_eq`, `pair_eq`, `bit_eq`, `sgn_eq` are PROVED from the accepted
  wall data (`est_retained_affected`, `est_not_retained_H`, `hR.sign_eq`, positivity); what remains is exactly
  **`hsucc : ∀ w, s176_wallΦ … ((D₊.record.restrictCrossings (s176_wallKeep u' v')).succ w) = D₀.record.succ
  (s176_wallΦ … w)`** — the first-return successor (`firstReturn D₊.visitSucc (CrossKeep …)`) of a retained L-side
  occurrence corresponds under `Φ` to the H-side successor.  Cost ≈ 500–700 lines: `CV.visitBetween_iff_key` on both
  lifts (cyclic order of the lifts = order of the parent visits' `geometricVisitKey`), `GT_Wall.key_lt` for every pair
  of retained parent visits (all non-triangle by `est_not_retained_H`, so `GT_not_rev_of_not_mem_left` applies; the
  wall is `est_wall`), and the uniqueness of the cyclic successor among the retained occurrences
  (`firstReturn_no_between` / `nextVisit_no_between` / `cycNext_unique_on`, the lemmas the W1 skeleton lists for its
  own open sub-leaf `m6_succ` — the same shape as `EXT_homfly_wall`'s `cyclic_order` clause with two deleted
  crossings).  Nothing else of `hrec` is open.

## 4. F-176-1 — the exact diff to RALedgers.lean (≈ 5 lines + the field type)

1. `est_PortData` (RALedgers:872): the field `port : Relation.ReflTransGen RII ((carrierDiagram hn hG' hS' q').switch y)
   (carrierDiagram hn hG hS q)` becomes `port : est_port_weak (carrierDiagram hn hG' hS' q') (carrierDiagram hn hG hS q) y`
   (`est_port_weak` from Statements_FINAL/SM.Link; add `open SM.Link` — already open in section `EST`).  Every other
   field unchanged (`s176_PortDataWeak` is the result, verbatim).
2. `est_omega1_eq_of_port` (:915): the line `have hft := CV.fulltwist_coefficient (CV.carrierDiagram hn hG hS q)
   (CV.carrierDiagram hn hG' hS' q') D.DA y hpos D.smooth D.port rfl rfl hd` becomes `have hft :=
   fulltwist_coefficient_of_port_weak (CV.carrierDiagram hn hG' hS' q') (CV.carrierDiagram hn hG hS q) D.DA y hpos D.smooth
   D.port rfl rfl hd` (note the ARGUMENT ORDER `Dp D₀`, the reverse of `fulltwist_coefficient`'s `D₀ D₊`); the rest of the
   body is byte-identical (`s176_est_omega1_eq_of_port_weak` replays it and compiles).
3. `est_port_relation` (:1453): `Nonempty (est_PortData …)` — unchanged text once `est_PortData` carries the weak field;
   `est_row_H`, `est_row`, `est_extremeTransportData`, `est_ledger`, `est_extreme_transport_of`: byte-identical
   (`s176_est_row_H_weak` etc. are the replays; `s176_est_ledger_weak` compiles).
4. Import: `fulltwist_coefficient_of_port_weak` lives in the moves toolkit (`SM/BigonDeletion.lean` per PLAN §3) — RALedgers
   would import it, or the lemma moves next to `CV.fulltwist_coefficient` (CV/FullTwist.lean; it uses only
   `CV.fulltwist_skein` + Laurent bookkeeping).
No row statement changes; the interface stays D-F11 (stated, never asserted).

## 5. Remaining consumer obligations of row 176 (beyond the site), with estimates

| obligation | where it enters | estimate |
|---|---|---|
| `hsucc` — the successor clause of `s176_hrec_unswitched_of_succ` (§3; everything else of `hrec` is proved) | `s176_hrec_wall_of_succ` → `s176_port_weak_of_event'` | ≈ 500–700 lines (PLAN §4.3's 1.0k minus the ≈ 300 proved here) |
| `s176_PortDataRest` items 2–5 of U_R176_REPORT §5: (T1) the oriented smoothing `D_A` of `D₊` at `y` with `componentCount = 2` (no existence theorem for oriented smoothings of a polygonal diagram in the library except `smoothDiagram`/`exists_smoothing_record_visit` — use those, as PLAN §4.2 recommends for 174), the exact owner map (9)/(9a) `poly₁ poly₂` (record iso of the component restrictions with the outer carriers `Λ₁, Λ₂` of `S_full`, lc:single-crossing for the kink), the linking number `ℓ`, the writhe ledger (14), the rotation ledger (13) (turnlift (ii) + corner ledger (12)), `alt₁ alt₂` | `s176_est_port_relation_weak_of`'s `hrest` | ≈ 3–4k lines (PLAN §7 "176 items 3–5"); NOT on any other unit's path |
| F-176-1 acceptance by the U-176 owner (§4) | RALedgers edit | 5 lines + field type |
| closing the frozen leaf `exists_bigonData_of_triangle` (U-M7) | `exists_bigon_switch₁/₂` | Wave 1 (not this site) |

## 6. Pitfalls met (for the 174 site, which shares the shape)

1. `rw` cannot rewrite `(D.switch y).overStrand y` inside `Eq` at type `(D.switch y).Γ.Strand` (motive not type-correct
   at implicit transparency); compose with `Eq.trans` instead (`same_over_switch₁`).
2. Numerals `0 : Fin (geoPositiveLift …).Γ.c` and `Subsingleton (Fin (geoPositiveLift …).Γ.c)` are NOT found by instance
   search (the `Γ.c` does not reduce at reducible transparency); write `(0 : Fin 1)` and prove `i = 0` by `Fin.ext` + `omega`
   after `change i.val < 1`.  On the abbrev `geoCarrierShadow = Shadow.single …` the numeral `0` and
   `Shadow.single_strand_eta` work.
3. `kA + 1` in the site's field type `y₂.val = {⟨i, a + 1⟩, s}` carries the `HAdd` instance of `ZMod ((D.Γ.comp i).k)`,
   syntactically different from `kA + 1 : ZMod (geoCornerCount …)`; `rw` with an equation stated on the latter fails —
   use `convert … using 2` + `show` (the `clear` field of `s176_cornerSite_case1`), or keep every site statement at the
   corner-polygon index level (`s176_clear_of_indices`) and convert once.
4. `s176_lift_val` is stated for `w : Visit P` with `⟨w.1, hw⟩`; instantiating at `visitOn u a _` gives
   `(visitOn u a _).1` syntactically, not `u` — take the instance with `have … := s176_lift_val …` (defeq) rather than `rw`.
5. Section variables not mentioned in a statement are not included (`include hn hT in`); an `include`d variable that a
   proof does not use is a linter error at call sites when later removed — keep call sites and `include` lists in sync.
6. `tauto` on `(z = a ∨ z = b ∨ z = c) ↔ (z = e ∨ z = f ∨ z = g)` over `ZMod n` hits the `whnf` heartbeat limit; prove the
   label permutations with `Finset.insert_comm` / `Finset.pair_comm`.
7. `D₊`/`D₀` are not identifiers (`₊` is not an identifier character); `Dp`, `D₀` are.
8. `push_neg` is deprecated in this toolchain (warning only); `not_or` rewrites do the job.
9. `obtain ⟨-, Tsite, hc⟩` on `∃ (hv' : Prop-witness) Tsite, P hv'` silently fails to clear `hv'` (the later components
   depend on it) and then `hc` is unbound — name the witness.
10. `est_liftCrossing hn hG hS q hc` is DEFINITIONALLY `(geoCarrierCrossingEquiv hn (CarrierGeometry.ofDiagrammatic
    (hG.diagrammatic hn)) (geoIndependent_of_mem_Ind _ hS) q).symm ⟨c, hc⟩` and `(CarrierGeometry.ofDiagrammatic
    ((genericAt E t ht).diagrammatic hn)).cg = geomAt E t ht` (both `rfl`, probed) — so the carrier-level theorem
    instantiates at the event level with no transport.

## 7. Notes

* The geometric reading: on the empty side `L` the carrier `q₀'` turns at `j'` and the third strand `c` (through `u', v'`)
  cuts the corner; the contact triangle is `conv{pt j', pt u', pt v'}` = the triangle of the three crossing points of
  `P'`, so the G11 Unit-A clearance toolkit applies verbatim for foreign edges and with a one-line change (the corner
  vertex IS in `K`) for the edges inside `a, b, c`.
* The site lemmas §C are stated for ANY carrier/independent support/labelled triangle with the corner selected and the
  two other crossings retained; the 174 site (`m`-corner of `carrierDiagram (τ qAB)`, PLAN §4.2) has the same shape
  and can reuse §A and §C directly (its `clear` is the same lemma; only the event-level plumbing §D differs).
* `s176_cyclic` shows the orientation dichotomy of the corner needs no sign data: retention of BOTH unselected
  crossings by one carrier already forces the corner to be "in–out".
