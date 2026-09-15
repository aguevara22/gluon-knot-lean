# CV-DOM unit U2b — REPORT (2026-09-14, ~03:16 UTC / 11:16pm ET)

Prover: Claude Code subagent (claude-fable-5-1) of the pod executor. Spec: work/drafts/cvdom/DECISION_FINAL.md
§0, §3 (rulings R1–R5) and §5 row **U2b**. Nothing under work/lean was written. Paths relative to the package root
/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912.

## Deliverable

| file | intended home | lines | status |
|---|---|---:|---|
| `work/drafts/cvdom/U2b/GeoCornerPolygon.lean` | `work/lean/SM/GeoCornerPolygon.lean` (new module, namespace `SM.GeoCarrier`, `open Carrier`, CV-free; imports `SM.GeoCarrierOrder`, `SM.GeoCarrierGeometry`) | 828 | `cd work/lean && lake env lean ../drafts/cvdom/U2b/GeoCornerPolygon.lean` → **exit 0, no output (no warnings), no `sorry`** (grep count 0) |

39 declarations (all `theorem`; no new `def`). `#print axioms` on every one of them (copy of the file with the lines
appended, /tmp): `[propext, Classical.choice, Quot.sound]` only (standard), 39/39.

Name safety (ruling R3): each of the 39 names grepped against every declaration head in work/lean (excluding `.lake`):
zero hits. No accepted `geo*` name is re-declared (`geoCornerMark_exists`, `geoCornerMark_add_one`, `geo_corner_chain`,
`geo_block_compression`, `geo_subsegment_data`, `geoCornerPolygon_edge/_edge_pred/_turn_det/_turn_eq_sign/_edge_ne_zero/
_not_antiparallel_of_det`, `geoCornerMark_injective`, `geoOwner_geoCornerMark`, `isTrueCorner_geoCornerMark`,
`geoComponentCornerCycle*` are referenced, not redefined). Distinct from the row-module lemmas of SM/CSilent.lean
(`SM.geoCornerPolygon_regular_of_weak (hn) (hW) (S) (q) (htr)`, `SM.exists_geoBlock`, `SM.geoCornerPolygon_*_of_weak`),
which are NOT imported (a library module must not depend on the prop:C-silent row module); see "Notes" below.

No `Generic`, `hP.1`-as-G1, `hP.2`, `independentSupports` or `IsDecomposition` anywhere in the file (`hP.1` appears once,
as `CrossingGeometry` clause 1 = edge ≠ 0, exactly where the source has `(g1 hn P hP.1).2.1 _`).

## §5 U2b targets — status (all proved)

| §5 target (shape as printed) | draft line | tier | status / note |
|---|---:|:-:|---|
| `geoCornerPolygon_edge_smul (hn) (hP) (hS) (q) (k) : ∃ c : ℝ, 0 < c ∧ edge (geoCornerPolygon hP S q) k = c • edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1` | 398 | 0 | **proved**, exact shape (`:= geoCornerPolygon_edge hn hP S q (geoTracedSuccessor_of_independent hn hP hS q) k`) |
| `geoCornerPolygon_trace (hn) (hP) (hS) (q) : (⋃ k, edgeSegment (geoCornerPolygon hP S q) k) = ⋃ a ∈ {a \| geoOwner hP S a = q}, geoSmoothingSegment hP S a '' Set.Icc 0 1` | 747 | 0 | **proved**, exact shape (sides in the §5 order; the source `ccpCornerPolygon_trace` has them swapped) |
| `geoCornerPolygon_regular (hn) (hG : CarrierGeometry P) (hS) (q) : Regular (geoCornerPolygon hG.cg S q)` | 631 | **1** | **proved** at tier 1 as ruling R4 prescribes, via U0's `CarrierGeometry.regular hn` (the fold-back exclusion) at vertex corners and `CrossingGeometry` clause 2 (`crossing_det_ne_zero_of_geometry`) at smoothing corners. No tier-2 need arose (risk 3 of §7 discharged for this group). |
| `three_le_geoCornerCount (hn) (hW : WeakGeneric P) (hS) (q) : 3 ≤ geoCornerCount (weak_crossingGeometry hW) S q` ["tier 2 as in the source; try tier 1 first"] | 644 (+678) | **1** | **proved at tier 1**: `three_le_geoCornerCount (hn) (hG : CarrierGeometry P) (hS : GeoIndependent hG.cg S) (q) : 3 ≤ geoCornerCount hG.cg S q`. The §5-printed tier-2 shape is the corollary `three_le_geoCornerCount_of_weak (hn) (hW) (hS) (q) : 3 ≤ geoCornerCount (weak_crossingGeometry hW) S q` (line 678, `:= three_le_geoCornerCount hn hW.carrierGeometry hS q`, proof irrelevance identifies the two `CrossingGeometry` proofs). **Consequence for U4/U7c:** `geoCarrierPolyComp`, `geoCarrierShadow`, `geoPositiveLift` can take `hG : CarrierGeometry P` (no `hW` fallback needed for the count). |
| `geoCornerPolygon_turn_ne_zero (hn) (hW) (hS) (q) (k)` | 578 | 2 | **proved**: `turn (geoCornerPolygon (weak_crossingGeometry hW) S q) k ≠ 0`; plus the `geoCornerTurn` form `geoCornerTurn_ne_zero (hn) (hW) (hS) (a) : geoCornerTurn (weak_crossingGeometry hW) S a ≠ 0` (588) |
| `geoCornerPolygon_turn_vertex (hn) (hP) (hS) (q) (k) (i) (h : geoCornerMark hP S q k = Sum.inl i) : turn (geoCornerPolygon hP S q) k = turn P i` | 442 | 0 | **proved**, exact shape |
| `geoCornerPolygon_turn_visit (hn) (hP) (hS) (q) (k) (v) (hv : v.1 ∈ S) (h : geoCornerMark hP S q k = Sum.inr v) : turn (geoCornerPolygon hP S q) k = crossingSign P v.2.val (visitTwin v).2.val` | 452 | 0 | **proved**, exact shape (argument order `(v) (hv) (h)` as in §5) |
| `geoCornerPolygon_turn_visit_twin (hn) (hP) (hS) (v) (hv)` ("one left one right") | 484 | 0 | **proved**: the full port of `ccp_selected_crossing_two_corners` — `q ≠ q'` (owners of `v` and its twin differ, U1a `geo_selected_visits_separated`), corner indices `k`, `k'` with `geoCornerMark … = Sum.inr v / Sum.inr (visitTwin v)`, turns `crossingSign P i j` / `crossingSign P j i`, `turn' = -turn`, and `(1, -1) ∨ (-1, 1)`. Tier 0 (the source used `turn ≠ 0`; here the smoothing-corner turn is nonzero by `CrossingGeometry` clause 2, `geoCornerPolygon_turn_visit_ne_zero`, 473). |
| block parametrisation / actual corner block | 61–175, 326 | 0 | **proved**: port of CarrierActualCornerBlock (`geoComponentMarkList_rotate_start`, `geoComponentCornerCycle_eq_filter_of_list`, `geoComponent_first_trueCorner_block`), the corner-cycle chain `geo_corner_chain_of_independent`, the full compressed block `geoCornerPolygon_block` (all eight clauses of `ccpCornerPolygon_block`, incl. the union-of-segments trace), and `geo_block_compression_trace` (the union clause the accepted `geo_block_compression` omits) |

Nothing left unproved; no obstacle. **One deviation from the §5 text, in the direction §5 asks for:** `three_le_geoCornerCount`
is at tier 1 (`hG : CarrierGeometry P`), with the printed tier-2 binder available as `three_le_geoCornerCount_of_weak`.
Everything else has its §5 binder list.

## Ported declarations (source → geo name, tier, hand edits)

"verbatim" = the source proof with the renaming `X hn hP → geoX hP`, `markPosition hn hP.1 → geoMarkPosition hP`,
`smoothingSuccessor → geoSmoothingSuccessor`, `owner → geoOwner`, `Component → GeoComponent`, `componentMarkList →
geoComponentMarkList`, `componentCornerCycle → geoComponentCornerCycle`, `componentCycle → geoComponentCycle`,
`ccpOutSlot → geoOutSlot`, `ccpInEdge → geoInEdge`, `ccpCornerList → geoComponentCornerList`, `ccpCornerCount →
geoCornerCount`, `ccpCornerMark → geoCornerMark`, `ccpCornerPolygon → geoCornerPolygon`, `smoothingSegment →
geoSmoothingSegment`, `S ∈ independentSupports hn hP → GeoIndependent hP S`; the `TracedSuccessor` argument `htr` of the
accepted corner-polygon lemmas is always `geoTracedSuccessor_of_independent hn hP hS q` (U1b). Hypothesis-free source
lemmas (`ccp_pow_apply_closed_list`, `ccp_image_affine_unit`, `ccp_det_smul_smul`, `ccp_not_trueCorner`, `firstCornerBlock`,
`edgePoint_affine`, `edgePoint_sub_edgePoint`, `visit_crossing_val_eq_pair`, `visitTwin_*`) are shared through `open Carrier`.

### SM/CarrierActualCornerBlock.lean (143 lines) → §0

| source | geo | tier | hand edits |
|---|---|:-:|---|
| `componentMarkList_rotate_start (hn) (hP) (S) (q) (a) (ha)` | `geoComponentMarkList_rotate_start (hP) (S) (q) (a) (ha)` | 0 | verbatim; `componentMarkList_data → geoComponentMarkList_data` (U1b); `hn` dropped |
| `componentCornerCycle_eq_filter_of_list` | `geoComponentCornerCycle_eq_filter_of_list (hP) (S) (q) (L) (hL)` | 0 | verbatim; `hn` dropped |
| `component_first_trueCorner_block (hn) (hP) {S} (hS) (q) (a) (ha) (hac)` | `geoComponent_first_trueCorner_block (hP) {S} (hS : GeoIndependent hP S) (q) (a) (ha) (hac)` | 0 | verbatim; `componentCycle_list_nodup/_mem_iff → geoComponentCycle_list_nodup/_mem_iff` (U1a); `componentCycle_list_eqOn hn hP S (independent_inheritsMarkOrder hn hP hS) → geoComponentCycle_list_eqOn hP S (geoInheritsMarkOrder_of_independent hP hS)` (U1a); `hn` dropped |

### SM/CarrierCornerPolygon.lean §3–§10 (lines 258–859) → §1–§7

| source | geo | tier | hand edits |
|---|---|:-:|---|
| §3 `ccp_pow_apply_closed_list` | shared (hypothesis-free) | — | not re-declared |
| §3 `ccp_corner_chain (hn) (hP) (hS) (q) (a) (ha) (hac)` (corner-cycle `next`) | `geo_corner_chain_of_independent (hP) (hS) (q) (a) (ha) (hac)` | 0 | verbatim from `geoComponent_first_trueCorner_block`; `hn` dropped. (The corner-LIST form is the accepted `geo_corner_chain hP S q htr`, FlatCarriers.lean:3185; the block lemma below uses that one, as `geoCornerPolygon_edge_data` does.) |
| §4 `ccpCornerList`, `ccpCornerCount`, `ccpCornerCount_neZero`, `ccpCornerMark`, `ccpCornerPolygon`, `ccpCornerList_nodup`, `mem_ccpCornerList`, `ccpCornerList_length_pos` | accepted `geoComponentCornerList`, `geoCornerCount`, `geoCornerCount_neZero`, `geoCornerMark`, `geoCornerPolygon`, `geoComponentCornerList_nodup`, `mem_geoComponentCornerList`, `geoComponentCornerList_length_pos` (FlatCarriersDefs) | 0 | not re-declared |
| §4 `ccpCornerList_coe` | `geoComponentCornerList_coe` | 0 | `rfl` (`geoComponentCornerCycle` is U1a's, GeoCarrierCount:1685) |
| §4 `ccpCornerPolygon_apply` | `geoCornerPolygon_apply` | 0 | `rfl` |
| §4 `ccpCornerMark_mem`, `_owner`, `_isTrueCorner`, `_mem_cornerCycle`, `_injective`, `_add_one` | accepted `geoCornerMark_mem` (FlatCarriers:3160), `geoOwner_geoCornerMark` / `isTrueCorner_geoCornerMark` / `geoCornerMark_injective` (FlatCarriers:4894–4907, namespace `SM`), `geoCornerMark_add_one` (FlatCarriers:3172); NEW `geoCornerMark_mem_cornerCycle` | 0 | only the cornerCycle-membership form added |
| §4 `ccpCornerMark_exists (q) (a) (ha : owner = q) (hac)` | `geoCornerMark_exists_of_owner (hP) (S) (q) (a) (ha) (hac)` | 0 | NEW wrapper: `subst ha; exact geoCornerMark_exists hP S hac` (the accepted `geoCornerMark_exists` is stated at `q = geoOwner hP S a`, FlatCarriersDefs:408) |
| §0 `ccp_subsegment_data` (with the affine formula) | `geo_subsegment_trace_data (hn) (hP) (S) (a)` | 0 | from the accepted `geoSmoothingSegment_subsegment_data hn` (the accepted `geo_subsegment_data` drops the formula clause the trace needs) |
| §1 `ccp_smoothingSegment_image (hn) (hP) (S) (a) (hst) (hf)` | `geo_smoothingSegment_image (hP) (S) (a) (hst) (hf)` | 0 | verbatim; `hn` dropped |
| §2 `ccp_block_compression` (with the union-of-images clause) | `geo_block_compression_trace (hn) (hP) (S) (a) (m) (hm) (hmid)` | 0 | verbatim (the accepted `geo_block_compression`, FlatCarriers:3080, is the same induction without the union clause, so the full statement is re-proved rather than derived); `(g1 hn P hP.1).2.1 _ → hP.1 _`; `ccp_incoming_visit_position → geo_incoming_visit_position` (accepted) |
| §5 `ccpCornerPolygon_block (hn) (hP) (hS) (q) (j)` | `geoCornerPolygon_block (hn) (hP) (hS) (q) (k)` | 0 | verbatim; `ccp_corner_chain hn hP hS … → geo_corner_chain hP S q htr …` with `htr := geoTracedSuccessor_of_independent hn hP hS q`; `ccpCornerMark_add_one → geoCornerMark_add_one` |
| §5 `ccpCornerPolygon_edge` | **`geoCornerPolygon_edge_smul`** (§5 target) | 0 | one-liner on the accepted `geoCornerPolygon_edge … htr` |
| §5 `ccpCornerPolygon_outEdge_eq_inEdge`, `_edge_pred` | `geoCornerPolygon_outEdge_eq_inEdge_of_independent`, `geoCornerPolygon_edge_pred_smul` | 0 | one-liners on the accepted `htr` forms |
| §6 `ccp_det_smul_smul` | shared | — | not re-declared |
| §6 `ccpCornerPolygon_turn_det`, `_turn_eq_sign` | accepted `geoCornerPolygon_turn_det/_turn_eq_sign … htr`; `hS` form `geoCornerPolygon_turn_eq_sign_of_independent` | 0 | one-liner |
| §6 `ccp_corner_directions_det_ne_zero (hn) (hP : Generic) (S) (a) (ha)` | split: `geo_visit_corner_det_ne_zero (hn) (hP) (S) (v) (hv)` [tier 0], `geo_vertex_corner_det_ne_zero (hn) (hW) (S) (i)` [tier 2], `geo_corner_directions_det_ne_zero (hn) (hW) (S) (a) (ha)` [tier 2] | 0 / 2 | G1 site 556 (`turn P i ∈ {±1}` from `g1`) → `hW.2.1 i : turn P i ≠ 0` (`WeakGeneric` clause 2); site 567 `crossing_det_ne_zero_of_geometry (generic_crossingGeometry hn hP) → crossing_det_ne_zero_of_geometry hP` |
| §6 `ccpCornerPolygon_det_ne_zero` | `geoCornerPolygon_det_ne_zero (hn) (hW) (hS) (q) (k)` | 2 | verbatim |
| §6 `ccpCornerPolygon_turn_ne_zero` | **`geoCornerPolygon_turn_ne_zero`** (§5 target) + `geoCornerTurn_ne_zero` (`geoCornerTurn` form) | 2 | verbatim / `unfold geoCornerTurn` |
| §6 `ccpCornerPolygon_turn_vertex` | **`geoCornerPolygon_turn_vertex`** (§5 target) + `geoCornerTurn_vertex (hn) (hP) (hS) (i) : geoCornerTurn hP S (Sum.inl i) = turn P i` | 0 | verbatim (`ccpInEdge_vertex → geoInEdge_vertex hn hP`) |
| §6 `ccpCornerPolygon_turn_smoothing (q) (j) (v) (hj) (hv)` | **`geoCornerPolygon_turn_visit (q) (k) (v) (hv) (h)`** (§5 target) + `geoCornerTurn_visit (hn) (hP) (hS) (v) (hv) : geoCornerTurn hP S (Sum.inr v) = crossingSign P v.2.val (visitTwin v).2.val` | 0 | verbatim, §5 argument order |
| §6 `ccp_selected_crossing_two_corners` | **`geoCornerPolygon_turn_visit_twin`** (§5 target) | 0 | verbatim except: `ccpCornerPolygon_turn_ne_zero` (tier 2) → `geoCornerPolygon_turn_visit_ne_zero` (tier 0, NEW: smoothing-corner turn ≠ 0 from clause 2); G1 site 665 `independent_selected_pair_owners_ne hn hP hS → geo_selected_visits_separated hP hS` (U1a) |
| §7 `ccpCornerPolygon_edge_ne_zero` | `geoCornerPolygon_edge_ne_zero_of_independent` | 0 | one-liner on the accepted `htr` form (G1 site 195 → `hP.1 _` there) |
| §7 `ccpCornerPolygon_not_antiparallel (hn) (hP : Generic) (hS) (q) (j)` | `geoCornerPolygon_not_antiparallel (hn) (hG : CarrierGeometry P) (hS) (q) (k)` | **1** | REWRITTEN (ruling R4): the source derives it from `det ≠ 0` (tier 2 at vertices). Here: case on `geoCornerMark hG.cg S q k`; vertex `i`: `edge k = c₂ • edge P i`, `edge (k-1) = c₁ • edge P (i-1)` (accepted `geoCornerPolygon_edge/_edge_pred`), so `edge k = r • edge (k-1)` with `r < 0` gives `edge P i = (c₂⁻¹ (r c₁)) • edge P (i-1)` with a negative coefficient, against `(hG.regular hn i).2.2` (U0 `CarrierGeometry.regular`); visit `v`: accepted `geoCornerPolygon_not_antiparallel_of_det` with `geo_visit_corner_det_ne_zero` |
| §7 `ccpCornerPolygon_regular` | **`geoCornerPolygon_regular`** (§5 target) + tier-2 corollary `geoCornerPolygon_regular_of_weakGeneric (hn) (hW) (hS) (q)` | **1** | verbatim (`regular_iff_edges`) on the two tier-≤1 inputs |
| §8 `ccpCornerCount_ge_three` | **`three_le_geoCornerCount (hn) (hG) (hS) (q)`** (§5 target) + `three_le_geoCornerCount_of_weak` (printed tier-2 shape) | **1** | verbatim except the `k = 2` case: `ccpCornerPolygon_det_ne_zero … 0` (tier 2) → `geoCornerPolygon_not_antiparallel … 0 ⟨-1, by norm_num, by rw [hopp, neg_one_smul]⟩` (tier 1) |
| §9 `ccp_pow_owner` | `geo_pow_owner (hP) (S) (a) (r)` | 0 | verbatim (`owner_eq_iff → geoOwner_eq_iff`); `hn` dropped |
| §9 `ccp_previous_corner` | `geo_previous_corner (hP) (S) (q) (x) (hx)` | 0 | verbatim (`component_has_trueCorner → geoComponent_has_trueCorner`); `hn` dropped |
| §9 `ccpCornerPolygon_edgeSegment` | `geoCornerPolygon_edgeSegment (hP) (S) (q) (k)` | 0 | verbatim; `hn` dropped |
| §9 `ccpCornerPolygon_trace` | **`geoCornerPolygon_trace`** (§5 target) | 0 | verbatim with the two `antisymm` bullets swapped (§5 states the polygon side first) |
| §10 `carriers_clause_ii (hn) (hP : Generic) (hS)` | `geo_carriers_clause_ii (hn) (hW : WeakGeneric P) (hS)` | 2 | verbatim shape (eight clauses) on `hP := weak_crossingGeometry hW`; tier 2 only because of the nonzero-turn clause — clauses 1, 2, 7, 8 are tier 0 and clauses 3, 4, 5 tier 1 above |

## Method

1. Read DECISION_FINAL §0/§3/§5, the two sources, the accepted geo layer (FlatCarriersDefs §3; FlatCarriers 2996–3425:
   `geoOutSlot` … `geoCornerPolygon_not_antiparallel_of_det`, the generic-transfer pattern, TurnBookkeeping 4887–4938),
   GeoCarrierGeometry (U0), GeoCarrierCount (U1a: `geoComponentCornerCycle`, the `geoComponentCycle_list_*` lemmas,
   `geo_selected_visits_separated`, `geoInheritsMarkOrder_of_independent`), GeoCarrierOrder (U1b:
   `geoComponentMarkList_data`, `geoTracedSuccessor_of_independent`), and CSilent.lean 430–1300 (to see what the row
   module already holds on the geo polygon — not imported, see Notes).
2. Hand port (the transformer's DEFMAP covers the renaming; the file is short enough that the residue — dropping the
   accepted §0–§2 declarations, replacing `htr`, the two R4 rewrites, the 4 `Generic` sites — was done by hand on the
   source text directly).
3. One compile round: `lake env lean` exit 0 with no output on the first pass (6.7 s); `#print axioms` standard on all
   39; name grep clean.

## Notes for the assembler and downstream units (U2c, U3, U4, U7a/b/c)

- **Import graph.** `SM.GeoCornerPolygon` imports `SM.GeoCarrierOrder` (→ `SM.GeoCarrierCount` → `SM.FlatCarriers`) and
  `SM.GeoCarrierGeometry` (→ `SM.FlatCarriersDefs`, `SM.RegularLocus`). CV-free; picked up by the lakefile glob `SM.+`.
- **Tier-1 group is fully tier 1.** `geoCornerPolygon_regular`, `geoCornerPolygon_not_antiparallel`,
  `three_le_geoCornerCount` all take `hG : CarrierGeometry P` and produce statements about `geoCornerPolygon hG.cg S q`.
  A consumer holding `hD : CV.Diagrammatic P` uses `CarrierGeometry.ofDiagrammatic hD` (U0, CV/Carriers.lean draft) and
  `hS : GeoIndependent (CarrierGeometry.ofDiagrammatic hD).cg S` is accepted for `hS : S ∈ Ind hD.crossingGeometry` after
  `CV.mem_Ind_iff_geoIndependent` (proof irrelevance identifies the `CrossingGeometry` proofs; `three_le_geoCornerCount_of_weak`
  is the compiled demonstration of this mixing). So U4's `geoCarrierPolyComp (hn) (hG : CarrierGeometry P) (hS) (q) :=
  ⟨geoCornerCount hG.cg S q, three_le_geoCornerCount hn hG hS q, geoCornerPolygon hG.cg S q⟩` is statable exactly as §5
  writes it, with no `hW` fallback.
- **For U7a (138 def:wind, last three fields) and U7b (164 selector_A):** `geoCornerTurn_vertex hn hP hS i`,
  `geoCornerTurn_visit hn hP hS v hv` (tier 0, on the accepted `geoCornerTurn`), `geoCornerTurn_ne_zero hn hW hS a`
  (tier 2) and `geoCornerPolygon_turn_ne_zero hn hW hS q k`; `three_le_geoCornerCount hn (CarrierGeometry.ofCV hG) hS q`
  for selector_A's `3 ≤ geoCornerCount hG.crossingGeometry S q`.
- **For U3 (`geoCarrierRotationInt`):** `geoCornerPolygon_regular hn hG hS q : Regular …` is the input of
  `rotationNumber_integer`; `geo_carriers_clause_ii` is the one-shot bundle if `GeoCarriersLemmaData` prefers it.
- **For U4 (tail-off / transverse / no-triple) and U2c:** the full block with its trace is `geoCornerPolygon_block hn hP hS q k`
  (eight clauses: chain length `m`, `ρ_S^m c_k = c_{k+1}`, intermediates are unselected visits on `e` with strictly
  increasing slot parameters, all slots on `e`, `c • edge P e`, `e = geoInEdge c_{k+1}`, union of the `m` segment images =
  the straight edge segment). SM/CSilent.lean (row prop:C-silent, `namespace SM`) already holds, at tier 0 with `htr`, a
  richer per-edge block record `GeoBlock hP S q k t` / `exists_geoBlock hn hP S q htr k` (mark-position clauses:
  `interior_mark`, `start_mark`, `end_mark`, `end_vertex`) and the tier-2 meeting lemmas `geoCornerPolygon_meet_same_edge`
  (tier 0), `_meet_next_edge (hreg : Regular P)`, `_meet_remote_edge`, `_tail_off_of_weak`, `_transverse_of_weak`,
  `_no_triple_of_weak` (CSilent.lean 556–1300). U4 should re-home / re-bind those to `CarrierGeometry` in
  SM/GeoPositiveLift.lean rather than import the row module; `_meet_next_edge` already takes only `Regular P`, which is
  U0's `hG.regular hn`, so the tier-1 re-binding looks mechanical.
- **Call shapes that differ from the source:** `geoCornerMark_exists_of_owner hP S q a ha hac` (source
  `ccpCornerMark_exists`), `geo_subsegment_trace_data hn hP S a` (source `ccp_subsegment_data`),
  `geo_block_compression_trace hn hP S a m hm hmid` (source `ccp_block_compression`), `geo_smoothingSegment_image hP S a hst hf`
  (no `hn`). Everything named in §5 has its §5 binder list; `three_le_geoCornerCount` has the tier-1 binder and
  `three_le_geoCornerCount_of_weak` the printed one.
- **Time.** ≈ 1.5 h including reading the decision, the two sources, the accepted geo layer and the three landed units,
  writing, one compile round and this report.
