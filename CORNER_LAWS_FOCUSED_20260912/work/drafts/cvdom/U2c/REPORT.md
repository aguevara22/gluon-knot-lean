# CV-DOM unit U2c — REPORT (2026-09-14, ~03:30 UTC / 11:30pm ET)

Prover: Claude Code subagent (claude-fable-5-1) of the pod executor. Spec: work/drafts/cvdom/DECISION_FINAL.md
§0, §3 (rulings R1–R5) and §5 row **U2c**. Nothing under work/lean was written. Paths relative to the package root
/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912.

## Deliverable

| file | intended home | lines | status |
|---|---|---:|---|
| `work/drafts/cvdom/U2c/GeoCarrierSelfIntersections.lean` | `work/lean/SM/GeoCarrierSelfIntersections.lean` (new module, namespace `SM.GeoCarrier`, `open Carrier`, CV-free; imports `SM.GeoCarrierCrossings` (U2a) and `SM.GeoCarrierGeometry` (U0); picked up by the lakefile glob `SM.+`) | 869 | `cd work/lean && lake env lean ../drafts/cvdom/U2c/GeoCarrierSelfIntersections.lean` → **exit 0, no output (no warnings), no `sorry`** (grep count 0); ~6 s |

40 declarations (4 `def`, 36 `theorem`). `#print axioms` on every one of them (copy of the file with the 40 lines
appended, /tmp/U2c_axioms.lean): `[propext, Classical.choice, Quot.sound]` only (standard), 40/40.

Name safety (ruling R3): each of the 40 names grepped against every declaration head in work/lean (excluding `.lake`):
zero hits. No accepted `geo*` name is re-declared (`geoSmoothingSuccessor_apply`, `geoSmoothingSegment_*`,
`geoMarkPosition_*`, `geoOwner_successor`, `geoMarkSuccessor_position_cases`, `geoMarkSuccessor_no_mark_between`,
`geoSelectedMarkPerm_evaluation`, `geo_unselected_visit_outgoing_direction`, `geo_visit_incoming_direction`,
`geoCarrierCrossings` are referenced, not redefined; `csi_det_smul_smul` is hypothesis-free and shared through
`open Carrier`). No `Generic P`, `hP.2`, `independentSupports`, `IsDecomposition` anywhere except §11 (agreement lemmas,
which are ABOUT SM-generic polygons) — `hP.1` appears only as `CrossingGeometry` clause 1 (edge ≠ 0).

## §5 U2c target — status

| §5 target (shape as printed) | draft line | tier | status |
|---|---:|:-:|---|
| `geo_self_intersections (hn) (hG : CarrierGeometry P) (hS) (q)` "with the exact shape of `CarriersLemmaData.self_intersections` (CarriersLemma.lean:50-70)" | 761 | **1** | **proved.** Binder list `(hn : 3 ≤ n) {P} (hG : CarrierGeometry P) {S} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)` (same implicitness pattern as U2b's `geoCornerPolygon_regular` and U2a's `geo_noncrossing`). **Shape check, mechanical:** the field body of `CarriersLemmaData.self_intersections` (SM/CarriersLemma.lean, the `∀ q, …` body) with the textual renaming `IsSelfIntersection hn hP S ↦ GeoIsSelfIntersection hG.cg S`, `IsTriplePoint hn hP S ↦ GeoIsTriplePoint hG.cg S`, `carrierCrossings hn hP S ↦ geoCarrierCrossings hG.cg S`, `smoothingSegment hn hP S ↦ geoSmoothingSegment hG.cg S`, `markPosition hn hP.1 ↦ geoMarkPosition hG.cg` is, after whitespace normalisation, **character-for-character equal** to the statement of `geo_self_intersections` (python diff, `EXACT MATCH after renaming: True`). |
| tier-2 corollary (not asked; for consumers holding the def:wind binder) | 790 | 2 | `geo_self_intersections_of_weak (hn) (hW : WeakGeneric P) (hS : GeoIndependent (weak_crossingGeometry hW) S) (q)` `:= geo_self_intersections hn hW.carrierGeometry hS q` (proof irrelevance identifies the two `CrossingGeometry` proofs). |

Nothing left unproved; no obstacle. **No tier deviation from R4:** every declaration is tier 0 or tier 1; tier 2
(`WeakGeneric`) is not used anywhere except in the optional `_of_weak` corollary's binder.

## Ported declarations (source → geo name, tier, hand edits)

"verbatim" = the source proof under the renaming `X hn hP → geoX hP`, `markPosition hn hP.1 → geoMarkPosition hP`,
`smoothingSuccessor → geoSmoothingSuccessor`, `smoothingSegment → geoSmoothingSegment`, `owner → geoOwner`,
`Component → GeoComponent`, `carrierCrossings → geoCarrierCrossings`, `S ∈ independentSupports hn hP → GeoIndependent hP S`,
plus the U2c-specific `csiX → geoCsiX`, `csi_X → geoCsi_X`, `carrier_X → geo_carrier_X`, `IsCarrierParameter →
GeoIsCarrierParameter`, `carrierTrace → geoCarrierTrace`, `IsSelfIntersection → GeoIsSelfIntersection`, `IsTriplePoint →
GeoIsTriplePoint` (the §5 DEFMAP extension). `hn` dropped where no consumed lemma takes it (as U2a/U2b did); kept where
`geoMarkSuccessor_position_cases hn`, `geoSmoothingSegment_injective hn` or the FlatCarriers §3 direction lemmas need it,
and on the §5 target.

### SM/CarrierSelfIntersections.lean §0 → U0 (not re-declared)

| source | geo | tier |
|---|---|:-:|
| `csi_vertex_not_mem_edgeInterior (hn) (hP : G1 P)` | U0 `cg_vertex_not_mem_edgeInterior (hG)` (SM/GeoCarrierGeometry.lean §4) | 1 |
| `csi_crossingPoint_ne_vertex (hn) (hP : G1 P)` | U0 `cg_crossingPoint_ne_vertex (hG) (c) (k)` | 1 |

### §1–§3 → §1–§3 (tier 0; the analysts' prototype work/drafts/cvdom/CarrierGeometry.lean, word for word, only the per-declaration `{P : LabelledTuple n}` binder added)

| source | geo | hand edits |
|---|---|---|
| `csiEdge (hn) (hP : Generic) (S) (a)`, `csiStart` | `geoCsiEdge (hP : CrossingGeometry P) (S) (a)`, `geoCsiStart` | `markPosition hn hP.1 → geoMarkPosition hP` |
| `csiStart_nonneg`, `csiStart_lt_one` | `geoCsiStart_nonneg`, `geoCsiStart_lt_one` | verbatim |
| `csi_smoothingSuccessor_eq` | accepted `geoSmoothingSuccessor_apply` (FlatCarriersDefs:239) | not re-declared |
| `csi_evaluation_start` | `geoCsi_evaluation_start (hP) (S) (a)` | `selectedMarkPerm_evaluation hn hP.1 → geoSelectedMarkPerm_evaluation hP` |
| `csi_segment_data (hn)` | `geoCsi_segment_data (hn) (hP) (S) (a)` | `markSuccessor_position_cases hn hP → geoMarkSuccessor_position_cases hn hP` |
| `csi_no_mark_in_gap (hn)` | `geoCsi_no_mark_in_gap (hn) (hP) (S) (a m) (t) …` | `markSuccessor_no_mark_between hn hP → geoMarkSuccessor_no_mark_between hP` (accepted, FlatCarriers:361) |
| `csi_same_edge_disjoint_of_lt`, `csi_same_edge_disjoint (hn)` | `geoCsi_same_edge_disjoint_of_lt`, `geoCsi_same_edge_disjoint (hn) (hP) (S) {a b} (hab) (he) …` | G1 site l.205 `g1_edge_ne_zero hn hP.1 → hP.1`; `markPosition_injective hn hP → geoMarkPosition_injective hP` |

### §4 → §4 (tier 1 — the R1/R4 re-binding of the prototype's `CornerGeometry` lemmas)

| source | prototype | geo (this unit) | hand edits |
|---|---|---|---|
| `csi_edgeSegment_meet (hn) (hP : G1 P) {i j} (hij) {x} (hxi) (hxj)` | `cg_edgeSegment_meet (hG : CornerGeometry P) …` via `turns_adjacent_intersection hG.turn_ne` (tier 2) | **`cg_edgeSegment_meet (hn : 3 ≤ n) (hG : CarrierGeometry P) {i j} (hij) {x} (hxi) (hxj)`** | adjacent case: `hG.adjacent_edges_meet hn hij hadj` (U0's fold-back exclusion, same `(j = i+1 ∧ … = {P j}) ∨ (i = j+1 ∧ … = {P i})` shape, so the two bullets are verbatim); remote case: `crossingPoint_unique → crossingPoint_unique_of_geometry hG.cg`. **Takes `hn` now** (the fold-back lemma needs `n ≥ 3`), which the prototype's tier-2 version did not. |
| `csi_edge_mem_of_crossingPoint_mem (hn) (hP : Generic)` | `cg_edge_mem_of_crossingPoint_mem (hG : CornerGeometry P)` | **`cg_edge_mem_of_crossingPoint_mem (hn) (hG : CarrierGeometry P) (c) {e} (hx)`** | `generic_crossingPoint_injective hn hP → crossingPoint_injective_of_geometry hG.cg`; `csi_crossingPoint_ne_vertex → cg_crossingPoint_ne_vertex hG` |

Names: the prototype's `cg_` prefix is kept for these two (they are lemmas about a `CarrierGeometry` polygon with no
carrier data, exactly the class U0 named `cg_vertex_not_mem_edgeInterior` / `cg_crossingPoint_ne_vertex`), so the
analysts' documents (ANALYSIS_A.md §3, the prototype) keep pointing at the right names.

### §5–§6 → §5–§6 (tier 1)

| source | geo | hand edits |
|---|---|---|
| `csi_trace_eq_vertex (hn) (hP : Generic)` | `geoCsi_trace_eq_vertex (hn) (hG : CarrierGeometry P) (S) (a) {u} (hu0) (hu1) (k) (h)` | prototype §5 verbatim (`g1_vertex_not_mem_edge hP.1 → hG.vertex_not_mem_edge hk0 hk1`, U0's form) |
| `csi_trace_eq_crossingPoint (hn) (hP : Generic)` | `geoCsi_trace_eq_crossingPoint (hn) (hG) (S) (a) {u} (hu0) (hu1) (c) (h)` | NEW port: `csi_edge_mem_of_crossingPoint_mem → cg_edge_mem_of_crossingPoint_mem hn hG`; the `rfl` position record `hpos0` now carries `(crossingParameter_interior_of_geometry hG.cg c e hec).1.le / .2` in place of `visitPosition_interior hn hP.1 w0` (it is `rfl` against `geometricVisitPosition`, GeometricVisits.lean:12) |
| `csi_trace_meet (hn) (hP : Generic)` | `geoCsi_trace_meet (hn) (hG) (S) {a b} (hab) {u v} … (h)` | `smoothingSegment_mem_edgeSegment hn hP S a hu0 hu1.le → geoSmoothingSegment_mem_edgeSegment hG.cg S a u hu0 hu1.le` (the accepted lemma takes `u` explicitly); `csi_edgeSegment_meet hn hP.1 → cg_edgeSegment_meet hn hG` |

### §7 → §7 (definitions tier 0; lemmas tier 1 unless noted)

| source | geo | hand edits |
|---|---|---|
| `IsCarrierParameter (hn) (hP) (S) (q) (p)` | **`GeoIsCarrierParameter (hP : CrossingGeometry P) (S) (q : GeoComponent hP S) (p : Mark P × ℝ) : Prop`** | body verbatim (`geoOwner hP S p.1 = q ∧ 0 ≤ p.2 ∧ p.2 < 1`) |
| `carrierTrace` | **`geoCarrierTrace (hP) (S) (p) : Plane := geoSmoothingSegment hP S p.1 p.2`** | verbatim |
| `IsSelfIntersection`, `IsTriplePoint` | **`GeoIsSelfIntersection (hP) (S) (q) (x)`**, **`GeoIsTriplePoint (hP) (S) (q) (x)`** | verbatim |
| `csi_mark_ne_of_param_ne (hn) (hP : Generic)` | `geoCsi_mark_ne_of_param_ne (hn) (hP : CrossingGeometry P) (S) {p p'} (hne) (h)` [tier 0] | `smoothingSegment_injective hn hP → geoSmoothingSegment_injective hn hP` (U1b) |
| `carrier_crossingPoint_parameters` | `geo_carrier_crossingPoint_parameters (hn) (hG) (S) (q) (c) (p)` | `smoothingSegment_zero → geoSmoothingSegment_zero` (U1b), `markPosition_evaluation_visit → geoMarkPosition_evaluation_visit` |
| `carrier_vertex_parameters` | `geo_carrier_vertex_parameters (hn) (hG) (S) (q) (k) (p)` | idem with `_vertex` |
| `csi_owned_marks_meet (hn) (hP) {S} (hS : S ∈ independentSupports) (q) …` | `geoCsi_owned_marks_meet (hn) (hG) {S} (hS : GeoIndependent hG.cg S) (q) {a b} (ha) (hb) (hab) {u v} … (h)` | G1 site: `independent_selected_pair_owners_ne hn hP hS w → geo_selected_visits_separated hG.cg hS w` (U1a, GeoCarrierCount:1727); `mem_carrierCrossings → mem_geoCarrierCrossings` (U2a) |
| `carrier_selfIntersection_iff` | `geo_carrier_selfIntersection_iff (hn) (hG) {S} (hS) (q) (x)` | verbatim |
| `carrier_selected_not_selfIntersection` | `geo_carrier_selected_not_selfIntersection (hn) (hG) {S} (hS) (q) {c} (hc : c ∈ S)` | G1 site l.534 `generic_crossingPoint_injective → crossingPoint_injective_of_geometry hG.cg`; `selected_not_mem_carrierCrossings → geo_selected_not_mem_carrierCrossings hG.cg S q hc` (U2a) |
| `carrier_vertex_not_selfIntersection` | `geo_carrier_vertex_not_selfIntersection (hn) (hG) (S) (q) (k)` | verbatim |
| `carrier_no_triple_point` | `geo_carrier_no_triple_point (hn) (hG) (S) (q) (x)` | verbatim |
| `carrier_crossing_two_passes` | `geo_carrier_crossing_two_passes (hn) (hG) (S) (q) {c} (hc) (w) (hw) (p)` | `rw [geo_carrier_crossingPoint_parameters hn hG]` (explicit args needed for the rewrite) |

### §8 → §8

| source | geo | tier | hand edits |
|---|---|:-:|---|
| `csi_det_smul_smul` | shared (hypothesis-free, `SM.Carrier`) | — | not re-declared |
| `csi_crossing_edges_det_ne_zero (hn) (hP : G1 P) (c) {i j} (hi) (hj) (hij)` | `geoCsi_crossing_edges_det_ne_zero (hP : CrossingGeometry P) (c) {i j} (hi) (hj) (hij)` | **0** | G1 site l.603 `(g1_remote_meeting hP hr …).2.2.1 → crossing_det_ne_zero_of_geometry hP hc0` with `hc0 : IsCrossing P {i0, j0}` from `c.property` and `hs`; `hn` dropped |
| `carrier_selfIntersection_transverse (hn) (hP : Generic) (S) (q) {c} (hc) (w) (hw)` | `geo_carrier_selfIntersection_transverse (hn) (hP : CrossingGeometry P) (S) (q) {c} (hc) (w) (hw)` | **0** | `unselected_visit_outgoing_direction hn hP S w hcS → geo_unselected_visit_outgoing_direction hn hP S w hcS` (accepted, FlatCarriers:2965), `visit_incoming_direction → geo_visit_incoming_direction` (FlatCarriers:2943), `smoothingSegment_one/_zero → geoSmoothingSegment_one/_zero` (U1b). The six-clause shape of the source is kept (incoming germs included) |
| `carrier_selfIntersection_not_corner (hn) (hP : Generic) (S) (q) {c} (hc)` | `geo_carrier_selfIntersection_not_corner (hG : CarrierGeometry P) (S) (q) {c} (hc)` | **1** | `csi_crossingPoint_ne_vertex hn hP.1 c → cg_crossingPoint_ne_vertex hG c` (U0); `generic_crossingPoint_injective → crossingPoint_injective_of_geometry hG.cg`; `hn` dropped (no consumed lemma takes it) |

### §9–§10 → §9–§10

| source | geo | tier | hand edits |
|---|---|:-:|---|
| `csi_normalize (hn) (hP : Generic)` | `geoCsi_normalize (hP : CrossingGeometry P) (S) (a) {u} (hu0) (hu1)` | 0 | `smoothingSegment_glue → geoSmoothingSegment_glue hP S a` (U1b), `owner_successor → geoOwner_successor hP S a` (accepted); `hn` dropped |
| `carrier_nonconsecutive_segments_meet` | `geo_carrier_nonconsecutive_segments_meet (hn) (hG) {S} (hS) (q) {a b} (ha) (hb) (hab) (hba) (hab') {u v} … (h)` | 1 | verbatim |
| `carrier_selfIntersections (hn) (hP : Generic) {S} (hS : S ∈ independentSupports hn hP) (q)` | **`geo_self_intersections (hn) (hG : CarrierGeometry P) {S} (hS : GeoIndependent hG.cg S) (q)`** (§5 target) | **1** | verbatim (four-way `refine`, the transverse clause projected to the four printed conjuncts) |

### §11 (new, small) — agreement with the accepted lane on SM-generic polygons

Through the accepted §4b lemmas only (`geoMarkPosition_eq_generic`, `geoSmoothingSegment_eq_generic`,
`geoComponentEquivGeneric_owner`): `geoCsiEdge_eq_generic`, `geoCsiStart_eq_generic` (from the prototype),
`geoCarrierTrace_eq_generic (hn) (hP : Generic P) (S) (p) : geoCarrierTrace (generic_crossingGeometry hn hP) S p =
carrierTrace hn hP S p`, `geoIsCarrierParameter_iff_generic`, `geoIsSelfIntersection_iff_generic (hn) (hP) (S) (q) (x) :
GeoIsSelfIntersection (generic_crossingGeometry hn hP) S q x ↔ IsSelfIntersection hn hP S (geoComponentEquivGeneric hn hP S q) x`,
`geoIsTriplePoint_iff_generic`. These are the pieces U6 (SM/GeoCarrierAgreement.lean) would otherwise have to write for
the self-intersection predicates; the `geoCarrierCrossings_eq_generic` half of U6 is not touched here.

## Method

1. Read DECISION_FINAL §0/§3/§5, the source SM/CarrierSelfIntersections.lean (763 lines), the prototype
   work/drafts/cvdom/CarrierGeometry.lean, the accepted field `CarriersLemmaData.self_intersections`, U0
   (SM/GeoCarrierGeometry.lean, in full), the U2a declaration list and its §1/§4 lemmas, the U2b REPORT, and the
   signatures of every accepted `geo*` lemma the port consumes (FlatCarriersDefs/FlatCarriers/GeoCarrierOrder/GeoCarrierCount).
2. Hand port on the source text with the port_lane.py renaming (the file is short enough that the transformer's residue —
   dropping the U0 §0 lemmas and `csi_smoothingSuccessor_eq`, the R4 re-binding of §4, the `Generic`-site replacements, the
   explicit `u` of `geoSmoothingSegment_mem_edgeSegment`, `hn` drops — was done directly).
3. Two compile rounds: round 1 gave one `unusedSectionVars` warning (`[NeZero n]` on `cg_edgeSegment_meet` → `omit
   [NeZero n] in` on the two §4 lemmas, placed before the docstring), one `rw` needing explicit arguments
   (`geo_carrier_crossingPoint_parameters hn hG`), and two `simp only` calls that made no progress in §11 (replaced by
   `exists_congr` + `rw`); round 2: exit 0, no output. Then `#print axioms` (40/40 standard), name grep (0 collisions),
   tier grep, and the mechanical shape diff against the accepted field (exact match).

## Notes for the assembler and downstream units (U3, U4, U6, U7c)

- **Import graph.** `SM.GeoCarrierSelfIntersections` imports `SM.GeoCarrierCrossings` (→ `SM.GeoCarrierOrder` →
  `SM.GeoCarrierCount` → `SM.FlatCarriers`) and `SM.GeoCarrierGeometry` (→ `SM.FlatCarriersDefs`, `SM.RegularLocus`).
  It does NOT import `SM.GeoCornerPolygon` (nothing from U2b is consumed; the source did not import CarrierCornerPolygon
  either), so U2b and U2c are siblings under U2a/U1b; U3/U4 import both. CV-free.
- **For U3 (`GeoCarriersLemmaData.self_intersections`):** `fun q => geo_self_intersections hn hG hS q` is the field
  verbatim, exactly as `carriers_lemma` uses `carrier_selfIntersections` (CarriersLemma.lean:133). If the bundle takes
  `hW : WeakGeneric P` for the turn clause, use `geo_self_intersections_of_weak hn hW hS q` or
  `geo_self_intersections hn hW.carrierGeometry hS q` (both typecheck against `geoOwner (weak_crossingGeometry hW) S`
  by proof irrelevance).
- **For U4 (tail-off / transverse / no-triple of the corner polygon, re-binding CSilent.lean 556–1300):** the segment-level
  facts are here at tier 1 — `geoCsi_trace_meet hn hG S` (two distinct half-open segments meet only at a crossing point,
  at their start marks), `geo_carrier_nonconsecutive_segments_meet hn hG hS q` (closed segments), `geo_carrier_crossing_two_passes`
  (exactly two parameters at a retained crossing), `geo_carrier_selfIntersection_transverse hn hP S q hc w hw` (tier 0, six
  clauses incl. the incoming germs), `geoCsi_trace_eq_vertex` / `geoCsi_trace_eq_crossingPoint` (a vertex / crossing point on a
  half-open segment is its start mark), and `cg_edgeSegment_meet hn hG` (two distinct closed edges of `P` meet in a vertex or a
  crossing point). The corner-polygon block trace of U2b (`geoCornerPolygon_block`, `geoCornerPolygon_trace`) turns these
  into statements about `edgeSegment (geoCornerPolygon hG.cg S q) k`.
- **For U7c (piececurve Step 2, `geoCarrierCrossings _ (S ∪ K) q = pieceLabels H`):** `geo_carrier_selfIntersection_iff hn hG hS q x`
  is the "self-intersections = retained crossings" direction; `geo_carrier_selected_not_selfIntersection` and
  `geo_carrier_vertex_not_selfIntersection` exclude the selected points and the vertices.
- **Call shapes that differ from the source:** `cg_edgeSegment_meet hn hG hij hxi hxj` and `cg_edge_mem_of_crossingPoint_mem hn hG c hx`
  take `hn` (the source's G1 versions did too; the prototype's tier-2 versions did not);
  `geo_carrier_selfIntersection_not_corner hG S q hc`, `geoCsi_normalize hP S a hu0 hu1`, `geoCsi_crossing_edges_det_ne_zero hP c hi hj hij`
  take no `hn`. Everything else has the source's binder list under the renaming; the §5 target has its §5 binder list.
- **Time.** ≈ 1.3 h including reading the decision, the source, the prototype, U0 in full, the landed units' interfaces,
  writing, two compile rounds, the checks and this report.
