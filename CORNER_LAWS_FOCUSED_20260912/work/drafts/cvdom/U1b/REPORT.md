# CV-DOM unit U1b — REPORT (2026-09-14, ~02:57 UTC / 10:57pm ET)

Prover: Claude Code subagent (claude-fable-5-1) of the pod executor. Spec: work/drafts/cvdom/DECISION_FINAL.md
§0, §3 (rulings R1–R5) and §5 row **U1b**; scope re-cut by the coordinator's mid-task message (U1a landed as
work/lean/SM/GeoCarrierCount.lean; import it, drop duplicates, deliver only the rest). Nothing under work/lean was
written. Paths relative to the package root
/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912.

## Deliverables

| file | intended home | lines | status |
|---|---|---:|---|
| `work/drafts/cvdom/U1b/GeoCarrierOrder.lean` | `work/lean/SM/GeoCarrierOrder.lean` (new module, namespace `SM.GeoCarrier`, `open Carrier`, CV-free; single import `SM.GeoCarrierCount`) | 231 | `cd work/lean && lake env lean ../drafts/cvdom/U1b/GeoCarrierOrder.lean` → **exit 0, no output (no warnings), no `sorry`** (the only `sorry` token is in the header prose) |
| `work/drafts/cvdom/U1b/GeoCarrierOrder_standalone_SUPERSEDED.lean.txt` | record only, NOT for assembly | 1,452 | the pre-coordination draft (import `SM.FlatCarriers`, self-contained ports of all eight U1b files plus their U1a-side prerequisites); `lake env lean` reported no errors before the re-cut. Kept as an independent cross-check of the statements now taken from GeoCarrierCount; every declaration in it that is not in `GeoCarrierOrder.lean` is a duplicate of one in SM/GeoCarrierCount.lean (same names, same statements). |
| `work/drafts/cvdom/U1b/assemble_u1b.py` | tooling only | 70 | the post-processor run on port_lane.py's output (rename dictionary + binder patterns) that produced the standalone draft |

14 declarations, all tier 0 (`hP : CrossingGeometry P`). `#print axioms` (on a copy of the file with the lines
appended): `geoComponentCycle_eq_filter`, `geoSmoothingSegment_zero`, `_one`, `_glue`, `continuous_geoSmoothingSegment`,
`geoSmoothingSegment_length_pos`, `_injective`, `geoComponentMarkList_data`, `geoComponentMarkList_getElem_successor`,
`geoTracedSuccessor_of_independent`, `geoCarrierSpec_of_independent`, `geoComponentTraceEdge_data`, `geo_closed_trace` —
each `[propext, Classical.choice, Quot.sound]` only (standard).

Name safety (ruling R3): each of the 14 names grepped against every `.lean` under work/lean (excluding `.lake`) — zero
hits; no accepted `geo*` name is re-declared; nothing in SM/FlatCarriersDefs.lean, SM/FlatCarriers.lean,
SM/GeoCarrierGeometry.lean or SM/GeoCarrierCount.lean is shadowed. No `Generic`, `hP.1`-as-G1, `hP.2`, `hn hP` or
`independentSupports` anywhere in the file (`hP.1` appears once, as `CrossingGeometry` clause 1 = edge ≠ 0).

## §5 U1b targets — status

| §5 target (shape as printed in §5) | where it is | status / note |
|---|---|---|
| `def GeoInheritsMarkOrder hP S : Prop` | **SM/GeoCarrierCount.lean:564** (U1a) | done there; not re-declared |
| `geoInheritsMarkOrder_of_independent (hn) (hP) (hS)` | **SM/GeoCarrierCount.lean:1734**, shape `(hP) (hS)` — **no `hn`** | done there (U1a's report says so); not re-declared. Downstream must call `geoInheritsMarkOrder_of_independent hP hS`. The chain genuinely needs no `hn`, so this is R5-correct; only the §5 text differs. |
| `geoTracedSuccessor_of_independent (hn) (hP) (hS) (q) : TracedSuccessor hP S q` | GeoCarrierOrder.lean:152 | **proved**, exact §5 shape (`hn` unused, kept as §5 prescribes under `set_option linter.unusedVariables false in`; the `hn`-free content is `geoComponentMarkList_getElem_successor (hP) (hS) (q) (i)`, :136) |
| `geoSmoothingSegment_mem_edgeSegment (hn) (hP) (S) (a) {u} (hu0) (hu1)` | **accepted, SM/FlatCarriers.lean:1466** (`SM.GeoCarrier`), shape `(hP) (S) (a) (u) (hu0) (hu1)` — no `hn`, `u` explicit | NOT declared (ruling R3 forbids re-declaring an accepted `geo*` name); the accepted lemma is strictly stronger. Downstream must call `geoSmoothingSegment_mem_edgeSegment hP S a u hu0 hu1`. |
| `geoCarrierSpec_of_independent (hn) (hP) (hS) : GeoCarrierSpec hP S` (via `GeoCarrierSpec.of_core`) | GeoCarrierOrder.lean:162 | **proved**, exact §5 shape: `GeoCarrierSpec.of_core hP S (traced_successor from geoComponentMarkList_getElem_successor) (inherited_pieces from the accepted geoSmoothingSegment_mem_edgeSegment)`; `hn` unused (same treatment) |
| `def geoComponentCycle` | **SM/GeoCarrierCount.lean:355** (U1a; port of `componentCycle`) | done there |
| `geoComponentCycle_eq_filter (q) : geoComponentCycle hP S q = (geoMarkCycle hP).filter (fun m => decide (geoOwner hP S m = q))` | GeoCarrierOrder.lean:49 | **proved** (`rfl`), exactly the §5 statement; U1a's `geoComponentCycle_eq_filtered_markList` (GeoCarrierCount:361) is the `(geoMarkList hP).filter … : Cycle` form of the same fact |
| `geo_closed_trace` (port of CarrierClosedTrace's main statement) | GeoCarrierOrder.lean:216 | **proved**: `(hn) (hP) {S} (hS : GeoIndependent hP S) (q) (i : Fin (geoComponentMarkList hP S q).length)` with the exact ported conclusion of `componentTraceEdge_data` (each trace edge is the inherited `geoSmoothingSegment`, has positive Euclidean length, glues to the next modular edge, is continuous); `:= geoComponentTraceEdge_data hn hP hS q i` |

Nothing left unproved; no obstacle. No lemma needed `SM.Generic` beyond `CrossingGeometry` (no tier-1/tier-2
statement was necessary anywhere in U1b).

## Ported declarations (source → geo name, tier, hand edits)

All in GeoCarrierOrder.lean unless marked GCC (= SM/GeoCarrierCount.lean, U1a) or FC (= accepted SM/FlatCarriers.lean).
"verbatim" = the source proof with the renaming `X hn hP → geoX hP`, `markPosition hn hP.1 → geoMarkPosition hP`,
`smoothingSuccessor → geoSmoothingSuccessor`, `owner → geoOwner`, `Component → GeoComponent`,
`S ∈ independentSupports hn hP → GeoIndependent hP S`.

### SM/CarrierAffineSegments.lean (102 lines)
| source | geo | tier | hand edits |
|---|---|:-:|---|
| `edgePoint_sub_edgePoint`, `edgePoint_affine` | shared as they are (`SM.Carrier`, hypothesis-free) | — | not re-declared |
| `smoothingSegment` | accepted `geoSmoothingSegment` (FlatCarriersDefs:317) | 0 | not re-declared |
| `smoothingSegment_zero` | `geoSmoothingSegment_zero` (`@[simp]`) | 0 | verbatim, `hn` dropped |
| `smoothingSegment_one` | `geoSmoothingSegment_one` (`@[simp]`) | 0 | verbatim, `hn` dropped |
| `smoothingSegment_glue` | `geoSmoothingSegment_glue` | 0 | verbatim, `hn` dropped |
| `continuous_smoothingSegment` | `continuous_geoSmoothingSegment` | 0 | verbatim, `hn` dropped |

### SM/CarrierSegmentGeometry.lean (147 lines)
| source | geo | tier | hand edits |
|---|---|:-:|---|
| `smoothingSegment_subsegment_data`, `_positive_direction`, `_displacement_ne_zero`, `smoothingSuccessor_ne_self` | accepted FC:2841, 2864, 2874, 2882 (all `(hn) (hP) (S) (a)`) | 0 | not re-declared |
| `smoothingSegment_mem_edgeSegment` | accepted FC:1466 `geoSmoothingSegment_mem_edgeSegment (hP) (S) (a) (u) (hu0) (hu1)` (no `hn`) | 0 | not re-declared (see targets table) |
| `smoothingSegment_length_pos` | `geoSmoothingSegment_length_pos (hn) (hP) (S) (a)` | 0 | verbatim; `hn` kept because the accepted `geoSmoothingSegment_displacement_ne_zero` takes it (R5) |
| `smoothingSegment_injective` | `geoSmoothingSegment_injective (hn) (hP) (S) (a)` | 0 | verbatim except the one G1 site: `(g1 hn P hP.1).2.1 _` (edge ≠ 0) → `hP.1 _` (`CrossingGeometry` clause 1); `hn` kept for `geoSmoothingSegment_subsegment_data hn` |

### SM/CarrierClosedTrace.lean (148 lines)
| source | geo | tier | hand edits |
|---|---|:-:|---|
| `componentMarkList`, `componentPlaneCycle` | accepted `geoComponentMarkList`, `geoComponentPlaneCycle` (FlatCarriersDefs:290, 310) | 0 | not re-declared |
| `componentMarkList_data` | `geoComponentMarkList_data (hP) (S) (q)` | 0 | verbatim; uses GCC `geoComponentCycle_eq_filtered_markList`, `geoComponentCycle_list_mem_iff`, `geoComponentCycle_list_nodup` and accepted `geoOwner_surjective` |
| `componentMarkList_getElem_successor` | `geoComponentMarkList_getElem_successor (hP) {S} (hS) (q) (i)` | 0 | verbatim; `independent_inheritsMarkOrder hn hP hS` → GCC `geoInheritsMarkOrder_of_independent hP hS`; `hn` dropped (nothing needs it) |
| — (new, §5) | `geoTracedSuccessor_of_independent (hn) (hP) (hS) (q) : TracedSuccessor hP S q` | 0 | `fun i => geoComponentMarkList_getElem_successor hP hS q i` (`TracedSuccessor` is the accepted abbrev FC:3147) |
| — (new, §5) | `geoCarrierSpec_of_independent (hn) (hP) (hS) : GeoCarrierSpec hP S` | 0 | `GeoCarrierSpec.of_core` (FC:390) with the two inputs above |
| `componentTraceEdge` | `geoComponentTraceEdge (hP) (S) (q) (i) (u)` | 0 | verbatim, `hn` dropped |
| `componentTraceEdge_data` | `geoComponentTraceEdge_data (hn) (hP) {S} (hS) (q) (i)` | 0 | verbatim; `hn` kept for `geoSmoothingSegment_length_pos hn` |
| — (§5 name) | `geo_closed_trace (hn) (hP) {S} (hS) (q) (i)` | 0 | same statement as `geoComponentTraceEdge_data`; `:=` it |

### SM/CarrierInheritedOrder, CarrierInheritedInsert, CarrierIndependentOrder, CarrierSameArc, CarrierMarkedArcLists (905 lines)
Ported in full in the standalone draft (verbatim proofs; the SameArc port replaces `Interlaces hn hP →
GeometricInterlaces hP`, `crossingVisitBetween hn hP.1 → geometricCrossingVisitBetween hP`, `visitPosition hn hP.1 →
geometricVisitPosition hP`, `crossingVisitBetween_complement hn hP → geo_crossingVisitBetween_complement hP`,
`interlaces_iff_unique hn hP → geo_interlaces_iff_unique hP`, `(mem_independentSupports_iff hn hP S).mp hS → hS`, all
hypothesis-free lemmas `filter_splitList_left/right`, `splitList_*`, `sorted_rotate_split_*`, `sameCycle_congr_of_eqOn_bijOn`
shared as they are), then **dropped from the deliverable** because SM/GeoCarrierCount.lean already contains the same
ports under the same names: `GeoInheritsMarkOrder` (:564), `geoInheritsMarkOrder_iff_formPerm/_empty/_singleton/_insert`
(:572, 587, 674, 1040), `geoComponentCycle_singleton_splitList` (:606), `geoComponentCycle_filter_of_owner_imp/
_insert_child_cycles/_formPerm_eq_of_list` (:927, 943, 1024), `geo_visitPosition_ne_of_ne/_ne_of_visit_ne`,
`geo_crossingVisitBetween_complement`, `geo_alternating_visits_iff_unique`, `geo_unique_between_swap`,
`geo_interlaces_iff_unique` (:1179–1232), the SameArc section (:1262–1405; U1a names `geoIndependent_crossing_visits_*`,
`geoIndependent_twin_one_open_arc` where the standalone draft had `geo_independent_*`), `geoMarkList_rotate_left_iff/
_right_iff`, `geoMarkList_filter_left_iff/_right_iff`, `geoIndependent_twin_same_slice/_same_filtered_slice` (:1412–1475),
`GeoPendingPairsTogether`, `geoPendingPairsTogether_empty/_insert` (:1495–1511), `geoIndependent_partial_invariants`,
`geoIndependent_inheritsMarkOrder`, `geoIndependent_remaining_pair_owners`, `geoIndependent_selected_pair_owners_ne`
(:1550–1588), `geoInheritsMarkOrder_of_independent` (:1734). The U1a-side prerequisites the standalone draft duplicated
(`geoSmoothingSuccessor_union_of_disjoint/_insert/_insert_other/_insert_eqOn_owner/_empty`, `geoComponent_empty_subsingleton`,
`geoMarkCycle_rotation`, `geoMarkSuccessor_eq_formPerm`, `geoMarkList_rotate_start/_split`, `geoMarkSuccessor_splitList`,
`geoComponentCycle*` of CarrierFilteredCycles, `geoSmoothingSuccessor_singleton_splitList`, `geoOwner_singleton_ne/_exhaust`,
`geoComponentCycle_list_nodup/_mem_iff/_eqOn/_current_split_data`, `geoSmoothingSuccessor_insert_child_data`,
`geoOwner_insert_iff_of_unaffected`, `geoComponentCycle_insert_unaffected`) are likewise all in GeoCarrierCount.lean.

## Method

1. `python3 work/drafts/cvdom/port_lane.py work/lean/SM/<file>.lean` on the eight U1b files and on the six U1a-side
   dependency files (CycleList, FilteredCycles, SingleSupport, CurrentCycle, InsertOrbits, PendingPairs); substitution
   counts 29–98 per file.
2. `assemble_u1b.py`: strip headers, concatenate in dependency order, apply the binder patterns the transformer lacks
   (`(hn : 3 ≤ n) (hP : Generic P)` of CarrierSameArc, `{S} (hS : S ∈ independentSupports hn hP)`,
   `(mem_independentSupports_iff hn hP S).mp hS`), the global ` hn hP(.1)? → hP`, and a rename dictionary for the names
   outside DEFMAP (`componentCycle* → geoComponentCycle*`, `mem_componentCycle → mem_geoComponentCycle`,
   `InheritsMarkOrder → GeoInheritsMarkOrder`, `PendingPairsTogether → GeoPendingPairsTogether`, `Interlaces →
   GeometricInterlaces`, `crossingVisitBetween → geometricCrossingVisitBetween`, the `_empty`/`_rotation`/`_formPerm`
   helpers, `geo_filter_splitList_* → filter_splitList_*` (hypothesis-free, shared)).
3. Compile loop (3 rounds on the standalone draft): (a) declaration/use mismatch `geo_componentCycle*` vs
   `geoComponentCycle*` (one regex); (b) block order — CarrierCurrentCycle's `componentCycle_list_eqOn` needs
   `InheritsMarkOrder`, so the CurrentCycle block moves after the InheritedOrder block (as the source import graph says);
   bare cross-file uses `independent_twin_one_open_arc`, `independent_twin_same_filtered_slice` → `geo_*`;
   (c) `set_option … in` must precede the docstring. Then exit 0.
4. Coordinator message → re-cut to `import SM.GeoCarrierCount`; kept sections 1–3 above + the two §5 wrappers + the
   §5-named alias; adjusted the one call `geo_independent_inheritsMarkOrder hP hS → geoInheritsMarkOrder_of_independent hP hS`.
   Two compile rounds (the same `set_option`/docstring order slip). Exit 0, no warnings.

## Notes for the assembler and downstream units (U2a, U2b, U7b)

- Dependency direction: `SM.GeoCarrierOrder` imports `SM.GeoCarrierCount` (U1a's report already recommends this).
- Call shapes that differ from the §5 text: `geoInheritsMarkOrder_of_independent hP hS` (no `hn`; GeoCarrierCount) and
  `geoSmoothingSegment_mem_edgeSegment hP S a u hu0 hu1` (no `hn`, `u` explicit; accepted FlatCarriers:1466). Everything
  else in §5 U1b has its printed binder list.
- `geoCarrierSpec_of_independent hn hP hS : GeoCarrierSpec hP S` gives U7a's row 135 fields (`reconnect_selected`,
  `keep_unselected`, `keep_vertex`, `carriers`, `traced_curve`, `traced_marks`, `traced_successor`, `straight_pieces`,
  `inherited_pieces`) at every `GeoIndependent` set with no genericity; `tracedSuccessor_of_spec` (FC:3154) recovers
  `TracedSuccessor` from it, and `geoTracedSuccessor_of_independent hn hP hS q` gives it directly (U2b's corner-chain
  lemmas FC:3185–3350 take `TracedSuccessor hP S q`).
- `geoSmoothingSegment_injective hn hP S a`, `geoSmoothingSegment_length_pos hn hP S a`, `geo_closed_trace hn hP hS q i`
  are the U2b/U2c inputs for `geoCornerPolygon_trace` / the self-intersection analysis.
- Time: ≈ 2.5 h including reading the decision, the eight sources and their 12 dependency files, the accepted geo layer,
  the transformer runs, three compile rounds on the standalone draft and two on the re-cut module.
