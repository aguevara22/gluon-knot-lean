# CV-DOM unit U1a — REPORT (2026-09-14, ~02:50 UTC / 10:50pm ET)

Prover: Claude Code subagent (claude-fable-5-1) of the pod executor. Spec: work/drafts/cvdom/DECISION_FINAL.md
§0, §3 (rulings R1–R3, R5) and §5 row **U1a**. Nothing under work/lean was written. Paths relative to the
package root /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912.

## Deliverables

| file | intended home | lines | status |
|---|---|---:|---|
| `work/drafts/cvdom/U1a/GeoCarrierCount.lean` | `work/lean/SM/GeoCarrierCount.lean` (new module, namespace `SM.GeoCarrier`, `open Carrier`, CV-free; single import `SM.FlatCarriers`) | 1,792 | `cd work/lean && lake env lean ../drafts/cvdom/U1a/GeoCarrierCount.lean` → **exit 0, no warnings, no `sorry`** (≈ 13 s) |
| `work/drafts/cvdom/U1a/port_u1a.py` | (tooling only) | 120 | the transformer used: work/drafts/cvdom/port_lane.py with the §5 DEFMAP extensions and the substitutions listed below; run from work/ on the 20 source files in dependency order |

106 declarations, all tier 0 (`hP : CrossingGeometry P`). `#print axioms` (checked on a copy of the file with the
lines appended): `geoComponent_card`, `geo_selected_visits_separated`, `geoOwner_refines`,
`geoInheritsMarkOrder_of_independent`, `geoComponent_card_independent`, `geoIndependent_successor_components`,
`geoComponentCornerCycle_nonempty` — each `[propext, Classical.choice, Quot.sound]` only (standard).

Name safety (ruling R3): every declared name was grepped against every declaration site under work/lean — zero
collisions; zero overlap with the `geo*` names of SM/FlatCarriersDefs.lean, SM/FlatCarriers.lean,
SM/GeoCarrierGeometry.lean (43 source declarations whose `geo*` counterpart already exists there are NOT
re-declared; references resolve to the accepted ones — marked `-- [port]` in the file). No `Generic`, `hP.1`,
`hP.2`, `hn hP` or `independentSupports` remains anywhere in the file (grep: only the header prose).

## Targets (§5 U1a) — all proved

| target | statement in the draft (line) | proof |
|---|---|---|
| `geoComponent_card` | `theorem geoComponent_card (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S) : Fintype.card (GeoComponent hP S) = S.card + 1` (1718) | `:= geoComponent_card_independent hP hS` (the port of `component_card_independent`, CarrierComponentCount.lean:78). **`hn` is unused** (the geo definitions do not take it; ruling R5 would drop it, §5's shape lists it): kept as §5 prescribes under `set_option linter.unusedVariables false in`; the `hn`-free form is `geoComponent_card_independent (hP) (hS)` (1655). The executor may delete either. |
| `geo_selected_visits_separated` | `(hP) {S} (hS : GeoIndependent hP S) (v : Visit P) (hv : v.1 ∈ S) : geoOwner hP S (Sum.inr v) ≠ geoOwner hP S (Sum.inr (visitTwin v))` (1725) | `:= geoIndependent_selected_pair_owners_ne hP hS v hv` (port of CarrierIndependentOrder.lean:97) |
| `geoOwner_refines` | `(hP) {S S'} (hS' : GeoIndependent hP S') (hSS' : S ⊆ S') (q' : GeoComponent hP S') : ∃ q : GeoComponent hP S, ∀ m, geoOwner hP S' m = q' → geoOwner hP S m = q` (1783) | NEW (no source counterpart; carrierword clause 3): from `geoOwner_eq_of_subset` (1740) — `Finset.induction_on` over `D ⊆ S' \ S` for `T = S ∪ D`; each inserted crossing `c ∈ S' \ S` has its two visits on one current carrier of `S ∪ D` (`geoIndependent_remaining_pair_owners`, port of CarrierIndependentOrder.lean:88, i.e. the pending-pairs invariant), so `geoOwner_insert_eq_imp` (port of CarrierOrbitRefinement.lean:56) refines; the dependent `Finset` rewrite `S ∪ insert c D = insert c (S ∪ D)` (`Finset.union_insert`) is done by generalising `T` and `rintro T rfl`. 50 lines. |
| (U1b spec name, needed here) `geoInheritsMarkOrder_of_independent` | `(hP) {S} (hS : GeoIndependent hP S) : GeoInheritsMarkOrder hP S` (1733) | `:= geoIndependent_inheritsMarkOrder hP hS` (port of CarrierIndependentOrder.lean:80) |
| also | `geoIndependent_successor_components (hP) (hS) : Fintype.card (GeoComponent hP S) = S.card + 1 ∧ GeoInheritsMarkOrder hP S ∧ ∀ v, v.1 ∈ S → geoOwner … ≠ geoOwner …` (1662) | port of CarrierComponentCount.lean:105 (the three combinatorial conclusions of lem:carriers in one bundle) |

## Scope note for the assembler — overlap with U1b

`geoComponent_card` genuinely depends on the inherited-order invariant: `component_card_insert`
(CarrierComponentCount.lean:16) takes `hI : InheritsMarkOrder hn hP T`, and `component_card_independent_partial`
gets it from `independent_partial_invariants` (CarrierIndependentOrder.lean:56), which needs `inheritsMarkOrder_insert`
(CarrierInheritedInsert), `pendingPairsTogether_insert` (CarrierPendingPairs ← `independent_twin_same_filtered_slice`
of CarrierMarkedArcLists ← CarrierSameArc). §5 put `InheritsMarkOrder` / `geoInheritsMarkOrder_of_independent` and the
port of CarrierInheritedOrder, CarrierInheritedInsert, CarrierIndependentOrder, CarrierSameArc, CarrierMarkedArcLists
into **U1b**, but U1a cannot compile without them, so this file contains their ports too (five sections, ≈ 620
lines: draft lines 558–707 InheritedOrder, 920–1098 InheritedInsert, 1258–1405 SameArc, 1406–1488 MarkedArcLists,
1544–1605 IndependentOrder), under the names the extended DEFMAP gives (`GeoInheritsMarkOrder`,
`geoInheritsMarkOrder_iff_formPerm`, `geoInheritsMarkOrder_empty/_singleton/_insert`, `geoComponentCycle_*`,
`geoIndependent_*`). U1b's directory was still empty when this report was written (02:48 UTC). Recommended
resolution: **U1b's `SM/GeoCarrierOrder.lean` imports `SM.GeoCarrierCount` and drops its own copies of these
declarations** (or the assembler moves the five sections into GeoCarrierOrder.lean and has GeoCarrierCount import it —
the dependency direction is Order → Count, so both cannot be independent). `def geoComponentCycle` (§5 lists it under
U1b as `geoComponentCycle` with `geoComponentCycle_eq_filter`) is here as the port of `componentCycle`
(CarrierFilteredCycles.lean:15); `geoComponentCycle_eq_filtered_markList` (draft 359) is exactly §5's
`geoComponentCycle_eq_filter` statement (`geoComponentCycle hP S q = ((geoMarkList hP).filter (fun m => decide (geoOwner hP S m = q)) : Cycle _)`,
`rfl`), under the source's name.

The five other §5-listed U1a inputs that are "done" in the sample (CarrierSingleSwitch, CarrierUnchangedComponent,
`geoSmoothingSuccessor_union_of_disjoint`) are re-generated here by the transformer (identical text to
work/drafts/cvdom/GeoCombinatorialSample.lean); the sample is superseded by this file.

## Method and hand edits (all recorded; everything else is the transformer's output, proofs verbatim)

Transformer `port_u1a.py` = port_lane.py plus:
1. DEFMAP extensions (§5): `componentCycle→geoComponentCycle`, `InheritsMarkOrder→GeoInheritsMarkOrder`,
   `inheritsMarkOrder→geoInheritsMarkOrder`, `componentForgetSwitch→geoComponentForgetSwitch`,
   `PendingPairsTogether→GeoPendingPairsTogether`, `pendingPairsTogether→geoPendingPairsTogether`,
   `componentCornerCycle→geoComponentCornerCycle`, `component→geoComponent` (so `component_card_* → geoComponent_card_*`),
   `independent→geoIndependent` (matching the library's `geoIndependent_map_iff`), `markPosition→geoMarkPosition`;
   `mem_X → mem_geoX` (library convention `mem_geoMarkList`, `mem_geoComponentMarkList`); three spellings fixed to the
   accepted names: `prevMark_nextMark→geoPrevMark_geoNextMark`, `nextMark_prevMark→geoNextMark_geoPrevMark`,
   `selectedMarkPerm_evaluation→geoSelectedMarkPerm_evaluation` (FlatCarriers.lean:2829).
2. Binder rule extended to `(hn : 3 ≤ n) {P} (hP : G1 P)` (CarrierMarks/CarrierSmoothing residue) and to the
   brace-free `(hn : 3 ≤ n) (hP : Generic P)` of CarrierSameArc (whose section variable `{P}` is kept by wrapping its
   port in `section SameArc … end SameArc`).
3. Plumbing substitutions (the lane's only uses of `Generic`, ANALYSIS_A §2 / DECISION §1): `markPosition hn hP(.1) →
   geoMarkPosition hP`, `visitPosition hn hP(.1) → geometricVisitPosition hP`, `visitKey hn hP → geometricVisitKey hP`,
   `Interlaces hn hP → GeometricInterlaces hP`, `crossingVisitBetween hn hP.1 → geometricCrossingVisitBetween hP`,
   `(hS : S ∈ independentSupports hn hP) → (hS : GeoIndependent hP S)`, `(mem_independentSupports_iff hn hP S).mp hS → hS`
   (`GeoIndependent` IS the `∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ …` clause, FlatCarriersDefs.lean:457),
   `crossingVisitBetween_complement hn hP → geo_crossingVisitBetween_complement hP`,
   `interlaces_iff_unique hn hP → geo_interlaces_iff_unique hP` (see 5).
4. Hypothesis-free declarations (18: `Mark`, `selectedMarkPerm*`, `selectedVisitTwin(_Perm)_singleton`,
   `selectedMarkPerm_singleton`, `sameCycle_refines_of_step`, `mul_swap_sameCycle_step`, `sameCycle_mul_swap_refines`,
   `filter_splitList_left/right`, `IsTrueCorner`, `isTrueCorner_vertex/visit`) are dropped from the output and referenced
   under their accepted `SM.Carrier` names via `open Carrier` (the sample re-declared them with a `geo_` prefix; the
   decision says they "are shared as they are"). `letI := … → let _ := …` (Mathlib style linter; the accepted
   FlatCarriersDefs uses `let _`).
5. Hand-written block (draft 1169–1257, 89 lines): `geo_visitPosition_ne_of_ne`, `geo_visitPosition_ne_of_visit_ne`,
   `geo_crossingVisitBetween_complement`, `geo_alternating_visits_iff_unique`, `geo_unique_between_swap`,
   `geo_interlaces_iff_unique` — the tier-0 replacements of `crossingVisitBetween_complement` (SM/Interlacement.lean:35)
   and `interlaces_iff_unique` (SM/InterlaceCount.lean:20) that CarrierSameArc consumes. They are word-for-word CV-free
   copies of `CV.geometricVisitPosition_ne_of_ne`, `…_of_visit_ne`, `geometricCrossingVisitBetween_complement`,
   `geometric_alternating_visits_iff_unique`, `geometric_unique_between_swap`, `geometricInterlaces_iff_unique`
   (work/lean/CV/Events.lean:79–160). Kept CV-free so that the SM module does not import `CV.*` (U0's convention); if the
   executor prefers a single copy, replace the block by `import CV.Events` and the six names by their `CV.` originals.
6. Three textual patches: `simp [or_comm] → simp` in `geoSmoothingSuccessor_insert` (unused-simp-arg linter; the sample
   silenced it with `set_option`); `letI : Unique … → let _ : Unique …` in `geoComponent_card_empty`;
   `omit [NeZero n] in` before `geoMarkKey_visit` and the two `geo_visitPosition_ne_*` lemmas (unused section variable).
7. Targets block (draft 1712–1791), described above.

Tiers: **every declaration is tier 0**; no ported lemma needed `CarrierGeometry` or `WeakGeneric`, and none needed
`hn : 3 ≤ n` (the source used `hn` only as the argument of `markPosition`/`visitPosition`/`Interlaces`; ruling R5).
The only `hn` in the file is the one §5 prescribes on `geoComponent_card`.

## Declarations, source → geo name

Status "ported, tier 0" = declared in the draft at the given line, proof verbatim modulo the substitutions above;
"accepted" = the `geo*` counterpart already exists in SM/FlatCarriersDefs.lean or SM/FlatCarriers.lean (not re-declared,
reference resolves there); "hypothesis-free, shared" = the accepted `SM.Carrier` declaration is used as is.

**work/lean/SM/CarrierMarks.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `Mark` (33) | `Carrier.Mark` | hypothesis-free, shared (not re-declared) | — |
| `markPosition` (37) | `geoMarkPosition` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markPosition_vertex` (42) | `geoMarkPosition_vertex` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markPosition_visit` (45) | `geoMarkPosition_visit` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markPosition_evaluation_vertex` (49) | `geoMarkPosition_evaluation_vertex` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markPosition_evaluation_visit` (54) | `geoMarkPosition_evaluation_visit` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markPosition_injective` (60) | `geoMarkPosition_injective` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markKey` (79) | `geoMarkKey` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markKey_vertex` (82) | `geoMarkKey_vertex` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markKey_visit` (86) | `geoMarkKey_visit` | ported, tier 0 | 69 |
| `markKey_injective` (89) | `geoMarkKey_injective` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markLinearOrder` (94) | `geoMarkLinearOrder` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markList` (99) | `geoMarkList` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markList_nodup` (104) | `geoMarkList_nodup` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `mem_markList` (110) | `mem_geoMarkList` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markList_sorted` (116) | `geoMarkList_sorted` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markList_length` (122) | `geoMarkList_length` | ported, tier 0 | 84 |
| `markList_nonempty` (130) | `geoMarkList_nonempty` | ported, tier 0 | 92 |

**work/lean/SM/CarrierSuccessor.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `markCycle` (34) | `geoMarkCycle` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markCycle_nodup` (37) | `geoMarkCycle_nodup` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `mem_markCycle` (40) | `mem_geoMarkCycle` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markCycle_rotation` (44) | `geoMarkCycle_rotation` | ported, tier 0 | 106 |
| `nextMark` (49) | `geoNextMark` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `prevMark` (53) | `geoPrevMark` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `nextMark_eq_list_next` (57) | `geoNextMark_eq_list_next` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `prevMark_eq_list_prev` (61) | `geoPrevMark_eq_list_prev` | ported, tier 0 | 117 |
| `prevMark_nextMark` (66) | `geoPrevMark_geoNextMark` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `nextMark_prevMark` (71) | `geoNextMark_geoPrevMark` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markSuccessor` (77) | `geoMarkSuccessor` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markSuccessor_apply` (84) | `geoMarkSuccessor_apply` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markSuccessor_symm_apply` (88) | `geoMarkSuccessor_symm_apply` | ported, tier 0 | 129 |
| `markSuccessor_getElem` (93) | `geoMarkSuccessor_getElem` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markSuccessor_symm_getElem` (104) | `geoMarkSuccessor_symm_getElem` | ported, tier 0 | 136 |
| `nextMark_no_mark_between` (114) | `geoNextMark_no_mark_between` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markSuccessor_no_mark_between` (132) | `geoMarkSuccessor_no_mark_between` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markSuccessor_prev_no_mark_between` (140) | `geoMarkSuccessor_prev_no_mark_between` | ported, tier 0 | 150 |
| `markSuccessor_sameCycle_getElem` (148) | `geoMarkSuccessor_sameCycle_getElem` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `markSuccessor_sameCycle` (167) | `geoMarkSuccessor_sameCycle` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |

**work/lean/SM/CarrierSmoothing.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `selectedMarkPerm` (36) | `Carrier.selectedMarkPerm` | hypothesis-free, shared (not re-declared) | — |
| `selectedMarkPerm_vertex` (41) | `Carrier.selectedMarkPerm_vertex` | hypothesis-free, shared (not re-declared) | — |
| `selectedMarkPerm_visit` (45) | `Carrier.selectedMarkPerm_visit` | hypothesis-free, shared (not re-declared) | — |
| `selectedMarkPerm_involutive` (48) | `Carrier.selectedMarkPerm_involutive` | hypothesis-free, shared (not re-declared) | — |
| `selectedMarkPerm_evaluation` (54) | `geoSelectedMarkPerm_evaluation` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `selectedMarkPerm_commute` (64) | `Carrier.selectedMarkPerm_commute` | hypothesis-free, shared (not re-declared) | — |
| `selectedMarkPerm_union_of_disjoint` (72) | `Carrier.selectedMarkPerm_union_of_disjoint` | hypothesis-free, shared (not re-declared) | — |
| `smoothingSuccessor` (82) | `geoSmoothingSuccessor` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `smoothingSuccessor_vertex` (86) | `geoSmoothingSuccessor_vertex` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `smoothingSuccessor_visit_of_mem` (90) | `geoSmoothingSuccessor_visit_of_mem` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `smoothingSuccessor_visit_of_not_mem` (97) | `geoSmoothingSuccessor_visit_of_not_mem` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `smoothingSuccessor_empty` (103) | `geoSmoothingSuccessor_empty` | ported, tier 0 | 185 |
| `smoothingSuccessor_union_of_disjoint` (115) | `geoSmoothingSuccessor_union_of_disjoint` | ported, tier 0 | 197 |
| `Component` (124) | `GeoComponent` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `owner` (130) | `geoOwner` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `owner_eq_iff` (134) | `geoOwner_eq_iff` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `owner_successor` (145) | `geoOwner_successor` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `owner_predecessor` (150) | `geoOwner_predecessor` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `owner_surjective` (155) | `geoOwner_surjective` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `componentFintype` (161) | `geoComponentFintype` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `component_card_pos` (165) | `geoComponent_card_pos` | ported, tier 0 | 217 |
| `component_empty_subsingleton` (171) | `geoComponent_empty_subsingleton` | ported, tier 0 | 223 |
| `component_card_empty` (181) | `geoComponent_card_empty` | ported, tier 0 | 232 |

**work/lean/SM/CarrierSingleSwitch.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `selectedVisitTwin_singleton` (37) | `Carrier.selectedVisitTwin_singleton` | hypothesis-free, shared (not re-declared) | — |
| `selectedVisitTwinPerm_singleton` (53) | `Carrier.selectedVisitTwinPerm_singleton` | hypothesis-free, shared (not re-declared) | — |
| `selectedMarkPerm_singleton` (61) | `Carrier.selectedMarkPerm_singleton` | hypothesis-free, shared (not re-declared) | — |
| `smoothingSuccessor_insert` (69) | `geoSmoothingSuccessor_insert` | ported, tier 0 | 250 |
| `smoothingSuccessor_insert_visit` (81) | `geoSmoothingSuccessor_insert_visit` | ported, tier 0 | 262 |
| `smoothingSuccessor_insert_twin` (88) | `geoSmoothingSuccessor_insert_twin` | ported, tier 0 | 268 |
| `smoothingSuccessor_insert_other` (96) | `geoSmoothingSuccessor_insert_other` | ported, tier 0 | 275 |

**work/lean/SM/CarrierOrbitRefinement.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `sameCycle_refines_of_step` (37) | `Carrier.sameCycle_refines_of_step` | hypothesis-free, shared (not re-declared) | — |
| `mul_swap_sameCycle_step` (50) | `Carrier.mul_swap_sameCycle_step` | hypothesis-free, shared (not re-declared) | — |
| `sameCycle_mul_swap_refines` (62) | `Carrier.sameCycle_mul_swap_refines` | hypothesis-free, shared (not re-declared) | — |
| `smoothingSuccessor_insert_sameCycle_refines` (71) | `geoSmoothingSuccessor_insert_sameCycle_refines` | ported, tier 0 | 292 |
| `owner_insert_eq_imp` (80) | `geoOwner_insert_eq_imp` | ported, tier 0 | 300 |
| `owner_insert_ne_of_ne` (90) | `geoOwner_insert_ne_of_ne` | ported, tier 0 | 310 |
| `componentForgetSwitch` (99) | `geoComponentForgetSwitch` | ported, tier 0 | 319 |
| `componentForgetSwitch_owner` (106) | `geoComponentForgetSwitch_owner` | ported, tier 0 | 326 |
| `componentForgetSwitch_surjective` (113) | `geoComponentForgetSwitch_surjective` | ported, tier 0 | 333 |
| `component_card_le_insert` (123) | `geoComponent_card_le_insert` | ported, tier 0 | 342 |

**work/lean/SM/CarrierFilteredCycles.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `componentCycle` (40) | `geoComponentCycle` | ported, tier 0 | 353 |
| `componentCycle_eq_filtered_markList` (46) | `geoComponentCycle_eq_filtered_markList` | ported, tier 0 | 359 |
| `mem_componentCycle` (54) | `mem_geoComponentCycle` | ported, tier 0 | 366 |
| `componentCycle_nodup` (60) | `geoComponentCycle_nodup` | ported, tier 0 | 372 |
| `mem_componentCycle_owner` (66) | `mem_geoComponentCycle_owner` | ported, tier 0 | 378 |
| `componentCycle_nonempty` (73) | `geoComponentCycle_nonempty` | ported, tier 0 | 385 |
| `componentCycle_members_disjoint` (81) | `geoComponentCycle_members_disjoint` | ported, tier 0 | 393 |
| `componentCycle_injective` (91) | `geoComponentCycle_injective` | ported, tier 0 | 402 |
| `componentCycle_empty` (102) | `geoComponentCycle_empty` | ported, tier 0 | 412 |
| `componentCycle_eq_filtered_splitList` (113) | `geoComponentCycle_eq_filtered_splitList` | ported, tier 0 | 423 |

**work/lean/SM/CarrierCycleList.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `markSuccessor_eq_formPerm` (41) | `geoMarkSuccessor_eq_formPerm` | ported, tier 0 | 441 |
| `markList_rotate_start` (51) | `geoMarkList_rotate_start` | ported, tier 0 | 450 |
| `markList_rotate_split` (60) | `geoMarkList_rotate_split` | ported, tier 0 | 458 |
| `markSuccessor_splitList` (73) | `geoMarkSuccessor_splitList` | ported, tier 0 | 470 |

**work/lean/SM/CarrierSingleSupport.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `smoothingSuccessor_singleton_splitList` (43) | `geoSmoothingSuccessor_singleton_splitList` | ported, tier 0 | 491 |
| `owner_singleton_ne` (62) | `geoOwner_singleton_ne` | ported, tier 0 | 509 |
| `owner_singleton_exhaust` (73) | `geoOwner_singleton_exhaust` | ported, tier 0 | 520 |
| `component_card_singleton` (99) | `geoComponent_card_singleton` | ported, tier 0 | 546 |

**work/lean/SM/CarrierInheritedOrder.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `InheritsMarkOrder` (44) | `GeoInheritsMarkOrder` | ported, tier 0 | 562 |
| `inheritsMarkOrder_iff_formPerm` (52) | `geoInheritsMarkOrder_iff_formPerm` | ported, tier 0 | 570 |
| `inheritsMarkOrder_empty` (68) | `geoInheritsMarkOrder_empty` | ported, tier 0 | 585 |
| `filter_splitList_left` (83) | `Carrier.filter_splitList_left` | hypothesis-free, shared (not re-declared) | — |
| `filter_splitList_right` (103) | `Carrier.filter_splitList_right` | hypothesis-free, shared (not re-declared) | — |
| `componentCycle_singleton_splitList` (124) | `geoComponentCycle_singleton_splitList` | ported, tier 0 | 604 |
| `inheritsMarkOrder_singleton` (193) | `geoInheritsMarkOrder_singleton` | ported, tier 0 | 672 |

**work/lean/SM/CarrierCurrentCycle.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `componentCycle_list_nodup` (44) | `geoComponentCycle_list_nodup` | ported, tier 0 | 711 |
| `componentCycle_list_mem_iff` (53) | `geoComponentCycle_list_mem_iff` | ported, tier 0 | 719 |
| `componentCycle_list_eqOn` (63) | `geoComponentCycle_list_eqOn` | ported, tier 0 | 728 |
| `componentCycle_current_split_data` (89) | `geoComponentCycle_current_split_data` | ported, tier 0 | 753 |

**work/lean/SM/CarrierUnchangedComponent.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `smoothingSuccessor_mapsTo_owner` (47) | `geoSmoothingSuccessor_mapsTo_owner` | ported, tier 0 | 777 |
| `smoothingSuccessor_symm_mapsTo_owner` (55) | `geoSmoothingSuccessor_symm_mapsTo_owner` | ported, tier 0 | 784 |
| `smoothingSuccessor_bijOn_owner` (64) | `geoSmoothingSuccessor_bijOn_owner` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `smoothingSuccessor_insert_eqOn_owner` (74) | `geoSmoothingSuccessor_insert_eqOn_owner` | ported, tier 0 | 794 |
| `smoothingSuccessor_insert_bijOn_owner` (91) | `geoSmoothingSuccessor_insert_bijOn_owner` | ported, tier 0 | 810 |
| `smoothingSuccessor_insert_symm_eqOn_owner` (102) | `geoSmoothingSuccessor_insert_symm_eqOn_owner` | ported, tier 0 | 820 |

**work/lean/SM/CarrierInsertOrbits.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `smoothingSuccessor_insert_child_data` (49) | `geoSmoothingSuccessor_insert_child_data` | ported, tier 0 | 838 |
| `owner_insert_iff_of_unaffected` (99) | `geoOwner_insert_iff_of_unaffected` | ported, tier 0 | 887 |
| `componentCycle_insert_unaffected` (121) | `geoComponentCycle_insert_unaffected` | ported, tier 0 | 908 |

**work/lean/SM/CarrierInheritedInsert.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `componentCycle_filter_of_owner_imp` (56) | `geoComponentCycle_filter_of_owner_imp` | ported, tier 0 | 925 |
| `componentCycle_insert_child_cycles` (73) | `geoComponentCycle_insert_child_cycles` | ported, tier 0 | 941 |
| `componentCycle_formPerm_eq_of_list` (155) | `geoComponentCycle_formPerm_eq_of_list` | ported, tier 0 | 1022 |
| `inheritsMarkOrder_insert` (172) | `geoInheritsMarkOrder_insert` | ported, tier 0 | 1038 |

**work/lean/SM/CarrierComponentFibers.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `componentForgetSwitch_fiber_affected` (50) | `geoComponentForgetSwitch_fiber_affected` | ported, tier 0 | 1104 |
| `componentForgetSwitch_fiber_unaffected` (101) | `geoComponentForgetSwitch_fiber_unaffected` | ported, tier 0 | 1154 |

**work/lean/SM/CarrierSameArc.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `not_interlaces_iff_same_arc_status` (51) | `geo_not_interlaces_iff_same_arc_status` | ported, tier 0 | 1266 |
| `not_interlaces_iff_one_open_arc` (80) | `geo_not_interlaces_iff_one_open_arc` | ported, tier 0 | 1295 |
| `not_interlaces_all_visits_same_arc` (97) | `geo_not_interlaces_all_visits_same_arc` | ported, tier 0 | 1312 |
| `independent_crossing_visits_same_arc` (110) | `geoIndependent_crossing_visits_same_arc` | ported, tier 0 | 1325 |
| `independent_crossing_visits_one_open_arc` (122) | `geoIndependent_crossing_visits_one_open_arc` | ported, tier 0 | 1337 |
| `not_interlaces_iff_twin_same_arc` (137) | `geo_not_interlaces_iff_twin_same_arc` | ported, tier 0 | 1352 |
| `not_interlaces_iff_twin_one_open_arc` (153) | `geo_not_interlaces_iff_twin_one_open_arc` | ported, tier 0 | 1368 |
| `independent_twin_one_open_arc` (174) | `geoIndependent_twin_one_open_arc` | ported, tier 0 | 1389 |

**work/lean/SM/CarrierMarkedArcLists.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `markList_rotate_left_iff` (53) | `geoMarkList_rotate_left_iff` | ported, tier 0 | 1410 |
| `markList_rotate_right_iff` (64) | `geoMarkList_rotate_right_iff` | ported, tier 0 | 1421 |
| `markList_filter_left_iff` (75) | `geoMarkList_filter_left_iff` | ported, tier 0 | 1432 |
| `markList_filter_right_iff` (85) | `geoMarkList_filter_right_iff` | ported, tier 0 | 1442 |
| `independent_twin_same_slice` (98) | `geoIndependent_twin_same_slice` | ported, tier 0 | 1455 |
| `independent_twin_same_filtered_slice` (117) | `geoIndependent_twin_same_filtered_slice` | ported, tier 0 | 1473 |

**work/lean/SM/CarrierPendingPairs.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `PendingPairsTogether` (54) | `GeoPendingPairsTogether` | ported, tier 0 | 1493 |
| `pendingPairsTogether_empty` (61) | `geoPendingPairsTogether_empty` | ported, tier 0 | 1500 |
| `pendingPairsTogether_insert` (71) | `geoPendingPairsTogether_insert` | ported, tier 0 | 1509 |

**work/lean/SM/CarrierIndependentOrder.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `independent_partial_invariants` (56) | `geoIndependent_partial_invariants` | ported, tier 0 | 1548 |
| `independent_inheritsMarkOrder` (80) | `geoIndependent_inheritsMarkOrder` | ported, tier 0 | 1571 |
| `independent_remaining_pair_owners` (87) | `geoIndependent_remaining_pair_owners` | ported, tier 0 | 1577 |
| `independent_selected_pair_owners_ne` (97) | `geoIndependent_selected_pair_owners_ne` | ported, tier 0 | 1586 |

**work/lean/SM/CarrierComponentCount.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `component_card_insert` (58) | `geoComponent_card_insert` | ported, tier 0 | 1611 |
| `component_card_independent_partial` (78) | `geoComponent_card_independent_partial` | ported, tier 0 | 1630 |
| `component_card_independent` (104) | `geoComponent_card_independent` | ported, tier 0 | 1655 |
| `independent_successor_components` (112) | `geoIndependent_successor_components` | ported, tier 0 | 1662 |

**work/lean/SM/CarrierTrueCorners.lean**

| source decl (line) | geo name | status | draft line |
|---|---|---|---:|
| `IsTrueCorner` (44) | `Carrier.IsTrueCorner` | hypothesis-free, shared (not re-declared) | — |
| `isTrueCorner_vertex` (49) | `Carrier.isTrueCorner_vertex` | hypothesis-free, shared (not re-declared) | — |
| `isTrueCorner_visit` (53) | `Carrier.isTrueCorner_visit` | hypothesis-free, shared (not re-declared) | — |
| `component_has_trueCorner` (59) | `geoComponent_has_trueCorner` | accepted (FlatCarriersDefs/FlatCarriers), not re-declared | — |
| `componentCornerCycle` (84) | `geoComponentCornerCycle` | ported, tier 0 | 1683 |
| `componentCornerCycle_eq_filtered_markList` (90) | `geoComponentCornerCycle_eq_filtered_markList` | ported, tier 0 | 1689 |
| `mem_componentCornerCycle` (97) | `mem_geoComponentCornerCycle` | ported, tier 0 | 1695 |
| `componentCornerCycle_nodup` (103) | `geoComponentCornerCycle_nodup` | ported, tier 0 | 1700 |
| `componentCornerCycle_nonempty` (110) | `geoComponentCornerCycle_nonempty` | ported, tier 0 | 1706 |

**Hand-written (no source counterpart)**

| geo name | draft line | role |
|---|---:|---|
| `geo_visitPosition_ne_of_ne`, `geo_visitPosition_ne_of_visit_ne` | 1177, 1184 | CV-free copies of CV/Events.lean:79, 86 |
| `geo_crossingVisitBetween_complement` | 1193 | tier-0 `crossingVisitBetween_complement` (copy of CV/Events.lean:99) |
| `geo_alternating_visits_iff_unique`, `geo_unique_between_swap` | 1203, 1218 | copies of CV/Events.lean:109, 125 |
| `geo_interlaces_iff_unique` | 1230 | tier-0 `interlaces_iff_unique` (copy of CV/Events.lean:136) |
| `geoComponent_card` | 1718 | §5 target (lem:carriers (i)) |
| `geo_selected_visits_separated` | 1725 | §5 target |
| `geoInheritsMarkOrder_of_independent` | 1732 | U1b's spec name (alias) |
| `geoOwner_eq_of_subset` | 1740 | refinement lemma behind `geoOwner_refines` |
| `geoOwner_refines` | 1783 | §5 target (carrierword clause 3) |

## Time

≈ 1 h 20 min wall-clock: reading the decision, the 20 source files and the accepted geo layer (≈ 45 min), the
transformer extension and two compile rounds (first round: one missed line-broken binder in CarrierOrbitRefinement and
one reference renamed before its spelling fix; second round: three linter warnings and a docstring/`set_option` order),
checks and this report.
