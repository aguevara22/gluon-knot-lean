# CV-DOM — Analyst A: measure first, then cost the options

Written 2026-09-14 (~01:50 UTC / 9:50pm ET) by a Claude Code analyst subagent (claude-fable-5-1) of the
pod executor, for the decision panel of AUTHOR_NOTES "CV-DOM" (2026-09-13 F2(A) recorded; cost re-examined).
Everything below was read from the files named; the two prototypes were checked with
`cd work/lean && lake env lean ../drafts/cvdom/<file>` (exit 0, no sorry, axioms propext / Classical.choice /
Quot.sound). Paths are relative to `work/lean/` unless said otherwise. Deliverables in this directory:

| file | what |
|---|---|
| `ANALYSIS_A.md` | this report |
| `CarrierGeometry.lean` (367 lines) | the two-tier hypothesis `SM.CarrierGeometry` / `SM.CornerGeometry`, its instances from `SM.Generic`, `SM.WeakGeneric`, `CV.Generic`, `CV.Diagrammatic`, the equivalence `CornerGeometry ↔ WeakGeneric`, and a word-for-word port of SM/CarrierSelfIntersections.lean §0–§5 (the lane file that consumes the most `Generic` lemmas) onto the accepted geometric layer `SM.GeoCarrier` |
| `GeoCombinatorialSample.lean` (169 lines) | a *mechanical* port (script below, zero hand edits to proof bodies) of SM/CarrierSingleSwitch.lean + SM/CarrierUnchangedComponent.lean onto `SM.GeoCarrier` |
| `port_lane.py` | the renaming transformer used for the sample (prints its substitution count) |

## 0. Summary

1. **No definition of the Carrier lane needs `SM.Generic`.** Every lane definition is already re-stated on
   `CrossingGeometry P` in the *accepted* module `SM/FlatCarriersDefs.lean` (namespace `SM.GeoCarrier`:
   `geoMarkPosition`, `geoMarkSuccessor`, `geoSmoothingSuccessor`, `GeoComponent`, `geoOwner`,
   `geoComponentMarkList`, `geoComponentPlaneCycle`, `geoSmoothingSegment`, `geoComponentCornerList`,
   `geoCornerCount`, `geoCornerMark`, `geoCornerPolygon`, `geoCornerTurn`, `geoCarrierCrossings`,
   `GeoIndependent`, `geoCarrierSelector`; lines 77–473), together with the agreement lemmas on SM-generic
   polygons (§4b, lines 626–722: `geoSmoothingSuccessor_eq_generic`, `geoComponentEquivGeneric`,
   `geoComponentMarkList_eq_generic`, `geoComponentCornerList_eq_generic`, …; `geoMarkPosition_eq_generic`
   is `cases a <;> rfl`). Rows def:flat-carriers / cor:flat-carriers (accepted 2026-09-13) are built on it.
2. **The lane's whole dependence on `Generic` is 15 external lemma uses** (table §2), every one with a
   `CrossingGeometry` / `WeakGeometry` counterpart already in the library, plus 15 uses of the SM positive
   lift (which is itself parametrised by `SM.Generic`). `hP.2` (SM's G2) is never used directly by the lane
   (0 occurrences in all 53 files); the 307 occurrences of `hP.1` are all the Prop argument of
   `markPosition/visitPosition/visitKey/crossingVisitBetween hn hP.1` — plumbing, not mathematics.
3. **Three hypothesis tiers suffice**, and CV's printed binders match them exactly:
   tier 0 `CrossingGeometry` (marks, successor, carriers, count, inherited order, noncrossing, pieces);
   tier 1 `CarrierGeometry` = tier 0 + "no vertex on a non-incident closed edge" (self-intersections of a
   carrier; = CV *diagrammatic*, `CV.Diagrammatic → CarrierGeometry` proved);
   tier 2 `CornerGeometry` = tier 1 + nonzero turns (corner polygons, def:wind, def:X1; proved equivalent
   to the accepted `SM.WeakGeneric`, so `CV.Generic → CornerGeometry` and `SM.Generic → CornerGeometry`
   are one-liners from `CV.Generic.weakGeneric` / `generic_implies_weak`).
4. **The port is mechanical.** Calibration: 367 lines (CarrierSelfIntersections §0–§5, incl. all its
   Generic-consuming lemmas) compiled at the second attempt (one fix: a `Fact (1 < n)` that the original
   obtained from `hn`); 220 lines of the combinatorial core compiled at the first attempt after a
   pure-renaming script, with one 6-line lemma added by hand. About 981 lines of the lane (91
   declarations) are *already* ported inside SM/FlatCarriers.lean (units U1–U3 of the flat-carriers work:
   `geoMarkSuccessor_position_cases`, `geoSmoothingSegment_positive_direction`, `geoOutSlot`,
   `geo_block_compression`, `geoCornerMark_add_one`, …, lines 2698–3200).
5. **Option (A) as literally stated is inadmissible and, when made admissible, *is* option (C).** The
   statement hash of an accepted row binds "the type and every local definition it uses"
   (ACCEPT_CYCLE.md:20–22; tools/check_lean.py:129 hashes `semantic_dependencies`). Changing the binder of
   `Carrier.Component`/`owner`/`smoothingSuccessor` changes the hashes of at least 14 accepted rows
   (def:smoothing, conv:selected-visits, lem:carriers, def:decomposition, def:uniform, def:positive-lift,
   def:C, lem:C-X1, prop:C-chamber, thm:C-S3, thm:C-S5, def:flat-carriers, cor:flat-carriers,
   def:interlace). So the only admissible "re-parametrisation" is a generalised lane *alongside* the
   accepted one with agreement lemmas — and that lane already exists in skeleton form: `SM.GeoCarrier`.
6. **Recommendation: (C) — complete `SM.GeoCarrier` into a full lane** (port the lane's theorems, ~6,500
   new lines, ~60 agent-hours, 1.5–2 days wall-clock with 5–6 parallel provers), state the CV rows on their
   printed domains through `CarrierGeometry.ofDiagrammatic` / `CornerGeometry.ofCV`, and prove Bridge:B4
   through the §4b agreement lemmas. Zero risk to accepted rows (additive modules only). The same lane is
   what SM prop:C-silent (row 107, pending) and CV:lem:silence need at the *centre* of a silent germ
   (`silent_curve_weak`, SM/SilentCenter.lean:46: the whole germ is `WeakGeneric` = tier 2), so most of
   this cost is not (C)-specific. (B) remains the fallback if the panel wants the R lane unblocked this
   week: it costs nothing now but narrows 12 CV rows + `CV.hyp_R`, and it does **not** avoid the geo-lane
   work for prop:C-silent / lem:silence / chamberinv(ii). (D) is rejected on fidelity (§4).

## 1. What the lane is (measurements)

Import closure of the Carrier lane restricted to lane modules (`SM/Carrier*.lean`, CarriersLemma,
SmoothingDefinition, SelectedVisitsConvention, UniformDefinition, DecompositionDefinition, InterlaceSupports,
Interlacement, InterlaceCount, InterlaceRelabel, InterlaceDefinition, GaussWord, GaussCyclicGap, CrossingPair,
GaussVisits, CornerStateSum, CX1, PositiveLiftDefinition): **53 files, 9,262 lines**. The theorem/definition
files proper (Carrier* + the six row modules): **44 files, 8,602 lines, 449 declarations, 72 definitions**.

Per-file `Generic` dependence (grep counts, 2026-09-14):

| file | lines | `hP : Generic` binders | `hP.1` | `hP.2` | external Generic lemmas used |
|---|---:|---:|---:|---:|---|
| CarrierCornerPolygon | 859 | 52 | 15 | 0 | `g1 … .2.1` (edge ≠ 0) ×2 (l.195, 665), `g1 … .2.2.1` (turn = ±1) ×1 (l.556), `generic_crossingGeometry` ×1 |
| CarrierSelfIntersections | 763 | 32 | 42 | 0 | `g1_edge_ne_zero` ×4 (l.40,205,289,332), `g1_vertex_off_edge_line` (l.51), `crossingPoint_interior` (l.60), `g1_adjacent_intersection` (l.245), `crossingPoint_unique` (l.255), `generic_crossingPoint_injective` ×3 (l.272,534,673), `g1_vertex_not_mem_edge` (l.316), `g1_remote_meeting` (l.603) |
| CarrierNoncrossing | 476 | 15 | 33 | 0 | none (plumbing only) |
| CarrierCrossings | 474 | 31 | 26 | 0 | none |
| CarrierNeighborSeparation | 257 | 9 | 14 | 0 | none |
| CarrierInheritedInsert / InheritedOrder / IndependentOrder | 234/230/118 | 4/5/4 | 0 | 0 | none |
| CarrierSameArc / MarkedArcLists / MarkedSegments / SegmentGeometry / AffineSegments | 189/134/180/147/102 | 8/6/3/7/5 | 37/8/17/22/5 | 0 | `g1 … .2.1` ×2 (SegmentGeometry l.98,133); rest none |
| CarrierMarks / Successor / Smoothing / TrueCorners / FilteredCycles / … (13 small files) | ≈1,650 | ≈75 | 6 | 0 | `visitPosition_injective hn hP` (Marks l.61, via GaussVisits) |
| CarrierVisitTwin, SplitList, AmbientTransport, SortedArcLists, FiberCard, FirstCornerBlock | 931 | 0 | 0 | 0 | hypothesis-free (shared as they are) |
| CarriersLemma / SmoothingDefinition / UniformDefinition / DecompositionDefinition / CX1 / CornerStateSum / PositiveLiftDefinition | 139/189/96/42/292/308/130 | 2/3/12/3/19/28/5 | 5/12/0/0/0/0/0 | 0 | `crossing_edgeParameter_det_ne_zero hP.1` (SmoothingDefinition l.173); `positiveLift`, `homfly`, `positiveLift_isPositive`, `positiveLift_writhe_eq_carrierCrossingCount`, `carrierShadow`, `carrierCrossingEquiv`, `eq_positiveLift_of_isPositive` (CornerStateSum, PositiveLiftDefinition; all on `SM.Generic` from SM/LinkPositiveLift.lean:211–602) |
| GaussVisits (defines `visitPosition`) | 109 | 2 | 3 | 0 | `crossingParameter_interior hn hP` ×3, `generic_crossingPoint_injective`, `crossingParameter_shift` |

Whole-`hP` consumers are the lane's own definitions (`owner hn hP` 436×, `Component hn hP` 223×,
`smoothingSuccessor hn hP` 191×, `markPosition hn hP.1` 186×, `ccpCornerPolygon hn hP` 115×, …): the
hypothesis is threaded, never opened.

## 2. The external interface, lemma by lemma, and its replacement

| accepted lemma consumed | uses | replacement on the geometric layer (already in the library) | tier |
|---|---:|---|:-:|
| `g1 hn P hP.1` `.2.1` (edge ≠ 0) (G1Consequences.lean:110) | 4 | `hP.1 : ∀ i, edge P i ≠ 0` (CrossingGeometry.lean:12) | 0 |
| `g1_edge_ne_zero hn hP.1` (Generic.lean:79) | 4 | `hP.1` | 0 |
| `generic_crossingPoint_injective hn hP` (Crossings.lean:126; uses `h.2`) | 4 | `crossingPoint_injective_of_geometry` (CrossingGeometry.lean:63) | 0 |
| `crossingParameter_interior hn hP.1` (Crossings.lean:112) | 3 | `crossingParameter_interior_of_geometry` (CrossingGeometry.lean:53); `geometricVisitPosition` (GeometricVisits.lean:12) | 0 |
| `crossingPoint_interior hP.1`, `crossingPoint_unique hP.1` (Crossings.lean:47,60) | 1+1 | `crossingPoint_interior_of_geometry`, `crossingPoint_unique_of_geometry` (CrossingGeometry.lean:28,42) | 0 |
| `g1_remote_meeting hP.1` (det ≠ 0 at a crossing) | 1 | `hP.2.1 i j hr x _ _ |>.2.2` (CrossingGeometry.lean:13–14) | 0 |
| `crossing_edgeParameter_det_ne_zero hn hP.1` (Chambers.lean:123) | 1 | same clause | 0 |
| `generic_crossingGeometry hn hP`, `crossingParameter_shift hn hP.1` | 1+1 | identity; shift lemma restated | 0 |
| `g1_vertex_off_edge_line hP.1`, `g1_vertex_not_mem_edge hP.1` (Generic.lean:104,113) | 1+1 | `CarrierGeometry.vertex_off` (the *segment* form suffices at both sites: CarrierSelfIntersections l.51 is inside an `edgeInterior` membership, l.316 an `edgeSegment` membership) | 1 |
| `g1 hn P hP.1` `.2.2.1` (turn = ±1) (CornerPolygon l.556) | 1 | `CornerGeometry.turn_ne` + `SignType` cases | 2 |
| `g1_adjacent_intersection hn hP.1` (G1Consequences.lean:47) | 1 | `turns_adjacent_intersection` (WeakGeometry.lean:44, hypothesis `∀ i, turn P i ≠ 0`) — or, for the *diagrammatic* domain of CV:lem:piececurve, a 40–60-line lemma from `CV.Diagrammatic` clause 3 (an antiparallel overlap would be a self-intersection with `det = 0`) | 2 (1 with the extra lemma) |
| `positiveLift hn hP S q hS` and its six companions (LinkPositiveLift.lean:596; `carrierShadow_generic` l.580 consumes `ccpCornerPolygon_regular/_tail_off/_transverse/_no_triple`) | 15 | none yet: a `geoPositiveLift` on tier 2 (unit U4 below; ~400 lines, a re-binding of LinkPositiveLift.lean:205–602) | 2 |

Consequently the CV rows split as: **tier 0** — CV:def:smoothing (135, definitions + count + inherited
order + trace), CV:lem:carriers (136 (i)–(iv)), CV:lem:carrierword (137), CV:def:pieces (139);
**tier 1** — the self-intersection clause consumed by CV:lem:piececurve (143) and CV:def:piecediagram (142)
("Let P be diagrammatic", d1_setup.tex:565, 594); **tier 2** — CV:def:wind (138, "Let P be generic",
d1:488), CV:def:X1 (146, d1:909), CV:selector_A (d6:1019–1021 "under the guards of def:generic(A)"),
CV:prop:chamberinv(ii) (147), CV:lem:silence (151). CV's own text confirms the tiering: lem:carriers says
"genericity is not needed here … what the argument reads is the Gauss word" (d1_setup.tex:363–365).

## 3. The prototypes (what was checked)

`CarrierGeometry.lean` (exit 0, standard axioms):
* `structure SM.CarrierGeometry (P) : Prop := (cg : CrossingGeometry P) (vertex_off : ∀ k e, ¬ incident k e → P k ∉ edgeSegment P e)`;
  `structure SM.CornerGeometry (P) : Prop extends CarrierGeometry P := (turn_ne : ∀ i, turn P i ≠ 0)`.
* Instances: `CarrierGeometry.ofDiagrammatic (hD : CV.Diagrammatic P)` (from `Diagrammatic.crossingGeometry`,
  CV/Setup.lean:1566, and clause 5 of `CV.Diagrammatic`, l.1388); `CornerGeometry.ofWeak (WeakGeneric P)`
  (WeakGeneric.lean:11: clauses 1,2,3,5 + `weak_crossingGeometry`); `CornerGeometry.ofGeneric hn (SM.Generic P)`;
  `CornerGeometry.ofCV (CV.Generic P)` (via `CV.Generic.weakGeneric`, CV/Setup.lean:1135);
  `CornerGeometry.weakGeneric` (converse, via `transverse_segments_unique`), hence
  `cornerGeometry_iff_weakGeneric : CornerGeometry P ↔ WeakGeneric P` — tier 2 introduces nothing new.
* Ported word for word from SM/CarrierSelfIntersections.lean (l.36–320): `cg_vertex_not_mem_edgeInterior`,
  `cg_crossingPoint_ne_vertex` (tier 1), `geoCsiEdge`, `geoCsiStart`, `geoCsi_segment_data`,
  `geoCsi_no_mark_in_gap`, `geoCsi_same_edge_disjoint_of_lt`, `geoCsi_same_edge_disjoint` (tier 0, on the
  accepted `geoMarkSuccessor_position_cases` / `geoMarkSuccessor_no_mark_between` /
  `geoSelectedMarkPerm_evaluation` of SM/FlatCarriers.lean:361, 2729, 2829), `cg_edgeSegment_meet`,
  `cg_edge_mem_of_crossingPoint_mem` (tier 2), `geoCsi_trace_eq_vertex` (tier 1); agreement lemmas
  `geoCsiEdge_eq_generic`, `geoCsiStart_eq_generic`; and the check that on an SM-generic polygon
  `geoSmoothingSuccessor (CornerGeometry.ofGeneric hn hP).cg S = smoothingSuccessor hn hP S` is the accepted
  `geoSmoothingSuccessor_eq_generic`. Edits needed relative to the original text: the hypothesis line, the
  eleven lemma-name swaps of §2, and one `have : Fact (1 < n) := ⟨by omega⟩` (kept `hn : 3 ≤ n` where the
  original used it).

`GeoCombinatorialSample.lean` (exit 0): `port_lane.py` applied to CarrierSingleSwitch.lean and
CarrierUnchangedComponent.lean (32 + 73 textual substitutions; the script drops declarations whose geo
counterpart already exists — here `geoSmoothingSuccessor_bijOn_owner`, FlatCarriersDefs.lean:326 — and
keeps hypothesis-free lemmas as they are). Zero edits to any proof body; one 6-line lemma
(`geoSmoothingSuccessor_union_of_disjoint`, port of CarrierSmoothing.lean:120) added because the geo layer
lacked it. This is the shape of the ≈2,500 lines of the combinatorial core (§5, unit U1).

## 4. The four options

Common to all: the CV rows 135–139, 142–147, 151, 164 must be *stated and proved* anyway (≈1,500–2,000
new lines: lem:carriers (iv) ~120, carrierword refinement ~150, piececurve/G4 400–600, X1 definitions and
unfolding lemmas ~300, chamberinv(ii)/silence assembly, selector_A). The table costs only what each option
adds *on top of that*; agent-hours are for prover subagents including compile loops, port into work/lean,
and the review round (not wall-clock; with 5–6 provers in parallel divide by ~4).

| | (A) re-parametrise the accepted lane | (B) documented narrowing | (C) complete the geo lane (recommended) | (D) transfer principle |
|---|---|---|---|---|
| **Fidelity of the CV rows** | printed domains, if it could be done | 12 rows + `CV.hyp_R` + `RProof.*` stated on `SM.Generic` sides ("domain narrowed to U_n^SM"); chamberinv(ii) only on SM-labelled chambers, lem:silence with an extra `hSM` binder — the R lane's *theorem* is then not CV's ax:R | printed domains: `hD : CV.Diagrammatic` for 135–137, 142–143; `hP : CV.Generic` for 138, 146, 147(ii), 164; events for 151 and `CV.hyp_R` | not faithful as a *definition* route: CV defines carriers, corners, turn signs, P_H, X₁ directly on P (d1:355, 487, 565, 908); defining them at a perturbation P′ and proving choice-independence is a different definition and would fail `definition_equivalence_reviewed` unless the direct objects on P exist — i.e. unless (C) is done |
| **Effort on top of the common work** | as literally stated: impossible (statement hashes of ≥ 14 accepted rows change, ACCEPT_CYCLE.md:20–22); made admissible = (C) with SM-flavoured names, same cost | 0 lines now; but the geo-lane work reappears for SM prop:C-silent (row 107) / CV:lem:silence / chamberinv(ii) (the centre of a silent germ is only `WeakGeneric`, SM/SilentCenter.lean:46) and for the R lane's cross-wall transport (G8), which is a `CrossingGeometry`-family transport whichever lane it is stated on | **≈6,500 lines, ≈60 agent-hours** (range 45–80): U1 ≈2,460 lines mechanical (6–8 h), U2 ≈2,100 lines tiers 1–2 (12–15 h), U3 ≈500 (4 h), U4 ≈500 (6 h), U5 ≈750 (10 h), U6 ≈200 (3 h), assembly + review + porting ≈10 h | density of `SM.Generic` inside the CV-generic locus (~400–600 lines of new real-algebraic-set arguments, no Mathlib lemma for "a nonzero polynomial's zero set has empty interior" in the needed form) + record transport (partly exists: `markTransport`, `geoMarkList_map_transport`, FlatCarriers.lean:236, 1533–1692) — and it transfers only the *combinatorial* statements; the geometric ones (trace, self-intersections, regularity, turn signs of corner polygons) still need the tier-1/2 port. Net: no saving over (C), plus an unfaithful definition. Reject. |
| **Risk to accepted rows** | fatal (rewrites) | none | none: additive modules only (`SM/GeoCarrier*.lean`, `CV/*.lean`); the accepted `SM.GeoCarrier` definitions are frozen by the flat-carriers rows and are used as they are | none |
| **Effect on the final theorem** (SM:corner_laws_and_soft ← Bridge.sm_R ← B1–B4 + RProof.cv_R) | — | unaffected: Bridge B1 lands every SM triple germ on SM-generic sides, `Bridge.sm_R` needs `cv_R` only there | unaffected: B4 is stated at SM-generic P; its proof gains ≈200 lines of agreement (unit U6): `geoComponentEquivGeneric`, `geoComponentCornerList_eq_generic` → `geoCornerPolygon` = `recastTuple` of `ccpCornerPolygon` (CChamber.lean:76 `recastTuple`, l.108 `polyComp_recastTuple`), `Ind_eq_generic` (CV/Events.lean:204), `geoPositiveLift` = `positiveLift` up to that recast | — |
| **Other beneficiaries** | — | — | SM prop:C-silent (107), the R-lane transports (R:exterior 168, availability 170, G8), CV:lem:silence direct proof (no detour through prop:C-silent + B4), CV:prop:chamberinv(ii) on CV chambers | — |

Why (B) does not actually save the geo-lane work. Under (B) CV:prop:chamberinv(ii) is stated on
SM-labelled chambers; the printed statement (CV chambers, d1:932–940) needs X₁ constant across the
non-guarded collinearity walls that lie *inside* a CV chamber, i.e. exactly a `CrossingGeometry`-family
transport of the carrier data — which is unit U5. CV:lem:silence under (B) is routed through SM
prop:C-silent (pending) whose own proof must read carriers at a `WeakGeneric` centre (`silent_curve_weak`);
the design report already flagged def:flat-carriers / lem:weak-carriers for this reason, and the
flat-carriers work (accepted 2026-09-13) built the first ≈1,000 lines of the geo lane to do it. So (B) is a
sequencing choice, not a saving; its real merit is that the R-lane *statements* could be fixed this week.

## 5. Execution plan for (C) — units

All new modules under `work/lean/SM/GeoCarrier*.lean` (namespace `SM.GeoCarrier`, `open Carrier`) and
`work/lean/CV/*.lean`; nothing under `SM/Carrier*.lean` or `SM/FlatCarriers*.lean` is touched. Hypothesis
tiers as in `CarrierGeometry.lean` (move it to `SM/GeoCarrierGeometry.lean`). Keep `hn : 3 ≤ n` exactly
where the original proofs use it (`Fact (1 < n)`, `exists_third_index`, three corners).

| unit | content (source files → target) | lines | est. hours | tier | depends on |
|---|---|---:|---:|:-:|---|
| **U0** | `CarrierGeometry` / `CornerGeometry`, instances, `↔ WeakGeneric`; the Diagrammatic adjacent-edge lemma (`Diagrammatic` clause 3 ⇒ adjacent closed edges meet only at the shared vertex) so that tier 1 can replace `turns_adjacent_intersection` in the self-intersection clause | 150 (80 done) | 2 | 1 | — |
| **U1** (mechanical, `port_lane.py`, 2 provers) | SingleSwitch, UnchangedComponent (done as sample), FilteredCycles, TrueCorners (rest), CycleList, SingleSupport, InheritedOrder, CurrentCycle, InsertOrbits, SameArc, MarkedArcLists, PendingPairs, InheritedInsert, IndependentOrder, ComponentCount, ComponentFibers, OrbitRefinement, ClosedTrace → `GeoCarrierCount.lean`, `GeoCarrierOrder.lean`; ends with `geo_independent_successor_components` (count = |S|+1, `GeoInheritsMarkOrder`, selected visits separated) | 2,460 | 6–8 | 0 | U0 |
| **U2a** | CarrierCrossings §1, §3, §5 (crossings of a carrier, corner directions, unselected non-neighbour ownership — §2, §4 are in FlatCarriers.lean:2889–2995), CarrierNeighborSeparation, CarrierNoncrossing → `GeoCarrierCrossings.lean`, `GeoCarrierNoncrossing.lean` | 1,100 | 6–8 | 0 | U1 |
| **U2b** | CarrierCornerPolygon §3–§7 (corner chain, `ccpCornerPolygon_block/_edge/_turn_*`, regular, ≥ 3 corners, trace; §0–2 are in FlatCarriers.lean:2996–3200), CarrierActualCornerBlock → `GeoCornerPolygon.lean` (`geo_carriers_clause_ii` at tier 2; the trace and edge clauses at tier 0) | 650 | 5–6 | 0/2 | U1 |
| **U2c** | CarrierSelfIntersections §5 (rest)–§9 (`IsSelfIntersection`, `IsTriplePoint`, `carrier_selfIntersections`) on top of the prototype's §0–§5 → `GeoCarrierSelfIntersections.lean` | 500 | 4–5 | 1 (2 only via U0's lemma removed) | U2a, U2b |
| **U3** | the row-level bundles on the geo lane: `GeoCarriersLemmaData` (mirror of CarriersLemma.lean:38–124), `GeoSmoothingData` (SmoothingDefinition.lean:39–150), uniform/mixed/rotation/leftTurns (UniformDefinition.lean:27–50), `geoWind`/`geoCarrierWeight`/`markTurn` lemmas (CX1.lean:24–140) | 500 | 4 | 2 | U2 |
| **U4** | `geoCarrierShadow`, `geoCarrierShadow_generic`, `geoPositiveLift`, writhe/crossing correspondence (LinkPositiveLift.lean:205–602 re-bound to `GeoComponent`), and `geoPositiveLift_eq_generic` (homfly agreement with `positiveLift` through `polyComp_recastTuple`) | 500 | 6 | 2 | U2b, U2c |
| **U5** | `GeoMarkTransport` between two `CrossingGeometry` polygons (CChamber.lean:112–560 re-bound; the side↔centre half exists: FlatCarriers.lean:1533–1692 `geoSmoothingSuccessor_markTransport`, `geoComponentCornerList_markTransport`, `geoCornerCount_markTransport`), path transport along a `CrossingGeometry` family with constant crossing set / parameter orders / turn signs (CChamber.lean:861–1216 re-bound), and the CV-chamber persistence lemma (guards keep sign along a path in a CV chamber ⇒ record constant; from CV/ChamberInv.lean:95–120 `Relevant`/`eval` continuity) | 750 | 10 | 2 | U3, U4 |
| **U6** | Bridge-B4 agreement package: `geoCornerPolygon_eq_generic` (recast), `geoWind_eq_generic`, `geoCarrierCrossings_eq_generic`, `Ind_eq_generic` re-export, `geoPositiveLift` = `positiveLift`; then `CV.X1 hn P (CV.generic_of_sm hn hG) = cornerStateSum hn hG` needs only lem:C-X1's selector identity (accepted `SM.C_X1`) | 200 | 3 | 2 | U3, U4 |
| **CV rows** (common work, not (C)-specific) | 135 def:smoothing, 136 lem:carriers (+ (iv)), 137 carrierword (+ refinement), 138 def:wind, 139 def:pieces, 142 piecediagram, 143 piececurve (G4), 146 def:X1, 164 selector_A, 147(ii), 151 — binders exactly as printed, proofs = the U1–U5 theorems applied to `(CarrierGeometry.ofDiagrammatic hD).cg` / `CornerGeometry.ofCV hP` | 1,500–2,000 | 20–30 | — | U1–U5 as listed in §2 |

Order and parallelism: U0 first (half a day, one prover); then U1 (2 provers, mechanical) ∥ U4's
shadow-generic part waits; U2a ∥ U2b after U1; U2c after both; U3 ∥ U4 ∥ U6 after U2; U5 last (needed only by
147(ii), 151 and the R lane's G8). The rows 135–139 can be stated as soon as U1–U2a land (tier 0);
138/146/164 after U3–U4. Acceptance mechanics unchanged (one row per declaration, statement review against
the CV excerpt; the review of each carrier row cites `CarrierGeometry.ofDiagrammatic` / `CornerGeometry.ofCV`
as the reading of "diagrammatic" / "generic" and `cornerGeometry_iff_weakGeneric` as the SM cross-reference).

Total (C)-specific: ≈6,500 new lines, ≈60 agent-hours (45–80), no accepted file modified. Wall-clock
with 5–6 provers and one assembler, following the flat-carriers/cchamber pattern (PLAN_FINAL + units +
assembler): about 2 days.

## 6. Risks

1. **Name collisions and drift with the accepted geo layer.** `SM.GeoCarrier` is frozen (flat-carriers rows);
   the port must *reuse* its declarations, never redeclare (the transformer's GEO check does this; 23 of the
   72 lane definitions and 91 of 449 declarations already have counterparts). A second, divergent
   `geoCornerPolygon` would break B4's agreement chain.
2. **`hn : 3 ≤ n` plumbing.** The geo layer dropped `hn`; several ported proofs need `Fact (1 < n)` or
   `exists_third_index` (seen once in the prototype). Mechanical, but the reviewer must check no statement
   silently gained `hn` where CV does not have it (CV fixes n ≥ 3 globally, d1:932 "Fix n ≥ 3", so this is
   harmless for the rows).
3. **Recast of corner counts in B4/U4.** `geoCornerCount` and `ccpCornerCount` are propositionally, not
   definitionally, equal on SM-generic polygons (`geoMarkList_eq_generic` is a `Perm.eq_of_pairwise` argument,
   FlatCarriersDefs.lean:644); the corner polygons are related by `recastTuple`. CChamber.lean already has the
   `recastTuple`/`polyComp_recastTuple`/`rotationNumber_recastTuple` toolkit, so this is bookkeeping, but it is
   the one place where "agreement" is not `rfl`.
4. **The positive lift on tier 2 (U4)** depends on `Shadow.single_generic_of` consuming the four geometric
   clauses (regular, tail-off, transverse, no triple point); all four are U2b/U2c outputs. If any turns out
   to need more than `CornerGeometry`, the fallback is to state def:X1 on `CV.Generic ∧ SM.Generic`-free
   `WeakGeneric` (still the printed domain, since `CV.Generic → WeakGeneric`).
5. **Schedule interaction with the R lane.** Under (C) the R-lane statements should be written against
   `SM.GeoCarrier` names from the start (`GeoComponent`, `geoOwner`, `geoWind`, `CV.X1`); if the panel wants
   the four X₁-free R rows stated this week, they can be (they do not mention carriers), and the carrier-
   dependent ones wait ≈2 days for U1–U3.
6. **Estimate confidence.** The two calibrations cover the two kinds of file (Generic-consuming geometric,
   and pure combinatorial); the untested kind is the long `SimpleGraph`/`Cycle` proofs of CarrierNoncrossing
   and CarrierInheritedOrder, which contain no Generic content but are the longest proofs — allow the upper
   end of the range if their `letI := markLinearOrder hn hP` instance plumbing resists renaming
   (`geoMarkLinearOrder` has the same shape, FlatCarriersDefs.lean:133).
