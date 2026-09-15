# CV-DOM — Analysis B (fidelity and end-to-end first)

Written 2026-09-14 by a Claude Code analyst subagent (claude-fable-5-1) of the pod executor, for the
CV-DOM decision panel (work/AUTHOR_NOTES.md, grep "CV-DOM"). Package root:
/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912 (paths below
are relative to it; `work/lean/` is the Lean project). Everything asserted about the library was checked
against the named files; the prototype `work/drafts/cvdom/CV_X1_prototype.lean` was checked with
`cd work/lean && lake env lean ../drafts/cvdom/CV_X1_prototype.lean` (exit 0; `sorry` only in the six
places listed in §6). Nothing under work/lean was written.

## 0. Summary

1. **The final theorem evaluates every CV carrier notion only at SM-generic polygons.** `Bridge.sm_R`
   applies `RProof.cv_R : CV.hyp_R` to `Bridge.eventOfTriple hn g h` (Bridge/B1.lean:126–134), whose
   curve IS the SM germ's curve, and every punctured value is `SM.Generic` by `g.generic_punctured`
   (prototype theorem `CV.eventOfTriple_sides_sm_generic`, proof term `g.generic_punctured t ht`). B4 is
   invoked only there; CV chamber constancy is not needed by `sm_R` at all (point values + accepted
   `prop_C_chamber`). So option (B) is *sufficient* for `SM.corner_laws_and_soft`.
2. **But (B) is not a faithful reading of the CV rows**, and (D) is not a faithful reading of the CV
   *definitions*; (A) in place is forbidden by the hash rule. Evidence in §2–§3.
3. **The cost question has changed since the scout's report.** A `CrossingGeometry`-parametrised
   carrier layer — marks, successor, reconnection, components, owner, corner list, corner polygon,
   corner turns, retained crossings, independence, selector — is ALREADY ACCEPTED as the local
   definitions of def:flat-carriers (work/lean/SM/FlatCarriersDefs.lean, namespace `SM.GeoCarrier`,
   1,257 lines), with the agreement layer `geo*_eq_generic` / `geoComponentEquivGeneric` on SM-generic
   polygons (FlatCarriersDefs.lean:638–724) and a first stock of theorems on `CrossingGeometry`
   (FlatCarriers.lean:361–460, 3253–3350, 4070, 4912). CV:def:interlace (accepted) already lives on
   `CrossingGeometry` (`CV.Ind`, `CV.N`, `CV.U`, CV/Events.lean:165–218). Hence **every carrier-dependent
   CV definition row can be stated on its printed binder today** (prototype §6), and the remaining
   work is porting *theorems* (not definitions) as new modules — nothing accepted is touched.
4. **Recommendation: option (C) realised on the accepted geo layer** ("C-geo"): CV rows stated natively
   on `CV.Generic` / `Diagrammatic` through `hP.crossingGeometry` / `hP.weakGeneric`; the carrier
   theorems ported as new `geo*` modules on `CrossingGeometry` (combinatorial tier) and `WeakGeneric`
   (geometric tier); B4 through the existing `_eq_generic` bridges. Estimate: ≈ 12,000 new library
   lines, of which ≈ 8,000 are a mechanical port (binder + two function names), ≈ 60 agent-hours
   (range 45–80) of prover time, parallelisable in 2–3 lanes, none of it on the critical path if
   started now (the critical path is G4/cb:products/phase-2 moves/the R obligations, identical under
   every option). Decision F2 of 2026-09-13 ("no narrowing") is *kept*; only its mechanism changes
   from "re-parametrise the Carrier lane" to "extend the accepted geo layer alongside it".

## 1. The final theorem chain and where each CV notion is evaluated

Chain (blueprint/ORDER.md:185–195; axiom-policy.json targets): `SM:corner_laws_and_soft` (191) ←
`Bridge:theorem` = `Bridge.sm_R : SM.hyp_R` (187) ← `R:cv_theorem` = `RProof.cv_R : CV.hyp_R` (185) +
`Bridge:B4` (159) + `Bridge:B1–B3` (accepted: Bridge/B1.lean:157 `B1`, :339 `B2`; Bridge/B3.lean:186
`B3`) + `prop:C-chamber` (accepted, SM/CChamber.lean:1378, bundle `CChamberData` :1372).

Proof of `sm_R` as printed (reference/BRIDGE/BRIDGE.md §3, lines 1443–1470) and as the library shapes
it: fix an SM simple triple germ `g : WallGerm n`, `h : g.TripleAt e f k`; `E := Bridge.eventOfTriple hn
g h` (curve := g.curve, generic_punctured := generic_of_sm ∘ g.generic_punctured, B1.lean:126–134); B2
gives `E.zeroSet = {G3, G4, G4, G4}`, B3 `E.Transversal`, so `E.IsSimpleRIII …` (CV/Events.lean:1131);
`RProof.cv_R` yields `X₁(E.curve t₊) = X₁(E.curve t₋)` for small `t₊ > 0 > t₋`; B4 at those two
polygons gives `X₁ = C`; `prop_C_chamber` identifies `C(E.curve t±)` with the side values of `SM.hyp_R`.

Consequences (all checked against the files):
- **Evaluation domain of X₁, wind, pieces, P_H, Ω₁, carriers in the final proof:** the polygons
  `(eventOfTriple hn g h).curve t`, `t ≠ 0`, i.e. `g.curve t` with `SM.Generic (g.curve t)`
  (`WallGerm.generic_punctured`, def:germ). Prototype: `CV.eventOfTriple_sides_sm_generic`.
- **B4 is only ever applied on SM-generic polygons.** Its printed part 5 ("value on the containing CV
  chamber", BRIDGE.md:1429–1441) is not consumed by `sm_R` when `cv_R` is stated with point values on a
  punctured neighbourhood (the form the R-lane drafts use: work/drafts/rlane/Statements_A.lean:351–431,
  `Punctured E δ t`); it is consumed only if `CV.hyp_R` is stated with CV-chamber values, which then
  needs CV:prop:chamberinv(ii).
- **What is stated on CV events but never evaluated off the SM locus by `sm_R`:** the twelve `RProof.*`
  obligations and `CV.hyp_R` quantify over all simple RIII events; their *proofs* must therefore handle
  CV-generic sides (bench A's witness, sm-1-polygons.tex:548–560, is CV-generic, not SM-generic).
- **Rows not on the target chain but in the package (must still be accepted for the stage check,
  ACCEPT_CYCLE.md:49–50):** CV:lem:smoothing/carriers/carrierword/wind/pieces/piecediagram/piececurve/
  X1/chamberinv/silence/selector_A/singleton_D_i (rows 135–147, 151, 164, 165). Their printed binders
  are CV-generic (def:wind d1_setup.tex:487–489 makes the point explicitly), diagrammatic
  (lem:carriers d1:362–365: "genericity is not needed here … what the argument reads is the Gauss
  word"; def:pieces sits in the diagrammatic subsection), or "any closed curve" (lem:carrierword
  d1:450–456).

## 2. Fidelity assessment of (B) and (D); what breaks on the SM locus

### (B) Documented narrowing — sufficient for the target, NOT a faithful reading of the rows

Sufficiency: §1. Everything `sm_R` needs is on SM-generic polygons; with `hSM : ∀ t ≠ 0, SM.Generic
(E.curve t)` added to `CV.hyp_R` and to the R rows, `Bridge.sm_R` still goes through because
`eventOfTriple` satisfies `hSM` by definition.

Fidelity failures (each is a "weaker domain" verdict under ACCEPT_CYCLE.md step 4):
1. CV:ax:R (d10_axioms.tex:18–24) quantifies over *every* simple transversal RIII event; OPEN_WORK.md
   item 4 says verbatim "prove CV ax:R on its entire printed simple/transversal forced-bundle domain",
   and the recorded decision F2 (work/AUTHOR_NOTES.md:2114–2126) says "A row is never accepted on a
   domain smaller than printed." (B) needs a reviewed scope change that overturns both.
2. CV:def:wind (d1:487–498) argues *for* the CV-generic binder ("the generic binder is part of this
   definition and not decoration"); stating it on SM-generic polygons replaces the discussed binder by a
   strictly stronger one (rem:fidelity d1:290–296 calls domain fidelity "load-bearing").
3. CV:lem:carriers is printed on *diagrammatic* polygons; SM-generic is two strict steps narrower
   (Diagrammatic ⊋ CV-generic ⊋ SM-generic; CV/Setup.lean:1382, 1710–1711 and `generic_of_sm` :1187).
4. **CV:prop:chamberinv(ii) cannot be stated as printed under (B).** "X₁ is constant on each chamber"
   refers to CV chambers (`CV.chamber`, CV/Setup.lean:1060, components of the CV locus); a CV chamber
   contains non-SM-generic points (pure cuts: three non-consecutive collinear vertices are CV-generic,
   CV G1 guards consecutive triples only) and hence several SM chambers. The scout's fallback (state
   it for P, Q in one *SM labelled chamber*, cv-lane-plan §147(3)) is a materially weaker theorem —
   it does not even imply constancy across an SM pure-cut wall inside one CV chamber (that is
   prop:C-silent's pure-cut clause, itself pending).
5. CV:lem:silence, CV:selector_A, cor:groupedknot, singleton_D_i: same narrowing; lem:silence's centre
   is only WeakGeneric, so under (B) the row is routed through SM prop:C-silent + B4 instead of its own
   proof (a proof substitution, to be declared).
6. The R rows (fixed names `RProof.*`) acquire a binder `hSM` that the RA text does not have
   (R_ATTACHMENT_WARRANTS.md:16–29 is about the CV event); the drafts already stated them without it
   (work/drafts/rlane/NOTES_A.md:16–28, NOTES_B.md:19–23, "Decision F2(A): no narrowing").

Review note (B) would require on every affected row (14 CV rows + CV:ax:R + 13 R rows + B4): "Domain
narrowed from U_n^CV (resp. diagrammatic) to U_n^SM ⊊ U_n^CV (witness sm-1:548–560). The final theorem
SM.corner_laws_and_soft is unaffected: Bridge.sm_R evaluates CV.X1 only at (eventOfTriple hn g h).curve
t, t ≠ 0, which are SM-generic by WallGerm.generic_punctured. CV:prop:chamberinv(ii) is stated on SM
labelled chambers (weaker than printed); CV:lem:silence is proved through SM prop:C-silent; CV:ax:R is
stated on the subclass of simple RIII events with SM-generic sides." Cost of the notes alone: 28 rows ×
(a reviewer reading the source, deciding "weaker but justified") ≈ 15–25 agent-hours, with a real chance
of rejection on rows 4–5 above. Net: (B) is cheap to *write* and expensive/uncertain to *accept*, and it
contradicts two written package rules.

### (D) Transfer principle — legitimate proof technique, unfaithful as a definition

CV's definitions are stated on P's own geometry: carriers are the curves obtained by smoothing P
(d1:355–360); corner turns are determinants of P's incoming/outgoing directions (d1:490–494); R(L) is
the rotation of the actual carrier (d1:920, def:rot); P_H is the HOMFLY of the diagram *the piece of P
presents* (d1:915–917, def:piecediagram). Defining `X1 P := X1^SM (perturb P)` replaces each definition
by the theorem "these data are constant along a perturbation", which is prop:chamberinv(ii) itself —
circular for that row and a definition-by-theorem for the others; a reviewer applying ACCEPT_CYCLE step 4
("same conclusion … definition_equivalence_reviewed") would reject it. As a *proof* technique it is
exactly what SM does for lem:weak-carriers (sm-3-statesum.tex:264–276: choose a generic P′ nearby with
the same signature; the combinatorial clauses transfer; "the geometric assertions are verified directly
at P") and what the library already does in places (`geometricInterlacementTransportIso`,
GeometricInterlacement.lean:86; `geoCornerCount_markTransport`, FlatCarriers.lean:1646). In our setting
it saves nothing: the combinatorial facts are the cheap sed-portable ones (§4), and the geometric facts
must be proved at P anyway. Keep (D) only as a tool where a transport lemma already exists.

### (A) In-place re-parametrisation — forbidden by the checker

The statement hash of an accepted row is `sha256` of `semantic_dependencies` (tools/check_lean.py:125–
130), which is the transitive closure of project constants used in the *type* and, for non-theorems,
the *body* (work/lean/Supplemental/Audit.lean:28–53). Changing `Generic`, `visitPosition`, `gaussList`,
`Component`, `smoothingSuccessor`, … changes the hashes of def:gauss, def:interlace, def:decomposition,
def:smoothing, conv:selected-visits, lem:carriers, def:uniform, def:positive-lift, def:C, lem:C-X1,
prop:C-chamber, thm:C-S3, def:flat-carriers, cor:flat-carriers, CV:def:interlace, Bridge:B1–B3, … (≥ 20
accepted rows) and forces their re-review. Not an option. (A)-as-a-copy is option (C) below.

## 3. What the Carrier lane actually needs from `Generic` (measured)

Files: work/lean/SM/Carrier*.lean (37 files, 7,411 lines), SmoothingDefinition.lean (189),
CarriersLemma.lean (139), UniformDefinition.lean, DecompositionDefinition.lean, CornerStateSum.lean
(308), CX1.lean (292), LinkPositiveLift.lean (846). (SM/Smoothing.lean, 8,216 lines, is the Chapter-3
*link-diagram* smoothing on `Shadow.Generic`, not the polygon carrier lane; it needs no port.)

- `hP.2` (SM G2) is used **0** times in the lane (16 uses in SM total, all outside the lane).
- `hP.1` (SM G1, all triples) is used 530 times, of which 178 are `markPosition hn hP.1`, 102
  `visitPosition hn hP.1`, 30 `crossingVisitBetween hn hP.1`, 10 `visitKey hn hP.1`, 6/5
  `visitPosition_interior/evaluation`, 4 `markKey`, 3 `selectedMarkPerm_evaluation`, and only **9**
  genuine G1 facts: `g1_edge_ne_zero` (3), `csi_edgeSegment_meet`/`csi_crossingPoint_ne_vertex` (2+2),
  `g1_vertex_not_mem_edge` (1), `csi_crossing_edges_det_ne_zero` (1), `crossing_edgeParameter_det_ne_zero`
  (1). Whole-`Generic` lemmas consumed: `visitKey_injective`, `visitPosition_injective`,
  `markPosition_injective`, `markKey_injective`, `generic_crossingPoint_injective` (CSI ×3,
  LinkPositiveLift), `crossingPoint_unique` (CSI:255), `g1_vertex_off_edge_line` (CSI:51, used only to
  get "vertex ∉ open interior of a non-incident edge").
- Every one has a counterpart on `CrossingGeometry`/`WeakGeneric`: `crossingParameter_interior_of_geometry`,
  `crossingPoint_unique_of_geometry`, `crossingPoint_injective_of_geometry` (CrossingGeometry.lean:27–59),
  `geometricVisitPosition_injective` (GeometricVisits.lean:22), `geoMarkPosition_injective`
  (FlatCarriersDefs.lean:108), transversality det ≠ 0 = CrossingGeometry clause 2, edges ≠ 0 = clause 1,
  turns ≠ 0 = WeakGeneric clause 2, vertex off non-incident closed edges = WeakGeneric clause 3
  (WeakGeneric.lean:11–19). The design note of the accepted geo layer says the same
  (FlatCarriersDefs.lean:15–20).
- `CV.Generic → WeakGeneric` (`Generic.weakGeneric`, CV/Setup.lean:1135), `→ CrossingGeometry` (:1154),
  `→ Regular` (:1163); `Diagrammatic → CrossingGeometry` (:1566); `SM.Generic → CV.Generic`
  (`generic_of_sm`, :1187 = B1(1)).

Conclusion: the right binders are `CrossingGeometry P` for the combinatorial tier (covers CV's
"diagrammatic": Diagrammatic ↔ CrossingGeometry ∧ vertex off non-incident segments, CV/Setup.lean:1631)
and the accepted `WeakGeneric P` for the geometric tier (no new predicate needed; the scout's
`CarrierGeometry` is not required). CV rows keep their printed binder `hP : CV.Generic P` and pass
`hP.weakGeneric` / `hP.crossingGeometry`.

### 3.1 What already exists on those binders (accepted, no work)

FlatCarriersDefs.lean (`SM.GeoCarrier`): `geoMarkPosition` (:77), `geoMarkKey/LinearOrder/List/Cycle`
(:127–165), `geoNextMark/PrevMark/MarkSuccessor` (:168–223), `geoSmoothingSuccessor` (:235),
`GeoComponent` (:258), `geoOwner` (:262, with `_eq_iff`, `_successor`, `_surjective`, `Fintype`),
`geoComponentMarkList` (:290), `geoComponentPlaneCycle` (:310), `geoSmoothingSegment` (:317),
`geoSmoothingSuccessor_bijOn_owner` (:326), `geoComponent_has_trueCorner` (:344),
`geoComponentCornerList/geoCornerCount/geoCornerMark/geoCornerPolygon` (:367–402), `geoCornerIndex`,
`geoCornerTurn` (:446), `geoCarrierCrossings` (:451), `GeoIndependent` (:457), `cornerSelector`,
`geoCarrierSelector` (:466–473); agreement: `geoMarkKey/List/Successor/SmoothingSuccessor_eq_generic`
(:638–673), `geoComponentEquivGeneric` (+`_owner`, :676–686), `geoComponentMarkList/PlaneCycle/
CornerList_eq_generic` (:688–724); spec `GeoCarrierSpec` (:737). FlatCarriers.lean: `GeoCarrierSpec.of_core`
(:390, every field but `traced_successor`/`inherited_pieces` on ANY CrossingGeometry),
`geoMarkSuccessor_no_mark_between` (:361), `geoSmoothingSegment_eq_generic` (:423),
`geoCarrierSpec_of_generic` (:434), `geoCarriers_are_cycles` (:538), `geoCornerCount_markTransport`
(:1646), `geoCornerPolygon_edge_data/edge/outEdge_eq_inEdge/edge_pred/turn_det/turn_eq_sign/
edge_ne_zero/not_antiparallel_of_det` (:3253–3350, under the hypothesis `TracedSuccessor`, :3147),
`geoCornerPolygon_eq_markPolygon` (:4070), `geoCornerTurn_eq_turn` (:4912). CV/Events.lean: `Ind`, `N`,
`U` (:165–177), `Ind/N/U_eq_generic` (:204–218), `interlace_definition` on `CrossingGeometry` (:318),
`interlace_generic_agree` (:336). Geometric Gauss API: GeometricVisits.lean, GeometricInterlacement.lean
(`geometricInterlacementGraph_eq_generic` is `rfl`, :40), GeometricRecords.lean
(`geometric_records_persist`, :63), CV/ChamberInv.lean (`Generic.eventually_generic` :128,
`isOpen_genericLocus` :134, `isPathConnected_chamber` :152 — chamberinv(i) is `chamberinv_i`, :176).

### 3.2 What is missing on those binders (the port)

Tier 1 (`CrossingGeometry` + `GeoIndependent`), combinatorial, currently `Generic` in binders only
(hP.1 = 0): CarrierInheritedOrder 230, CarrierInheritedInsert 234, CarrierOrbitRefinement 130,
CarrierInsertOrbits 134, CarrierIndependentOrder 118, CarrierSingleSupport 111, CarrierCurrentCycle 110,
CarrierCycleList 91, CarrierFilteredCycles 128, CarrierUnchangedComponent 116, CarrierSingleSwitch 104,
CarrierPendingPairs 107, CarrierMarkedArcLists 134, CarrierComponentFibers 117, CarrierComponentCount 122,
CarrierTrueCorners 117, CarrierActualCornerBlock 143, CarrierVisitTwin 142 (partly P-free) ≈ 2,400 lines
→ deliverables `geoComponent_card` (= |S|+1), `GeoInheritsMarkOrder`, `geoTracedSuccessor_of_independent`
(closes `GeoCarrierSpec` on the CV locus), `geo_noncrossing` (CarrierNoncrossing 476, uses
`markPosition`→`geoMarkPosition`), `geo_neighbor_visits_separated`/`geo_nonneighbor_visits_together`
(CarrierNeighborSeparation 257), `geo_selected_visits_separated`. P-free files shared as is (no port):
CarrierSplitList 222, CarrierSortedArcLists 156, CarrierFirstCornerBlock 133, CarrierFiberCard 86,
CarrierAmbientTransport 192 (Generic = 0 in all five).

Tier 2 (`WeakGeneric`), geometric: CarrierMarkedSegments 180, CarrierAffineSegments 102,
CarrierSegmentGeometry 147, CarrierClosedTrace 148, CarrierSameArc 189, CarrierCrossings 474,
CarrierCornerPolygon 859 (≈ 250 lines already on `CrossingGeometry` in FlatCarriers.lean:3253–3350),
CarrierSelfIntersections 763, SmoothingDefinition-style and CarriersLemma-style bundles ≈ 3,000 lines →
deliverables `geoCornerPolygon_regular`, `geoCornerCount_ge_three` (= CV:selector_A), `geoCornerPolygon_
turn_ne_zero/turn_vertex/turn_smoothing`, `geoCornerPolygon_trace`, `geo_self_intersections` (transverse,
not at corners, no triple point), `geoCarrierCrossings` facts. Then LinkPositiveLift on the CV locus
(846 lines: `geoCarrierShadow`, `_generic`, `geoPositiveLift`, writhe = crossings), uniform/rotation/
coefficient/wind definitions (≈ 300 lines) and the agreement layer with the accepted lane (≈ 400 lines:
corner polygon up to `cast` on the count via `geoComponentCornerList_eq_generic` and `markPolygon`,
crossings, selector = `carrierWeight`, positive lift, Ω₁ = `cornerCoefficient` given cb:products).

R-lane support: the accepted Triple* lane (SM/Triple*.lean, ≈ 900 lines) is on `WallGerm`/`Generic`;
NOTES_A.md:222–224 records that its six lemmas use `SM.Generic` only through `generic_edgeParameters_ne`
= `CV.Generic.crossParam_ne` (CV/Setup.lean:1130) → re-derive on CV events, ≈ 700 lines.

## 4. Option comparison

| option | fidelity to the CV rows | effort (new lines / agent-hours) | risk to accepted rows | effect on the final theorem |
|---|---|---|---|---|
| (A) in-place re-parametrisation of the Carrier lane | faithful | 0 new lines but rewrites ≥ 20 accepted declarations' semantic dependencies | **forbidden**: invalidates statement hashes (Audit.lean:30–53) of def:gauss … thm:C-S3, def:flat-carriers; re-review of all | none if redone, but blocks everything meanwhile |
| (A′) copy of the lane with weaker binder, ignoring the accepted geo layer (the scout's "2–3 prover-weeks") | faithful | ≈ 10,000–14,000 lines / 80–120 h | none (new constants only) | unblocks CV rows and R lane after the port |
| (B) documented narrowing to U_n^SM | **not faithful** for 14 CV rows, CV:ax:R, 13 R rows; chamberinv(ii) unstatable as printed; contradicts OPEN_WORK item 4 and decision F2 | ≈ 0 lane lines; ≈ 1,200 row lines; 28 scope-change reviews ≈ 15–25 h with real rejection risk | none | sufficient (§1); B4 part 5 dropped; hyp_R weaker than printed |
| (C) CV-native layer on `CrossingGeometry`/`WeakGeneric`, realised on the ACCEPTED geo layer (recommended) | faithful; lem:carriers even on its printed *diagrammatic* binder | ≈ 12,000 lines (≈ 8,000 mechanical port; 1,400 chamberinv(ii); 800 silence; 700 Triple on CV events; 400 agreement; 700 CV row bodies) / ≈ 60 h (45–80), 2–3 lanes in parallel | none (new modules under `SM.GeoCarrier`/`CV`; accepted `geo*` names reused, never redefined) | B4 through `geoComponentEquivGeneric` and friends; sm_R unchanged; CV:ax:R on its printed domain |
| (D) transfer principle as definitions | **not faithful** (definitions replaced by chamber-invariance theorems; circular for chamberinv(ii)) | transport lemmas ≈ the size of the combinatorial port; geometric facts still proved at P | none | sufficient but unreviewable as "same definition" |
| (D′) transfer as a proof technique inside (C) | n/a (tool) | saves little; use where transport lemmas exist (`geoCornerCount_markTransport`, `geometricInterlacementTransportIso`) | none | — |

The R lane (≈ 7,500 lines by the scout's per-row figures) and its phase-2 dependencies (G10/G11 moves,
cb:products, G4) are identical under every option and are the actual critical path; the CV-DOM work of
(C) runs beside them.

## 5. Recommendation and review-note template

**Adopt (C) on the accepted geo layer. Keep decision F2's content ("no narrowing"), change its
mechanism** from "re-parametrise the Carrier lane (Gap G1, 2–3 weeks)" to "extend `SM.GeoCarrier`
alongside the accepted lane; state CV rows on their printed binders now; port theorems as new modules".
Rationale: it is the only faithful option that is admissible under the hash rule; the definitional half
is already accepted; the port is mechanical (two function names, one binder) because `hP.2` is unused
and `hP.1` reaches the lane through `markPosition`/`visitPosition` only (§3); and it also serves
SM-side needs (silent-centre transport for prop:C-silent, SM lem:weak-carriers).

Review note to attach to every CV carrier-dependent row (and to B4): "Stated on the printed binder
(`CV.Generic` / `Diagrammatic`). Carriers, corners, corner polygons and retained crossings are the
accepted `SM.GeoCarrier` objects read through `hP.crossingGeometry`; on SM-generic polygons these are the
accepted def:smoothing/lem:carriers objects by `geoComponentEquivGeneric`, `geoComponentCornerList_eq_generic`
and the `geo*_eq_generic` bridges (FlatCarriersDefs.lean:638–724). The ownership convention at a selected
crossing is SM conv:selected-visits (the SAME `selectedMarkPerm`), a disambiguation CV leaves implicit
(cv-lane-plan §135(2))." For CV:ax:R additionally: "sides read as point values on a punctured
δ-neighbourhood; equal to the printed chamber values by def:event + prop:chamberinv(ii)."

## 6. Prototype: `work/drafts/cvdom/CV_X1_prototype.lean`

Typechecks against the built library (`lake env lean`, exit 0). Contents, on the printed binder
`hG : CV.Generic P`:
- def:smoothing/def:wind on the geo layer: `CV.weight := geoCarrierSelector`, `CV.wind`, `CV.CarrierUniform`.
- def:pieces: `CV.residualGraph`, `CV.Piece` (Mathlib `ConnectedComponent` of the induced graph on
  `CV.U`), `pieceLabels`, `pieceWrithe`, `piecesOn` ("assigned to L by lem:carriers(iv)").
- lem:piececurve/def:piecediagram TYPES: `pieceSupport`, `pieceCarrier` (Gap G4, bodies `sorry`),
  `pieceDiagram := (Shadow.single ⟨…, geoCornerPolygon …⟩).positiveDiagram _`, `piecePolynomial := homfly ∘ pieceDiagram`.
- def:X1: `groupedPoly`, `groupedWrithe`, `carrierR := CV.rotAbs (geoCornerPolygon …) _`, `slot`,
  `Omega1 := coeffAt slot 0 groupedPoly`, `X1 hn P hG := ∑ S ∈ Ind hG.crossingGeometry, wind * ∏ q, Omega1`,
  and the row bundle `X1DefinitionData` with `X1_definition` PROVED (empty conventions, factor, state
  sum, def:wind's "wind ≠ 0 forces uniform").
- `eventOfTriple_sides_sm_generic` (proved): the evaluation points of `sm_R` are SM-generic.
- `X1_eq_cornerStateSum` (B4 shape, `sorry`) and `hyp_R'` (the printed CV:ax:R on the printed domain,
  point-value form; primed so as not to pre-empt the fixed name).
`sorry` count: 6 — `pieceSupport`, `pieceCarrier` (G4), `three_le_geoCornerCount`, `geoCornerPolygon_
cvRegular`, `carrierShadow_generic` (tier-2 port, unit C3), `X1_eq_cornerStateSum` (B4, unit C5).

## 7. Execution plan (units, dependencies, estimates)

Naming: new modules `work/lean/SM/GeoCarrier*.lean` (library, namespace `SM.GeoCarrier`, prefix `geo`,
never redefining an accepted name) and `work/lean/CV/*.lean` (rows). Each ≤ 600 lines. Port recipe per
file: copy the accepted file; `hP : Generic P` → `hP : CrossingGeometry P` (tier 1) or `hW : WeakGeneric P`
with `hP := weak_crossingGeometry hW` (tier 2); `S ∈ independentSupports hn hP` → `GeoIndependent hP S`;
`markPosition hn hP.1` → `geoMarkPosition hP`; `visitPosition hn hP.1` → `geometricVisitPosition hP`;
`Component/owner/smoothingSuccessor/markSuccessor/markList/componentMarkList/ccpCorner*` → `geo*`; the
≈ 10 genuine `Generic` lemma sites → the `_of_geometry` / WeakGeneric-clause counterparts (§3); drop `hn`
where unused. Compile with `lake env lean` per file.

| unit | content | depends on | est. lines | est. hours | who |
|---|---|---|---|---|---|
| C0 | Record the decision in AUTHOR_NOTES (F2 mechanism = C-geo), review-note template (§5), naming policy | — | — | 0.5 | executor |
| C1 | Statement rows now, no port: CV:def:smoothing (135; bundle from `GeoCarrierSpec.of_core` fields available without `TracedSuccessor`, plus `traced_successor` as a forward clause closed by C2), CV:def:wind (138; from the prototype + `geoCornerPolygon_turn_eq_sign`), CV:def:pieces (139; prototype), CV:def:X1 statement module (146; prototype minus the G4 bodies, mapped once C4 lands) | C0 | 450 | 4 | 1 prover |
| C2 | Tier-1 port (§3.2): inherited order, refinement, component count, noncrossing, neighbour separation → `geoComponent_card`, `GeoInheritsMarkOrder`, `geoTracedSuccessor_of_independent`, `geoSmoothingSegment_mem_edgeSegment`, `geo_noncrossing`, `geo_neighbor_visits_separated`, `geo_nonneighbor_visits_together`; then CV:lem:carriers (136) on `Diagrammatic` incl. clause (iv) (G3, ~120 lines) and CV:lem:carrierword (137, refinement clause ~150) | C0 | 2,700 + 270 | 10 | 2 provers (file groups: {InheritedOrder, Insert, OrbitRefinement, InsertOrbits, IndependentOrder, SingleSupport, CurrentCycle, CycleList, FilteredCycles} / {UnchangedComponent, SingleSwitch, PendingPairs, MarkedArcLists, ComponentFibers, ComponentCount, TrueCorners, Noncrossing, NeighborSeparation}) |
| C3 | Tier-2 port on `WeakGeneric`: segments, closed trace, crossings, same-arc, corner polygon (regular, ≥ 3 corners, turns ≠ 0, vertex/smoothing turn values, trace), self-intersections; CV:selector_A (164) falls out | C2 | 3,000 | 12 | 2 provers ({MarkedSegments, AffineSegments, SegmentGeometry, ClosedTrace, SameArc, Crossings} / {CornerPolygon, SelfIntersections}) |
| C4 | Positive lift and coefficient on the CV locus: `geoCarrierShadow(_generic)`, `geoPositiveLift`, writhe = crossings; `geoCarrierRotation`, uniform/mixed; lem:piececurve (143, Gap G4, greedy `pieceSupport` with the three invariants) and def:piecediagram (142); close the two G4 `sorry`s of the prototype → CV:def:X1 row (146) | C3 | 850 + 500 + 100 | 10 | 1–2 provers |
| C5 | Agreement layer and B4: `geoCornerPolygon_eq_generic` (via `geoComponentCornerList_eq_generic` + `markPolygon`, `cast` on the count), `geoCarrierCrossings_eq_generic`, `geoCarrierSelector_eq_carrierWeight`, `geoPositiveLift_eq_generic`, `Omega1_eq_cornerCoefficient` (needs cb:products, row 102, and `groupedWrithe = carrierCrossingCount`); `Bridge.B4 : X1 hn P (generic_of_sm hn hP) = cornerStateSum hn hP` via `SM.C_X1` | C4, cb:products | 400 + 300 | 6 | 1 prover |
| C6 | CV:prop:chamberinv(ii) (147ii) on CV chambers: port CChamber.lean's path-constancy (`cornerStateSum_path_constant`) to `X1` on the CV locus using `CV.Generic.eventually_*` (ChamberInv.lean:55–130), `GeometricRecords`, `RotationContinuity`, `LinkMoves` | C4 | 1,200–1,400 | 8 | 1 prover |
| C7 | CV:lem:silence (151): geo layer at the WeakGeneric silent centre (`silent_curve_weak`, SilentCenter.lean), `geometric_records_persist`, rotation constancy of `geoCornerPolygon` along the germ, piece polynomials via `gausscode_polynomial` (F4) | C4, C6's transport lemmas | 800 | 6 | 1 prover |
| C8 | R-lane support: the six Triple* lemmas on CV events (`crossParam_ne` in place of `generic_edgeParameters_ne`), `VisitsAdjacent → GaussAdjacent` bridge; then the R rows exactly as drafted in work/drafts/rlane (no `hSM`) | C2 (for carriers), C0 | 700 (+ R rows as scouted) | 5 (+ R lane) | R-lane provers |
| C9 | Judge/assembler: merge, `lake build` of the new modules, review prompts with the §5 note | C1–C8 | — | 6 | executor |

Totals: ≈ 12,000 new lines; prover time ≈ 60 agent-hours (C1 4 + C2 10 + C3 12 + C4 10 + C5 6 + C6 8 +
C7 6 + C8 5) + 6 h assembly; with the usual 1.3–1.5 contingency 60–80 h wall-clock-agent time, achievable
in 2–3 parallel lanes in about a day and a half of executor time. Critical path: C2 → C3 → C4 → C5/B4
(≈ 38 h serial), which is shorter than the phase-2 move/G10/G11 work the R lane waits for anyway.

## 8. Risks

1. Dependent types in the agreement layer: `geoCornerPolygon : LabelledTuple (geoCornerCount …)` versus
   `ccpCornerPolygon : LabelledTuple (ccpCornerCount …)` — equal counts, different terms. Mitigation: B4
   needs only turn lists, counts, rotation numbers and homfly values; transport through the accepted list
   equality `geoComponentCornerList_eq_generic` and `markPolygon_rotate_apply` (FlatCarriers.lean:4076),
   or state `HEq`/`cast` lemmas once.
2. The port may meet proofs that used `visitLinearOrder hn hP` or `gaussList hn hP` (Generic-typed
   instances) under the hood; the geo counterparts (`geoMarkLinearOrder`, `geometricGaussList`, both with
   `_eq_generic`) exist, but each such site is a manual fix. Budgeted in the 1.5× contingency.
3. chamberinv(ii) on CV chambers (C6) is new mathematics for the library, not a port: a CV chamber
   contains SM walls, so the local-constancy argument must be run at every CV-generic point; the
   ingredients exist (`Generic.eventually_generic`, `geometric_records_persist`, rotation continuity,
   planar-isotopy invariance of `homfly` as used by CChamber.lean). Medium risk; not on the sm_R path.
4. Module growth/compile time: +12k lines next to a 5.7k-line FlatCarriers.lean; keep modules ≤ 600
   lines and import only `SM.FlatCarriersDefs` (not `SM.FlatCarriers`) where possible.
5. Name hygiene: never redefine an accepted `geo*` name (hash rule is per accepted row; the geo layer is
   in def:flat-carriers' dependency closure). New names only; if a bundle field of `GeoCarrierSpec` is
   wanted with a different hypothesis, state a new lemma.
6. Review load moves from "scope-change notes" (B) to ordinary "same domain" reviews (C): lower risk,
   but each CV row review must be told to check the `geo`-object identification against the printed
   words (template §5).
7. If the executor prefers CV rows to depend on a CV-owned namespace rather than `SM.GeoCarrier`, add
   `abbrev`s in `CV/Carriers.lean` (zero cost) — do not copy definitions.

## 9. Evidence index (file:line)

- Target chain: blueprint/ORDER.md:185–195; axiom-policy.json `targets`; TARGETS.md:1–20.
- sm_R proof shape: reference/BRIDGE/BRIDGE.md:1443–1470; B4 part 5 :1429–1441; §0 scope :100.
- `eventOfTriple`: work/lean/Bridge/B1.lean:126–134; `B1` :157; `B2` :339; `B3` Bridge/B3.lean:186.
- `prop_C_chamber`/`CChamberData`: work/lean/SM/CChamber.lean:1372–1385.
- CV domain texts: reference/R/CV/d1_setup.tex:220–238 (def:generic), 263–296 (prop:fidelity,
  rem:fidelity), 315–344 (diagrammatic), 355–365 (def:smoothing, lem:carriers binder), 450–456
  (carrierword), 487–512 (def:wind binder), 514–520 (pieces), 908–930 (def:X1), 932–938
  (chamberinv), 1300–1320 (silence); d10_axioms.tex:18–24 (ax:R); d6_vertexedge.tex:1017–1020.
- Package rules: OPEN_WORK.md (item 4 and last paragraph); ACCEPT_CYCLE.md:13–22, 26–30, 49–50;
  tools/check_lean.py:125–130; work/lean/Supplemental/Audit.lean:28–53; work/AUTHOR_NOTES.md:2114–2126
  (F2), 3047–3053 (CV-DOM panel).
- Accepted geo layer: work/lean/SM/FlatCarriersDefs.lean:15–20 (design note), 77–473 (definitions),
  638–724 (agreement), 737–807 (`GeoCarrierSpec`); work/lean/SM/FlatCarriers.lean:361–460, 538–550,
  1646, 3147, 3253–3350, 4070, 4912; work/AUTHOR_NOTES.md:2813 (acceptance).
- CV on CrossingGeometry: work/lean/CV/Events.lean:165–218, 274–342; CV/Setup.lean:1051, 1135, 1154,
  1163, 1187, 1382, 1566, 1631, 1710–1711; CV/ChamberInv.lean:55–182.
- Lane measurements: `grep -c hP.1 / hP.2 / Generic` over work/lean/SM/Carrier*.lean etc. (§3);
  consumers: CarrierSelfIntersections.lean:35–51, 205, 255, 272, 316, 534, 673; SmoothingDefinition.lean:173;
  CarrierMarks.lean:60; GaussVisits.lean:48–95; GaussWord.lean:17–24; CarrierCornerPolygon.lean:39–46,
  550–558, 579, 598, 609, 679, 691, 778; LinkPositiveLift.lean:160–166, 211–221, 580–598, 820.
- Counterparts: work/lean/SM/CrossingGeometry.lean:11–59; WeakGeneric.lean:11–19; GeometricVisits.lean:
  12–71; GeometricInterlacement.lean:16–41, 86; GeometricRecords.lean:55–63.
- R-lane drafts already on the CV locus: work/drafts/rlane/NOTES_A.md:14–28, 216–224; NOTES_B.md:17–23;
  Statements_A.lean:351–431.
- SM's own transfer-by-perturbation proof (D as technique): reference/SM/sm-3-statesum.tex:249–276.

## 10. Cross-reference to Analyst A (read after this report was drafted)

work/drafts/cvdom/ANALYSIS_A.md (same directory) reaches the same recommendation independently —
"(C): complete `SM.GeoCarrier` into a full lane, ≈ 60 agent-hours (range 45–80)" — from the
measurement side, with two prototypes that strengthen the effort claim here: `CarrierGeometry.lean`
(a hand port of CarrierSelfIntersections §0–§5, the lane file with the most `Generic` consumers, onto
`SM.GeoCarrier`) and `GeoCombinatorialSample.lean` + `port_lane.py` (a *zero-hand-edit* mechanical port
of two binder-only combinatorial files). The two line counts differ (A ≈ 6,500 for the lane port; here
≈ 8,000 for the lane port plus ≈ 4,000 for chamberinv(ii) on CV chambers, lem:silence, the Triple*
re-derivation on CV events, the agreement layer and the CV row bodies) because they count different
scopes; the agent-hour totals coincide (≈ 60). Where the two differ in design — A proposes a named
two-tier predicate `SM.CarrierGeometry`/`SM.CornerGeometry` (with `CornerGeometry ↔ WeakGeneric`), this
report uses the accepted `CrossingGeometry`/`WeakGeneric` directly — the choice is cosmetic (A proves
the equivalence); the judge may pick either, provided CV rows keep the printed binder `CV.Generic` /
`Diagrammatic`. The fidelity conclusions of §2 (B not faithful, D not faithful as definitions, A in place
forbidden) and the evaluation-domain fact of §1 (sm_R evaluates X₁ only at SM-generic polygons, proved
in the prototype) are this report's own contribution and are not contradicted by A.
