# CV-DOM — DECISION (judge), 2026-09-14 ~02:40 UTC / 10:40pm ET

Written by the judge subagent (claude-fable-5-1) of the pod executor for the CV-DOM decision panel
(work/AUTHOR_NOTES.md 2026-09-14 ~01:28Z). Inputs: ANALYSIS_A.md + CarrierGeometry.lean +
GeoCombinatorialSample.lean + port_lane.py (Analyst A); ANALYSIS_B.md + CV_X1_prototype.lean
(Analyst B); the scout report work/reports/cv-lane-plan-20260913.md (F1-F5, G1, rows 135-147, 151,
164, §5-§7); the code under work/lean. Paths below are relative to the package root
/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912 unless absolute.
Nothing under work/lean was written.

## 0. Decision

**Option (C), realised on the ALREADY-ACCEPTED geometric carrier layer `SM.GeoCarrier`
(work/lean/SM/FlatCarriersDefs.lean, frozen by the accepted rows def:flat-carriers and cor:flat-carriers).**
Decision F2 of 2026-09-13 ("no narrowing for any row") is KEPT in content; only its *mechanism* changes,
from "re-parametrise the Carrier lane (Gap G1, 2-3 prover-weeks)" to "port the Carrier lane's THEOREMS as
new `SM/GeoCarrier*.lean` modules onto the accepted geo DEFINITIONS, state every carrier-dependent CV row
on its printed binder, prove Bridge:B4 through the accepted `geo*_eq_generic` agreement lemmas". No accepted
declaration is modified; every new module is additive.

Why this and not the others (details §2):
- (A) "re-parametrise the Carrier lane" is inadmissible as literally stated: the statement hash of an
  accepted row is the sha256 of the transitive `semantic_dependencies` of its declaration
  (work/lean/Supplemental/Audit.lean:29-53 — constants of the type and, for non-theorems, of the body,
  closed transitively; tools/check_lean.py:125-130). Changing the binder of `Carrier.Component`, `owner`,
  `smoothingSuccessor`, `markPosition`, `visitPosition` changes the hash of every accepted row that reaches
  them (def:gauss, def:interlace, def:smoothing, conv:selected-visits, lem:carriers, def:decomposition,
  def:uniform, def:positive-lift, def:C, lem:C-X1, prop:C-chamber, thm:C-S3, thm:C-S5, def:flat-carriers,
  cor:flat-carriers, CV:def:interlace, Bridge:B1-B3 — at least 18 rows) and forces their re-review. The only
  admissible form of (A) — a generalised lane *alongside* the accepted one with agreement lemmas — IS (C),
  and its definitional half already exists and is accepted.
- (B) documented narrowing is *sufficient* for SM:corner_laws_and_soft (verified: `Bridge.sm_R` applies
  `RProof.cv_R` to `Bridge.eventOfTriple hn g h`, Bridge/B1.lean:126-134, whose punctured values are
  `SM.Generic` by `g.generic_punctured`; the prototype theorem `CV.eventOfTriple_sides_sm_generic` proves it)
  but it is NOT a faithful reading of the CV rows: it narrows 12 CV rows + CV:ax:R + the 13 `RProof.*` rows
  (28 scope-change reviews), it contradicts OPEN_WORK.md item 4 ("prove CV ax:R on its entire printed
  simple/transversal forced-bundle domain") and the recorded decision F2 ("A row is never accepted on a
  domain smaller than printed"), CV:prop:chamberinv(ii) cannot even be *stated* as printed on the SM locus
  (a CV chamber contains SM pure-cut walls: three non-consecutive collinear vertices are CV-generic), and it
  does not avoid the geo-lane work (SM prop:C-silent, CV:lem:silence and chamberinv(ii) all read carriers at
  `WeakGeneric` centres / along `CrossingGeometry` families). It saves statements this week at the price of a
  written contradiction and a real rejection risk. Rejected; kept only as the emergency fallback of §7.
- (D) a transfer principle is a legitimate *proof technique* (SM's own lem:weak-carriers proof does it,
  and the library has transport lemmas: `geoCornerCount_markTransport`, `geometricInterlacementTransportIso`)
  but unfaithful as a *definition*: CV defines carriers, corner turns, R(L), P_H and X1 directly on P's own
  geometry (d1_setup.tex:355-360, 490-494, 908-930); a perturbation-based definition is a different
  definition (and circular for chamberinv(ii)), and the density lemma "SM-generic is dense in the CV locus"
  is new real-algebraic work with no Mathlib lemma in the needed form. It saves nothing because the geometric
  clauses must be proved at P anyway. Rejected as a definitional route; allowed inside (C) proofs where a
  transport lemma already exists.
- Between (C) and (B), (C) is the one with the smaller risk to accepted declarations (none for either) and
  the only one with no fidelity debt; its cost is bounded and mostly mechanical (§1, §5).

## 1. What the judge verified (2026-09-14, `source /workspace/envs/lean/env.sh; cd work/lean`)

| claim (analyst) | check | result |
|---|---|---|
| The three prototypes typecheck (A, B) | `lake env lean ../drafts/cvdom/{CV_X1_prototype,CarrierGeometry,GeoCombinatorialSample}.lean` | exit 0 ×3; `CV_X1_prototype` has exactly the six declared `sorry` (lines 98, 101, 106, 111, 116, 221 = pieceSupport, pieceCarrier, three_le_geoCornerCount, geoCornerPolygon_cvRegular, carrierShadow_generic, X1_eq_cornerStateSum); the other two have none |
| `hP.2` (SM G2) is never used by the lane (A: 0, B: 0) | `grep -c "hP\.2"` over SM/Carrier*.lean, SmoothingDefinition, CarriersLemma, Uniform/DecompositionDefinition, CornerStateSum, CX1, InterlaceSupports, GaussVisits, PositiveLiftDefinition, SelectedVisitsConvention | 0 in every file |
| `hP.1` uses are plumbing (A: 307, B: 530 incl. GaussWord) | `grep -o "hP\.1" \| wc -l` over the lane files | 313; the genuine G1 sites are the 28 listed below |
| The lane's genuine `Generic` consumers (A's table §2) | `grep -n "g1_\|generic_crossingPoint_injective\|crossingParameter_interior\|crossingPoint_interior\|crossingPoint_unique\|crossing_edgeParameter_det_ne_zero\|crossingParameter_shift\|generic_crossingGeometry\|g1 hn\|visitPosition_injective\|visitKey_injective"` | 28 sites: CarrierCornerPolygon 195, 556, 567, 665; CarrierMarks 77; CarrierSegmentGeometry 98, 133; CarrierSelfIntersections 40, 51, 60, 205, 245, 255, 272, 289, 316, 332, 534, 603, 673; SmoothingDefinition 173; GaussVisits 51, 52, 62, 73, 91, 98, 102. Every one has a `CrossingGeometry`/`WeakGeneric` counterpart already in the library (A §2 table checked: `CrossingGeometry` clauses 1-3, `crossingPoint_{interior,unique,injective}_of_geometry`, `geometricVisitPosition(_injective)`, `geoMarkPosition_injective`, `turns_adjacent_intersection`, `crossing_det_ne_zero_of_geometry`) |
| Lane size (A: 37 files / 7,411 lines; B: same) | `wc -l SM/Carrier*.lean` | 37 files, 7,411 lines; six files are hypothesis-free (AmbientTransport, FiberCard, FirstCornerBlock, SortedArcLists, SplitList, VisitTwin: 931 lines) and are shared as they are |
| The geo layer is accepted and complete at the definition level (A, B) | lean-declarations.json: def:flat-carriers `SM.flat_carriers_definition`, cor:flat-carriers `SM.flat_carriers` both `accepted`; FlatCarriersDefs.lean 77-473 defines geoMarkPosition, geoMarkKey/LinearOrder/List/Cycle, geoNext/PrevMark, geoMarkSuccessor, geoSmoothingSuccessor, GeoComponent, geoOwner (+Fintype), geoComponentMarkList/PlaneCycle, geoSmoothingSegment, geoComponentCornerList, geoCornerCount (+NeZero), geoCornerMark, geoCornerPolygon, geoCornerIndex, geoCornerTurn, geoCarrierCrossings, GeoIndependent, cornerSelector, geoCarrierSelector; agreement 638-724 (`geoMarkKey/List/Successor/SmoothingSuccessor_eq_generic`, `geoComponentEquivGeneric`, `geoComponentMarkList/PlaneCycle/CornerList_eq_generic`); `GeoCarrierSpec` 737-807 | confirmed; FlatCarriers.lean has 85 `geo*` theorems, incl. `GeoCarrierSpec.of_core` (390: every field except `traced_successor`/`inherited_pieces` on ANY `CrossingGeometry`), `geoMarkSuccessor_position_cases` (2729), the CarrierMarkedSegments port (2725-2889), CarrierCrossings §2/§4 (2889-2995), CarrierCornerPolygon §0-2 (2996-3143), `TracedSuccessor` (3147) and the corner-polygon edge/turn lemmas under it (3253-3350), the generic-transfer pattern `polyOfList`/`generic_corner_props`/`generic_geoCornerPolygon_props`/`generic_geoCornerTurn_{vertex,visit}` (3358-3425), `geoCornerPolygon_eq_markPolygon` (4070), `geoCornerTurn_eq_turn` (4912) |
| Hash rule binds transitive definitions (A, B) | Supplemental/Audit.lean 29-53 (`semanticDependencies`: worklist over `getUsedConstants` of the type, plus the body for non-theorems, plus constructors; closed transitively over project modules); check_lean.py 125-130 | confirmed — (A) in place is inadmissible |
| CV binders as printed (A, B) | reference/R/CV/d1_setup.tex 355-365 (def:smoothing; lem:carriers "Let P be diagrammatic … genericity is not needed here"), 450-456 (carrierword: any closed curve; "in particular P generic"), 487-498 (def:wind: "Let P be generic … the generic binder is part of this definition and not decoration"), 514-520 (def:pieces), 565 (piecediagram: "For a diagrammatic parent P"), 592-600 (piececurve: "Let P be diagrammatic"), 908-930 (def:X1: "Let P be generic"), 932-940 (chamberinv: CV chambers), 1300-1312 (silence: silent event), d6_vertexedge.tex 1017-1020 (selector_A: "Under the guards of def:generic(A)"), d10_axioms.tex 18-24 (ax:R: every simple RIII event) | confirmed |
| CV.Generic → WeakGeneric → CrossingGeometry; Diagrammatic ↔ CrossingGeometry ∧ vertex-off (n ≥ 3); SM.Generic → CV.Generic | CV/Setup.lean 1135 `Generic.weakGeneric`, 1154 `Generic.crossingGeometry`, 1566 `Diagrammatic.crossingGeometry`, 1630 `diagrammatic_iff`, 1187 `generic_of_sm` | confirmed |
| `Regular` does not require nonzero turns; the positive lift needs only regular/tail-off/transverse/no-triple | SM/RegularLocus.lean:12 (`Regular P := ∀ i, RegularPair (edge P (i-1)) (edge P i)`), LinkPositiveLift.lean:160-188 (`Shadow.single_generic_of`), LinkDiagram.lean:394 (`Shadow.Generic`) | confirmed — hence the piece diagram can be built at tier 1 (§3, ruling R4) |
| Recast toolkit exists (A risk 3, B risk 1) | CChamber.lean 76-110 (`recastTuple`, `rotationNumber_recastTuple`, `regular_recastTuple`, `turn_recastTuple`, `forall_turn_recastTuple`, `polyComp_recastTuple`) and FlatCarriers.lean 3358-3425 (`subst` along the accepted list equality) | confirmed — two working patterns for the one non-`rfl` agreement point |
| No name collision for the new tier predicate | `grep -rn "CarrierGeometry\|CornerGeometry" --include=*.lean work/lean` | none |
| New modules are picked up | work/lean/lakefile.toml globs `SM.+`, `CV.+`, `RProof.+`, `Bridge.+` | confirmed |
| R lane already stated on CV events without hSM (B) | work/drafts/rlane/NOTES_FINAL.md §0 ("Domain — F2(A), no narrowing … No SM genericity anywhere"), Statements_FINAL.lean (exit 0, X1 enters only as an arbitrary summand `F`); AUTHOR_NOTES 3165-3168 (R-lane units G1/F1 launched on CV events) | confirmed — (C) is the option consistent with work already in flight |
| `SM.hyp_R` | `grep -rn hyp_R work/lean` | not yet declared; its form is fixed when def:C's wall-law rows are stated (checker fixes the name only) |

Row status (lean-declarations.json, 111/192 accepted): CV:def:polygon/regular/guarded/generic/diagrammatic/interlace/record/homfly/rot/turnlift/event/silent, lem:guardconst/uniformrot/fulltwist, ax:homfly/gausscode, Bridge:B1-B3 accepted; CV:def:smoothing (135), lem:carriers (136), lem:carrierword (137), def:wind (138), def:pieces (139), def:piecediagram (142), lem:piececurve (143), def:X1 (146), prop:chamberinv (147), lem:silence (151), selector_A (164), singleton_D_i (165), CV:ax:R, the 13 R rows, Bridge:B4, Bridge:theorem pending. cb:products (102) and prop:C-silent (107) pending (both on B4's / silence's path independently of CV-DOM).

## 2. Fidelity argument (the AUTHOR_NOTES entry the executor should record)

Record the following verbatim under a heading `## CV-DOM decided: F2 mechanism = (C) on the accepted geo layer — 2026-09-14 <time>`:

> **Decision (CV-DOM panel: 2 analysts + judge; reports work/drafts/cvdom/ANALYSIS_A.md, ANALYSIS_B.md,
> DECISION_FINAL.md).** Decision F2 of 2026-09-13 stands: no carrier-dependent CV row, and neither CV:ax:R nor
> any `RProof.*` row, is stated on a domain smaller than printed. Its mechanism is changed. The Carrier lane
> (`hP : SM.Generic P`) is NOT re-parametrised — rewriting the binder of `Carrier.Component`/`owner`/
> `smoothingSuccessor` would change the statement hash (Supplemental/Audit.lean `semanticDependencies`) of
> ≥ 18 accepted rows. Instead the accepted geometric carrier layer `SM.GeoCarrier` (SM/FlatCarriersDefs.lean,
> local definitions of def:flat-carriers: `geoMarkPosition`, `geoMarkSuccessor`, `geoSmoothingSuccessor`,
> `GeoComponent`, `geoOwner`, `geoComponentMarkList`, `geoComponentCornerList`, `geoCornerCount`,
> `geoCornerPolygon`, `geoCornerTurn`, `geoCarrierCrossings`, `GeoIndependent`, `geoCarrierSelector`, all on
> `hP : CrossingGeometry P`) is completed into a full lane by porting the Carrier lane's THEOREMS as new
> modules `SM/GeoCarrier*.lean` (namespace `SM.GeoCarrier`, prefix `geo`, never redefining an accepted name),
> in three hypothesis tiers: tier 0 `CrossingGeometry P` (marks, successor, carriers, count, inherited order,
> noncrossing, neighbour separation, pieces, trace); tier 1 `SM.CarrierGeometry P` := `CrossingGeometry P` ∧
> (∀ k e, ¬ incident k e → P k ∉ edgeSegment P e), which is CV "diagrammatic" (`CV.diagrammatic_iff`, n ≥ 3)
> (self-intersections of a carrier, regular corner polygon, positive lift); tier 2 the accepted `WeakGeneric P`
> (nonzero turns of the corner polygon, def:wind, selector_A). `CV.Generic → WeakGeneric → CarrierGeometry →
> CrossingGeometry` and `CV.Diagrammatic → CarrierGeometry` are one-line theorems (CV/Setup.lean:1135, 1154,
> 1566; `diagrammatic_iff` 1630).
>
> **Measured basis.** `hP.2` (SM G2) is used 0 times in the 37 lane files; `hP.1` 313 times, all as the Prop
> argument of `markPosition/visitPosition hn hP.1`; the lane's whole mathematical dependence on `Generic` is 28
> lemma sites (CarrierSelfIntersections ×13, CarrierCornerPolygon ×4, GaussVisits ×7, SegmentGeometry ×2,
> Marks ×1, SmoothingDefinition ×1), each with a `CrossingGeometry`/`WeakGeneric` counterpart in the library,
> plus the SM positive lift (`SM.Link.positiveLift`, on `SM.Generic`), which is re-bound at tier 1. Two
> prototypes compiled: a hand port of CarrierSelfIntersections §0-§5 onto the tiers (work/drafts/cvdom/
> CarrierGeometry.lean, 367 lines, exit 0, no sorry) and a zero-hand-edit mechanical port of two combinatorial
> files (GeoCombinatorialSample.lean, 169 lines, exit 0, no sorry; transformer port_lane.py). A third prototype
> (CV_X1_prototype.lean) states CV:def:X1 on its printed binder `hG : CV.Generic P` over the accepted geo layer
> with the DEFINE-row bundle proved (exit 0; `sorry` only in the six separately-rowed places).
>
> **Fidelity.** Every carrier-dependent CV row is stated on its printed binder: `hD : CV.Diagrammatic P` for
> CV:def:smoothing (d1:355), lem:carriers (d1:362-365 "genericity is not needed here"), lem:carrierword
> (d1:450-456), def:pieces (d1:514), def:piecediagram (d1:565 "diagrammatic parent"), lem:piececurve (d1:592);
> `hG : CV.Generic P` for def:wind (d1:487-489), def:X1 (d1:909), selector_A (d6:1017-1020), prop:chamberinv(ii)
> (d1:932-940, CV chambers); `E : CV.Event n`, `E.Silent` for lem:silence (d1:1300); `E.IsSimpleRIII` for
> CV:ax:R (d10:18-24) and the `RProof.*` rows. No scope change; ordinary "same domain" reviews. CV's carriers
> are read as the accepted `SM.GeoCarrier` objects through `hD.crossingGeometry` / `hG.crossingGeometry`; on
> SM-generic polygons these ARE def:smoothing's objects by the accepted `geoSmoothingSuccessor_eq_generic`,
> `geoComponentEquivGeneric`, `geoComponentCornerList_eq_generic` (FlatCarriersDefs.lean:638-724). The ownership
> convention at a selected crossing is SM conv:selected-visits (the same `selectedMarkPerm`), a disambiguation
> CV leaves implicit (cited in each review). The final theorem is unaffected: `Bridge.sm_R` evaluates `CV.X1`
> only at `(Bridge.eventOfTriple hn g h).curve t`, `t ≠ 0`, which are `SM.Generic` (`WallGerm.generic_punctured`;
> `CV.eventOfTriple_sides_sm_generic` in the prototype), and there `Bridge.B4` identifies `CV.X1` with the
> accepted `cornerStateSum` through the agreement lemmas and the accepted `SM.C_X1` (lem:C-X1) — B4 itself is
> printed on SM-generic representatives (BRIDGE.md:639), so nothing in the target chain changes domain.
>
> **Three documented readings (not scope changes; each review must cite them):** (i) lem:carrierword's
> printed generality over "a closed curve C with finitely many transverse double points" is realised on the
> carriers of a diagrammatic polygon P and its refinement clause (S ⊆ S′ both independent ⇒ every carrier of
> S′ lies in one carrier of S with the induced order) — the only instances the CV text consumes (lem:piececurve
> Step 5 applies it to daughter carriers); (ii) def:piecediagram's "parent curve with every double point outside
> H erased" is the datum (restricted word + rotation system, d1:580-590) realised by the piece curve C_H of
> lem:piececurve, so `CV.pieceDiagram H` is the positive lift (divide convention = `Diagram.IsPositive`) of the
> carrier of S ∪ K_H that carries H; (iii) `hn : 3 ≤ n` is carried where the geo lemmas need it (CV fixes n ≥ 3
> globally, d1:932). **One form decision:** `CV.hyp_R` is stated in the printed chamber-value form — for every
> simple RIII event, `X1 (E.curve t₊) = X1 (E.curve t₋)` for ALL parameters t₊ > 0 > t₋ of the event (the two
> sides ARE the two chambers of the event, def:event d1:1080-1083); `RProof.cv_R` proves it from the R lane's
> punctured-δ form (`RProof.cv_R_near`) and CV:prop:chamberinv(ii) (constancy of X1 along each connected side).
>
> **Cost (judge's estimate).** ≈ 7,000-7,500 new lane lines (≈ 2,450 pure renaming, the rest binder-and-lemma
> swaps), ≈ 850 positive lift, ≈ 700 agreement + B4, plus the common work every option pays (CV row bodies incl.
> Gaps G3/G4 ≈ 2,000; chamberinv(ii) on CV chambers ≈ 1,300; silence ≈ 800; Triple* lemmas on CV events ≈ 700):
> ≈ 12,000-13,500 lines, ≈ 95 prover agent-hours (range 75-125), of which ≈ 55-60 are (C)-specific. Critical
> path U0 → U1 → U2 → U4 → U6 ≈ 30 serial hours; with 5-6 provers ≈ 2-3 days wall-clock, beside (not ahead of)
> the phase-2 move / cb:products / G10-G11 work the R lane waits for under every option. No accepted file is
> modified. Emergency fallback if the R-lane statements must be frozen before U1-U3 land: state them
> parametric in `E : CV.Event n` as already drafted (they mention X1 only as a summand), never with `hSM`.

## 3. Rulings that provers must follow (naming and shape)

R1. **Tiers and names.** Tier 0 = the accepted `CrossingGeometry P` (SM/CrossingGeometry.lean:11). Tier 1 =
    NEW `structure SM.CarrierGeometry (P : LabelledTuple n) : Prop := (cg : CrossingGeometry P) (vertex_off :
    ∀ k e : ZMod n, ¬ incident k e → P k ∉ edgeSegment P e)` (Analyst A's prototype, kept). Tier 2 = the
    accepted `WeakGeneric P` (SM/WeakGeneric.lean:11) — Analyst A's `CornerGeometry` is DROPPED (A proved
    `CornerGeometry ↔ WeakGeneric`; a second name for an accepted predicate only costs review questions).
    Helpers: `CarrierGeometry.ofWeak`, `CarrierGeometry.ofGeneric hn`, `WeakGeneric.carrierGeometry` (SM side,
    CV-free module SM/GeoCarrierGeometry.lean); `CarrierGeometry.ofDiagrammatic`, `CarrierGeometry.ofCV`,
    `carrierGeometry_iff_diagrammatic (hn)` on the CV side (CV/Carriers.lean). Tier-2 lemmas take
    `hW : WeakGeneric P` and use `weak_crossingGeometry hW` / `hW.carrierGeometry`; proof irrelevance makes
    `geoOwner hP S` for different `hP` proofs definitionally equal, so tiers mix freely.
R2. **Independence.** On the geo side use the accepted `GeoIndependent hP S`; on the CV side the row binder is
    `hS : S ∈ CV.Ind hP` (accepted CV:def:interlace); U0 provides `CV.mem_Ind_iff_geoIndependent : S ∈ Ind hP ↔
    GeoIndependent hP S`. Never `IsDecomposition hn hP` (that is `SM.Generic`-bound).
R3. **Names.** New library modules `work/lean/SM/GeoCarrier*.lean`, namespace `SM.GeoCarrier`, `open Carrier`,
    prefix `geo` for ported definitions/lemmas (`X hn hP` → `geoX hP`; lemma without a mapped prefix → `geo_X`);
    port_lane.py's GEO check: a declaration whose `geo*` name already exists in FlatCarriersDefs/FlatCarriers is
    NOT re-declared (references resolve to the accepted one). Redefining or shadowing an accepted `geo*` name is
    forbidden (it is in def:flat-carriers' dependency closure). Row modules `work/lean/CV/*.lean`,
    `work/lean/Bridge/B4.lean`; names `CV.<label>_definition` (DEFINE rows, one `Prop` bundle, one field per
    printed sentence) and `CV.<label>` (PROVE rows), fixed names `CV.hyp_R`, `RProof.*`, `Bridge.B4`, `Bridge.sm_R`.
R4. **Tier of the corner-polygon geometry.** `geoCornerPolygon_regular`, `_tail_off`, `_transverse`, `_no_triple`,
    `geo_self_intersections` are to be proved at tier 1 (`hG : CarrierGeometry P`), using U0's fold-back
    exclusion lemma in place of `turns_adjacent_intersection` (`Regular` forbids only zero/antiparallel
    consecutive edges, RegularLocus.lean:12; at a vertex corner antiparallel in/out edges would put P(k+2) on
    edge k or P k on edge k+1, excluded by `vertex_off` for n ≥ 3; at a smoothing corner det ≠ 0 is
    `CrossingGeometry` clause 2). Only `turn ≠ 0` at vertex corners is tier 2. Consequence: `geoPositiveLift`
    and hence def:piecediagram / lem:piececurve are statable on `CV.Diagrammatic` as printed. If a prover finds a
    genuine tier-2 need in this group, stop and report — do not silently move the row to `CV.Generic`.
R5. **`hn : 3 ≤ n`.** Keep it exactly where the source proofs use it (`geoMarkSuccessor_position_cases hn`,
    `exists_third_index`, `Fact (1 < n)`); never add it to a CV row statement that CV states without it
    (`chamberinv_i` already shows the `chamberinv_i_of_three_le` pattern if a row needs both forms).
R6. **`CV.hyp_R` form** (printed chamber values): 
    `def CV.hyp_R : Prop := ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : Event n) (e f g : ZMod n) h3 h4e h4f h4g,
     E.IsSimpleRIII e f g h3 h4e h4f h4g → ∀ (tp tm : E.Parameter), 0 < tp.val → tm.val < 0 →
     X1 hn (E.curve tp) (E.generic_punctured tp _) = X1 hn (E.curve tm) (E.generic_punctured tm _)`.
    The R lane delivers `RProof.cv_R_near` (the same with `∃ δ > 0, tp.val < δ → -δ < tm.val → …`, the form of
    work/drafts/rlane `Punctured E δ t`); `RProof.cv_R : CV.hyp_R` = `cv_R_near` + side constancy from
    `CV.chamberinv_ii` (each side image `E.curve (Ioo 0 radius)` is connected inside the CV locus, hence in one
    CV chamber — `CV.Event.sideChamber` of the accepted def:event). `Bridge.sm_R` uses `cv_R` at one pair (tp, tm)
    with the SM germ's `g.curve`.
R7. **`Bridge.B4` shape**: `structure Bridge.B4Data : Prop` with `pointwise : ∀ n [NeZero n] (hn : 3 ≤ n) (P)
    (hP : SM.Generic P), CV.X1 hn P (CV.generic_of_sm hn hP) = SM.cornerStateSum hn hP` (BRIDGE.md (17), the
    field `sm_R` consumes) and `sides : ∀ hn (g : WallGerm n) e f k (h : g.TripleAt e f k) (t : g.SideParameter)
    (b : Bool), SM.cornerStateSum hn (g.sideTuple b t).2 = CV.X1 hn Q (hQ)` for every `Q` in the CV side chamber
    of `Bridge.eventOfTriple hn g h` (BRIDGE.md (18); proof = `pointwise` + accepted `SM.prop_C_chamber` +
    `CV.chamberinv_ii`). `theorem Bridge.B4 : B4Data`.

## 4. Review note each affected row must carry (not a scope change — a "same domain" note)

Template for CV:def:smoothing, lem:carriers, lem:carrierword, def:wind, def:pieces, def:piecediagram,
lem:piececurve, def:X1, selector_A, prop:chamberinv(ii), lem:silence (fill the binder):

> "Stated on the printed binder (`hD : CV.Diagrammatic P` / `hG : CV.Generic P` / `E : CV.Event n`); no domain
> change (CV-DOM decision, AUTHOR_NOTES 2026-09-14). The carriers, their marks, corners, corner polygons, turns
> and retained crossings are the accepted `SM.GeoCarrier` objects (def:flat-carriers, SM/FlatCarriersDefs.lean)
> read through `hD.crossingGeometry` / `hG.crossingGeometry`; `Ind(G_P)` is the accepted `CV.Ind` (CV:def:interlace).
> On SM-generic polygons these are the accepted def:smoothing / lem:carriers objects by `geoSmoothingSuccessor_eq_generic`,
> `geoComponentEquivGeneric`, `geoComponentCornerList_eq_generic` (FlatCarriersDefs.lean:638-724). The ownership of
> the two visits of a selected crossing follows SM conv:selected-visits (the same `selectedMarkPerm`), a
> disambiguation the CV text leaves implicit. The reviewer checks: same binder as printed, same quantifiers, each
> printed sentence = one bundle field, and that the `geo*` object named in each field is the one the sentence
> describes."

Additional sentence per row:
- lem:carrierword: "The printed generality over an arbitrary closed curve C is realised on the carriers of P
  (clauses 1-2) and on daughter carriers via the refinement clause (clause 3); these are the only instances the
  CV text consumes (lem:piececurve Step 5)."
- def:piecediagram: "`CV.pieceDiagram H` is the positive lift (`Shadow.positiveDiagram`, divide convention =
  `Diagram.IsPositive`, LinkDiagram.lean:547) of the piece curve C_H of lem:piececurve (d1:602-611: 'the
  construction and not a description of its result'); 'erasing' a double point is realised as smoothing it into
  the carrier of S ∪ K_H, whose Gauss word is the parent word restricted to H (lem:piececurve's conclusion)."
- def:X1: "R(L) is the accepted `CV.rotAbs` (CV:def:rot) of the carrier's corner polygon (regular by
  `geoCornerPolygon_regular`); P_H is `homfly (pieceDiagram H)` (CV:def:homfly); wind is CV:def:wind's."
- prop:chamberinv(ii): "Chambers are `CV.chamber` (CV:def:generic (B)); constancy is asserted on CV chambers,
  which contain SM pure-cut walls — no SM-chamber fallback."
- CV:ax:R (`CV.hyp_R`): "Sides are the two chambers of the event (def:event d1:1080-1083), rendered as `X1` at
  every positive and every negative parameter of the event; equal to the chamber values by prop:chamberinv(ii)."
- Bridge:B4: "Field `pointwise` is (17) on SM-generic labelled representatives, as printed; field `sides` is
  (18). `CV.X1` at an SM-generic P is evaluated through `CV.generic_of_sm hn hP` (B1(1)); the identification with
  `cornerStateSum` goes through the agreement lemmas of SM/GeoCarrierAgreement.lean, lem:C-X1 (`SM.C_X1`) and
  cb:products."
- `RProof.*` rows: "Domain `E : CV.Event n`, `E.IsSimpleRIII …` as printed in the RA files; no `hSM`."

## 5. Execution plan — parallel prover units

Conventions: one prover per unit unless stated; every unit is a draft under work/drafts/cvdom/<unit>/ checked
with `cd work/lean && lake env lean <file>` (never `lake build`, never writing under work/lean); the assembler
ports into work/lean as in the flat-carriers / cchamber PLAN_FINAL pattern. Port recipe per source file
(port_lane.py does the renaming): binder `(hn : 3 ≤ n) {P} (hP : Generic P)` → `{P} (hP : CrossingGeometry P)`
[tier 0] / `(hG : CarrierGeometry P)` [tier 1] / `(hW : WeakGeneric P)` [tier 2]; `S ∈ independentSupports hn hP`
→ `GeoIndependent hP S`; `markPosition hn hP.1` → `geoMarkPosition hP`; `visitPosition hn hP.1` →
`geometricVisitPosition hP`; lane names → `geo*` (DEFMAP in port_lane.py, extended with `componentCycle`,
`InheritsMarkOrder`, `carrierCrossingCount`, `IsSelfIntersection`, `IsTriplePoint`); the 28 `Generic` sites →
their `_of_geometry` / clause counterparts (table in ANALYSIS_A.md §2); `hn` kept where used. Line estimates
are new lines; hours are prover agent-hours including compile loops.

| unit | module(s) | exact deliverables (statements to produce) | lines | hours | tier | depends on |
|---|---|---|---:|---:|:-:|---|
| **U0** | SM/GeoCarrierGeometry.lean; CV/Carriers.lean (part) | `structure SM.CarrierGeometry` (R1) with `ofWeak`, `ofGeneric hn`, `WeakGeneric.carrierGeometry`; `CarrierGeometry.adjacent_edges_meet (hn : 3 ≤ n) (hG : CarrierGeometry P) {i j} (hij : i ≠ j) (hadj : adjacent i j) : (j = i + 1 ∧ edgeSegment P i ∩ edgeSegment P j = {P j}) ∨ (i = j + 1 ∧ edgeSegment P i ∩ edgeSegment P j = {P i})` (the tier-1 replacement of `turns_adjacent_intersection`, shape as consumed at CarrierSelfIntersections.lean:245); `cg_vertex_not_mem_edgeInterior`, `cg_crossingPoint_ne_vertex` (from A's prototype); CV side: `CarrierGeometry.ofDiagrammatic (hD : CV.Diagrammatic P)`, `CarrierGeometry.ofCV (hG : CV.Generic P)`, `carrierGeometry_iff_diagrammatic (hn)`, `CV.mem_Ind_iff_geoIndependent (hP) (S) : S ∈ Ind hP ↔ GeoIndependent hP S`, `CV.mem_U_iff`, `CV.mem_N_iff` re-exports | 200 | 2-3 | 1 | — |
| **U1a** (mechanical) | SM/GeoCarrierCount.lean | port of CarrierSingleSwitch (done), CarrierUnchangedComponent (done), CarrierSmoothing residue (`geoSmoothingSuccessor_union_of_disjoint` done), CarrierSuccessor/CarrierMarks residue not in FlatCarriersDefs, CarrierTrueCorners, CarrierFilteredCycles, CarrierCycleList, CarrierCurrentCycle, CarrierSingleSupport, CarrierComponentFibers, CarrierComponentCount, CarrierPendingPairs, CarrierInsertOrbits, CarrierOrbitRefinement → `theorem geoComponent_card (hn) (hP : CrossingGeometry P) (hS : GeoIndependent hP S) : Fintype.card (GeoComponent hP S) = S.card + 1`; `geo_selected_visits_separated (hP) (hS) (v : Visit P) (hv : v.1 ∈ S) : geoOwner hP S (Sum.inr v) ≠ geoOwner hP S (Sum.inr (visitTwin v))`; `geoOwner_refines (hP) (hS' : GeoIndependent hP S') (hSS' : S ⊆ S') (q' : GeoComponent hP S') : ∃ q : GeoComponent hP S, ∀ m, geoOwner hP S' m = q' → geoOwner hP S m = q` (carrierword clause 3) | 1,350 | 4-5 | 0 | U0 |
| **U1b** (mechanical) | SM/GeoCarrierOrder.lean | port of CarrierInheritedOrder, CarrierInheritedInsert, CarrierIndependentOrder, CarrierMarkedArcLists, CarrierSameArc, CarrierAffineSegments, CarrierSegmentGeometry, CarrierClosedTrace → `def GeoInheritsMarkOrder (hP) (S) : Prop` (port of `InheritsMarkOrder`), `geoInheritsMarkOrder_of_independent (hn) (hP) (hS)`, `geoTracedSuccessor_of_independent (hn) (hP) (hS) (q) : TracedSuccessor hP S q` (FlatCarriers.lean:3147), `geoSmoothingSegment_mem_edgeSegment (hn) (hP) (S) (a) {u} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : geoSmoothingSegment hP S a u ∈ edgeSegment P (geoMarkPosition hP (selectedMarkPerm S a)).1`, hence `geoCarrierSpec_of_independent (hn) (hP) (hS) : GeoCarrierSpec hP S` (via `GeoCarrierSpec.of_core`); `def geoComponentCycle`, `geoComponentCycle_eq_filter (q) : geoComponentCycle hP S q = (geoMarkCycle hP).filter (fun m => decide (geoOwner hP S m = q))`; `geo_closed_trace` (port of CarrierClosedTrace's main statement) | 1,250 | 5-6 | 0 | U0 |
| **U2a** | SM/GeoCarrierCrossings.lean, SM/GeoCarrierNoncrossing.lean | port of CarrierCrossings §1, §3, §5 (§2, §4 are FlatCarriers.lean:2889-2995), CarrierNeighborSeparation, CarrierNoncrossing → `geo_noncrossing (hn) (hP) (hS)` with the exact shape of `CarriersLemmaData.noncrossing` (CarriersLemma.lean:76-…) on `geoOwner`/`geometricVisitPosition`; `geo_neighbor_visits_separated (hn) (hP) (hS) : ∀ x ∈ CV.N hP S, ∀ v : Visit P, v.1 = x → geoOwner hP S (Sum.inr v) ≠ geoOwner hP S (Sum.inr (visitTwin v))` (state with `N hP S` via U0's re-export or with `∃ y ∈ S, GeometricInterlaces hP x y`); `geo_nonneighbor_visits_together (hn) (hP) (hS) : ∀ x ∈ CV.U hP S, ∀ v w : Visit P, v.1 = x → w.1 = x → geoOwner hP S (Sum.inr v) = geoOwner hP S (Sum.inr w)`; `mem_geoCarrierCrossings_iff`, `geoCarrierCrossings_subset_U`, `geoCarrierCrossings_disjoint (q ≠ q')`, `geoCarrierCrossingCount` | 1,100 | 6-8 | 0 | U1a, U1b |
| **U2b** | SM/GeoCornerPolygon.lean | port of CarrierCornerPolygon §3-§7 (§0-2 are FlatCarriers.lean:2996-3143) and CarrierActualCornerBlock → `geoCornerPolygon_edge_smul (hn) (hP) (hS) (q) (k) : ∃ c : ℝ, 0 < c ∧ edge (geoCornerPolygon hP S q) k = c • edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1` [tier 0]; `geoCornerPolygon_trace (hn) (hP) (hS) (q) : (⋃ k, edgeSegment (geoCornerPolygon hP S q) k) = ⋃ a ∈ {a | geoOwner hP S a = q}, geoSmoothingSegment hP S a '' Set.Icc 0 1` [tier 0]; `geoCornerPolygon_regular (hn) (hG : CarrierGeometry P) (hS) (q) : Regular (geoCornerPolygon hG.cg S q)` [tier 1, via U0's fold-back lemma]; `three_le_geoCornerCount (hn) (hW : WeakGeneric P) (hS) (q) : 3 ≤ geoCornerCount (weak_crossingGeometry hW) S q` [tier 2 as in the source; try tier 1 first]; `geoCornerPolygon_turn_ne_zero (hn) (hW) (hS) (q) (k)` [tier 2]; `geoCornerPolygon_turn_vertex (hn) (hP) (hS) (q) (k) (i) (h : geoCornerMark hP S q k = Sum.inl i) : turn (geoCornerPolygon hP S q) k = turn P i` [tier 0 given the edge lemma]; `geoCornerPolygon_turn_visit (…) (v) (hv : v.1 ∈ S) (h : geoCornerMark … k = Sum.inr v) : turn … k = crossingSign P v.2.val (visitTwin v).2.val` and `_turn_visit_twin` (one left one right) [tier 0] | 750 | 6-7 | 0/1/2 | U1b |
| **U2c** | SM/GeoCarrierSelfIntersections.lean | CarrierSelfIntersections §0-§5 from A's prototype re-bound to R1 (`CornerGeometry` → `WeakGeneric`/`CarrierGeometry` as R4 says) + port of §5-§9 → `geo_self_intersections (hn) (hG : CarrierGeometry P) (hS) (q)` with the exact shape of `CarriersLemmaData.self_intersections` (CarriersLemma.lean:50-70: self-intersections of the carrier = crossing points of `geoCarrierCrossings`, transverse, not at corners, no triple point) | 500 | 4-5 | 1 | U2a, U2b |
| **U3** | SM/GeoCarriersLemma.lean | the row-level mirrors on the geo lane: `structure GeoCarriersLemmaData (hn) (hG : CarrierGeometry P) (S) (hS : GeoIndependent hG.cg S) : Prop` with the fields of `CarriersLemmaData` (CarriersLemma.lean:38-124) restated on `geo*` (turn ≠ 0 field under an extra `hW : WeakGeneric P` or in a separate `GeoCornerTurnsData hW`), `theorem geo_carriers_lemma : GeoCarriersLemmaData …`; `GeoSmoothingData` mirror of `SmoothingDefinition.lean:39-150`; `def geoCarrierUniform (hP) (S) (q) : Prop := ∃ τ : SignType, τ ≠ 0 ∧ ∀ k, turn (geoCornerPolygon hP S q) k = τ`, `geoCarrierMixed`, `geoUniformSupport`, `geoCarrierRotation := rotationNumber (geoCornerPolygon …)`, `geoCarrierRotationInt` (integer, `rotationNumber_integer` on the regular polygon), `geoCarrierSelector_ne_zero_iff_uniform`, `geoWind hP S := ∏ q, geoCarrierSelector hP S q`, `geoWind_ne_zero_iff` | 350 | 3-4 | 1/2 | U2b, U2c |
| **U4** | SM/GeoPositiveLift.lean | re-binding of SM/LinkPositiveLift.lean:202-840 → `abbrev geoCarrierPolyComp (hn) (hG : CarrierGeometry P) (hS) (q) : PolyComp := ⟨geoCornerCount hG.cg S q, three_le_geoCornerCount …, geoCornerPolygon hG.cg S q⟩` (if `three_le` stays tier 2, take `hW` here and everything below), `geoCarrierShadow := Shadow.single (geoCarrierPolyComp …)`; block parametrization (LinkPositiveLift 237-520) → `geoCornerPolygon_tail_off`, `geoCornerPolygon_transverse`, `geoCornerPolygon_no_triple`; `geoCarrierShadow_generic : (geoCarrierShadow …).Generic` (via `Shadow.single_generic_of` + `geoCornerPolygon_regular`); `def geoPositiveLift (hn) (hG) (hS) (q) : Diagram := (geoCarrierShadow …).positiveDiagram (geoCarrierShadow_generic …)`; `geoPositiveLift_isPositive`, `geoPositiveLift_componentCount = 1`, `geoCarrierCrossingEquiv : (geoCarrierShadow …).Crossing ≃ geoCarrierCrossings hG.cg S q`, `geoPositiveLift_writhe : writhe = (geoCarrierCrossings hG.cg S q).card`, `eq_geoPositiveLift_of_isPositive` | 850 | 6-8 | 1 (2 fallback) | U2b, U2c |
| **U5a** | SM/GeoMarkTransport.lean, SM/GeoPathTransport.lean, CV/ChamberInvII.lean | re-binding of CChamber.lean §1 (112-560, `MarkTransport` on two `Generic` polygons → two `CrossingGeometry` polygons with `GeometricRecordsAgree hP hQ`; half exists: FlatCarriers.lean:1533-1692 `geoSmoothingSuccessor_markTransport`, `geoComponentCornerList_markTransport`, `geoCornerCount_markTransport`) → `GeoMarkTransport hP hQ hs : Prop` with `geoOwner`/`geoComponentCornerList`/`geoCornerCount`/`geoCornerTurn`/`geoCarrierCrossings` transported and `CV.Ind`/`CV.U`/pieces transported (`geometricInterlacementTransportIso`); CChamber §2 PathTransport (861-1216) re-bound to a continuous family in the CV locus: corner polygons form a continuous regular family (`geoCornerPolygon` continuous in P under constant record), `rotationNumber` constant (`rotation_number` clause 3), positive lifts related by a generic deformation ⇒ `homfly` equal (the accepted `CV.gausscode_polynomial` / planar-isotopy invariance as CChamber used), piece polynomials equal; CV persistence: `CV.Generic.eventually_generic` (ChamberInv.lean:128) + `geometric_records_persist` (GeometricRecords.lean) ⇒ `CV.X1_locally_constant (hn) (hG : CV.Generic P) : ∀ᶠ Q in 𝓝 P, ∀ hQ : CV.Generic Q, X1 hn Q hQ = X1 hn P hG`; then `theorem CV.chamberinv_ii (hn) (P Q) (hP : Generic P) (hQ : Generic Q) (h : Q ∈ CV.chamber P) : X1 hn P hP = X1 hn Q hQ` (compactness of the path from `chamber_joinedIn`, ChamberInv.lean:158) and the row bundle `CV.chamberinv` = (i) (accepted `chamberinv_i`) ∧ (ii) | 1,300 | 8-10 | 0/2 | U3, U4, CV rows 138/139/142/143/146 statements |
| **U5b** | CV/Silence.lean | `CV.silent_center_weakGeneric (hn) (E : Event n) (hE : E.Silent) : WeakGeneric E.center` (CV analogue of SM/SilentCenter.lean:40-46: G1 members off Z ⇒ turns ≠ 0; G2 members off Z ⇒ vertices off lines; the vanishing G2 puts p_i off the segment by `Silent`; active G3/G5 off Z ⇒ `CrossingGeometry`), `CV.silent_curve_weakGeneric : ∃ δ > 0, ∀ t, |t.val| < δ → WeakGeneric (E.curve t)` (`SM.weak_open`, accepted lem:weak-open); records agree through the centre (`geometric_records_persist` at the centre + `guardconst`); rotation of each `geoCornerPolygon` constant through t = 0 along the regular family (U5a's continuity lemmas on `WeakGeneric`); piece polynomials constant (U5a's record-iso transport); hence `theorem CV.silence (hn) (E) (hE : E.Silent) : ∃ δ > 0, ∀ tp tm : E.Parameter, 0 < tp.val → tm.val < 0 → tp.val < δ → -δ < tm.val → X1 hn (E.curve tp) _ = X1 hn (E.curve tm) _` and, with chamberinv(ii), the all-sides form | 800 | 6 | 2 | U5a |
| **U6** | SM/GeoCarrierAgreement.lean, Bridge/B4.lean | agreement on SM-generic P (hn, hP : Generic P, S, hS : S ∈ independentSupports hn hP; write `hc := generic_crossingGeometry hn hP`, `e := geoComponentEquivGeneric hn hP S`): `geoIndependent_iff_mem_independentSupports`, `geoCornerCount_eq_generic (q) : geoCornerCount hc S q = ccpCornerCount hn hP S (e q)`, `geoCornerPolygon_eq_generic (q) : geoCornerPolygon hc S q = recastTuple (geoCornerCount_eq_generic q) (ccpCornerPolygon hn hP S (e q))` (via `geoComponentCornerList_eq_generic` + `geoMarkPosition_eq_generic` + `polyOfList`/`subst` as FlatCarriers.lean:3366-3400, or `markPolygon_rotate_apply`), `geoCarrierCrossings_eq_generic`, `geoCarrierSelector_eq_carrierWeight (q) : geoCarrierSelector hc S q = SM.carrierWeight hn hP S hS (e q)` (via `forall_turn_recastTuple`), `CV.wind_eq_generic : CV.wind hc S = SM.wind hn hP S hS`, `geoCarrierRotation_eq_generic` (`rotationNumber_recastTuple`), `CV.carrierR_eq : CV.carrierR … q = (carrierRotationInt hn hP S hS (e q)).natAbs`, `geoPositiveLift_eq_generic : geoPositiveLift … q = positiveLift hn hP S (e q) hS` (shadows equal via `polyComp_recastTuple`, then `eq_positiveLift_of_isPositive`), `CV.groupedWrithe_eq_carrierCrossingCount` (lem:carriers(iv) + lem:piececurve Step 2: the labels of the pieces on q are `geoCarrierCrossings q`), `CV.groupedPoly_eq_homfly_positiveLift` (= cb:products, row 102, pending — U6 states it as a hypothesis-shaped lemma `of_cb_products` until row 102 lands), `CV.Omega1_eq_cornerCoefficient`; then `Bridge.B4Data.pointwise` via `cornerStateSum_eq_sum_independentSupports` (CornerStateSum.lean:174), `Ind_eq_generic` (CV/Events.lean:204), the accepted `SM.C_X1` and `Finset.sum_congr`/`prod_equiv e`; `sides` via `SM.prop_C_chamber` + `CV.chamberinv_ii`; `theorem Bridge.B4 : B4Data` | 700 | 6-8 | — | U3, U4, CV row 146; `sides` also U5a; final closure needs cb:products |
| **U7a** (rows now) | CV/Carriers.lean, CV/Wind.lean, CV/Pieces.lean | statements + provable bundles today, on the accepted geo layer: **135** `CV.smoothing_definition : SmoothingDefinitionData` (binder `hD : Diagrammatic P`, `S ∈ Ind hD.crossingGeometry`; fields: carriers := `GeoComponent`, reconnection at the two visits of a selected crossing (`GeoCarrierSpec.reconnect_selected`), unselected visits/vertices keep their successor (`keep_unselected`, `keep_vertex`), carriers are the cycles of `geoSmoothingSuccessor` (`carriers`), disjoint union of closed curves traced by inherited straight pieces (`traced_curve`, `traced_marks`, `straight_pieces`) — all from `GeoCarrierSpec.of_core`'s core fields, which need no `TracedSuccessor`); **139** `CV.pieces_definition` (prototype `residualGraph`, `Piece`, `pieceLabels`, `pieceWrithe`, `piecesOn`; clauses: `mem_U`, pieces partition `U`, nonempty, disjoint); **138** `CV.wind_definition : WindDefinitionData` on `hG : CV.Generic P` (prototype `weight`, `wind`, `CarrierUniform`; clauses `weight ≠ 0 ↔ uniform`, `wind ≠ 0 → ∀ q uniform` [now], `∀ q k, turn ≠ 0`, vertex-corner turn = `turn P i`, smoothing-corner turns = `crossingSign`/its negative [after U2b]) | 450 | 4 | — | U0 (U2b for 138's last three fields) |
| **U7b** (rows after U1/U2a) | CV/Carriers.lean | **136** `CV.carriers (hn) (P) (hD : Diagrammatic P) (S) (hS : S ∈ Ind hD.crossingGeometry) : CarriersData` with (i) `Fintype.card (GeoComponent hD.crossingGeometry S) = S.card + 1` [U1a], (ii) noncrossing for visits with `u_k.1 ∉ S` [U2a, restricted], (iii) `∀ c ∈ U _ S, ∀ v w, v.1 = c → w.1 = c → geoOwner … (inr v) = geoOwner … (inr w)` [U2a], (iv) `∀ H : Piece _ S, ∃! q, ∀ c ∈ pieceLabels _ S H, ∀ v, v.1 = c → geoOwner _ S (inr v) = q` (Gap G3, ~120 lines: `SimpleGraph.ConnectedComponent.ind` + `geometric_alternating_visits_iff_unique` + (ii)/(iii)); `CV.pieceOwner H : GeoComponent …`, `piecesOn_eq`; **137** `CV.carrierword (hn) (P) (hD) (S) (hS) : GeoInheritsMarkOrder … ∧ (∀ q, geoComponentCycle … q = (geoMarkCycle _).filter …) ∧ (∀ S' (hS' : S' ∈ Ind _), S ⊆ S' → ∀ q', ∃ q, ∀ m, geoOwner _ S' m = q' → geoOwner _ S m = q)` [U1b, U1a]; **164** `CV.selector_A (hn) (P) (hG : CV.Generic P) (S) (hS : S ∈ Ind hG.crossingGeometry) (q) : 3 ≤ geoCornerCount hG.crossingGeometry S q` [U2b] | 400 | 4-5 | — | U1a, U1b, U2a, U2b |
| **U7c** (rows after U4) | CV/PieceCurve.lean, CV/X1.lean | **143** `CV.piececurve (hn) (P) (hD : Diagrammatic P) (S) (hS) (H : Piece _ S) : ∃ (K : Finset (Crossing P)) (hK : S ∪ K ∈ Ind _) (q : GeoComponent _ (S ∪ K)), Disjoint K (pieceLabels _ S H) ∧ K ⊆ U _ S ∧ geoCarrierCrossings _ (S ∪ K) q = pieceLabels _ S H ∧ (∀ c ∈ pieceLabels _ S H, ∀ v, v.1 = c → geoOwner _ (S ∪ K) (inr v) = q) ∧ GeoInheritsMarkOrder _ (S ∪ K)` (Gap G4: well-founded recursion on `(geoCarrierCrossings _ (S ∪ K) q \ pieceLabels H).card` with invariants (a) `S ∪ K` independent, (b) H owned by one carrier, (c) retained crossings ⊆ labels on the carrier; Steps 1-4 from U2a/U2c/U1b/graph theory); `CV.pieceSupport`, `CV.pieceCarrier` (Classical.choose), `CV.pieceCurve := geoCornerPolygon _ (S ∪ K_H) q_H`; **142** `CV.piecediagram_definition (hn) (P) (hD) (S) (hS) (H) : (∀ x, (pieceDiagram H).IsPositive x) ∧ (pieceDiagram H).writhe = (pieceLabels _ S H).card ∧ Nonempty ((pieceDiagram H).Γ.Crossing ≃ pieceLabels _ S H) ∧ (pieceDiagram H).componentCount = 1`, `CV.P_H := homfly (pieceDiagram H)`; **146** `CV.X1` as in the prototype with `pieceSupport`/`pieceCarrier` from 143 and `three_le_geoCornerCount`/`geoCornerPolygon_regular`/`geoCarrierShadow_generic` from U2b/U4; `CV.X1_definition : X1DefinitionData` (already proved in the prototype); also `CV.groupedWrithe_eq_card_geoCarrierCrossings` | 900 | 8-10 | 1 | U2a, U2b, U2c, U4, U7b |
| **U8** (R-lane support) | CV/TripleEvents.lean | the six Triple* lemmas of SM/TripleAdjacency.lean, SM/TripleSides.lean (928 lines, `SM.Generic` only through `generic_edgeParameters_ne`) restated on `E : CV.Event n` with `CV.Generic.crossParam_ne` (CV/Setup.lean:1130), `crossParam_eq_edgeParameter` (:572); `VisitsAdjacent → AdjacentVisits` (empty-arc) bridge for `RProof.localization` (2b) | 700 | 5 | — | U0 (independent of the port; can start now) |
| **U9** (assembler/executor) | — | merge U0-U8 drafts, port into work/lean (header only), `lake build` of the new modules through the checker, review briefs with §4 notes, acceptance of rows in the order of §6 | — | 10-12 | — | all |

Totals: ≈ 12,500 new lines (U0-U6 ≈ 8,800 of which ≈ 2,600 pure renaming; rows U7 ≈ 1,750; U8 700; U5a/b
2,100), ≈ 95 prover agent-hours (range 75-125), ≈ 12 executor hours. Parallelism: U0 first (one prover, half a
day); then U1a ∥ U1b ∥ U8 ∥ U7a; U2a ∥ U2b after U1; U2c after both; U3 ∥ U4 ∥ U7b after U2; U6 ∥ U7c after U4;
U5a after U7c's statements; U5b after U5a. Critical path U0 → U1b → U2b → U2c → U4 → U7c → U6 ≈ 30-35 serial
prover-hours ≈ 2-3 days wall-clock with 5-6 provers + assembler in the flat-carriers/cchamber PLAN_FINAL pattern.
This is shorter than, and runs beside, the phase-2 move instances (G10/G11), cb:products (row 102) and the twelve
R obligations that Bridge:B4 / R:cv_theorem wait for under every option; CV-DOM adds no critical-path time if
launched now.

## 6. Order of rows to unblock

1. **Now (U0 + U7a, no port needed):** 135 CV:def:smoothing, 139 CV:def:pieces (statable and provable on the
   accepted geo layer today); 138 CV:def:wind statement + the two clauses that need no tier-2 fact. Also 164
   CV:selector_A statement (proof waits for U2b) and 146 CV:def:X1 statement module (proof-complete once 142/143
   exist; the prototype is the draft).
2. **After U1a/U1b (day 1):** 137 CV:lem:carrierword; 136 CV:lem:carriers (i); with U2a: 136 (ii)-(iv).
3. **After U2b (day 1-2):** 138 CV:def:wind complete; 164 CV:selector_A. R rows that consume only these:
   R:generic_selector (172: def:wind + selector_A), R:generic_table words (171: carrierword) — their statements
   are already fixed in work/drafts/rlane on CV events.
4. **After U2c + U4 (day 2):** 143 CV:lem:piececurve (G4), 142 CV:def:piecediagram, then 146 CV:def:X1 as a
   row. R:fibre_partition (169) gets its X1 specialisation; R:exterior (168) gets carrierword + the piece
   polynomials (still waits for CV:cor:groupedknot = cb:products).
5. **After U6 (day 2-3):** Bridge:B4 `pointwise` (needs cb:products, row 102, for `Ω₁ = cornerCoefficient`; until
   then the B4 draft carries it as the one open lemma); B4 `sides` after U5a.
6. **After U5a (day 3):** 147 CV:prop:chamberinv (ii) [(i) is accepted]; `CV.hyp_R` in its printed form (R6);
   `RProof.cv_R` = `cv_R_near` + chamberinv(ii) once the twelve R obligations exist.
7. **After U5b:** 151 CV:lem:silence (its own proof; no detour through SM prop:C-silent). SM prop:C-silent (row
   107) can then reuse U5a/U5b's WeakGeneric-centre transport (the same lane the design report flagged for
   lem:weak-carriers).
8. **R lane throughout:** the X1-free rows (166 localization, 167 parity, 169 abstract partition, 171 sign
   classification) proceed now on CV events with U8; the carrier-dependent ones (168, 170, 172-178) after steps
   3-4 and their phase-2 dependencies (G10/G11 moves, cb:products, homflyrows, carrierfloor) — none of which is
   a CV-DOM item.
9. **Bridge:theorem** `Bridge.sm_R` last: B1-B3 (accepted) + `RProof.cv_R` + `Bridge.B4.pointwise` +
   `SM.prop_C_chamber` (accepted).

## 7. Risks and mitigations

1. **Name drift against the frozen geo layer.** A second, divergent `geoCornerPolygon`/`geoOwner` would break
   the B4 agreement chain and could shadow accepted names. Mitigation: port_lane.py's GEO check (drop
   declarations whose `geo*` name exists in FlatCarriersDefs/FlatCarriers); the assembler greps every new
   declaration name against `work/lean/SM/FlatCarriers*.lean` before porting; new modules import
   `SM.FlatCarriersDefs` (and `SM.FlatCarriers` only where a lemma is needed) — never copy a definition.
2. **The one non-`rfl` agreement point (U6).** `geoCornerPolygon : LabelledTuple (geoCornerCount …)` and
   `ccpCornerPolygon : LabelledTuple (ccpCornerCount …)` have propositionally equal counts
   (`geoMarkList_eq_generic` is a `Perm.eq_of_pairwise` argument). Mitigation: two working patterns exist —
   `recastTuple` + `rotationNumber/regular/turn/forall_turn/polyComp_recastTuple` (CChamber.lean:76-110) and
   `polyOfList` + `subst` along `geoComponentCornerList_eq_generic` (FlatCarriers.lean:3366-3400). B4 needs only
   turn lists, counts, rotation numbers, selectors and `homfly` values, all of which those lemmas transport.
3. **Tier-1 corner-polygon geometry (R4).** The judge's argument that `Regular`/tail-off/transverse/no-triple
   hold at `CarrierGeometry` (fold-back excluded by `vertex_off` for n ≥ 3) is a proof sketch, not a compiled
   lemma. Mitigation: U0 proves `adjacent_edges_meet` first (half a day); if U2b/U4 hit a genuine tier-2 need,
   the fallback is `hW : WeakGeneric P` for that group, which keeps def:X1/def:wind/selector_A on their printed
   `CV.Generic` binder and narrows ONLY def:piecediagram/lem:piececurve from "diagrammatic" to "generic" — a
   small, reviewable scope change (all consumers of those two rows are on generic P), to be recorded then, not
   pre-emptively.
4. **`hn : 3 ≤ n` and instance plumbing in the long proofs.** CarrierNoncrossing (476 lines) and
   CarrierInheritedOrder (230) are the longest `SimpleGraph`/`Cycle` proofs, with `letI := markLinearOrder hn hP`
   (4 files use `markLinearOrder`/`gaussList`); `geoMarkLinearOrder`/`geometricGaussList` have the same shape
   and `_eq_generic` bridges. Each such site is a manual fix; budgeted in the 75-125 h range (upper end if they
   resist). Reviewers must check no CV row statement silently gained `hn`.
5. **chamberinv(ii) on CV chambers (U5a) is new mathematics for the library**, not a port: local constancy must
   hold at every CV-generic point, including SM pure-cut walls. Ingredients exist (`Generic.eventually_generic`,
   `geometric_records_persist`, rotation continuity, CChamber's path argument, the accepted
   `CV.gausscode_polynomial`). Medium risk; it is on the path of `CV.hyp_R` in its printed form (R6) and of B4
   `sides`, but NOT of `Bridge.sm_R`'s mathematical content (which needs only `cv_R_near` + B4 `pointwise`). If
   U5a slips, `RProof.cv_R_near` and B4 `pointwise` can be accepted as intermediate theorems while the rows wait.
6. **B4 waits for cb:products (row 102) under every option.** `Ω₁(S,L) = cornerCoefficient` needs
   `∏_H P_H = homfly (positiveLift L)` (cor:groupedknot(B) = cb:products). Not a CV-DOM cost; U6 isolates it as
   one lemma.
7. **Estimate confidence.** Calibrated on the two prototypes (367 lines at the second compile; 220 lines at the
   first). Untested: the long combinatorial proofs (risk 4), the block-parametrization port in U4 (350 lines of
   coordinate bookkeeping), G4 (new recursion). Total 75-125 agent-hours; (C)-specific 45-70.
8. **Schedule interaction.** Do not schedule CV-DOM ahead of the R lane's own blockers; run it beside them. The
   R-lane statements stay parametric in `E : CV.Event n` (as drafted) so nothing there changes when the carrier
   rows land. If the executor ever needs the emergency fallback (B) for a *statement* freeze, every affected row
   must carry the (B) note of ANALYSIS_B.md §2 and OPEN_WORK item 4 / decision F2 must be explicitly overturned
   in AUTHOR_NOTES — the judge does not recommend it.
9. **Option (D) if anyone pursues it despite this decision:** needs a density lemma (SM-generic dense in the CV
   locus) with no ready Mathlib lemma, and yields definitions that are not CV's; a `definition_equivalence`
   review would likely reject. Use transport only as a proof tool where a lemma already exists.

## 8. Where the two analyses differed and how the judge ruled

| point | Analyst A | Analyst B | ruling |
|---|---|---|---|
| tier predicates | new `SM.CarrierGeometry` (tier 1) and `SM.CornerGeometry` (tier 2, ↔ WeakGeneric) | accepted `CrossingGeometry` / `WeakGeneric` directly | `CarrierGeometry` kept (it names CV "diagrammatic" on the SM side, CV-free); `CornerGeometry` dropped for `WeakGeneric` (R1) |
| tier of piecediagram/piececurve | tier 1 "with the extra lemma" | prototype on `CV.Generic` | tier 1 = printed `Diagrammatic` (R4), with the documented fallback of risk 3 |
| `CV.hyp_R` | not addressed | punctured-δ point-value form + review note | printed all-sides form; δ-form is the R lane's intermediate `cv_R_near` (R6) |
| line count | ≈ 6,500 (lane only) + 1,500-2,000 rows | ≈ 12,000 (everything) | ≈ 12,500 everything; A undercounted the AffineSegments/SegmentGeometry/ClosedTrace/Marks/Successor residue (≈ 500 lines) now in U1b |
| hours | ≈ 60 (lane) + 20-30 (rows) | ≈ 60 + 6 | ≈ 95 total (75-125), (C)-specific 45-70 |
| B4 shape | `X1 = cornerStateSum` | same + notes on part 5 | bundle with `pointwise` (17) and `sides` (18) (R7) |

Both analysts independently recommended (C); the judge concurs, with the rulings above. Emergency fallback (B) is
recorded only as such.
