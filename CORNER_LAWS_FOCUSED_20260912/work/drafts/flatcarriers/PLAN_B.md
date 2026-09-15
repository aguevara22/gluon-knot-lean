# PLAN_B — def:flat-carriers and cor:flat-carriers (statement design, tag B)

Written 2026-09-13 by the statement-architect subagent (tag B). Frame SM15.
Statement file: `work/drafts/flatcarriers/Statement_B.lean` (1160 lines; typechecks with
`cd work/lean && lake env lean ../drafts/flatcarriers/Statement_B.lean`, output = exactly the two
`declaration uses 'sorry'` warnings for `SM.flat_carriers_definition` and `SM.flat_carriers`; every
other declaration is sorry-free with axioms `propext, Classical.choice, Quot.sound`).

Source rows: def:flat-carriers = `reference/SM/sm-3-statesum.tex:788-803` (bridge sentence
805-809, proof 838-913), cor:flat-carriers = `sm-3-statesum.tex:805-835`. Both "under the
hypotheses of Lemma lem:flat-sides" = `sm-1-polygons.tex:778-826`, accepted as
`SM.flat_sides : … → FlatSidesData hn g j hz hb hc` (`work/lean/SM/FlatSides.lean:17,47`).

## 0. The one-paragraph design

Emphasis B: define the carriers *intrinsically* in every configuration. The accepted carrier
machinery (`SM.Carrier.*`) is parametrized by `hP : Generic P`, but a grep of how `hP` is used shows
it needs genericity only for two facts: every crossing parameter is strictly interior
(`crossingParameter_interior`, for `visitPosition`) and visit positions are injective
(`visitPosition_injective`, for the sorted mark list). Both hold on the accepted geometric record
domain `CrossingGeometry P` (`CrossingGeometry.lean:52 crossingParameter_interior_of_geometry`,
`GeometricVisits.lean:22 geometricVisitPosition_injective`), which lem:flat-sides (ii) proves at the
nongeneric centre (`FlatCrossingGeometry.lean:12 flat_crossingGeometry`). So the statement file
restates the marked traversal circle / successor `ρ` / reconnection `ρ_S = ρ ∘ selectedMarkPerm S`
/ cycles / traced polygon / corner polygon word for word on `CrossingGeometry P` (namespace
`SM.GeoCarrier`, prefix `geo`), reusing unchanged the parts that never needed genericity
(`Mark`, `selectedMarkPerm`, `visitTwin`, `IsTrueCorner`). The centre `P(0)`, the deletion
`P(0)∖j` and the two sides `P(t)` are then four instances of ONE definition, exactly as the printed
sentence "in each of these four configurations … the same words define them, no genericity being
assumed" demands. Only afterwards are the four related, through the accepted record bijections
(`visitTransport`/`crossingTransport` for the sides, `fusionVisitEquiv`/`fusionCrossingEquiv` for
the deletion), extended to marks.

On a generic `P` the geo machinery is PROVED (in the statement file, sorry-free) to coincide with
the accepted one: `geoMarkPosition_eq_generic`, `geoMarkList_eq_generic`,
`geoMarkSuccessor_eq_generic`, `geoSmoothingSuccessor_eq_generic`, and the concrete equivalence
`geoComponentEquivGeneric : GeoComponent (generic_crossingGeometry hn hP) S ≃ Component hn hP S`
with `geoComponentEquivGeneric (geoOwner a) = owner a` (rfl), `geoComponentMarkList_eq_generic`,
`geoComponentPlaneCycle_eq_generic`, `geoComponentCornerList_eq_generic`. This is what makes the
printed "On the two generic sides they are the carriers of Definition def:smoothing" a theorem
about literally the same objects rather than a re-definition, and it lets every consumer
(sm-4 `lc:presentations`, `lp:core`, which speak of `ccpCornerPolygon`, `carrierRotation`,
`carrierCrossings`) reach the side carriers of this row through `geoComponentEquivGeneric`.

## 1. Definitions (all in `Statement_B.lean`; `n ≥ 3`, parent size `n+1`, as in FlatSides)

### 1.1 Intrinsic carriers on `CrossingGeometry P` (namespace `SM.GeoCarrier`, section 1-3)

| Lean | meaning (printed words) | mirrors (accepted) |
|---|---|---|
| `geoMarkPosition hP : Mark P → TraversalPoint n` | "mark the traversal circle at every original vertex and every crossing visit": vertex `i ↦ (i,0)`, visit `v ↦ geometricVisitPosition hP v` | `CarrierMarks.lean:37 markPosition` (G1 → CrossingGeometry) |
| `geoMarkPosition_injective` (proved) | distinct marks have distinct positions | `CarrierMarks.lean markPosition_injective` (Generic) |
| `geoMarkKey`, `geoMarkLinearOrder`, `geoMarkList`, `geoMarkCycle` | all marks sorted by traversal coordinate; the marked circle | `CarrierMarks.lean:79,99`, `CarrierSuccessor.lean:34` |
| `geoNextMark`, `geoPrevMark`, `geoMarkSuccessor : Perm (Mark P)` = `ρ` | the outgoing successor of every mark | `CarrierSuccessor.lean:49,77` |
| `geoMarkSuccessor_sameCycle` (proved) | before reconnection the circle is one cycle | `markSuccessor_sameCycle` |
| `geoSmoothingSuccessor hP S = (selectedMarkPerm S).trans (geoMarkSuccessor hP)` = `ρ_S` | "exchange the two outgoing successors at the two visits of every selected crossing" (def:smoothing + conv:selected-visits); SAME `selectedMarkPerm` (`CarrierSmoothing.lean:36`) | `CarrierSmoothing.lean:82 smoothingSuccessor` |
| `GeoComponent hP S := Quotient (SameCycle.setoid ρ_S)`, `geoOwner` | "the resulting oriented closed cycles" = the carriers; incoming-visit ownership | `CarrierSmoothing.lean:124,130` |
| `geoComponentMarkList hP S q` | the marks of a carrier in inherited cyclic order | `CarrierClosedTrace.lean:59` |
| `geoComponentPlaneCycle hP S q : Cycle Plane` | "trace the resulting oriented closed cycles": the oriented closed polygonal cycle of plane points | `CarrierClosedTrace.lean:66` |
| `geoSmoothingSegment hP S a u` | "the inherited straight subsegments" (mark → `ρ_S`-successor) | `CarrierAffineSegments.lean:69` |
| `geoSmoothingSuccessor_bijOn_owner`, `geoComponent_has_trueCorner` (proved) | every carrier has a corner (vertex or selected visit) | `CarrierTrueCorners.lean component_has_trueCorner` (port, via the generic-α lemma `CarrierAmbientTransport.lean:54 sameCycle_congr_of_eqOn_bijOn`) |
| `geoComponentCornerList`, `geoCornerCount` (+ `NeZero` instance, proved), `geoCornerMark`, `geoCornerPolygon hP S q : LabelledTuple (geoCornerCount ..)` | the carrier read at its corners in inherited order: its turns, rotation number and selector are those of this labelled tuple | `CarrierCornerPolygon.lean:317,341,350,357` |
| `geoCornerIndex`, `geoCornerTurn hP S a : SignType` | the turn of a carrier at its corner mark `a` (`+1` left, `-1` right) | new helper (indexes `ccpCornerMark⁻¹`) |
| `geoCarrierCrossings hP S q` | the retained crossings of a carrier (def:smoothing: unselected, both visits owned) | `CarrierCrossings.lean:56` |
| `GeoIndependent hP S` | `S` independent in the interlacement graph read on the record domain | `InterlaceSupports.lean:27 independentSupports` via `GeometricInterlacement.lean:16 GeometricInterlaces` |
| `SM.carrierSelector Q : ℤ` | cor (iii): `1` if all turns `= -1` (right), `(-1)^k` if all turns `= 1` (left, `k` = corner count), else `0` | new |

Rationale for `geoCornerTurn` via `List.idxOf`: the printed clauses (ii) compare "corresponding
corners", i.e. corners named by marks; the turn of the corner polygon at the position of a mark
is the natural reading, and it avoids existential quantification over indices. The junk value
at non-corner marks is never used (every clause restricts to `IsTrueCorner S a`).

### 1.2 The four configurations and their identifications (section 4)

| Lean | meaning |
|---|---|
| `flatCentreCG hn g j hz hb hc : CrossingGeometry g.center` | `C = P(0)` (`flat_crossingGeometry`) |
| `flatDeletionCG hn g j hz hb hc : CrossingGeometry (deleteVertex g.center j)` | `D = P(0)∖j` (`generic_crossingGeometry ∘ generic_deleteVertex`) |
| `flatSideCG hn g b t : CrossingGeometry (g.sideTuple b t).val` | `T = P(±t)`, `b : Bool` (`true` = `t>0`) |
| `IsRightSide g j b t := turn (side) j = -1`, `IsLeftSide := … = 1` | def:walls (F), sm-1:743-744 |
| `markTransport hs : Mark P ≃ Mark Q` (vertices fixed, `visitTransport hs` on visits) | the identification of marks of the centre with a side, `hs : ∀ s, IsCrossing C s ↔ IsCrossing T s` |
| `transportSupport hs S := S.map (crossingTransport hs)` | `S` read on a side |
| `deletionSupport hn g j hz hb hc S := S.map (fusionCrossingEquiv ..)` | `S` read on the deletion (fused-edge bijection, lem:flat-sides (iii)) |
| `fusionMark : Mark D → Mark C` (vertex `i ↦ deletionIndex j i`, visit `w ↦ fusionVisitEquiv⁻¹ w`); `delMark : Mark C → Mark D` (vertex `k ↦ fusionIndex j k`, visit `v ↦ fusionVisitEquiv v`) | marks of the deletion read at the centre and back; proved: `delMark_fusionMark`, `fusionMark_delMark (a ≠ inl j)`, `fusionMark_ne_deleted` |
| `centralCarrierThroughJ := geoOwner C S (Sum.inl j)` | "exactly one contains μ_j" |
| `deletionCopyThroughJ := geoOwner D S_D (delMark (ρ_S^C (Sum.inl j)))` | its deletion copy (the deletion carrier of the mark after μ_j on the central carrier) |

Why `b : Bool` and not "right/left" as the index: `FlatSidesData` (`FlatSides.lean:26-27`) only
says `turn (sideTuple true t) j * turn (sideTuple false t) j < 0`; which Bool is the right side
depends on the germ. Clauses that mention right/left are therefore quantified over both sides
and use `IsRightSide`/`IsLeftSide` (in (iii) over the pair `bR bL` with those properties, which
exists and is unique by the sign change).

Why `∀ hs` and not a fixed identification: `hs` is a Prop, so `visitTransport hs` is
proof-irrelevant; the identification exists on the radius by `GeometricRecordsAgree`
(`side_records` / `identify_sides` fields), and quantifying over it avoids extracting a witness
from an existential inside a `Prop` structure.

Why a `δ` parameter: `structure … : Prop` cannot carry data, and the side clauses hold only
"after shrinking the interval". Both structures take `δ : ℝ` with fields `radius_pos`,
`radius_le`; the theorems assert `∃ δ, …`, exactly like `FlatSidesData`'s inner `∃ δ`.

Indexing of "corresponding carriers": the carriers of corresponding marks. Side copy of the
centre carrier of `a` = `geoOwner T S_T (markTransport hs a)`; centre copy of the deletion carrier
of `b : Mark D` = `geoOwner C S (fusionMark b)`. Every centre carrier is reached from a deletion
mark (the μ_j carrier contains `ρ_S(inl j) ≠ inl j`), so quantifying over marks quantifies over all
corresponding pairs; the induced bijections of carriers are the content of the (i) fields
`correspond_sides` / `correspond_deletion` (owner-iff + successor conjugation), not an
existential.

### 1.3 `GeoCarrierSpec hP S : Prop` (section 5)

The printed sentence 2 of def:flat-carriers, read in one configuration: marks (vertex at
`(i,0)` with point `P i`; visit at its interior parameter with point `crossingPoint`), injectivity,
`ρ` is the traversal successor (no mark strictly between a mark and `ρ a`), the reconnection
(`ρ_S = ρ ∘ selectedMarkPerm S`; `ρ_S a = ρ b`, `ρ_S b = ρ a` at a selected pair; unselected
visits/vertices unchanged), carriers = cycles, traced curve = plane cycle of the mark list, the
mark list is nodup/nonempty/exact and consecutive entries are `ρ_S`-successors, the inherited
straight subsegments lie on the original edge of the outgoing slot, corners = vertices and
selected visits. It mirrors `SmoothingDefinition.lean:39 SmoothingData` (accepted def:smoothing).

## 2. Clause-by-clause: printed text → Lean field

### 2.1 def:flat-carriers → `FlatCarriersDefinitionData hn g j hz hb hc S δ`

| printed (sm-3:789-803) | field |
|---|---|
| "Under the hypotheses of Lemma lem:flat-sides" | theorem hypotheses `hn g hz hb hc hsc` (= `flat_sides`'s), `radius_pos`, `radius_le` |
| "identify the crossing visits of the two sides, of the centre P(0) … through the common cyclic Gauss word of that lemma's clauses (ii)" | `identify_sides : ∀ b t<δ, GeometricRecordsAgree C T` (Gauss list/word, interlacement, signs under `visitTransport hs`); `identify_sides_marks : (geoMarkList C).map (markTransport hs) = geoMarkList T` |
| "… and of the deletion P(0)∖j through … clause (iii)" | `identify_deletion : FlatFusionData hn hz hb hc` (accepted, `FlatFusionData.lean:12`); `identify_deletion_marks : (((geoMarkList C).erase (inl j)).map delMark : Cycle) = (geoMarkList D : Cycle)` |
| "fix an independent set S in their common interlacement graph" | `common_independence`: `GeoIndependent C S ↔ IsDecomposition T (transportSupport hs S)` and `↔ IsDecomposition D (deletionSupport S)`; theorem hypothesis `hS : GeoIndependent C S` |
| "In each of these four configurations mark …, exchange …, trace …" | `centre_carriers : GeoCarrierSpec C S`, `deletion_carriers : GeoCarrierSpec D S_D`, `side_carriers : ∀ b t<δ hs, GeoCarrierSpec T S_T` (each under `GeoIndependent C S`) |
| "These oriented closed polygonal cycles are the carriers of S in that configuration." | `carriers_are_cycles` (centre and deletion: every carrier is the `ρ_S`-cycle of one of its marks, traced as its plane cycle) |
| "On the two generic sides they are the carriers of Definition def:smoothing;" | `sides_are_smoothing_carriers`: `geoMarkPosition = markPosition`, `geoMarkList = markList`, `geoMarkSuccessor = markSuccessor`, `geoSmoothingSuccessor = smoothingSuccessor`, `geoComponentEquivGeneric (geoOwner a) = owner a`, mark list / plane cycle / corner list agree through the equivalence, and `SmoothingData` (accepted def:smoothing) holds |
| "at the centre and on the deletion the same words define them, no genericity being assumed." | `centre_deletion_same_words`: `¬ Generic g.center`, `ρ_S^C = ρ^C ∘ selectedMarkPerm S`, carriers = cycles at the centre, and on the deletion the same words give the accepted `smoothingSuccessor`/`markList`/`owner` and `SmoothingData` |

### 2.2 cor:flat-carriers → `FlatCarriersData hn g j hz hb hc S δ`

| printed (sm-3:806-834) | field |
|---|---|
| "form the carriers of S on both sides, at the centre and on the deletion" | `radius_pos`, `radius_le`, `side_records` (the identification exists on the radius) |
| (i) "The carriers correspond under their named traversal arcs." | `correspond_sides`: `ρ_S^T (markTransport a) = markTransport (ρ_S^C a)` and `owner^C a = owner^C a' ↔ owner^T (T a) = owner^T (T a')`; `correspond_deletion`: `ρ_S^D b = delMark (ρ_S^C (fusionMark b))`, skipping `inl j` when hit (arc through μ_j fused), and `owner^D b = owner^D b' ↔ owner^C (fusionMark b) = owner^C (fusionMark b')` |
| (i) "Exactly one contains μ_j." | `unique_through_mu_j`: a centre carrier passes through the point `g.center j` iff it is `centralCarrierThroughJ`; same on each side for `μ_j(t)` with the carrier of `markTransport hs (inl j)` |
| (i) "The central copy of that carrier differs from its deletion copy only by the positive-flat subdivision at μ_j" | `central_vs_deletion_through_mu_j`: mark cycle of the central carrier minus `inl j`, read on `D`, = mark cycle of `deletionCopyThroughJ`; `StrictBetween (point before μ_j) μ_j (point after μ_j)`; both displacements positive multiples of the fused direction `edge D (-1) = μ_{j+1} - μ_{j-1}` |
| (i) "every other central carrier is unchanged by deletion." | `others_unchanged`: mark cycles agree through `fusionMark` and the traced plane cycles are equal |
| (i) "Every carrier has nonzero segments" | `nonzero_segments`: every inherited subsegment has distinct endpoints and every corner-polygon edge is nonzero, in all four configurations |
| (i) "and no antiparallel corner" | `no_antiparallel`: `Regular (geoCornerPolygon ..)` in all four |
| (i) "except for that one central zero turn, all corner turns are nonzero." | `turns_nonzero`: centre `turn = 0 ↔ corner mark = inl j`; deletion and sides all `≠ 0` |
| (ii) "Corresponding carriers have the same retained self-crossing visits, pairing," | `same_retained_crossings` (membership in `geoCarrierCrossings` transported by `crossingTransport`/`fusionCrossingEquiv`), `same_pairing` (`visitTwin` commutes with the identifications) |
| (ii) "signs and positive over/under bits." | `same_signs`: `crossingSign` read from the visited edge and `0 < det(d_e, d_f)` agree at every crossing visit, sides and deletion |
| (ii) "They have the same signed rotation and hence the same absolute rotation." | `same_rotation`: `rotationNumber` of corresponding corner polygons equal, and absolute values equal, side↔centre and deletion↔centre (so centre copy included, per round-4 broadening; sides↔deletion follows) |
| (ii) "Every corresponding corner away from μ_j has the same turn sign on both sides and in the deletion." | `same_turn_signs_away`: for corner marks `a ≠ inl j`: `geoCornerTurn T (markTransport a) = geoCornerTurn C a` and `geoCornerTurn D (delMark a) = geoCornerTurn C a` |
| (ii) "The extra corner at μ_j is right on the right side and left on the left side." | `extra_corner`: `geoCornerTurn T (inl j) = turn T j`; `IsRightSide → = -1`; `IsLeftSide → = 1` |
| (iii) selector definition | `SM.carrierSelector` |
| (iii) eq. flatpr:selector-identity `W_right − W_left = W_del` | `selector_identity` (over `bR bL` with `IsRightSide`/`IsLeftSide`, the μ_j carrier = carrier of `markTransport (inl j)`, deletion copy `deletionCopyThroughJ`) |
| (iii) "All other corresponding carrier selectors agree." | `other_selectors_agree`: each side copy's selector = the deletion copy's selector for every carrier `≠ centralCarrierThroughJ` |
| closing sentences | no field (non-definitional) |

### 2.3 STRONGER / WEAKER than printed

STRONGER (all justified by the printed proof, flagged so a referee can strike them):
- `same_turn_signs_away` and `same_rotation` include the CENTRE copy (printed (ii) names only
  the sides and the deletion for turn signs; the rotation sentence covers the centre by the
  round-4 status note; the proof's "all surviving corner signs … agree among the configurations"
  covers the centre for signs).
- `identify_sides_marks`, `identify_deletion_marks`, `correspond_*` give the correspondence as
  explicit equalities of mark lists / conjugation of successors (the printed "correspond under
  their named traversal arcs" is informal; the printed proof's first paragraph is exactly this).
- `same_signs` is stated for all crossing visits, not only retained ones (it is lem:flat-sides
  (ii)/(iii) content).
- `nonzero_segments` also states nonzero corner-polygon edges (the printed proof's "subsegments
  … have positive length" + block compression).
- `others_unchanged` also asserts equality of the traced plane cycles (immediate from
  `crossingPoint_fusion` and `deleteVertex_apply`).
- `unique_through_mu_j` is also stated on the sides.
- The def row's `sides_are_smoothing_carriers` asserts the accepted `SmoothingData` (def:smoothing
  in full) on each side — this is what "they are the carriers of def:smoothing" means, and it is
  a one-line consequence of `smoothing_data` once `IsDecomposition` is transported.

WEAKER / choices:
- The selector is defined only through the corner polygon's `turn` values; with a zero turn
  (centre) it is never evaluated (printed (iii) does not evaluate it there either).
- "Named traversal arcs" are read as `ρ_S`-steps (mark → successor); a traversal arc as a subset
  of the circle is not defined separately (the accepted library never needed it either).
- `other_selectors_agree` states side = deletion for each side (hence right = left); the centre's
  selectors are not asserted (the printed clause names the two sides and the deletion).
- `carriers_are_cycles` (sentence 3) restates part of `GeoCarrierSpec.carriers`; it is kept as a
  separate field only so that the field list is one-per-sentence.

## 3. Reuse list (accepted, `work/lean/SM/…`)

Geometry/records: `FlatSides.lean:17 FlatSidesData`, `:47 flat_sides`; `FlatFusionData.lean:12
FlatFusionData`, `:52 flat_fusion_data`; `FlatCrossingGeometry.lean:12 flat_crossingGeometry`;
`FlatLocal.lean:39 flat_germ_crossingGeometry`; `FlatCenter.lean:30 flat_center_geometry`;
`DeletionGeneric.lean:31 generic_deleteVertex`; `DeletionChamber.lean:12 flat_deletion_chamber`;
`CrossingGeometry.lean:11 CrossingGeometry`, `:24 generic_crossingGeometry`, `:52
crossingParameter_interior_of_geometry`, `:61 crossingPoint_injective_of_geometry`;
`GeometricVisits.lean:12 geometricVisitPosition`, `:22 geometricVisitPosition_injective`, `:51
geometricGaussList`, `:56 geometricGaussWord`; `GeometricRecords.lean:35 geometricGaussList_transport`,
`:55 GeometricRecordsAgree`, `:63 geometric_records_persist`; `GeometricTransport.lean:10
CrossingParameterOrderAgrees`, `:14 geometric_visitParameterOrder`; `GeometricInterlacement.lean:16
GeometricInterlaces`; `GeometricOrderStability.lean:13,47`; `GeometricCrossingStability.lean:35`;
`CrossingTransport.lean:12 crossingTransport`, `:18 visitTransport`; `Crossings.lean:80
crossingSign`; `Traversal.lean:73 traversalBetween`; `Chirotope.lean:13 turn`;
`RegularLocus.lean:12 Regular`, `:15 principalTurn`, `:51 principalTurn_eq_zero_iff`;
`StrictBetween.lean:9`; `WallGerm.lean:13 WallGerm`, `:49 sideTuple`; `GermSignChange.lean:10
SignChanges`; `GermDefinition.lean:12,14 pointZeros/concurrences`.

Fusion: `DeletedTuple.lean:13 deleteVertex`; `DeletionIndices.lean:11 deletionIndex` (+
`deletionIndex_ne_deleted`, `deletionIndex_exhaust`); `FusionIndices.lean:10 fusionIndex`,
`fusionIndex_deletionIndex`; `FusionVisits.lean:39 fusionVisitEquiv`, `:57 fusionVisit_pairing`,
`:64 visitParameter_fusion`; `FusionCrossings.lean:42 crossingPoint_fusion`, `:91
fusionCrossingEquiv`; `FusionKey.lean:121 fusionVisit_cyclic_order`; `FusionGaussWord.lean:33
geometricGaussList_fusion_rotation`, `:58 geometricGaussWord_fusion`; `FusionInterlacement.lean:24`;
`FusionSigns.lean:19 crossingSign_fusion`, `:28 positive_over_fusion`; `FusionGeometry.lean:34
edge_fusion`.

Carriers: `CarrierMarks.lean:33 Mark`, `:37 markPosition`, `:79 markKey`, `:99 markList`;
`CarrierSuccessor.lean:34 markCycle`, `:49 nextMark`, `:77 markSuccessor`, `:114
nextMark_no_mark_between`; `SortedCyclicGap.lean:10 sorted_next_no_cyclic_between`;
`CarrierVisitTwin.lean:34 visitTwin`, `:80 selectedVisitTwin`; `CarrierSmoothing.lean:36
selectedMarkPerm`, `:82 smoothingSuccessor`, `:124 Component`, `:130 owner`;
`CarrierAmbientTransport.lean:54 sameCycle_congr_of_eqOn_bijOn`; `CarrierTrueCorners.lean:44
IsTrueCorner`; `CarrierClosedTrace.lean:59 componentMarkList`, `:66 componentPlaneCycle`, `:89
componentMarkList_getElem_successor`, `:118 componentTraceEdge_data`; `CarrierAffineSegments.lean:69
smoothingSegment`; `CarrierCrossings.lean:56 carrierCrossings`, `:231 visit_incoming_direction`,
`:270 unselected_visit_outgoing_direction`, `:323 smoothing_corner_directions`, `:362
vertex_corner_directions`; `CarrierCornerPolygon.lean:317 ccpCornerList`, `:341 ccpCornerCount`,
`:357 ccpCornerPolygon`, `:822 carriers_clause_ii`; `CarrierComponentCount.lean:104,112`;
`CarrierIndependentOrder.lean:80 independent_inheritsMarkOrder`; `CarrierSelfIntersections.lean:734`;
`SmoothingDefinition.lean:39 SmoothingData`, `:152 smoothing_data`; `CarriersLemma.lean:42,126`;
`UniformDefinition.lean:27,42`; `DecompositionDefinition.lean:15 IsDecomposition`;
`InterlaceSupports.lean:14,27`.

Rotation: `RotationNumber.lean:10 rotationNumber`, `:45 rotationNumber_integer`, `:53
rotationNumber_shift`; `RegularPerturbation.lean:38 continuousAt_rotationNumber`, `:46
rotationNumber_locally_constant`, `regular_persists`; `RotationContinuity.lean:39-58`;
`AppendRotation.lean:54 rotationNumber_appendVertex`; `DeletedTuple.lean append_deleteVertex`,
`strictBetween_append_deleteVertex`; `Chambers.lean continuousAt_edgeParameter_of_geometry`
(GeometricParameters.lean).

## 4. Proof-effort estimate (lines of Lean) and strategy per field

Def row (`flat_carriers_definition`), ≈ 950 lines:
- `radius_*`, `identify_sides`: 15 (unpack `FlatSidesData`'s δ).
- `identify_sides_marks`: 120 — mark-key order transport (vertex/visit cases; vertex vs visit by
  edge index and parameter `0 < p`), then `List.Perm.eq_of_pairwise` as in
  `geometricGaussList_transport`.
- `identify_deletion`: 1 (`flat_fusion_data`).
- `identify_deletion_marks`: 250 — sorted-list/erase/map/rotation argument; the visit part is
  `geometricGaussList_fusion_rotation`-like (`FusionGaussWord.lean:33`), vertices via
  `deletionIndex`; the cut point moves from vertex 0 to vertex `j+1` → `Cycle` equality.
- `common_independence`: 60 (`GeometricRecordsAgree.2.2.2.1`, `geometric_interlaces_fusion`,
  `Finset.mem_map`).
- `GeoCarrierSpec` ×3: rfl fields 0; `mark_*`, `marks_injective` 15; `successor_gap` 40 (port of
  `nextMark_no_mark_between`); `traced_marks` 10 (proved lemmas); `traced_successor`: sides and
  deletion 40 via `geoSmoothingSuccessor_eq_generic` + `componentMarkList_getElem_successor`;
  centre 150 via `identify_sides_marks` + `correspond_sides`-style conjugation transporting the
  side's inherited order; `inherited_pieces`: generic configs 30 (`smoothingSegment_mem_edgeSegment`
  through the equalities), centre 80 (successor gap ⇒ same edge, parameters ordered).
- `carriers_are_cycles`: 15. `sides_are_smoothing_carriers`: 30 (proved lemmas + `smoothing_data`).
  `centre_deletion_same_words`: 20.

Cor row (`flat_carriers`), ≈ 2450 lines:
- `side_records`: 5. `correspond_sides`: 150 (from `identify_sides_marks`: `List.next` commutes
  with `map` of an injective function ⇒ `ρ^T ∘ T = T ∘ ρ^C`; `selectedMarkPerm` commutes with
  `markTransport` since `visitTransport` commutes with `visitTwin` (`same_pairing`); owner-iff by
  `Equiv.Perm.SameCycle.conj`/`sameCycle_conj`).
- `correspond_deletion`: 250 (skip-successor from `identify_deletion_marks`; owner-iff by an
  `EqOn`/`BijOn` argument on the block of marks `≠ inl j`).
- `unique_through_mu_j`: 60 (`crossingPoint ≠ vertex` and vertex injectivity in `FlatSidesData`).
- `central_vs_deletion_through_mu_j`: 250 (filter/erase commute; `vertex_corner_directions`
  transported to the centre; fusion eq. `edge C (j-1) = r•w`, `edge C j = (1-r)•w` from
  `FlatFusionData`).
- `others_unchanged`: 150 (owner-iff + list filter/map; plane points equal by
  `crossingPoint_fusion`, `deleteVertex_apply`).
- `nonzero_segments`, `no_antiparallel`, `turns_nonzero`: sides and deletion 120 via
  `geoComponentEquivGeneric` + `carriers_clause_ii` + `componentTraceEdge_data`; centre 450 —
  the riskiest block (see §5): corner-polygon edges of the centre carrier are positive multiples
  of original edge directions, obtained either by porting the block-compression of
  `CarrierCornerPolygon.lean` to `CrossingGeometry` (~500 lines, mechanical) or by a limit
  argument from the sides (continuity of crossing points + `CrossingParameterOrderAgrees` for a
  positive lower bound); then `Regular` from `flat_center_geometry` / transverse crossings.
- `same_retained_crossings`: 80; `same_pairing`: 30 (`visitTwin_unique`); `same_signs`: 40
  (`FlatSidesData` records, `FlatFusionData`).
- `same_rotation`: 300 — sides↔centre: the side corner polygon is a continuous family in `t`
  converging to the centre corner polygon (corner marks correspond, crossing points continuous),
  centre polygon `Regular` ⇒ `rotationNumber_locally_constant` ⇒ equality for `t` small, one δ for
  the finitely many carriers; deletion↔centre: the centre corner polygon of the μ_j carrier is
  `shift k (appendVertex (deletion corner polygon) r)` ⇒ `rotationNumber_appendVertex` +
  `rotationNumber_shift`; other carriers: equal polygons up to shift.
- `same_turn_signs_away`: 250 — turn at a corner = `sign det` of the two incident original
  directions (positive multiples), constant across configurations by `FlatSidesData`'s chi
  constancy off `turnSupport j` and `crossingSign_fusion`; corner indices correspond via the corner
  list equalities.
- `extra_corner`: 80 (`vertex_corner_directions` at `inl j` on the side + `sign det` of positive
  multiples = `turn T j`; sign change gives the right/left statements).
- `selector_identity`: 150 (table flatpr:selector-table: corner count of the side copy = deletion
  count + 1 from the corner-list correspondence; case analysis on all-right / all-left / mixed of
  the surviving turns using `same_turn_signs_away` and `extra_corner`).
- `other_selectors_agree`: 80 (equal turn multisets via corner correspondence).

Total ≈ 3400 lines (plus ~450 already written and proved in the statement file).

## 5. Riskiest points

1. Centre-side geometry of corner polygons (nonzero edges, `Regular`, turn signs) — the accepted
   proofs (`CarrierCornerPolygon.lean`, 860 lines) are parametrized by `Generic P`; at the centre
   one must either port block compression to `CrossingGeometry` or argue by limits from the
   sides. The intrinsic definition makes the port mechanical (only `visitPosition_interior`,
   `visitPosition_injective`, `g1_edge_ne_zero` and `crossing_edgeParameter_det_ne_zero` need
   `CrossingGeometry` replacements, all present), but it is the largest single block.
2. `identify_deletion_marks` / `correspond_deletion`: the deletion's sorted mark list is a
   ROTATION of the centre's (cut at vertex `j+1` vs `0`) with one mark removed; the `Cycle`-level
   equality must be threaded through `List.filter`/`erase`/`map` in the (i) fields. The visit-only
   version exists (`geometricGaussList_fusion_rotation`) and is the template.
3. `traced_successor` at the centre (inherited order of a carrier's marks) — no intrinsic proof at
   the centre; it is transported from a side via `correspond_sides`. This is faithful to the
   printed proof ("Exchanging the same selected successors in that permutation gives the same
   cycles afterwards") but couples the def row's centre spec to the cor row's correspondence
   (both are under the same theorem hypotheses, so no circularity).
4. `same_rotation` needs a uniform δ for finitely many carriers and continuity of the corner
   points in `t` (crossing points via `continuousAt_edgeParameter_of_geometry`); the corner mark
   lists must be identified across `t` (they are, via `identify_sides_marks`), but the corner
   polygons live on different index types `ZMod (geoCornerCount ..)` for different `t`, so the
   family must be re-indexed through the equal corner counts (`Nat` casts). Expect friction.
5. `geoCornerTurn` via `List.idxOf` is convenient in statements but proofs need
   `List.idxOf_getElem`/`getElem_idxOf` bookkeeping between `geoCornerMark` and `geoCornerIndex`.
6. Right/left: sm-1:743-744 define the right side by `τ_j = -1`; SM's `turn = +1` is a left turn
   (sm-1:84). The statement uses exactly this; a referee should confirm no consumer (sm-4:205)
   reads the sides the other way (it does not: `W(Q_*^right) − W(Q_*^left) = W(Q_*^D)`).

## 6. Missing auxiliary definitions

None are missing for the statements: everything is stated on the accepted library plus the
`geo*` restatements in the file. Two auxiliary lemmas will be needed for the proofs and do not
yet exist (intended statements):
- `geoMarkList_map_transport` (for `identify_sides_marks`): for `hP hQ : CrossingGeometry`,
  `hs`, `CrossingParameterOrderAgrees P Q` ⇒ `(geoMarkList hP).map (markTransport hs) = geoMarkList hQ`
  (mark analogue of `geometricGaussList_transport`).
- `geoMarkList_deleteVertex` (for `identify_deletion_marks`): under `hz hb hc`,
  `(((geoMarkList C).erase (Sum.inl j)).map delMark : Cycle) = (geoMarkList D : Cycle)`
  (mark analogue of `geometricGaussList_fusion_rotation`).
