# PLAN_FINAL — def:flat-carriers / cor:flat-carriers (judged design)

Written 2026-09-13 by the judge subagent after reading PLAN_A.md / Statement_A.lean (transport design,
725 lines) and PLAN_B.md / Statement_B.lean (intrinsic design, 1169 lines), the printed rows
`reference/SM/sm-3-statesum.tex:788-835` (proof 836-913), lem:flat-sides
`reference/SM/sm-1-polygons.tex:778-826`, and the accepted `work/lean/SM/FlatSides.lean`,
`SmoothingDefinition.lean`. Frame SM15. Companion: `work/drafts/flatcarriers/Statement_FINAL.lean`
(1285 lines; `cd work/lean && lake env lean ../drafts/flatcarriers/Statement_FINAL.lean` → exactly two
`declaration uses 'sorry'` warnings, at `flat_carriers_definition` and `flat_carriers`; every other
declaration is sorry-free with axioms `propext, Classical.choice, Quot.sound`, checked with
`#print axioms`).

## 0. Verdict

**Winner: B (intrinsic carriers on `CrossingGeometry`), with A's statement ergonomics grafted in.**

| criterion | A (transport) | B (intrinsic) |
|---|---|---|
| (a) fidelity | **6** | **8** |
| (b) provability | **7** | **6** |
| (c) reviewability | **6** | **7** |

Rationale.

*Fidelity.* The printed definition's operative sentence is "In each of these four configurations
mark the traversal circle …, exchange …, and trace …; at the centre and on the deletion the same
words define them, no genericity being assumed." B renders this literally: one definition
(`GeoComponent hP S`, the cycles of `ρ_S = ρ ∘ selectedMarkPerm S` on the marked circle sorted by
the centre's own crossing parameters) instantiated four times on `CrossingGeometry`, which is the
accepted record domain of lem:flat-sides (ii) ("no function on the generic locus is evaluated at the
flat centre"). A instead *defines* the centre carriers by transport from a side (indexed by
`SideCarrier b`) and certifies intrinsic-ness by def-row fields (`centre_successor`,
`centre_reconnection`, `centre_traced`, `centre_side_independent`); this is the printed *proof's*
first paragraph, not the printed definition, and it makes the side ↔ centre half of cor (i) "the
carriers correspond" definitional (a reviewer cannot check it). A also drops `hsc` from the def-row
theorem (weaker hypotheses; the bench asked for exactly lem:flat-sides' domain). B's `δ` is
per-`S` (the theorem takes `S` before `∃ δ`), a small weakening against the printed proof's "a common
sufficiently small interval works for all of them" — repaired here. Both flag the same broadenings
(centre copy in the turn-sign clause; nonzero corner edges; signs for all visits).

*Provability.* A's estimate (2200) is optimistic on its own centre geometry
(`centreCornerPolygon_edge` at 80 lines is the whole block-compression argument at the centre) and
its side ↔ centre rotation limit (250); B's (3400) is pessimistic on the port of the corner-polygon
lane. Both need the same three hard blocks: mark-list transport centre ↔ side, mark-list rotation
centre ↔ deletion with `μ_j` erased, and the corner geometry at the centre. B pays extra for
`GeoCarrierSpec` at the centre (`traced_successor`, `inherited_pieces`) but has already proved the
generic-agreement layer (`geoMarkList_eq_generic`, `geoSmoothingSuccessor_eq_generic`,
`geoComponentEquivGeneric`, mark/plane/corner list agreement) sorry-free inside the statement
file. Realistic totals: A ≈ 2700, B ≈ 3200.

*Reviewability.* B's definitions are checkable word for word against def:smoothing and
conv:selected-visits (`geoMarkPosition`, `geoSmoothingSuccessor`, `GeoComponent`), and "on the two
generic sides they are the carriers of def:smoothing" is a *theorem* in the file. B's fields carried
`∀ b t, t.val < δ → ∀ hs, …` boilerplate in every clause and used an `idxOf`-based `geoCornerTurn`
with no certificate; A's fields are lighter because `t` and `hs` are structure parameters and its
"no antiparallel" is the literal `¬ ∃ r < 0, edge k = r • edge (k-1)`. The final file takes B's
definitions and A's parametrisation.

## 1. The final design (B + grafts)

Kept from B (verbatim): namespace `SM.GeoCarrier` sections 1–3 (`geoMarkPosition`, `geoMarkList`,
`geoMarkSuccessor`, `geoSmoothingSuccessor`, `GeoComponent`, `geoOwner`, `geoComponentMarkList`,
`geoComponentPlaneCycle`, `geoSmoothingSegment`, `geoComponent_has_trueCorner`,
`geoComponentCornerList`, `geoCornerCount`, `geoCornerMark`, `geoCornerPolygon`, `geoCornerTurn`,
`geoCarrierCrossings`, `GeoIndependent`); the four configurations (`flatCentreCG`, `flatDeletionCG`,
`flatSideCG`), `markTransport`, `transportSupport`, `deletionSupport`, `fusionMark`/`delMark` with
their three lemmas, `centralCarrierThroughJ`, `deletionCopyThroughJ`; the generic-agreement section
4b; `GeoCarrierSpec`; the shapes of the cor fields `correspond_sides`, `correspond_deletion`,
`unique_through_mu_j`, `central_vs_deletion_through_mu_j`, `others_unchanged`, `nonzero_segments`,
`turns_nonzero`, `same_retained_crossings`, `same_pairing`, `same_signs`, `same_rotation`,
`extra_corner`, `selector_identity`, `other_selectors_agree`.

Grafted from A / changed by the judge:

1. **Parameters.** Both structures take `(t : g.SideParameter) (hs : CommonSupports g t) (S)`;
   `CommonSupports g t := ∀ b s, IsCrossing g.center s ↔ IsCrossing (side b) s` (A). Every
   `∀ b t, t.val < δ → ∀ hs` prefix of B disappears. The theorems read
   `∃ δ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t, t.val < δ → ∃ hs : CommonSupports g t, ∀ S, GeoIndependent C S → Data`
   — one radius for all `t`, all `S`, all carriers (printed "after shrinking the interval" / "a
   common sufficiently small interval"), `hs` produced not assumed.
2. **Domain.** Both theorems take exactly lem:flat-sides' hypotheses `hn g hz hb hc hsc`
   (A omitted `hsc` in the def row; B had it). `hsc` is unused by the def-row proof; it is kept
   for the exact printed domain.
3. **`named_sides`** (cor): `∃ br, IsRightSide g j br t ∧ IsLeftSide g j (!br) t` (A's
   `right_side`/`left_side`, here derived from the sign change rather than assumed). Right = `τ_j = -1`
   (`turn = -1`, a right turn), left = `τ_j = +1` (def:walls (F), sm-1:743-744).
4. **`no_antiparallel`** in A's literal form `¬ ∃ r : ℝ, r < 0 ∧ edge Q k = r • edge Q (k-1)` (B had
   `Regular`; with `nonzero_segments` the two are `regular_iff_edges`).
5. **`selector_def`** (A): the three defining clauses of `cornerSelector` plus
   `geoCarrierSelector = cornerSelector ∘ geoCornerPolygon` (the printed sentence "Define a
   carrier's selector …" gets its field).
6. **Corner-cycle conjuncts** in `central_vs_deletion_through_mu_j` and `others_unchanged` (A): the
   corner lists correspond as cycles (with `μ_j` erased / unchanged), alongside B's mark-cycle and
   plane-cycle equalities. Needed by (iii) (`c_side = c_del + 1`) and reviewable as "differs only by
   the subdivision at `μ_j`" at the corner level.
7. **`central_vs_deletion_through_mu_j`** starts with `ρ_S^C (inl j) ≠ inl j`, certifying that
   `deletionCopyThroughJ` (the deletion carrier of `delMark (ρ_S^C (inl j))`) is the deletion copy.
8. **`correspond_deletion`** gets a third conjunct `∀ q : centre carrier, ∃ b : Mark D, owner_C (fusionMark b) = q`
   so that, with the owner-iff, the assignment deletion carrier ↦ centre carrier is a bijection (A's
   `Function.Bijective`, stated without `Quotient.out`). Side ↔ centre needs no extra conjunct
   (`markTransport` is an `Equiv`).
9. **`same_turn_signs`** is stated side ↔ deletion (the printed "on both sides and in the
   deletion") and the centre copy is a separate flagged field `centre_turn_signs` (A's split; B had
   folded the centre in).
10. **`geoCornerTurn` certificate.** `geoCornerIndex` is now `Classical.choose` of
    `geoCornerMark_exists` (proved: every owned true corner is a `geoCornerMark`), and
    `geoCornerMark_geoCornerIndex : IsTrueCorner S a → geoCornerMark (geoOwner a) (geoCornerIndex a) = a`
    is proved in the file (B's `List.idxOf` version could not be certified: the classical `BEq`
    has no `LawfulBEq` instance syntactically).
11. Names: `cornerSelector` (on `LabelledTuple k`) and `geoCarrierSelector` (on a carrier);
    `flat_hn1 hn : 3 ≤ n + 1` replaces `by omega` where a term is needed.

## 2. Exact statement decisions, clause by clause

### def:flat-carriers (sm-3:788-804) → `FlatCarriersDefinitionData hn g j hz hb hc t hs S`

| printed | field | notes |
|---|---|---|
| "Under the hypotheses of lem:flat-sides" | theorem hypotheses `hn g hz hb hc hsc`; `∃ δ … ∀ t < δ, ∃ hs` | same as `flat_sides`; `n + 1 ≥ 4` |
| "identify the crossing visits of the two sides, of the centre P(0) … through the common cyclic Gauss word of … (ii)" | `common_gauss_word.1,.2,.4` | Gauss list (cut at `0`) and cyclic word carried by `visitTransport (hs b)` / `crossingTransport (hs b)`; pairing commutes |
| "… and of the deletion P(0)∖j through … (iii)" | `common_gauss_word.3,.5`, `identify_deletion : FlatFusionData` | cyclic word carried by `fusionCrossingEquiv`; pairing commutes; accepted fusion packet |
| (extension to marks, STRONGER) | `identify_sides_marks`, `identify_deletion_marks` | `(geoMarkList C).map (markTransport (hs b)) = geoMarkList T`; `((geoMarkList C).erase (inl j)).map delMark = geoMarkList D` as cycles |
| "fix an independent set S in their common interlacement graph" | `common_interlacement`, `independent_supports` | graphs correspond under both identifications; `GeoIndependent C S ↔ IsDecomposition` on each side and on the deletion |
| "In each of these four configurations mark …, exchange …, trace …" | `centre_carriers`, `deletion_carriers`, `side_carriers : ∀ b, …` — each `GeoCarrierSpec` | one spec, four instances: marks (vertex `(i,0)`, visit at its interior parameter), injectivity, `ρ` = traversal successor (`successor_gap`), `ρ_S = ρ ∘ selectedMarkPerm`, selected swap, cycles, traced curve, inherited order (`traced_successor`), straight inherited subsegments on the edge of the outgoing slot, corners |
| "These oriented closed polygonal cycles are the carriers of S" | `carriers_are_cycles` | centre and deletion; sides via sentence 4 |
| "On the two generic sides they are the carriers of def:smoothing" | `sides_are_smoothing_carriers` | `geo* = accepted*` (positions, list, `ρ`, `ρ_S`, owners through `geoComponentEquivGeneric`, mark/plane/corner lists) and the accepted `SmoothingData` |
| "at the centre and on the deletion the same words define them, no genericity being assumed" | `centre_deletion_same_words` | `¬ Generic g.center`; centre `ρ_S = ρ ∘ swap`, carriers = cycles; deletion `geo* = accepted*` and `SmoothingData` |

### cor:flat-carriers (sm-3:805-835) → `FlatCarriersData hn g j hz hb hc t hs S`

| printed | field |
|---|---|
| "form the carriers … on both sides, at the centre and on the deletion" (right/left named) | `named_sides` |
| (i) "The carriers correspond under their named traversal arcs" | `correspond_sides` (∀ b: `ρ_S^T ∘ markTransport = markTransport ∘ ρ_S^C`; owner-iff), `correspond_deletion` (skip-`μ_j` successor; owner-iff through `fusionMark`; surjectivity onto centre carriers) |
| (i) "Exactly one contains μ_j" | `unique_through_mu_j` (centre: ↔ `centralCarrierThroughJ`; each side: ↔ carrier of `inl j`) |
| (i) "The central copy … differs from its deletion copy only by the positive-flat subdivision at μ_j" | `central_vs_deletion_through_mu_j` (`ρ_S^C (inl j) ≠ inl j`; mark cycle and corner cycle with `μ_j` erased = deletion copy's; `StrictBetween`; both incident displacements positive multiples of `edge D (-1) = μ_{j+1} - μ_{j-1}`, eq. flatpr:fusion) |
| (i) "every other central carrier is unchanged by deletion" | `others_unchanged` (mark cycle, corner cycle, plane cycle) |
| (i) "Every carrier has nonzero segments" | `nonzero_segments` (subsegments and corner-polygon edges, four configurations) |
| (i) "and no antiparallel corner" | `no_antiparallel` (literal, four configurations) |
| (i) "except for that one central zero turn, all corner turns are nonzero" | `turns_nonzero` (centre: `turn = 0 ↔ corner mark = inl j`; deletion, sides: `≠ 0`) |
| (ii) "same retained self-crossing visits, pairing, signs and positive over/under bits" | `same_retained_crossings`, `same_pairing`, `same_signs` |
| (ii) "same signed rotation and hence the same absolute rotation" (round 4: centre copy included) | `same_rotation` (side = centre, deletion = centre, signed and absolute) |
| (ii) "Every corresponding corner away from μ_j has the same turn sign on both sides and in the deletion" | `same_turn_signs` (`geoCornerTurn T (markTransport a) = geoCornerTurn D (delMark a)` for corner marks `a ≠ inl j`, both sides) |
| (flagged broadening, proof text sm-3:875-876) | `centre_turn_signs` |
| (ii) "The extra corner at μ_j is right on the right side and left on the left side" | `extra_corner` (`geoCornerTurn T (inl j) = turn T j`; `IsRightSide → -1`; `IsLeftSide → 1`) |
| (iii) "Define a carrier's selector …" | `cornerSelector`, `geoCarrierSelector`, field `selector_def` |
| (iii) `W_right − W_left = W_del` | `selector_identity` (∀ bR bL with `IsRightSide bR`, `IsLeftSide bL`) |
| (iii) "All other corresponding carrier selectors agree" | `other_selectors_agree` (side copy = deletion copy, each side, carriers ≠ the `μ_j` one) |
| closing sentences | no field (non-definitional) |

Conventions. `C = g.center` with `flatCentreCG`, `D = deleteVertex g.center j` with `flatDeletionCG`
(`= generic_crossingGeometry hn (generic_deleteVertex …)`), `T = (g.sideTuple b t).val` with
`flatSideCG`; `S_T = transportSupport (hs b) S`, `S_D = deletionSupport hn g j hz hb hc S`.
Side copy of the centre carrier of `a` = `geoOwner T S_T (markTransport (hs b) a)`; centre copy of
the deletion carrier of `b` = `geoOwner C S (fusionMark b)`. `markTransport (hs b) (inl j) = inl j`
definitionally, so the `μ_j` carrier on a side is `geoOwner T S_T (inl j)`. Rotation is
`rotationNumber` of `geoCornerPolygon` (def:uniform's `carrierRotation` unfolds to the accepted
`ccpCornerPolygon`, which equals `geoCornerPolygon` on a side through `geoComponentEquivGeneric`).

## 3. STRONGER / WEAKER than printed

STRONGER (each justified by the printed proof and flagged in the docstrings):
- `identify_sides_marks`, `identify_deletion_marks`, `correspond_*`: the identification is given at
  the level of mark lists and successor conjugation (the printed "correspond under their named
  traversal arcs" is informal; the printed proof's first paragraph is exactly this).
- `correspond_deletion.3`: surjectivity onto centre carriers (bijection content of "correspond").
- `central_vs_deletion_through_mu_j.1`: `ρ_S^C (inl j) ≠ inl j` (well-namedness of the deletion copy).
- Corner-cycle equalities in `central_vs_deletion_through_mu_j` and `others_unchanged`.
- `nonzero_segments` also states nonzero corner-polygon edges (block compression).
- `same_signs` is for all crossing visits, not only retained ones (lem:flat-sides (ii)/(iii) content).
- `same_rotation` includes the centre copy (round-4 status note) and `centre_turn_signs` includes
  the centre copy for turn signs (proof text only; strike if the bench wants the literal (ii)).
- `extra_corner.1`: the corner turn at `μ_j` equals the side's own `τ_j(t)` (proof text).
- `unique_through_mu_j` also on the sides.
- `sides_are_smoothing_carriers` asserts the full accepted `SmoothingData`.
- The def-row theorem keeps `hsc` although unused (exact domain, no strengthening).

WEAKER / reading choices:
- "Named traversal arcs" are read as `ρ_S`-steps (mark → successor); no separate arc object.
- The deletion identification of the mark `μ_j` is junk (`delMark (inl j)`), excluded by every clause.
- The selector at the centre is never evaluated (as printed).
- `other_selectors_agree` states side = deletion for each side (right = left follows).
- `unique_through_mu_j` reads "contains μ_j" as the plane point `μ_j` lying on the traced cycle.
- `carriers_are_cycles` partly restates `GeoCarrierSpec.carriers` (kept for one field per sentence).

## 4. Reuse (accepted, `work/lean/SM/…`; all cited entries exist)

`FlatSides.lean:17,47` (`FlatSidesData`: centre injective/edges/`Regular`/`turn = 0 ↔ i = j`/positive
multiple; `FlatFusionData`; `∃ δ` with the turn-product `< 0`, chi constancy off `turnSupport j`,
`CrossingGeometry (g.curve t)`, `crossingPoint` injective and `≠` vertices,
`CrossingParameterOrderAgrees g.center (g.curve t)`, `GeometricRecordsAgree` (`∃ hs, Gauss list/word,
interlacement, signs`), deletion in the chamber of `Q`); `FlatFusionData.lean:12,52` (`r` with
`edge C (j-1) = r • edge D (-1)`, `edge C j = (1-r) • edge D (-1)`, `visitParameter_fusion`, supports,
`crossingPoint_fusion`, `fusionVisit_edge`, pairing, cyclic order iff, word, interlacement,
`crossingSign_fusion`, `positive_over_fusion`); `FlatLocal.lean:49 flat_germ_local_data`;
`FlatCenter.lean:30`; `FlatCrossingGeometry.lean:12`; `DeletionGeneric.lean:31`;
`GeometricRecords.lean:35,49,55` (`geometricGaussList_transport`, `geometricGaussWord_transport`);
`GeometricTransport.lean:10,14,33` (`geometric_visitParameterOrder`, `geometric_visitKey_lt_transport`);
`GeometricInterlacement.lean:16,38`; `CrossingTransport.lean:12,18` (+ `visitTransport_edge`,
`visitTransport_crossing`); `GeometricVisits.lean:12,22,49,56,59-70`; `GeometricParameters.lean:58
continuousAt_edgeParameter_of_geometry`; `CrossingGeometry.lean:11,24,52,61`; `Traversal.lean:46,73`
(`traversalKey_lt_iff`, `traversalBetween`); `SortedCyclicGap.lean:10 sorted_next_no_cyclic_between`
(generic in the `LinearOrder`); `SortedCompressedCut.lean:8 sorted_map_monotone_cut_rotation`;
`FusionKey.lean:33-72` (`fusionKey`, `fusionKey_low/middle/high`, `fusionVisitKey_compression`);
`FusionGaussWord.lean:33 geometricGaussList_fusion_rotation` (template); `DeletionIndices.lean`
(`deletionIndex`, `_zero`, `_last`, `_exhaust`, `_ne_deleted`); `DeletedTuple.lean` (`deleteVertex_apply`,
`edge_deleteVertex`, `edge_deleteVertex_last`, `append_deleteVertex`, `strictBetween_append_deleteVertex`);
`FusionIndices.lean`, `FusionGeometry.lean:34 edge_fusion`, `FusionVisits.lean:39-64`,
`FusionCrossings.lean:42,91`; `StrictBetween.lean:9,19`; `AngleScaling.lean:12 principalAngle_smul`;
`RegularLocus.lean:12,18 regular_iff_edges`; `RotationNumber.lean:10,45,53`; `RegularPerturbation.lean
regular_persists, continuousAt_rotationNumber, rotationNumber_locally_constant`;
`RotationContinuity.lean:39,45`; `AppendRotation.lean:26,54 regular_appendVertex, rotationNumber_appendVertex`;
`InsertedTuple.lean:11 appendVertex`; carriers: `CarrierMarks.lean`, `CarrierSuccessor.lean:114
nextMark_no_mark_between` (template), `CarrierSmoothing.lean:36,82,124,130`, `CarrierVisitTwin.lean:34,60,80`,
`CarrierAmbientTransport.lean:54 sameCycle_congr_of_eqOn_bijOn`, `CarrierIndependentOrder.lean:81
independent_inheritsMarkOrder`, `CarrierClosedTrace.lean:59-118`, `CarrierCrossings.lean:130-380`
(direction lemmas, templates for the centre port), `CarrierCornerPolygon.lean:36-506,536-691,822
carriers_clause_ii`, `SmoothingDefinition.lean:39,152`, `DecompositionDefinition.lean:15`,
`InterlaceSupports.lean:27,46`, `UniformDefinition.lean:42`, `WallGerm.lean`, `GermSignChange.lean:10`,
`Generic.lean:72 g1_vertices_injective`.

## 5. Proof plan — five independent prover units

Each unit writes new lemmas in `work/drafts/flatcarriers/U<k>_*.lean` (importing
`Statement_FINAL.lean`'s content, to be moved into `work/lean/SM/FlatCarriers*.lean` at acceptance)
and may ASSUME the listed interface lemmas of other units as explicit hypotheses of its own lemmas
(state them as arguments, never `sorry` them). The assembly (U1) fills the two theorems from the
units' top lemmas. Notation as in §2; `hF : FlatSidesData hn g j hz hb hc := flat_sides … hsc`.

### U1 — Records, mark identifications, generic configurations, assembly (≈ 700 lines)

Goals (def row except the centre spec; cor `named_sides`, `same_pairing`, `same_signs`;
the two theorems):
1. `flat_common_supports : ∀ t, t.val < δF → CommonSupports g t` from `hF`'s `GeometricRecordsAgree`
   (`Exists.choose` of the `∃ hs`; proof irrelevance identifies it with any other `hs`).
2. `common_gauss_word` (from `GeometricRecordsAgree` + `geometricGaussWord_fusion`; pairing via
   `visitTwin_unique` and `fusionVisit_pairing`), `common_interlacement`
   (`GeometricRecordsAgree.2.2.2.1`, `geometric_interlaces_fusion`), `independent_supports`
   (`mem_independentSupports_iff`, `Finset.mem_map_equiv`, `geometricInterlaces_iff_generic`).
3. **`geoMarkList_map_transport`** (new, needed by U2): for `hP hQ : CrossingGeometry` on `n`-gons,
   `hs`, `CrossingParameterOrderAgrees P Q` ⇒ `(geoMarkList hP).map (markTransport hs) = geoMarkList hQ`.
   Proof as `geometricGaussList_transport`: `List.Perm.eq_of_pairwise` with the key order transported
   mark by mark (`traversalKey_lt_iff`; vertex/vertex by index; vertex/visit by edge index and
   `0 < visitParameter`; visit/visit by `geometric_visitKey_lt_transport`). Gives `identify_sides_marks`.
4. **`geoMarkList_deleteVertex_rotation`** (new, needed by U2):
   `(((geoMarkList C).erase (inl j)).map delMark).IsRotated (geoMarkList D)` via
   `sorted_map_monotone_cut_rotation` with `k = geoMarkKey C`, `t = geoMarkKey D`, `N = n+1`,
   `a = (j+1).val`, `φ = fusionKey (n-1) r` (`fusionKey_strictMono`), `hp` from `delMark` bijective off
   `inl j` (`fusionMark_delMark`, `delMark_fusionMark`), `hk` from `fusionVisitKey_compression` for
   visits and `fusionKey_low/middle` + `deletionIndex`/`fusionIndex` arithmetic for vertices. Gives
   `identify_deletion_marks` (`Cycle.coe_eq_coe`). This is the riskiest item of U1 (≈ 250 lines).
5. `deletion_carriers`, `side_carriers` (`GeoCarrierSpec` on generic configurations): every field via
   the section-4b equalities and the accepted `smoothing_data`/`componentMarkList_getElem_successor`/
   `vertex_corner_directions`/`smoothing_corner_directions`/`visit_incoming_mem_edgeSegment`;
   `successor_gap` via `nextMark_no_mark_between` through `geoMarkSuccessor_eq_generic`.
6. `sides_are_smoothing_carriers`, `centre_deletion_same_words`, `carriers_are_cycles`, `named_sides`
   (turn product `< 0` ⇒ `SignType` case split), `same_pairing`, `same_signs`
   (`GeometricRecordsAgree` signs read at `v.2.val, (visitTwin v).2.val`; `crossingSign_fusion`,
   `positive_over_fusion`, `fusionVisit_edge`).
7. Assembly: `δ := min` of `hF`'s `δ` and U4's `δ_rot`; build both structures from U1–U5's top lemmas.

May assume: nothing from other units except U2's `GeoCarrierSpec C S` and U2–U5 top lemmas at
assembly time.

### U2 — Centre spec by transport, carrier correspondences, cycle identities (≈ 900 lines)

Goals: `centre_carriers : GeoCarrierSpec C S`; cor `correspond_sides`, `correspond_deletion`,
`unique_through_mu_j`, `central_vs_deletion_through_mu_j` (all but the two geometric conjuncts, see
U3), `others_unchanged`, `same_retained_crossings`.

1. `GeoCarrierSpec C S` intrinsic fields: `mark_*` (rfl / `geometricVisitPosition_evaluation` /
   `crossingParameter_interior_of_geometry`), `marks_injective` (`geoMarkPosition_injective`),
   `successor_gap` (port of `nextMark_no_mark_between`: `sorted_next_no_cyclic_between` on
   `geoMarkLinearOrder`, 20 lines), `reconnection`/`reconnect_selected`/`keep_*` (rfl,
   `geoSmoothingSuccessor_visit_of_mem/not_mem`), `carriers` (`geoOwner_eq_iff`), `traced_curve`
   (rfl), `traced_marks` (proved lemmas), `straight_pieces` (rfl), `corners`/`corner_*` (rfl).
2. **`ρ_S` conjugation** `geoSmoothingSuccessor T S_T ∘ markTransport = markTransport ∘ geoSmoothingSuccessor C S`
   from U1.3: `List.next` commutes with `List.map` of an injective map on nodup lists
   (`List.next_getElem` on both sides + `List.getElem_map`); `selectedMarkPerm S_T (markTransport a) =
   markTransport (selectedMarkPerm S a)` from `visitTwin` commutation (U1.2) and
   `Finset.mem_map_equiv`. Owner-iff by `Equiv.Perm.SameCycle` under conjugation
   (`SameCycle.conj` or a two-line `zpow` argument). Gives `correspond_sides`.
3. `traced_successor` and `inherited_pieces` at the centre by transport: `geoComponentMarkList C q`
   maps under `markTransport` to `geoComponentMarkList T q'` (`List.map_filter` + owner-iff), so the
   side's `componentMarkList_getElem_successor` (through `geoComponentMarkList_eq_generic`) and item 2
   give the centre's; `inherited_pieces`: `ρ(a')` is the next mark after `a'` (`successor_gap`),
   hence on the same edge at a larger centre parameter or the next vertex, and the segment lies in
   `edgeSegment C e` (convexity of `edgeSegment`; `CrossingParameterOrderAgrees` is not needed once the
   gap is intrinsic). ≈ 200 lines.
4. **Skip-`μ_j` conjugation** from U1.4: for `b : Mark D`, `ρ_S^D b = delMark (ρ_S^C (fusionMark b))`
   unless `ρ_S^C (fusionMark b) = inl j`, in which case `= delMark (ρ_S^C (inl j))` (rotation of the
   erased list; `List.next` of `erase`). Owner-iff through `fusionMark` by
   `sameCycle_congr_of_eqOn_bijOn` on the block `{a | a ≠ inl j}` with the modified permutation, or by
   direct `zpow` induction with one skipped point. Surjectivity: `ρ_S^C (inl j) ≠ inl j` (a
   successor on a circle with ≥ 4 marks is not itself: `geoMarkList` has length ≥ n+1 ≥ 4 and is
   nodup) and `fusionMark_delMark`. Gives `correspond_deletion` and
   `central_vs_deletion_through_mu_j.1`.
5. Cycle identities: `central_vs_deletion_through_mu_j.2,.3` and `others_unchanged.1,.2` from items 2,4
   (`List.filter`/`erase`/`map` commutation on `geoMarkList`, then `Cycle.coe_eq_coe` via U1.4's
   rotation); `others_unchanged.3` from `crossingPoint_fusion`, `deleteVertex_apply`.
6. `unique_through_mu_j` (`FlatSidesData.1` centre injectivity, `crossingPoint_ne_vertex_of_geometry`,
   `g1_vertices_injective` on the sides; `hF`'s `crossingPoint c ≠ g.curve t k`);
   `same_retained_crossings` (`Finset.mem_filter`, owner-iff, pairing commutation).

May assume: U1.3 `geoMarkList_map_transport` and U1.4 `geoMarkList_deleteVertex_rotation` (as
hypotheses), `hF`.

### U3 — Corner geometry at the centre; turns (≈ 900 lines, riskiest)

Goals: `nonzero_segments`, `no_antiparallel`, `turns_nonzero`, `same_turn_signs`, `centre_turn_signs`,
`extra_corner`, and the two geometric conjuncts of `central_vs_deletion_through_mu_j`
(`StrictBetween`, positive multiples of `edge D (-1)`).

1. Sides and deletion: through `geoComponentEquivGeneric`, `geoComponentCornerList_eq_generic`
   (so `geoCornerPolygon = ccpCornerPolygon` up to the equivalence, `geoCornerCount = ccpCornerCount`)
   and `carriers_clause_ii` (nonzero edges, no antiparallel, turns `≠ 0`, vertex turn `= turn P i`,
   smoothing turn `= crossingSign`); subsegments via `smoothingSegment_length_pos`. ≈ 120 lines.
2. **Centre direction lemmas** (port of `CarrierCrossings.lean:130-300` to `CrossingGeometry`,
   replacing `visitPosition_interior` → `crossingParameter_interior_of_geometry`,
   `visitPosition_injective` → `geometricVisitPosition_injective`, `(g1 …).2.1` → `hP.1`,
   `crossing_edgeParameter_det_ne_zero` → `crossing_det_ne_zero_of_geometry`, `nextMark_no_mark_between`
   → U2's `successor_gap`): the displacement from a mark to its `ρ_S`-successor is a positive multiple
   of `edge C e` for the edge `e` of the outgoing slot; the incoming displacement at a mark is a positive
   multiple of the edge of its `ρ`-predecessor. ≈ 250 lines.
3. **Centre block compression** (`geoCornerPolygon_edge_centre`): each edge of `geoCornerPolygon C S q`
   is a positive multiple of `edge C (outgoing slot edge of the corner)`; port of
   `ccp_block_compression`/`ccp_corner_chain`/`ccpCornerPolygon_block`/`ccpCornerPolygon_edge`
   (the union-of-segments part may be dropped) — or the shorter route: the corner marks and the
   in/out slots are the side's (U2.2), the two corner points lie on the centre edge `e` at parameters
   `s < t` (order of the intermediate marks is the sorted order), hence the difference is
   `(t - s) • edge C e`. ≈ 300 lines. Then `nonzero_segments` (centre), `no_antiparallel`
   (two consecutive corner edges are positive multiples of `edge C (in-edge)`, `edge C (out-edge)`
   whose `det ≠ 0` at a smoothing corner (`hP.2` transversality) and at a vertex `i ≠ j`
   (`FlatSidesData.4`); at `μ_j` they are positive multiples of each other (`FlatSidesData.5`), not
   antiparallel), `turns_nonzero` (centre iff: `turn_det`, `sign` of positive multiples).
4. Turn transport: `turn (geoCornerPolygon X q) k = sign det (edge X in) (edge X out)` in every
   configuration (item 3 and its side/deletion analogue `ccpCornerPolygon_turn_eq_sign`); the
   original directions correspond (`chi (g.curve t) = chi g.center` off `turnSupport j` from `hF`;
   `crossingSign_fusion`; at a vertex corner `i ≠ j` the in/out edges are `i-1, i`, at a smoothing
   corner `v.2, (visitTwin v).2` — for the deletion `fusionIndex` of these, `FlatFusionData` sign
   clauses). Gives `same_turn_signs`, `centre_turn_signs`, `extra_corner` (`ccpCornerPolygon_turn_vertex`
   on the side, `IsRightSide`/`IsLeftSide` unfold).
5. `StrictBetween` and the fused multiples at `μ_j`: the predecessor of `inl j` is on edge `j-1`,
   its successor on edge `j` (item 2), so the displacements are positive multiples of `edge C (j-1)`,
   `edge C j`, which are `r • edge D (-1)`, `(1-r) • edge D (-1)` (`FlatFusionData.2`); `StrictBetween`
   from the two positive multiples of one nonzero vector.

May assume: U2's `GeoCarrierSpec C S` and correspondences (as hypotheses), `hF`.

### U4 — Rotation (≈ 600 lines)

Goals: `same_rotation` (both halves), and a radius `δ_rot` for the side half.

1. Deletion ↔ centre. For the `μ_j` carrier: the centre corner list is the deletion corner list with
   `inl j` inserted between its neighbours (U2.5 corner-cycle identity), so
   `geoCornerPolygon C muC = shift a (appendVertex (geoCornerPolygon D delCopy) r')` for the `r'` of
   `StrictBetween` (U3.5; `append_deleteVertex`-style equality on `ZMod` indices; expect index
   bookkeeping), then `rotationNumber_shift`, `rotationNumber_appendVertex` (needs `Regular` of the
   deletion polygon: U3.1). Other carriers: equal corner polygons up to `shift` (U2.5) ⇒
   `rotationNumber_shift`. Absolute values by `congrArg`.
2. Side ↔ centre (the printed limit argument). Fix `S` and a centre carrier `q`; the corner marks of
   its side copies are the same marks for every `t` (U2.2 applied at each `t`), so
   `F : g.Parameter → LabelledTuple (geoCornerCount C S q)`, `F s := fun k => point of the corner mark k
   read on g.curve s` (vertices by `g.continuous_curve`, crossing points by `crossingPoint =
   edgePoint _ e (edgeParameter _ e f)` and `continuousAt_edgeParameter_of_geometry` at the centre) is
   continuous at `0` with `F 0 = geoCornerPolygon C S q`, which is `Regular` (U3.3 +
   `regular_iff_edges`); `rotationNumber_locally_constant` gives `∀ᶠ s, rot (F s) = rot (F 0)`;
   `F (sideTime b t) = geoCornerPolygon T S_T (side copy)` up to the re-indexing
   `ZMod (geoCornerCount T …) = ZMod (geoCornerCount C …)` (equal counts from U2.2; use
   `LabelledTuple` transport along the `Nat` equality). Uniform `δ_rot`: `Filter.eventually_all` over
   the finitely many `S : Finset (Crossing g.center)` and `q : GeoComponent C S`
   (`Fintype`), then `g.eventually_center_iff_radius`. ≈ 400 lines; the re-indexing is the friction
   point (both plans agree).

May assume: U2 (correspondences, corner-cycle identities, equal corner counts), U3 (`Regular` of all
corner polygons, `StrictBetween`), `hF`.

### U5 — Selector (≈ 250 lines)

Goals: `selector_def`, `selector_identity`, `other_selectors_agree`.

1. `selector_def`: unfold `cornerSelector` (`if_pos`/`if_neg`), `geoCarrierSelector` rfl.
2. `other_selectors_agree`: a bijection of corner indices side ↔ deletion preserving turns (U3.4 +
   U2.5 corner cycles) ⇒ `∀ i, turn = -1` and `∀ i, turn = 1` transfer and the counts agree ⇒ equal
   selectors.
3. `selector_identity`: the printed table flatpr:selector-table. Corner count of each side copy of the
   `μ_j` carrier `= c + 1` with `c` the deletion copy's count (U2.5); the surviving turns agree (U3.4);
   the extra turn is `-1` on `bR`, `+1` on `bL` (`extra_corner`). Case split: mixed surviving turns ⇒
   `0 - 0 = 0`; all right ⇒ `1 - 0 = 1`; all left ⇒ `0 - (-1)^(c+1) = (-1)^c` (`pow_succ`).

May assume: U2.5, U3.4, `extra_corner`.

Total ≈ 3350 lines (range 2800–3800).

## 6. Risks (ranked) and fallbacks

1. **U3 centre corner geometry** — largest block; the port is mechanical (replacement table above)
   but long. Fallback: prove only `geoCornerPolygon_edge_centre` by the "two corner points on one
   centre edge" route and skip the union-of-segments statements (not needed by any field).
2. **U1.4 / U2.4 deletion mark list** — the `Cycle` rotation with one erased element threaded through
   `filter`/`erase`/`map`; template `geometricGaussList_fusion_rotation` (visits only). Fallback: prove
   the owner-iff for the deletion directly by `zpow` induction on the skip permutation and derive the
   list statements afterwards.
3. **U4.2 re-indexing across `t`** — different `ZMod` index types per `t`; mitigate by stating the
   family on the centre's index type and transporting corner marks, never polygons.
4. **U2.2 `List.next` vs `map`** — no direct Mathlib lemma; prove via `List.next_getElem` and
   `List.getElem_map` (nodup both sides).
5. Right/left reading (`turn = -1` right) — matches sm-1:743-744 and sm-4:205
   (`W(right) − W(left) = W(del)`); a referee should confirm once.

## 7. Compile status

`cd work/lean && lake env lean ../drafts/flatcarriers/Statement_FINAL.lean` →
`:950 declaration uses 'sorry'` (`flat_carriers_definition`), `:1272 declaration uses 'sorry'`
(`flat_carriers`); nothing else. `#print axioms` on `geoCornerMark_geoCornerIndex`,
`geoComponent_has_trueCorner`, `geoComponentCornerList_eq_generic`, `geoComponentEquivGeneric`,
`fusionMark_delMark`: `[propext, Classical.choice, Quot.sound]`.
