# Row 156 — CV:lem:pieceintrinsic — report

File: `work/drafts/cvdom/CVPieceIntrinsic.lean` (1058 lines). Main declaration `CV.pieceintrinsic : CV.PieceIntrinsicData …`
(bundle `CV.PieceIntrinsicData`, working form `CV.pieceintrinsic_of_diagrammatic`). Written 2026-09-14 by a Claude Code
prover subagent (draft; nothing under work/lean touched). Compiled with `cd work/lean && lake env lean ../drafts/cvdom/CVPieceIntrinsic.lean`:
exit 0, no errors, no warnings, no incomplete proofs, no new axioms. `#print axioms` on a /tmp copy:

| declaration | axioms |
|---|---|
| `CV.pieceintrinsic`, `CV.pieceintrinsic_of_diagrammatic` | `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` (the three literature interfaces, reached only through `homfly` / `CV.gausscode_polynomial` in the polynomial fields; same set as rows 157/160/163) |
| `CV.exists_recordIso_of_geoCarrierCrossings_eq` (the record isomorphism), `CV.cornerCoord_cycBetween_iff_key` | `propext, Classical.choice, Quot.sound` |

Imports: `CV.PieceCurve` only (which brings `CV.CarrierWord`, `CV.RecordHomfly` (→ `CV.Axioms`), `SM.GeoPositiveLift`).
Source: reference/R/CV/d6_vertexedge.tex `lem:pieceintrinsic`, statement 56–74 (EXTRACTS.json segment 1), proof 75–115
(segment 2); consumer `cor:groupedknot` 263–330 (leaf record comparison, clause (B) factor identification).
Binder of the row: `hn : 3 ≤ n`, `hG : CV.Generic P` (printed "Let `P` be generic", d6:58), `S ∈ Ind hG.crossingGeometry`,
`H : Piece hG.crossingGeometry S`; the bundle is stated on `hD : Diagrammatic P` and the row instantiates it at
`hG.diagrammatic hn` (the `carrierword_generic` pattern). Row 142's objects (`pieceDiagram`, `pieceHomfly`, `pieceWrithe`,
`pieceSupport`, `pieceCarrier`, `PieceDiagramData`) are used exactly as in work/lean/CV/PieceCurve.lean; nothing the sibling
U7c-fix repair changes (`PieceCurveData`) is touched.

## 1. Clause → field map (`CV.PieceIntrinsicData hn hD S H hS`)

| tex lines | printed clause | field | proof |
|---|---|---|---|
| 58–59, 64–66 | "Let `P` be generic, `S ∈ Ind(G_P)`, and let `H` be a residual piece of `S`, carried by the carrier `L` (Lemma lem:carriers (iv))"; "Throughout, that a crossing *lies on* a carrier means that both of its traversal preimages belong to that carrier, which is the condition Lemma lem:carriers (iv) supplies" | `carried`: every `c ∈ H` is in `geoCarrierCrossings S (pieceOwner H)` (unselected, both visits on `L`), and `L = pieceOwner H` is the unique carrier of `S` owning the visits of `H` | `pieceOwner_spec`, `pieceOwner_unique` (CV/CarriersLemma.lean, lem:carriers (iv)), `pieceLabels_subset`, `mem_U_iff` |
| 59–62 | "Let `D_L(H)` be the diagram obtained from `L` by retaining exactly the crossings of `H`, each resolved by the divide convention of Definition def:piecediagram, and erasing all others" | `restriction`: the family `carrierRestriction h`, `h : IsCarrierRestriction K q` (reading R1 below), is nonempty; each member lies inside `L` (`IsCarrierRestriction.owner_eq`), has one component, crossings ≃ `H`, and every crossing positive (`IsPositive` = the divide convention `det(u_over,u_under) > 0`, row 142) | `isCarrierRestriction_pieceSupport`; `carrierword_refines` + `pieceOwner_unique`; `geoCarrierCrossingEquiv` (SM/GeoPositiveLift.lean) + `retained`; `geoPositiveLift_isPositive` |
| 62–64 | "and let `D_P(H)` be the intrinsic piece diagram of that definition, obtained from the parent polygon `P` by retaining exactly the same crossings under the same convention" | `intrinsic`: `pieceDiagram hn hD hS H` has one component, crossings ≃ `H`, all positive, and is itself a member of the family (`K = pieceSupport`, `q = pieceCarrier`, `carrierRestriction … = pieceDiagram` by `rfl`) | row 142 lemmas `pieceDiagramCrossingEquiv`, `pieceDiagram_isPositive`; `pieceSupport_stepInvariant`, `pieceCarrier_geoCarrierCrossings` |
| 67–69 | "Then the identity map on the visits of `H` is a record isomorphism (Definition def:record) from the record of `D_L(H)` to the record of `D_P(H)`" | `record_iso`: for every member `∃ ι : RecordIso (D_L(H)).record (D_P(H)).record, ∀ v, pieceVisit (ι.Φ v) = restrictionVisit v` — the marked-point bijection fixes the parent visit (`liftVisit`, "the same point of the plane, reached by the same branch", d6:100–102) | `carrierRestriction_recordIso` ← `exists_recordIso_of_geoCarrierCrossings_eq` (§3 below) |
| 69–70 | "Consequently they present the same oriented link (Axiom ax:gausscode)" | `same_link`: `homfly (D_L(H)) = homfly (D_P(H))` — the F4 replacement of row 163 (`CV.gausscode_polynomial`, CV/Axioms.lean: link equivalence is out of scope; every consumer reads the polynomial) | `gausscode_polynomial _ _ rfl rfl ι` |
| 72 | "`P_{D_L(H)} = P_H`" | `polynomial`: `homfly (D_L(H)) = pieceHomfly hn hD hS H` (`pieceHomfly = homfly (pieceDiagram)`, row 142) | same |
| 72 | "`w(D_L(H)) = |H|`" | `writhe`: `(D_L(H)).writhe = (pieceLabels H).card ∧ … = pieceWrithe H` | `geoPositiveLift_writhe` + `retained` |

The proof's three paragraphs are the four general lemmas of §4–§5 of the file (not fields): *same double points* (76–82)
`liftVisitEquiv`; *same over/under and signs* (84–90) `overBit_eq_true_iff_parent`, `geoPositiveLift_sign`; *same cyclic
order* (92–96) `visitBetween_iff_key`; *the isomorphism* (98–108) `exists_recordIso_of_geoCarrierCrossings_eq` via the accepted
`CV.recordIsoOfData` (row 140: clauses (a)–(d) ⇒ SM `RecordIso`). The closing remark (110–114, "the two records are not
equal") is respected: the row asserts a `RecordIso`, never an equality of records.

## 2. Readings (recorded for the review; DECISION_FINAL.md §2 reading (ii) throughout)

R1. **`D_L(H)` is a family, quantified universally.** Under reading (ii) "erasing" a double point of `L` means smoothing it
into the carrier of `H` (Step 5 of lem:piececurve, d1:639–653), so `D_L(H)` is the positive lift of a carrier `q` of
`S ∪ K`, `K` the erased double points. `IsCarrierRestriction K q := StepInvariant S H K ∧ geoCarrierCrossings (S ∪ K) q = H`
(`StepInvariant`, CV/PieceCurve.lean §3: `K ⊆ U(S)`, `K ∩ H = ∅`, `S ∪ K ∈ Ind(G_P)` — the printed "erasing all others"
performed as lem:piececurve performs it). The text names one `D_L(H)` but fixes neither the order of erasures nor the terminal
set, and the lemma's content is precisely that the result does not depend on them; the fields therefore hold for *every*
member. Every member lies inside `L` (`owner_eq`: lem:carrierword's refinement clause, row 137, field `refinement`), and
`D_P(H)` is itself a member (`pieceSupport`, `pieceCarrier`). Not a narrowing: the printed object is an instance of the family;
not a strengthening beyond the printed content, since "the" diagram must be well defined for the sentence to mean anything.

R2. **`D_P(H) = pieceDiagram H`** (row 142, reading (ii) of DECISION_FINAL): the intrinsic piece diagram is the positive lift of
the piece curve `C_H`. The row does not introduce a second "parent-curve" object.

R3. **"the identity map on the visits of `H`"** is rendered as `pieceVisit (ι.Φ v) = restrictionVisit v`, where `liftVisit`
sends an occurrence of the lift of a carrier `q` (a double point of the corner polygon of `q` with one of its two strands) to
the parent visit `w : Visit P` whose crossing is the retained crossing at that double point and whose parent edge carries the
strand (`liftVisit_fst`, `liftVisit_edge`, `dir_liftVisit`: the strand is a positive multiple of `edge P w.2`). Both records'
marked points are thereby identified with the visits of `H` (`liftVisitEquiv`), and `ι.Φ` is the identity on them.

R4. **"present the same oriented link (Axiom ax:gausscode)"** = the F4 replacement of row 163 (`homfly D = homfly D'` from a
`RecordIso` of one-component diagrams). Link equivalence is neither assumed nor claimed (CV/Axioms.lean docstring; OPEN_WORK).

R5. **Binder.** The row is on the printed `hG : CV.Generic P` (d6:58) through `hG.diagrammatic hn`; the bundle and all
supporting lemmas are on `hD : Diagrammatic P` (tier 1, `CarrierGeometry.ofDiagrammatic hD`), where rows 142/143 live. `hn : 3 ≤ n`
is reading (iii) (needed by the positive lift and by `three_le_geoCornerCount`).

R6. **`w(D_L(H)) = |H|`** is stated both as `(pieceLabels H).card` (the printed `|H|`) and as `pieceWrithe H` (row 139's name
for it), definitional.

## 3. The general theorem and its proof (file §1–§5)

`CV.exists_recordIso_of_geoCarrierCrossings_eq (hn) (hG : CarrierGeometry P) (hT : GeoIndependent hG.cg T) (hT') (q) (q')
(h : geoCarrierCrossings T q = geoCarrierCrossings T' q') : ∃ ι : RecordIso (geoPositiveLift q).record (geoPositiveLift q').record,
∀ v, liftVisit' (ι.Φ v) = liftVisit v` — two carriers of two independent sets with the same retained crossings have
record-isomorphic positive lifts by the identity on parent visits (standard axioms only). This is also the "block record"
lemma cb:products (row 102, work/drafts/cb/Statements_B.lean's planned `positiveLift_record_iso`) needs; it is stated for
arbitrary retained sets, not only pieces.

* §1 (pure): `cycBetween` transports along a map preserving/reflecting `<`; a step-increasing sequence is strictly increasing
  below `N`; cyclic betweenness of three positions is invariant under rotating the cut (`rotate_cyc_iff`, omega).
* §2 (tier 0, lem:carrierword): the traced mark list `geoComponentMarkList q` (Γ-sorted, `geoComponentMarkList_getElem_successor`)
  is `ρ_T^i` of its head (`markList_getElem_pow`), `ρ_T^N` fixes the head (`markList_pow_length`, `markList_pow`), and the
  `Γ`-keys are strictly increasing along it (`markList_key_lt_iff`, from `geoMarkList_sorted` + nodup + `geoMarkKey_injective`).
* §3 (tier 1): the **corner coordinate** `cornerCoord a = k.val + t` of a mark `a = ρ^r c_k` of `q` (block `k` by `geo_mark_block`,
  unique by `geo_block_mark_eq`; `t` the parameter of its point on edge `k` of the corner polygon). `cornerCoord_lt_successor`:
  it increases along `ρ_T` except at the return to `c_0` — inside a block by the increasing parent-edge parameters of
  `geoCornerPolygon_block`, at a block end by `(k+1).val = k.val + 1` and `t < 1` (`geo_block_param_corner`, `3 ≤` corners).
  Hence (`cornerCoord_orbit_lt_iff`) it is strictly increasing along the orbit from `c_0`, and since the Γ-order is the orbit
  order from the list head (§2), the two cyclic orders on the marks of `q` coincide up to a rotation of the cut:
  `cornerCoord_cycBetween_iff_key`.
* §4 (tier 1): `liftVisit` (block parametrisation `geo_edgeSegment_param` + `geo_carrier_crossingPoint_parameters`, corners
  excluded by `geo_carrier_selfIntersection_not_corner`), its crossing, owner, block, parent edge (`GeoBlockInterior.visit_edge`),
  strand direction (`geoCornerPolygon_edge_smul`), coordinate (`cornerCoord_liftVisit`: the shadow's `visitCoord` is the corner
  coordinate of the parent visit), twin (`liftVisit_twin`: the two strands are along the two parent edges, by transversality
  `Shadow.Generic.transverse`), bijectivity (`liftVisitEquiv`).
* §5 (tier 1): over/under `overBit_eq_true_iff_parent` (`Shadow.positiveDiagram_det_pos` + the positive scalars), cyclic order
  `visitBetween_iff_key`; then `IsRecordIsoData` (a) from `visitBetween_iff_key` on both lifts, (b) from `liftVisit_twin`,
  (c) from the bit formula, (d) all signs `+1`; `recordIsoOfData` (CV/RecordHomfly.lean) builds the `RecordIso`.

Library declarations consumed (file:line where relevant): SM/GeoPositiveLift.lean `geoPositiveLift` 527, `geoPositiveLift_isPositive`
548, `geoPositiveLift_sign` 552, `geoPositiveLift_componentCount` 540, `geoPositiveLift_writhe` 720, `geoCarrierCrossingEquiv` 698,
`crossingPoint_geoCarrierCrossingEquiv` 707, `GeoBlockInterior` 129, `GeoBlockInterior.visit_edge` 160, `geoIsCarrierParameter_block`
172, `geo_block_mark_eq` 229, `geo_edgeSegment_param` 241, `geo_mark_block` 285, `geo_block_param_corner` 339; SM/GeoCornerPolygon.lean
`geoCornerPolygon_block` 328, `geoCornerPolygon_edge_smul` 400, `geoCornerPolygon_edge_ne_zero_of_independent` 424,
`three_le_geoCornerCount` 646, `geo_pow_owner` 697, `geoCornerPolygon_apply` 186; SM/GeoCarrierSelfIntersections.lean
`geo_carrier_crossingPoint_parameters` 457, `geo_carrier_selfIntersection_not_corner` 683, `geoCsi_evaluation_start` 99;
SM/GeoCarrierOrder.lean `geoComponentMarkList_getElem_successor` 138, `geoSmoothingSegment_zero` 61; SM/FlatCarriersDefs.lean
`geoMarkKey` 127, `geoMarkList_sorted` 153, `geoComponentMarkList_nodup` 299, `geoOwner_successor` 270, `geoMarkPosition_evaluation_visit`
95; SM/FlatCarriers.lean `geoOwner_geoCornerMark` 4895, `isTrueCorner_geoCornerMark` 4899; SM/GeoCarrierCount.lean `geoMarkKey_visit`
71; SM/LinkPositiveLift.lean `Shadow.positiveDiagram_det_pos` 105; SM/LinkDiagramRecord.lean `Diagram.overBit_eq_true_iff` 472,
`Diagram.twin_overVisit/underVisit` 454/456, `Diagram.eq_or_eq_twin` 431; SM/LinkDiagram.lean `Shadow.crossing_pair_spec` 291,
`Shadow.Generic.transverse` 394, `Diagram.crossingParam_spec` 1416, `Diagram.visit_eq_over_or_under` 613; SM/CarrierVisitTwin.lean
`visitTwin_unique` 60, `visit_eq_or_twin` 47, `visitTwin_ne` 41; CV/RecordHomfly.lean `IsRecordIsoData` 272, `recordIsoOfData` 298,
`carriesDoublePoints_iff` 178, `carriesOverUnder_iff` 205; CV/Axioms.lean `gausscode_polynomial` 260; CV/CarriersLemma.lean
`pieceOwner` 319, `pieceOwner_spec` 322, `pieceOwner_unique` 327, `geoIndependent_of_mem_Ind` 170; CV/CarrierWord.lean
`carrierword_refines` 226; CV/PieceCurve.lean `StepInvariant` 207, `pieceSupport_stepInvariant` 374, `pieceCarrier_geoCarrierCrossings`
379, `pieceSupport_geoIndependent` 347, `pieceDiagram` 571, `pieceHomfly` 577, `pieceDiagramCrossingEquiv` 605,
`pieceDiagram_isPositive` 587; CV/Setup.lean `Generic.diagrammatic` 1636.

## 4. Fidelity risks

1. R1 (the `D_L(H)` family) is the one reading a reviewer must accept; the alternative — fixing a single diagram — would either
   make the row a tautology (`D_L(H) := pieceDiagram`, `RecordIso.refl`) or require a canonical choice the text does not make.
2. "Present the same oriented link" is the F4 polynomial reading (row 163, already accepted with that note); inherited, not new.
3. The row is on the printed `Generic` binder; the bundle on `Diagrammatic`, strictly more general, is the working form (as
   `carrierword` / `carrierword_generic`). No domain change.
4. `hn : 3 ≤ n` is a bundle parameter (reading (iii)); CV fixes `n ≥ 3` globally (d1:932).
5. The proof route differs from the printed one only in mechanism: the printed "same cyclic order" cites lem:carrierword
   directly; here it is lem:carrierword (`TracedSuccessor`, Γ-sortedness) plus the block parametrisation of the corner polygon,
   because the positive lift's record orders occurrences by the corner polygon's own traversal coordinate.
6. The pairing clause (b) is `liftVisit (twin v) = visitTwin (liftVisit v)` — "the pairing is by label in both" (d6:104–105).
7. Signs: both records carry `+1` everywhere (`geoPositiveLift_sign`); the row does not re-derive "the sign is read from the same
   two directions with the orientation" beyond that.

## 5. Open items / notes for the assembler

* Intended home: `work/lean/CV/PieceIntrinsic.lean` (after CV/PieceCurve.lean). §1–§5 are geo-lane material (tier 0/1) and could
  live in an `SM/GeoCarrierRecord.lean` module in namespace `SM.GeoCarrier` (prefix `geo`) per ruling R3; they are placed in
  namespace `CV` here to keep the draft self-contained. `exists_recordIso_of_geoCarrierCrossings_eq` is the lemma cb:products
  (row 102) needs for its block-record clause; recommend porting it to the geo lane rather than duplicating.
* `parentCrossing` was named to avoid `SM.Link.liftCrossing` (SM/Smoothing.lean:3424), which is in the import closure through
  `SM.PolynomialBlock`; `liftVisit` has no clash in work/lean.
* `det_smul_left'`, `det_smul_right'`, `det_self'` duplicate small facts available elsewhere (`SM.det_smul_right`, SM/Segment.lean;
  `det_smul_left`, SM/CS3.lean, not in this file's import closure); drop on porting if the imports allow.
* No declaration of U7c-fix (`cornerPolygon_edge_of_crossingPoint_mem`, `pieceShadow_strand_dir`, `pieceShadow_rotationSystem`,
  `pieceShadowCrossingEquiv_crossingPoint`) is used or re-declared; `liftVisit_exists` overlaps the first in method only.
* Review brief (DECISION_FINAL §4 note, filled in): stated on the printed binder `hG : CV.Generic P` (row) / `hD : Diagrammatic P`
  (bundle); no domain change; carriers, corner polygons, retained crossings are the accepted `SM.GeoCarrier` objects read through
  `hD.crossingGeometry`; `Ind(G_P)` is the accepted `CV.Ind`; ownership of selected visits follows SM conv:selected-visits. The
  reviewer checks each field against its quoted sentence and that `IsCarrierRestriction` is the printed "obtained from `L` by
  retaining exactly the crossings of `H` … and erasing all others" under reading (ii).
