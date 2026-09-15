# Row 158 — CV:cor:groupedknot — report

Prover: Claude Code subagent of the pod executor, 2026-09-14. Source: reference/R/CV/d6_vertexedge.tex,
`cor:groupedknot`, statement lines 263–298 (clause (A) 265–288, clause (B) 289–296; EXTRACTS.json segment
263–298), printed proof 299–439. Draft: `work/drafts/cvdom/CVGroupedKnot.lean` (939 lines). Compile:
`cd work/lean && lake env lean ../drafts/cvdom/CVGroupedKnot.lean` → exit 0, 0 errors, 0 warnings. No
incomplete proofs, no placeholder tactic anywhere in the file (grep count 0). Nothing under work/lean was
written or read-modified.

Row declaration: `CV.groupedknot (hn : 3 ≤ n) (hG : CV.Generic P) (hS : S ∈ Ind hG.crossingGeometry)
(q : GeoComponent hG.crossingGeometry S) : CV.GroupedKnotData hn hG hS q`, Prop bundle `CV.GroupedKnotData`,
one field per printed clause (docstrings quote the clause with d6 line numbers).

Axioms (`#print axioms` on a /tmp copy with the three lines appended):
```
'CV.groupedknot' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]
'CV.liftRestrictRecordIso' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.arcBetween_iff_visitBetween' depends on axioms: [propext, Classical.choice, Quot.sound]
```
The three literature interfaces enter only through `homfly` / `SM.P` / mp:blocks (`SM.blocks`), exactly as in
the accepted rows CV:lem:homflyrows (157), CV:ax:homfly (160), cb:blocks (101). No new axiom.

**cb:products (row 102) is NOT used and NOT needed.** Every clause is proved from accepted rows on the CV
lane's printed binder (`hG : CV.Generic P`); `SM.cb_products` is stated on `SM.Generic`/`IsDecomposition` and
would not even cover the CV domain. The record-restriction chain that the cb lane builds for row 102 (its
units KL1–KL3, T1, GL) is here rebuilt directly on the accepted geo layer from lem:pieceintrinsic's tools
(§2–§4 of the file); the cb drafts were consulted for shape only (nothing copied; the drafts are on the SM
lane and are not accepted).

## 0. Binder and objects

* Binder: `hn : 3 ≤ n`, `hG : CV.Generic P`, `hS : S ∈ Ind hG.crossingGeometry`, `q : GeoComponent … S`
  (the carrier `L`). The corollary does not restate its polygon hypothesis; clause (B) is about def:X1's
  `P_{S,L}`, `w_{S,L}` (row 146, `groupedPoly hn hG hS q`, `groupedWrithe hG q`, defined for `hG : Generic P`,
  d1:909 "Let `P` be generic"), and lem:pieceintrinsic (row 156, its factor identification) is "Let `P` be
  generic" (d6:58). So the row is stated on `Generic P`; the working theorems of §1–§5 are on
  `hD : Diagrammatic P` (§4–§5) or tier 1 `hG : CarrierGeometry P` (§1–§4), read at `hG.diagrammatic hn`
  (reading (iii): `hn` enters through `pieceDiagram hn`, `geoPositiveLift hn`).
* `W` = `CV.groupedLabels hG q := (piecesOn hG.crossingGeometry S q).biUnion (pieceLabels …)` (d6:267–271,
  "the union of their label sets — a set of crossing labels").
* `D(W)` = `CV.carrierDiagram hn hG hS q := geoPositiveLift hn (CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn))
  (geoIndependent_of_mem_Ind _ hS) q` — the positive lift (U4, SM/GeoPositiveLift.lean:527) of the carrier
  `q`. Reading (ii): "retaining exactly the labels of `W`, each resolved by the divide convention, and erasing
  all others" performs no erasing because `W` is already the whole self-crossing set of `L`
  (`groupedLabels_eq` = `biUnion_pieceLabels_piecesOn`, CV/X1.lean:140, lem:piececurve Step 2 as the text
  says, d6:271–272); the divide convention is `Diagram.IsPositive` (`geoPositiveLift_isPositive`).
* `ρ` = `(carrierDiagram …).record`; its interlacement-graph blocks `K` are indexed to the pieces on `L` by
  `CV.blockEquiv` (§4), `K.supp = liftBlock … (pieceLabels (blockEquiv K).1)` (`supp_eq_liftBlock`).
* Leaves `D(W_i)`: any `C : blocks → Diagram` with `CV.IsPieceLeafFamily hn hD hS q C`, i.e. `(C K).record ≅
  (pieceDiagram hn hD hS (blockPiece K)).record`. The canonical family is `K ↦ pieceDiagram (blockPiece K)`
  (`isPieceLeafFamily_pieceDiagram`); every `D_L(H_i)` of lem:pieceintrinsic (`carrierRestriction h`) is a
  member by the accepted `carrierRestriction_recordIso` (CV/PieceIntrinsic.lean:939).

## 1. Clause → field map (`CV.GroupedKnotData hn hG hS q`)

| printed clause (d6 lines) | field | Lean content | proof (accepted rows / new lemmas) |
|---|---|---|---|
| (A) "Let `S ∈ Ind(G_P)`, let `L` be a carrier of `S` bearing at least one residual piece, and let `W = ⋃{H …}` be the union of their label sets … By Lemma lem:piececurve Step 2, `W` is exactly the set of self-crossings of `L`" (265–272) | `label_union` | `groupedLabels hG q = geoCarrierCrossings hG.crossingGeometry S q ∧ ∀ x, GeoIsSelfIntersection … q x ↔ ∃ c ∈ groupedLabels hG q, x = crossingPoint c` | `biUnion_pieceLabels_piecesOn` (CV/X1.lean:140); `geo_self_intersections` (SM/GeoCarrierSelfIntersections.lean:763, clause 1) |
| (A) "so the diagram `D(W)` obtained from `L` by retaining exactly the labels of `W`, each resolved by the divide convention, and erasing all others, is `L` itself carrying all of its own crossings; no realization argument is needed" (272–275) | `retain_all` | `componentCount = 1 ∧ Nonempty (Γ.Crossing ≃ {c // c ∈ W}) ∧ (∀ x, IsPositive x) ∧ ∀ i, (Γ.comp i).P = geoCornerPolygon … q` | `geoPositiveLift_componentCount` (:540, rfl), `geoCarrierCrossingEquiv` (:698), `geoPositiveLift_isPositive` (:548), `geoPositiveLift_comp` (:543, rfl) |
| (A) "Let `W = W₁ ⊔ ⋯ ⊔ W_k`, `k ≥ 1`, be the partition of `W` into the connected components of the interlacement graph induced on `W`; these are the label sets of the residual pieces" (275–277) | `partition` | labels of the pieces on `L` nonempty, `PairwiseDisjoint`, union `= W`; `∃ β : ((geometricInterlacementGraph …).induce ↑W).ConnectedComponent ≃ {H // H ∈ piecesOn … q}, ∀ K c, c ∈ K.supp ↔ c.1 ∈ pieceLabels (β K).1` | `pieceLabels_nonempty` (CV/Carriers.lean:735), `piecesOn_pairwiseDisjoint` (X1:159), rfl; new `exists_inducedComponentEquiv` (file:580; via `labelGraphIso` :562, `blockEquiv` :529, Mathlib `Iso.connectedComponentEquiv`, `ConnectedComponent.map_mk`, `Iso.reachable_iff`) |
| (A) "The components can be indexed and equipped with a fixed ordered binary parenthesization `𝓣` such that `D(W) ≅ #_𝓣(D(W₁), …, D(W_k))` … Here `#_𝓣` is evaluated recursively: a leaf has value `D(W_i)` and an internal node has the connected sum of its two ordered child values" (277–282, 285–287) | `tree` | `(∀ K, K.supp = liftBlock … (pieceLabels (blockEquiv … K).1)) ∧ ∀ C, IsPieceLeafFamily … C → (piecesOn … q).Nonempty → ∃ J, JoinForest C Set.univ J ∧ Nonempty (RecordIso J.record (carrierDiagram …).record)` | new `supp_eq_liftBlock` (:555); `SM.blocks.realizes` (SM/MarkedProducts.lean:4947/4848) through new `blockSupply` (:665) |
| (A) "`P_{D(W)} = ∏_{i=1}^{k} P_{D(W_i)}`" (283) | `product` | `(∀ C, IsPieceLeafFamily … C → Nonempty → homfly D(W) = ∏ K, homfly (C K)) ∧ (Nonempty → homfly D(W) = ∏ H ∈ piecesOn … q, pieceHomfly hn (hG.diagrammatic hn) hS H)` | `SM.blocks.product` (:4865), `P_eq_homfly` (SM/PolynomialBlock.lean:667), `Finset.prod_nbij` with `blockPiece` (new :457, `_mem` :476, `_injective` :508, `_surj` :518) |
| (A) "In particular, when `k = 1`, `#_𝓣(D(W₁)) = D(W₁)`" (287–288) | `single` | `∀ H, piecesOn … q = {H} → Nonempty (RecordIso D(W).record (pieceDiagram … H).record) ∧ homfly D(W) = pieceHomfly … H` | new `recordIso_pieceDiagram_of_single` (:741) from `exists_recordIso_of_geoCarrierCrossings_eq` (CV/PieceIntrinsic.lean:823); `gausscode_polynomial` (CV/Axioms.lean:260) |
| (B) "Let `S ∈ Ind(G_P)` and let `L` be a carrier of `S` bearing the residual pieces `H₁, …, H_k` with `k ≥ 1` … Then the diagram obtained from `L` by retaining exactly the crossings of `H₁ ∪ ⋯ ∪ H_k` is a knot diagram" (289–294) | `knot_diagram` | `(piecesOn … q).Nonempty → componentCount = 1 ∧ Nonempty (Γ.Crossing ≃ {c // c ∈ W})` | as `retain_all` |
| (B) "whose HOMFLY polynomial is `P_{S,L} = ∏_i P_{H_i}`" (294–295) | `grouped_polynomial` | `Nonempty → homfly D(W) = groupedPoly hn hG hS q ∧ groupedPoly … = ∏ H ∈ piecesOn … q, pieceHomfly …` | new `homfly_eq_prod_pieceHomfly` (:709); def:X1 `groupedPoly` (rfl) |
| (B) "whose writhe is `w_{S,L} = Σ_i |H_i|`" (295) | `grouped_writhe` | `Nonempty → D(W).writhe = groupedWrithe hG q ∧ groupedWrithe hG q = ∑ H ∈ piecesOn … q, ((pieceLabels … H).card : ℤ)` | `groupedWrithe_eq_card_geoCarrierCrossings` (X1:164), `geoPositiveLift_writhe` (:720); `groupedWrithe`/`pieceWrithe` unfold (rfl) |
| (B) "and whose underlying plane curve is `L`" (295–296) | `underlying_curve` | `∀ i : Fin 1, (D(W).Γ.comp i).P = geoCornerPolygon hG.crossingGeometry S q` | `geoPositiveLift_comp` (rfl) |
| (B) "which has no triple points" (296) | `no_triple_points` | `(∀ x, ¬ GeoIsTriplePoint … q x) ∧ ¬ ∃ s t u : Γ.Strand, … (interior s ∩ interior t ∩ interior u).Nonempty` | `geo_carrier_no_triple_point` (SM/GeoCarrierSelfIntersections.lean:570, lem:carriers (iii)); `(geoCarrierShadow_generic …).no_triple` (:511) |
| (B) parenthetical "(If `L` bears no piece the assertion is Theorem thm:carrierfloor (D): `P_{S,L} = 1`, `w_{S,L} = 0`, and there is nothing to decompose.)" (290–293) | `no_piece` | `piecesOn … q = ∅ → groupedPoly … = 1 ∧ groupedWrithe … = 0 ∧ D(W).IsCrossingFreeCircle ∧ homfly D(W) = 1` | `groupedPoly_of_piecesOn_eq_empty`, `groupedWrithe_of_piecesOn_eq_empty` (X1:111/115), `geoPositiveLift_isCrossingFreeCircle` (:737), `homfly_circle` (SM/LinkInterfaces.lean:386) |

Not rendered: the printed proof's `sign_preserved` content ("every old crossing is present once, with its old
sign") is not a clause of the corollary (it is a clause of mp:blocks and available as
`SM.blocks.sign_preserved` for every `JoinForest` produced by `tree`). The remark `rem:connectedsumscope`
following the corollary is not part of the row.

## 2. Readings (recorded for the review; DECISION_FINAL.md §2 reading (ii) throughout)

R1. **`D(W)` and the (B) diagram are the positive lift of the carrier.** "Retaining … each resolved by the
divide convention, and erasing all others" is read exactly as in rows 142/156 (def:piecediagram's divide
convention = `Diagram.IsPositive`, erasing = smoothing into a carrier); since `W` is the full self-crossing
set of `L` (the text's own observation, d6:271–275, `biUnion_pieceLabels_piecesOn`), nothing is erased and the
diagram is `geoPositiveLift` of `L`. This is the same object cb:blocks calls `D_A` on the SM lane
(`positiveLift`; agreement `geoPositiveLift_eq_generic`, SM/GeoPositiveLift.lean:820).

R2. **"`≅`" and "`#_𝓣`" (D9).** `D(W) ≅ #_𝓣(D(W₁),…,D(W_k))` is rendered as mp:blocks' `realizes`: a diagram
`J` built from the leaves by a `JoinForest` (each internal node an actual clean marked join
`IsCleanMarkedJoin`, SM/MarkedProducts.lean:95 — lem:homflyrows (i)'s `K # J` at marked representatives;
the well-definedness of `#` on classes is not claimed, design decision D9), with a named record isomorphism
`RecordIso J.record (D(W)).record` — the hypothesis of CV:ax:gausscode (row 163, F4: "present the same
oriented link" is only claimed as its polynomial consequence). The tree `𝓣`, its leaf indexing and the marked
intervals are those the printed proof constructs existentially ("can be indexed and equipped with a fixed
ordered binary parenthesization"); the row asserts existence, as printed. The printed proof's specific
closed-block tree (gap lemma, innermost block) is mp:blocks' proof (`exists_block_gap`,
`restrictCrossings_join_decomp`), not re-proved here.

R3. **"`D(W_i)`" = any leaf family record-isomorphic to the intrinsic piece diagrams.** The text's `D(W_i)`
("the diagram of `L` with only the crossings of `W_i` retained") is lem:pieceintrinsic's `D_L(H_i)`
(`carrierRestriction`, any admissible erasing route), which row 156 proves record-isomorphic to
`D_P(H_i) = pieceDiagram H_i`. The fields `tree` and `product` quantify over every `IsPieceLeafFamily`, so
they hold for the `D_L(H_i)` (take `C K := carrierRestriction h_{(β K).1}`, `hC K` from
`carrierRestriction_recordIso`) and for the `D_P(H_i)` (canonical instance, `isPieceLeafFamily_pieceDiagram`).
The displayed `∏ P_{D(W_i)}` is then the printed `∏ P_{H_i}` (second conjunct of `product`, field
`grouped_polynomial`), which is the factor identification the text stresses (d6:410–424: "a product of the
`P_{H_i}` and not of some other family").

R4. **The blocks.** "The connected components of the interlacement graph induced on `W`" is read on
`G_P = geometricInterlacementGraph` (CV:def:interlace) induced on `↑W` (field `partition`, graph-level,
Mathlib `SimpleGraph.induce`), and, for mp:blocks, on the record interlacement graph of `D(W)`
(`Record.interlacementGraph`, chords alternating in the record's cyclic order). The two are the same graph
through the labels: `adj_iff_geometricInterlaces` (file :387) — the record's arc order is the traversal order
(`arcBetween_iff_visitBetween`, :103), which is the parent's cyclic order of the parent visits
(`visitBetween_iff_key`, row 156's lem:carrierword consequence). `k ≥ 1` is `(piecesOn … q).Nonempty`; the
graph-level and record-level bijections do not need it, the `JoinForest`/product fields carry it (mp:blocks
needs a nonempty crossing set).

R5. **"knot diagram", "underlying plane curve is `L`", "no triple points".** `componentCount = 1`; the one
component's polygon is `geoCornerPolygon` (the carrier as a closed polygon, def:flat-carriers, the CV carrier
of def:smoothing read on the accepted geo layer per DECISION_FINAL §2); "no triple points" is stated for `L`
(`¬ GeoIsTriplePoint`, lem:carriers (iii) at tier 1) and for the shadow of `D(W)` (`Shadow.Generic.no_triple`).

R6. **The parenthetical of (B)** cites thm:carrierfloor (D) (row pending). It is a remark, not an assertion of
the corollary; it is rendered (`no_piece`) and proved from def:X1's empty conventions (row 146) and the
crossing-free lift + ax:homfly's `P_○ = 1`, so no dependence on carrierfloor is introduced.

R7. **`hn : 3 ≤ n`** (reading (iii)) is carried by `pieceDiagram hn`/`geoPositiveLift hn`; the graph-level
statement `exists_inducedComponentEquiv` also takes `hn` and `hT` (it is proved through the lift) — a proof
artefact, harmless for the row.

## 3. The new general theorems (file §1–§5) and the lemmas they use

* §1 `arcBetween_iff_visitBetween (D) (hD : D.componentCount = 1) (v w u)` (:103): `D.record.ArcBetween v w u ↔
  D.VisitBetween v w u`. From `exists_ent`/`visitSucc_pow_ent`/`ent_add_sub`/`visitBetween_ent_iff`
  (SM/LinkDiagramRecord.lean:926/937/953/960) and `steps_eq_mod` (SM/MarkedProducts.lean:3625). New; nothing
  of this shape existed (the cb lane's KL2 proves the analogue for its abstract Gauss record instead).
* §2 `liftLabel`, `liftBlock`, `crossKeep_liftBlock_iff` (:162–222): chord labels of the lift's record and the
  restricted set; `arcBetween_iff_key` (:222) = §1 + `visitBetween_iff_key` (CV/PieceIntrinsic.lean:777).
  `liftRestrictRecordIso hn hG hT hT' q q' hsub : RecordIso (geoPositiveLift q').record
  ((geoPositiveLift q).record.restrictCrossings (liftBlock (geoCarrierCrossings T' q')))` (:310) for
  `geoCarrierCrossings T' q' ⊆ geoCarrierCrossings T q` — successor by `cycNext_unique_on`
  (SM/LinkDiagramRecord.lean:102) against `restrictCrossings_succ_val_eq_iff` (:4346) and
  `not_arcBetween_firstReturn` (:3796); pairing by `liftVisit_twin` (:666); bits by `overBit_eq_true_iff_parent`
  (:766); signs by `geoPositiveLift_sign` (:552). Generalises row 156's `exists_recordIso_of_geoCarrierCrossings_eq`
  (equal crossing sets) to a restriction.
* §3 `adj_iff_geometricInterlaces` (:387): record adjacency of two chords ↔ `GeometricInterlaces` of their
  labels; through `adj_iff_alternates` (:3957), `Record.Alternates` (:3896), `geometricInterlaces_iff_unique`
  (CV/Events.lean:136) and the two-visit `Xor` lemma `crossing_existsUnique_iff_xor` (:347; `crossing_unique_visit_iff`,
  `crossing_visits_exhaust`, SM/CrossingPair.lean:34/17).
* §4 `blockPiece`, `blockEquiv` (:457/:529), `supp_eq_liftBlock` (:555), `labelGraphIso` (:562),
  `exists_inducedComponentEquiv` (:580): walk-lifting via `mem_pieceLabels_of_interlaces`
  (CV/PieceCurve.lean:157), `pieceLabels_subset_geoCarrierCrossings` (:417, from `mem_piecesOn`),
  `mem_piecesOn_iff`/`pieceOwner_pieceOf` (CV/CarriersLemma.lean:338/333), Mathlib `ConnectedComponent.lift/
  ind/ind₂/sound/exact/connectedComponentMk_eq_of_adj/mem_supp_iff`.
* §5 `pieceDiagram_recordIso_restrict` (:614): `(pieceDiagram (blockPiece K)).record ≅ ρ.restrictCrossings K.supp`
  (§2 at `T' = S ∪ pieceSupport`, `q' = pieceCarrier`, `pieceCarrier_geoCarrierCrossings` CV/PieceCurve.lean:424);
  `blockSupply` (:665) = `BlockSupply ρ C` (SM/MarkedProducts.lean:245: `isRealizable_record`, one circle,
  nonempty via `liftVisit_surjective`, `supplied` by `RecordIso.trans`); `exists_joinForest` (:688),
  `homfly_eq_prod_leaves` (:698), `homfly_eq_prod_pieceHomfly` (:709), `writhe_eq_sum_leaves` (:730) from
  `SM.blocks` (:4947); `recordIso_pieceDiagram_of_single` (:741).

## 4. Fidelity risks

1. **"`≅`" is a record isomorphism, not link equivalence** (F4, as in rows 156/163). The row claims the
   isomorphism of records with an actual clean-marked-join diagram `J` and the polynomial identity; "present
   the same oriented link" is not claimed. Same status as CV:ax:gausscode's replacement; the review should
   cite F4.
2. **The tree is existential and D9-shaped.** The printed proof builds one specific `𝓣` (closed-block tree)
   with specific clean join arcs; the row asserts the existence of a `JoinForest` with any marked intervals
   (mp:blocks' `realizes`). This is the printed statement's quantifier ("can be indexed and equipped with a
   fixed …"), but the reviewer should note the ordered-binary-tree structure is carried by `JoinForest`
   (leaf / join of two disjoint sub-forests) and not by an explicit tree datatype.
3. **Leaf family quantification.** `tree`/`product` are stated for every `IsPieceLeafFamily`; the printed
   `D(W_i)` is one such family (R3). Stronger than the letter, as `PieceIntrinsicData.restriction` was.
4. **Graph-level partition through the lift.** `exists_inducedComponentEquiv` is proved via the record graph
   of the lift (hence carries `hn`, `hT`); a direct graph-theoretic proof would be lane-free. No effect on the
   row (binder already has `hn`).
5. **`k ≥ 1`.** Placed as the hypothesis `(piecesOn … q).Nonempty` of the fields that need it (`tree.2`,
   `product`, and all of (B) except `underlying_curve`/`no_triple_points`, which hold unconditionally and are
   stated so). Clause (A)'s label-set and partition fields hold without it (trivially for `k = 0`); the
   printed (A) is stated for "at least one residual piece" — the Lean fields are therefore slightly stronger
   in those two places (harmless).
6. **Diagrammatic vs generic binder.** The row is on `hG : Generic P` (def:X1's `P_{S,L}`); §1–§5 hold on
   `Diagrammatic`/tier 1. If a reviewer prefers the row on `Diagrammatic` for clause (A), `GroupedKnotData` can
   be split; (B) genuinely needs def:X1's binder.
7. **The `no_piece` field** cites def:X1 and ax:homfly, not thm:carrierfloor (R6); this is an over-delivery of
   the parenthetical and should not be read as a proof of carrierfloor (D).
8. **Same-domain note** (DECISION_FINAL §4 template) applies: carriers and their crossings are the accepted
   `SM.GeoCarrier` objects read through `hG.crossingGeometry`; the ownership convention at selected crossings
   is SM conv:selected-visits.

## 5. Open items / notes for the assembler

* Port target: `work/lean/CV/GroupedKnot.lean` (imports `CV.X1`, `CV.PieceIntrinsic`, `CV.HomflyRows`);
  add only the header line. Names: `CV.groupedknot`, `CV.GroupedKnotData`, `CV.carrierDiagram`,
  `CV.groupedLabels`, `CV.blockPiece`, `CV.blockEquiv`, `CV.liftLabel`, `CV.liftBlock`,
  `CV.liftRestrictRecordIso`, `CV.arcBetween_iff_visitBetween`, `CV.adj_iff_geometricInterlaces`,
  `CV.IsPieceLeafFamily`, `CV.blockSupply`, … (full list: 53 declarations, `grep -nE "^(theorem|def|…)"`).
  Name check against work/lean: no `CV.*` collision; `SM.Link.Diagram.restrictRecordIso` and an `RProof`
  `existsUnique_iff_xor` exist with different namespaces (mine were renamed `liftRestrictRecordIso`,
  `crossing_existsUnique_iff_xor` to avoid confusion).
* Consumers: Bridge:B4 `pointwise` needs `∏_H P_H = homfly (positiveLift L)` at SM-generic `P`; this row gives
  `homfly (carrierDiagram hn hG hS q) = groupedPoly hn hG hS q` on the CV lane, and `carrierDiagram` is
  `geoPositiveLift`, which agrees with the accepted `positiveLift` by `geoPositiveLift_eq_generic`
  (SM/GeoPositiveLift.lean:820). So B4's `groupedPoly_eq_homfly_positiveLift` (DECISION_FINAL §5 U6) can be
  closed from this row without cb:products. R:exterior (168) waits for this row (DECISION_FINAL §6 item 4).
* `SM.blocks.sign_preserved` is available for any `J` from `tree`; not a clause, not stated.
* The general lemmas of §1–§3 (`arcBetween_iff_visitBetween`, `liftRestrictRecordIso`, `adj_iff_geometricInterlaces`)
  are lane-free / tier-1 and could serve the cb lane's row 102 on `SM.Generic` through
  `geoPositiveLift_eq_generic` if that lane prefers accepted inputs.
* Compile time ≈ 20 s against the compiled library (no `lake build` run; `lake env lean` only).
