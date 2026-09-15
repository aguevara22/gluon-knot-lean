# PLAN_FINAL — cb:blocks (row 101) and cb:products (row 102): judge's decision and synthesis

Judge, 2026-09-14. Inputs: PLAN_A.md / Statements_A.lean (Architect A: accepted CV geo objects + `SM.blocks`),
PLAN_B.md / Statements_B.lean (Architect B: literal SM Carrier lane, own `Block`/`positiveRecord`). Both compile
(A: 1 sorry, row 101 proved; B: 2 sorries). Printed text: reference/SM/sm-3-statesum.tex 4623–4637 (cb:blocks),
4638–4651 (cb:products), proof 4652–4696; consumers cb:singleton 4697–4759, thm:C-S7 sm-4-knotlaws.tex:267–330.

Deliverables (all under work/drafts/cb/, checked with `cd work/lean && lake env lean <file>`):
* **Statements_FINAL.lean** (363 lines): 0 errors, exactly two `sorry` = `SM.cb_blocks_definition`,
  `SM.cb_products`; `SM.cb_blocks_definition_check` proves the row-101 bundle from accepted declarations
  (sorry-free); `recordPolynomial_eq` sorry-free.
* **Skeleton_FINAL.lean** (609 lines): the same definitions and bundles (byte-identical), 14 sorried chain leaves
  (units KL0, KL1, KL2, KL3, T1, GL, AS), the PC leaf PROVED from CV:lem:piececurve, all glue proved, both row
  theorems assembled (`cb_blocks_definition` leaf-free; `cb_products` from the leaves), companion lemmas
  `SM.greedy_independent`, `SM.greedy_step` (eq. cb:greedy-step, for cb:singleton) proved.

## 1. Decision: **winner A**, with three grafts from B

| criterion | A | B | why |
|---|---|---|---|
| FIDELITY | 8 | 7 | Both render every printed clause. A: blocks ARE the accepted CV:def:pieces object (the printed "connected components of `G_P[U(S)]`" is CV's definition verbatim); `N_G(T)` for every `T` (B only at `S`); `one_owner` as `∃!` (literal "has one owner"); `P_H` = polynomial of a diagram. A's deviations: `D_A` defined as `geoPositiveLift` with equality to `positiveLift` as a field (R-3), owner of a crossing defined via `pieceOwner` of its block (definition through lem:carriers (iv), pinned to the printed meaning only by a field), `blockDiagram := CV.pieceDiagram` puts an UNACCEPTED definition (rows 142/143 under review) into the statement. B's deviations: a hand-built `positiveRecord` (P's Gauss record read positively) is a new statement-level construction not pinned by any field; four fields render PROOF sentences (R-B5); `Block`/`blockLabels` duplicate the accepted `CV.Piece`; `neighbors` only at `T = S`. |
| FEASIBILITY | 8 | 6 | Same heart (the carrier record bridge), but A proves it where the tools are: the geo lane has the accepted `carrierGaussList_eq_filter` / `CV.carrierword.carrier_word` (inherited order = P's Gauss list filtered — the combinatorial half of the bridge), `pieceCarrier_gaussWord`, GeoPositiveLift §2 block parametrisation, `TracedSuccessor`; A ≈ 2.5–3k lines vs B ≈ 3.6–4.6k (B rebuilds L0 bridge, L2 owners-by-walk, L3 greedy support, L5 on the SM lane — all of which exist on the CV lane: `owner_eq_of_walk`, `pieceSupport`/`StepInvariant`, `biUnion_pieceLabels_piecesOn`). `SM.blocks` is now ACCEPTED (04:54Z), so both plans' "mp:blocks under review" risk is gone. |
| REUSE | 9 | 6 | A consumes accepted rows CV:def:pieces, CV:lem:carriers (pieceOwner, piecesOn, exists_unique_piece_carrier), CV:def:X1's lemmas (`biUnion_pieceLabels_piecesOn`, `groupedWrithe_eq_card`), `geoPositiveLift_eq_generic`, `SM.blocks`. Its objects are the ones the chamber-transport machinery already moves (CV/ChamberInvII: `pieceEquiv`, `homfly_geoPositiveLift_eq_of_mem_chamber`) — what thm:C-S7's "It transports supports, undominated blocks, owners, actual carrier diagrams and writhes" will need. A's KL1+KL3 also deliver `pieceHomfly_eq_of_pieceLabels_eq`, the one open lemma of CV:prop:chamberinv(ii) (`PieceHomflyTransported`, U5a REPORT §6). B's `Block` needs the L0 bridge before any CV consumer can use it. |

Grafts from B (each removes an A deviation at zero proof cost):
1. **Owner of a crossing** defined literally: `crossingOwner c := owner hn hP S (Sum.inr (someVisit c))` (the carrier
   of either visit, SM `owner` of def:smoothing), pinned on `U(S)` by `crossing_owner` (B's `owner_spec`).
2. **`D_A` IS the accepted `positiveLift hn hP S A hS`** and carriers are `Component hn hP S` (def:smoothing) — the
   objects of def:C / thm:C-S7 / cb:singleton; no geo alias, no equality field. The CV block objects (`Piece`,
   `pieceLabels`, `pieceOwner`, `piecesOn`) are joined to the SM carriers by the accepted `geoComponentEquivGeneric`
   (`geoComponentEquivGeneric_owner` is `rfl`, `geoCarrierCrossings_eq_generic`).
3. **`P_H := recordPolynomial (blockRecord H)`** (B's device, sorry-free `recordPolynomial_eq` from lc:presentations),
   pinned by `polynomial_independent`; `D_H` existential (`block_diagram : ∃ D, IsBlockCarrierDiagram H D ∧ RecordIso …`).
   So `CV.pieceDiagram` (rows 142/143, still `implemented`) appears only in the PROOF (PC leaf), never in the statement.
Rejected from B: `positiveRecord` (R-B1 — the restricted record is D_{A_H}'s record restricted, mp:blocks' phrase;
the "original record restricted" reading is `RecordIso` to it by KL1+KL3), the proof-sentence fields (R-B5 — moved to
companion lemmas `greedy_independent`, `greedy_step`), the SM `Block` restatement (R-B6 — duplicates CV:def:pieces).

## 2. Clause map — row 101 `CbBlocksDefinitionData hn hP hS` (10 fields, all PROVED in `cb_blocks_definition_check`)

| printed clause (4625–4637) | field | proof (accepted) |
|---|---|---|
| "its interlacement graph `G_P`" | `interlacement_graph` | `geometricInterlacementGraph_eq_generic` (bridge), `interlacementGraph_adj` (rfl) |
| "`N_G(T)` … union of its graph neighbourhoods" (∀ T) | `neighbourhood` | `mem_supportNeighbors`; bridge `CV.N_eq_generic` |
| eq. cb:undominated `U(S) = V∖(S∪N(S))` | `undominated` | `supportUnselected_eq` (rfl), `mem_supportUnselected`; bridge `CV.U_eq_generic` |
| "connected components of `G_P[U(S)]` are its blocks" | `blocks` | `residualGraph` adjacency rfl; `SimpleGraph.ConnectedComponent.eq` |
| (blocks partition `U(S)`) | `blocks_partition` | `pieceLabels_subset/_nonempty/_disjoint`, `biUnion_pieceLabels` (CV:def:pieces) |
| "undominated crossing has both visits on one carrier by lem:carriers" | `undominated_one_carrier` | `unselected_nonneighbor_both_visits_one_carrier` (lem:carriers (iii)) |
| "that carrier is its owner" | `crossing_owner` | same + `mem_carrierCrossings` |
| "`D_A` the actual positive diagram of a carrier `A`" | `actual_positive_diagram` | `positiveLift_componentCount/_isPositive/_sign/_writhe_eq_carrierCrossingCount` |
| "`P_A = P_{D_A}`" | `carrier_polynomial` | rfl |
| "equal the corresponding `H_A^+` by lp:core" | `equals_Hplus` | `P_eq_homfly` (× 2; `cornerHomfly` unfolds to `homfly (positiveLift …)`) |

## 3. Clause map — row 102 `CbProductsData hn hP hS` (7 fields; assembly in Skeleton_FINAL.lean)

| printed clause (4640–4648) | field | route |
|---|---|---|
| "Every block `H` has one owner" | `one_owner` (∃! + owner of each label = `blockOwner H`) | `CV.exists_unique_piece_carrier`, `CV.pieceOwner_spec`, transport by `e` (PROVED in skeleton) |
| "admits an actual positive carrier diagram `D_H` with exactly its restricted named cyclic record" | `block_diagram` | PC (`exists_blockCarrier`, proved from `pieceSupport`/`pieceCarrier`) + `record_iso_blockRecord` (KL1 ×2, KL3, T1, AS) |
| "`P_H` independent of the further smoothings" (+ "Any other choices produce the same named record") | `polynomial_independent` | `record_iso_blockRecord` + `recordPolynomial_eq` (PROVED given the leaves) |
| "`H` owned by `A`" | `owned_by` | `mem_piecesOn` unfolding + `Equiv.eq_symm_apply`; `CV.mem_piecesOn_iff` (PROVED) |
| eq. cb:product `P_A = ∏ P_H` | `product` | `product_of_chain`: `SM.blocks.product` on `ρ := D_A.record` itself (`actual := ⟨D_A, refl⟩`, `one_circle := Fintype.card_fin 1`, `nonempty` from a label of an owned block, `supplied K` from `block_diagram` + `blockRecord_eq_at` + GL's `supp` identity), reindexed by GL's `β` (`Fintype.prod_equiv`, `Finset.prod_coe_sort`); empty case = `no_blocks` (PROVED given the leaves) |
| eq. cb:product `m_A = ∑|H|` | `count` | `carrierCrossings_eq_biUnion` (`biUnion_pieceLabels_piecesOn`, `geoCarrierCrossings_eq_generic`) + `Finset.card_biUnion` (PROVED, leaf-free) |
| "no owned blocks: value 1, `m_A = 0`" | `no_blocks` | `carrierCrossings = ∅` ⇒ `positiveLift_isCrossingFreeCircle` ⇒ `P_circle` (PROVED, leaf-free) |

Note: with `ρ := D_A.record` (not an abstract record) `BlockSupply.actual` is trivial and no realizability argument
is needed anywhere; the abstract `gaussRecord` enters only through KL1/KL3 to compare records of different diagrams.

## 4. The chain — units → leaves → estimated lines (namespace `SM.CB`; one module per unit under work/lean/SM/CB*.lean)

Write `hc := cg hn hP`, `L_T := (geometricGaussList hc).filter (· .1 ∈ T)` (`gaussList hc T`).

* **KL0 — abstract restricted Gauss record** (`SM/CBGaussRecord.lean`, ≈ 250 lines, 3 h). Leaves: `gaussSucc`
  (cyclic `List.next` on `L_T` as a `Perm`; pattern `geoMarkSuccessor`/`geoNextMark_eq_list_next`, FlatCarriersDefs:174–206)
  with spec `gaussSucc_val`; `gaussPair` (= `visitTwinPerm.subtypePerm`, `visitTwin_crossing`) with `gaussPair_val`;
  `gaussRecord`'s laws `succ_cycle` (one cycle: `geoMarkSuccessor_sameCycle_getElem` pattern), `pair_ne` (`visitTwin_ne`),
  `pair_invol` (`visitTwin_involutive`), `bit_pair` (B's `positiveOverBit_twin`, sorry-free in Statements_B.lean:189–206 —
  port verbatim); `label_crossingOf` (`Crossing.rep_mem`, `crossingOf_eq_iff`, both occurrences share the label).
* **KL1 — carrier record bridge** (`SM/CBCarrierRecord.lean`, ≈ 800–1000 lines, 12–16 h; critical path). Leaves:
  `positiveLiftRecordIso hT q : RecordIso (positiveLift hn hP T q hT).record (gaussRecord hc (carrierCrossings hn hP T q))`
  and its spec `positiveLiftRecordIso_val` (the P-visit of a shadow visit `v` is at `carrierCrossingEquiv v.1`).
  Route (prove on `geoPositiveLift` at `CarrierGeometry.ofGeneric`, transfer by `geoPositiveLift_eq_generic`, a literal
  equality): `Φ` : shadow visit `(x, strand j)` ↦ the P-visit of `c := geoCarrierCrossingEquiv x` whose mark lies in corner
  block `j` (`geo_mark_block`, `geo_block_param_corner`, `geo_carrierCrossing_edges`, GeoPositiveLift:285/339/621); `pair_eq`
  (other strand ↔ twin), `bit_eq` (over strand = `det > 0`, `Shadow.positiveDiagram` spec; strand direction is a positive
  multiple of the original edge, `geoCornerPolygon_edge_smul` GeoCornerPolygon:400), `sgn_eq` (`geoPositiveLift_sign` vs 1),
  `comp_eq` (`Fin 1 ≃ Unit`); `succ_eq` — the heart: `D.record.succ = nextVisit` (LinkDiagramRecord:522, characterised by
  `nextVisit_no_between`/`cycNext_unique` on `visitCoord = j + t`) equals `List.next` on `L_{X(q)}`: the carrier's crossing
  visits in inherited order are `carrierGaussList hc T q` = `geometricGaussList` filtered by owner (ACCEPTED
  `carrierGaussList_eq_filter`, CV/CarrierWord:176; `carrier_word` gives `TracedSuccessor`), the selected visits drop out
  (`mem_geoCarrierCrossings`), and `visitCoord` is strictly monotone along the inherited mark order (block index = corner
  index in `geoComponentCornerList`; within a block the parameter grows with the successor iterate `r`,
  `geo_edgeSegment_param`/`geo_edgeInterior_param`/`GeoBlockInterior`). Template: `singleDiagram_nextVisit` /
  `record_of_single_polygon` (LinkDiagramRecord:804/829). Fallback: `TracedSuccessor` + `geoComponentMarkList_getElem_successor`
  (GeoCarrierOrder:138) walking `ρ_T` between consecutive crossing visits. Acceptance checks to demand: `S = ∅` gives the
  record of the single polygon (`record_of_single_polygon`); `Φ` preserves crossing points (`crossingPoint_geoCarrierCrossingEquiv`).
* **KL2 — record interlacement = `Interlaces`** (`SM/CBRecordInterlacement.lean`, ≈ 500–700 lines, 7–9 h). Leaf
  `gaussRecord_adj_iff`. Route: `steps`/`ArcBetween` (MarkedProducts:160/172) on the one-circle record = index difference mod
  `|L_T|` (`steps_eq_mod` :3625, `steps_eq_of_base` :3649); `L_T` is key-sorted (`geometricVisitKey`, `mem_geometricGaussList`,
  `_nodup`), so index cyclic betweenness = `cycBetween` of positions = `traversalBetween`; then `adj_iff_alternates` (:3957) /
  `Alternates` (:3896) against `Interlaces` via `geometric_alternating_visits_iff_unique` (CV/Events:109) and
  `geometricInterlaces_iff_generic`.
* **KL3 — restriction of the abstract record** (`SM/CBRecordRestriction.lean`, ≈ 250–350 lines, 3–4 h). Leaf
  `gaussRecord_restrict_iso (h : T' ⊆ T)`. Route: occurrences `{v // v.1 ∈ T ∧ label ∈ T'} ≃ {v // v.1 ∈ T'}`; `succ` of
  `restrictCrossings` = `firstReturn` (:214) of `next_{L_T}` on the retained set = `next_{L_{T'}}` (`List.filter_filter`,
  `firstReturn_val_eq_of_pow` Stack:207); pairing/bits/signs by `restrictCrossings_sgn` :232 and the `Subtype` restriction.
* **T1 — transport of `restrictCrossings` along a `RecordIso`** (`SM/CBRecordIsoTransport.lean`, ≈ 150 lines, 2 h). Leaf
  `restrictCrossings_iso_of_recordIso ι X X' hX` (occurrence-level condition `crossingOf v ∈ X ↔ crossingOf (Φ v) ∈ X'`);
  pattern `RecordIso.ofOcc` (MarkedProducts U-J4a) with `firstReturn` commuting with `Φ` (`crossingOf_eq` LinkRecord:628).
* **GL — record blocks of `D_A` = blocks owned by `A`** (`SM/CBBlockGraph.lean`, ≈ 250 lines, 3–4 h). Leaf
  `exists_blockGraphEquiv hS A : ∃ β : (D_A.record.interlacementGraph).ConnectedComponent ≃ {H // H ∈ blocksOwnedBy A},
  ∀ K, K.supp = blockRecordCrossings hn hP hS A (β K).1`. Route: KL1's `Φ` + KL2 give `D_A.record.interlacementGraph ≃g
  (geometricInterlacementGraph hc).induce ↑(carrierCrossings A)`; `carrierCrossings A ⊆ U(S)` (`geoCarrierCrossings_subset_U`)
  embeds it in `residualGraph hc S`; a walk from a label of `H` stays in `H` (`owner_eq_of_walk` pattern, CV/CarriersLemma:277)
  and `pieceLabels H ⊆ carrierCrossings A` for `H ∈ piecesOn` (`carrierCrossings_eq_biUnion`, proved); Mathlib
  `SimpleGraph.Iso.connectedComponentEquiv` + `ConnectedComponent.mem_supp_iff`.
* **AS — assembly leaves** (in the row module, ≈ 80 lines, 1 h): `mem_blockRecordCrossings_crossingOf` (both occurrences
  of a shadow crossing have the same `.1`; `crossingOf_eq_iff`), `exists_visit_of_mem_carrierCrossings`
  (`carrierCrossingEquiv.symm` + one strand).
* **PC — the block carrier** (PROVED in the skeleton from CV:lem:piececurve's `pieceSupport`/`pieceCarrier`,
  `pieceSupport_mem_Ind`, `pieceCarrier_geoCarrierCrossings`, `geoCarrierCrossings_eq_generic`; 12 lines). Rows 142/143 are
  `implemented`, not yet accepted: if their acceptance stalls, replace by PLAN_B §4 L3 (greedy support on the SM lane,
  ≈ 300 lines: `insert_unselected_mem_independentSupports`, `greedy_step`, strong induction on `|U(T) ∖ H|`).
* **Assembly** (`SM/CBBlocks.lean` = Statements_FINAL defs + row 101; `SM/CBProducts.lean` = glue + row 102 + companion
  lemmas): already written in Skeleton_FINAL.lean (≈ 250 lines), compiles against the leaves.

Totals ≈ 2,300–2,800 new lines, ≈ 32–40 prover agent-hours. Order: KL0 first (gate); then KL1 ∥ KL2 ∥ KL3 ∥ T1 ∥ GL(needs
KL1 spec + KL2) ∥ AS. Critical path KL0 → KL1 → GL → assembly ≈ 20 h serial. Row 101 can be ported and reviewed NOW
(`cb_blocks_definition_check` is its proof).

## 5. Fidelity risks — to be written into AUTHOR_NOTES before the rows are stated

* R-1 SM "block" = accepted `CV.Piece (generic_crossingGeometry hn hP) S` (the printed object; vertex set `CV.U = supportUnselected`
  by `CV.U_eq_generic`, adjacency `Interlaces` by rfl). Bridging conjuncts `CV.N = supportNeighbors`, `CV.U = supportUnselected`,
  `geometricInterlacementGraph = interlacementGraph` sit inside the fields of the clauses they serve (not separate fields).
* R-2 Owner of a crossing DEFINED through a fixed visit (`someVisit`, `Classical.choose`), pinned on `U(S)` by `crossing_owner`;
  owner of a block through the accepted `CV.pieceOwner` (a `Classical.choose` of CV:lem:carriers (iv)) transported by
  `geoComponentEquivGeneric`, pinned by `one_owner`. No clause depends on either choice.
* R-3 Two lanes in one statement: carriers/owner/`D_A`/`m_A` on the SM Carrier lane (`Component`, `owner`, `positiveLift`,
  `carrierCrossingCount`), blocks on the geo layer (`CV.Piece`, `pieceLabels`, `piecesOn`, `pieceOwner`), joined by the accepted
  `geoComponentEquivGeneric` (`e`), which is the identity on owners (`geoComponentEquivGeneric_owner` is `rfl`) and carries
  self-crossings (`geoCarrierCrossings_eq_generic`). `blocksOwnedBy A := CV.piecesOn hc S (e.symm A)`; `blockOwner H := e (pieceOwner H)`.
* R-4 "actual positive carrier diagram `D_H`" = `positiveLift` of a carrier `q` of an independent refinement `T ⊇ S` with
  `carrierCrossings T q = pieceLabels H` (which implies `q` owns both visits of every label). The printed `S_H` has moreover
  `U(S_H) = H`; no clause needs it; the proof's witness (`CV.pieceDiagram`, cleaning only the carrier of `H`) satisfies the predicate.
* R-5 "its restricted named cyclic record" = `Record.restrictCrossings` (mp:blocks, accepted) of the record of the OWNER's actual
  diagram `D_{A_H}` to the chords whose geometric crossing (`carrierCrossingEquiv`) is a label of `H`. The printed proof's "the
  original record restricted to `H`" (P's traversal record) is `RecordIso` to it by KL1 + KL3; B's `positiveRecord` form was not adopted.
* R-6 `P_H := recordPolynomial (blockRecord H)` — `SM.P` of a `Classical.choose`n realization (0 if none); pinned by
  `polynomial_independent` (and realizable by `block_diagram`). The printed "`P_H`, the polynomial of `D_H`" is this common value.
* R-7 `polynomial_independent` asserts, for EVERY block carrier diagram `D` of `H`, both the record clause (`RecordIso D.record
  (blockRecord H)`, the proof's "Any other choices produce the same named record") and `SM.P D = P_H` — stronger than the printed
  statement sentence, which speaks of `P_H` only. `one_owner` asserts `∃!` (existence and uniqueness of the carrier of all visits of all
  labels) plus that it is `blockOwner H` — the printed "one owner" read as "exactly one".
* R-8 `hn : 3 ≤ n`, `[NeZero n]` are bundle parameters (as def:C and every Chapter-3 row); `hS : IsDecomposition hn hP S`
  (= `S ∈ independentSupports hn hP`) is the printed "independent support".
* R-9 Proof sentences are NOT row fields: eq. cb:greedy-step and "the enlarged support is independent" (cited by cb:singleton)
  are companion lemmas `SM.greedy_step`, `SM.greedy_independent` in the row module (proved); "The self-crossings of a carrier are
  exactly its owned undominated labels" is `SM.CB.carrierCrossings_eq_biUnion` (proved).
* R-10 Proof-irrelevant identifications inside the proof (not the statements): `CV.Piece hD.crossingGeometry S` vs
  `CV.Piece (cg hn hP) S` in the PC leaf (`CrossingGeometry P` is a Prop) — compiled; reviewers should be told.
* R-11 Dependencies: row 102's proof (not statement) uses CV:lem:piececurve (row 143, `implemented`) through the PC leaf;
  fallback PLAN_B L3. Axioms: row 101 `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness`
  (through `homfly`/`SM.P` in `equals_Hplus`, as def:C); row 102 adds nothing beyond `SM.blocks`' (`SM.lp_lm`).
* R-12 D8 guard: `RecordIso` enters only through `SM.P`/`presentations`; no `LinkEquiv` is concluded from a record isomorphism.

## 6. Consumers (shape check)

* cb:singleton (4697–4759): needs `product`/`count` at `S` and at `S' = insert c S` (`greedy_independent`), `greedy_step`
  with `N(c) ∩ U(S) = ∅`, the singleton block's diagram (`IsBlockCarrierDiagram {c}` + lc:single-crossing), and `P_H` equal
  before/after the split: `blockPoly_eq_of_labels_eq` — both restricted records are `RecordIso` to `gaussRecord hc (labels)` by
  KL1 + KL3 (state it in KL3's module as a corollary; ≈ 40 lines). Still blocked by GAP-2 (thm:floor) downstream.
* thm:C-S7 (sm-4:267–330): transport of supports, blocks, owners, actual carrier diagrams and writhes along the named map `φ`
  between `P₋` and `P₊` — CV/ChamberInvII.lean already transports `Ind`, `N`, `U`, pieces, `groupedWrithe` and the positive-lift
  HOMFLY along chamber paths on exactly these objects; the SM carriers follow by `e`.
* CV:prop:chamberinv (ii): the open `PieceHomflyTransported` reduces (U5a REPORT §6) to `pieceHomfly … H = pieceHomfly … H'`
  for equal label sets — a corollary of KL1 + KL3 + `P_eq_homfly` (the same `blockPoly_eq_of_labels_eq`). Schedule KL1 with
  that consumer in mind.

## 7. What the executor does next

1. Write R-1…R-12 into work/AUTHOR_NOTES.md; port Statements_FINAL.lean as `SM/CBBlocks.lean` with
   `cb_blocks_definition := cb_blocks_definition_check`'s body; map row 101 (`SM.cb_blocks_definition`), review, accept.
2. Launch KL0; then KL1, KL2, KL3, T1, GL, AS in parallel (leaf statements verbatim from Skeleton_FINAL.lean; provers may
   add lemmas, never change a leaf's statement). PC as in the skeleton (or PLAN_B L3 if rows 142/143 are not accepted by then).
3. Merge into Skeleton_FINAL.lean (its glue and assembly are final), port as `SM/CBProducts.lean`, map row 102
   (`SM.cb_products`), `#print axioms`, review with R-1…R-12 disclosed, accept.
