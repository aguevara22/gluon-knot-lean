# PLAN_A — cb:blocks (101) and cb:products (102): maximal reuse of the accepted CV geo objects + `SM.blocks`

Architect A, 2026-09-14. Statements: `work/drafts/cb/Statements_A.lean` (319 lines; `cd work/lean && lake env lean
../drafts/cb/Statements_A.lean` → 0 errors, **1 sorry** = `SM.cb_products`; **`SM.cb_blocks_definition` is PROVED**
from accepted declarations as the statement check; axioms of row 101: propext, Classical.choice, Quot.sound,
SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness — through `homfly`/`P_eq_homfly` in the field `equals_Hplus`, as for def:C).
Sources: reference/SM/sm-3-statesum.tex 4623–4637 (cb:blocks), 4638–4663 (cb:products statement), 4664–4696 (proof);
consumers read for shape only: cb:singleton 4697–4759, thm:C-S7 sm-4-knotlaws.tex:267–330.

## 0. Decision summary

* **Binder**: `{n} [NeZero n] (hn : 3 ≤ n) {P} (hP : SM.Generic P) {S} (hS : IsDecomposition hn hP S)` — the printed
  "generic polygon `P`" is SM def:generic (not `CV.Diagrammatic`/`CV.Generic`), "independent support" is def:decomposition.
  Everything geometric is read at `SM.CB.cg hn hP := generic_crossingGeometry hn hP` (reducible abbrev) through the
  accepted geo layer; on an SM-generic polygon these are def:smoothing's objects (field `carriers`:
  `geoComponentEquivGeneric_owner`, FlatCarriersDefs:683).
* **Blocks = `CV.Piece hc S`** (CV:def:pieces, accepted): the printed object "connected components of `G_P[U(S)]`"
  with `G_P = interlacementGraph hn hP = geometricInterlacementGraph hc` (rfl, GeometricInterlacement:88) and
  `U(S) = CV.U hc S = supportUnselected hn hP S` (`CV.U_eq_generic`, Events:215). Labels `CV.pieceLabels`.
* **Owner** of an undominated crossing: `SM.CB.crossingOwner := CV.pieceOwner hc _ (pieceOf hc S c _)`; the field
  `owner` proves it carries both visits (`CV.pieceOwner_pieceOf`, CarriersLemma:333) and that `c` is a self-crossing of it
  (`geo_unselected_nonneighbor_mem_carrierCrossings`, GeoCarrierCrossings:344). "Both visits on one carrier by
  lem:carriers" = SM lem:carriers (iii) `nonneighbor_visits_together` (CarriersLemma.lean:104) in geo form
  (`CV.carriers.nonadjacent_together`, CV/CarriersLemma:429).
* **`D_A` = `SM.CB.carrierDiagram := geoPositiveLift hn (CarrierGeometry.ofGeneric hn hP) _ q`**, equal to the accepted
  def:positive-lift `positiveLift hn hP S (e q) hS` (`geoPositiveLift_eq_generic`, GeoPositiveLift:820) — the diagram of
  def:C's `cornerHomfly` (CornerStateSum:96). `P_A = SM.P D_A`; `m_A = geoCarrierCrossingCount hc S q`.
  "equal `H_A^+` by lp:core" = the field `equals_Hplus` (`P_eq_homfly`, PolynomialBlock:667 = `lp_core.eq_homfly`).
* **`D_H`**: predicate `IsBlockCarrierDiagram H D` (positive lift of a carrier `q'` of an independent `T ⊇ S` carrying `H`
  with self-crossings exactly `H`); canonical witness `SM.CB.blockDiagram := CV.pieceDiagram` (PieceCurve:571) —
  CV:lem:piececurve's iteration IS the printed greedy construction restricted to the carrier of `H`. `P_H = SM.P D_H`.
* **102 from `SM.blocks`** (MarkedProducts:4947, `implemented`): apply `BlocksData.product` to the abstract one-circle
  record `gaussRecord hc (crossings of A)` (§3 KL0), realizable by `D_A` (KL1), with `C H' := blockDiagram H` supplied
  through KL1 + KL3; the record blocks are the pieces owned by `A` through KL2 + GL.

## 1. Clause map — row 101 (`CbBlocksDefinitionData`, 11 fields, all PROVED)

| printed clause (4625–4637) | field | proof (accepted decl, file:line) |
|---|---|---|
| "its interlacement graph `G_P`" | `interlacement_graph` | `geometricInterlacementGraph_eq_generic` GeometricInterlacement:88; `interlacementGraph_adj` InterlaceSupports:19 (rfl) |
| "`N_G(T)` … union of its graph neighbourhoods" | `neighbourhood` | `CV.mem_N` Events:194 (+ `geometricInterlaces_iff_generic` :84, rfl) |
| eq. cb:undominated `U(S)=V∖(S∪N(S))` | `undominated` | `CV.pieces_definition.undominated_eq` Carriers:781, `CV.U_eq_generic` Events:215, `CV.mem_U` :199 |
| "connected components of `G_P[U(S)]` are its blocks" | `blocks` | `residualGraph` adjacency rfl (Carriers:690); `SimpleGraph.ConnectedComponent.eq` |
| (blocks partition `U(S)`) | `blocks_partition` | `pieceLabels_subset/_nonempty/_disjoint`, `biUnion_pieceLabels` Carriers:735–770 |
| (carriers are def:smoothing's) | `carriers` | `geoComponentEquivGeneric_owner` FlatCarriersDefs:683 |
| "undominated crossing has both visits on one carrier by lem:carriers" | `undominated_one_carrier` | `CV.carriers … .nonadjacent_together` CV/CarriersLemma:429 |
| "that carrier is its owner" | `owner` | `CV.pieceOwner_pieceOf` :333; `geo_unselected_nonneighbor_mem_carrierCrossings` GeoCarrierCrossings:344 |
| "`D_A` the actual positive diagram of a carrier `A`" | `actual_positive_diagram` | `geoPositiveLift_eq_generic` :820, `_isPositive` :548, `_sign` :552, `_writhe_eq_geoCarrierCrossingCount` :725 |
| "`P_A = P_{D_A}`" | `carrier_polynomial` | rfl |
| "equal the corresponding `H_A^+` by lp:core" | `equals_Hplus` | `P_eq_homfly` PolynomialBlock:667; `cornerHomfly` CornerStateSum:96 unfolds to `homfly (positiveLift …)` |

## 2. Clause map — row 102 (`CbProductsData`, 10 fields; proof route in §3)

| printed clause (4640–4648) | field | route |
|---|---|---|
| "Every block `H` has one owner" | `one_owner` | `CV.carriers.piece_carrier` (lem:carriers (iv)); `exists_unique_piece_carrier` CV/CarriersLemma:304 |
| (owner of the block = owner of its labels) | `owner_of_block` | `pieceOwner_pieceOf` + `mem_pieceLabels` (pieceOf c = H) |
| "admits an actual positive carrier diagram `D_H`" | `block_diagram` | T := S ∪ pieceSupport, `pieceSupport_mem_Ind` :343 (→ IsDecomposition via `CV.Ind_eq_generic`), q := pieceCarrier, `pieceCarrier_geoCarrierCrossings` :379, `pieceCarrier_owns` :385; `pieceDiagram` = geoPositiveLift (rfl up to proof irrelevance of `CarrierGeometry`) |
| "with exactly its restricted named cyclic record" | `block_record` | KL1 (D_H), KL3.symm, T1 along KL1 (D_A) |
| "Any other choices produce the same named record" | `record_independent` | KL1 twice |
| "`P_H` independent of the further smoothings" | `polynomial_independent` | `presentations` PolynomialBlock:1177 (= `record_polynomial.P_eq`) |
| "`H` owned by `A`" | `owned_by` | `mem_piecesOn_iff` CV/CarriersLemma:338 |
| eq. cb:product `P_A = ∏ P_H` | `product` | `SM.blocks.product` on `gaussRecord hc (crossings A)` + reindexing (GL, KL2) ; empty case = `no_blocks` |
| eq. cb:product `m_A = ∑|H|` | `count` | `CV.groupedWrithe_eq_card_geoCarrierCrossings` X1:164 (Nat.cast injective); writhe: GeoPositiveLift:725 |
| "no owned blocks: value 1, `m_A = 0`" | `no_blocks` | `biUnion_pieceLabels_piecesOn` X1:140 ⇒ crossings = ∅; `geoPositiveLift_isCrossingFreeCircle` :737; `P_circle` PolynomialBlock:609 (`lp_core.circle`) |

## 3. The chain (new lemmas; namespace `SM.CB`, one module each under work/lean/SM/CB*.lean or SM/CB/*.lean)

Write `hc : CrossingGeometry P`, `T : Finset (Crossing P)`, `L_T := (geometricGaussList hc).filter (fun v => decide (v.1 ∈ T))`.

**KL0 — the abstract restricted Gauss record** (≈ 250 lines; gate for everything else).
```
noncomputable def gaussRecord (hc) (T) : Record          -- comps := Unit; M := {v : Visit P // v.1 ∈ T};
  -- succ := cyclic `List.next` on L_T as a Perm (pattern: geoMarkSuccessor FlatCarriersDefs:187, geoNextMark_eq_list_next :174,
  --   geoMarkSuccessor_sameCycle_getElem :206 for succ_cycle); pair := visitTwin (visitTwin_crossing keeps T);
  -- isOver v := decide (0 < det (edge P v.1.2.val) (edge P (visitTwin v.1).2.val))  (bit_pair: det antisymmetric, ≠ 0 by
  --   CrossingGeometry clause 2 = crossing_det_ne_zero_of_geometry); sgn := 1 (sgn_pair, sgn_ne trivial)
theorem gaussRecord_componentCount (hc T) : (gaussRecord hc T).componentCount = 1
def gaussRecord.crossingEquiv (hc T) : (gaussRecord hc T).Crossing ≃ {c : Crossing P // c ∈ T}      -- p ↦ ⟨p.rep.1.1, _⟩ (Crossing.rep LinkRecordExtras:587)
theorem gaussRecord_isRealizable_iff …   (not needed; realizability comes from KL1)
```
**KL1 — the record of the positive lift of a carrier** (≈ 800–1000 lines; the geometric heart).
```
theorem geoPositiveLift_record_iso (hn) (hG : CarrierGeometry P) {T} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T) :
    Nonempty (RecordIso (geoPositiveLift hn hG hT q).record (gaussRecord hG.cg (geoCarrierCrossings hG.cg T q)))
```
Proof plan. `Φ` : shadow visits `(x, strand j)` of `geoCarrierShadow` ↦ the `Visit P` of `c := geoCarrierCrossingEquiv x`
(GeoPositiveLift:698) whose mark lies in block `j` of the corner polygon (`GeoBlockInterior` :129, `geo_mark_block` :285,
`geo_block_param_corner` :339); the strand `j` is a positive multiple of that visit's original edge
(`geo_carrierCrossing_edges` :621, `geoCornerPolygon_edge_smul` GeoCornerPolygon:400), which gives `pair_eq` (the other strand
↔ the twin) and `bit_eq` (over strand = `det(dir over, dir under) > 0`, `Shadow.positiveDiagram` spec, signs of `det`
invariant under positive scaling); `sgn_eq`: both `1` (`geoPositiveLift_sign` :552, `gaussRecord` sgn); `e := Fin 1 ≃ Unit`.
`succ_eq`: `D.record.succ = D.nextVisit` (LinkDiagramRecord:522, characterised by `nextVisit_no_between` :335 /
`cycNext_unique` :124 on `visitCoord` :181 `= j.val + crossingParam`); show `visitCoord` is strictly monotone in the inherited
mark order of `q` (block index = index of the corner in `geoComponentCornerList`; within a block the parameter increases along
the straight piece, `geo_edgeSegment_param` :241, `geo_edgeInterior_param` :266) and that the inherited order of `q`'s crossing
visits is `L_T`-order: `carrierGaussList_eq_filter` (CV/CarrierWord:176: the visits of `q` in inherited order = `geometricGaussList`
filtered by owner), `mem_geoCarrierCrossings` (GeoCarrierCrossings:91) to drop the selected visits. Both successors are then
"the next element in a key-sorted cyclic list" and `cycNext_unique` identifies them. Template: `singleDiagram_nextVisit`
(LinkDiagramRecord:804) / `record_of_single_polygon` :829 (the same for one generic polygon).
Fallback for `succ_eq`: `TracedSuccessor` + `geoComponentMarkList_getElem_successor` (GeoCarrierOrder:138) to walk `ρ_T` from a
crossing visit to the next crossing visit through the intermediate marks (vertices, selected visits, unselected visits of
other crossings are impossible on the same carrier … only vertices/corners intervene), and the block parametrisation to show
no shadow visit has an intermediate coordinate.

**KL2 — record interlacement = geometric interlacement** (≈ 500–700 lines).
```
theorem gaussRecord_arcBetween_iff (hc T) {v w u : (gaussRecord hc T).M} (hvw : v ≠ w) (hvu : v ≠ u) (hwu : w ≠ u) :
    (gaussRecord hc T).ArcBetween v w u ↔
      traversalBetween (geometricVisitPosition hc v.1) (geometricVisitPosition hc w.1) (geometricVisitPosition hc u.1)
theorem gaussRecord_adj_iff (hc T) (p q : (gaussRecord hc T).Crossing) :
    (gaussRecord hc T).interlacementGraph.Adj p q ↔ GeometricInterlaces hc (crossingEquiv p).1 (crossingEquiv q).1
noncomputable def gaussRecord_graphIso (hc T) :
    (gaussRecord hc T).interlacementGraph ≃g (geometricInterlacementGraph hc).induce (↑T : Set (Crossing P))
```
Proof plan. `steps` (MarkedProducts:160, `ArcBetween` :172) on the one-circle record = index difference mod `|L_T|`
(`steps_eq_mod` :3625, `steps_eq_of_base` :3649; `succ^k` = `List.next` iterated = index shift, as in
`geoMarkSuccessor_sameCycle_getElem`); `L_T` is sorted by `geometricVisitKey` (GeometricVisits:39; `geometricGaussList` is the
key-sorted visit list, `mem_geometricGaussList` :73, `_nodup` :79), so index cyclic betweenness = key cyclic betweenness
(`cycBetween` LinkDiagramRecord:78) = `traversalBetween` of positions. Then `adj_iff_alternates` (:3957) with `Alternates`
(:3896) against `GeometricInterlaces` (GeometricInterlacement:16: `x ≠ y ∧ ∃ x₀ x₁ y₀ y₁, alternating betweenness`) via
`geometric_alternating_visits_iff_unique` (CV/Events:109). Graph iso from `crossingEquiv` (KL0) + `gaussRecord_adj_iff`.

**KL3 — restriction of the abstract record** (≈ 250–350 lines).
```
theorem gaussRecord_restrict_iso (hc) {T' T : Finset (Crossing P)} (h : T' ⊆ T) :
    Nonempty (RecordIso ((gaussRecord hc T).restrictCrossings {p | (crossingEquiv p).1 ∈ T'}) (gaussRecord hc T'))
```
Proof plan. Occurrences `{v // v.1 ∈ T ∧ crossing ∈ T'} ≃ {v // v.1 ∈ T'}`; `succ` of `restrictCrossings` = `firstReturn`
(MarkedProducts:214) of `next_{L_T}` on the retained set = `next_{L_{T'}}` since `L_{T'} = L_T.filter _`
(`List.filter_filter`; `firstReturn_val_eq_of_pow` Stack:207, `firstReturn_pow_val_spec` :243); pairing/bits/signs by
`restrictCrossings_sgn` :232 and the `Subtype` restriction of `pair`.

**GL — the record blocks of a carrier are the pieces it owns** (≈ 200 lines).
```
theorem geoCarrierCrossings_eq_biUnion_piecesOn (hS : S ∈ Ind hc) (q) :
    geoCarrierCrossings hc S q = (piecesOn hc S q).biUnion (pieceLabels hc S)             -- CV.biUnion_pieceLabels_piecesOn X1:140
noncomputable def blockEquiv (hS) (q) :
    ((geometricInterlacementGraph hc).induce ↑(geoCarrierCrossings hc S q)).ConnectedComponent ≃ {H : Piece hc S // H ∈ piecesOn hc S q}
theorem blockEquiv_supp (hS q K) : {c | ∃ x ∈ K.supp, x.1 = c} = ↑(pieceLabels hc S (blockEquiv hS q K).1)
```
Proof plan. `geoCarrierCrossings ⊆ U(S)` (`geoCarrierCrossings_subset_U` GeoCarrierCrossings:593) so a walk in the induced
graph on the carrier's crossings is a walk in `residualGraph hc S` (`SimpleGraph.Walk.map` along the embedding; `ConnectedComponent.lift`);
conversely every vertex of a `residualGraph` walk from a label of `H` is a label of `H` (`SimpleGraph.Walk` induction with
`connectedComponentMk_eq_of_adj`, the pattern of `owner_eq_of_walk` CV/CarriersLemma:277) and `pieceLabels H ⊆ crossings(A)`
for `H ∈ piecesOn q`; the two maps are mutually inverse.

**T1 — transport of `restrictCrossings` and of the interlacement graph along a `RecordIso`** (≈ 150 lines).
```
noncomputable def RecordIso.crossingEquiv (ι : RecordIso ρ ρ') : ρ.Crossing ≃ ρ'.Crossing          -- crossingOf_eq LinkRecord:628 (B2 pattern, MarkedProducts:2600)
noncomputable def RecordIso.restrictCrossings (ι) (T : Set ρ.Crossing) :
    RecordIso (ρ.restrictCrossings T) (ρ'.restrictCrossings (ι.crossingEquiv '' T))
noncomputable def RecordIso.graphIso (ι) : ρ.interlacementGraph ≃g ρ'.interlacementGraph              -- steps/ArcBetween preserved by succ_eq, pair_eq
```

**Assembly of `SM.cb_products`** (≈ 300 lines; `SM/CBProducts.lean`, the row module).
Write `ι_A : RecordIso D_A.record (gaussRecord hc (crossings A))` (KL1 at `hG := CarrierGeometry.ofGeneric hn hP`),
`ι_H : RecordIso D_H.record (gaussRecord hc (pieceLabels H))` (KL1 at `S ∪ pieceSupport`, rewritten by
`pieceCarrier_geoCarrierCrossings`).
* `block_record H` := `ι_H.trans (KL3.symm).trans ((ι_A.restrictCrossings _).symm)` after `blockRecordCrossings = ι_A.crossingEquiv⁻¹ '' {…}`
  (`recordCrossingOf` commutes with `crossingEquiv`, by construction of `Φ` in KL1 — expose `Φ` as a `def` with a
  `geoPositiveLift_recordIso_Φ_crossing` lemma).
* `record_independent` := KL1 for `D`, KL1 for `blockDiagram H`, `trans`/`symm`; `polynomial_independent` := `presentations`.
* `product q`: if `piecesOn q = ∅` use `no_blocks`; else `ρ := gaussRecord hc (crossings A)`,
  `β := (gaussRecord_graphIso …).connectedComponentEquiv.trans (blockEquiv …)` (Mathlib `SimpleGraph.Iso.connectedComponentEquiv`),
  `C K := blockDiagram hn hP hS (β K).1`, `BlockSupply ρ C`: `actual := ⟨D_A, ⟨ι_A⟩⟩`, `one_circle := gaussRecord_componentCount`,
  `nonempty` from a label of some owned piece (`pieceLabels_nonempty`), `supplied K := ι_H.trans (KL3.symm)` with
  `K.supp = {p | (crossingEquiv p).1 ∈ pieceLabels (β K).1}` (GL `blockEquiv_supp`); then
  `SM.blocks.product ρ C supply D_A ⟨ι_A⟩ : SM.P D_A = ∏ K, SM.P (C K)` and `Fintype.prod_equiv β` + `Finset.prod_subtype`
  → `∏ H ∈ piecesOn hc S q, blockPoly H`.
* `count q` := `CV.groupedWrithe_eq_card_geoCarrierCrossings (CV.generic_of_sm hn hP) (mem_Ind hn hP hS) q` (X1:164;
  `groupedWrithe = ∑ pieceWrithe`, `pieceWrithe = card` as ℤ; `Nat.cast_injective`), and `geoPositiveLift_writhe_eq_geoCarrierCrossingCount`.
  (Alternative: `SM.blocks.writhe_additive` + `pieceDiagram_writhe` PieceCurve:596 — printed proof's "Every retained crossing is
  positive and appears once".)
* `no_blocks q` := `biUnion_pieceLabels_piecesOn` ⇒ `geoCarrierCrossings = ∅` ⇒ `geoPositiveLift_isCrossingFreeCircle` ⇒ `P_circle`;
  `carrierCount = 0` by `Finset.card_empty`.

## 4. What 102 needs from mp:blocks and lem:carriers; fidelity readings

* From `SM.blocks` (`BlocksData`, MarkedProducts:335): ONLY `product` (and optionally `writhe_additive`). Its hypotheses
  `BlockSupply` (:245) — `actual` (KL1 gives realizability by `D_A` itself, no clean-join construction), `one_circle`,
  `nonempty` (hence the separate no-block clause, exactly as printed), `supplied` (KL1 + KL3). `realizes`/`sign_preserved` unused.
  The printed proof says "mp:blocks now constructs clean marked joins with the full record of `D_A`"; in the Lean route the
  full record is realized by the actual `D_A` (mp:blocks' `product` quantifies over EVERY actual diagram with the full record),
  which is the MarkedProducts `realizes` reading (root node = the supplied actual diagram).
* From lem:carriers: (iii) both visits of an undominated crossing on one carrier (`nonadjacent_together` / geo :335);
  (iv) noncrossing + connectivity ⇒ one owner per block (`CV.carriers.piece_carrier`, `exists_unique_piece_carrier`);
  "Lemma lem:carriers supplies actual geometric carriers for `S_H`" = the geo carriers of `S ∪ pieceSupport`
  (`pieceSupport_mem_Ind`) and their positive lift (def:positive-lift at tier 1, `CarrierGeometry.ofGeneric`).
* Is the restricted record realizable by an actual diagram? YES, constructively: `CV.pieceDiagram` (the printed "further
  smoothings" = lem:piececurve's iteration `StepInvariant`, PieceCurve:207–297) is an actual positive diagram, and KL1+KL3 give
  its record = `D_A.record.restrictCrossings (H)`. No appeal to mp:blocks' `realizes` or to `isRealizable_restrictCrossings_of_gapContiguous`.
* Readings recorded in the statement file header (R-1…R-6): block = `Piece`; owner defined via `pieceOwner` of the block and
  proved to carry both visits; `D_A` = `geoPositiveLift` with equality to `positiveLift` as a field; "actual positive carrier
  diagram `D_H`" = positive lift of a carrier of an independent refinement `T ⊇ S` with self-crossings exactly `H` (the
  printed `S_H` has `U(S_H) = H`, `pieceSupport` cleans only `H`'s carrier — both satisfy the predicate; the statement never
  needs `U(S_H) = H`); the record clause for the canonical `D_H` plus record-equality for every block carrier diagram;
  `hn : 3 ≤ n` a bundle parameter (as def:C). Candid vocabulary differences: SM "generic polygon" (G1 ∧ G2) vs CV
  "diagrammatic"/"generic" — the CV objects are instantiated at `generic_crossingGeometry hn hP` and, for `pieceDiagram`, at
  `CV.Generic.diagrammatic hn (CV.generic_of_sm hn hP)` (proof-irrelevant in all `geo*`/`CV.Piece` types; compiled); SM
  "actual positive diagram of a carrier" (`positiveLift` on `Component hn hP S`) vs the geo `geoPositiveLift` on `GeoComponent`
  (`geoPositiveLift_eq_generic`); lem:carriers clause numbering differs between SM (iii)/(iv) and CV (iii)/(iv) — cited by name.
* D8 guard: `RecordIso` enters only through `SM.P`/`presentations`; no `LinkEquiv` is concluded from a record isomorphism.

## 5. Effort, units, order, risks

| unit | module | lines | hours | depends on |
|---|---|---|---|---|
| KL0 | SM/CBGaussRecord.lean | 250 | 3 | — |
| KL1 | SM/CBCarrierRecord.lean | 800–1000 | 12–16 | KL0 |
| KL2 | SM/CBRecordInterlacement.lean | 500–700 | 7–9 | KL0 |
| KL3 | SM/CBRecordRestriction.lean | 250–350 | 3–4 | KL0 |
| GL | SM/CBBlockGraph.lean | 200 | 3 | — (CV/X1) |
| T1 | SM/CBRecordIsoTransport.lean | 150 | 2 | — |
| assembly | SM/CBProducts.lean (+ port of Statements_A as SM/CBBlocks.lean) | 300 | 4 | all |

Total ≈ 2,450–2,950 lines, ≈ 34–41 prover agent-hours; KL1 ∥ KL2 ∥ KL3 ∥ GL ∥ T1 after KL0; critical path KL0 → KL1 →
assembly ≈ 20 h. Row 101 is already closed (port `Statements_A.lean` §101 as is).

Risks. (1) KL1 `succ_eq` (shadow `nextVisit` = next carrier crossing-visit in inherited order) is the hardest step — block
parametrisation lemmas exist (GeoPositiveLift §2) but the monotonicity of `visitCoord` along the inherited order must be
assembled; mitigation: the `singleDiagram_nextVisit` template and the `TracedSuccessor` fallback. (2) KL2's `steps`/index
arithmetic is tedious; `steps_eq_mod`/`steps_eq_of_base` reduce it. (3) `SM.blocks` is `implemented` (under review): only its
`product` field is consumed; if `BlockSupply` changes shape the assembly adapts. (4) Proof-irrelevant identifications in
the statements (`ofGeneric` vs `ofDiagrammatic`, `cg` vs `hD.crossingGeometry`) — compiled, must be disclosed to reviewers.
(5) Consumers: cb:singleton needs `product`/`count` at `S` and at `S' = S ∪ {c}` (two instances) plus
`IsBlockCarrierDiagram` for the singleton block with lc:single-crossing — provided; thm:C-S7 needs transport of `Piece`/
`pieceOwner`/`carrierDiagram` along the named map `φ` between `P₋` and `P₊` (`geometricInterlacementTransportIso`,
GeometricInterlacement:80, `visitTransport`) — not in scope here, but every object is stated through `cg`/CV objects, which
transport. (6) Axioms: row 101 depends on `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness` through `homfly` (field
`equals_Hplus`), like def:C; row 102 will add nothing beyond `SM.lp_lm` (through `SM.P`) and `SM.blocks`' axioms.
