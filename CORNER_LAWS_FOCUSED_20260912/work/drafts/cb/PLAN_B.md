# PLAN B — cb:blocks (row 101, DEFINE) and cb:products (row 102, PROVE)

Statement file: work/drafts/cb/Statements_B.lean (compiles, `lake env lean` exit 0; `sorry` only in
`SM.cb_blocks_definition` and `SM.cb_products`). Source: reference/SM/sm-3-statesum.tex 4623–4637 (101),
4638–4651 + proof 4652–4696 (102). Emphasis of this draft: LITERAL fidelity to the printed SM text in SM
vocabulary on the accepted SM Carrier lane (`Component`, `owner`, `carrierCrossings`, `positiveLift`,
`supportUnselected`, `interlacementGraph`), thin SM restatements of the CV pieces, the printed proof's own
route ("further smoothings" = enlarging the support; "record restriction" = `Record.restrictCrossings`).

## 1. Decisions (a)

| printed | Lean (Statements_B.lean) | why |
|---|---|---|
| "generic polygon P", "independent support S" | `hn : 3 ≤ n`, `hP : SM.Generic P`, `hS : IsDecomposition hn hP S` (SM/DecompositionDefinition.lean:15) | 101 says generic; the state sum (def:C) and thm:C-S7 read `P_A`, `m_A` on the SM lane, so the row uses the SM objects, not CV.Diagrammatic/geo copies |
| `G_P`, `N_{G_P}(T)`, `U(S) = V(G_P)∖(S∪N(S))` | `interlacementGraph hn hP` (SM/InterlaceSupports.lean:14), `supportNeighbors` (:49), `supportUnselected` (:60; `supportUnselected_eq` is the printed equation by rfl) | accepted def:interlace objects |
| "connected components of G_P[U(S)] … blocks" | `residualGraph := (interlacementGraph hn hP).induce ↑(supportUnselected …)`, `Block := …ConnectedComponent`, `blockOf`, `blockLabels`, `|H| = (blockLabels H).card` | restated on the SM side word for word; equal to `CV.residualGraph/Piece/pieceLabels` at `generic_crossingGeometry hn hP` (graph: `geometricInterlacementGraph_eq_generic` SM/GeometricInterlacement.lean:40 is rfl; vertex set: `CV.U_eq_generic` CV/Events.lean:215). Bridge `blockEquivPiece` is a plan lemma (§4 L0), not a row clause |
| "both visits on one carrier by lem:carriers; that carrier is its owner" | `crossingOwner c := owner hn hP S (Sum.inr (someVisit c))` + fields `both_visits_one_carrier`, `owner_spec`, `owner_unique` | hypothesis-free definition; the clause is the accepted `carriers_lemma.nonneighbor_visits_together` (SM/CarriersLemma.lean:110) |
| owner of a block, "H owned by A" | `blockOwner H := crossingOwner (blockRep H)`, `blocksOwnedBy A` | 102's "Every block has one owner" makes the choice of label immaterial (field `one_owner`) |
| "D_A the actual positive diagram of a carrier A" | `positiveLift hn hP S A hS` (SM/LinkPositiveLift.lean:596; accepted def:positive-lift row) with field `actual_positive_diagram` (one component, curve = `ccpCornerPolygon`, all crossings positive, writhe = `carrierCrossingCount`) | the accepted construction of a Diagram from a carrier; same object def:C uses (`cornerHomfly`, SM/CornerStateSum.lean:96) |
| `P_A = P_{D_A}`; "equal H_A^+ by lp:core" | `carrierPolynomial := SM.P (positiveLift …)`; field `P_A_eq_cornerHomfly : carrierPolynomial = cornerHomfly ∧ cornerHomfly = homfly (positiveLift …)` | consequence field, proved by `P_eq_homfly` (SM/PolynomialBlock.lean:667) |
| `m_A` | `carrierCrossingCount hn hP S A` (def:smoothing's `m_Q`; writhe of `D_A` by `positiveLift_writhe_eq_carrierCrossingCount` LinkPositiveLift.lean:820) | printed proof: "The self-crossings of a carrier are exactly its owned undominated labels"; thm:C-S7: "writhe m_A … those in the state sum" |
| "its restricted named cyclic record" (of a block H) | `positiveRecord hn hP : Record` (one circle, `M = Visit P`, succ = Gauss successor `gaussSucc = (gaussList hn hP).formPerm` = `nextGaussVisit`, pair = `visitTwin`, bit = `det(d_v, d_twin) > 0`, sgn = +1) restricted by the accepted `Record.restrictCrossings` (SM/MarkedProducts.lean:210) to `recordCrossings (blockLabels H)`: `blockRecord hn hP S H` | reading R-B1 (§3): "the original record restricted to H, with its signs, pairing and over/under choices" (proof 4675–4677); the record of `D_A` is this record restricted to `carrierCrossings A` (lemma L4), so it is also mp:blocks' "`D_A`'s record restricted to H" |
| "actual positive carrier diagram D_H with exactly its restricted named cyclic record" | `∃ T hT (q : Component hn hP T), Nonempty (RecordIso (positiveLift hn hP T q hT).record (blockRecord … H))` (`block_diagram`) | "carrier diagram" = the actual positive diagram of a carrier of some independent support of P; "exactly … record" = def:gauss-record's `RecordIso` (SM/LinkRecord.lean:539), the shape of `BlockSupply.supplied` |
| "P_H … independent of the further smoothings" | `recordPolynomial ρ := P (choose realization)` (proved `recordPolynomial_eq` from `presentations`), `blockPolynomial H := recordPolynomial (blockRecord H)`; fields `P_H_independent`, `P_H_spec` | P_H is a term without choosing a D_H; independence = rp:record-polynomial |
| eq. cb:product | `product`, `crossing_count` (sum over `blocksOwnedBy A`) | literal |
| "With no owned blocks the actual diagram has value 1 and m_A = 0" | `no_owned_blocks` (+ `IsCrossingFreeCircle` conjunct) | literal, plus the reason sentence of the proof |
| proof sentences cited downstream | `block_diagram_support` (S_H ⊇ S, U(S_H) = H, X(q_H) = H), `greedy_independent`, `greedy_step` (eq. cb:greedy-step, cited by cb:singleton 4705–4707), `self_crossings_eq_owned` | marked "(proof)" in the docstrings; cb:singleton consumes cb:greedy-step and the owned-block description |

## 2. What 102 needs from mp:blocks and lem:carriers (b)

* mp:blocks (`SM.blocks : BlocksData`, SM/MarkedProducts.lean:4947, status implemented; `BlocksData.product`
  :342, `writhe_additive` :353): applied with `ρ := R_A := (positiveRecord hn hP).restrictCrossings
  (recordCrossings (carrierCrossings hn hP S A))` (one circle: `componentCount_restrictCrossings` :236 +
  `positiveRecord_componentCount`; actual: L4 gives `IsRealizable R_A` through `D_A`; nonempty M iff
  `carrierCrossings A ≠ ∅`), `C H := D_H` from `block_diagram`. Realizability of the restricted block
  records is NOT taken from mp:blocks' clean-join `realizes` (design D9): the row's `block_diagram` supplies
  the actual `D_H` geometrically (L3 + L4), exactly as the printed proof does ("Lemma lem:carriers supplies
  actual geometric carriers for S_H … its actual positive diagram is a required D_H"), and mp:blocks is
  consumed only for `product` (and, as a cross-check, `writhe_additive`). MarkedProducts' `realizes`
  reading (smoothing away the other blocks inside an actual realization, `isRealizable_restrictCrossings_of_gapContiguous`
  :3443) is the record-level twin of the printed "further smoothings" and is a fallback for L3 (§5).
* lem:carriers (`SM.carriers_lemma`, SM/CarriersLemma.lean:126): (iii) `nonneighbor_visits_together`
  (:110) — the owner clause; (iv) `noncrossing` (:113) in the form `carriers_noncrossing_owner_eq`
  (SM/CarrierNoncrossing.lean:426) — "their alternating four visits cannot lie on two different carriers";
  (i) `inherited_order : InheritsMarkOrder` (:50; def SM/CarrierInheritedOrder.lean:44: `smoothingSuccessor`
  on a carrier = cyclic `next` of its inherited mark list) — "Successor splitting retains the cyclic order
  inherited from the original traversal" (L4); (ii)/(iii) self-intersections — already inside the accepted
  positive lift (`carrierCrossingEquiv`, LinkPositiveLift.lean:799).

## 3. Readings to record before the rows are stated (c)

* **R-B1 (restricted record).** "its restricted named cyclic record" = `positiveRecord hn hP` (P's Gauss
  record with the positive resolution: def:gauss-record on the traversal circle of P; bit `det > 0` as in
  def:positive-lift; all signs +1) restricted by `Record.restrictCrossings` to the crossings of H. The
  printed text names it through `D_A` (mp:blocks) and through "the original record" (proof 4675–4677);
  L4 shows the two agree (`RecordIso`). Consequence: `blockRecord` depends only on `(P, blockLabels H)`, so
  cb:singleton's before/after-split comparison of `P_H` is definitional.
* **R-B2 (carrier diagram).** "an actual positive carrier diagram" = `positiveLift hn hP T q hT` for some
  independent support `T` of the SAME polygon P and carrier `q` of `T`. The `T ⊇ S`, `U(T) = H`,
  `carrierCrossings q = H` of the construction are stated separately (`block_diagram_support`, a proof
  sentence), so `block_diagram` is exactly the printed clause.
* **R-B3 (P_H as a term).** `P_H := recordPolynomial (blockRecord H)` (P of any actual diagram with that
  record; 0 if none). Realizability holds by `block_diagram`; the printed "independent of the further
  smoothings" is the field `P_H_independent` (any two diagrams with the record), `P_H_spec` pins the value.
* **R-B4 (owner definitions).** `crossingOwner` is defined for every crossing through a fixed visit
  (`someVisit`); it is "the owner" only on `U(S)` (`owner_spec`). `blockOwner` through a fixed label
  (`blockRep`, `Quot.exists_rep`); 102's `one_owner` makes it label-independent.
* **R-B5 (proof sentences as fields).** `greedy_independent`, `greedy_step`, `block_diagram_support`,
  `self_crossings_eq_owned` render sentences of the printed PROOF because cb:singleton (4705–4707,
  4711–4716) and thm:C-S7 (sm-4:319: "It transports supports, undominated blocks, owners, actual carrier diagrams and writhes") cite them; each is
  marked "(proof, lines)" in its docstring. `greedy_step` is stated for all `T, c` (a set identity; the
  printed context `T` independent, `c ∈ U(T)` is not needed).
* **R-B6 (SM vs CV blocks).** `Block hn hP S` is a thin SM restatement equal to `CV.Piece
  (generic_crossingGeometry hn hP) S` (L0). Both denote the printed object; no CV import in the SM row.
* Standing readings inherited: CV-DOM (i)–(iii) are not touched (the rows are on SM-generic P and the SM
  Carrier lane); conv:selected-visits fixes ownership of selected visits (irrelevant on U(S)); D9 (marked
  join by record concatenation) is used only through `SM.blocks.product`.

## 4. Chain of lemmas (exact statements; all on `hn : 3 ≤ n`, `hP : Generic P`, `hS : IsDecomposition hn hP S`)

L0 (bridge to CV, acceptance lemma, ≈120 lines, CV-side file): `blockEquivPiece : Block hn hP S ≃
  CV.Piece (generic_crossingGeometry hn hP) S` with `pieceLabels (e H) = blockLabels H`; via
  `SimpleGraph.ConnectedComponent.map` of the graph iso given by `Equiv.setCongr (congrArg (↑) (CV.U_eq_generic hn hP _ S).symm)`
  and `geometricInterlacementGraph_eq_generic`.

L1 (row 101 bundle, ≈200 lines): `neighbors := mem_supportNeighbors` (InterlaceSupports.lean:54);
  `undominated_eq := rfl`; `undominated_iff` from `mem_supportUnselected` (:70); `induced_adj := Iff.rfl`;
  `same_block_iff := SimpleGraph.ConnectedComponent.eq`; `block_labels := mem_blockLabels`;
  `blocks_partition` as CV/Carriers.lean:740–790 (`pieceLabels_nonempty/_disjoint/biUnion_pieceLabels`,
  reproved on `Block`); `both_visits_one_carrier := unselected_nonneighbor_both_visits_one_carrier hn hP hS`
  (SM/CarrierCrossings.lean:433); `owner_spec` from it at `someVisit c`; `owner_unique` trivial;
  `owned_iff_carrierCrossing` from `mem_carrierCrossings` (:66) + `unselected_nonneighbor_exists_unique_carrier`
  (:453) + `carrierCrossings ⊆ U` (the generic twin of `geoCarrierCrossings_subset_U`, SM/GeoCarrierCrossings.lean:593 —
  port or transport by `geoComponentEquivGeneric_owner`, FlatCarriersDefs.lean:683);
  `actual_positive_diagram := ⟨positiveLift_componentCount, positiveLift_comp, positiveLift_isPositive, positiveLift_writhe_eq_carrierCrossingCount⟩`
  (LinkPositiveLift.lean:610–627, 820); `P_A_def := rfl`; `P_A_eq_cornerHomfly := ⟨P_eq_homfly _, rfl⟩`.

L2 (one owner per block, ≈150 lines): `owner_eq_of_interlaces_mem_U : c c' ∈ U(S) → Interlaces c c' →
  crossingOwner c = crossingOwner c'` — the four visits alternate (`Interlaces` def, SM/Interlacement.lean:16)
  and `carriers_noncrossing_owner_eq` (CarrierNoncrossing.lean:426) forbids two owners; then induction on a
  `residualGraph` walk (`SimpleGraph.Walk`), the SM twin of CV/CarriersLemma.lean:258–300 (`owner_eq_of_walk`,
  `owner_eq_of_same_piece`). Gives `one_owner` and `self_crossings_eq_owned` (with L1's `owned_iff_carrierCrossing`),
  `crossing_count` (`Finset.card_biUnion` over disjoint `blockLabels`), `no_owned_blocks`
  (`carrierCrossings A = ∅` → `positiveLift_isCrossingFreeCircle` LinkPositiveLift.lean:833 → `P_circle`
  PolynomialBlock.lean:609; count 0).

L3 (greedy support, ≈300 lines): `greedy_independent := insert_unselected_mem_independentSupports hn hP`
  (CarrierCrossings.lean:399); `greedy_step` by `Finset.ext` + `mem_supportUnselected`, `mem_supportNeighbors`,
  `Finset.mem_insert`; `exists_greedySupport : ∀ H, ∃ T, S ⊆ T ∧ IsDecomposition T ∧ supportUnselected T = blockLabels H`
  by strong induction on `(supportUnselected T \ blockLabels H).card` with the invariant
  `S ⊆ T ∧ IsDecomposition T ∧ blockLabels H ⊆ supportUnselected T ∧ T ∩ blockLabels H = ∅` (a label of H is
  not adjacent to a `c ∈ U(S)∖H`: both in `U(S)`, adjacency would put `c` in `H`, `SimpleGraph.ConnectedComponent.eq`);
  the SM twin of CV/PieceCurve.lean:207–330 (`StepInvariant`, `exists_pieceSupport_aux`, `exists_pieceSupport`),
  run until `U(T) = H` (CV stops when the H-carrier has no other double point; here the printed stopping rule).
  Then `q_H := crossingOwner hn hP T (blockRep H)`; `carrierCrossings hn hP T q_H = blockLabels H`: ⊆ from
  `carrierCrossings ⊆ U(T) = H`; ⊇ since H is connected in `G_P[U(T)] = G_P[H]` (induced subgraph of an
  induced subgraph; `SimpleGraph.induce` monotonicity) and L2 at `T`.

L4 (**carrier record bridge**, the new geometry, ≈1,800–2,500 lines, critical path): for every
  `hT : IsDecomposition hn hP T` and `q : Component hn hP T`,
  `positiveLift_record_iso : Nonempty (RecordIso (positiveLift hn hP T q hT).record
     ((positiveRecord hn hP).restrictCrossings (recordCrossings hn hP (carrierCrossings hn hP T q))))`.
  Construction: `Φ : (carrierShadow …).Visit ≃ {v : Visit P // v.1 ∈ carrierCrossings T q}` — a shadow visit
  `⟨x, s⟩` (crossing `x` at `crossingPoint c`, `c := carrierCrossingEquiv x`, strand `s = (j)` of the corner
  polygon) ↦ the P-visit of `c` on the original edge carrying edge `j` (`mark_block` LinkPositiveLift.lean:676,
  `carrierCrossing_edges` :722, `edgeSegment_param` :353, `block_mark_eq` :339: the strand `j` is the block of
  the outgoing slot of corner `j`, and `crossingPoint c ∈ edgeSegment Q j` iff the visit of `c` on that edge is
  a mark of the block). Fields: `comp_eq` (both one circle: `Fin 1 ≃ Unit`); `pair_eq`: the other strand at `x`
  ↔ `visitTwin` (`Shadow.other`, `visit_crossing_val_eq_pair` CarrierCrossings.lean:216); `bit_eq`: overStrand
  = strand with `det(dir s, dir t) > 0` (`Shadow.positiveDiagram`, LinkPositiveLift.lean:93) and `dir j` is a
  positive multiple of the original edge (`smoothing_corner_directions` SM/CarrierCrossings.lean:323,
  `edgeSegment_param` LinkPositiveLift.lean:353; geo twin `geoCornerPolygon_edge_smul` SM/GeoCornerPolygon.lean:400) ⇒ equal to
  `positiveOverBit`; `sgn_eq`: `positiveLift_sign` (:622) vs `1`; `succ_eq` (the heart): `D.record.succ =
  nextVisit` = cyclic successor by `visitCoord` = `traversalKey (j, t)` (LinkDiagramRecord.lean:181, 258,
  `nextVisit_no_between` :335) ↔ `firstReturn gaussSucc (CrossKeep …)` = next retained visit in
  `gaussList` order (`gaussList_sorted` GaussWord.lean:47, `gauss_next_no_visit_between` GaussCyclicGap.lean).
  Middle term: the order of the marks along the carrier is the inherited one — `InheritsMarkOrder`
  (`carriers_lemma.inherited_order`, CarriersLemma.lean:50; `componentMarkList` CarrierClosedTrace.lean:59 is
  the `filter` of the sorted mark list) and the corner-polygon parameter `(j, t)` is monotone in the block
  position `(j, r)` of a mark (`isCarrierParameter_block` :289, `param_eq_of_corner` :398,
  `edgeInterior_param` :377). Proof strategy: show both successors are "the next element of the same
  cyclic list" — the list of `carrierCrossings`-visits in `componentMarkList` order — via a strictly
  monotone map from list position to `visitCoord` (List.next of a sorted nodup list, cf. MarkedProducts
  `firstReturn_apply`). Corollary `IsRealizable R_q` (`⟨positiveLift …, iso⟩`) and the special case `block_diagram`
  := L3 + L4 at `(T, q_H)` (`carrierCrossings T q_H = blockLabels H` rewrites the restricted set).
  Sanity/acceptance lemmas to demand: `Φ` preserves crossing points; for `S = ∅` the lift of the unique
  carrier has record ≅ `positiveRecord` itself (via `restrictCrossings_univ_iso` MarkedProducts.lean:1754).

L5 (record-level interlacement vs G_P, ≈600–900 lines): `interlaces_positiveRecord_iff : ∀ v w,
  (positiveRecord hn hP).Interlaces (crossingOf v) (crossingOf w) ↔ Interlaces hn hP v.1 w.1` —
  `interlaces_iff_alternates` (MarkedProducts.lean:3941, one-circle) reduces to `Alternates` (:3896) =
  `ArcBetween` via `steps` along `gaussSucc`; `steps` along `(gaussList).formPerm` = cyclic index
  difference in `gaussList` (`List.formPerm_pow_apply_getElem`), and cyclic index order in the sorted
  `gaussList` = `traversalBetween` on `visitPosition` (GaussWord.lean:47, the accepted Gauss-word lemmas of
  SM/GaussVisits.lean). Then restriction invariance: for `x, y ∈ T`, `(ρ.restrictCrossings T).Interlaces x' y'
  ↔ ρ.Interlaces x y` (`arcBetween_restrictCrossings_succ_iff` :3815, `restrictCrossings_succ_val` :3810 —
  first-return arcs contain the same retained points). Corollary: the connected components of
  `R_A.interlacementGraph` correspond to `blocksOwnedBy A` with `supp ↔ recordCrossings (blockLabels H)`
  (adjacency between crossings of `carrierCrossings A ⊆ U(S)` is G_P adjacency, L2's
  `owner_eq_of_interlaces_mem_U` shows the induced graph on X(A) is a union of blocks of `G_P[U(S)]`).

L6 (restriction of a restriction, record level, ≈100 lines): for `T' ⊆ T`,
  `restrictCrossings_restrictCrossings_iso : Nonempty (RecordIso ((ρ.restrictCrossings T).restrictCrossings T'')
   (ρ.restrictCrossings T'))` (`T''` the preimage) — `Equiv.subtypeSubtypeEquivSubtype`,
  `restrictCrossings_firstReturn_val` (MarkedProducts.lean:3429), as in `isRealizable_restrictCrossings_of_gapContiguous`'s
  final `of_iso` (:3500–3512).

L7 (assembly of `product`, ≈200 lines): `carrierCrossings A = ∅` → `no_owned_blocks` case (product over ∅ = 1).
  Else `BlockSupply R_A C` with `actual := (L4).of_iso`, `one_circle`, `nonempty`, `supplied H' := (block_diagram
  (H ↔ H')).trans (L6)`; `SM.blocks.product R_A C hsup (positiveLift …) ⟨L4⟩ : P D_A = ∏ H', P (C H')`;
  reindex `∏` over `R_A.interlacementGraph.ConnectedComponent ≃ blocksOwnedBy A` (L5) and rewrite each factor
  by `P_H_spec` (`recordPolynomial_eq`). `P_H_independent := presentations` (PolynomialBlock.lean:1177, or
  `record_polynomial.P_eq` :1108); `P_H_spec := (recordPolynomial_eq _ _ h).symm`.

Row 102 = L1–L7; row 101 = L1 (+ L0 for the review). Both rows on the accepted library only; no new
axiom; the mp:blocks row (implemented, under review) is consumed through its statement `SM.blocks`.

## 5. Effort and order

| unit | lines | agent-h | depends on |
|---|---|---|---|
| L1 (101 bundle) | 200 | 2 | — |
| L2 (owners, count, empty case) | 250 | 3 | L1 |
| L3 (greedy support S_H) | 300 | 3 | L1, L2 |
| L4 (carrier record bridge) | 1,800–2,500 | 14–20 | — (independent; start first) |
| L5 (record ↔ G_P interlacement) | 600–900 | 5–7 | — |
| L6 (restriction of restriction) | 100 | 1 | — |
| L7 (assembly + product) | 200 | 2 | all |
| L0 (CV bridge, acceptance lemma) | 120 | 1 | — |
Total ≈ 3,600–4,600 lines, ≈ 31–39 agent-hours; critical path L4 (≈ 2 days wall-clock with one prover);
L1–L3, L5, L6 in parallel lanes. Fallback if L4 stalls: state and prove everything except `block_diagram`,
`block_diagram_support`(record part) and `product`, and deliver the record-level twin of `block_diagram`
(`∃ D : Diagram, (∀ x, D.IsPositive x) ∧ RecordIso D.record (blockRecord H)`) from
`isRealizable_restrictCrossings_of_gapContiguous` + `restrictCrossings_join_decomp` (MarkedProducts.lean:3443,
4651; needs `IsRealizable R_A`, i.e. L4 again for A — so the fallback still needs L4 at the single carrier A;
no route avoids the bridge, because every product/record clause compares a carrier's diagram with P's record).

## 6. Risks

1. **New geometry cost (L4).** The carrier record bridge (shadow visits of `positiveLift` ↔ P-visits, with the
   inherited cyclic order = corner-polygon parameter order) has no accepted precedent; ≈ 2k lines on the
   generic lane. It is also what cb:singleton (P_H before/after a split) and thm:C-S7 (transport of blocks,
   owners, actual carrier diagrams) will consume, so it is not sunk cost. Mitigation: prove it once on the
   generic lane; the geo lane inherits it through `geoPositiveLift_eq_generic` (SM/GeoPositiveLift.lean:820)
   if CV consumers (`CV.pieceDiagram`, CV/PieceCurve.lean:571) need it.
2. **Reading R-B1** (restricted record = P's positive record restricted) may be judged a deviation from
   mp:blocks' "record of D_A restricted"; L4 makes the two `RecordIso`, and the docstring cites 4675–4677.
   A reviewer may prefer the D_A form; the alternative (`(positiveLift … A).record.restrictCrossings (image of H)`)
   is a one-definition change in the statement, at the price of making cb:singleton's before/after comparison
   need L4 explicitly.
3. **Proof sentences as fields (R-B5).** `block_diagram_support`, `greedy_*`, `self_crossings_eq_owned` are
   stronger than the printed statement; provable, but a "one field per printed clause" lens may ask to move
   them to a companion lemma. They are cited by cb:singleton (eq. cb:greedy-step) — keep, or split into
   `CbProductsProofData` if the review demands.
4. **Definitions fixed by choice** (`someVisit`, `blockRep`, `recordPolynomial`): each is pinned by a field
   (`owner_spec`, `one_owner`, `P_H_spec`); reviewers must check that no clause depends on the choice.
5. **mp:blocks status.** `SM.blocks` is implemented, not accepted; row 102 cannot be accepted before mp:blocks
   is (its `realizes` clause is the D9 sub-obligation; 102 uses only `product`).
6. **Scope note.** cb:products is off the GAP-2 chain (no thm:floor); cb:singleton (its consumer) is blocked by
   GAP-2 (AUTHOR_NOTES D-F3), so 102 is deliverable and accepted independently, but its consumers stay open.
7. **`hn`/`NeZero`**: the bundles carry `[NeZero n]` from the Carrier lane; `hn : 3 ≤ n` is a parameter as in
   every accepted Chapter-3 row.
