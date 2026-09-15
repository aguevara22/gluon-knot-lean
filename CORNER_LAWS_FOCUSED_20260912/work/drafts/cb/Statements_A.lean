import CV.X1
import SM.MarkedProducts
import SM.CornerStateSum

/-! # Statements_A — cb:blocks (row 101) and cb:products (row 102) on the accepted geo carrier layer

Architect A (maximal reuse), 2026-09-14. Source: reference/SM/sm-3-statesum.tex, cb:blocks 4623–4637
(DEFINE) and cb:products 4638–4696 (LEMMA; proof 4664–4696). Plan: work/drafts/cb/PLAN_A.md.
Row declarations: `SM.cb_blocks_definition hn hP hS : SM.CbBlocksDefinitionData hn hP hS` and
`SM.cb_products hn hP hS : SM.CbProductsData hn hP hS` (row 101 PROVED from accepted declarations as the
statement check; row 102 `sorry`, its chain is PLAN_A.md §3). Each field of a bundle renders one printed clause
and quotes it. Auxiliary definitions live in `SM.CB` (carrier blocks).

## Binder (as printed)

"Fix a generic polygon `P` … and an independent support `S`": `hn : 3 ≤ n`, `[NeZero n]`,
`hP : SM.Generic P` (def:generic, G1 ∧ G2 — the SM notion, NOT `CV.Generic`), `hS : IsDecomposition hn hP S`
(def:decomposition = `S ∈ independentSupports hn hP` = "`S ∈ Ind(G_P)`"). The rows are SM rows on the SM
binder; the carriers, blocks and owners are read through the accepted geometric carrier layer at
`SM.CB.cg hn hP := generic_crossingGeometry hn hP` (the CV-DOM reading of 2026-09-14: on an SM-generic
polygon the geo objects ARE def:smoothing's, `geoSmoothingSuccessor_eq_generic`, `geoComponentEquivGeneric`,
`geoComponentEquivGeneric_owner`; independence: `CV.Ind_eq_generic`, `geoIndependent_iff_isDecomposition`).

## Notation map (printed → Lean); `hc := SM.CB.cg hn hP`, `e := geoComponentEquivGeneric hn hP S`

* "its interlacement graph `G_P`": the accepted def:interlace `interlacementGraph hn hP` on the vertex set
  `V(G_P) = Crossing P`; `= geometricInterlacementGraph hc` (`geometricInterlacementGraph_eq_generic`, rfl).
* "`N_G(T)`, the union of its graph neighbourhoods": `CV.N hc T` (= `supportNeighbors hn hP T`, `CV.N_eq_generic`).
* eq. cb:undominated "`U(S) = V(G_P) ∖ (S ∪ N_{G_P}(S))`": `CV.U hc S = Finset.univ \ (S ∪ CV.N hc S)`
  (= `supportUnselected hn hP S`, `CV.U_eq_generic`; = `geoSupportUnselected hc S`).
* "`G_P[U(S)]`": `CV.residualGraph hc S = (geometricInterlacementGraph hc).induce ↑(CV.U hc S)`;
  "its blocks", the connected components: `CV.Piece hc S` (Mathlib `SimpleGraph.ConnectedComponent`; the CV
  rows call the same object a "residual piece", CV:def:pieces, accepted); the block of `c ∈ U(S)` is
  `CV.pieceOf hc S c hc'`; the label set of a block `H` ("`|H|`" is its card) is `CV.pieceLabels hc S H`.
* "carrier `A` of `S`": `q : GeoComponent hc S` (the cycles of `ρ_S`; `e q : Component hn hP S` is the accepted
  def:smoothing carrier). "a visit lies on the carrier `A`": `geoOwner hc S (Sum.inr v) = q`.
* "An undominated crossing has both visits on one carrier by Lemma lem:carriers": SM lem:carriers (iii)
  `nonneighbor_visits_together` (`SM.carriers_lemma`), here in its geo form
  `geo_unselected_nonneighbor_both_visits_one_carrier` / `CV.carriers.nonadjacent_together`.
  "that carrier is its owner": `SM.CB.crossingOwner hn hP hS c hc' := CV.pieceOwner hc _ (pieceOf hc S c hc')`,
  the carrier of the block of `c` (lem:carriers (iv), `CV.pieceOwner_spec`); the field `owner` says it is
  the owner of every visit of `c`. "`H` owned by `A`": `H ∈ CV.piecesOn hc S q ↔ CV.pieceOwner hc _ H = q`.
* "`D_A`, the actual positive diagram of a carrier `A`": `SM.CB.carrierDiagram hn hP hS q :=
  geoPositiveLift hn (CarrierGeometry.ofGeneric hn hP) _ q`, which IS the accepted def:positive-lift
  `positiveLift hn hP S (e q) hS` (`geoPositiveLift_eq_generic`) — the diagram of def:C's `cornerHomfly`.
* "`P_A = P_{D_A}`": `SM.CB.carrierPoly hn hP hS q := SM.P (carrierDiagram …)`, `SM.P` the accepted local
  polynomial (lp:core; written `SM.P` because `P` is the polygon). "the corresponding `H_A^+`":
  `cornerHomfly hn hP S (e q) hS = homfly (positiveLift …)` (def:C); "by Theorem lp:core": `lp_core.eq_homfly`.
* "`m_A`" (writhe of `D_A` = number of self-crossings of `A`, def:positive-lift/def:smoothing):
  `SM.CB.carrierCount hn hP q := geoCarrierCrossingCount hc S q` (= `carrierCrossingCount hn hP S (e q)`).
* "an actual positive carrier diagram `D_H`" (cb:products): `SM.CB.IsBlockCarrierDiagram hn hP hS H D` — `D` is
  the positive lift of a carrier `q'` of an independent refinement `T ⊇ S` that carries `H` and whose
  self-crossings are exactly `H` ("Lemma lem:carriers supplies actual geometric carriers for `S_H` …
  No other self-crossing label survives, so its actual positive diagram is a required `D_H`"). The canonical
  witness is `SM.CB.blockDiagram hn hP hS H := CV.pieceDiagram hn _ _ H` (CV:def:piecediagram: the positive
  lift of the carrier of `S ∪ K_H` carrying `H`, `K_H` = the smoothings of CV:lem:piececurve's iteration).
  "`P_H`": `SM.CB.blockPoly hn hP hS H := SM.P (blockDiagram …)`.
* "with exactly its restricted named cyclic record": `Nonempty (RecordIso D_H.record
  (D_A.record.restrictCrossings (blockRecordCrossings … H)))` — `Record.restrictCrossings` (mp:blocks' "restricted
  named cyclic record": same circle, the occurrences of the crossings of `H`, first-return successor, old
  pairing/bits/signs), `blockRecordCrossings … H` the record crossings of `D_A` whose geometric crossing
  (`recordCrossingOf`, through `geoCarrierCrossingEquiv`) lies in `pieceLabels hc S H`.
* "independent of the further smoothings used to produce it": every block carrier diagram of `H` has the same
  named record and the same `SM.P` (rp:record-polynomial / lc:presentations).
* eq. cb:product: `carrierPoly q = ∏ H ∈ piecesOn hc S q, blockPoly H` and
  `carrierCount q = ∑ H ∈ piecesOn hc S q, (pieceLabels hc S H).card`.
* "With no owned blocks the actual diagram has value 1 and `m_A = 0`": `piecesOn hc S q = ∅ →
  D_A.IsCrossingFreeCircle ∧ SM.P D_A = 1 ∧ carrierCount q = 0` (lp:core "`P_○ = 1`"). "No empty link is
  evaluated": `D_A.componentCount = 1` (field `actual_positive_diagram`).

## Readings recorded (fidelity; see PLAN_A.md §4)

R-1 SM vocabulary "block" = CV `Piece` (identical object, printed as "connected components of `G_P[U(S)]`").
R-2 the owner of an undominated crossing is DEFINED through the accepted `pieceOwner` of its block and PROVED
to own both visits (printed order: both visits on one carrier first, then "that carrier is its owner").
R-3 `D_A` is `geoPositiveLift` with the equality to the accepted `positiveLift` as a field.
R-4 "actual positive carrier diagram `D_H`" = positive lift of a carrier of an independent refinement `T ⊇ S`
with self-crossings exactly `H` (the printed proof's `S_H` has moreover `U(S_H) = H`; `pieceSupport` cleans
only the carrier of `H`; both satisfy the predicate). R-5 the record clause is stated for the canonical `D_H`
and record-equality for every block carrier diagram. R-6 `hn : 3 ≤ n` is a bundle parameter (as in def:C). -/

namespace SM

open SM.Carrier SM.GeoCarrier SM.Link

attribute [local instance] Classical.propDecidable

namespace CB

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-- `G_P` read on the geometric record domain: the accepted `generic_crossingGeometry hn hP`
(def:generic ⇒ the geometric record domain, SM/CrossingGeometry.lean). Reducible; every `geo*` object below
is parametrised by this proof, and proof irrelevance identifies it with any other `CrossingGeometry P`. -/
abbrev cg (hn : 3 ≤ n) (hP : Generic P) : CrossingGeometry P := generic_crossingGeometry hn hP

variable (hn : 3 ≤ n) (hP : Generic P) {S : Finset (Crossing P)}

/-- "an independent support `S`" (def:decomposition) is `S ∈ Ind(G_P)` in the accepted CV form
(`CV.Ind_eq_generic`). -/
theorem mem_Ind (hS : IsDecomposition hn hP S) : S ∈ CV.Ind (cg hn hP) := by
  rw [CV.Ind_eq_generic hn hP]
  exact hS

/-- … and geometric independence (def:flat-carriers' `GeoIndependent`, `geoIndependent_iff_isDecomposition`). -/
theorem geoIndependent (hS : IsDecomposition hn hP S) : GeoIndependent (cg hn hP) S :=
  (geoIndependent_iff_isDecomposition hn hP S).mpr hS

/-- The SM-generic polygon is CV-diagrammatic (`CV.generic_of_sm`, `CV.Generic.diagrammatic`): the binder
under which CV:def:piecediagram's block diagram is defined. -/
theorem diagrammatic (hn : 3 ≤ n) (hP : Generic P) : CV.Diagrammatic P :=
  CV.Generic.diagrammatic hn (CV.generic_of_sm hn hP)

/-- **The owner of an undominated crossing** (cb:blocks): the carrier of its block (lem:carriers (iv),
`CV.pieceOwner`). The field `owner` of the bundle says that this is the carrier carrying both visits of `c`. -/
noncomputable def crossingOwner (hS : IsDecomposition hn hP S) (c : Crossing P)
    (hc : c ∈ CV.U (cg hn hP) S) : GeoComponent (cg hn hP) S :=
  CV.pieceOwner (cg hn hP) (mem_Ind hn hP hS) (CV.pieceOf (cg hn hP) S c hc)

/-- **`D_A`, the actual positive diagram of the carrier `A = q`** (def:positive-lift): the positive lift of the
carrier's corner polygon, read on the geo layer (`geoPositiveLift`, tier 1 `CarrierGeometry.ofGeneric`); equal
to the accepted `positiveLift hn hP S (e q) hS` by `geoPositiveLift_eq_generic` (field `actual_positive_diagram`). -/
noncomputable def carrierDiagram (hS : IsDecomposition hn hP S) (q : GeoComponent (cg hn hP) S) : Diagram :=
  geoPositiveLift hn (CarrierGeometry.ofGeneric hn hP) (geoIndependent hn hP hS) q

/-- **`P_A = P_{D_A}`**: the accepted local polynomial `SM.P` (lp:core) of `D_A`. -/
noncomputable def carrierPoly (hS : IsDecomposition hn hP S) (q : GeoComponent (cg hn hP) S) : R :=
  SM.P (carrierDiagram hn hP hS q)

/-- **`m_A`**: the number of self-crossings of the carrier `A` (def:smoothing's `m_Q`, the accepted
`geoCarrierCrossingCount`; the writhe of `D_A` by def:positive-lift). -/
noncomputable def carrierCount (q : GeoComponent (cg hn hP) S) : ℕ :=
  geoCarrierCrossingCount (cg hn hP) S q

/-- **An actual positive carrier diagram of the block `H`** (cb:products): the positive lift of a carrier `q'`
of an independent refinement `T ⊇ S` ("the further smoothings") that carries `H` and whose self-crossings are
exactly the labels of `H` ("No other self-crossing label survives, so its actual positive diagram is a
required `D_H`"). -/
def IsBlockCarrierDiagram (_hS : IsDecomposition hn hP S) (H : CV.Piece (cg hn hP) S) (D : Diagram) :
    Prop :=
  ∃ (T : Finset (Crossing P)) (hT : IsDecomposition hn hP T) (q : GeoComponent (cg hn hP) T),
    S ⊆ T ∧
    geoCarrierCrossings (cg hn hP) T q = CV.pieceLabels (cg hn hP) S H ∧
    (∀ c ∈ CV.pieceLabels (cg hn hP) S H, ∀ v : Visit P, v.1 = c →
      geoOwner (cg hn hP) T (Sum.inr v) = q) ∧
    D = geoPositiveLift hn (CarrierGeometry.ofGeneric hn hP) (geoIndependent hn hP hT) q

/-- **`D_H`**, the canonical block carrier diagram: CV:def:piecediagram's `CV.pieceDiagram` — the positive lift
of the carrier of `S ∪ K_H` carrying `H`, `K_H = CV.pieceSupport` the smoothings of lem:piececurve's iteration
(the printed greedy construction "choose any label `c ∈ U(S) ∖ H` and adjoin it", restricted to the carrier of
`H`). -/
noncomputable def blockDiagram (hS : IsDecomposition hn hP S) (H : CV.Piece (cg hn hP) S) : Diagram :=
  CV.pieceDiagram hn (diagrammatic hn hP) (mem_Ind hn hP hS) H

/-- **`P_H`**: the local polynomial of the canonical block diagram. -/
noncomputable def blockPoly (hS : IsDecomposition hn hP S) (H : CV.Piece (cg hn hP) S) : R :=
  SM.P (blockDiagram hn hP hS H)

/-- The geometric crossing of `P` under a record crossing of `D_A` (any representative occurrence, through the
crossing correspondence `geoCarrierCrossingEquiv` of def:positive-lift). -/
noncomputable def recordCrossingOf (hS : IsDecomposition hn hP S) (q : GeoComponent (cg hn hP) S)
    (p : (carrierDiagram hn hP hS q).record.Crossing) : Crossing P :=
  (geoCarrierCrossingEquiv hn (CarrierGeometry.ofGeneric hn hP) (geoIndependent hn hP hS) q
    ((p.rep : (carrierDiagram hn hP hS q).Γ.Visit).1)).val

/-- The record crossings of `D_A` belonging to the block `H` ("its restricted … record": the crossings of `H`). -/
def blockRecordCrossings (hS : IsDecomposition hn hP S) (q : GeoComponent (cg hn hP) S)
    (H : CV.Piece (cg hn hP) S) : Set (carrierDiagram hn hP hS q).record.Crossing :=
  {p | recordCrossingOf hn hP hS q p ∈ CV.pieceLabels (cg hn hP) S H}

end CB

open CB

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {S : Finset (Crossing P)}

/-- **cb:blocks (sm-3:4623–4637) as printed**, one field per printed clause, on the printed binder
"a generic polygon `P` … an independent support `S`" (`hP : Generic P`, `hS : IsDecomposition hn hP S`).
`hc = cg hn hP`, `e = geoComponentEquivGeneric hn hP S`. -/
structure CbBlocksDefinitionData (hS : IsDecomposition hn hP S) : Prop where
  /-- "Fix a generic polygon `P`, its interlacement graph `G_P`": the graph is def:interlace's
  `interlacementGraph hn hP` (adjacency = `Interlaces`), read on the geometric record domain -/
  interlacement_graph :
    geometricInterlacementGraph (cg hn hP) = interlacementGraph hn hP ∧
    ∀ x y : Crossing P, (interlacementGraph hn hP).Adj x y ↔ Interlaces hn hP x y
  /-- "For a vertex set `T` write `N_G(T)` for the union of its graph neighbourhoods" -/
  neighbourhood : ∀ (T : Finset (Crossing P)) (y : Crossing P),
    y ∈ CV.N (cg hn hP) T ↔ ∃ x ∈ T, Interlaces hn hP y x
  /-- eq. cb:undominated: "`U(S) = V(G_P) ∖ (S ∪ N_{G_P}(S))`" (= def:interlace's `supportUnselected`) -/
  undominated :
    CV.U (cg hn hP) S = Finset.univ \ (S ∪ CV.N (cg hn hP) S) ∧
    CV.U (cg hn hP) S = supportUnselected hn hP S ∧
    ∀ x : Crossing P, x ∈ CV.U (cg hn hP) S ↔ x ∉ S ∧ x ∉ CV.N (cg hn hP) S
  /-- "The connected components of `G_P[U(S)]` are called its *blocks*": `G_P[U(S)]` is the induced subgraph
  on `U(S)` with the adjacency of `G_P`, and two undominated crossings have the same block iff they are joined
  by a path in it -/
  blocks :
    (∀ x y : (↑(CV.U (cg hn hP) S) : Set (Crossing P)),
      (CV.residualGraph (cg hn hP) S).Adj x y ↔ Interlaces hn hP x y) ∧
    ∀ (x y : Crossing P) (hx : x ∈ CV.U (cg hn hP) S) (hy : y ∈ CV.U (cg hn hP) S),
      CV.pieceOf (cg hn hP) S x hx = CV.pieceOf (cg hn hP) S y hy ↔
        (CV.residualGraph (cg hn hP) S).Reachable ⟨x, hx⟩ ⟨y, hy⟩
  /-- … the blocks are nonempty, pairwise disjoint subsets of `U(S)` covering it (a partition, `π₀`) -/
  blocks_partition :
    (∀ H : CV.Piece (cg hn hP) S,
      CV.pieceLabels (cg hn hP) S H ⊆ CV.U (cg hn hP) S ∧ (CV.pieceLabels (cg hn hP) S H).Nonempty) ∧
    (∀ H H' : CV.Piece (cg hn hP) S, H ≠ H' →
      Disjoint (CV.pieceLabels (cg hn hP) S H) (CV.pieceLabels (cg hn hP) S H')) ∧
    (Finset.univ : Finset (CV.Piece (cg hn hP) S)).biUnion (CV.pieceLabels (cg hn hP) S) = CV.U (cg hn hP) S
  /-- the carriers of `S` in this row are def:smoothing's (the geo carriers of the SM-generic `P` are the
  accepted `Component`s, mark by mark) -/
  carriers : ∀ a : Mark P,
    geoComponentEquivGeneric hn hP S (geoOwner (cg hn hP) S a) = owner hn hP S a
  /-- "An undominated crossing has both visits on one carrier by Lemma lem:carriers" -/
  undominated_one_carrier : ∀ c ∈ CV.U (cg hn hP) S, ∀ v w : Visit P, v.1 = c → w.1 = c →
    geoOwner (cg hn hP) S (Sum.inr v) = geoOwner (cg hn hP) S (Sum.inr w)
  /-- "that carrier is its owner": `crossingOwner c` is the carrier of every visit of `c`, and `c` is one of
  its self-crossings -/
  owner : ∀ (c : Crossing P) (hc : c ∈ CV.U (cg hn hP) S),
    (∀ v : Visit P, v.1 = c → geoOwner (cg hn hP) S (Sum.inr v) = crossingOwner hn hP hS c hc) ∧
    c ∈ geoCarrierCrossings (cg hn hP) S (crossingOwner hn hP hS c hc)
  /-- "Write `D_A` for the actual positive diagram of a carrier `A`": `carrierDiagram q` is def:positive-lift's
  `positiveLift` of the carrier `e q` — one component, every crossing positive, writhe `m_A` -/
  actual_positive_diagram : ∀ q : GeoComponent (cg hn hP) S,
    carrierDiagram hn hP hS q = positiveLift hn hP S (geoComponentEquivGeneric hn hP S q) hS ∧
    (carrierDiagram hn hP hS q).componentCount = 1 ∧
    (∀ x, (carrierDiagram hn hP hS q).IsPositive x) ∧
    (∀ x, (carrierDiagram hn hP hS q).sign x = 1) ∧
    (carrierDiagram hn hP hS q).writhe = carrierCount hn hP q
  /-- "and `P_A = P_{D_A}`" -/
  carrier_polynomial : ∀ q : GeoComponent (cg hn hP) S,
    carrierPoly hn hP hS q = SM.P (carrierDiagram hn hP hS q)
  /-- "These polynomials equal the corresponding `H_A^+` by Theorem lp:core": `P_A = H(D_A)` (lp:core
  "It equals `H_D`"), and `H(D_A)` is def:C's `H^+_A = cornerHomfly` -/
  equals_Hplus : ∀ q : GeoComponent (cg hn hP) S,
    carrierPoly hn hP hS q = homfly (carrierDiagram hn hP hS q) ∧
    carrierPoly hn hP hS q = cornerHomfly hn hP S (geoComponentEquivGeneric hn hP S q) hS

/-- **cb:products (sm-3:4638–4663) as printed**, one field per printed clause, on the binder of cb:blocks.
`hc = cg hn hP`, `A_H := pieceOwner hc _ H` the owner of the block `H`. -/
structure CbProductsData (hS : IsDecomposition hn hP S) : Prop where
  /-- "Every block `H` has one owner": exactly one carrier carries both visits of every label of `H` -/
  one_owner : ∀ H : CV.Piece (cg hn hP) S, ∃! q : GeoComponent (cg hn hP) S,
    ∀ c ∈ CV.pieceLabels (cg hn hP) S H, ∀ v : Visit P, v.1 = c →
      geoOwner (cg hn hP) S (Sum.inr v) = q
  /-- … and it is the owner (cb:blocks) of each of its labels -/
  owner_of_block : ∀ (H : CV.Piece (cg hn hP) S) (c : Crossing P) (hc : c ∈ CV.U (cg hn hP) S),
    c ∈ CV.pieceLabels (cg hn hP) S H →
      crossingOwner hn hP hS c hc = CV.pieceOwner (cg hn hP) (mem_Ind hn hP hS) H
  /-- "and admits an actual positive carrier diagram `D_H`": the canonical `blockDiagram H` is one -/
  block_diagram : ∀ H : CV.Piece (cg hn hP) S,
    IsBlockCarrierDiagram hn hP hS H (blockDiagram hn hP hS H)
  /-- "with exactly its restricted named cyclic record": the named record of `D_H` is the record of
  `D_{A_H}` restricted to the crossings of `H` -/
  block_record : ∀ H : CV.Piece (cg hn hP) S,
    Nonempty (RecordIso (blockDiagram hn hP hS H).record
      ((carrierDiagram hn hP hS (CV.pieceOwner (cg hn hP) (mem_Ind hn hP hS) H)).record.restrictCrossings
        (blockRecordCrossings hn hP hS (CV.pieceOwner (cg hn hP) (mem_Ind hn hP hS) H) H)))
  /-- "Any other choices produce the same named record": every block carrier diagram of `H` has the named
  record of `D_H` -/
  record_independent : ∀ (H : CV.Piece (cg hn hP) S) (D : Diagram),
    IsBlockCarrierDiagram hn hP hS H D → Nonempty (RecordIso D.record (blockDiagram hn hP hS H).record)
  /-- "Its polynomial `P_H` is independent of the further smoothings used to produce it" -/
  polynomial_independent : ∀ (H : CV.Piece (cg hn hP) S) (D : Diagram),
    IsBlockCarrierDiagram hn hP hS H D → SM.P D = blockPoly hn hP hS H
  /-- "`H` owned by `A`" spelled out: the blocks owned by the carrier `q` are those whose owner is `q` -/
  owned_by : ∀ (q : GeoComponent (cg hn hP) S) (H : CV.Piece (cg hn hP) S),
    H ∈ CV.piecesOn (cg hn hP) S q ↔ CV.pieceOwner (cg hn hP) (mem_Ind hn hP hS) H = q
  /-- eq. cb:product, first identity: "For every original carrier `A`, `P_A = ∏_{H owned by A} P_H`" -/
  product : ∀ q : GeoComponent (cg hn hP) S,
    carrierPoly hn hP hS q = ∏ H ∈ CV.piecesOn (cg hn hP) S q, blockPoly hn hP hS H
  /-- eq. cb:product, second identity: "`m_A = ∑_{H owned by A} |H|`" (and the same for the writhe of `D_A`) -/
  count : ∀ q : GeoComponent (cg hn hP) S,
    carrierCount hn hP q = ∑ H ∈ CV.piecesOn (cg hn hP) S q, (CV.pieceLabels (cg hn hP) S H).card ∧
    (carrierDiagram hn hP hS q).writhe =
      ∑ H ∈ CV.piecesOn (cg hn hP) S q, ((CV.pieceLabels (cg hn hP) S H).card : ℤ)
  /-- "With no owned blocks the actual diagram has value `1` and `m_A = 0`" (`D_A` is then an actual
  crossing-free one-circle diagram; "No empty link is evaluated") -/
  no_blocks : ∀ q : GeoComponent (cg hn hP) S, CV.piecesOn (cg hn hP) S q = ∅ →
    (carrierDiagram hn hP hS q).IsCrossingFreeCircle ∧
    carrierPoly hn hP hS q = 1 ∧ carrierCount hn hP q = 0

/-- **Row 101, cb:blocks** (DEFINE row), on the printed binder. Every field is an accepted fact; the proof is
written out here as the statement check of the design (Architect A), to be re-verified by the prover unit. -/
theorem cb_blocks_definition (hS : IsDecomposition hn hP S) : CbBlocksDefinitionData hn hP hS where
  interlacement_graph := ⟨geometricInterlacementGraph_eq_generic hn hP _, fun _ _ => Iff.rfl⟩
  neighbourhood T y := CV.mem_N (cg hn hP) T y
  undominated :=
    ⟨(CV.pieces_definition (diagrammatic hn hP) S (mem_Ind hn hP hS)).undominated_eq,
      CV.U_eq_generic hn hP _ S, CV.mem_U (cg hn hP) S⟩
  blocks := ⟨fun _ _ => Iff.rfl, fun _ _ _ _ => SimpleGraph.ConnectedComponent.eq⟩
  blocks_partition :=
    ⟨fun H => ⟨CV.pieceLabels_subset _ S H, CV.pieceLabels_nonempty _ S H⟩,
      CV.pieceLabels_disjoint _ S, CV.biUnion_pieceLabels _ S⟩
  carriers a := geoComponentEquivGeneric_owner hn hP S a
  undominated_one_carrier c hc v w hv hw :=
    (CV.carriers (diagrammatic hn hP) S (mem_Ind hn hP hS)).nonadjacent_together c
      ((CV.mem_U_iff _ S c).mp hc).1 ((CV.mem_U_iff _ S c).mp hc).2 v w hv hw
  owner c hc :=
    ⟨fun v hv => (CV.pieceOwner_pieceOf (cg hn hP) (mem_Ind hn hP hS) hc v hv).symm,
      by
        obtain ⟨i, -, -⟩ := crossing_visits_exist c
        unfold crossingOwner
        rw [CV.pieceOwner_pieceOf (cg hn hP) (mem_Ind hn hP hS) hc ⟨c, i⟩ rfl]
        exact geo_unselected_nonneighbor_mem_carrierCrossings (cg hn hP) (geoIndependent hn hP hS)
          ((mem_geoSupportUnselected_iff _ S c).mpr ((CV.mem_U_iff _ S c).mp hc)) ⟨c, i⟩ rfl⟩
  actual_positive_diagram q :=
    ⟨geoPositiveLift_eq_generic hn hP S _ _ hS q, rfl, geoPositiveLift_isPositive hn _ _ q,
      geoPositiveLift_sign hn _ _ q, geoPositiveLift_writhe_eq_geoCarrierCrossingCount hn _ _ q⟩
  carrier_polynomial _ := rfl
  equals_Hplus q :=
    ⟨P_eq_homfly _, by
      show SM.P (carrierDiagram hn hP hS q) = homfly (positiveLift hn hP S _ hS)
      rw [P_eq_homfly, carrierDiagram, geoPositiveLift_eq_generic hn hP S _ _ hS q]⟩

/-- **Row 102, cb:products** (PROVE row), on the printed binder. -/
theorem cb_products (hS : IsDecomposition hn hP S) : CbProductsData hn hP hS := by
  sorry

end SM
