import CV.X1
import SM.MarkedProducts
import SM.CornerStateSum


/-! Ported 2026-09-14 05:41Z from work/drafts/cb/Statements_FINAL.lean (design panel judge synthesis, PLAN_FINAL.md §1-§3, §5): row cb:blocks (101), main declaration `SM.cb_blocks_definition`, bundle `CbBlocksDefinitionData` (proof = the panel's proved `cb_blocks_definition_check` body); the bundle `CbProductsData` of row 102 is fixed here, its theorem lives in SM/CBProducts.lean. Only this header added and the two row theorems rearranged as described. -/
/-! # Statements_FINAL — cb:blocks (row 101) and cb:products (row 102)

Judge synthesis, 2026-09-14 (design panel work/drafts/cb/: PLAN_A / Statements_A, PLAN_B / Statements_B;
decision PLAN_FINAL.md). Winner A (blocks = the accepted CV pieces, owner/product through the accepted CV
carrier lemmas, 102 from the accepted `SM.blocks`), with three grafts from B: the owner of a crossing is
DEFINED literally as the carrier of (either) visit on the accepted SM lane (`owner`), `D_A` IS the accepted
`positiveLift` (no geo alias, no equality field), and `P_H` is the polynomial of the restricted named record
(`recordPolynomial`, pinned by `polynomial_independent`) so that no unaccepted definition (`CV.pieceDiagram`,
rows 142/143 under review) and no proof sentence enters the statement.

Source (frame SM15): reference/SM/sm-3-statesum.tex — cb:blocks 4623–4637 (eq. cb:undominated 4627–4629),
cb:products 4638–4651 (eq. cb:product 4645–4648; proof 4652–4696, eq. cb:greedy-step 4661–4663). Consumers
read for shape only: cb:singleton 4697–4759, thm:C-S7 sm-4-knotlaws.tex:267–330.

Row declarations: `SM.cb_blocks_definition hn hP hS : SM.CbBlocksDefinitionData hn hP hS` (DEFINE row 101; proved as the
row statement, PROVED from accepted declarations as `cb_blocks_definition_check`) and `SM.cb_products hn hP hS :
SM.CbProductsData hn hP hS` (PROVE row 102; chain in PLAN_FINAL.md §4 / Skeleton_FINAL.lean; proved in SM/CBProducts.lean).
Every field renders one printed clause and quotes it; bridging conjuncts (CV object = SM object) sit inside
the field of the clause they serve and are marked "(bridge)". Auxiliary definitions live in `SM.CB`.

## Binder (as printed)

"Fix a generic polygon `P`, its interlacement graph `G_P`, and an independent support `S`":
`hn : 3 ≤ n`, `[NeZero n]`, `hP : SM.Generic P` (def:generic, G1 ∧ G2 — the SM notion, as in def:smoothing,
lem:carriers, def:C), `hS : IsDecomposition hn hP S` (def:decomposition, `S ∈ independentSupports hn hP`
= "`S ∈ Ind(G_P)`").

## Notation map (printed → Lean); `hc := SM.CB.cg hn hP := generic_crossingGeometry hn hP`,
`e := geoComponentEquivGeneric hn hP S : GeoComponent hc S ≃ Component hn hP S` (identity on owners, `rfl`)

* `G_P`: the accepted def:interlace `interlacementGraph hn hP` on `V(G_P) = Crossing P`
  (= `geometricInterlacementGraph hc`, `geometricInterlacementGraph_eq_generic`, rfl).
* `N_{G_P}(T)`: `supportNeighbors hn hP T` (def:interlace; bridge `CV.N hc T = supportNeighbors`, `CV.N_eq_generic`).
* eq. cb:undominated `U(S) = V(G_P) ∖ (S ∪ N(S))`: `supportUnselected hn hP S` (`supportUnselected_eq` is
  the printed equation by `rfl`; bridge `CV.U hc S = supportUnselected`, `CV.U_eq_generic`).
* `G_P[U(S)]`: `CV.residualGraph hc S = (geometricInterlacementGraph hc).induce ↑(CV.U hc S)`; "its blocks",
  the connected components: `CV.Piece hc S` (Mathlib `SimpleGraph.ConnectedComponent`; CV:def:pieces, ACCEPTED,
  where the CV text calls the same object a "residual piece"); the block of `c ∈ U(S)`: `CV.pieceOf hc S c _`;
  the labels of a block `H` (`|H|` = their card): `CV.pieceLabels hc S H`.
* "carrier `A` of `S`": `A : Component hn hP S` (def:smoothing, the accepted carriers); "a visit lies on `A`":
  `owner hn hP S (Sum.inr v) = A`.
* "An undominated crossing has both visits on one carrier by Lemma lem:carriers; that carrier is its owner":
  `SM.CB.crossingOwner hn hP S c := owner hn hP S (Sum.inr (someVisit c))`, the carrier of a fixed visit of `c`
  (hypothesis-free); the field `crossing_owner` says that for `c ∈ U(S)` it carries EVERY visit of `c`
  (lem:carriers (iii), accepted `unselected_nonneighbor_both_visits_one_carrier`) and that `c` is one of its
  self-crossings (`carrierCrossings`, def:smoothing).
* the owner of a block `H` (cb:products "Every block `H` has one owner"): `SM.CB.blockOwner hn hP hS H :=
  e (CV.pieceOwner hc _ H)` (CV:lem:carriers (iv), ACCEPTED); pinned by `one_owner`: it is the owner of every
  label of `H`. "`H` owned by `A`": `H ∈ SM.CB.blocksOwnedBy hn hP S A := CV.piecesOn hc S (e.symm A)`, whose
  membership is literally "every visit of every label of `H` lies on `A`" (field `owned_by`).
* "`D_A`, the actual positive diagram of a carrier `A`": the accepted def:positive-lift `positiveLift hn hP S A hS`
  (the diagram of def:C's `cornerHomfly`). "`P_A = P_{D_A}`": `SM.CB.carrierPoly hn hP hS A := SM.P (positiveLift …)`,
  `SM.P` the accepted local polynomial (lp:core). "the corresponding `H_A^+`": `cornerHomfly hn hP S A hS` (def:C);
  "by Theorem lp:core": `P_eq_homfly` (`lp_core.eq_homfly`).
* "`m_A`" (the writhe of `D_A`; def:positive-lift "its writhe is `m_Q`", thm:C-S7 "its polynomial `P_A = H_A^+`
  and writhe `m_A` are those in the state sum"): `carrierCrossingCount hn hP S A` (def:smoothing's `m_Q`);
  `D_A.writhe = m_A` is a conjunct of `actual_positive_diagram`.
* "an actual positive carrier diagram `D_H`" (cb:products): `SM.CB.IsBlockCarrierDiagram hn hP hS H D` — `D` is
  the accepted positive lift of a carrier `q` of an independent refinement `T ⊇ S` ("the further smoothings")
  whose self-crossings are exactly the labels of `H` (proof 4664–4672: "Lemma lem:carriers supplies actual
  geometric carriers for `S_H` … No other self-crossing label survives, so its actual positive diagram is a
  required `D_H`"). Reading R-4 below.
* "its restricted named cyclic record": `SM.CB.blockRecord hn hP hS H := (D_{A_H}).record.restrictCrossings
  (blockRecordCrossings H)` — the named record of the owner's actual diagram `D_{A_H}` (def:gauss-record's
  `Diagram.record`), restricted by mp:blocks' accepted `Record.restrictCrossings` (same circle, the occurrences
  of the crossings of `H`, first-return successor, old pairing/bits/signs) to the record crossings whose
  geometric crossing (`carrierCrossingEquiv`, def:positive-lift) is a label of `H`. "exactly": `RecordIso`
  (def:gauss-record's named isomorphism), the shape of `BlockSupply.supplied`.
* "Its polynomial `P_H`": `SM.CB.blockPoly hn hP hS H := recordPolynomial (blockRecord H)` — `SM.P D` for an actual
  `D` with that named record (`recordPolynomial_eq`, from lc:presentations / rp:record-polynomial; `0` for a
  record no actual diagram has — excluded by `block_diagram`). "independent of the further smoothings used to
  produce it": the field `polynomial_independent` (every block carrier diagram of `H` has the record and the
  value `P_H`).
* eq. cb:product: fields `product`, `count` (sums and products over `blocksOwnedBy A`).
* "With no owned blocks the actual diagram has value `1` and `m_A = 0`": field `no_blocks` (`D_A` is then an
  actual crossing-free one-circle diagram, lp:core "`P_○ = 1`"; "No empty link is evaluated":
  `componentCount = 1` in `actual_positive_diagram`).

## Readings recorded (fidelity; to be written into AUTHOR_NOTES before the rows are stated)

R-1 SM "block" = CV `Piece` at `hc = generic_crossingGeometry hn hP` (the same printed object "connected
components of `G_P[U(S)]`"; vertex set `CV.U hc S = supportUnselected` by `CV.U_eq_generic`, adjacency
`Interlaces hn hP` by rfl). R-2 the owner of a crossing is defined through a fixed visit (`someVisit`) and
pinned on `U(S)` by `crossing_owner`; the owner of a block through the accepted `CV.pieceOwner` (a
`Classical.choose` of CV:lem:carriers (iv)) transported by `e` (rfl on owners), pinned by `one_owner`.
R-3 `D_A` is the accepted `positiveLift`; blocks/owners are read on the geo layer and carriers on the SM lane,
joined by the accepted `geoComponentEquivGeneric` (`geoComponentEquivGeneric_owner : e (geoOwner a) = owner a`
is `rfl`; `geoCarrierCrossings_eq_generic`). R-4 "actual positive carrier diagram `D_H`" = positive lift of a
carrier of an independent refinement `T ⊇ S` with self-crossings exactly `H`; the printed `S_H` has moreover
`U(S_H) = H`, which the statement never needs (the canonical witness of the proof, `CV.pieceDiagram`, cleans
only the carrier of `H`; both satisfy the predicate). R-5 "its restricted named cyclic record" = the record of
the OWNER's actual diagram `D_{A_H}` restricted to `H` (mp:blocks' phrase; the printed proof's "the original
record restricted to `H`" is `RecordIso` to it by the chain lemma KL1 + KL3). R-6 `P_H` is a term
(`recordPolynomial`, a `Classical.choose` over realizations) pinned by `polynomial_independent`; no clause
depends on the choice. R-7 `polynomial_independent` also asserts the record clause for every block carrier
diagram ("Any other choices produce the same named record", proof 4678) — stronger than the printed statement
sentence, which speaks of `P_H` only. R-8 `hn : 3 ≤ n` and `[NeZero n]` are bundle parameters (as def:C).
Not in the rows (companion lemmas of the module): eq. cb:greedy-step and "the enlarged support is independent"
(proof 4657–4663, cited by cb:singleton), and `blockPoly_eq_of_labels_eq` (cb:singleton's before/after split).
Axioms: row 101 depends on `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness` through `homfly`/`SM.P` in
`equals_Hplus` (as def:C); row 102 adds `SM.blocks`' axioms (`SM.lp_lm`).

Checked with `cd work/lean && lake env lean ../drafts/cb/Statements_FINAL.lean`: 0 errors, exactly two
row 101 proved here; row 102 in SM/CBProducts.lean. -/

namespace SM

open SM.Carrier SM.GeoCarrier SM.Link

attribute [local instance] Classical.propDecidable

namespace CB

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-- `G_P` read on the geometric record domain: the accepted `generic_crossingGeometry hn hP`
(def:generic ⇒ the geometric record domain, SM/CrossingGeometry.lean). Reducible; every `CV.*`/`geo*` object
below is parametrised by this proof, and proof irrelevance identifies it with any other `CrossingGeometry P`. -/
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

omit [NeZero n] in
/-- A fixed visit of a crossing (hypothesis-free; for `c ∈ U(S)` both visits have the same owner,
field `crossing_owner`). -/
noncomputable def someVisit (c : Crossing P) : Visit P :=
  ⟨c, Classical.choose (crossing_visits_exist c)⟩

omit [NeZero n] in
theorem someVisit_crossing (c : Crossing P) : (someVisit c).1 = c := rfl

variable (S) in
/-- **The owner of an undominated crossing** (cb:blocks): "An undominated crossing has both visits on one
carrier by Lemma lem:carriers; that carrier is its *owner*" — the carrier (def:smoothing's `owner`) of (either)
visit of `c`, fixed at `someVisit c`. The field `crossing_owner` says that for `c ∈ U(S)` it carries every
visit of `c`. -/
noncomputable def crossingOwner (c : Crossing P) : Component hn hP S :=
  owner hn hP S (Sum.inr (someVisit c))

/-- **The owner of a block `H`** (cb:products "Every block `H` has one owner"): CV:lem:carriers (iv)'s unique
carrier of the piece (`CV.pieceOwner`, accepted), read as a def:smoothing carrier through the accepted
equivalence `geoComponentEquivGeneric` (the identity on owners: `geoComponentEquivGeneric_owner` is `rfl`).
Pinned by `one_owner`: it is `crossingOwner c` for every label `c` of `H`. -/
noncomputable def blockOwner (hS : IsDecomposition hn hP S) (H : CV.Piece (cg hn hP) S) :
    Component hn hP S :=
  geoComponentEquivGeneric hn hP S (CV.pieceOwner (cg hn hP) (mem_Ind hn hP hS) H)

variable (S) in
/-- **"`H` owned by `A`"** (eq. cb:product): the blocks all of whose labels' visits lie on the carrier `A`
(CV:def:pieces' `piecesOn`, accepted, at the geo carrier `e.symm A`); field `owned_by` spells the membership
out with def:smoothing's `owner`. -/
noncomputable def blocksOwnedBy (A : Component hn hP S) : Finset (CV.Piece (cg hn hP) S) :=
  CV.piecesOn (cg hn hP) S ((geoComponentEquivGeneric hn hP S).symm A)

/-- **`P_A = P_{D_A}`** (cb:blocks): the accepted local polynomial `SM.P` (lp:core) of the accepted actual
positive diagram `D_A = positiveLift hn hP S A hS` (def:positive-lift). -/
noncomputable def carrierPoly (hS : IsDecomposition hn hP S) (A : Component hn hP S) : R :=
  SM.P (positiveLift hn hP S A hS)

/-- **An actual positive carrier diagram of the block `H`** (cb:products): the actual positive diagram
(def:positive-lift) of a carrier `q` of an independent refinement `T ⊇ S` ("the further smoothings") whose
self-crossings are exactly the labels of `H` ("Lemma lem:carriers supplies actual geometric carriers for
`S_H` … No other self-crossing label survives, so its actual positive diagram is a required `D_H`").
Reading R-4: the printed `S_H` has moreover `U(S_H) = H`, which no clause needs. -/
def IsBlockCarrierDiagram (_hS : IsDecomposition hn hP S) (H : CV.Piece (cg hn hP) S) (D : Diagram) :
    Prop :=
  ∃ (T : Finset (Crossing P)) (hT : IsDecomposition hn hP T) (q : Component hn hP T),
    S ⊆ T ∧ carrierCrossings hn hP T q = CV.pieceLabels (cg hn hP) S H ∧
    D = positiveLift hn hP T q hT

/-- The record crossings of the actual diagram `D_A` of a carrier `A` belonging to the block `H`: the chords
`{v, τ v}` of the occurrences `v` whose geometric crossing (def:positive-lift's `carrierCrossingEquiv`) is a
label of `H`. (Stated for every carrier `A`; the restricted record of `H` takes `A = A_H`, its owner.) -/
def blockRecordCrossings (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    (H : CV.Piece (cg hn hP) S) : Set (positiveLift hn hP S A hS).record.Crossing :=
  {p | ∃ v : (positiveLift hn hP S A hS).Γ.Visit,
    p = (positiveLift hn hP S A hS).record.crossingOf v ∧
    (carrierCrossingEquiv hn hP S A hS v.1).val ∈ CV.pieceLabels (cg hn hP) S H}

/-- **"its restricted named cyclic record"** (cb:products; mp:blocks' phrase): the named record
(def:gauss-record) of the owner's actual positive diagram `D_{A_H}`, restricted by the accepted
`Record.restrictCrossings` to the crossings of `H` — same circle, the occurrences of the crossings of `H`,
first-return successor (their inherited cyclic order), pairing, over/under bits and signs unchanged. -/
noncomputable def blockRecord (hS : IsDecomposition hn hP S) (H : CV.Piece (cg hn hP) S) : Record :=
  (positiveLift hn hP S (blockOwner hn hP hS H) hS).record.restrictCrossings
    (blockRecordCrossings hn hP hS (blockOwner hn hP hS H) H)

/-- The polynomial of a named record: `SM.P D` for an actual diagram `D` with that record (any such `D`
gives the same value, `recordPolynomial_eq`, by lc:presentations / rp:record-polynomial); `0` for a record no
actual diagram has. -/
noncomputable def recordPolynomial (ρ : Record) : R :=
  if h : IsRealizable ρ then
    SM.P (Classical.choose (show ∃ D : Diagram, Nonempty (RecordIso D.record ρ) from h))
  else 0

theorem recordPolynomial_eq (ρ : Record) (D : Diagram) (h : Nonempty (RecordIso D.record ρ)) :
    recordPolynomial ρ = SM.P D := by
  unfold recordPolynomial
  split_ifs with hr
  · obtain ⟨ι⟩ := Classical.choose_spec (show ∃ D : Diagram, Nonempty (RecordIso D.record ρ) from hr)
    obtain ⟨κ⟩ := h
    exact presentations _ D ⟨ι.trans κ.symm⟩
  · exact absurd ⟨D, h⟩ hr

/-- **`P_H`** (cb:products "Its polynomial `P_H`"): the polynomial of (any) actual diagram with the restricted
named cyclic record of `H`; pinned by `polynomial_independent`. -/
noncomputable def blockPoly (hS : IsDecomposition hn hP S) (H : CV.Piece (cg hn hP) S) : R :=
  recordPolynomial (blockRecord hn hP hS H)

end CB

open CB

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {S : Finset (Crossing P)}

/-- **cb:blocks (sm-3:4623–4637) as printed**, one field per printed clause, on the printed binder
"a generic polygon `P` … an independent support `S`" (`hP : Generic P`, `hS : IsDecomposition hn hP S`).
Notation: `hc = cg hn hP`, `U = supportUnselected hn hP S`, `N = supportNeighbors hn hP`,
`D_A = positiveLift hn hP S A hS`, `m_A = carrierCrossingCount hn hP S A`. -/
structure CbBlocksDefinitionData (hS : IsDecomposition hn hP S) : Prop where
  /-- "Fix a generic polygon `P`, its interlacement graph `G_P`": def:interlace's `interlacementGraph hn hP`
  (adjacency = `Interlaces`), read on the geometric record domain (bridge) -/
  interlacement_graph :
    geometricInterlacementGraph (cg hn hP) = interlacementGraph hn hP ∧
    ∀ x y : Crossing P, (interlacementGraph hn hP).Adj x y ↔ Interlaces hn hP x y
  /-- "For a vertex set `T` write `N_G(T)` for the union of its graph neighbourhoods": a crossing lies in
  `N_{G_P}(T)` iff it interlaces some element of `T` (and (bridge) `CV.N hc T` is that set) -/
  neighbourhood :
    (∀ (T : Finset (Crossing P)) (y : Crossing P),
      y ∈ supportNeighbors hn hP T ↔ ∃ x ∈ T, Interlaces hn hP y x) ∧
    ∀ T : Finset (Crossing P), CV.N (cg hn hP) T = supportNeighbors hn hP T
  /-- eq. cb:undominated: "`U(S) = V(G_P) ∖ (S ∪ N_{G_P}(S))`" (`V(G_P) = Finset.univ`), membership-wise
  "neither selected nor adjacent to a selected crossing", and (bridge) `CV.U hc S` is that set -/
  undominated :
    supportUnselected hn hP S = Finset.univ \ (S ∪ supportNeighbors hn hP S) ∧
    (∀ x : Crossing P, x ∈ supportUnselected hn hP S ↔ x ∉ S ∧ x ∉ supportNeighbors hn hP S) ∧
    CV.U (cg hn hP) S = supportUnselected hn hP S
  /-- "The connected components of `G_P[U(S)]` are called its *blocks*": `G_P[U(S)]` is the induced subgraph
  on `U(S)` with the adjacency of `G_P`, and two undominated crossings have the same block iff they are joined
  by a path in it -/
  blocks :
    (∀ x y : (↑(CV.U (cg hn hP) S) : Set (Crossing P)),
      (CV.residualGraph (cg hn hP) S).Adj x y ↔ Interlaces hn hP x y) ∧
    ∀ (x y : Crossing P) (hx : x ∈ CV.U (cg hn hP) S) (hy : y ∈ CV.U (cg hn hP) S),
      CV.pieceOf (cg hn hP) S x hx = CV.pieceOf (cg hn hP) S y hy ↔
        (CV.residualGraph (cg hn hP) S).Reachable ⟨x, hx⟩ ⟨y, hy⟩
  /-- … the blocks are nonempty, pairwise disjoint subsets of `U(S)` covering it (the connected components
  partition the vertex set) -/
  blocks_partition :
    (∀ H : CV.Piece (cg hn hP) S,
      CV.pieceLabels (cg hn hP) S H ⊆ CV.U (cg hn hP) S ∧ (CV.pieceLabels (cg hn hP) S H).Nonempty) ∧
    (∀ H H' : CV.Piece (cg hn hP) S, H ≠ H' →
      Disjoint (CV.pieceLabels (cg hn hP) S H) (CV.pieceLabels (cg hn hP) S H')) ∧
    (Finset.univ : Finset (CV.Piece (cg hn hP) S)).biUnion (CV.pieceLabels (cg hn hP) S) = CV.U (cg hn hP) S
  /-- "An undominated crossing has both visits on one carrier by Lemma lem:carriers" (lem:carriers (iii)) -/
  undominated_one_carrier : ∀ c ∈ supportUnselected hn hP S, ∀ v w : Visit P, v.1 = c → w.1 = c →
    owner hn hP S (Sum.inr v) = owner hn hP S (Sum.inr w)
  /-- "that carrier is its owner": `crossingOwner c` is the carrier of every visit of `c ∈ U(S)`, and `c` is
  one of its self-crossings (def:smoothing's `carrierCrossings`) -/
  crossing_owner : ∀ c ∈ supportUnselected hn hP S,
    (∀ v : Visit P, v.1 = c → owner hn hP S (Sum.inr v) = crossingOwner hn hP S c) ∧
    c ∈ carrierCrossings hn hP S (crossingOwner hn hP S c)
  /-- "Write `D_A` for the actual positive diagram of a carrier `A`": `D_A = positiveLift hn hP S A hS`
  (def:positive-lift) is a one-component diagram, every crossing positive (sign `+1`), of writhe `m_A` -/
  actual_positive_diagram : ∀ A : Component hn hP S,
    (positiveLift hn hP S A hS).componentCount = 1 ∧
    (∀ x, (positiveLift hn hP S A hS).IsPositive x) ∧
    (∀ x, (positiveLift hn hP S A hS).sign x = 1) ∧
    (positiveLift hn hP S A hS).writhe = carrierCrossingCount hn hP S A
  /-- "and `P_A = P_{D_A}`" -/
  carrier_polynomial : ∀ A : Component hn hP S,
    carrierPoly hn hP hS A = SM.P (positiveLift hn hP S A hS)
  /-- "These polynomials equal the corresponding `H_A^+` by Theorem lp:core": `P_A = H(D_A)` (lp:core
  "It equals `H_D`"), and `H(D_A)` is def:C's `H^+_A = cornerHomfly` -/
  equals_Hplus : ∀ A : Component hn hP S,
    carrierPoly hn hP hS A = homfly (positiveLift hn hP S A hS) ∧
    carrierPoly hn hP hS A = cornerHomfly hn hP S A hS

/-- **cb:products (sm-3:4638–4651) as printed**, one field per printed clause, on the binder of cb:blocks.
Notation: `hc = cg hn hP`, `A_H = blockOwner hn hP hS H` the owner of the block `H`,
`D_A = positiveLift hn hP S A hS`, `P_A = carrierPoly hn hP hS A`, `m_A = carrierCrossingCount hn hP S A`,
`|H| = (CV.pieceLabels hc S H).card`, `P_H = blockPoly hn hP hS H`, the restricted named cyclic record of `H`
= `blockRecord hn hP hS H`. -/
structure CbProductsData (hS : IsDecomposition hn hP S) : Prop where
  /-- "Every block `H` has one owner": exactly one carrier carries both visits of every label of `H`, and it
  is the owner (cb:blocks) of each of its labels -/
  one_owner : ∀ H : CV.Piece (cg hn hP) S,
    (∃! q : Component hn hP S, ∀ c ∈ CV.pieceLabels (cg hn hP) S H, ∀ v : Visit P, v.1 = c →
      owner hn hP S (Sum.inr v) = q) ∧
    ∀ c ∈ CV.pieceLabels (cg hn hP) S H, crossingOwner hn hP S c = blockOwner hn hP hS H
  /-- "and admits an actual positive carrier diagram `D_H` with exactly its restricted named cyclic record" -/
  block_diagram : ∀ H : CV.Piece (cg hn hP) S, ∃ D : Diagram,
    IsBlockCarrierDiagram hn hP hS H D ∧ Nonempty (RecordIso D.record (blockRecord hn hP hS H))
  /-- "Its polynomial `P_H` is independent of the further smoothings used to produce it": every actual
  positive carrier diagram of `H` has the restricted named record ("Any other choices produce the same named
  record", proof 4678) and the polynomial `P_H` (rp:record-polynomial) -/
  polynomial_independent : ∀ (H : CV.Piece (cg hn hP) S) (D : Diagram),
    IsBlockCarrierDiagram hn hP hS H D →
      Nonempty (RecordIso D.record (blockRecord hn hP hS H)) ∧ SM.P D = blockPoly hn hP hS H
  /-- "`H` owned by `A`" (eq. cb:product) spelled out: `H ∈ blocksOwnedBy A` iff every visit of every label
  of `H` lies on the carrier `A`, iff `A` is the owner of the block -/
  owned_by : ∀ (A : Component hn hP S) (H : CV.Piece (cg hn hP) S),
    (H ∈ blocksOwnedBy hn hP S A ↔
      ∀ c ∈ CV.pieceLabels (cg hn hP) S H, ∀ v : Visit P, v.1 = c → owner hn hP S (Sum.inr v) = A) ∧
    (H ∈ blocksOwnedBy hn hP S A ↔ blockOwner hn hP hS H = A)
  /-- eq. cb:product, first identity: "For every original carrier `A`, `P_A = ∏_{H owned by A} P_H`" -/
  product : ∀ A : Component hn hP S,
    carrierPoly hn hP hS A = ∏ H ∈ blocksOwnedBy hn hP S A, blockPoly hn hP hS H
  /-- eq. cb:product, second identity: "`m_A = ∑_{H owned by A} |H|`" -/
  count : ∀ A : Component hn hP S,
    carrierCrossingCount hn hP S A = ∑ H ∈ blocksOwnedBy hn hP S A, (CV.pieceLabels (cg hn hP) S H).card
  /-- "With no owned blocks the actual diagram has value `1` and `m_A = 0`" (`D_A` is then an actual
  crossing-free one-circle diagram; "No empty link is evaluated") -/
  no_blocks : ∀ A : Component hn hP S, blocksOwnedBy hn hP S A = ∅ →
    (positiveLift hn hP S A hS).IsCrossingFreeCircle ∧
    carrierPoly hn hP hS A = 1 ∧ carrierCrossingCount hn hP S A = 0

/-- **Row 101, cb:blocks** (DEFINE row), on the printed binder (its proof
from accepted declarations is `cb_blocks_definition_check` below, to be ported as the row proof). -/
theorem cb_blocks_definition (hS : IsDecomposition hn hP S) : CbBlocksDefinitionData hn hP hS where
  interlacement_graph := ⟨geometricInterlacementGraph_eq_generic hn hP _, fun _ _ => Iff.rfl⟩
  neighbourhood := ⟨fun T y => mem_supportNeighbors hn hP T y, fun T => CV.N_eq_generic hn hP _ T⟩
  undominated :=
    ⟨supportUnselected_eq hn hP S, fun x => mem_supportUnselected hn hP S x, CV.U_eq_generic hn hP _ S⟩
  blocks := ⟨fun _ _ => Iff.rfl, fun _ _ _ _ => SimpleGraph.ConnectedComponent.eq⟩
  blocks_partition :=
    ⟨fun H => ⟨CV.pieceLabels_subset _ S H, CV.pieceLabels_nonempty _ S H⟩,
      CV.pieceLabels_disjoint _ S, CV.biUnion_pieceLabels _ S⟩
  undominated_one_carrier _ hc v w hv hw :=
    unselected_nonneighbor_both_visits_one_carrier hn hP hS hc v w hv hw
  crossing_owner c hc :=
    have h1 : ∀ v : Visit P, v.1 = c → owner hn hP S (Sum.inr v) = crossingOwner hn hP S c :=
      fun v hv => unselected_nonneighbor_both_visits_one_carrier hn hP hS hc v (someVisit c) hv rfl
    ⟨h1, (mem_carrierCrossings hn hP S _ c).mpr ⟨((mem_supportUnselected hn hP S c).mp hc).1, h1⟩⟩
  actual_positive_diagram A :=
    ⟨positiveLift_componentCount hn hP S A hS, positiveLift_isPositive hn hP S A hS,
      positiveLift_sign hn hP S A hS, positiveLift_writhe_eq_carrierCrossingCount hn hP S A hS⟩
  carrier_polynomial _ := rfl
  equals_Hplus _ := ⟨P_eq_homfly _, P_eq_homfly _⟩

/-- Statement check of row 101: every field is an accepted fact (the row proof, verbatim). -/
theorem cb_blocks_definition_check (hS : IsDecomposition hn hP S) : CbBlocksDefinitionData hn hP hS :=
  cb_blocks_definition hn hP hS

/-! Row 102 cb:products (`SM.cb_products : CbProductsData hn hP hS`) is proved in SM/CBProducts.lean from the chain of
PLAN_FINAL.md §4; its bundle `CbProductsData` is fixed here. -/

end SM
