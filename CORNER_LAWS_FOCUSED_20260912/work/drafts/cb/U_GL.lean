import CV.X1
import CV.PieceCurve
import SM.MarkedProducts
import SM.CornerStateSum

/-! # Skeleton_FINAL — cb:blocks (101) and cb:products (102): chain leaves + assembled rows

Judge synthesis, 2026-09-14. The definitions and the two bundles are BYTE-IDENTICAL to
work/drafts/cb/Statements_FINAL.lean (notation map and readings R-1..R-8 there). After them: the chain lemmas of
PLAN_FINAL.md §4 as `sorry` leaves (units KL0, KL1, KL2, KL3, T1, GL, AS; PC proved from CV:lem:piececurve), the
proved glue, and the two row theorems `SM.cb_blocks_definition` (no leaf) and `SM.cb_products` (assembled from
the leaves), plus the companion lemmas `SM.greedy_independent` / `SM.greedy_step` (eq. cb:greedy-step) that
cb:singleton cites. Checked with `cd work/lean && lake env lean ../drafts/cb/Skeleton_FINAL.lean`. -/

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


/-! ## Chain (Skeleton_FINAL): sorried leaves by unit, then the row theorems assembled from them

Units (PLAN_FINAL.md §4): KL0 abstract restricted Gauss record; KL1 the carrier record bridge (the geometric
heart); KL2 record interlacement = `Interlaces`; KL3 restriction of the abstract record; T1 transport of
`restrictCrossings` along a `RecordIso`; GL the record blocks of `D_A` are the blocks owned by `A`; PC the
block carrier (from CV:lem:piececurve, or B's greedy support); AS small assembly leaves. Everything after
the leaves is proved here. -/

namespace CB

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-! ### KL0 — the abstract restricted Gauss record `gaussRecord hc T` (one circle, occurrences = the visits of
the crossings in `T`, successor = cyclic `next` in P's key-sorted Gauss list filtered to `T`, pairing = `visitTwin`,
over bit = the positive resolution `det(d_v, d_{τv}) > 0`, all signs `+1`) -/

/-- `L_T`: P's key-sorted Gauss list (`geometricGaussList`, accepted) filtered to the crossings in `T`. -/
noncomputable def gaussList (hc : CrossingGeometry P) (T : Finset (Crossing P)) : List (Visit P) :=
  (geometricGaussList hc).filter (fun v => decide (v.1 ∈ T))

/-- KL0 leaf: the cyclic successor on `L_T` as a permutation of the retained visits. -/
noncomputable def gaussSucc (hc : CrossingGeometry P) (T : Finset (Crossing P)) :
    Equiv.Perm {v : Visit P // v.1 ∈ T} := sorry

/-- KL0 leaf (spec of `gaussSucc`): it is `List.next` on `L_T`. -/
theorem gaussSucc_val (hc : CrossingGeometry P) (T : Finset (Crossing P)) (v : {v : Visit P // v.1 ∈ T})
    (hv : v.1 ∈ gaussList hc T) : (gaussSucc hc T v).1 = (gaussList hc T).next v.1 hv := sorry

/-- KL0 leaf: the twin pairing on the retained visits (`visitTwin` keeps the crossing). -/
noncomputable def gaussPair (hc : CrossingGeometry P) (T : Finset (Crossing P)) :
    Equiv.Perm {v : Visit P // v.1 ∈ T} := sorry

theorem gaussPair_val (hc : CrossingGeometry P) (T : Finset (Crossing P)) (v : {v : Visit P // v.1 ∈ T}) :
    (gaussPair hc T v).1 = visitTwin v.1 := sorry

/-- The over bit of the positive resolution at `v`: `det(d_v, d_{τ v}) > 0` (def:positive-lift). -/
noncomputable def positiveOverBit (v : Visit P) : Bool :=
  decide (0 < det (edge P v.2.val) (edge P (visitTwin v).2.val))

/-- **KL0: the abstract restricted Gauss record.** Data fixed here; the record laws are KL0 leaves. -/
noncomputable def gaussRecord (hc : CrossingGeometry P) (T : Finset (Crossing P)) : Record where
  comps := Unit
  M := {v : Visit P // v.1 ∈ T}
  comp _ := ()
  succ := gaussSucc hc T
  pair := gaussPair hc T
  isOver v := positiveOverBit v.1
  sgn _ := 1
  succ_comp _ := rfl
  succ_cycle := sorry
  pair_ne := sorry
  pair_invol := sorry
  bit_pair := sorry
  sgn_pair _ := rfl
  sgn_ne _ := by decide

@[simp] theorem gaussRecord_M (hc : CrossingGeometry P) (T : Finset (Crossing P)) :
    (gaussRecord hc T).M = {v : Visit P // v.1 ∈ T} := rfl

theorem gaussRecord_componentCount (hc : CrossingGeometry P) (T : Finset (Crossing P)) :
    (gaussRecord hc T).componentCount = 1 := Fintype.card_unit

/-- The P-visit of an occurrence of `gaussRecord hc T`. -/
def occVisit (hc : CrossingGeometry P) (T : Finset (Crossing P)) (x : (gaussRecord hc T).M) : Visit P :=
  (x : {v : Visit P // v.1 ∈ T}).1

theorem occVisit_mem (hc : CrossingGeometry P) (T : Finset (Crossing P)) (x : (gaussRecord hc T).M) :
    (occVisit hc T x).1 ∈ T := (x : {v : Visit P // v.1 ∈ T}).2

/-- The geometric crossing ("label") of a record crossing of `gaussRecord hc T` (both occurrences of a chord
have the same label, `gaussPair_val` + `visitTwin_crossing`). -/
noncomputable def label (hc : CrossingGeometry P) (T : Finset (Crossing P))
    (p : (gaussRecord hc T).Crossing) : Crossing P :=
  (p.rep : {v : Visit P // v.1 ∈ T}).1.1

theorem label_mem (hc : CrossingGeometry P) (T : Finset (Crossing P)) (p : (gaussRecord hc T).Crossing) :
    label hc T p ∈ T := (p.rep : {v : Visit P // v.1 ∈ T}).2

/-- KL0 leaf: the label of the chord of an occurrence is the occurrence's crossing. -/
theorem label_crossingOf (hc : CrossingGeometry P) (T : Finset (Crossing P)) (x : (gaussRecord hc T).M) :
    label hc T ((gaussRecord hc T).crossingOf x) = (occVisit hc T x).1 := sorry

/-! ### KL1 — the carrier record bridge (the geometric heart, on the accepted `positiveLift`; prove on
`geoPositiveLift` and transfer by `geoPositiveLift_eq_generic` if convenient) -/

variable (hn : 3 ≤ n) (hP : Generic P)

/-- **KL1 leaf: the named record of the actual positive diagram of a carrier `q` of an independent `T` IS the
abstract restricted Gauss record of its self-crossings** ("Successor splitting retains the cyclic order inherited
from the original traversal. The surviving crossing germs have not changed"). -/
noncomputable def positiveLiftRecordIso {T : Finset (Crossing P)} (hT : IsDecomposition hn hP T)
    (q : Component hn hP T) :
    RecordIso (positiveLift hn hP T q hT).record (gaussRecord (cg hn hP) (carrierCrossings hn hP T q)) := sorry

/-- KL1 leaf (spec of the occurrence bijection): the P-visit assigned to a shadow visit `v` lies at the
geometric crossing of `v` (`carrierCrossingEquiv`, def:positive-lift). -/
theorem positiveLiftRecordIso_val {T : Finset (Crossing P)} (hT : IsDecomposition hn hP T)
    (q : Component hn hP T) (v : (positiveLift hn hP T q hT).Γ.Visit) :
    (occVisit (cg hn hP) _ ((positiveLiftRecordIso hn hP hT q).Φ v)).1 =
      (carrierCrossingEquiv hn hP T q hT v.1).val := sorry

/-! ### KL2 — record interlacement on `gaussRecord` is `Interlaces` (def:interlace) -/

/-- KL2 leaf. -/
theorem gaussRecord_adj_iff (T : Finset (Crossing P)) (p p' : (gaussRecord (cg hn hP) T).Crossing) :
    (gaussRecord (cg hn hP) T).interlacementGraph.Adj p p' ↔
      Interlaces hn hP (label (cg hn hP) T p) (label (cg hn hP) T p') := sorry

/-! ### KL3 — restriction of the abstract record -/

/-- KL3 leaf: restricting `gaussRecord hc T` to the chords labelled in `T' ⊆ T` gives `gaussRecord hc T'`. -/
theorem gaussRecord_restrict_iso (hc : CrossingGeometry P) {T' T : Finset (Crossing P)} (h : T' ⊆ T) :
    Nonempty (RecordIso ((gaussRecord hc T).restrictCrossings {p | label hc T p ∈ T'}) (gaussRecord hc T')) :=
  sorry

/-! ### T1 — transport of `restrictCrossings` along a `RecordIso` -/

/-- T1 leaf: a named record isomorphism restricts to corresponding crossing sets (occurrence-level condition). -/
theorem restrictCrossings_iso_of_recordIso {ρ ρ' : Record} (ι : RecordIso ρ ρ') (X : Set ρ.Crossing)
    (X' : Set ρ'.Crossing)
    (hX : ∀ v : ρ.M, ρ.crossingOf v ∈ X ↔ ρ'.crossingOf (ι.Φ v) ∈ X') :
    Nonempty (RecordIso (ρ.restrictCrossings X) (ρ'.restrictCrossings X')) := sorry

/-! ### GL — the record blocks of `D_A` are the blocks owned by `A` -/

/-! #### GL helpers (unit GL, prefixed `gl_`): transport of record interlacement along a `RecordIso`, the
label map of `D_A`'s record crossings, and the component bijection. -/

section GLHelpers

omit hn hP in
/-- A named record isomorphism preserves the forward step count. -/
theorem gl_steps_map {ρ ρ' : Record} (ι : RecordIso ρ ρ') (v w : ρ.M) :
    ρ'.steps (ι.Φ v) (ι.Φ w) = ρ.steps v w := by
  have key : ∀ k : ℕ, (ρ'.succ ^ k) (ι.Φ v) = ι.Φ w ↔ (ρ.succ ^ k) v = w := fun k => by
    rw [← ι.Φ_pow]; exact ι.Φ.injective.eq_iff
  unfold Record.steps
  by_cases h : ∃ k : ℕ, (ρ.succ ^ k) v = w
  · have h' : ∃ k : ℕ, (ρ'.succ ^ k) (ι.Φ v) = ι.Φ w := by
      obtain ⟨k, hk⟩ := h
      exact ⟨k, (key k).mpr hk⟩
    rw [dite_eq_left h', dite_eq_left h]
    exact le_antisymm (Nat.find_min' h' ((key _).mpr (Nat.find_spec h)))
      (Nat.find_min' h ((key _).mp (Nat.find_spec h')))
  · have h' : ¬ ∃ k : ℕ, (ρ'.succ ^ k) (ι.Φ v) = ι.Φ w := by
      rintro ⟨k, hk⟩
      exact h ⟨k, (key k).mp hk⟩
    rw [dite_eq_right h', dite_eq_right h]

omit hn hP in
theorem gl_arcBetween_map {ρ ρ' : Record} (ι : RecordIso ρ ρ') (v w u : ρ.M) :
    ρ'.ArcBetween (ι.Φ v) (ι.Φ w) (ι.Φ u) ↔ ρ.ArcBetween v w u := by
  unfold Record.ArcBetween
  rw [gl_steps_map, gl_steps_map]

omit hn hP in
/-- The crossing map induced by a named record isomorphism (the chord of the image of a chosen occurrence). -/
noncomputable def gl_crossingMap {ρ ρ' : Record} (ι : RecordIso ρ ρ') (x : ρ.Crossing) : ρ'.Crossing :=
  ρ'.crossingOf (ι.Φ x.rep)

omit hn hP in
theorem gl_crossingOf_Φ_eq_iff {ρ ρ' : Record} (ι : RecordIso ρ ρ') (v w : ρ.M) :
    ρ'.crossingOf (ι.Φ v) = ρ'.crossingOf (ι.Φ w) ↔ ρ.crossingOf v = ρ.crossingOf w := by
  rw [Record.crossingOf_eq_iff, Record.crossingOf_eq_iff]
  show ι.Φ v ∈ ({ι.Φ w, ρ'.pair (ι.Φ w)} : Finset ρ'.M) ↔ v ∈ ({w, ρ.pair w} : Finset ρ.M)
  rw [← ι.pair_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton, ι.Φ.injective.eq_iff]

omit hn hP in
theorem gl_crossingMap_crossingOf {ρ ρ' : Record} (ι : RecordIso ρ ρ') (v : ρ.M) :
    gl_crossingMap ι (ρ.crossingOf v) = ρ'.crossingOf (ι.Φ v) := by
  unfold gl_crossingMap
  rw [gl_crossingOf_Φ_eq_iff, Record.crossingOf_rep]

omit hn hP in
theorem gl_crossingMap_inj {ρ ρ' : Record} (ι : RecordIso ρ ρ') (x y : ρ.Crossing) :
    gl_crossingMap ι x = gl_crossingMap ι y ↔ x = y := by
  unfold gl_crossingMap
  rw [gl_crossingOf_Φ_eq_iff, Record.crossingOf_rep, Record.crossingOf_rep]

omit hn hP in
theorem gl_mem_crossingMap_iff {ρ ρ' : Record} (ι : RecordIso ρ ρ') (x : ρ.Crossing) (v : ρ.M) :
    ι.Φ v ∈ (gl_crossingMap ι x).1 ↔ v ∈ x.1 := by
  unfold gl_crossingMap
  rw [← Record.crossingOf_eq_iff, gl_crossingOf_Φ_eq_iff, Record.crossingOf_rep, Record.crossingOf_eq_iff]

omit hn hP in
theorem gl_forall_mem_crossingMap {ρ ρ' : Record} (ι : RecordIso ρ ρ') (x : ρ.Crossing) (Q : ρ'.M → Prop) :
    (∀ v' ∈ (gl_crossingMap ι x).1, Q v') ↔ ∀ v ∈ x.1, Q (ι.Φ v) := by
  constructor
  · intro h v hv
    exact h _ ((gl_mem_crossingMap_iff ι x v).mpr hv)
  · intro h v' hv'
    obtain ⟨v, rfl⟩ := ι.Φ.surjective v'
    exact h v ((gl_mem_crossingMap_iff ι x v).mp hv')

omit hn hP in
/-- A named record isomorphism preserves record interlacement (mp:blocks' chord interlacement). -/
theorem gl_interlaces_map {ρ ρ' : Record} (ι : RecordIso ρ ρ') (x y : ρ.Crossing) :
    ρ'.Interlaces (gl_crossingMap ι x) (gl_crossingMap ι y) ↔ ρ.Interlaces x y := by
  unfold Record.Interlaces
  refine and_congr (not_congr (gl_crossingMap_inj ι x y)) ?_
  rw [gl_forall_mem_crossingMap]
  refine forall_congr' fun v => forall_congr' fun _ => ?_
  rw [gl_forall_mem_crossingMap]
  refine forall_congr' fun w => forall_congr' fun _ => ?_
  rw [← ι.pair_eq, ← ι.pair_eq, gl_arcBetween_map, gl_arcBetween_map]

omit hn hP in
/-- A named record isomorphism induces an isomorphism of record interlacement graphs. -/
theorem gl_adj_map {ρ ρ' : Record} (ι : RecordIso ρ ρ') (x y : ρ.Crossing) :
    ρ'.interlacementGraph.Adj (gl_crossingMap ι x) (gl_crossingMap ι y) ↔
      ρ.interlacementGraph.Adj x y := by
  unfold Record.interlacementGraph
  rw [SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  exact and_congr (not_congr (gl_crossingMap_inj ι x y))
    (or_congr (gl_interlaces_map ι x y) (gl_interlaces_map ι y x))

omit hn hP in
/-- Two chords of `gaussRecord hc T` with the same label are equal (each crossing has exactly the two
visits `v`, `visitTwin v`, which are paired). -/
theorem gl_label_inj (hc : CrossingGeometry P) (T : Finset (Crossing P))
    {x x' : (gaussRecord hc T).Crossing} (h : label hc T x = label hc T x') : x = x' := by
  have hx := (gaussRecord hc T).crossingOf_rep x
  have hx' := (gaussRecord hc T).crossingOf_rep x'
  rcases visit_eq_or_twin (x.rep : {v : Visit P // v.1 ∈ T}).1 (x'.rep : {v : Visit P // v.1 ∈ T}).1 h.symm
    with h1 | h1
  · have h2 : x'.rep = x.rep := Subtype.ext h1
    rw [← hx, ← hx', h2]
  · have h2 : x'.rep = (gaussRecord hc T).pair x.rep := by
      apply Subtype.ext
      rw [h1]
      exact (gaussPair_val hc T x.rep).symm
    rw [← hx, ← hx', h2, Record.crossingOf_pair]

variable {S : Finset (Crossing P)}

/-- The self-crossings of `A` are the labels of the blocks it owns (same proof as the glue lemma
`carrierCrossings_eq_biUnion`, needed before the leaf). -/
theorem gl_carrierCrossings_eq_biUnion (hS : IsDecomposition hn hP S) (A : Component hn hP S) :
    carrierCrossings hn hP S A = (blocksOwnedBy hn hP S A).biUnion (CV.pieceLabels (cg hn hP) S) := by
  unfold blocksOwnedBy
  rw [CV.biUnion_pieceLabels_piecesOn _ (mem_Ind hn hP hS), geoCarrierCrossings_eq_generic,
    Equiv.apply_symm_apply]

theorem gl_exists_block_of_mem (hS : IsDecomposition hn hP S) (A : Component hn hP S) {c : Crossing P}
    (hc : c ∈ carrierCrossings hn hP S A) :
    ∃ H ∈ blocksOwnedBy hn hP S A, c ∈ CV.pieceLabels (cg hn hP) S H := by
  rw [gl_carrierCrossings_eq_biUnion hn hP hS A] at hc
  exact Finset.mem_biUnion.mp hc

theorem gl_pieceLabels_subset (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    {H : CV.Piece (cg hn hP) S} (hH : H ∈ blocksOwnedBy hn hP S A) :
    CV.pieceLabels (cg hn hP) S H ⊆ carrierCrossings hn hP S A := by
  rw [gl_carrierCrossings_eq_biUnion hn hP hS A]
  exact Finset.subset_biUnion_of_mem _ hH

theorem gl_mem_U_of_mem (hS : IsDecomposition hn hP S) (A : Component hn hP S) {c : Crossing P}
    (hc : c ∈ carrierCrossings hn hP S A) : c ∈ CV.U (cg hn hP) S := by
  obtain ⟨H, -, hcH⟩ := gl_exists_block_of_mem hn hP hS A hc
  exact CV.pieceLabels_subset _ S H hcH

/-- The geometric crossing ("label") of a record crossing of `D_A`: the label of its image chord in
`gaussRecord hc (carrierCrossings A)` under KL1's isomorphism. -/
noncomputable def gl_lbl (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    (p : (positiveLift hn hP S A hS).record.Crossing) : Crossing P :=
  label (cg hn hP) (carrierCrossings hn hP S A) (gl_crossingMap (positiveLiftRecordIso hn hP hS A) p)

theorem gl_lbl_mem (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    (p : (positiveLift hn hP S A hS).record.Crossing) : gl_lbl hn hP hS A p ∈ carrierCrossings hn hP S A :=
  label_mem _ _ _

theorem gl_lbl_mem_U (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    (p : (positiveLift hn hP S A hS).record.Crossing) : gl_lbl hn hP hS A p ∈ CV.U (cg hn hP) S :=
  gl_mem_U_of_mem hn hP hS A (gl_lbl_mem hn hP hS A p)

/-- The label of the chord of a shadow visit is its geometric crossing (KL1's spec). -/
theorem gl_lbl_crossingOf (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    (v : (positiveLift hn hP S A hS).Γ.Visit) :
    gl_lbl hn hP hS A ((positiveLift hn hP S A hS).record.crossingOf v) =
      (carrierCrossingEquiv hn hP S A hS v.1).val := by
  unfold gl_lbl
  rw [gl_crossingMap_crossingOf, label_crossingOf, positiveLiftRecordIso_val]

/-- Record interlacement of `D_A` is `Interlaces` of the labels (KL1 + KL2). -/
theorem gl_adj_iff (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    (p p' : (positiveLift hn hP S A hS).record.Crossing) :
    (positiveLift hn hP S A hS).record.interlacementGraph.Adj p p' ↔
      Interlaces hn hP (gl_lbl hn hP hS A p) (gl_lbl hn hP hS A p') := by
  rw [← gl_adj_map (positiveLiftRecordIso hn hP hS A), gaussRecord_adj_iff]
  exact Iff.rfl

theorem gl_lbl_injective (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    {p p' : (positiveLift hn hP S A hS).record.Crossing} (h : gl_lbl hn hP hS A p = gl_lbl hn hP hS A p') :
    p = p' :=
  (gl_crossingMap_inj (positiveLiftRecordIso hn hP hS A) p p').mp (gl_label_inj _ _ h)

theorem gl_exists_lbl_eq (hS : IsDecomposition hn hP S) (A : Component hn hP S) {c : Crossing P}
    (hc : c ∈ carrierCrossings hn hP S A) :
    ∃ p : (positiveLift hn hP S A hS).record.Crossing, gl_lbl hn hP hS A p = c := by
  let u : (gaussRecord (cg hn hP) (carrierCrossings hn hP S A)).M :=
    (⟨someVisit c, hc⟩ : {v : Visit P // v.1 ∈ carrierCrossings hn hP S A})
  refine ⟨(positiveLift hn hP S A hS).record.crossingOf ((positiveLiftRecordIso hn hP hS A).Φ.symm u), ?_⟩
  unfold gl_lbl
  rw [gl_crossingMap_crossingOf, Equiv.apply_symm_apply, label_crossingOf]
  rfl

/-- Membership in the block set of `D_A`'s chords is the label test. -/
theorem gl_mem_blockRecordCrossings_iff (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    (H : CV.Piece (cg hn hP) S) (p : (positiveLift hn hP S A hS).record.Crossing) :
    p ∈ blockRecordCrossings hn hP hS A H ↔ gl_lbl hn hP hS A p ∈ CV.pieceLabels (cg hn hP) S H := by
  constructor
  · rintro ⟨v, rfl, hv⟩
    rw [gl_lbl_crossingOf]
    exact hv
  · intro h
    refine ⟨(p.rep : (positiveLift hn hP S A hS).Γ.Visit), ((positiveLift hn hP S A hS).record.crossingOf_rep p).symm, ?_⟩
    rw [← gl_lbl_crossingOf hn hP hS A, (positiveLift hn hP S A hS).record.crossingOf_rep p]
    exact h

/-- The block of a record crossing of `D_A`: the piece of its label. -/
noncomputable def gl_piece (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    (p : (positiveLift hn hP S A hS).record.Crossing) : CV.Piece (cg hn hP) S :=
  CV.pieceOf (cg hn hP) S (gl_lbl hn hP hS A p) (gl_lbl_mem_U hn hP hS A p)

theorem gl_piece_mem (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    (p : (positiveLift hn hP S A hS).record.Crossing) : gl_piece hn hP hS A p ∈ blocksOwnedBy hn hP S A := by
  obtain ⟨H, hH, hcH⟩ := gl_exists_block_of_mem hn hP hS A (gl_lbl_mem hn hP hS A p)
  obtain ⟨hc, hpc⟩ := (CV.mem_pieceLabels _ S H _).mp hcH
  have h : gl_piece hn hP hS A p = H := hpc
  rw [h]
  exact hH

theorem gl_piece_eq_of_adj (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    {p p' : (positiveLift hn hP S A hS).record.Crossing}
    (h : (positiveLift hn hP S A hS).record.interlacementGraph.Adj p p') :
    gl_piece hn hP hS A p = gl_piece hn hP hS A p' := by
  have hI : Interlaces hn hP (gl_lbl hn hP hS A p) (gl_lbl hn hP hS A p') := (gl_adj_iff hn hP hS A p p').mp h
  have hadj : (CV.residualGraph (cg hn hP) S).Adj ⟨gl_lbl hn hP hS A p, gl_lbl_mem_U hn hP hS A p⟩
      ⟨gl_lbl hn hP hS A p', gl_lbl_mem_U hn hP hS A p'⟩ := hI
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj

theorem gl_piece_eq_of_walk (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    {p p' : (positiveLift hn hP S A hS).record.Crossing}
    (w : (positiveLift hn hP S A hS).record.interlacementGraph.Walk p p') :
    gl_piece hn hP hS A p = gl_piece hn hP hS A p' := by
  induction w with
  | nil => rfl
  | cons h _ ih => exact (gl_piece_eq_of_adj hn hP hS A h).trans ih

/-- The block of a record block of `D_A` (well defined: adjacent chords have interlacing labels, hence
lie in one piece). -/
noncomputable def gl_pieceOfComp (hS : IsDecomposition hn hP S) (A : Component hn hP S) :
    (positiveLift hn hP S A hS).record.interlacementGraph.ConnectedComponent → CV.Piece (cg hn hP) S :=
  SimpleGraph.ConnectedComponent.lift (gl_piece hn hP hS A) fun _ _ w _ => gl_piece_eq_of_walk hn hP hS A w

theorem gl_pieceOfComp_mk (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    (p : (positiveLift hn hP S A hS).record.Crossing) :
    gl_pieceOfComp hn hP hS A ((positiveLift hn hP S A hS).record.interlacementGraph.connectedComponentMk p) =
      gl_piece hn hP hS A p := rfl

theorem gl_pieceOfComp_mem (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    (K : (positiveLift hn hP S A hS).record.interlacementGraph.ConnectedComponent) :
    gl_pieceOfComp hn hP hS A K ∈ blocksOwnedBy hn hP S A := by
  induction K using SimpleGraph.ConnectedComponent.ind with
  | h p => exact gl_piece_mem hn hP hS A p

/-- A walk of `G_P[U(S)]` between two labels of `D_A` lifts to a walk of its record interlacement graph
(the walk stays in one block owned by `A`, whose labels are self-crossings of `A`; `owner_eq_of_walk`
pattern). -/
theorem gl_reachable_of_walk (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    {x y : (↑(CV.U (cg hn hP) S) : Set (Crossing P))} (w : (CV.residualGraph (cg hn hP) S).Walk x y) :
    ∀ p p' : (positiveLift hn hP S A hS).record.Crossing, gl_lbl hn hP hS A p = x.1 →
      gl_lbl hn hP hS A p' = y.1 →
      (positiveLift hn hP S A hS).record.interlacementGraph.Reachable p p' := by
  induction w with
  | nil =>
    intro p p' hp hp'
    obtain rfl := gl_lbl_injective hn hP hS A (hp.trans hp'.symm)
    exact SimpleGraph.Reachable.refl p
  | @cons a b _ hab _ ih =>
    intro p p' hp hp'
    have haX : a.1 ∈ carrierCrossings hn hP S A := hp ▸ gl_lbl_mem hn hP hS A p
    obtain ⟨H, hH, haH⟩ := gl_exists_block_of_mem hn hP hS A haX
    have hbH : b.1 ∈ CV.pieceLabels (cg hn hP) S H := CV.mem_pieceLabels_of_interlaces _ H haH b.2 hab
    obtain ⟨p₁, hp₁⟩ := gl_exists_lbl_eq hn hP hS A (gl_pieceLabels_subset hn hP hS A hH hbH)
    have hadj : (positiveLift hn hP S A hS).record.interlacementGraph.Adj p p₁ := by
      rw [gl_adj_iff hn hP hS A, hp, hp₁]
      exact hab
    exact hadj.reachable.trans (ih p₁ p' hp₁ hp')

theorem gl_pieceOfComp_injective (hS : IsDecomposition hn hP S) (A : Component hn hP S) :
    Function.Injective (gl_pieceOfComp hn hP hS A) := by
  intro K K'
  refine SimpleGraph.ConnectedComponent.ind₂ (fun p p' => ?_) K K'
  intro h
  have hr : (CV.residualGraph (cg hn hP) S).Reachable ⟨gl_lbl hn hP hS A p, gl_lbl_mem_U hn hP hS A p⟩
      ⟨gl_lbl hn hP hS A p', gl_lbl_mem_U hn hP hS A p'⟩ :=
    SimpleGraph.ConnectedComponent.exact h
  exact SimpleGraph.ConnectedComponent.sound (hr.elim fun w => gl_reachable_of_walk hn hP hS A w p p' rfl rfl)

theorem gl_pieceOfComp_surj (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    (H : CV.Piece (cg hn hP) S) (hH : H ∈ blocksOwnedBy hn hP S A) :
    ∃ K, gl_pieceOfComp hn hP hS A K = H := by
  obtain ⟨c, hcH⟩ := CV.pieceLabels_nonempty (cg hn hP) S H
  obtain ⟨p, hp⟩ := gl_exists_lbl_eq hn hP hS A (gl_pieceLabels_subset hn hP hS A hH hcH)
  refine ⟨(positiveLift hn hP S A hS).record.interlacementGraph.connectedComponentMk p, ?_⟩
  obtain ⟨hc, hpc⟩ := (CV.mem_pieceLabels _ S H c).mp hcH
  subst hp
  exact hpc

/-- The bijection between the record blocks of `D_A` and the blocks owned by `A`. -/
noncomputable def gl_blockEquiv (hS : IsDecomposition hn hP S) (A : Component hn hP S) :
    (positiveLift hn hP S A hS).record.interlacementGraph.ConnectedComponent ≃
      {H : CV.Piece (cg hn hP) S // H ∈ blocksOwnedBy hn hP S A} :=
  Equiv.ofBijective (fun K => ⟨gl_pieceOfComp hn hP hS A K, gl_pieceOfComp_mem hn hP hS A K⟩)
    ⟨fun _ _ h => gl_pieceOfComp_injective hn hP hS A (congrArg Subtype.val h),
      fun H => by
        obtain ⟨K, hK⟩ := gl_pieceOfComp_surj hn hP hS A H.1 H.2
        exact ⟨K, Subtype.ext hK⟩⟩

theorem gl_blockEquiv_val (hS : IsDecomposition hn hP S) (A : Component hn hP S)
    (K : (positiveLift hn hP S A hS).record.interlacementGraph.ConnectedComponent) :
    (gl_blockEquiv hn hP hS A K).1 = gl_pieceOfComp hn hP hS A K := rfl

end GLHelpers

/-- GL leaf: the connected components of the record interlacement graph of `D_A` correspond to the blocks
owned by `A`, with supports the record crossings of the block's labels (KL1 + KL2 + `owner_eq_of_walk`). -/
theorem exists_blockGraphEquiv {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (A : Component hn hP S) :
    ∃ β : (positiveLift hn hP S A hS).record.interlacementGraph.ConnectedComponent ≃
        {H : CV.Piece (cg hn hP) S // H ∈ blocksOwnedBy hn hP S A},
      ∀ K, K.supp = blockRecordCrossings hn hP hS A (β K).1 := by
  refine ⟨gl_blockEquiv hn hP hS A, fun K => ?_⟩
  induction K using SimpleGraph.ConnectedComponent.ind with
  | h p₀ =>
    ext p
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, gl_blockEquiv_val, gl_mem_blockRecordCrossings_iff,
      gl_pieceOfComp_mk, CV.mem_pieceLabels]
    constructor
    · intro h
      exact ⟨gl_lbl_mem_U hn hP hS A p, congrArg (gl_pieceOfComp hn hP hS A) h⟩
    · rintro ⟨hc, h⟩
      have h' : gl_pieceOfComp hn hP hS A
          ((positiveLift hn hP S A hS).record.interlacementGraph.connectedComponentMk p) =
          gl_pieceOfComp hn hP hS A
            ((positiveLift hn hP S A hS).record.interlacementGraph.connectedComponentMk p₀) := h
      exact gl_pieceOfComp_injective hn hP hS A h'

/-! ### AS — small assembly leaves -/

/-- AS leaf: membership of a chord of `D_A` in the block set is the label test on its occurrence
(both occurrences of a shadow crossing have the same geometric crossing). -/
theorem mem_blockRecordCrossings_crossingOf {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (A : Component hn hP S) (H : CV.Piece (cg hn hP) S) (v : (positiveLift hn hP S A hS).Γ.Visit) :
    (positiveLift hn hP S A hS).record.crossingOf v ∈ blockRecordCrossings hn hP hS A H ↔
      (carrierCrossingEquiv hn hP S A hS v.1).val ∈ CV.pieceLabels (cg hn hP) S H := sorry

/-- AS leaf: a carrier with a self-crossing has a shadow visit (`carrierCrossingEquiv.symm`, one of its two
strands). -/
theorem exists_visit_of_mem_carrierCrossings {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (A : Component hn hP S) {c : Crossing P} (hc : c ∈ carrierCrossings hn hP S A) :
    Nonempty (positiveLift hn hP S A hS).Γ.Visit := sorry

/-! ### PC — the block carrier: an independent refinement `T ⊇ S` with a carrier whose self-crossings are
exactly `H` (proved here from CV:lem:piececurve's `pieceSupport`/`pieceCarrier`, rows 142/143 under review;
fallback: PLAN_B's greedy support L3 on the SM lane) -/

theorem exists_blockCarrier {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (H : CV.Piece (cg hn hP) S) :
    ∃ (T : Finset (Crossing P)) (hT : IsDecomposition hn hP T) (q : Component hn hP T),
      S ⊆ T ∧ carrierCrossings hn hP T q = CV.pieceLabels (cg hn hP) S H := by
  have hD : CV.Diagrammatic P := CV.Generic.diagrammatic hn (CV.generic_of_sm hn hP)
  have hInd : S ∈ CV.Ind hD.crossingGeometry := mem_Ind hn hP hS
  refine ⟨S ∪ CV.pieceSupport hD hInd H, ?_, geoComponentEquivGeneric hn hP _ (CV.pieceCarrier hD hInd H),
    Finset.subset_union_left, ?_⟩
  · have h := CV.pieceSupport_mem_Ind hD hInd H
    rwa [CV.Ind_eq_generic hn hP] at h
  · rw [← geoCarrierCrossings_eq_generic]
    exact CV.pieceCarrier_geoCarrierCrossings hD hInd H

/-! ### Proved glue (no leaves) -/

section Glue

variable {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)

/-- "`H` owned by `A`" spelled out (field `owned_by`). -/
theorem mem_blocksOwnedBy_iff (A : Component hn hP S) (H : CV.Piece (cg hn hP) S) :
    H ∈ blocksOwnedBy hn hP S A ↔
      ∀ c ∈ CV.pieceLabels (cg hn hP) S H, ∀ v : Visit P, v.1 = c → owner hn hP S (Sum.inr v) = A := by
  unfold blocksOwnedBy CV.piecesOn
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  refine forall_congr' fun c => forall_congr' fun _ => forall_congr' fun v => forall_congr' fun _ => ?_
  rw [← geoComponentEquivGeneric_owner hn hP S]
  exact Equiv.eq_symm_apply _

theorem mem_blocksOwnedBy_iff_blockOwner (A : Component hn hP S) (H : CV.Piece (cg hn hP) S) :
    H ∈ blocksOwnedBy hn hP S A ↔ blockOwner hn hP hS H = A := by
  unfold blocksOwnedBy blockOwner
  rw [CV.mem_piecesOn_iff (cg hn hP) (mem_Ind hn hP hS)]
  exact Equiv.eq_symm_apply _

theorem blockOwner_eq_of_mem {A : Component hn hP S} {H : CV.Piece (cg hn hP) S}
    (h : H ∈ blocksOwnedBy hn hP S A) : blockOwner hn hP hS H = A :=
  (mem_blocksOwnedBy_iff_blockOwner hn hP hS A H).mp h

include hS in
/-- The self-crossings of `A` are the labels of the blocks it owns ("The self-crossings of a carrier are
exactly its owned undominated labels", proof 4653; CV `biUnion_pieceLabels_piecesOn`). -/
theorem carrierCrossings_eq_biUnion (A : Component hn hP S) :
    carrierCrossings hn hP S A = (blocksOwnedBy hn hP S A).biUnion (CV.pieceLabels (cg hn hP) S) := by
  unfold blocksOwnedBy
  rw [CV.biUnion_pieceLabels_piecesOn _ (mem_Ind hn hP hS), geoCarrierCrossings_eq_generic,
    Equiv.apply_symm_apply]

/-- The labels of `H` are self-crossings of its owner. -/
theorem pieceLabels_subset_carrierCrossings (H : CV.Piece (cg hn hP) S) :
    CV.pieceLabels (cg hn hP) S H ⊆ carrierCrossings hn hP S (blockOwner hn hP hS H) := by
  intro c hc
  rw [carrierCrossings_eq_biUnion hn hP hS, Finset.mem_biUnion]
  exact ⟨H, (mem_blocksOwnedBy_iff_blockOwner hn hP hS _ H).mpr rfl, hc⟩

/-- `blockRecord H` at the owner `A` of `H`, written at `A`. -/
theorem blockRecord_eq_at {A : Component hn hP S} {H : CV.Piece (cg hn hP) S} (h : blockOwner hn hP hS H = A) :
    blockRecord hn hP hS H =
      (positiveLift hn hP S A hS).record.restrictCrossings (blockRecordCrossings hn hP hS A H) := by
  subst h; rfl

/-- **The record clause for every block carrier diagram**: the actual positive diagram of any carrier of an
independent `T` whose self-crossings are exactly `H` has the restricted named cyclic record of `H`
(KL1 at `q`, KL1 at `A_H`, KL3, T1). -/
theorem record_iso_blockRecord {T : Finset (Crossing P)} (hT : IsDecomposition hn hP T) (q : Component hn hP T)
    (H : CV.Piece (cg hn hP) S) (hq : carrierCrossings hn hP T q = CV.pieceLabels (cg hn hP) S H) :
    Nonempty (RecordIso (positiveLift hn hP T q hT).record (blockRecord hn hP hS H)) := by
  have ιH := positiveLiftRecordIso hn hP hT q
  rw [hq] at ιH
  obtain ⟨κ⟩ := gaussRecord_restrict_iso (cg hn hP) (pieceLabels_subset_carrierCrossings hn hP hS H)
  obtain ⟨τ⟩ := restrictCrossings_iso_of_recordIso (positiveLiftRecordIso hn hP hS (blockOwner hn hP hS H))
    (blockRecordCrossings hn hP hS (blockOwner hn hP hS H) H)
    {p | label (cg hn hP) _ p ∈ CV.pieceLabels (cg hn hP) S H} (fun v => by
      rw [mem_blockRecordCrossings_crossingOf, Set.mem_setOf_eq,
        label_crossingOf (cg hn hP) _ ((positiveLiftRecordIso hn hP hS (blockOwner hn hP hS H)).Φ v),
        positiveLiftRecordIso_val])
  exact ⟨ιH.trans (κ.symm.trans τ.symm)⟩

/-- eq. cb:product, first identity, given the block diagrams (assembly through the accepted `SM.blocks`). -/
theorem product_of_chain (A : Component hn hP S) (hne : (blocksOwnedBy hn hP S A).Nonempty)
    (hbd : ∀ H : CV.Piece (cg hn hP) S, ∃ D : Diagram,
      IsBlockCarrierDiagram hn hP hS H D ∧ Nonempty (RecordIso D.record (blockRecord hn hP hS H))) :
    carrierPoly hn hP hS A = ∏ H ∈ blocksOwnedBy hn hP S A, blockPoly hn hP hS H := by
  obtain ⟨β, hβ⟩ := exists_blockGraphEquiv hn hP hS A
  choose D hD using hbd
  let C : (positiveLift hn hP S A hS).record.interlacementGraph.ConnectedComponent → Diagram :=
    fun K => D (β K).1
  have hsup : BlockSupply (positiveLift hn hP S A hS).record C := by
    refine ⟨⟨positiveLift hn hP S A hS, ⟨RecordIso.refl _⟩⟩, ?_, ?_, fun K => ?_⟩
    · exact Fintype.card_fin 1
    · obtain ⟨H, hH⟩ := hne
      obtain ⟨c, hc⟩ := CV.pieceLabels_nonempty (cg hn hP) S H
      have hcA : c ∈ carrierCrossings hn hP S A := by
        rw [carrierCrossings_eq_biUnion hn hP hS, Finset.mem_biUnion]
        exact ⟨H, hH, hc⟩
      exact exists_visit_of_mem_carrierCrossings hn hP hS A hcA
    · obtain ⟨ι⟩ := (hD (β K).1).2
      rw [blockRecord_eq_at hn hP hS (blockOwner_eq_of_mem hn hP hS (β K).2), ← hβ K] at ι
      exact ⟨ι⟩
  have hprod := SM.blocks.product _ C hsup (positiveLift hn hP S A hS) ⟨RecordIso.refl _⟩
  have hfac : ∀ K, SM.P (C K) = blockPoly hn hP hS (β K).1 :=
    fun K => (recordPolynomial_eq _ _ (hD (β K).1).2).symm
  show SM.P (positiveLift hn hP S A hS) = _
  rw [hprod, Fintype.prod_equiv β _ (fun H => blockPoly hn hP hS H.1) hfac]
  exact Finset.prod_coe_sort _ _

include hS in
/-- eq. cb:product, second identity. -/
theorem count_of_chain (A : Component hn hP S) :
    carrierCrossingCount hn hP S A = ∑ H ∈ blocksOwnedBy hn hP S A, (CV.pieceLabels (cg hn hP) S H).card := by
  show (carrierCrossings hn hP S A).card = _
  rw [carrierCrossings_eq_biUnion hn hP hS, Finset.card_biUnion]
  intro H _ H' _ hne
  exact CV.pieceLabels_disjoint _ S H H' hne

end Glue

end CB

open CB

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {S : Finset (Crossing P)}

/-- **Row 101, cb:blocks** — assembled (every field an accepted fact). -/
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

/-- **Row 102, cb:products** — assembled from the chain leaves. -/
theorem cb_products (hS : IsDecomposition hn hP S) : CbProductsData hn hP hS where
  one_owner H := by
    refine ⟨?_, fun c hc => ?_⟩
    · obtain ⟨q, hq, huniq⟩ := CV.exists_unique_piece_carrier (cg hn hP) (mem_Ind hn hP hS) H
      refine ⟨geoComponentEquivGeneric hn hP S q, fun c hc v hv => ?_, fun q' hq' => ?_⟩
      · rw [← geoComponentEquivGeneric_owner hn hP S]
        exact congrArg _ (hq c hc v hv)
      · have h : (geoComponentEquivGeneric hn hP S).symm q' = q :=
          huniq _ fun c hc v hv => by
            rw [Equiv.eq_symm_apply, geoComponentEquivGeneric_owner hn hP S]
            exact hq' c hc v hv
        rw [← h, Equiv.apply_symm_apply]
    · show owner hn hP S (Sum.inr (someVisit c)) = _
      unfold blockOwner
      rw [← geoComponentEquivGeneric_owner hn hP S]
      exact congrArg _ (CV.pieceOwner_spec (cg hn hP) (mem_Ind hn hP hS) H c hc (someVisit c) rfl)
  block_diagram H := by
    obtain ⟨T, hT, q, hST, hq⟩ := exists_blockCarrier hn hP hS H
    exact ⟨positiveLift hn hP T q hT, ⟨T, hT, q, hST, hq, rfl⟩, record_iso_blockRecord hn hP hS hT q H hq⟩
  polynomial_independent H D hD := by
    obtain ⟨T, hT, q, -, hq, rfl⟩ := hD
    have ι := record_iso_blockRecord hn hP hS hT q H hq
    exact ⟨ι, (recordPolynomial_eq _ _ ι).symm⟩
  owned_by A H := ⟨mem_blocksOwnedBy_iff hn hP A H, mem_blocksOwnedBy_iff_blockOwner hn hP hS A H⟩
  product A := by
    rcases (blocksOwnedBy hn hP S A).eq_empty_or_nonempty with h | h
    · rw [h, Finset.prod_empty]
      have hX : carrierCrossings hn hP S A = ∅ := by
        rw [carrierCrossings_eq_biUnion hn hP hS, h, Finset.biUnion_empty]
      exact P_circle (positiveLift_isCrossingFreeCircle hn hP S A hS hX)
    · exact product_of_chain hn hP hS A h fun H => by
        obtain ⟨T, hT, q, hST, hq⟩ := exists_blockCarrier hn hP hS H
        exact ⟨positiveLift hn hP T q hT, ⟨T, hT, q, hST, hq, rfl⟩, record_iso_blockRecord hn hP hS hT q H hq⟩
  count A := count_of_chain hn hP hS A
  no_blocks A h := by
    have hX : carrierCrossings hn hP S A = ∅ := by
      rw [carrierCrossings_eq_biUnion hn hP hS, h, Finset.biUnion_empty]
    refine ⟨positiveLift_isCrossingFreeCircle hn hP S A hS hX,
      P_circle (positiveLift_isCrossingFreeCircle hn hP S A hS hX), ?_⟩
    show (carrierCrossings hn hP S A).card = 0
    rw [hX, Finset.card_empty]

/-! ### Companion lemmas cited by cb:singleton (proof sentences of cb:products, NOT row clauses) -/

omit [NeZero n] in
/-- "It is adjacent to no selected label, so the enlarged support is independent" (proof 4658–4660;
accepted `insert_unselected_mem_independentSupports`). -/
theorem greedy_independent (hS : IsDecomposition hn hP S) {c : Crossing P}
    (hc : c ∈ supportUnselected hn hP S) : IsDecomposition hn hP (insert c S) :=
  insert_unselected_mem_independentSupports hn hP hS hc

omit [NeZero n] in
/-- eq. cb:greedy-step (proof 4661–4663): `U(T ∪ {c}) = U(T) ∖ ({c} ∪ N_{G_P}(c))`. -/
theorem greedy_step (T : Finset (Crossing P)) (c : Crossing P) :
    supportUnselected hn hP (insert c T) =
      supportUnselected hn hP T \ insert c (supportNeighbors hn hP {c}) := by
  ext y
  simp only [mem_supportUnselected, mem_supportNeighbors, Finset.mem_sdiff, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hy, hN⟩
    refine ⟨⟨fun h => hy (Or.inr h), fun ⟨x, hx, hxy⟩ => hN ⟨x, Or.inr hx, hxy⟩⟩, ?_⟩
    rintro (rfl | ⟨x, rfl, hxy⟩)
    · exact hy (Or.inl rfl)
    · exact hN ⟨x, Or.inl rfl, hxy⟩
  · rintro ⟨⟨hy, hN⟩, hc⟩
    refine ⟨?_, ?_⟩
    · rintro (rfl | h)
      · exact hc (Or.inl rfl)
      · exact hy h
    · rintro ⟨x, hx | hx, hxy⟩
      · exact hc (Or.inr ⟨x, hx, hxy⟩)
      · exact hN ⟨x, hx, hxy⟩

end SM
