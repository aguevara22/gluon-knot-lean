import SM.FlatSides
import SM.CarriersLemma
import SM.UniformDefinition
import SM.SmoothingDefinition

/-! Source def:flat-carriers (reference/SM/sm-3-statesum.tex:788-804, frame SM15) and
cor:flat-carriers (sm-3-statesum.tex:805-835, proof 836-913), both "under the hypotheses of
Lemma lem:flat-sides" (sm-1-polygons.tex:778-826, accepted as `SM.flat_sides : … →
FlatSidesData hn g j hz hb hc`, SM/FlatSides.lean). Main declarations:
`SM.flat_carriers_definition` (def row) and `SM.flat_carriers` (cor row). Statement draft, tag A
(transport design); proofs are `sorry`.

Notation. `g : WallGerm (n + 1)` (`n ≥ 3`, so the printed size `N = n + 1 ≥ 4`) is the flat wall
germ of lem:flat-sides; `g.center = P(0)` is the flat centre, `(g.sideTuple b t).val = P(±t)` the
two generic sides (`b = true`: positive parameter, `b = false`: negative parameter; which of them
is the *right* side is decided by the turn at `j`, `IsRightSide`: `τ_j = -1`, a right turn, and
`IsLeftSide`: `τ_j = 1`), and `deleteVertex g.center j = Q = P(0) ∖ j` the deletion (an `n`-gon,
generic by lem:flat-sides (iii)). `j` is the flat vertex, `μ_j = g.center j`.

The four configurations and their marks. The marked traversal circle of a polygon `P` is
`Carrier.Mark P = ZMod m ⊕ Visit P` (every original vertex and every crossing visit, def:smoothing,
conv:selected-visits). The common cyclic Gauss word of lem:flat-sides (ii) is realised by the
equality of crossing supports `CommonSupports g t : ∀ b s, IsCrossing g.center s ↔
IsCrossing (g.sideTuple b t).val s` (the `hs` of `GeometricRecordsAgree` centre ↔ side in
`FlatSidesData`), which identifies visits by `visitTransport (hs b)` (same crossing support, same
visited edge) and marks by `markTransport (hs b) : Mark g.center ≃ Mark P(±t)`; the common word
of (iii) is realised by the fused-edge bijections `fusionCrossingEquiv`/`fusionVisitEquiv`
(`FlatFusionData`), extended to marks by `deletionMark` (vertex `i ≠ j` ↦ vertex `fusionIndex j i`
of `Q`; `μ_j` has no image and is sent to a junk vertex never used).

The carriers. On a generic side the carriers of `S` are those of def:smoothing:
`Carrier.Component (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S)` (cycles of
`ρ_S = smoothingSuccessor`), traced by `componentPlaneCycle`, with corner polygon
`ccpCornerPolygon` (lem:carriers). On the deletion they are the same accepted objects for the
generic `n`-gon `Q` and the fused support `deletionSupport`. At the centre, which is NOT generic,
the same words define them by TRANSPORT (the printed proof, sm-3:837-840: "The common cyclic word
identifies the visits and the successor permutation before smoothing. Exchanging the same
selected successors in that permutation gives the same cycles afterwards."): the centre's marks
are the side's marks under `markTransport`, the centre's successor is the side's `ρ`
(certified intrinsic by the field `centre_successor`: no centre mark lies strictly between a mark
and its `ρ`-successor on the centre circle, positions `geometricMarkPosition` read from the
segments of `P(0)` as in lem:flat-sides (ii)), the reconnection is the same swap of selected
visits (`centre_reconnection`), and the centre carrier of the cycle `q` is the closed polygonal
cycle `centrePlaneCycle` through the centre points `centreMarkPoint` of its marks in inherited
order, with corner polygon `centreCornerPolygon` (the centre points of the corner marks
`ccpCornerMark`). So a centre carrier is indexed by the side carrier it corresponds to; the field
`centre_side_independent` certifies that the two sides give the same centre family.

Carrier correspondences (cor (i) "under their named traversal arcs") are the maps `carrierMap`
induced by the mark identifications: `sideToSide br (!br)` (right ↔ left) and `sideToDeletion`
(side, hence centre, ↔ deletion), sending a carrier to the carrier of the image of any of its
marks (`Quotient.out`); cor (i) asserts they are bijections compatible with `owner`. The carrier
through `μ_j` is `muCarrier = owner (Sum.inl j)`. A carrier's selector (cor (iii)) is
`carrierSelector = cornerSelector ∘ ccpCornerPolygon` with `cornerSelector Q = 1` if all turns of
`Q` are right (`turn = -1`), `(-1)^c` if all its `c` turns are left (`turn = 1`), `0` otherwise
(`c` = number of corners = number of turns). Rotation: `rotationNumber` (lem:rot, def:uniform). -/

namespace SM

open Carrier

attribute [local instance] Classical.propDecidable

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## 1. Marks of polygons with a common crossing set; marks without genericity -/

/-- The identification of the marked traversal circles of two polygons with the same crossing
supports (the common cyclic Gauss word): vertex `i ↦ i`, visit `v ↦ visitTransport hs v` (same
support, same visited edge). -/
def markTransport {P Q : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) :
    Mark P ≃ Mark Q :=
  Equiv.sumCongr (Equiv.refl (ZMod n)) (visitTransport hs)

/-- The traversal position of a mark of a polygon with crossing geometry, no genericity assumed:
vertex `i` at parameter `0` of its outgoing edge, a visit at its own crossing parameter on its
visited edge (lem:flat-sides (ii): "read from the segments of `P(0)` exactly as for a generic
polygon"). On a generic polygon this is `Carrier.markPosition` (definitionally). -/
def geometricMarkPosition {P : LabelledTuple n} (h : CrossingGeometry P) :
    Mark P → TraversalPoint n
  | Sum.inl i => (i, ⟨0, by norm_num⟩)
  | Sum.inr v => geometricVisitPosition h v

/-- The plane point of a mark under crossing geometry: the vertex, resp. the crossing point. -/
def geometricMarkPoint {P : LabelledTuple n} (h : CrossingGeometry P) (a : Mark P) : Plane :=
  traversalEvaluation P (geometricMarkPosition h a)

/-- The plane point of a mark of a generic polygon (`traversalEvaluation ∘ markPosition`). -/
def markPoint (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (a : Mark P) : Plane :=
  traversalEvaluation P (markPosition hn hP.1 a)

/-- The carrier-to-carrier map induced by a map of marks `T`: the carrier (of the target
smoothing) of the image of any mark of `q`. Cor (i) asserts, for the mark identifications of the
flat configurations, that this is a bijection with `carrierMap T (owner a) = owner (T a)`. -/
def carrierMap {m k : ℕ} [NeZero m] [NeZero k] (hm : 3 ≤ m) (hk : 3 ≤ k)
    {P : LabelledTuple m} {Q : LabelledTuple k} (hP : Generic P) (hQ : Generic Q)
    (S : Finset (Crossing P)) (S' : Finset (Crossing Q)) (T : Mark P → Mark Q)
    (q : Component hm hP S) : Component hk hQ S' :=
  owner hk hQ S' (T (Quotient.out q))

/-- cor:flat-carriers (iii): the selector of a closed polygon `Q` with `k` corners: `1` if all its
turns are right (`turn = -1`), `(-1)^k` if all its `k` turns are left (`turn = 1`), `0` if mixed. -/
def cornerSelector {k : ℕ} [NeZero k] (Q : LabelledTuple k) : ℤ :=
  if ∀ i, turn Q i = -1 then 1 else if ∀ i, turn Q i = 1 then (-1 : ℤ) ^ k else 0

/-- The selector of a carrier: the selector of its corner polygon (`c = ccpCornerCount`). -/
def carrierSelector (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : ℤ :=
  cornerSelector (ccpCornerPolygon hn hP S q)

/-! ## 2. The four flat configurations -/

omit [NeZero n] in
/-- The parent size `n + 1 ≥ 4` of lem:flat-sides satisfies the carrier lemmas' `3 ≤ ·`. -/
theorem flat_hn1 (hn : 3 ≤ n) : 3 ≤ n + 1 := Nat.le_succ_of_le hn

omit [NeZero n] in
/-- The crossing geometry of the flat centre `P(0)` (lem:flat-sides (ii); accepted
`flat_crossingGeometry`): the centre's crossings, visits and their positions are read from the
segments of `P(0)` with no genericity. -/
theorem flatCentreGeometry (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) : CrossingGeometry g.center :=
  flat_crossingGeometry (by omega) hz hb hc

/-- The deletion `Q = P(0) ∖ j` is generic (lem:flat-sides (iii); accepted
`generic_deleteVertex`). -/
theorem flatDeletionGeneric (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) : Generic (deleteVertex g.center j) :=
  generic_deleteVertex hn hz hb hc

/-- The common crossing supports of the centre and of both sides at the side parameter `t`
(lem:flat-sides (ii): "the set of remote edge pairs that cross is constant, including at zero").
This is the `hs` of `GeometricRecordsAgree` in `FlatSidesData`, for both sides. -/
abbrev CommonSupports (g : WallGerm (n + 1)) (t : g.SideParameter) : Prop :=
  ∀ (b : Bool) (s : Finset (ZMod (n + 1))),
    IsCrossing g.center s ↔ IsCrossing (g.sideTuple b t).val s

/-- The right side: the side on which the turn at `j` is a right turn (`τ_j = -1`). -/
def IsRightSide (g : WallGerm (n + 1)) (j : ZMod (n + 1)) (b : Bool) (t : g.SideParameter) :
    Prop :=
  turn (g.sideTuple b t).val j = -1

/-- The left side: the side on which the turn at `j` is a left turn (`τ_j = 1`). -/
def IsLeftSide (g : WallGerm (n + 1)) (j : ZMod (n + 1)) (b : Bool) (t : g.SideParameter) :
    Prop :=
  turn (g.sideTuple b t).val j = 1

/-- The independent set `S` (fixed at the centre) read on the side `b`. -/
def sideSupport (g : WallGerm (n + 1)) (t : g.SideParameter) (hs : CommonSupports g t)
    (b : Bool) (S : Finset (Crossing g.center)) : Finset (Crossing (g.sideTuple b t).val) :=
  S.map (crossingTransport (hs b)).toEmbedding

/-- The independent set `S` read on the deletion through the fused-edge bijection. -/
def deletionSupport (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center)) :
    Finset (Crossing (deleteVertex g.center j)) :=
  S.map (fusionCrossingEquiv hn hz hb hc).toEmbedding

/-- **The carriers of `S` on the side `b`** (def:smoothing): the cycles of `ρ_S`. -/
abbrev SideCarrier (hn : 3 ≤ n) (g : WallGerm (n + 1)) (t : g.SideParameter)
    (hs : CommonSupports g t) (b : Bool) (S : Finset (Crossing g.center)) : Type :=
  Component (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S)

/-- **The carriers of `S` on the deletion** (def:smoothing on the generic `n`-gon `Q`). -/
abbrev DeletionCarrier (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center)) : Type :=
  Component hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S)

/-- The carrier through `μ_j` on the side `b`: the owner of the vertex mark `j`. -/
def muCarrier (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1)) (t : g.SideParameter)
    (hs : CommonSupports g t) (b : Bool) (S : Finset (Crossing g.center)) :
    SideCarrier hn g t hs b S :=
  owner (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) (Sum.inl j)

/-! ## 3. The centre configuration by transport from a side -/

/-- The centre position of a side mark: the same vertex, resp. the identified visit, at its
position on the centre's traversal circle (`geometricMarkPosition` of `P(0)`). -/
def centreMarkPosition (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t) (b : Bool)
    (a : Mark (g.sideTuple b t).val) : TraversalPoint (n + 1) :=
  geometricMarkPosition (flatCentreGeometry hn g hz hb hc) ((markTransport (hs b)).symm a)

/-- The centre point of a side mark: the centre vertex `μ_i`, resp. the centre crossing point. -/
def centreMarkPoint (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t) (b : Bool)
    (a : Mark (g.sideTuple b t).val) : Plane :=
  traversalEvaluation g.center (centreMarkPosition hn g hz hb hc t hs b a)

/-- The inherited straight subsegment of the centre from a mark to its `ρ_S`-successor. -/
def centreSegment (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t) (b : Bool)
    (S : Finset (Crossing g.center)) (a : Mark (g.sideTuple b t).val) (u : ℝ) : Plane :=
  centreMarkPoint hn g hz hb hc t hs b a +
    u • (centreMarkPoint hn g hz hb hc t hs b
      (smoothingSuccessor (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) a) -
      centreMarkPoint hn g hz hb hc t hs b a)

/-- **The carrier of `S` at the centre** corresponding to the side carrier `q`: the closed
polygonal cycle through the centre points of the marks of `q` in inherited cyclic order. -/
def centrePlaneCycle (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t) (b : Bool)
    (S : Finset (Crossing g.center)) (q : SideCarrier hn g t hs b S) : Cycle Plane :=
  ((componentMarkList (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q).map
    (centreMarkPoint hn g hz hb hc t hs b) : Cycle Plane)

/-- The corner polygon of the centre carrier of `q`: the centre points of the corner marks of
`q` (original vertices and selected visits) in inherited cyclic order. -/
def centreCornerPolygon (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t) (b : Bool)
    (S : Finset (Crossing g.center)) (q : SideCarrier hn g t hs b S) :
    LabelledTuple (ccpCornerCount (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q) :=
  fun k => centreMarkPoint hn g hz hb hc t hs b
    (ccpCornerMark (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q k)

/-- The retained (unselected, both visits owned) crossings of the centre carrier of `q`, as
crossings of the centre. -/
def centreCarrierCrossings (hn : 3 ≤ n) (g : WallGerm (n + 1)) (t : g.SideParameter)
    (hs : CommonSupports g t) (b : Bool) (S : Finset (Crossing g.center))
    (q : SideCarrier hn g t hs b S) : Finset (Crossing g.center) :=
  (carrierCrossings (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q).map
    (crossingTransport (hs b)).symm.toEmbedding

/-! ## 4. The mark identifications and the carrier correspondences -/

/-- Marks of the side `b` identified with marks of the side `b'` through the centre. -/
def sideMarkTransport (g : WallGerm (n + 1)) (t : g.SideParameter) (hs : CommonSupports g t)
    (b b' : Bool) (a : Mark (g.sideTuple b t).val) : Mark (g.sideTuple b' t).val :=
  markTransport (hs b') ((markTransport (hs b)).symm a)

/-- Marks of the centre identified with marks of the deletion through the fused-edge bijection:
vertex `i ≠ j ↦` vertex `fusionIndex j i` of `Q` (the same point of the plane), visit `v ↦
fusionVisitEquiv v` (the same crossing point). The deleted vertex `μ_j` has no counterpart; its
value here (`Sum.inl (-1)`, the vertex `μ_{j-1}` of `Q`) is junk and is excluded by every clause
that uses this map. -/
def deletionMark (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) : Mark g.center → Mark (deleteVertex g.center j)
  | Sum.inl i => Sum.inl (fusionIndex j i)
  | Sum.inr v => Sum.inr (fusionVisitEquiv hn hz hb hc v)

/-- Marks of the side `b` (hence of its centre copy) identified with marks of the deletion. -/
def sideToDeletionMark (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t) (b : Bool)
    (a : Mark (g.sideTuple b t).val) : Mark (deleteVertex g.center j) :=
  deletionMark hn g hz hb hc ((markTransport (hs b)).symm a)

/-- The carrier correspondence between the two sides (and, through it, between the two centre
copies). -/
def sideToSide (hn : 3 ≤ n) (g : WallGerm (n + 1)) (t : g.SideParameter)
    (hs : CommonSupports g t) (S : Finset (Crossing g.center)) (b b' : Bool) :
    SideCarrier hn g t hs b S → SideCarrier hn g t hs b' S :=
  carrierMap (flat_hn1 hn) (flat_hn1 hn) (g.sideTuple b t).property (g.sideTuple b' t).property
    (sideSupport g t hs b S) (sideSupport g t hs b' S) (sideMarkTransport g t hs b b')

/-- The carrier correspondence from a side (and its centre copy) to the deletion. -/
def sideToDeletion (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t) (b : Bool)
    (S : Finset (Crossing g.center)) :
    SideCarrier hn g t hs b S → DeletionCarrier hn g hz hb hc S :=
  carrierMap (flat_hn1 hn) hn (g.sideTuple b t).property (flatDeletionGeneric hn g hz hb hc)
    (sideSupport g t hs b S) (deletionSupport hn g hz hb hc S) (sideToDeletionMark hn g hz hb hc t hs b)

/-! ## 5. def:flat-carriers -/

/-- def:flat-carriers as printed (sm-3:788-804), one field per sentence, at one side parameter
`t` (both sides), for one independent set `S` fixed at the centre. -/
structure FlatCarriersDefinitionData (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center)) : Prop where
  /-- "identify the crossing visits of the two sides, of the centre `P(0)` and of the deletion
  `P(0) ∖ j` through the common cyclic Gauss word of that lemma's clauses (ii) and (iii)": the
  centre ↔ side identification `visitTransport (hs b)` carries the centre's Gauss list (the
  visits in traversal order, cut at label `0`) onto the side's; the centre ↔ deletion
  identification `fusionVisitEquiv` carries the centre's cyclic Gauss word onto the deletion's;
  both identifications respect the pairing of the two visits of every crossing -/
  common_gauss_word :
    (∀ b : Bool, (geometricGaussList (flatCentreGeometry hn g hz hb hc)).map (visitTransport (hs b)) =
      gaussList (flat_hn1 hn) (g.sideTuple b t).property) ∧
    ((geometricGaussWord (flatCentreGeometry hn g hz hb hc)).map (fusionCrossingEquiv hn hz hb hc) =
      gaussWord hn (flatDeletionGeneric hn g hz hb hc)) ∧
    (∀ (b : Bool) (v : Visit g.center),
      visitTransport (hs b) (visitTwin v) = visitTwin (visitTransport (hs b) v)) ∧
    (∀ v : Visit g.center,
      fusionVisitEquiv hn hz hb hc (visitTwin v) = visitTwin (fusionVisitEquiv hn hz hb hc v))
  /-- "and fix an independent set `S` in their common interlacement graph": the interlacement
  graphs of the four configurations correspond under the identifications, so `S`, independent in
  the centre's (geometric) interlacement graph, is a decomposition on each side and on the
  deletion -/
  common_interlacement :
    (∀ (b : Bool) (x y : Crossing g.center),
      GeometricInterlaces (flatCentreGeometry hn g hz hb hc) x y ↔
        Interlaces (flat_hn1 hn) (g.sideTuple b t).property
          (crossingTransport (hs b) x) (crossingTransport (hs b) y)) ∧
    (∀ x y : Crossing g.center,
      GeometricInterlaces (flatCentreGeometry hn g hz hb hc) x y ↔
        Interlaces hn (flatDeletionGeneric hn g hz hb hc)
          (fusionCrossingEquiv hn hz hb hc x) (fusionCrossingEquiv hn hz hb hc y))
  independent_supports :
    (∀ b : Bool, IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S)) ∧
    IsDecomposition hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S)
  /-- "In each of these four configurations mark the traversal circle at every original vertex
  and every crossing visit, exchange the two outgoing successors at the two visits of every
  selected crossing — the reconnection of def:smoothing with conv:selected-visits — and trace the
  resulting oriented closed cycles by the inherited straight subsegments": on the two generic
  sides and on the (generic) deletion this is def:smoothing verbatim (`SmoothingData`: marks,
  `ρ_S = ρ ∘ swap`, cycles, traced curves, straight inherited subsegments) -/
  side_smoothing : ∀ b : Bool,
    SmoothingData (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S)
  deletion_smoothing :
    SmoothingData hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S)
  /-- (the same sentence at the centre, "mark the traversal circle at every original vertex and
  every crossing visit") the marks of the centre are the centre's own vertices and crossing
  visits at their own positions on the centre's traversal circle: vertex `i` at `μ_i`, a visit on
  its visited edge at the centre crossing point; these positions are pairwise distinct -/
  centre_marks : ∀ b : Bool,
    Function.Injective (centreMarkPosition hn g hz hb hc t hs b) ∧
    (∀ i : ZMod (n + 1), centreMarkPoint hn g hz hb hc t hs b (Sum.inl i) = g.center i) ∧
    (∀ v : Visit (g.sideTuple b t).val,
      (centreMarkPosition hn g hz hb hc t hs b (Sum.inr v)).1 = v.2.val ∧
      centreMarkPoint hn g hz hb hc t hs b (Sum.inr v) =
        crossingPoint ((crossingTransport (hs b)).symm v.1))
  /-- (the same sentence at the centre, the successor of the marked circle) the side's successor
  `ρ`, read at the centre, is the centre's own cyclic successor of marks: no centre mark lies
  strictly between a mark and its `ρ`-successor on the centre's traversal circle -/
  centre_successor : ∀ (b : Bool) (a u : Mark (g.sideTuple b t).val),
    ¬ traversalBetween (centreMarkPosition hn g hz hb hc t hs b a)
      (centreMarkPosition hn g hz hb hc t hs b u)
      (centreMarkPosition hn g hz hb hc t hs b
        (markSuccessor (flat_hn1 hn) (g.sideTuple b t).property a))
  /-- (the same sentence at the centre, "exchange the two outgoing successors at the two visits
  of every selected crossing") `ρ_S = ρ ∘ selectedMarkPerm`, and the exchange is the exchange of
  the centre's own two visits of every selected crossing of `S` -/
  centre_reconnection : ∀ (b : Bool) (a : Mark (g.sideTuple b t).val),
    smoothingSuccessor (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) a =
      markSuccessor (flat_hn1 hn) (g.sideTuple b t).property
        (selectedMarkPerm (sideSupport g t hs b S) a) ∧
    (markTransport (hs b)).symm (selectedMarkPerm (sideSupport g t hs b S) a) =
      selectedMarkPerm S ((markTransport (hs b)).symm a)
  /-- (the same sentence at the centre, "trace the resulting oriented closed cycles by the
  inherited straight subsegments") the centre carrier of `q` is the cycle of the centre points of
  its marks in inherited order, and the straight piece from each of its marks to its
  `ρ_S`-successor lies on the centre's edge of the outgoing slot -/
  centre_traced : ∀ (b : Bool) (q : SideCarrier hn g t hs b S),
    centrePlaneCycle hn g hz hb hc t hs b S q =
      ((componentMarkList (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q).map
        (centreMarkPoint hn g hz hb hc t hs b) : Cycle Plane) ∧
    ∀ a : Mark (g.sideTuple b t).val,
      owner (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) a = q →
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        centreSegment hn g hz hb hc t hs b S a u ∈
          edgeSegment g.center
            (centreMarkPosition hn g hz hb hc t hs b (selectedMarkPerm (sideSupport g t hs b S) a)).1
  /-- "These oriented closed polygonal cycles are the carriers of `S` in that configuration":
  the carriers are the cycles of `ρ_S` (two marks lie on one carrier iff `ρ_S` connects them), on
  the sides (hence at the centre, whose carriers are indexed by the side's) and on the deletion -/
  carriers_are_cycles :
    (∀ (b : Bool) (a a' : Mark (g.sideTuple b t).val),
      owner (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) a =
        owner (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) a' ↔
      (smoothingSuccessor (flat_hn1 hn) (g.sideTuple b t).property
        (sideSupport g t hs b S)).SameCycle a a') ∧
    (∀ a a' : Mark (deleteVertex g.center j),
      owner hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S) a =
        owner hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S) a' ↔
      (smoothingSuccessor hn (flatDeletionGeneric hn g hz hb hc)
        (deletionSupport hn g hz hb hc S)).SameCycle a a')
  /-- "On the two generic sides they are the carriers of def:smoothing": the side carriers are
  `Component`, traced by `componentPlaneCycle` (the plane points of their marks in inherited
  order) -/
  side_carriers_smoothing : ∀ (b : Bool) (q : SideCarrier hn g t hs b S),
    componentPlaneCycle (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q =
      ((componentMarkList (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q).map
        (markPoint (flat_hn1 hn) (g.sideTuple b t).property) : Cycle Plane)
  /-- "at the centre and on the deletion the same words define them, no genericity being
  assumed": the centre is not generic; its marks are placed by the centre's own crossing
  parameters (lem:flat-sides (ii), no function on the generic locus evaluated at the centre) -/
  centre_not_generic : ¬ Generic g.center
  centre_positions_geometric : ∀ (b : Bool) (v : Visit (g.sideTuple b t).val),
    (centreMarkPosition hn g hz hb hc t hs b (Sum.inr v)).2.val =
      visitParameter ((visitTransport (hs b)).symm v)
  /-- (well-definedness of the centre family) the centre carriers do not depend on the side
  through which they are identified: the side ↔ side carrier correspondence carries the centre
  traced cycles and the centre corner cycles to equal cycles of plane points -/
  centre_side_independent : ∀ (b b' : Bool) (q : SideCarrier hn g t hs b S),
    centrePlaneCycle hn g hz hb hc t hs b' S (sideToSide hn g t hs S b b' q) =
      centrePlaneCycle hn g hz hb hc t hs b S q ∧
    ((ccpCornerList (flat_hn1 hn) (g.sideTuple b' t).property (sideSupport g t hs b' S)
        (sideToSide hn g t hs S b b' q)).map (centreMarkPoint hn g hz hb hc t hs b') : Cycle Plane) =
      ((ccpCornerList (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q).map
        (centreMarkPoint hn g hz hb hc t hs b) : Cycle Plane)

/-- def:flat-carriers under the geometric hypotheses of lem:flat-sides (the sign change of `τ_j`
is not needed to define the carriers): on a common radius, for every independent set `S` of the
centre's interlacement graph, the four carrier families are defined as printed. -/
theorem flat_carriers_definition (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.SideParameter, t.val < δ →
      ∃ hs : CommonSupports g t, ∀ S : Finset (Crossing g.center),
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ GeometricInterlaces (flatCentreGeometry hn g hz hb hc) x y) →
        FlatCarriersDefinitionData hn g hz hb hc t hs S := by
  sorry

/-! ## 6. cor:flat-carriers -/

/-- cor:flat-carriers as printed (sm-3:805-835), one field per printed clause, at one side
parameter `t`, `br` being the right side (`!br` the left side), for one independent set `S`. -/
structure FlatCarriersData (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
    (S : Finset (Crossing g.center)) (br : Bool) : Prop where
  /-- the named sides: `br` is the right side (`τ_j = -1`), `!br` the left side (`τ_j = 1`) -/
  right_side : IsRightSide g j br t
  left_side : IsLeftSide g j (!br) t
  /-- (i) "The carriers correspond under their named traversal arcs": the carrier maps induced
  by the mark identifications are bijections compatible with the assignment of marks to carriers
  — right ↔ left (each side ↔ its centre copy being the identity of `SideCarrier`) -/
  correspond_sides :
    Function.Bijective (sideToSide hn g t hs S br (!br)) ∧
    ∀ a : Mark (g.sideTuple br t).val,
      sideToSide hn g t hs S br (!br)
          (owner (flat_hn1 hn) (g.sideTuple br t).property (sideSupport g t hs br S) a) =
        owner (flat_hn1 hn) (g.sideTuple (!br) t).property (sideSupport g t hs (!br) S)
          (sideMarkTransport g t hs br (!br) a)
  /-- (i) — and side (hence centre) ↔ deletion, for every mark other than `μ_j` -/
  correspond_deletion : ∀ b : Bool,
    Function.Bijective (sideToDeletion hn g hz hb hc t hs b S) ∧
    ∀ a : Mark (g.sideTuple b t).val, a ≠ Sum.inl j →
      sideToDeletion hn g hz hb hc t hs b S
          (owner (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) a) =
        owner hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S)
          (sideToDeletionMark hn g hz hb hc t hs b a)
  /-- (i) "Exactly one contains `μ_j`": on each side and at the centre, the point `μ_j` lies on
  the carrier of the vertex mark `j` and on no other carrier -/
  unique_mu : ∀ (b : Bool) (q : SideCarrier hn g t hs b S),
    ((g.sideTuple b t).val j ∈
        componentPlaneCycle (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q ↔
      q = muCarrier hn g j t hs b S) ∧
    (g.center j ∈ centrePlaneCycle hn g hz hb hc t hs b S q ↔ q = muCarrier hn g j t hs b S)
  /-- (i) "The central copy of that carrier differs from its deletion copy only by the
  positive-flat subdivision at `μ_j`": removing the mark `μ_j` from the central mark cycle
  (resp. corner cycle) of the `μ_j`-carrier gives the deletion copy's mark cycle (resp. corner
  cycle) as cycles of plane points, and `μ_j` lies strictly between its two neighbours on the
  straight segment joining them (its incident directions are positive multiples of the fused
  direction, eq. flatpr:fusion) -/
  central_deletion_subdivision : ∀ b : Bool,
    ((((componentMarkList (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S)
          (muCarrier hn g j t hs b S)).filter (fun a => decide (a ≠ Sum.inl j))).map
        (centreMarkPoint hn g hz hb hc t hs b) : Cycle Plane) =
      componentPlaneCycle hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S)
        (sideToDeletion hn g hz hb hc t hs b S (muCarrier hn g j t hs b S))) ∧
    ((((ccpCornerList (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S)
          (muCarrier hn g j t hs b S)).filter (fun a => decide (a ≠ Sum.inl j))).map
        (centreMarkPoint hn g hz hb hc t hs b) : Cycle Plane) =
      ((ccpCornerList hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S)
          (sideToDeletion hn g hz hb hc t hs b S (muCarrier hn g j t hs b S))).map
        (markPoint hn (flatDeletionGeneric hn g hz hb hc)) : Cycle Plane)) ∧
    StrictBetween
      (centreMarkPoint hn g hz hb hc t hs b
        ((smoothingSuccessor (flat_hn1 hn) (g.sideTuple b t).property
          (sideSupport g t hs b S)).symm (Sum.inl j)))
      (g.center j)
      (centreMarkPoint hn g hz hb hc t hs b
        (smoothingSuccessor (flat_hn1 hn) (g.sideTuple b t).property
          (sideSupport g t hs b S) (Sum.inl j)))
  /-- (i) "every other central carrier is unchanged by deletion": its mark cycle and its corner
  cycle, as cycles of plane points, are those of its deletion copy -/
  others_unchanged : ∀ (b : Bool) (q : SideCarrier hn g t hs b S), q ≠ muCarrier hn g j t hs b S →
    centrePlaneCycle hn g hz hb hc t hs b S q =
      componentPlaneCycle hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S)
        (sideToDeletion hn g hz hb hc t hs b S q) ∧
    ((ccpCornerList (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q).map
        (centreMarkPoint hn g hz hb hc t hs b) : Cycle Plane) =
      ((ccpCornerList hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S)
          (sideToDeletion hn g hz hb hc t hs b S q)).map
        (markPoint hn (flatDeletionGeneric hn g hz hb hc)) : Cycle Plane)
  /-- (i) "Every carrier has nonzero segments": in all four configurations every inherited
  subsegment (from a mark to its `ρ_S`-successor) has distinct endpoints, and every edge of every
  corner polygon is nonzero -/
  nonzero_segments :
    (∀ (b : Bool) (a : Mark (g.sideTuple b t).val),
      markPoint (flat_hn1 hn) (g.sideTuple b t).property
          (smoothingSuccessor (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) a) ≠
        markPoint (flat_hn1 hn) (g.sideTuple b t).property a ∧
      centreMarkPoint hn g hz hb hc t hs b
          (smoothingSuccessor (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) a) ≠
        centreMarkPoint hn g hz hb hc t hs b a) ∧
    (∀ a : Mark (deleteVertex g.center j),
      markPoint hn (flatDeletionGeneric hn g hz hb hc)
          (smoothingSuccessor hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S) a) ≠
        markPoint hn (flatDeletionGeneric hn g hz hb hc) a) ∧
    (∀ (b : Bool) (q : SideCarrier hn g t hs b S)
      (k : ZMod (ccpCornerCount (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q)),
      edge (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q) k ≠ 0 ∧
      edge (centreCornerPolygon hn g hz hb hc t hs b S q) k ≠ 0) ∧
    (∀ (q : DeletionCarrier hn g hz hb hc S)
      (k : ZMod (ccpCornerCount hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S) q)),
      edge (ccpCornerPolygon hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S) q) k ≠ 0)
  /-- (i) "and no antiparallel corner": no corner polygon (sides, centre, deletion) has
  antiparallel consecutive directions -/
  no_antiparallel :
    (∀ (b : Bool) (q : SideCarrier hn g t hs b S)
      (k : ZMod (ccpCornerCount (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q)),
      (¬ ∃ r : ℝ, r < 0 ∧
        edge (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q) k =
          r • edge (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q)
            (k - 1)) ∧
      (¬ ∃ r : ℝ, r < 0 ∧
        edge (centreCornerPolygon hn g hz hb hc t hs b S q) k =
          r • edge (centreCornerPolygon hn g hz hb hc t hs b S q) (k - 1))) ∧
    (∀ (q : DeletionCarrier hn g hz hb hc S)
      (k : ZMod (ccpCornerCount hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S) q)),
      ¬ ∃ r : ℝ, r < 0 ∧
        edge (ccpCornerPolygon hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S) q) k =
          r • edge (ccpCornerPolygon hn (flatDeletionGeneric hn g hz hb hc)
            (deletionSupport hn g hz hb hc S) q) (k - 1))
  /-- (i) "except for that one central zero turn, all corner turns are nonzero" -/
  turns_nonzero :
    (∀ (b : Bool) (q : SideCarrier hn g t hs b S)
      (k : ZMod (ccpCornerCount (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q)),
      turn (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q) k ≠ 0) ∧
    (∀ (q : DeletionCarrier hn g hz hb hc S)
      (k : ZMod (ccpCornerCount hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S) q)),
      turn (ccpCornerPolygon hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S) q) k ≠ 0) ∧
    (∀ (b : Bool) (q : SideCarrier hn g t hs b S)
      (k : ZMod (ccpCornerCount (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q)),
      turn (centreCornerPolygon hn g hz hb hc t hs b S q) k = 0 ↔
        ccpCornerMark (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q k = Sum.inl j)
  /-- (ii) "Corresponding carriers have the same retained self-crossing visits, pairing, signs
  and positive over/under bits": the retained crossings correspond (right ↔ left, side ↔
  deletion, centre copy ↔ side), both visits of a retained crossing lie on the corresponding
  carriers, and for every crossing pair `{i, k}` the signs `sgn det(d_i, d_k)` and the positive
  over/under bits `det(d_i, d_k) > 0` agree in the four configurations -/
  same_crossings :
    (∀ (q : SideCarrier hn g t hs br S) (x : Crossing (g.sideTuple br t).val),
      x ∈ carrierCrossings (flat_hn1 hn) (g.sideTuple br t).property (sideSupport g t hs br S) q ↔
        crossingTransport (fun s => (hs br s).symm.trans (hs (!br) s)) x ∈
          carrierCrossings (flat_hn1 hn) (g.sideTuple (!br) t).property (sideSupport g t hs (!br) S)
            (sideToSide hn g t hs S br (!br) q)) ∧
    (∀ (b : Bool) (q : SideCarrier hn g t hs b S) (x : Crossing (g.sideTuple b t).val),
      x ∈ carrierCrossings (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q ↔
        fusionCrossingEquiv hn hz hb hc ((crossingTransport (hs b)).symm x) ∈
          carrierCrossings hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S)
            (sideToDeletion hn g hz hb hc t hs b S q)) ∧
    (∀ (b : Bool) (q : SideCarrier hn g t hs b S) (x : Crossing g.center),
      x ∈ centreCarrierCrossings hn g t hs b S q ↔
        crossingTransport (hs b) x ∈
          carrierCrossings (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q) ∧
    (∀ (b : Bool) (q : SideCarrier hn g t hs b S) (v : Visit (g.sideTuple b t).val),
      v.1 ∈ carrierCrossings (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q →
        owner (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) (Sum.inr v) = q ∧
        owner (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S)
          (Sum.inr (visitTwin v)) = q ∧
        owner hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S)
          (Sum.inr (fusionVisitEquiv hn hz hb hc ((visitTransport (hs b)).symm v))) =
            sideToDeletion hn g hz hb hc t hs b S q) ∧
    (∀ i k : ZMod (n + 1), IsCrossing g.center {i, k} →
      crossingSign (g.sideTuple (!br) t).val i k = crossingSign (g.sideTuple br t).val i k ∧
      crossingSign g.center i k = crossingSign (g.sideTuple br t).val i k ∧
      crossingSign (deleteVertex g.center j) (fusionIndex j i) (fusionIndex j k) =
        crossingSign (g.sideTuple br t).val i k ∧
      (0 < det (edge (g.sideTuple (!br) t).val i) (edge (g.sideTuple (!br) t).val k) ↔
        0 < det (edge (g.sideTuple br t).val i) (edge (g.sideTuple br t).val k)) ∧
      (0 < det (edge g.center i) (edge g.center k) ↔
        0 < det (edge (g.sideTuple br t).val i) (edge (g.sideTuple br t).val k)) ∧
      (0 < det (edge (deleteVertex g.center j) (fusionIndex j i))
          (edge (deleteVertex g.center j) (fusionIndex j k)) ↔
        0 < det (edge (g.sideTuple br t).val i) (edge (g.sideTuple br t).val k)))
  /-- (ii) "They have the same signed rotation and hence the same absolute rotation" — right ↔
  left, side ↔ deletion, and (round 4) the centre copy as well -/
  same_rotation :
    (∀ q : SideCarrier hn g t hs br S,
      rotationNumber (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple (!br) t).property
          (sideSupport g t hs (!br) S) (sideToSide hn g t hs S br (!br) q)) =
        rotationNumber (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple br t).property
          (sideSupport g t hs br S) q)) ∧
    (∀ (b : Bool) (q : SideCarrier hn g t hs b S),
      rotationNumber (ccpCornerPolygon hn (flatDeletionGeneric hn g hz hb hc)
          (deletionSupport hn g hz hb hc S) (sideToDeletion hn g hz hb hc t hs b S q)) =
        rotationNumber (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple b t).property
          (sideSupport g t hs b S) q) ∧
      rotationNumber (centreCornerPolygon hn g hz hb hc t hs b S q) =
        rotationNumber (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple b t).property
          (sideSupport g t hs b S) q)) ∧
    (∀ q : SideCarrier hn g t hs br S,
      |rotationNumber (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple (!br) t).property
          (sideSupport g t hs (!br) S) (sideToSide hn g t hs S br (!br) q))| =
        |rotationNumber (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple br t).property
          (sideSupport g t hs br S) q)|) ∧
    (∀ (b : Bool) (q : SideCarrier hn g t hs b S),
      |rotationNumber (ccpCornerPolygon hn (flatDeletionGeneric hn g hz hb hc)
          (deletionSupport hn g hz hb hc S) (sideToDeletion hn g hz hb hc t hs b S q))| =
        |rotationNumber (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple b t).property
          (sideSupport g t hs b S) q)| ∧
      |rotationNumber (centreCornerPolygon hn g hz hb hc t hs b S q)| =
        |rotationNumber (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple b t).property
          (sideSupport g t hs b S) q)|)
  /-- (ii) "Every corresponding corner away from `μ_j` has the same turn sign on both sides and
  in the deletion": a corner is a corner mark; corners correspond through the mark
  identifications -/
  same_turn_signs :
    (∀ (q : SideCarrier hn g t hs br S)
      (k : ZMod (ccpCornerCount (flat_hn1 hn) (g.sideTuple br t).property (sideSupport g t hs br S) q)),
      ccpCornerMark (flat_hn1 hn) (g.sideTuple br t).property (sideSupport g t hs br S) q k ≠ Sum.inl j →
      ∃ k' : ZMod (ccpCornerCount (flat_hn1 hn) (g.sideTuple (!br) t).property
          (sideSupport g t hs (!br) S) (sideToSide hn g t hs S br (!br) q)),
        ccpCornerMark (flat_hn1 hn) (g.sideTuple (!br) t).property (sideSupport g t hs (!br) S)
            (sideToSide hn g t hs S br (!br) q) k' =
          sideMarkTransport g t hs br (!br)
            (ccpCornerMark (flat_hn1 hn) (g.sideTuple br t).property (sideSupport g t hs br S) q k) ∧
        turn (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple (!br) t).property (sideSupport g t hs (!br) S)
            (sideToSide hn g t hs S br (!br) q)) k' =
          turn (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple br t).property (sideSupport g t hs br S) q) k) ∧
    (∀ (b : Bool) (q : SideCarrier hn g t hs b S)
      (k : ZMod (ccpCornerCount (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q)),
      ccpCornerMark (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q k ≠ Sum.inl j →
      ∃ k' : ZMod (ccpCornerCount hn (flatDeletionGeneric hn g hz hb hc)
          (deletionSupport hn g hz hb hc S) (sideToDeletion hn g hz hb hc t hs b S q)),
        ccpCornerMark hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S)
            (sideToDeletion hn g hz hb hc t hs b S q) k' =
          sideToDeletionMark hn g hz hb hc t hs b
            (ccpCornerMark (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q k) ∧
        turn (ccpCornerPolygon hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S)
            (sideToDeletion hn g hz hb hc t hs b S q)) k' =
          turn (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q) k)
  /-- (broadening, not a printed sentence of (ii) but the printed proof's "all surviving corner
  signs … agree among the configurations", sm-3:875-876) the centre copy has the same turn sign
  as its side at every corner away from `μ_j` -/
  centre_turn_signs : ∀ (b : Bool) (q : SideCarrier hn g t hs b S)
    (k : ZMod (ccpCornerCount (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q)),
    ccpCornerMark (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q k ≠ Sum.inl j →
    turn (centreCornerPolygon hn g hz hb hc t hs b S q) k =
      turn (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q) k
  /-- (ii) "The extra corner at `μ_j` is right on the right side and left on the left side" -/
  extra_corner_mu :
    (∃ k, ccpCornerMark (flat_hn1 hn) (g.sideTuple br t).property (sideSupport g t hs br S)
      (muCarrier hn g j t hs br S) k = Sum.inl j) ∧
    (∀ k, ccpCornerMark (flat_hn1 hn) (g.sideTuple br t).property (sideSupport g t hs br S)
        (muCarrier hn g j t hs br S) k = Sum.inl j →
      turn (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple br t).property (sideSupport g t hs br S)
        (muCarrier hn g j t hs br S)) k = -1) ∧
    (∀ k, ccpCornerMark (flat_hn1 hn) (g.sideTuple (!br) t).property (sideSupport g t hs (!br) S)
        (muCarrier hn g j t hs (!br) S) k = Sum.inl j →
      turn (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple (!br) t).property (sideSupport g t hs (!br) S)
        (muCarrier hn g j t hs (!br) S)) k = 1)
  /-- (iii) "Define a carrier's selector to be `1` if all its turns are right, `(-1)^c` if all
  its `c` turns are left, and `0` if its turns are mixed" (`c` = number of corners) -/
  selector_def :
    (∀ {m : ℕ} [NeZero m] (Q : LabelledTuple m),
      ((∀ i, turn Q i = -1) → cornerSelector Q = 1) ∧
      ((∀ i, turn Q i = 1) → cornerSelector Q = (-1 : ℤ) ^ m) ∧
      (¬ (∀ i, turn Q i = -1) → ¬ (∀ i, turn Q i = 1) → cornerSelector Q = 0)) ∧
    (∀ (b : Bool) (q : SideCarrier hn g t hs b S),
      carrierSelector (flat_hn1 hn) (g.sideTuple b t).property (sideSupport g t hs b S) q =
        cornerSelector (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple b t).property
          (sideSupport g t hs b S) q))
  /-- (iii) `W_right − W_left = W_del` for the carrier through `μ_j` (eq.
  flatpr:selector-identity) -/
  selector_identity :
    carrierSelector (flat_hn1 hn) (g.sideTuple br t).property (sideSupport g t hs br S)
        (muCarrier hn g j t hs br S) -
      carrierSelector (flat_hn1 hn) (g.sideTuple (!br) t).property (sideSupport g t hs (!br) S)
        (muCarrier hn g j t hs (!br) S) =
    carrierSelector hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S)
      (sideToDeletion hn g hz hb hc t hs br S (muCarrier hn g j t hs br S))
  /-- (iii) "All other corresponding carrier selectors agree" -/
  selector_others : ∀ q : SideCarrier hn g t hs br S, q ≠ muCarrier hn g j t hs br S →
    carrierSelector (flat_hn1 hn) (g.sideTuple (!br) t).property (sideSupport g t hs (!br) S)
        (sideToSide hn g t hs S br (!br) q) =
      carrierSelector (flat_hn1 hn) (g.sideTuple br t).property (sideSupport g t hs br S) q ∧
    carrierSelector hn (flatDeletionGeneric hn g hz hb hc) (deletionSupport hn g hz hb hc S)
        (sideToDeletion hn g hz hb hc t hs br S q) =
      carrierSelector (flat_hn1 hn) (g.sideTuple br t).property (sideSupport g t hs br S) q

/-- cor:flat-carriers under the hypotheses of lem:flat-sides: on a common radius, for every
independent set `S` of the centre's interlacement graph and with `br` the right side, the four
carrier families of def:flat-carriers satisfy (i)–(iii) as printed. The closing sentences
("These assertions concern geometric and combinatorial carrier data. They make no assignment of
a state-sum value at the flat centre.") are non-definitional and have no field. -/
theorem flat_carriers (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅)
    (hsc : g.SignChanges (fun P => (turn P j : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.SideParameter, t.val < δ →
      ∃ hs : CommonSupports g t,
        (∀ b : Bool, IsRightSide g j b t ∨ IsLeftSide g j b t) ∧
        ∀ S : Finset (Crossing g.center),
          (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ GeometricInterlaces (flatCentreGeometry hn g hz hb hc) x y) →
          ∀ br : Bool, IsRightSide g j br t → FlatCarriersData hn g hz hb hc t hs S br := by
  sorry

end

end SM
