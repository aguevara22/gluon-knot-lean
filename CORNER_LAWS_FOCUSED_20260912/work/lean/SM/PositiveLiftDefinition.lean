import SM.LinkPositiveLift

/-! Source def:positive-lift (reference/SM/sm-3-statesum.tex:325, frame SM15): positive crossings and
the positive lift of a subpolygon. Main declaration: `SM.positive_lift_definition`.

Notation (the Chapter-3 representation layer, design decision of 2026-09-13; modules SM/LinkDiagram,
SM/LinkPositiveLift, namespace `SM.Link`). An oriented link diagram in the plane is a `Link.Diagram`:
a `Shadow` — a finite collection of closed oriented polygonal curves, the components
`comp i : PolyComp` (a labelled tuple with `k ≥ 3` vertices, def:polygon) — which is `Generic`
(regular components; no vertex on a non-incident edge segment (`tail_off`); any two non-adjacent
meeting edges meet transversely, `det (dir s) (dir t) ≠ 0`; no point interior to three edges),
together with a choice of the over strand at each crossing (`overStrand x ∈ x.val`). Strands are
directed edges `⟨i, j⟩` with direction `dir = edge`; a crossing (double point) is an unordered pair
`{s, t}` of non-adjacent strands whose closed edge segments meet (`IsCrossing`), and `underStrand x`
is the other strand of the pair. `IsPositive x ↔ 0 < det (dir (over)) (dir (under))`,
`sign x = sgn det`, `writhe = Σ sign`.

Scope of the formal class (documented decisions, work/AUTHOR_NOTES.md 2026-09-13). (1) The class
is polygonal: the source fixes "A diagram here is a finite polygonal immersion, or a regular smooth
immersion with finitely many transverse double points and possible finitely many corners away
from crossings" (sm-3:337-343) and supplies finite PL models for the smooth case
(lem:gauss-pl-model, sm-3:371-427, not a selected row); every diagram the selected rows use
(positive lifts of carriers, diagrams of polygons) is polygonal, and the smooth alternative is not
formalized. (2) The class is nonempty, `c ≥ 1`: the source's convention for its diagrams
("Here c ≥ 1", lp:lm, sm-3:951; "Algebraic empty products are not empty links", sm-3:933). (3) A
`Diagram` carries labelled representatives (a base vertex per component and a component order),
as permitted by the formalization remark of def:polygon (sm-1:56-62); the notions of this row
(crossings, signs, writhe, the positive lift) are defined on representatives. (4) `tail_off` forbids
a vertex on a non-incident edge — the polygonal form of "corners away from crossings" and of
transversality (a double point at a vertex has no tangent) — including at a straight-through
(zero-turn) vertex; regular polygons allow zero turns, so a double point at such a subdivision
vertex is excluded by the Lean class (harmless for carriers, whose corner turns are nonzero).

A subpolygon `Q` is a carrier `q : Component hn hP S` of a decomposition `S` of the generic polygon
`P` (def:smoothing, lem:carriers), read as its corner polygon `Carrier.ccpCornerPolygon hn hP S q`
(the accepted reading of lem:carriers (ii) and def:uniform; it traces the same closed curve as the
carrier by lem:carriers (ii)); `carrierShadow hn hP S q hS` is the one-component shadow over it,
generic by lem:carriers, and `positiveLift hn hP S q hS` is the diagram on it with every over strand
chosen positive. The crossings of `Q` are `carrierCrossings hn hP S q` with count
`m_Q = carrierCrossingCount` (def:smoothing); `SM.crossingPoint` is the accepted crossing point of
the ambient polygon. -/

namespace SM

open Link Carrier

/-- def:positive-lift as printed on SM15, on the document's polygonal class of diagrams. -/
structure PositiveLiftDefinitionData : Prop where
  /-- "An oriented link diagram in the plane is a finite collection of closed oriented curves with
  finitely many transverse double points, no triple points, and at each double point a choice of the
  over strand": a `Diagram` is exactly a generic shadow with an over-strand choice (every such datum
  is a diagram and every diagram is of this form), where a shadow is generic exactly when its
  components are regular closed polygonal curves, no vertex lies on a non-incident edge, any two
  non-adjacent meeting edges are transverse, and no point is interior to three edges; its double
  points are its crossings — exactly the pairs of non-adjacent strands whose edge segments meet
  (finitely many); the over strand of a crossing is one of its two strands and the under strand is
  the other. -/
  diagram :
    (∀ D : Diagram, D = ⟨D.Γ, D.generic, D.overStrand, D.over_mem⟩) ∧
    (∀ (Γ : Shadow) (hΓ : Γ.Generic) (ov : Γ.Crossing → Γ.Strand) (hov : ∀ x, ov x ∈ x.val),
      (Diagram.mk Γ hΓ ov hov).Γ = Γ ∧ (Diagram.mk Γ hΓ ov hov).overStrand = ov) ∧
    (∀ Γ : Shadow, Γ.Generic ↔
      (∀ i, Regular (Γ.comp i).P) ∧
      (∀ s t : Γ.Strand, ¬ Γ.IncidentTail s t → Γ.tail s ∉ Γ.seg t) ∧
      (∀ s t : Γ.Strand, ¬ Γ.Adjacent s t → (Γ.seg s ∩ Γ.seg t).Nonempty →
        det (Γ.dir s) (Γ.dir t) ≠ 0) ∧
      ¬ ∃ s t u : Γ.Strand, s ≠ t ∧ t ≠ u ∧ s ≠ u ∧
        (Γ.interior s ∩ Γ.interior t ∩ Γ.interior u).Nonempty) ∧
    (∀ (Γ : Shadow) (x : Finset Γ.Strand), Γ.IsCrossing x ↔
      ∃ s t : Γ.Strand, x = {s, t} ∧ ¬ Γ.Adjacent s t ∧ (Γ.seg s ∩ Γ.seg t).Nonempty) ∧
    (∀ (D : Diagram) (x : D.Γ.Crossing), D.overStrand x ∈ x.val ∧ D.underStrand x ∈ x.val ∧
      D.underStrand x ≠ D.overStrand x ∧ x.val = {D.overStrand x, D.underStrand x})
  /-- The document's convention `c ≥ 1` (lp:lm, sm-3:951): every diagram has at least one
  component. -/
  components : ∀ D : Diagram, 0 < D.Γ.c
  /-- "A double point with over-strand direction `u_o` and under-strand direction `u_u` is positive
  if `det(u_o, u_u) > 0` and negative otherwise": the sign is `sgn det(u_o, u_u)`, never zero, `+1`
  exactly at positive crossings and `-1` exactly at the others. -/
  positive : ∀ (D : Diagram) (x : D.Γ.Crossing),
    (D.IsPositive x ↔ 0 < det (D.Γ.dir (D.overStrand x)) (D.Γ.dir (D.underStrand x))) ∧
    D.sign x = SignType.sign (det (D.Γ.dir (D.overStrand x)) (D.Γ.dir (D.underStrand x))) ∧
    D.sign x ≠ 0 ∧ (D.IsPositive x ↔ D.sign x = 1) ∧ (¬ D.IsPositive x ↔ D.sign x = -1)
  /-- "Its writhe (the sum of crossing signs)". -/
  writhe : ∀ D : Diagram, D.writhe = ∑ x : D.Γ.Crossing, (D.sign x : ℤ)
  /-- "The positive lift of a subpolygon `Q` is the oriented knot diagram whose curve is `Q`": one
  component, the corner polygon of the carrier. -/
  lift_curve : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S),
    (positiveLift hn hP S q hS).Γ.c = 1 ∧
    ∀ i, ((positiveLift hn hP S q hS).Γ.comp i).P = ccpCornerPolygon hn hP S q
  /-- "whose double points are the crossings of `Q`": the crossings of the lift correspond
  bijectively to the crossings of `Q` (def:smoothing), with the same crossing points. -/
  lift_crossings : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S),
    ∃ e : (positiveLift hn hP S q hS).Γ.Crossing ≃ {c : Crossing P // c ∈ carrierCrossings hn hP S q},
      ∀ x, (positiveLift hn hP S q hS).Γ.crossingPoint x = crossingPoint (e x).val
  /-- "in which at every double point the over strand is chosen so that the crossing is positive". -/
  lift_positive : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S)
    (x : (positiveLift hn hP S q hS).Γ.Crossing), (positiveLift hn hP S q hS).IsPositive x
  /-- "THE oriented knot diagram …": the positive lift is the only diagram on that curve all of whose
  crossings are positive. -/
  lift_unique : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S) (D : Diagram),
    D.Γ = carrierShadow hn hP S q hS → (∀ x, D.IsPositive x) → D = positiveLift hn hP S q hS
  /-- "Its writhe (the sum of crossing signs) is `m_Q`." -/
  lift_writhe : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S),
    (positiveLift hn hP S q hS).writhe = carrierCrossingCount hn hP S q

theorem positive_lift_definition : PositiveLiftDefinitionData where
  diagram :=
    ⟨fun _ => rfl, fun _ _ _ _ => ⟨rfl, rfl⟩,
      fun Γ => ⟨fun h => ⟨h.regular, h.tail_off, h.transverse, h.no_triple⟩,
        fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩,
      fun _ _ => Iff.rfl,
      fun D x => ⟨D.over_mem x, D.under_mem x, D.under_ne_over x, D.val_eq_pair x⟩⟩
  components := fun D => D.Γ.hc
  positive := fun D x =>
    ⟨Iff.rfl, rfl, D.sign_ne_zero x, D.isPositive_iff_sign_eq_one x, (D.sign_eq_neg_one_iff x).symm⟩
  writhe := fun _ => rfl
  lift_curve := fun _ _ _ _ _ _ _ _ => ⟨rfl, fun _ => rfl⟩
  lift_crossings := fun _ _ hn _ hP S q hS =>
    ⟨carrierCrossingEquiv hn hP S q hS,
      fun x => (crossingPoint_carrierCrossingEquiv hn hP S q hS x).symm⟩
  lift_positive := fun _ _ hn _ hP S q hS x => positiveLift_isPositive hn hP S q hS x
  lift_unique := fun _ _ hn _ hP S q hS D hD hpos => eq_positiveLift_of_isPositive hn hP S q hS D hD hpos
  lift_writhe := fun _ _ hn _ hP S q hS => positiveLift_writhe_eq_carrierCrossingCount hn hP S q hS

end SM
