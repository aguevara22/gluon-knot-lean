import SM.Rounding
import SM.LinkPositiveLift
import CV.TurnLift
import CV.CarrierBridges


/-! Ported 2026-09-14 05:37Z from work/drafts/cvdom/CVRounding.lean (row unit, report work/drafts/cvdom/CVROUNDING_REPORT.md): row CV:lem:rounding (152), main declaration `CV.rounding`, bundle `CVRoundingData`, proved from the accepted SM.cf_lem_rounding through the polygon bridge. Only this header added. -/
/-! # CV lane, row 152 — CV:lem:rounding, "rounding"

Source: reference/R/CV/d3_floor.tex, `lem:rounding` (statement lines 31–93: scoping sentence 32, the
objects 33–35, the hypotheses 35–38, the existence sentence 38–41, two commentary paragraphs 41–43 and
45–55, clause (a) 57–58, clause (b) 59–66 with its commentary 68–79, clause (c) 80–82, clause (d) 83,
clause (e) 84–91; printed proof 94–260, the clearance `ε₀(L)` at 230–236, its positivity 241–247).  Consumers: CV:lem:curl
(d3:304–330, reads (e) — "a disc meeting the diagram in one embedded arc") and CV:thm:carrierfloor
(d3:736–806: (A) names the record `Round(L, D, ε)`, (B) and (C) read (b), (c), (d)).

SM counterpart: `SM.cf_lem_rounding : SM.RoundingData` (work/lean/SM/Rounding.lean; fixed statement
work/drafts/rounding/Rounding_statement_FINAL.lean; sm-3-statesum.tex:3644–3700).  CV's clauses (a)–(e)
(d3:57–91) are SM's (sm-3:3657–3692) word for word (`τ_i` for `ϑ_i`); CV's hypotheses (d3:33–38) are
SM's (sm-3:3647–3652) word for word.  The two statements differ in exactly three places, all recorded
below: the scoping sentence ("rot as in Definition def:rot", one definition for polygons and `C¹` curves,
versus SM's "Lemma lem:rot for polygons and Definition cf:def-turning for curves"), the two CV commentary
paragraphs (41–43, 45–55; SM has none, only its `\status` line 3693), and the printed domain of the
polygon (CV: a labelled tuple `L : LabelledTuple n` with CV:def:diagrammatic; SM: `PolyComp` with a
generic one-component shadow).

Written 2026-09-14 by a Claude Code architect-prover subagent of the pod executor.  Checked with
`cd work/lean && lake env lean ../drafts/cvdom/CVRounding.lean` (exit 0, no errors, no warnings) against
the library module work/lean/SM/Rounding.lean (built 2026-09-14 05:12 UTC / 01:12am ET; before that build
the same file was checked with `SM.Rounding` compiled to an olean under a temporary overlay root, the
U5a/U0 pattern, with the same result).  No incomplete proofs; axioms of `CV.rounding` and of every
declaration here: `propext`, `Classical.choice`, `Quot.sound`.

## The printed statement (d3_floor.tex:32–91)

"Here rot is as in Definition def:rot. Let L be a closed polygon with corners q₁,…,q_c, and let D be an
oriented diagram whose underlying plane curve is L — L together with an over/under assignment at each of
its double points. Assume the principal turns of L all exist and are nonzero; that L has finitely many
double points, all transversal, none of them a corner; and that no corner of L lies on an edge of L
other than the two incident to it. Then there is a clearance ε₀(L) > 0 such that for every
ε ∈ (0, ε₀(L)) there is a C^∞ regular closed plane curve L_ε, and a diagram D_ε carried by it, with
these properties.
(a) L_ε coincides with L outside the union of the discs of radius ε about the corners.
(b) Inside the disc about q_i the unit tangent moves strictly monotonically, in the sense of sgn τ_i,
from δ_{i−1}/|δ_{i−1}| to δ_i/|δ_i|, sweeping an arc of length exactly |τ_i| and no more, and attaining
each direction of that arc at exactly one parameter. Moreover the unit-tangent map is an immersion on
the open junction arc: parametrized by arclength, its angular derivative is nonzero at every interior
parameter, while at the two ends it and all its derivatives vanish, the junction meeting the straight
edges flat to infinite order.
(c) L_ε has the same double points as L, with the same strands, the same over/under assignment and
hence the same crossing signs and the same writhe.
(d) rot(L_ε) = rot(L).
(e) The disc package is returned. There are pairwise disjoint closed discs D₁,…,D_c, one about each
corner q_i, such that each D_i meets no edge of L that is not incident to q_i, contains no double point
of L, meets the two incident edges exactly in the two sub-segments of length ε at q_i, and contains the
whole of the modification made at q_i."

## Printed notion → Lean (CV's printed domain; SM's model through the bridge of §1)

* "closed polygon with corners q₁,…,q_c" (33): `L : LabelledTuple n` (CV:def:polygon, `n ≥ 3`), corners
  `L i`, edges `δ_i = edge L i`, closed edges `edgeSegment L i` (`CV.polygon_definition.edge_segment`).
  Its SM one-component polygon object is `polyComp L hreg : PolyComp` (§1); `n ≥ 3` (CV:def:polygon)
  is `Regular.three_le`, supplied by the regularity hypothesis under the accepted CV binder `[NeZero n]`
  for labelled polygons (CV.Setup, CV.Rotation, CV:lem:uniformrot) — no `hn` hypothesis is added.
* "the principal turns of L all exist" (35–36): `Regular L` (CV:def:regular (B), `regular_iff_principalTurns`);
  "and are nonzero": `∀ i, principalTurn L i ≠ 0` (CV:def:regular (A); `principalTurn_eq_sm` is `rfl`).
* "L has finitely many double points, all transversal, none of them a corner; no corner of L lies on an
  edge of L other than the two incident to it" (36–38): `Diagrammatic L` — CV:def:diagrammatic
  (d1_setup.tex:316–320) is exactly this list (CV:thm:carrierfloor (B), d3:762, names the input "a
  diagrammatic closed polygon"; (C), d3:784–786, "the no-triple condition repeats the shared-image clause
  of Definition def:diagrammatic").  Through `single_generic_of_diagrammatic` this is the generic
  one-component shadow of SM (`regular`, `tail_off`, `transverse`, `no_triple`), so SM's model applies
  with no generic parent polygon assumed (45–55).
* "an oriented diagram whose underlying plane curve is L — L together with an over/under assignment at
  each of its double points" (33–35): `D : OverUnder (polyComp L hreg)`, the over strand at each crossing
  of the one-component shadow of `L`; the crossings ARE the printed double points
  (`crossingPoints_eq_selfIntersections`, via the accepted `CV.crossingPoint_bijOn`).  `D.toPolygonDiagram
  hL : SM.PolygonDiagram (polyComp L hreg)` is the same data with SM's `generic` field supplied by CV's
  hypotheses; `OverUnder.ofDiagram` / `toDiagram_ofDiagram` give the entry from any accepted `Diagram`
  whose shadow is the single polygon (the form CV:thm:carrierfloor (C) starts from).
* "clearance ε₀(L) > 0 … for every ε ∈ (0, ε₀(L)) there is …" (38–41): the existential
  `∃ ε₀, 0 < ε₀ ∧ ∀ D ε, 0 < ε → ε < ε₀ → Nonempty (RoundingWitness …)` — "the clearance is part of the
  conclusion and is quantified here" (41–43).  The printed value `ε₀(L) = ⅓ min{…}` (230–236) is
  `CV.clearance L hreg` (= `SM.CornerRounding.clearance`), and the "one curve and one diagram" that
  CV:thm:carrierfloor (A) names `Round(L, D, ε)` is `CV.roundingRecord` (= `SM.CornerRounding.roundedWitness`).
* "a C^∞ regular closed plane curve L_ε, and a diagram D_ε carried by it" (39–40): `W.Lε :
  SmoothRegularLoop`, `W.carried : Carried W.Lε (D.toPolygonDiagram hL).toDiagram` — `D_ε` is `D`
  (FR-R1; clause (c) "the same over/under assignment" is the identity `(D.toPolygonDiagram hL).overStrand
  = D.overStrand`, `rfl`).
* (a)–(e) are the fields of the accepted-for-review `SM.RoundingWitness` (Rounding_statement_FINAL.lean
  §5), read on CV's polygon; the two clauses where CV's vocabulary is its own are rendered in it:
  (c) "the same double points as L" = `SmoothRegularLoop.doublePoints W.Lε.γ = selfIntersections L`
  (CV:def:diagrammatic's double points); (d) `rotCurve W.curve = (rot L hreg : ℝ)` — CV:def:rot on both
  sides (`CV.rotCurve` for the curve, the `ε_i` ray formula `CV.rot` for the polygon); SM's `rotationNumber`
  enters only through the accepted theorem `CV.rot_eq_rotationNumber` (decision F2).

Row declaration: `CV.rounding : CV.CVRoundingData`, one field per printed sentence / clause. -/

namespace CV

open SM SM.Link
open scoped ContDiff

noncomputable section
open Classical

variable {n : ℕ} [NeZero n]

/-! ## 1. The bridge: CV's closed polygon and its diagram in SM's one-component model -/

/-- "Let L be a closed polygon with corners q₁,…,q_c" (d3:33): the labelled tuple `L` as SM's
one-component polygon object `PolyComp` (def:polygon, `k ≥ 3`); `k = n` and the vertex tuple is `L`.
The bound `3 ≤ n` of CV:def:polygon is supplied by regularity (`Regular.three_le`). -/
def polyComp (L : LabelledTuple n) (hreg : Regular L) : PolyComp := ⟨n, hreg.three_le, L⟩

@[simp] theorem polyComp_k (L : LabelledTuple n) (hreg : Regular L) : (polyComp L hreg).k = n := rfl

@[simp] theorem polyComp_P (L : LabelledTuple n) (hreg : Regular L) : (polyComp L hreg).P = L := rfl

/-- The printed hypotheses on `L` (d3:35–38) — "the principal turns of L all exist" (`Regular L`) and
"finitely many double points, all transversal, none of them a corner; no corner of L lies on an edge
of L other than the two incident to it" (`Diagrammatic L`, CV:def:diagrammatic) — make the one-component
shadow of `L` generic in SM's sense (`Shadow.Generic`: `regular`, `tail_off`, `transverse`,
`no_triple`), through the accepted label-level criterion `Shadow.single_generic_of`.  `tail_off` is the
last clause of `Diagrammatic`; `transverse` and `no_triple` are clauses 2 and 3 of the accepted
`Diagrammatic.crossingGeometry` (CV/Setup.lean:1566). -/
theorem single_generic_of_diagrammatic {L : LabelledTuple n} (hL : Diagrammatic L)
    (hreg : Regular L) : (Shadow.single (polyComp L hreg)).Generic :=
  Shadow.single_generic_of (polyComp L hreg) ((regular_iff_sm L).mp hreg) hL.2.2.2.2
    (fun a b hna hmeet => by
      obtain ⟨x, hxa, hxb⟩ := hmeet
      exact (hL.crossingGeometry.2.1 a b hna x hxa hxb).2.2)
    (by
      rintro ⟨a, b, c, hab, hbc, hac, x, ⟨hxa, hxb⟩, hxc⟩
      exact hL.crossingGeometry.2.2 ⟨a, b, c, x, hab, hbc, hac, hxa, hxb, hxc⟩)

omit [NeZero n] in
/-- Reading: for `n ≥ 3` the hypothesis "the principal turns of L all exist" (d3:35–36) is implied by
the diagrammatic hypotheses (tier 1 `CarrierGeometry`, accepted `CarrierGeometry.regular`); the printed
statement lists it separately and so does the row. -/
theorem Diagrammatic.regular (hn : 3 ≤ n) {L : LabelledTuple n} (hL : Diagrammatic L) : Regular L :=
  (regular_iff_sm L).mpr ((CarrierGeometry.ofDiagrammatic hL).regular hn)

/-- The double points of `L` (CV:def:diagrammatic, `selfIntersections L`) are the crossing points of
the one-component shadow of `L` (accepted `CV.crossingPoint_bijOn` through `Shadow.single_crossingPoint`
and `Shadow.singleCrossingEquiv`). -/
theorem crossingPoints_eq_selfIntersections {L : LabelledTuple n} (hL : Diagrammatic L)
    (hreg : Regular L) :
    {p : Plane | ∃ x : (Shadow.single (polyComp L hreg)).Crossing,
        p = (Shadow.single (polyComp L hreg)).crossingPoint x} = selfIntersections L := by
  have gen := single_generic_of_diagrammatic hL hreg
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    rw [Shadow.single_crossingPoint _ gen]
    exact crossingPoint_mem_selfIntersections hL _
  · intro hp
    obtain ⟨c, hc⟩ : ∃ c : SM.Crossing (polyComp L hreg).P, SM.crossingPoint c = p :=
      exists_crossing_of_selfIntersection hreg.three_le hL hp
    refine ⟨(Shadow.singleCrossingEquiv (polyComp L hreg)).symm c, ?_⟩
    rw [Shadow.single_crossingPoint _ gen, Equiv.apply_symm_apply]
    exact hc.symm

/-- "an oriented diagram whose underlying plane curve is L — L together with an over/under assignment
at each of its double points" (d3:33–35): the over/under assignment.  The double points of `L` are the
crossings of its one-component shadow (`crossingPoints_eq_selfIntersections`); at each the over strand
is one of the two strands through it.  With `L` this is the printed `D`; the printed hypotheses on `L`
supply the `generic` field of SM's `PolygonDiagram` (`toPolygonDiagram`). -/
structure OverUnder (C : PolyComp) where
  /-- the over strand at each double point -/
  overStrand : (Shadow.single C).Crossing → (Shadow.single C).Strand
  /-- the over strand is one of the two strands of the double point -/
  over_mem : ∀ x, overStrand x ∈ x.val

namespace OverUnder

/-- The printed `D` as SM's `PolygonDiagram`: the same over/under assignment, with the genericity of
the shadow taken from CV's hypotheses (`single_generic_of_diagrammatic`). -/
def toPolygonDiagram {L : LabelledTuple n} {hreg : Regular L} (hL : Diagrammatic L)
    (D : OverUnder (polyComp L hreg)) : PolygonDiagram (polyComp L hreg) :=
  ⟨single_generic_of_diagrammatic hL hreg, D.overStrand, D.over_mem⟩

@[simp] theorem toPolygonDiagram_overStrand {L : LabelledTuple n} {hreg : Regular L}
    (hL : Diagrammatic L) (D : OverUnder (polyComp L hreg)) :
    (D.toPolygonDiagram hL).overStrand = D.overStrand := rfl

@[simp] theorem toPolygonDiagram_toDiagram_Γ {L : LabelledTuple n} {hreg : Regular L}
    (hL : Diagrammatic L) (D : OverUnder (polyComp L hreg)) :
    (D.toPolygonDiagram hL).toDiagram.Γ = Shadow.single (polyComp L hreg) := rfl

/-- The over/under assignment of an SM `PolygonDiagram`. -/
def ofPolygonDiagram {C : PolyComp} (D : PolygonDiagram C) : OverUnder C := ⟨D.overStrand, D.over_mem⟩

theorem toPolygonDiagram_ofPolygonDiagram {L : LabelledTuple n} {hreg : Regular L}
    (hL : Diagrammatic L) (D : PolygonDiagram (polyComp L hreg)) :
    (ofPolygonDiagram D).toPolygonDiagram hL = D := by
  cases D; rfl

/-- The over/under assignment of any accepted `Diagram` whose shadow is the single polygon `C`
("an oriented diagram whose underlying plane curve is L", the form CV:thm:carrierfloor (C) starts
from). -/
def ofDiagram (C : PolyComp) (D : Diagram) (hD : D.Γ = Shadow.single C) : OverUnder C :=
  ofPolygonDiagram (PolygonDiagram.ofDiagram D hD)

/-- The carried diagram of the row, for an input given as an accepted `Diagram`, is that `Diagram`. -/
theorem toDiagram_ofDiagram {L : LabelledTuple n} {hreg : Regular L} (hL : Diagrammatic L)
    (D : Diagram) (hD : D.Γ = Shadow.single (polyComp L hreg)) :
    ((ofDiagram _ D hD).toPolygonDiagram hL).toDiagram = D := by
  unfold ofDiagram
  rw [toPolygonDiagram_ofPolygonDiagram]
  exact PolygonDiagram.toDiagram_ofDiagram D hD

end OverUnder

/-! ## 2. The named construction: the clearance `ε₀(L)` and the record `Round(L, D, ε)`

The printed statement is existential (d3:38–43); CV:thm:carrierfloor (A) (d3:745–760) names the
construction of the printed proof — "the junction inserted at the corner q_i is determined by ε, by the
two incident unit directions and by the transition profile, which is fixed once and for all" — as
`Round(L, D, ε) = (L_ε, D_ε)`.  Both are SM's `CornerRounding.clearance` / `CornerRounding.roundedWitness`
on the bridge; they are exported here under CV names for that consumer (FR-R2). -/

/-- The clearance `ε₀(L) = ⅓ min{min_i min_{k≠i} |q_k − q_i|, min_i dist(q_i, non-incident closed
edges), min_i |δ_i|, min_{i, x double point} |x − q_i|}` of the printed proof (d3:230–236), a function
of the polygon `L` alone. -/
def clearance (L : LabelledTuple n) (hreg : Regular L) : ℝ :=
  CornerRounding.clearance (polyComp L hreg)

/-- "Every listed quantity is positive" (d3:241–247): `ε₀(L) > 0` under the printed hypotheses. -/
theorem clearance_pos {L : LabelledTuple n} (hL : Diagrammatic L) (hreg : Regular L) :
    0 < clearance L hreg :=
  CornerRounding.clearance_pos (single_generic_of_diagrammatic hL hreg)

/-- The hypotheses of the printed construction at an admissible `ε ∈ (0, ε₀(L))`, in SM's bundle. -/
theorem roundingAdmissible {L : LabelledTuple n} (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) {ε : ℝ}
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg) :
    CornerRounding.Admissible (polyComp L hreg) (D.toPolygonDiagram hL) ε :=
  ⟨fun i => hturn i, hε, hε₀⟩

/-- The rounding record `Round(L, D, ε) = (L_ε, D_ε)` (CV:thm:carrierfloor (A), d3:745–760): the
printed construction — junction arcs of the fixed transition profile `φ = Real.smoothTransition` at the
corners, `L` itself elsewhere, the diagram data inherited — returned with every clause (a)–(e) read from
it.  This is `SM.CornerRounding.roundedWitness`; `roundingRecord_eq` records the identity. -/
def roundingRecord {L : LabelledTuple n} (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) {ε : ℝ}
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg) :
    RoundingWitness (polyComp L hreg) (D.toPolygonDiagram hL) ε :=
  CornerRounding.roundedWitness (roundingAdmissible hL hreg hturn D hε hε₀)

theorem roundingRecord_eq {L : LabelledTuple n} (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) {ε : ℝ}
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg) :
    roundingRecord hL hreg hturn D hε hε₀ =
      CornerRounding.roundedWitness (roundingAdmissible hL hreg hturn D hε hε₀) := rfl

/-- The rounded curve of the record is SM's `roundedLoop` (the one curve of (A)). -/
theorem roundingRecord_Lε {L : LabelledTuple n} (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) {ε : ℝ}
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg) :
    (roundingRecord hL hreg hturn D hε hε₀).Lε =
      CornerRounding.roundedLoop (roundingAdmissible hL hreg hturn D hε hε₀) := rfl

/-! ## 3. The two clauses read in CV's own vocabulary, on any witness -/

section Witness

variable {L : LabelledTuple n} {hreg : Regular L} {hL : Diagrammatic L}
  {D : OverUnder (polyComp L hreg)} {ε : ℝ}
  (W : RoundingWitness (polyComp L hreg) (D.toPolygonDiagram hL) ε)

/-- (d) "rot(L_ε) = rot(L)" (d3:83), "rot as in Definition def:rot" (32): the rotation `rot(γ) = tw(T_γ)`
of the `C¹` regular curve `L_ε` (`CV.rotCurve`, d1_setup.tex:775–780) equals the `ε_i` ray formula
`CV.rot` of the polygon (d1_setup.tex:734–739).  From SM's `rot_eq` (whose right-hand side is
lem:rot's `rotationNumber`) and the accepted `CV.rot_eq_rotationNumber` (decision F2). -/
theorem rotCurve_eq_rot : rotCurve W.curve = (rot L hreg : ℝ) := by
  rw [rot_eq_rotationNumber hreg]
  exact W.rot_eq

/-- (c) "L_ε has the same double points as L" (d3:80): the double points of the rounded curve are the
printed double points of `L`, CV:def:diagrammatic's `selfIntersections L`. -/
theorem doublePoints_eq_selfIntersections :
    SmoothRegularLoop.doublePoints W.Lε.γ = selfIntersections L := by
  rw [W.same_double_points]
  exact crossingPoints_eq_selfIntersections hL hreg

end Witness

/-! ## 4. The row bundle: one field per printed sentence / clause -/

/-- CV:lem:rounding (d3_floor.tex:31–93), one field per printed sentence or clause, on CV's printed
domain: a labelled polygon `L` with CV:def:diagrammatic, CV:def:regular and nonzero principal turns,
and an over/under assignment `D` at its double points.  The existence sentence (`exists_clearance`)
carries the theorem; the clause fields state how each printed clause reads on a witness (the accepted
`SM.RoundingWitness` of the bridge), with the two CV-specific readings — (c) "the same double points"
in `selfIntersections`, (d) `rot` as in CV:def:rot on both sides — in CV's vocabulary. -/
structure CVRoundingData : Prop where
  /-- "Then there is a clearance ε₀(L) > 0 such that for every ε ∈ (0, ε₀(L)) there is a C^∞ regular
  closed plane curve L_ε, and a diagram D_ε carried by it, with these properties [(a)–(e)]" (d3:38–41),
  under "Assume the principal turns of L all exist and are nonzero; that L has finitely many double
  points, all transversal, none of them a corner; and that no corner of L lies on an edge of L other
  than the two incident to it" (35–38).  "The clearance is part of the conclusion and is quantified
  here" (41–43): it depends on `L` alone, not on the over/under assignment `D` (the printed `ε₀(L)`). -/
  exists_clearance : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L),
    (∀ i, principalTurn L i ≠ 0) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (D : OverUnder (polyComp L hreg)) (ε : ℝ), 0 < ε → ε < ε₀ →
      Nonempty (RoundingWitness (polyComp L hreg) (D.toPolygonDiagram hL) ε)
  /-- "a C^∞ regular closed plane curve L_ε, and a diagram D_ε carried by it" (d3:39–40). -/
  smooth_regular_carried : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
      (D : OverUnder (polyComp L hreg)) (ε : ℝ)
      (W : RoundingWitness (polyComp L hreg) (D.toPolygonDiagram hL) ε),
    ContDiff ℝ ∞ W.Lε.γ ∧ Function.Periodic W.Lε.γ 1 ∧ (∀ t, deriv W.Lε.γ t ≠ 0) ∧
      Nonempty (Carried W.Lε (D.toPolygonDiagram hL).toDiagram)
  /-- (a) "L_ε coincides with L outside the union of the discs of radius ε about the corners"
  (d3:57–58): as a set statement, and parametrically — on the straight part along edge `j` the curve
  runs straight in the direction `δ_j/|δ_j|`. -/
  a : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
      (D : OverUnder (polyComp L hreg)) (ε : ℝ)
      (W : RoundingWitness (polyComp L hreg) (D.toPolygonDiagram hL) ε),
    (∀ p : Plane, p ∉ (⋃ i, cornerDisc (polyComp L hreg) ε i) →
      (p ∈ Set.range W.Lε.γ ↔ p ∈ ⋃ i : ZMod n, edgeSegment L i)) ∧
    ∀ j < n, ∀ t ∈ Set.Icc (W.b j) (W.a (j + 1)),
      W.Lε.γ t = W.Lε.γ (W.b j) + (W.speed * (t - W.b j)) • normalize (edge L j)
  /-- (b) "Inside the disc about q_i the unit tangent moves strictly monotonically, in the sense of
  sgn τ_i, from δ_{i−1}/|δ_{i−1}| to δ_i/|δ_i|, sweeping an arc of length exactly |τ_i| and no more,
  and attaining each direction of that arc at exactly one parameter. Moreover the unit-tangent map is
  an immersion on the open junction arc: parametrized by arclength, its angular derivative is nonzero
  at every interior parameter, while at the two ends it and all its derivatives vanish, the junction
  meeting the straight edges flat to infinite order" (d3:59–66).  The junction at corner `j` is the
  parameter interval `[a j, b j]` (all of the curve inside the disc about `q_j`, by (e)); `θ j` is its
  tangent-angle lift; the parameter is arclength up to the constant speed.  "Both clauses are
  exported" (68–79): strict monotonicity (`StrictMonoOn`/`StrictAntiOn`) and the nonzero derivative
  are separate conjuncts. -/
  b : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
      (D : OverUnder (polyComp L hreg)) (ε : ℝ)
      (W : RoundingWitness (polyComp L hreg) (D.toPolygonDiagram hL) ε) (j : ℕ), j < n →
    (∀ t ∈ Set.Icc (W.a j) (W.b j), W.Lε.γ t ∈ cornerDisc (polyComp L hreg) ε j) ∧
    ContDiff ℝ ∞ (W.θ j) ∧ IsLiftOn W.T (W.θ j) (W.a j) (W.b j) ∧
    (∀ t, euclideanLength (deriv W.Lε.γ t) = W.speed) ∧
    W.T (W.a j) = normalize (edge L ((j : ZMod n) - 1)) ∧ W.T (W.b j) = normalize (edge L j) ∧
    W.θ j (W.b j) - W.θ j (W.a j) = principalTurn L j ∧
    (∀ t ∈ Set.Icc (W.a j) (W.b j), W.θ j t ∈ Set.uIcc (W.θ j (W.a j)) (W.θ j (W.b j))) ∧
    (0 < principalTurn L j → StrictMonoOn (W.θ j) (Set.Icc (W.a j) (W.b j))) ∧
    (principalTurn L j < 0 → StrictAntiOn (W.θ j) (Set.Icc (W.a j) (W.b j))) ∧
    (∀ β ∈ Set.uIcc (W.θ j (W.a j)) (W.θ j (W.b j)),
      ∃! t, t ∈ Set.Icc (W.a j) (W.b j) ∧ W.θ j t = β) ∧
    Set.InjOn W.T (Set.Icc (W.a j) (W.b j)) ∧
    (∀ t ∈ Set.Ioo (W.a j) (W.b j), deriv (W.θ j) t ≠ 0) ∧
    (∀ m : ℕ, 1 ≤ m → iteratedDeriv m (W.θ j) (W.a j) = 0 ∧ iteratedDeriv m (W.θ j) (W.b j) = 0) ∧
    (∀ m : ℕ, 2 ≤ m → iteratedDeriv m W.Lε.γ (W.a j) = 0 ∧ iteratedDeriv m W.Lε.γ (W.b j) = 0) ∧
    (∀ t ≤ W.a j, W.θ j t = W.θ j (W.a j)) ∧ (∀ t, W.b j ≤ t → W.θ j t = W.θ j (W.b j))
  /-- (c) "L_ε has the same double points as L, with the same strands, the same over/under assignment
  and hence the same crossing signs and the same writhe" (d3:80–82).  "The same double points": the
  double points of `L_ε` are CV:def:diagrammatic's `selfIntersections L`.  "The same strands": each
  occurrence is traversed on the straight part of its strand's edge, in that edge's direction.  "The
  same over/under assignment": the carried diagram's over strand is `D`'s.  "The same crossing signs
  and the same writhe": the smooth signs (`sgn det` of the over velocity followed by the under
  velocity) and their sum are those of `D`. -/
  c : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
      (D : OverUnder (polyComp L hreg)) (ε : ℝ)
      (W : RoundingWitness (polyComp L hreg) (D.toPolygonDiagram hL) ε),
    SmoothRegularLoop.doublePoints W.Lε.γ = selfIntersections L ∧
    (∀ v : (D.toPolygonDiagram hL).toDiagram.Γ.Visit,
      W.carried.τ v ∈ Set.Ioo (W.b ((D.toPolygonDiagram hL).label v).val)
        (W.a (((D.toPolygonDiagram hL).label v).val + 1)) ∧
      ∃ r : ℝ, 0 < r ∧ deriv W.Lε.γ (W.carried.τ v) = r • edge L ((D.toPolygonDiagram hL).label v)) ∧
    (D.toPolygonDiagram hL).overStrand = D.overStrand ∧
    (∀ x : (D.toPolygonDiagram hL).toDiagram.Γ.Crossing,
      W.carried.smoothSign x = (D.toPolygonDiagram hL).toDiagram.sign x) ∧
    W.carried.smoothWrithe = (D.toPolygonDiagram hL).toDiagram.writhe
  /-- (d) "rot(L_ε) = rot(L)" (d3:83), "Here rot is as in Definition def:rot" (32): `CV.rotCurve` of
  the rounded `C¹` regular curve and the `ε_i` ray formula `CV.rot` of the polygon. -/
  d : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
      (D : OverUnder (polyComp L hreg)) (ε : ℝ)
      (W : RoundingWitness (polyComp L hreg) (D.toPolygonDiagram hL) ε),
    rotCurve W.curve = (rot L hreg : ℝ)
  /-- (e) "There are pairwise disjoint closed discs D₁,…,D_c, one about each corner q_i, such that each
  D_i meets no edge of L that is not incident to q_i, contains no double point of L, meets the two
  incident edges exactly in the two sub-segments of length ε at q_i, and contains the whole of the
  modification made at q_i" (d3:84–89); "its consumer asks for a disc meeting the diagram in one
  embedded arc and reads it here" (89–91): the modification is all of the curve in the disc, that arc
  is embedded, and the open straight parts avoid every disc. -/
  e : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
      (D : OverUnder (polyComp L hreg)) (ε : ℝ)
      (W : RoundingWitness (polyComp L hreg) (D.toPolygonDiagram hL) ε),
    (∀ i : ZMod n, IsDisc (cornerDisc (polyComp L hreg) ε i)) ∧
    (∀ i j : ZMod n, i ≠ j →
      Disjoint (cornerDisc (polyComp L hreg) ε i) (cornerDisc (polyComp L hreg) ε j)) ∧
    (∀ i : ZMod n, L i ∈ interior (cornerDisc (polyComp L hreg) ε i)) ∧
    (∀ i j : ZMod n, ¬ incident i j → Disjoint (cornerDisc (polyComp L hreg) ε i) (edgeSegment L j)) ∧
    (∀ (i : ZMod n) (x : (D.toPolygonDiagram hL).toDiagram.Γ.Crossing),
      (D.toPolygonDiagram hL).toDiagram.Γ.crossingPoint x ∉ cornerDisc (polyComp L hreg) ε i) ∧
    (∀ i : ZMod n, cornerDisc (polyComp L hreg) ε i ∩ edgeSegment L i = subsegOut (polyComp L hreg) ε i) ∧
    (∀ i : ZMod n,
      cornerDisc (polyComp L hreg) ε i ∩ edgeSegment L (i - 1) = subsegIn (polyComp L hreg) ε i) ∧
    (∀ j < n, ∀ t ∈ Set.Icc (W.a j) (W.b j), W.Lε.γ t ∈ cornerDisc (polyComp L hreg) ε j) ∧
    (∀ j < n, ∀ t ∈ Set.Ico (0 : ℝ) 1,
      W.Lε.γ t ∈ cornerDisc (polyComp L hreg) ε j → t ∈ Set.Icc (W.a j) (W.b j)) ∧
    (∀ j < n, Set.InjOn W.Lε.γ (Set.Icc (W.a j) (W.b j))) ∧
    (∀ j < n, ∀ t ∈ Set.Ioo (W.b j) (W.a (j + 1)), W.Lε.γ t ∉ ⋃ i, cornerDisc (polyComp L hreg) ε i)

/-- CV:lem:rounding, from `SM.cf_lem_rounding` through the bridge of §1: the clearance is the printed
`ε₀(L)` (`clearance`), the witness the printed construction (`roundingRecord`); the clause fields are
SM's readings on the bridge, with (c)'s double points and (d)'s `rot` re-read in CV's vocabulary
(`doublePoints_eq_selfIntersections`, `rotCurve_eq_rot`). -/
theorem rounding : CVRoundingData where
  exists_clearance := fun L hL hreg hturn =>
    ⟨clearance L hreg, clearance_pos hL hreg,
      fun D _ε hε hε₀ => ⟨roundingRecord hL hreg hturn D hε hε₀⟩⟩
  smooth_regular_carried := fun _ hL _ D _ W =>
    SM.cf_lem_rounding.smooth_regular_carried _ (D.toPolygonDiagram hL) _ W
  a := fun _ hL _ D _ W => SM.cf_lem_rounding.a _ (D.toPolygonDiagram hL) _ W
  b := fun _ hL _ D _ W j hj => SM.cf_lem_rounding.b _ (D.toPolygonDiagram hL) _ W j hj
  c := fun _ _ _ _ _ W =>
    ⟨doublePoints_eq_selfIntersections W, fun v => ⟨W.same_strands v, W.same_strand_dir v⟩, rfl,
      W.same_signs, W.same_writhe⟩
  d := fun _ _ _ _ _ W => rotCurve_eq_rot W
  e := fun _ hL _ D _ W => SM.cf_lem_rounding.e _ (D.toPolygonDiagram hL) _ W

/-- The existence sentence for an input given as an accepted `Diagram` whose shadow is the single
polygon `L` ("an oriented diagram whose underlying plane curve is L"; the form of CV:thm:carrierfloor
(C)): the carried diagram is that `Diagram` itself (`OverUnder.toDiagram_ofDiagram`). -/
theorem rounding_of_diagram (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : Diagram) (hD : D.Γ = Shadow.single (polyComp L hreg)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Nonempty (RoundingWitness (polyComp L hreg) ((OverUnder.ofDiagram _ D hD).toPolygonDiagram hL) ε) := by
  obtain ⟨ε₀, hpos, hW⟩ := rounding.exists_clearance L hL hreg hturn
  exact ⟨ε₀, hpos, fun ε hε hε₀ => hW _ ε hε hε₀⟩

/-- The clearance of the existence sentence can be taken to be the printed `ε₀(L)`: for every
`ε ∈ (0, ε₀(L))` the record `Round(L, D, ε)` is a witness (the form CV:thm:carrierfloor (B) reads,
"Take ε₁ = ε₀(L)"). -/
theorem exists_witness_of_lt_clearance (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) {ε : ℝ}
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg) :
    Nonempty (RoundingWitness (polyComp L hreg) (D.toPolygonDiagram hL) ε) :=
  ⟨roundingRecord hL hreg hturn D hε hε₀⟩

end

end CV
