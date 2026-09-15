import SM.FrontSmooth
import SM.TurnLift
import SM.LinkDiagramRecord
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # SM cf:lem-rounding — corner rounding of a polygonal diagram (FIXED-STATEMENT, FINAL)

Source: reference/SM/sm-3-statesum.tex:3644-3700 (statement), 3701-3869 (proof).  Judge's synthesis
of the two architect candidates (A: model-first, existential clearance; B: proof-first, named
construction), 2026-09-14.  Decision record: work/drafts/rounding/PLAN_FINAL.md; chain and
assembly: Skeleton_FINAL.lean.  SKELETON: the statement text of Rounding_statement_FINAL.lean verbatim (sections 1-6), then the
construction (§7), the chain of leaf lemmas (§8, proved by the seven units), the assembly (§9, proved) and the row (§10, proved).
Check: `cd work/lean && lake env lean ../drafts/rounding/Skeleton_FINAL.lean`.

## The printed statement (sm-3:3644-3700, clause by clause)

"Let L be a closed polygon with corners q₁,…,q_c, and let D be an oriented diagram whose underlying
plane curve is L — L together with an over/under assignment at each of its double points. Assume the
principal turns of L all exist and are nonzero; that L has finitely many double points, all
transversal, none of them a corner; and that no corner of L lies on an edge of L other than the two
incident to it. Then there is a clearance ε₀(L) > 0 such that for every ε ∈ (0, ε₀(L)) there is a
C^∞ regular closed plane curve L_ε, and a diagram D_ε carried by it, with these properties.
(a) L_ε coincides with L outside the union of the discs of radius ε about the corners.
(b) Inside the disc about q_i the unit tangent moves strictly monotonically, in the sense of sgn ϑ_i,
from δ_{i−1}/|δ_{i−1}| to δ_i/|δ_i|, sweeping an arc of length exactly |ϑ_i| and no more, and
attaining each direction of that arc at exactly one parameter. Moreover the unit-tangent map is an
immersion on the open junction arc: parametrized by arclength, its angular derivative is nonzero at
every interior parameter, while at the two ends it and all its derivatives vanish, the junction
meeting the straight edges flat to infinite order.
(c) L_ε has the same double points as L, with the same strands, the same over/under assignment and
hence the same crossing signs and the same writhe.
(d) rot(L_ε) = rot(L).
(e) The disc package is returned. There are pairwise disjoint closed discs D₁,…,D_c, one about each
corner q_i, such that each D_i meets no edge of L that is not incident to q_i, contains no double
point of L, meets the two incident edges exactly in the two sub-segments of length ε at q_i, and
contains the whole of the modification made at q_i."

## Printed notion → Lean (model decision, PLAN_FINAL.md §1)

| printed | Lean |
|---|---|
| closed polygon `L` with corners `q_i`, edges `δ_i = q_{i+1} − q_i` | `C : PolyComp` (accepted def:polygon object with `3 ≤ k`), `L = C.P : LabelledTuple C.k`, corners `C.P i`, edges `edge C.P i` |
| "oriented diagram whose underlying plane curve is L"; finitely many transversal double points, none a corner, no corner on a non-incident edge | `PolygonDiagram C` = the accepted one-component `Diagram` on the shadow `Shadow.single C` (its `Shadow.Generic` is exactly the printed list: `regular`, `tail_off`, `transverse`, `no_triple`; the over strand is the over/under assignment); `PolygonDiagram.ofDiagram` converts any accepted `D : Diagram` with `D.Γ = Shadow.single C` |
| "the principal turns of L all exist and are nonzero" | `Regular C.P` (in `Generic`) and `∀ i, principalTurn C.P i ≠ 0` |
| "clearance ε₀(L) > 0 … for every ε ∈ (0, ε₀(L)) there is …" | `∃ ε₀, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ → Nonempty (RoundingWitness C D ε)` (Q3: the clearance is quantified in the conclusion; the explicit value ⅓·min{η_v,η_e,η_ℓ,η_X} and the printed construction are the named witnesses `CornerRounding.clearance`, `CornerRounding.roundedWitness` of the skeleton, which cf:thm-carrierfloor (A) reads) |
| "a C^∞ regular closed plane curve L_ε" | `Lε : SmoothRegularLoop` = the accepted `SmoothLoop` (`C^∞`, 1-periodic, FrontSmooth.lean) with `regular : ∀ t, deriv γ t ≠ 0`; the accepted `ClosedC1Curve` is `Lε.toClosedC1Curve` (no second `rot`) |
| "a diagram D_ε carried by it" | `Carried Lε D.toDiagram` (FR-1 for immersed circles: the polygonal `Diagram` carries the smooth curve's named record — occurrences at parameters `τ`, pairing by `twin`, transversality, cyclic order via the accepted `cycBetween`/`visitCoord`, over/under from the polygonal record with sign consistency); `D_ε` *is* `D`, which is what (c) asserts |
| the unit tangent, arclength, tangent-angle lift, `rot` | `normalize (deriv Lε.γ t)` (= `tangentLoop.T`), constant speed `speed` (so arclength = `speed · Δt`), `IsLiftOn` (TurnLift.lean), `ClosedC1Curve.rot` (TurningNumber.lean), `rotationNumber` (lem:rot) |
| "the discs of radius ε about the corners" (closed, (e)) | `cornerDisc C ε i = {p | euclideanLength (p − C.P i) ≤ ε}` (Euclidean, not the product metric; `IsDisc` is the accepted clean-disc vocabulary, LinkMoves.lean) |
| "the two sub-segments of length ε at q_i" | `subsegOut C ε i`, `subsegIn C ε i` |
| "the modification made at q_i" | the junction arc `Lε.γ '' Icc (a k) (b k)` of the subdivision `a b : ℕ → ℝ` (junction at corner `k` on `[a k, b k]`, straight along edge `k` on `[b k, a (k+1)]`, the pattern of the accepted `rot_eq_rotationNumber_of_rounding`) — and it is ALL of the curve inside the disc, an embedded arc (the consumer's reading, sm-3:3697-3699) |

One structure field per printed sub-clause in `RoundingWitness` (grouped (a)–(e)); one bundle field
per printed sentence/clause in `RoundingData` (the existence sentence carries the theorem, the clause
fields are its reading on a witness); main declaration `SM.cf_lem_rounding : RoundingData`. -/

namespace SM

open Link
open scoped ContDiff

noncomputable section
open Classical

/-! ## 1. The input: a polygon carrying an oriented diagram -/

/-- "an oriented diagram whose underlying plane curve is L — L together with an over/under
assignment at each of its double points" (sm-3:3647-3649), for the polygon `L = C.P`: the accepted
one-component `Diagram` on the shadow `Shadow.single C`.  Its `generic` field is the printed
hypothesis list — "finitely many double points, all transversal (`transverse`), none of them a corner
(`tail_off`); no corner of L lies on an edge of L other than the two incident to it (`tail_off`)",
plus `no_triple` (part of the accepted class of oriented diagrams, def:positive-lift) and
`regular` ("the principal turns of L all exist").  `toDiagram` is the accepted `Diagram`
(definitionally on the shadow `single C`); `ofDiagram` is the converse. -/
structure PolygonDiagram (C : PolyComp) where
  /-- the hypotheses on the underlying polygon (see above) -/
  generic : (Shadow.single C).Generic
  /-- "an over/under assignment at each of its double points": the over strand -/
  overStrand : (Shadow.single C).Crossing → (Shadow.single C).Strand
  /-- the over strand is one of the two strands of the double point -/
  over_mem : ∀ x, overStrand x ∈ x.val

namespace PolygonDiagram

variable {C : PolyComp} (D : PolygonDiagram C)

/-- the diagram `D` as an accepted `Diagram` (definitionally on the shadow `single C`) -/
abbrev toDiagram : Diagram := ⟨Shadow.single C, D.generic, D.overStrand, D.over_mem⟩

@[simp] theorem toDiagram_Γ : D.toDiagram.Γ = Shadow.single C := rfl

/-- the edge label `i ∈ ZMod k` of the strand of an occurrence -/
def label (v : D.toDiagram.Γ.Visit) : ZMod C.k := Shadow.singleStrandEquiv C v.2.val

/-- the edge label of a strand -/
def strandLabel (s : D.toDiagram.Γ.Strand) : ZMod C.k := Shadow.singleStrandEquiv C s

theorem regular (D : PolygonDiagram C) : Regular C.P := D.generic.regular ⟨0, Nat.one_pos⟩

/-- the input in the form of the accepted `Diagram` class: any diagram whose shadow is the single
polygon `C` -/
def ofDiagram : ∀ (D : Diagram), D.Γ = Shadow.single C → PolygonDiagram C
  | ⟨_, gen, ov, hov⟩, h => by
    simp only at h
    subst h
    exact ⟨gen, ov, hov⟩

/-- the conversion is the identity on the accepted diagram -/
theorem toDiagram_ofDiagram :
    ∀ (D : Diagram) (h : D.Γ = Shadow.single C), (ofDiagram D h).toDiagram = D
  | ⟨_, _, _, _⟩, h => by
    simp only at h
    subst h
    rfl

end PolygonDiagram

/-! ## 2. Euclidean discs about the corners and the ε-sub-segments -/

/-- the Euclidean distance of the oriented plane (not the product metric of `ℝ × ℝ`) -/
def eucDist (p q : Plane) : ℝ := euclideanLength (p - q)

/-- "the disc of radius ε about the corner q_i", closed ((a), (e)) -/
def cornerDisc (C : PolyComp) (ε : ℝ) (i : ZMod C.k) : Set Plane := {p | eucDist p (C.P i) ≤ ε}

/-- "the sub-segment of length ε at q_i" on the outgoing edge `δ_i` -/
def subsegOut (C : PolyComp) (ε : ℝ) (i : ZMod C.k) : Set Plane :=
  {p | ∃ r : ℝ, 0 ≤ r ∧ r ≤ ε ∧ p = C.P i + r • normalize (edge C.P i)}

/-- "the sub-segment of length ε at q_i" on the incoming edge `δ_{i−1}` -/
def subsegIn (C : PolyComp) (ε : ℝ) (i : ZMod C.k) : Set Plane :=
  {p | ∃ r : ℝ, 0 ≤ r ∧ r ≤ ε ∧ p = C.P i - r • normalize (edge C.P (i - 1))}

/-- the underlying plane curve of the polygon, as a set -/
def polygonImage (C : PolyComp) : Set Plane := ⋃ i : ZMod C.k, edgeSegment C.P i

/-! ## 3. `C^∞` regular closed plane curves -/

/-- "a C^∞ regular closed plane curve": the accepted `SmoothLoop` (SM/FrontSmooth.lean: `C^∞`,
1-periodic — FR-3) whose velocity never vanishes.  The regular sub-class of the accepted smooth
class, as `ClosedC1Curve` is the regular `C¹` class; it is the input class of cf:lem-curl
("a connected C^∞ immersed circle"). -/
structure SmoothRegularLoop extends SmoothLoop where
  /-- regular: `γ' ≠ 0` everywhere -/
  regular : ∀ t, deriv γ t ≠ 0

namespace SmoothRegularLoop

/-- the accepted closed `C¹` regular curve of a `C^∞` regular loop (SM/TurningNumber.lean), whose
`rot` is the rotation of cf:def-turning — no second notion of `rot` -/
def toClosedC1Curve (c : SmoothRegularLoop) : ClosedC1Curve :=
  c.toSmoothLoop.toClosedC1Curve c.regular

@[simp] theorem toClosedC1Curve_γ (c : SmoothRegularLoop) : c.toClosedC1Curve.γ = c.γ := rfl

/-- the set of double points of a 1-periodic curve (as points of the plane) -/
def doublePoints (γ : ℝ → Plane) : Set Plane :=
  {p | ∃ s t : ℝ, s ∈ Set.Ico (0 : ℝ) 1 ∧ t ∈ Set.Ico (0 : ℝ) 1 ∧ s ≠ t ∧ γ s = p ∧ γ t = p}

end SmoothRegularLoop

/-! ## 4. A diagram carried by a `C^∞` regular closed curve (the smooth-diagram model)

FR-1 instantiated for immersed circles (sm-3:337-343 "a diagram here is a finite polygonal
immersion, or a regular smooth immersion …"; lem:gauss-pl-model "the crossing names, the four-ray
orders, the traversal direction and the over/under designations are retained"): the polygonal
one-component `Diagram X` is *carried by* the regular smooth loop `γ` when every occurrence of `X`
is realised at a parameter `τ v` of `γ` at the crossing point, the double points of `γ` are exactly
these pairs (paired by `X.twin`), the branches are transverse, the cyclic order of the occurrences
along the circle is that of `X` (the accepted `cycBetween`/`visitCoord`, as in the front block's
`Marking.between_iff`), and the over/under assignment is `X`'s — so that the crossing sign of the
smooth diagram (`sgn det` of the over velocity followed by the under velocity, def:positive-lift)
is `X.sign`.  This is the one smooth-diagram notion for cf:lem-rounding, cf:lem-curl and
cf:thm-carrierfloor; the front block's `SmoothFront.Marking` is the same reading with the front's
slope rule for over/under (a front is not a regular loop: it has cusps and the `no_vertical`
clause, so the two structures cannot be one).  Nothing here refers to edge directions of `X`, so
the notion applies to any immersed circle carrying a PL model, as cf:lem-curl needs. -/
structure Carried (γ : SmoothRegularLoop) (X : Diagram) where
  /-- one parameter circle -/
  one : X.Γ.c = 1
  /-- the parameter (in the fundamental period) at which the occurrence `v` is traversed -/
  τ : X.Γ.Visit → ℝ
  τ_mem : ∀ v, τ v ∈ Set.Ico (0 : ℝ) 1
  τ_inj : Function.Injective τ
  /-- the occurrence is traversed at the crossing point -/
  τ_eval : ∀ v, γ.γ (τ v) = X.Γ.crossingPoint v.1
  /-- every double point of `γ` is one of the crossings, with the two occurrences paired by `twin` -/
  doubles : ∀ s t : ℝ, s ∈ Set.Ico (0 : ℝ) 1 → t ∈ Set.Ico (0 : ℝ) 1 → s ≠ t → γ.γ s = γ.γ t →
    ∃ v : X.Γ.Visit, s = τ v ∧ t = τ (X.twin v)
  /-- transverse double points -/
  transverse : ∀ v, det (deriv γ.γ (τ v)) (deriv γ.γ (τ (X.twin v))) ≠ 0
  /-- the cyclic order of the occurrences along the oriented circle is that of `X` -/
  order : ∀ v w z : X.Γ.Visit,
    (cycBetween (τ v) (τ w) (τ z) ↔ cycBetween (X.visitCoord v) (X.visitCoord w) (X.visitCoord z))
  /-- the over/under assignment is `X`'s: the over-first tangent-determinant sign of the smooth
  double point equals the crossing sign of `X` -/
  sign_eq : ∀ x : X.Γ.Crossing,
    SignType.sign (det (deriv γ.γ (τ (X.overVisit x))) (deriv γ.γ (τ (X.underVisit x)))) = X.sign x

namespace Carried

variable {γ : SmoothRegularLoop} {X : Diagram} (c : Carried γ X)

/-- the crossing sign of the smooth diagram at `x`: `sgn det(velocity_over, velocity_under)` -/
def smoothSign (x : X.Γ.Crossing) : SignType :=
  SignType.sign (det (deriv γ.γ (c.τ (X.overVisit x))) (deriv γ.γ (c.τ (X.underVisit x))))

/-- the writhe of the smooth diagram -/
def smoothWrithe : ℤ := ∑ x : X.Γ.Crossing, (c.smoothSign x : ℤ)

theorem smoothSign_eq (x : X.Γ.Crossing) : c.smoothSign x = X.sign x := c.sign_eq x

theorem smoothWrithe_eq : c.smoothWrithe = X.writhe := by
  unfold smoothWrithe Diagram.writhe
  exact Finset.sum_congr rfl fun x _ => by rw [c.smoothSign_eq]

end Carried

/-! ## 5. The rounding witness: one field per printed sub-clause -/

/-- The data returned by cf:lem-rounding at a clearance-admissible `ε`: the curve `L_ε`, the
carried diagram (which is `D`), the subdivision of the parameter circle into junctions and straight
parts, the tangent-angle lifts of the junctions, and one Prop field per printed sub-clause of
(a)-(e).  The parameter is arclength up to the constant factor `speed` (so the printed arclength
`σ` along the junction at corner `k` is `speed · (t − a k)`, its length `ℓ = speed · (b k − a k)`). -/
structure RoundingWitness (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) where
  /-- "a C^∞ regular closed plane curve L_ε" -/
  Lε : SmoothRegularLoop
  /-- constant speed: the parameter is arclength scaled by `speed` -/
  speed : ℝ
  speed_pos : 0 < speed
  const_speed : ∀ t, euclideanLength (deriv Lε.γ t) = speed
  /-- "and a diagram D_ε carried by it": `D` itself, carried by `L_ε` -/
  carried : Carried Lε D.toDiagram
  /-- the subdivision `0 = a 0 < b 0 < a 1 < ⋯ < b (k−1) < a k = 1`: the junction at corner `j` runs
  on `[a j, b j]`, the straight part along edge `j` on `[b j, a (j+1)]` -/
  a : ℕ → ℝ
  b : ℕ → ℝ
  a_zero : a 0 = 0
  a_last : a C.k = 1
  a_lt_b : ∀ j < C.k, a j < b j
  b_lt_a : ∀ j < C.k, b j < a (j + 1)
  /-- the junction at `q_j` starts at `A₀ = q_j − ε δ_{j−1}/|δ_{j−1}|` … -/
  junction_start : ∀ j < C.k, Lε.γ (a j) = C.P j - ε • normalize (edge C.P ((j : ZMod C.k) - 1))
  /-- … and ends at `A₁ = q_j + ε δ_j/|δ_j|` -/
  junction_end : ∀ j < C.k, Lε.γ (b j) = C.P j + ε • normalize (edge C.P j)
  /-- (a) on the straight part along edge `j` the curve runs straight, at speed `speed`, in the
  direction `δ_j/|δ_j|`: it coincides with `L` there -/
  straight : ∀ j < C.k, ∀ t ∈ Set.Icc (b j) (a (j + 1)),
    Lε.γ t = Lε.γ (b j) + (speed * (t - b j)) • normalize (edge C.P j)
  /-- (a) "L_ε coincides with L outside the union of the discs of radius ε about the corners" -/
  outside : ∀ p : Plane, p ∉ (⋃ i, cornerDisc C ε i) →
    (p ∈ Set.range Lε.γ ↔ p ∈ polygonImage C)
  /-- (b) the tangent-angle lift of the junction at corner `j`: a `C^∞` function on `ℝ` … -/
  θ : ℕ → ℝ → ℝ
  θ_smooth : ∀ j < C.k, ContDiff ℝ ∞ (θ j)
  /-- … lifting the unit tangent on the closed junction interval -/
  θ_lift : ∀ j < C.k, IsLiftOn (fun t => normalize (deriv Lε.γ t)) (θ j) (a j) (b j)
  /-- … constant on the straight part before the junction … -/
  θ_const_left : ∀ j < C.k, ∀ t ≤ a j, θ j t = θ j (a j)
  /-- … and on the straight part after it -/
  θ_const_right : ∀ j < C.k, ∀ t, b j ≤ t → θ j t = θ j (b j)
  /-- (b) "from δ_{i−1}/|δ_{i−1}|" -/
  tangent_start : ∀ j < C.k, normalize (deriv Lε.γ (a j)) = normalize (edge C.P ((j : ZMod C.k) - 1))
  /-- (b) "to δ_i/|δ_i|" -/
  tangent_end : ∀ j < C.k, normalize (deriv Lε.γ (b j)) = normalize (edge C.P j)
  /-- (b) "sweeping an arc of length exactly |ϑ_i|": the lift increment is `ϑ_i` -/
  θ_sweep : ∀ j < C.k, θ j (b j) - θ j (a j) = principalTurn C.P j
  /-- (b) "… and no more": the lift stays within the swept arc -/
  θ_range : ∀ j < C.k, ∀ t ∈ Set.Icc (a j) (b j), θ j t ∈ Set.uIcc (θ j (a j)) (θ j (b j))
  /-- (b) "the unit tangent moves strictly monotonically, in the sense of sgn ϑ_i" -/
  θ_strict : ∀ j < C.k,
    (0 < principalTurn C.P j → StrictMonoOn (θ j) (Set.Icc (a j) (b j))) ∧
    (principalTurn C.P j < 0 → StrictAntiOn (θ j) (Set.Icc (a j) (b j)))
  /-- (b) "attaining each direction of that arc at exactly one parameter": every angle of the
  swept arc is attained at exactly one parameter of the closed junction … -/
  θ_unique : ∀ j < C.k, ∀ β ∈ Set.uIcc (θ j (a j)) (θ j (b j)),
    ∃! t, t ∈ Set.Icc (a j) (b j) ∧ θ j t = β
  /-- … and the unit tangent (as a vector) is injective on the closed junction -/
  direction_once : ∀ j < C.k, Set.InjOn (fun t => normalize (deriv Lε.γ t)) (Set.Icc (a j) (b j))
  /-- (b) "the unit-tangent map is an immersion on the open junction arc: parametrized by
  arclength, its angular derivative is nonzero at every interior parameter" (the parameter is
  arclength up to the factor `speed > 0`) -/
  immersion : ∀ j < C.k, ∀ t ∈ Set.Ioo (a j) (b j), deriv (θ j) t ≠ 0
  /-- (b) "while at the two ends it and all its derivatives vanish" -/
  flat_ends : ∀ j < C.k, ∀ m : ℕ, 1 ≤ m →
    iteratedDeriv m (θ j) (a j) = 0 ∧ iteratedDeriv m (θ j) (b j) = 0
  /-- (b) "the junction meeting the straight edges flat to infinite order": all derivatives of the
  curve of order `≥ 2` vanish at the two ends (those of a straight edge) -/
  flat_ends_curve : ∀ j < C.k, ∀ m : ℕ, 2 ≤ m →
    iteratedDeriv m Lε.γ (a j) = 0 ∧ iteratedDeriv m Lε.γ (b j) = 0
  /-- (c) "L_ε has the same double points as L": the double points of `L_ε` are exactly the
  crossing points of `L` -/
  same_double_points :
    SmoothRegularLoop.doublePoints Lε.γ =
      {p | ∃ x : D.toDiagram.Γ.Crossing, p = D.toDiagram.Γ.crossingPoint x}
  /-- (c) "with the same strands": each occurrence is traversed inside the straight part of its
  strand's edge … -/
  same_strands : ∀ v : D.toDiagram.Γ.Visit,
    carried.τ v ∈ Set.Ioo (b (D.label v).val) (a ((D.label v).val + 1))
  /-- … in the direction of that edge -/
  same_strand_dir : ∀ v : D.toDiagram.Γ.Visit,
    ∃ r : ℝ, 0 < r ∧ deriv Lε.γ (carried.τ v) = r • edge C.P (D.label v)
  /-- (c) "the same over/under assignment and hence the same crossing signs" -/
  same_signs : ∀ x : D.toDiagram.Γ.Crossing, carried.smoothSign x = D.toDiagram.sign x
  /-- (c) "and the same writhe" -/
  same_writhe : carried.smoothWrithe = D.toDiagram.writhe
  /-- (d) "rot(L_ε) = rot(L)" (cf:def-turning `rot` on the left, lem:rot on the right) -/
  rot_eq : Lε.toClosedC1Curve.rot = rotationNumber C.P
  /-- (e) "pairwise disjoint closed discs D₁,…,D_c" -/
  disc_isDisc : ∀ i, IsDisc (cornerDisc C ε i)
  disc_disjoint : ∀ i j, i ≠ j → Disjoint (cornerDisc C ε i) (cornerDisc C ε j)
  /-- (e) "one about each corner q_i" -/
  disc_center : ∀ i, C.P i ∈ interior (cornerDisc C ε i)
  /-- (e) "each D_i meets no edge of L that is not incident to q_i" -/
  disc_off_nonincident : ∀ i j, ¬ incident i j → Disjoint (cornerDisc C ε i) (edgeSegment C.P j)
  /-- (e) "contains no double point of L" -/
  disc_no_double : ∀ i (x : D.toDiagram.Γ.Crossing), D.toDiagram.Γ.crossingPoint x ∉ cornerDisc C ε i
  /-- (e) "meets the two incident edges exactly in the two sub-segments of length ε at q_i" -/
  disc_meets_out : ∀ i, cornerDisc C ε i ∩ edgeSegment C.P i = subsegOut C ε i
  disc_meets_in : ∀ i, cornerDisc C ε i ∩ edgeSegment C.P (i - 1) = subsegIn C ε i
  /-- (e) "and contains the whole of the modification made at q_i" -/
  disc_contains_modification : ∀ j < C.k, ∀ t ∈ Set.Icc (a j) (b j), Lε.γ t ∈ cornerDisc C ε j
  /-- (e) the modification is all of the curve in the disc ("a disc meeting the diagram in one
  embedded arc", sm-3:3697-3699) … -/
  disc_only_modification : ∀ j < C.k, ∀ t ∈ Set.Ico (0 : ℝ) 1,
    Lε.γ t ∈ cornerDisc C ε j → t ∈ Set.Icc (a j) (b j)
  /-- … and that arc is embedded -/
  junction_embedded : ∀ j < C.k, Set.InjOn Lε.γ (Set.Icc (a j) (b j))
  /-- (e) the modification is only there: the open straight parts avoid every disc -/
  straight_off_discs : ∀ j < C.k, ∀ t ∈ Set.Ioo (b j) (a (j + 1)), Lε.γ t ∉ ⋃ i, cornerDisc C ε i

namespace RoundingWitness

variable {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε)

/-- the rounded curve in the accepted `C¹` class (cf:def-turning) -/
def curve : ClosedC1Curve := W.Lε.toClosedC1Curve

/-- the unit tangent `T = γ'/|γ'|` -/
def T : ℝ → Plane := fun t => normalize (deriv W.Lε.γ t)

theorem T_eq_tangentLoop : W.T = W.curve.tangentLoop.T := rfl

theorem rot_curve : W.curve.rot = rotationNumber C.P := W.rot_eq

theorem smooth : ContDiff ℝ ∞ W.Lε.γ := W.Lε.smooth

theorem periodic : Function.Periodic W.Lε.γ 1 := W.Lε.periodic

theorem regular : ∀ t, deriv W.Lε.γ t ≠ 0 := W.Lε.regular

end RoundingWitness

/-! ## 6. The row bundle: one field per printed sentence / clause -/

/-- cf:lem-rounding (sm-3:3644-3700), one field per printed sentence or clause; the objects are
those of `RoundingWitness`.  The existence sentence (`exists_clearance`) carries the theorem; the
clause fields state how each printed clause reads on a witness (they are projections of
`RoundingWitness`, so the fixed content of (a)–(e) is the field list of that structure).
Model decisions: PLAN_FINAL.md §1 (input `PolygonDiagram`, output `SmoothRegularLoop` + `Carried`,
discs `cornerDisc`, subdivision `a b`). -/
structure RoundingData : Prop where
  /-- "Then there is a clearance ε₀(L) > 0 such that for every ε ∈ (0, ε₀(L)) there is a C^∞ regular
  closed plane curve L_ε, and a diagram D_ε carried by it, with these properties [(a)-(e)]." The
  clearance depends on the polygon `L` alone (the printed `ε₀(L)`; the hypotheses on `L` are the
  nonzero principal turns and the generic shadow), not on the over/under assignment `D`. -/
  exists_clearance : ∀ (C : PolyComp), (∀ i, principalTurn C.P i ≠ 0) → (Shadow.single C).Generic →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (D : PolygonDiagram C) (ε : ℝ), 0 < ε → ε < ε₀ →
      Nonempty (RoundingWitness C D ε)
  /-- "a C^∞ regular closed plane curve L_ε, and a diagram D_ε carried by it" -/
  smooth_regular_carried : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
      (W : RoundingWitness C D ε),
    ContDiff ℝ ∞ W.Lε.γ ∧ Function.Periodic W.Lε.γ 1 ∧ (∀ t, deriv W.Lε.γ t ≠ 0) ∧
      Nonempty (Carried W.Lε D.toDiagram)
  /-- (a) "L_ε coincides with L outside the union of the discs of radius ε about the corners." -/
  a : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (W : RoundingWitness C D ε),
    (∀ p : Plane, p ∉ (⋃ i, cornerDisc C ε i) → (p ∈ Set.range W.Lε.γ ↔ p ∈ polygonImage C)) ∧
    ∀ j < C.k, ∀ t ∈ Set.Icc (W.b j) (W.a (j + 1)),
      W.Lε.γ t = W.Lε.γ (W.b j) + (W.speed * (t - W.b j)) • normalize (edge C.P j)
  /-- (b) "Inside the disc about q_i the unit tangent moves strictly monotonically, in the sense of
  sgn ϑ_i, from δ_{i−1}/|δ_{i−1}| to δ_i/|δ_i|, sweeping an arc of length exactly |ϑ_i| and no more,
  and attaining each direction of that arc at exactly one parameter. Moreover the unit-tangent map is
  an immersion on the open junction arc: parametrized by arclength, its angular derivative is nonzero
  at every interior parameter, while at the two ends it and all its derivatives vanish, the junction
  meeting the straight edges flat to infinite order." -/
  b : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (W : RoundingWitness C D ε) (j : ℕ), j < C.k →
    (∀ t ∈ Set.Icc (W.a j) (W.b j), W.Lε.γ t ∈ cornerDisc C ε j) ∧
    ContDiff ℝ ∞ (W.θ j) ∧ IsLiftOn W.T (W.θ j) (W.a j) (W.b j) ∧
    (∀ t, euclideanLength (deriv W.Lε.γ t) = W.speed) ∧
    W.T (W.a j) = normalize (edge C.P ((j : ZMod C.k) - 1)) ∧ W.T (W.b j) = normalize (edge C.P j) ∧
    W.θ j (W.b j) - W.θ j (W.a j) = principalTurn C.P j ∧
    (∀ t ∈ Set.Icc (W.a j) (W.b j), W.θ j t ∈ Set.uIcc (W.θ j (W.a j)) (W.θ j (W.b j))) ∧
    (0 < principalTurn C.P j → StrictMonoOn (W.θ j) (Set.Icc (W.a j) (W.b j))) ∧
    (principalTurn C.P j < 0 → StrictAntiOn (W.θ j) (Set.Icc (W.a j) (W.b j))) ∧
    (∀ β ∈ Set.uIcc (W.θ j (W.a j)) (W.θ j (W.b j)),
      ∃! t, t ∈ Set.Icc (W.a j) (W.b j) ∧ W.θ j t = β) ∧
    Set.InjOn W.T (Set.Icc (W.a j) (W.b j)) ∧
    (∀ t ∈ Set.Ioo (W.a j) (W.b j), deriv (W.θ j) t ≠ 0) ∧
    (∀ m : ℕ, 1 ≤ m → iteratedDeriv m (W.θ j) (W.a j) = 0 ∧ iteratedDeriv m (W.θ j) (W.b j) = 0) ∧
    (∀ m : ℕ, 2 ≤ m → iteratedDeriv m W.Lε.γ (W.a j) = 0 ∧ iteratedDeriv m W.Lε.γ (W.b j) = 0) ∧
    (∀ t ≤ W.a j, W.θ j t = W.θ j (W.a j)) ∧ (∀ t, W.b j ≤ t → W.θ j t = W.θ j (W.b j))
  /-- (c) "L_ε has the same double points as L, with the same strands, the same over/under
  assignment and hence the same crossing signs and the same writhe." -/
  c : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (W : RoundingWitness C D ε),
    SmoothRegularLoop.doublePoints W.Lε.γ =
        {p | ∃ x : D.toDiagram.Γ.Crossing, p = D.toDiagram.Γ.crossingPoint x} ∧
    (∀ v : D.toDiagram.Γ.Visit,
      W.carried.τ v ∈ Set.Ioo (W.b (D.label v).val) (W.a ((D.label v).val + 1)) ∧
      ∃ r : ℝ, 0 < r ∧ deriv W.Lε.γ (W.carried.τ v) = r • edge C.P (D.label v)) ∧
    (∀ x : D.toDiagram.Γ.Crossing, W.carried.smoothSign x = D.toDiagram.sign x) ∧
    W.carried.smoothWrithe = D.toDiagram.writhe
  /-- (d) "rot(L_ε) = rot(L)." -/
  d : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (W : RoundingWitness C D ε),
    W.curve.rot = rotationNumber C.P
  /-- (e) "There are pairwise disjoint closed discs D₁,…,D_c, one about each corner q_i, such that
  each D_i meets no edge of L that is not incident to q_i, contains no double point of L, meets the
  two incident edges exactly in the two sub-segments of length ε at q_i, and contains the whole of the
  modification made at q_i." -/
  e : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (W : RoundingWitness C D ε),
    (∀ i, IsDisc (cornerDisc C ε i)) ∧
    (∀ i j, i ≠ j → Disjoint (cornerDisc C ε i) (cornerDisc C ε j)) ∧
    (∀ i, C.P i ∈ interior (cornerDisc C ε i)) ∧
    (∀ i j, ¬ incident i j → Disjoint (cornerDisc C ε i) (edgeSegment C.P j)) ∧
    (∀ i (x : D.toDiagram.Γ.Crossing), D.toDiagram.Γ.crossingPoint x ∉ cornerDisc C ε i) ∧
    (∀ i, cornerDisc C ε i ∩ edgeSegment C.P i = subsegOut C ε i) ∧
    (∀ i, cornerDisc C ε i ∩ edgeSegment C.P (i - 1) = subsegIn C ε i) ∧
    (∀ j < C.k, ∀ t ∈ Set.Icc (W.a j) (W.b j), W.Lε.γ t ∈ cornerDisc C ε j) ∧
    (∀ j < C.k, ∀ t ∈ Set.Ico (0 : ℝ) 1, W.Lε.γ t ∈ cornerDisc C ε j → t ∈ Set.Icc (W.a j) (W.b j)) ∧
    (∀ j < C.k, Set.InjOn W.Lε.γ (Set.Icc (W.a j) (W.b j))) ∧
    (∀ j < C.k, ∀ t ∈ Set.Ioo (W.b j) (W.a (j + 1)), W.Lε.γ t ∉ ⋃ i, cornerDisc C ε i)

/-- The existence sentence for the input given as an accepted `Diagram` whose shadow is the single
polygon `C` ("an oriented diagram whose underlying plane curve is L"): the carried diagram is that
`Diagram` itself (`PolygonDiagram.toDiagram_ofDiagram`). -/
theorem RoundingData.of_diagram (h : RoundingData) (C : PolyComp) (D : Diagram)
    (hD : D.Γ = Shadow.single C) (hturn : ∀ i, principalTurn C.P i ≠ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Nonempty (RoundingWitness C (PolygonDiagram.ofDiagram D hD) ε) := by
  obtain ⟨ε₀, hpos, hW⟩ := h.exists_clearance C hturn (PolygonDiagram.ofDiagram D hD).generic
  exact ⟨ε₀, hpos, fun ε hε hε₀ => hW _ ε hε hε₀⟩

/-! ## 7. The construction (printed proof, sm-3:3701-3869), as explicit definitions

The printed proof builds, at each corner, the junction `γ_ℓ(s) = A₀ + ∫₀^s (cos, sin)(θ_u + ϑ φ(t/ℓ)) dt`
with the fixed transition profile `φ = f(t)/(f(t)+f(1−t))`, `f(t) = e^{−1/t}` — exactly Mathlib's
`Real.smoothTransition` — and the length `ℓ = ε|u+v|/|m(φ)|`.  Here the whole rounded curve is built
at once from its tangent angle: `Θ` is the `C^∞` function on `ℝ` which is constant on the straight
parts and equals `θ_u + ϑ_j φ((t − a j)/(b j − a j))` on the junction `[a j, b j]`, with the
subdivision `a, b` given by cumulative arclength (so the speed is the constant `Λ` = total length);
`L_ε(t) = A₀(0) + Λ ∫₀^t (cos Θ, sin Θ)`.  Smoothness and regularity of `L_ε` are then automatic
(the primitive of a smooth unit field), the unit tangent is `(cos Θ, sin Θ)` and `Θ` is its global
tangent-angle lift; closedness is the vanishing of the total displacement, which is the telescoping
identity `Σ_j [ε(u_j + v_j) + (|δ_j| − 2ε) v_j] = Σ_j δ_j = 0`.  This is the printed construction,
determinate in `(L, ε)` — the "one curve and one diagram" that cf:thm-carrierfloor (A) reads
(`roundedLoop`, `PolygonDiagram` unchanged). -/

namespace CornerRounding

/-- the unit vector of angle `α` -/
def dirOf (α : ℝ) : Plane := (Real.cos α, Real.sin α)

/-- the tangent angle along a junction of turn `ϑ` from the direction of angle `θu`, in the profile
parameter `s ∈ [0,1]`: `θ_u + ϑ φ(s)` -/
def juncAngle (θu ϑ s : ℝ) : ℝ := θu + ϑ * Real.smoothTransition s

/-- the unit tangent along the junction -/
def juncDir (θu ϑ s : ℝ) : Plane := dirOf (juncAngle θu ϑ s)

/-- the positive scalar `M(ϑ) = ∫₀¹ cos(ϑ(φ(s) − ½)) ds` (the symmetric part of the printed `m(φ)`:
`m(φ) = M(ϑ) · (unit bisector)`, `|m(φ)| = M(ϑ)`) -/
def M (ϑ : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, Real.cos (ϑ * (Real.smoothTransition s - 1 / 2))

/-- the printed junction length `ℓ = ε|u+v|/|m(φ)|`, with `|u+v| = 2cos(ϑ/2)` and `|m(φ)| = M(ϑ)` -/
def juncLen (ε ϑ : ℝ) : ℝ := ε * (2 * Real.cos (ϑ / 2)) / M ϑ

/-- the printed junction arc `γ_ℓ`, in the profile parameter `s ∈ [0,1]` (arclength `σ = ℓ s`) -/
def juncArc (A0 : Plane) (ε θu ϑ s : ℝ) : Plane :=
  A0 + juncLen ε ϑ • ∫ r in (0 : ℝ)..s, juncDir θu ϑ r

variable (C : PolyComp)

/-- `u_j = δ_{j−1}/|δ_{j−1}|` -/
def uDir (j : ZMod C.k) : Plane := normalize (edge C.P (j - 1))
/-- `v_j = δ_j/|δ_j|` -/
def vDir (j : ZMod C.k) : Plane := normalize (edge C.P j)
/-- `ϑ_j`, the principal turn at corner `j` -/
def turn (j : ZMod C.k) : ℝ := principalTurn C.P j

/-- the accumulated tangent angle at the start of the junction at corner `j`: an argument of `u_0`,
then `θu (j+1) = θu j + ϑ_j` (so `dirOf (θu j) = u_j`, `dirOf (θu j + ϑ_j) = v_j`) -/
def θu : ℕ → ℝ
  | 0 => Complex.arg (planeComplex (uDir C 0))
  | j + 1 => θu j + turn C j

variable (ε : ℝ)

/-- the junction length at corner `j` -/
def ℓ (j : ℕ) : ℝ := juncLen ε (turn C j)
/-- the length of the straight part along edge `j`: `|δ_j| − 2ε` -/
def str (j : ℕ) : ℝ := euclideanLength (edge C.P j) - 2 * ε
/-- the total length `Λ` of the rounded curve (= its constant speed on `[0,1]`) -/
def Λ : ℝ := ∑ j ∈ Finset.range C.k, (ℓ C ε j + str C ε j)
/-- start of the junction at corner `j`, as a fraction of the total length -/
def a (j : ℕ) : ℝ := (∑ i ∈ Finset.range j, (ℓ C ε i + str C ε i)) / Λ C ε
/-- end of the junction at corner `j` -/
def b (j : ℕ) : ℝ := a C ε j + ℓ C ε j / Λ C ε

/-- the global tangent angle: constant on the straight parts, `θu j + ϑ_j φ((t − a j)/(b j − a j))`
on the junction at corner `j`, and `Θ (t+1) = Θ t + 2π rot(L)` -/
def Θ (t : ℝ) : ℝ :=
  θu C 0 + 2 * Real.pi * rotationNumber C.P * (⌊t⌋ : ℝ) +
    ∑ j ∈ Finset.range C.k,
      turn C j * Real.smoothTransition ((Int.fract t - a C ε j) * Λ C ε / ℓ C ε j)

/-- the unit tangent field `(cos Θ, sin Θ)` -/
def tangentField (t : ℝ) : Plane := dirOf (Θ C ε t)

/-- `A₀(j) = q_j − ε u_j` -/
def A0 (j : ℕ) : Plane := C.P j - ε • uDir C j
/-- `A₁(j) = q_j + ε v_j` -/
def A1 (j : ℕ) : Plane := C.P j + ε • vDir C j

/-- the rounded curve `L_ε(t) = A₀(0) + Λ ∫₀ᵗ (cos Θ, sin Θ)` -/
def curveMap (t : ℝ) : Plane := A0 C ε 0 + Λ C ε • ∫ s in (0 : ℝ)..t, tangentField C ε s

/-- the tangent-angle lift of the junction at corner `j`, as a `C^∞` function on `ℝ` constant
outside `[a j, b j]` -/
def liftAt (j : ℕ) (t : ℝ) : ℝ :=
  θu C j + turn C j * Real.smoothTransition ((t - a C ε j) * Λ C ε / ℓ C ε j)

/-- the parameter of the rounded curve at which the occurrence `v` (crossing `v.1`, strand `v.2`)
is traversed: on the straight part of its edge, at arclength `crossingParam·|δ| − ε` past `A₁` -/
def τ (D : PolygonDiagram C) (v : D.toDiagram.Γ.Visit) : ℝ :=
  b C ε (D.label v).val +
    (D.toDiagram.crossingParam v.1 v.2.2 * euclideanLength (edge C.P (D.label v)) - ε) / Λ C ε

/-! ### The clearance (printed: `ε₀(L) = ⅓ min{η_v, η_e, η_ℓ, η_X}`, sm-3:3822-3833) -/

/-- Euclidean distance from a point to a set (through `planeComplex`, so it is the Euclidean, not
the product, distance; `0` on the empty set) -/
def far (p : Plane) (S : Set Plane) : ℝ := Metric.infDist (planeComplex p) (planeComplex '' S)

/-- the other corners -/
def otherCorners (i : ZMod C.k) : Set Plane := {p | ∃ j, j ≠ i ∧ p = C.P j}
/-- the union of the closed edges not incident to `q_i` -/
def nonIncidentEdges (i : ZMod C.k) : Set Plane := ⋃ j ∈ {j | ¬ incident i j}, edgeSegment C.P j
/-- the double points of `L` (the crossings of the one-component shadow `single C`, which depend
on the polygon alone — the printed `ε₀(L)` is a function of `L`) -/
def crossingPts : Set Plane :=
  {p | ∃ x : (Shadow.single C).Crossing, p = (Shadow.single C).crossingPoint x}

/-- `η_v = min_i min_{k≠i} |q_k − q_i|` -/
def ηv : ℝ := Finset.univ.inf' Finset.univ_nonempty fun i => far (C.P i) (otherCorners C i)
/-- `η_e = min_i dist(q_i, 𝓔_i)` -/
def ηe : ℝ := Finset.univ.inf' Finset.univ_nonempty fun i => far (C.P i) (nonIncidentEdges C i)
/-- `η_ℓ = min_i |δ_i|` -/
def ηℓ : ℝ := Finset.univ.inf' Finset.univ_nonempty fun i => euclideanLength (edge C.P i)
/-- `η_X = min_{i, x} |x − q_i|`, read as `+∞` (here: `η_ℓ`) when there is no double point -/
def ηX : ℝ :=
  if Nonempty (Shadow.single C).Crossing then
    Finset.univ.inf' Finset.univ_nonempty fun i => far (C.P i) (crossingPts C)
  else ηℓ C

/-- the clearance `ε₀(L) = ⅓ min{η_v, η_e, η_ℓ, η_X}` -/
def clearance : ℝ := (1 / 3) * min (min (ηv C) (ηe C)) (min (ηℓ C) (ηX C))

end CornerRounding

/-! ## 8. The chain of lemmas (all proved by units P, G1, E, A, G2, G3, X; unit split in PLAN_FINAL.md §4)

Hypotheses are bundled in `Admissible C D ε`: the printed input conditions ("principal turns
nonzero"; the rest is `D.generic`) and `0 < ε < ε₀(L)`. -/

namespace CornerRounding

open Set

/-- the hypotheses of the row at an admissible `ε` -/
structure Admissible (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) : Prop where
  /-- "the principal turns of L all exist and are nonzero" (existence is `D.regular`) -/
  turn_ne : ∀ i, principalTurn C.P i ≠ 0
  /-- `ε ∈ (0, ε₀(L))` -/
  ε_pos : 0 < ε
  ε_lt : ε < clearance C

/-! ### Unit P — the transition profile `φ = Real.smoothTransition` (sm-3:3705-3735) -/

/-- `φ(1 − t) = 1 − φ(t)` -/
theorem smoothTransition_symm (t : ℝ) :
    Real.smoothTransition (1 - t) = 1 - Real.smoothTransition t := by
  unfold Real.smoothTransition
  have h1 := (Real.smoothTransition.pos_denom t).ne'
  rw [sub_sub_cancel, eq_sub_iff_add_eq, add_comm (expNegInvGlue (1 - t)) (expNegInvGlue t),
    ← add_div, add_comm (expNegInvGlue (1 - t)) (expNegInvGlue t), div_self h1]

/-- `φ` is strictly increasing on `[0,1]` -/
theorem smoothTransition_strictMonoOn : StrictMonoOn Real.smoothTransition (Icc 0 1) := by
  intro s hs t ht hst
  have hs0 : 0 ≤ s := hs.1
  have ht1 : t ≤ 1 := ht.2
  have hpos_t : 0 < expNegInvGlue t := expNegInvGlue.pos_of_pos (hs0.trans_lt hst)
  have hpos_1s : 0 < expNegInvGlue (1 - s) := expNegInvGlue.pos_of_pos (by linarith)
  -- the core inequality `f(s) f(1−t) < f(t) f(1−s)` (sm-3:3705-3735), no derivatives
  have key : expNegInvGlue s * expNegInvGlue (1 - t) <
      expNegInvGlue t * expNegInvGlue (1 - s) := by
    rcases hs0.eq_or_lt with rfl | hs0'
    · rw [expNegInvGlue.zero, zero_mul]; exact mul_pos hpos_t hpos_1s
    rcases ht1.eq_or_lt with rfl | ht1'
    · rw [sub_self, expNegInvGlue.zero, mul_zero]; exact mul_pos hpos_t hpos_1s
    -- `0 < s < t < 1`: compare the exponents `1/t + 1/(1−s) < 1/s + 1/(1−t)`
    have e1 : expNegInvGlue s = Real.exp (-s⁻¹) := by simp [expNegInvGlue, not_le.mpr hs0']
    have e2 : expNegInvGlue t = Real.exp (-t⁻¹) := by
      simp [expNegInvGlue, not_le.mpr (hs0'.trans hst)]
    have e3 : expNegInvGlue (1 - s) = Real.exp (-(1 - s)⁻¹) := by
      simp [expNegInvGlue, not_le.mpr (sub_pos.mpr (hst.trans ht1'))]
    have e4 : expNegInvGlue (1 - t) = Real.exp (-(1 - t)⁻¹) := by
      simp [expNegInvGlue, not_le.mpr (sub_pos.mpr ht1')]
    rw [e1, e2, e3, e4, ← Real.exp_add, ← Real.exp_add, Real.exp_lt_exp]
    have i1 : t⁻¹ < s⁻¹ := inv_strictAnti₀ hs0' hst
    have i2 : (1 - s)⁻¹ < (1 - t)⁻¹ := inv_strictAnti₀ (sub_pos.mpr ht1') (by linarith)
    linarith
  unfold Real.smoothTransition
  rw [div_lt_div_iff₀ (Real.smoothTransition.pos_denom s) (Real.smoothTransition.pos_denom t)]
  linear_combination key

/-- `f' x = x⁻² f x` for `f = expNegInvGlue` (the case `p = 1` of Mathlib's
`expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul`) -/
private theorem P_hasDerivAt_expNegInvGlue (x : ℝ) :
    HasDerivAt expNegInvGlue (x⁻¹ ^ 2 * expNegInvGlue x) x := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 x
  simpa using h

/-- `φ' > 0` on `(0,1)` -/
theorem deriv_smoothTransition_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    0 < deriv Real.smoothTransition t := by
  have ha : 0 < expNegInvGlue t := expNegInvGlue.pos_of_pos h0
  have hb : 0 < expNegInvGlue (1 - t) := expNegInvGlue.pos_of_pos (sub_pos.mpr h1)
  have hf : HasDerivAt expNegInvGlue (t⁻¹ ^ 2 * expNegInvGlue t) t :=
    P_hasDerivAt_expNegInvGlue t
  have hg : HasDerivAt (fun x => expNegInvGlue (1 - x))
      (-((1 - t)⁻¹ ^ 2 * expNegInvGlue (1 - t))) t := by
    have := (P_hasDerivAt_expNegInvGlue (1 - t)).comp t ((hasDerivAt_id' t).const_sub 1)
    exact this.congr_deriv (by ring)
  -- quotient rule: `φ' = (f' g − f g') / (f + g)²` with `g x = f (1 − x)`
  have hd : HasDerivAt Real.smoothTransition _ t :=
    hf.fun_div (hf.add hg) (Real.smoothTransition.pos_denom t).ne'
  rw [hd.deriv]
  apply div_pos
  · -- numerator `= f(t) f(1−t) (t⁻² + (1−t)⁻²) > 0`
    have key : 0 < expNegInvGlue t * expNegInvGlue (1 - t) * (t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2) :=
      mul_pos (mul_pos ha hb)
        (add_pos (pow_pos (inv_pos.mpr h0) 2) (pow_pos (inv_pos.mpr (sub_pos.mpr h1)) 2))
    exact key.trans_eq (by ring)
  · exact pow_pos (Real.smoothTransition.pos_denom t) 2

/-- a `C^∞` function constant on an open set has all derivatives of order `≥ 1` vanishing on the
closure of that set (`iteratedDeriv m f` is continuous and `0` on the open set) -/
private theorem P_iteratedDeriv_eq_zero_of_eqOn_open {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {s : Set ℝ} (hs : IsOpen s) {c : ℝ} (h : ∀ t ∈ s, f t = c) {m : ℕ} (hm : 1 ≤ m) {x : ℝ}
    (hx : x ∈ closure s) : iteratedDeriv m f x = 0 := by
  have h1 : EqOn (iteratedDeriv m f) (iteratedDeriv m (fun _ => c)) s :=
    Set.EqOn.iteratedDeriv_of_isOpen (fun t ht => h t ht) hs m
  have hc1 : Continuous (iteratedDeriv m f) :=
    hf.continuous_iteratedDeriv m (by exact_mod_cast le_top)
  have hc2 : Continuous (iteratedDeriv m (fun _ : ℝ => c)) :=
    ContDiff.continuous_iteratedDeriv' m contDiff_const
  rw [h1.closure hc1 hc2 hx, iteratedDeriv_const]
  simp [Nat.one_le_iff_ne_zero.mp hm]

/-- A `C^∞` function constant on `(−∞, x]` has all derivatives of order `≥ 1` vanishing at `x`
(the value at `x` is the limit from the left of the continuous `m`-th derivative, which is `0`
on the open half-line). -/
theorem iteratedDeriv_eq_zero_of_const_left {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {x c : ℝ}
    (h : ∀ t ≤ x, f t = c) {m : ℕ} (hm : 1 ≤ m) : iteratedDeriv m f x = 0 := by
  refine P_iteratedDeriv_eq_zero_of_eqOn_open hf isOpen_Iio (fun t ht => h t (le_of_lt ht)) hm ?_
  rw [closure_Iio]
  exact Set.mem_Iic.mpr le_rfl

/-- the mirror statement on `[x, ∞)` -/
theorem iteratedDeriv_eq_zero_of_const_right {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {x c : ℝ}
    (h : ∀ t, x ≤ t → f t = c) {m : ℕ} (hm : 1 ≤ m) : iteratedDeriv m f x = 0 := by
  refine P_iteratedDeriv_eq_zero_of_eqOn_open hf isOpen_Ioi (fun t ht => h t (le_of_lt ht)) hm ?_
  rw [closure_Ioi]
  exact Set.mem_Ici.mpr le_rfl

/-! ### Unit A — one junction arc, abstractly (sm-3:3736-3820): `A₀ = q − εu`, `u = dirOf θu`,
`v = dirOf (θu + ϑ)`, `0 < |ϑ| < π` -/

theorem dirOf_unit (α : ℝ) : euclideanLength (dirOf α) = 1 := by
  rw [euclideanLength_formula]
  show Real.sqrt (Real.cos α * Real.cos α + Real.sin α * Real.sin α) = 1
  rw [← sq, ← sq, Real.cos_sq_add_sin_sq, Real.sqrt_one]

theorem normalize_smul_dirOf {r : ℝ} (hr : 0 < r) (α : ℝ) : normalize (r • dirOf α) = dirOf α := by
  rw [normalize_smul_of_pos hr, normalize, dirOf_unit, inv_one, one_smul]

/-- two directions of angles differing by less than `π` are equal only if the angles are -/
theorem dirOf_injOn_of_lt_pi {α β : ℝ} (h : |α - β| < Real.pi) (he : dirOf α = dirOf β) : α = β := by
  have hc : Real.cos α = Real.cos β := congrArg Prod.fst he
  have hs : Real.sin α = Real.sin β := congrArg Prod.snd he
  have h1 : Real.cos (α - β) = 1 := by
    rw [Real.cos_sub, hc, hs, ← sq, ← sq, Real.cos_sq_add_sin_sq]
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 h1
  have hpi := Real.pi_pos
  rw [← hn, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h
  have hn1 : |(n : ℝ)| < 1 := by nlinarith [abs_nonneg (n : ℝ)]
  rw [← Int.cast_abs] at hn1
  have hn2 : |n| < 1 := by exact_mod_cast hn1
  have hn0 : n = 0 := by
    obtain ⟨h3, h4⟩ := abs_lt.mp hn2
    omega
  rw [hn0] at hn
  simp at hn
  linarith

theorem contDiff_juncAngle (θu ϑ : ℝ) : ContDiff ℝ ∞ (juncAngle θu ϑ) := by
  unfold juncAngle
  exact contDiff_const.add (contDiff_const.mul Real.smoothTransition.contDiff)

theorem contDiff_juncDir (θu ϑ : ℝ) : ContDiff ℝ ∞ (juncDir θu ϑ) := by
  unfold juncDir dirOf
  exact (Real.contDiff_cos.comp (contDiff_juncAngle θu ϑ)).prodMk
    (Real.contDiff_sin.comp (contDiff_juncAngle θu ϑ))

/-- (Unit A helper) `|ϑ(φ(r) − ½)| ≤ |ϑ|/2`, since `φ ∈ [0,1]` -/
theorem A_abs_arg_le (ϑ r : ℝ) : |ϑ * (Real.smoothTransition r - 1 / 2)| ≤ |ϑ| / 2 := by
  rw [abs_mul]
  have h1 : |Real.smoothTransition r - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [Real.smoothTransition.nonneg r, Real.smoothTransition.le_one r]
  calc |ϑ| * |Real.smoothTransition r - 1 / 2| ≤ |ϑ| * (1 / 2) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg ϑ)
    _ = |ϑ| / 2 := by ring

/-- (Unit A helper) `cos(ϑ/2) > 0` for `|ϑ| < π` -/
theorem A_cos_half_pos {ϑ : ℝ} (h : |ϑ| < Real.pi) : 0 < Real.cos (ϑ / 2) := by
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

/-- (Unit A helper) the integrand of `M` is `≥ cos(ϑ/2)` -/
theorem A_cos_half_le {ϑ : ℝ} (h : |ϑ| < Real.pi) (r : ℝ) :
    Real.cos (ϑ / 2) ≤ Real.cos (ϑ * (Real.smoothTransition r - 1 / 2)) := by
  have e1 : Real.cos (ϑ / 2) = Real.cos |ϑ / 2| := (Real.cos_abs _).symm
  have e2 : Real.cos (ϑ * (Real.smoothTransition r - 1 / 2)) =
      Real.cos |ϑ * (Real.smoothTransition r - 1 / 2)| := (Real.cos_abs _).symm
  rw [e1, e2]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
  · rw [abs_div, abs_two]; linarith [abs_nonneg ϑ]
  · rw [abs_div, abs_two]; exact A_abs_arg_le ϑ r

/-- (Unit A helper) the integrand of `M` is positive -/
theorem A_cos_arg_pos {ϑ : ℝ} (h : |ϑ| < Real.pi) (r : ℝ) :
    0 < Real.cos (ϑ * (Real.smoothTransition r - 1 / 2)) :=
  (A_cos_half_pos h).trans_le (A_cos_half_le h r)

theorem A_continuous_cos (ϑ : ℝ) :
    Continuous fun r => Real.cos (ϑ * (Real.smoothTransition r - 1 / 2)) :=
  Real.continuous_cos.comp
    (continuous_const.mul (Real.smoothTransition.continuous.sub continuous_const))

theorem A_continuous_sin (ϑ : ℝ) :
    Continuous fun r => Real.sin (ϑ * (Real.smoothTransition r - 1 / 2)) :=
  Real.continuous_sin.comp
    (continuous_const.mul (Real.smoothTransition.continuous.sub continuous_const))

/-- `M(ϑ) > 0` for `|ϑ| < π`: the integrand is `≥ cos(ϑ/2) > 0` -/
theorem M_pos {ϑ : ℝ} (h : |ϑ| < Real.pi) : 0 < M ϑ := by
  unfold M
  exact intervalIntegral.intervalIntegral_pos_of_pos
    ((A_continuous_cos ϑ).intervalIntegrable _ _) (A_cos_arg_pos h) zero_lt_one

theorem juncLen_pos {ε ϑ : ℝ} (hε : 0 < ε) (h : |ϑ| < Real.pi) : 0 < juncLen ε ϑ := by
  unfold juncLen
  exact div_pos (mul_pos hε (mul_pos two_pos (A_cos_half_pos h))) (M_pos h)

/-- (Unit A helper) the junction tangent in the bisector frame `(dirOf c, dirOf (c + π/2))`,
`c = θu + ϑ/2`: `juncDir = cos w • e_w + sin w • e_z`, `w = ϑ(φ − ½)` -/
theorem A_juncDir_eq (θu ϑ r : ℝ) : juncDir θu ϑ r =
    Real.cos (ϑ * (Real.smoothTransition r - 1 / 2)) • dirOf (θu + ϑ / 2) +
      Real.sin (ϑ * (Real.smoothTransition r - 1 / 2)) •
        ((-Real.sin (θu + ϑ / 2), Real.cos (θu + ϑ / 2)) : Plane) := by
  have e : juncAngle θu ϑ r = (θu + ϑ / 2) + ϑ * (Real.smoothTransition r - 1 / 2) := by
    unfold juncAngle; ring
  unfold juncDir dirOf
  rw [e, Real.cos_add (θu + ϑ / 2), Real.sin_add (θu + ϑ / 2)]
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
  constructor <;> ring

/-- (Unit A helper) the integral of the junction tangent in the bisector frame -/
theorem A_integral_juncDir (θu ϑ s : ℝ) :
    (∫ r in (0 : ℝ)..s, juncDir θu ϑ r) =
      (∫ r in (0 : ℝ)..s, Real.cos (ϑ * (Real.smoothTransition r - 1 / 2))) • dirOf (θu + ϑ / 2) +
        (∫ r in (0 : ℝ)..s, Real.sin (ϑ * (Real.smoothTransition r - 1 / 2))) •
          ((-Real.sin (θu + ϑ / 2), Real.cos (θu + ϑ / 2)) : Plane) := by
  simp only [A_juncDir_eq]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const]
  · exact ((A_continuous_cos ϑ).smul continuous_const).intervalIntegrable _ _
  · exact ((A_continuous_sin ϑ).smul continuous_const).intervalIntegrable _ _

/-- (Unit A helper) `u + v = 2cos(ϑ/2) · (unit bisector)` -/
theorem A_dirOf_add_dirOf (θu ϑ : ℝ) :
    dirOf θu + dirOf (θu + ϑ) = (2 * Real.cos (ϑ / 2)) • dirOf (θu + ϑ / 2) := by
  have key : ∀ c d : ℝ, dirOf (c - d) + dirOf (c + d) = (2 * Real.cos d) • dirOf c := by
    intro c d
    unfold dirOf
    ext <;> simp [Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub] <;> ring
  have := key (θu + ϑ / 2) (ϑ / 2)
  rwa [show θu + ϑ / 2 - ϑ / 2 = θu by ring, show θu + ϑ / 2 + ϑ / 2 = θu + ϑ by ring] at this

/-- (Unit A helper) `u` in the bisector frame: `u = cos(ϑ/2) e_w − sin(ϑ/2) e_z` -/
theorem A_dirOf_frame (θu ϑ : ℝ) :
    dirOf θu = Real.cos (ϑ / 2) • dirOf (θu + ϑ / 2) -
      Real.sin (ϑ / 2) • ((-Real.sin (θu + ϑ / 2), Real.cos (θu + ϑ / 2)) : Plane) := by
  have key : ∀ c d : ℝ, dirOf (c - d) =
      Real.cos d • dirOf c - Real.sin d • ((-Real.sin c, Real.cos c) : Plane) := by
    intro c d
    unfold dirOf
    ext <;> simp [Real.cos_sub, Real.sin_sub] <;> ring
  have := key (θu + ϑ / 2) (ϑ / 2)
  rwa [show θu + ϑ / 2 - ϑ / 2 = θu by ring] at this

/-- (Unit A helper) the transverse component integrates to `0` over `[0,1]` by the symmetry
`φ(1 − s) = 1 − φ(s)` -/
theorem A_integral_sin_symm (ϑ : ℝ) :
    (∫ r in (0 : ℝ)..1, Real.sin (ϑ * (Real.smoothTransition r - 1 / 2))) = 0 := by
  have h1 : (∫ x in (0 : ℝ)..1, Real.sin (ϑ * (Real.smoothTransition (1 - x) - 1 / 2))) =
      ∫ x in (0 : ℝ)..1, Real.sin (ϑ * (Real.smoothTransition x - 1 / 2)) := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
      (fun x => Real.sin (ϑ * (Real.smoothTransition x - 1 / 2))) 1
    simp only [sub_self, sub_zero] at this
    exact this
  have h2 : (∫ x in (0 : ℝ)..1, Real.sin (ϑ * (Real.smoothTransition (1 - x) - 1 / 2))) =
      -∫ x in (0 : ℝ)..1, Real.sin (ϑ * (Real.smoothTransition x - 1 / 2)) := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext x
    rw [smoothTransition_symm, ← Real.sin_neg]
    congr 1
    ring
  linarith

/-- the printed `m(φ)` points along the bisector: `∫₀¹ juncDir = (M(ϑ)/(2cos(ϑ/2))) • (u + v)`
(symmetry `φ(1−s) = 1 − φ(s)` kills the transverse component) -/
theorem integral_juncDir {θu ϑ : ℝ} (h : |ϑ| < Real.pi) :
    (∫ s in (0 : ℝ)..1, juncDir θu ϑ s) =
      (M ϑ / (2 * Real.cos (ϑ / 2))) • (dirOf θu + dirOf (θu + ϑ)) := by
  rw [A_integral_juncDir, A_integral_sin_symm, zero_smul, add_zero, A_dirOf_add_dirOf, smul_smul]
  have hc : (2 * Real.cos (ϑ / 2)) ≠ 0 := (mul_pos two_pos (A_cos_half_pos h)).ne'
  rw [div_mul_cancel₀ _ hc]
  rfl

/-- the displacement realised by the junction: `A₁ − A₀ = ε(u + v)` -/
theorem juncArc_one {A0 : Plane} {ε θu ϑ : ℝ} (h : |ϑ| < Real.pi) :
    juncArc A0 ε θu ϑ 1 = A0 + ε • (dirOf θu + dirOf (θu + ϑ)) := by
  unfold juncArc
  rw [integral_juncDir h, smul_smul]
  congr 2
  unfold juncLen
  have hM := (M_pos h).ne'
  have hc : Real.cos (ϑ / 2) ≠ 0 := by
    obtain ⟨h1, h2⟩ := abs_lt.mp h
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).ne'
  field_simp

theorem juncArc_zero (A0 : Plane) (ε θu ϑ : ℝ) : juncArc A0 ε θu ϑ 0 = A0 := by
  simp [juncArc]

theorem hasDerivAt_juncArc (A0 : Plane) (ε θu ϑ s : ℝ) :
    HasDerivAt (juncArc A0 ε θu ϑ) (juncLen ε ϑ • juncDir θu ϑ s) s := by
  have hc : Continuous (juncDir θu ϑ) := (contDiff_juncDir θu ϑ).continuous
  have h1 : HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, juncDir θu ϑ r) (juncDir θu ϑ s) s :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  exact (h1.const_smul (juncLen ε ϑ)).const_add A0

/-- (Unit A helper) the bisector coordinate `F(s) = ∫₀ˢ cos w` is strictly increasing
(`F(s₂) − F(s₁) = ∫_{s₁}^{s₂} cos w > 0`, the integrand being `≥ cos(ϑ/2) > 0`) -/
theorem A_F_strictMono {ϑ : ℝ} (h : |ϑ| < Real.pi) :
    StrictMono (fun u => ∫ r in (0 : ℝ)..u, Real.cos (ϑ * (Real.smoothTransition r - 1 / 2))) := by
  intro s₁ s₂ hlt
  have hi := (A_continuous_cos ϑ).intervalIntegrable (μ := MeasureTheory.volume)
  have e := intervalIntegral.integral_interval_sub_left (hi 0 s₂) (hi 0 s₁)
  have hp := intervalIntegral.intervalIntegral_pos_of_pos (hi s₁ s₂) (A_cos_arg_pos h) hlt
  simp only
  linarith

/-- (Unit A helper) `cos(ϑ/2) ≤ M(ϑ)` -/
theorem A_cos_half_le_M {ϑ : ℝ} (h : |ϑ| < Real.pi) : Real.cos (ϑ / 2) ≤ M ϑ := by
  unfold M
  have := intervalIntegral.integral_mono_on (a := 0) (b := 1) (μ := MeasureTheory.volume)
    zero_le_one (intervalIntegrable_const (c := Real.cos (ϑ / 2)))
    ((A_continuous_cos ϑ).intervalIntegrable _ _) (fun r _ => A_cos_half_le h r)
  have e : (∫ _ in (0 : ℝ)..1, Real.cos (ϑ / 2)) = Real.cos (ϑ / 2) := by
    rw [intervalIntegral.integral_const]; simp
  rw [e] at this
  exact this

/-- (Unit A helper) `ℓ · M = 2ε cos(ϑ/2)` -/
theorem A_juncLen_mul_M {ε ϑ : ℝ} (h : |ϑ| < Real.pi) :
    juncLen ε ϑ * M ϑ = ε * (2 * Real.cos (ϑ / 2)) := by
  unfold juncLen
  exact div_mul_cancel₀ _ (M_pos h).ne'

/-- (Unit A helper) `ℓ ≤ 2ε` -/
theorem A_juncLen_le {ε ϑ : ℝ} (hε : 0 < ε) (h : |ϑ| < Real.pi) : juncLen ε ϑ ≤ 2 * ε := by
  unfold juncLen
  rw [div_le_iff₀ (M_pos h)]
  have := A_cos_half_le_M h
  nlinarith [mul_le_mul_of_nonneg_left this hε.le]

/-- (Unit A helper) `φ(½) = ½` -/
theorem A_smoothTransition_half : Real.smoothTransition (1 / 2) = 1 / 2 := by
  have := smoothTransition_symm (1 / 2)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at this
  linarith

theorem A_smoothTransition_le_half {r : ℝ} (hr : r ≤ 1 / 2) :
    Real.smoothTransition r ≤ 1 / 2 := by
  have := Real.smoothTransition.monotone hr
  rwa [A_smoothTransition_half] at this

theorem A_half_le_smoothTransition {r : ℝ} (hr : 1 / 2 ≤ r) :
    1 / 2 ≤ Real.smoothTransition r := by
  have := Real.smoothTransition.monotone hr
  rwa [A_smoothTransition_half] at this

/-- (Unit A helper) `ϑ sin(ϑt) ≥ 0` for `0 ≤ t ≤ ½`, `|ϑ| < π` -/
theorem A_mul_sin_nonneg {ϑ t : ℝ} (h : |ϑ| < Real.pi) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    0 ≤ ϑ * Real.sin (ϑ * t) := by
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  rcases le_or_gt 0 ϑ with hp | hn
  · apply mul_nonneg hp
    apply Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hp ht0)
    nlinarith
  · have hs : Real.sin (ϑ * t) ≤ 0 := by
      apply Real.sin_nonpos_of_nonpos_of_neg_pi_le
      · nlinarith
      · nlinarith
    nlinarith

/-- (Unit A helper) `ϑ sin(ϑt) ≤ 0` for `−½ ≤ t ≤ 0`, `|ϑ| < π` -/
theorem A_mul_sin_nonpos {ϑ t : ℝ} (h : |ϑ| < Real.pi) (ht0 : t ≤ 0) (ht : -(1 / 2) ≤ t) :
    ϑ * Real.sin (ϑ * t) ≤ 0 := by
  have := A_mul_sin_nonneg h (t := -t) (by linarith) (by linarith)
  rw [mul_neg, Real.sin_neg, mul_neg] at this
  linarith

/-- (Unit A helper) the sign of the transverse coordinate: `sgn ϑ · ∫₀ˢ sin w ≤ 0` on `[0,1]`
(`w ≤ 0` before `s = ½`, `≥ 0` after, and the total is `0`) -/
theorem A_integral_sin_sign {ϑ : ℝ} (h : |ϑ| < Real.pi) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ϑ * (∫ r in (0 : ℝ)..s, Real.sin (ϑ * (Real.smoothTransition r - 1 / 2))) ≤ 0 := by
  obtain ⟨hs0, hs1⟩ := hs
  have hi := (A_continuous_sin ϑ).intervalIntegrable (μ := MeasureTheory.volume)
  have hc' : Continuous fun r => ϑ * Real.sin (ϑ * (Real.smoothTransition r - 1 / 2)) :=
    continuous_const.mul (A_continuous_sin ϑ)
  have hi' := hc'.intervalIntegrable (μ := MeasureTheory.volume)
  rcases le_or_gt s (1 / 2) with hs2 | hs2
  · have := intervalIntegral.integral_mono_on hs0 (hi' 0 s) (intervalIntegrable_const (c := (0 : ℝ)))
      (fun r hr => A_mul_sin_nonpos h (t := Real.smoothTransition r - 1 / 2)
        (by linarith [A_smoothTransition_le_half (hr.2.trans hs2)])
        (by linarith [Real.smoothTransition.nonneg r]))
    rw [intervalIntegral.integral_zero, intervalIntegral.integral_const_mul] at this
    exact this
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals (hi 0 s) (hi s 1)
    rw [A_integral_sin_symm] at hsplit
    have := intervalIntegral.integral_mono_on hs1 (intervalIntegrable_const (c := (0 : ℝ))) (hi' s 1)
      (fun r hr => A_mul_sin_nonneg h (t := Real.smoothTransition r - 1 / 2)
        (by linarith [A_half_le_smoothTransition (hs2.le.trans hr.1)])
        (by linarith [Real.smoothTransition.le_one r]))
    rw [intervalIntegral.integral_zero, intervalIntegral.integral_const_mul] at this
    have e : (∫ r in (0 : ℝ)..s, Real.sin (ϑ * (Real.smoothTransition r - 1 / 2))) =
        -∫ r in s..1, Real.sin (ϑ * (Real.smoothTransition r - 1 / 2)) := by linarith
    rw [e, mul_neg]
    linarith

/-- (Unit A helper) `|sin w| ≤ |sin(ϑ/2)|` since `|w| ≤ |ϑ|/2 < π/2` -/
theorem A_abs_sin_arg_le {ϑ : ℝ} (h : |ϑ| < Real.pi) (r : ℝ) :
    |Real.sin (ϑ * (Real.smoothTransition r - 1 / 2))| ≤ |Real.sin (ϑ / 2)| := by
  have hb := A_abs_arg_le ϑ r
  have hpi : |ϑ| / 2 ≤ Real.pi / 2 := by linarith
  have e1 : |Real.sin (ϑ * (Real.smoothTransition r - 1 / 2))| =
      Real.sin |ϑ * (Real.smoothTransition r - 1 / 2)| :=
    Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [abs_nonneg ϑ])
  have e2 : |Real.sin (ϑ / 2)| = Real.sin |ϑ / 2| :=
    Real.abs_sin_eq_sin_abs_of_abs_le_pi (by rw [abs_div, abs_two]; linarith [abs_nonneg ϑ])
  rw [e1, e2, abs_div, abs_two]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [abs_nonneg (ϑ * (Real.smoothTransition r - 1 / 2))]) hpi hb

/-- (Unit A helper) `|∫₀ˢ sin w| ≤ |sin(ϑ/2)|/2` on `[0,1]` -/
theorem A_integral_sin_bound {ϑ : ℝ} (h : |ϑ| < Real.pi) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    |∫ r in (0 : ℝ)..s, Real.sin (ϑ * (Real.smoothTransition r - 1 / 2))| ≤
      |Real.sin (ϑ / 2)| / 2 := by
  obtain ⟨hs0, hs1⟩ := hs
  have hi := (A_continuous_sin ϑ).intervalIntegrable (μ := MeasureTheory.volume)
  have hb : ∀ a b : ℝ, |∫ r in a..b, Real.sin (ϑ * (Real.smoothTransition r - 1 / 2))| ≤
      |Real.sin (ϑ / 2)| * |b - a| := by
    intro a b
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (C := |Real.sin (ϑ / 2)|)
      (f := fun r => Real.sin (ϑ * (Real.smoothTransition r - 1 / 2)))
      (fun x _ => by rw [Real.norm_eq_abs]; exact A_abs_sin_arg_le h x)
    rwa [Real.norm_eq_abs] at this
  rcases le_or_gt s (1 / 2) with hs2 | hs2
  · calc _ ≤ |Real.sin (ϑ / 2)| * |s - 0| := hb 0 s
      _ ≤ |Real.sin (ϑ / 2)| / 2 := by
        rw [sub_zero, abs_of_nonneg hs0]
        nlinarith [abs_nonneg (Real.sin (ϑ / 2))]
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals (hi 0 s) (hi s 1)
    rw [A_integral_sin_symm] at hsplit
    have e : (∫ r in (0 : ℝ)..s, Real.sin (ϑ * (Real.smoothTransition r - 1 / 2))) =
        -∫ r in s..1, Real.sin (ϑ * (Real.smoothTransition r - 1 / 2)) := by linarith
    rw [e, abs_neg]
    calc _ ≤ |Real.sin (ϑ / 2)| * |1 - s| := hb s 1
      _ ≤ |Real.sin (ϑ / 2)| / 2 := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s)]
        nlinarith [abs_nonneg (Real.sin (ϑ / 2))]

/-- (Unit A helper) the Euclidean length in the orthonormal frame `(dirOf c, (−sin c, cos c))` -/
theorem A_euclideanLength_frame (c X Z : ℝ) :
    euclideanLength (X • dirOf c + Z • ((-Real.sin c, Real.cos c) : Plane)) =
      Real.sqrt (X ^ 2 + Z ^ 2) := by
  rw [euclideanLength_formula]
  congr 1
  simp only [dirOf, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  linear_combination (X ^ 2 + Z ^ 2) * Real.sin_sq_add_cos_sq c

/-- (Unit A helper) the bisector coordinate is read off by `planeDot · (dirOf c)` -/
theorem A_planeDot_frame (c X Z : ℝ) :
    planeDot (X • dirOf c + Z • ((-Real.sin c, Real.cos c) : Plane)) (dirOf c) = X := by
  simp only [planeDot, dirOf, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  linear_combination X * Real.sin_sq_add_cos_sq c

/-- (Unit A helper) the junction arc relative to the corner `q = A₀ + εu`, in the bisector frame:
`x_w = ℓ ∫₀ˢ cos w − ε cos(ϑ/2)`, `x_z = ℓ ∫₀ˢ sin w + ε sin(ϑ/2)` -/
theorem A_juncArc_sub (A0 : Plane) (ε θu ϑ s : ℝ) :
    juncArc A0 ε θu ϑ s - (A0 + ε • dirOf θu) =
      (juncLen ε ϑ * (∫ r in (0 : ℝ)..s, Real.cos (ϑ * (Real.smoothTransition r - 1 / 2))) -
          ε * Real.cos (ϑ / 2)) • dirOf (θu + ϑ / 2) +
        (juncLen ε ϑ * (∫ r in (0 : ℝ)..s, Real.sin (ϑ * (Real.smoothTransition r - 1 / 2))) +
          ε * Real.sin (ϑ / 2)) • ((-Real.sin (θu + ϑ / 2), Real.cos (θu + ϑ / 2)) : Plane) := by
  unfold juncArc
  rw [A_integral_juncDir θu ϑ s, A_dirOf_frame θu ϑ]
  module

/-- (Unit A helper) the transverse coordinate is bounded by `ε|sin(ϑ/2)|` -/
theorem A_Z_sq_le {ε ϑ ℓ G : ℝ} (hε : 0 < ε) (h0 : ϑ ≠ 0) (h : |ϑ| < Real.pi) (hℓ : 0 < ℓ)
    (hℓ2 : ℓ ≤ 2 * ε) (hG1 : ϑ * G ≤ 0) (hG2 : |G| ≤ |Real.sin (ϑ / 2)| / 2) :
    (ℓ * G + ε * Real.sin (ϑ / 2)) ^ 2 ≤ (ε * Real.sin (ϑ / 2)) ^ 2 := by
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  rcases lt_or_gt_of_ne h0 with hn | hp
  · have hsin : Real.sin (ϑ / 2) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
    rw [abs_of_neg hsin] at hG2
    have hG0 : 0 ≤ G := by nlinarith
    have hGu : G ≤ -Real.sin (ϑ / 2) / 2 := (le_abs_self G).trans hG2
    rw [← neg_sq (ε * Real.sin (ϑ / 2))]
    apply sq_le_sq'
    · nlinarith [mul_nonneg hℓ.le hG0]
    · nlinarith [mul_le_mul_of_nonneg_left hGu hℓ.le,
        mul_le_mul_of_nonneg_right hℓ2 (neg_nonneg.mpr hsin.le)]
  · have hsin : 0 < Real.sin (ϑ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [abs_of_pos hsin] at hG2
    have hG0 : G ≤ 0 := by nlinarith
    have hGl : -(Real.sin (ϑ / 2) / 2) ≤ G := (abs_le.mp hG2).1
    apply sq_le_sq'
    · nlinarith [mul_le_mul_of_nonneg_left hGl hℓ.le, mul_le_mul_of_nonneg_right hℓ2 hsin.le]
    · nlinarith [mul_nonneg hℓ.le (neg_nonneg.mpr hG0)]

/-- the arc lies in the closed triangle `A₀ q A₁`, hence in the closed `ε`-disc about `q = A₀ + εu`
(the two cone inequalities and the chord inequality, sm-3:3762-3806) -/
theorem juncArc_mem_disc {A0 : Plane} {ε θu ϑ : ℝ} (hε : 0 < ε) (h0 : ϑ ≠ 0) (h : |ϑ| < Real.pi)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    eucDist (juncArc A0 ε θu ϑ s) (A0 + ε • dirOf θu) ≤ ε := by
  have hℓ := juncLen_pos hε h
  have hℓM := A_juncLen_mul_M (ε := ε) h
  have hℓ2 := A_juncLen_le hε h
  have hF := A_F_strictMono h
  have hF0 : 0 ≤ ∫ r in (0 : ℝ)..s, Real.cos (ϑ * (Real.smoothTransition r - 1 / 2)) := by
    have := hF.monotone hs.1
    simp only [intervalIntegral.integral_same] at this
    exact this
  have hF1 : (∫ r in (0 : ℝ)..s, Real.cos (ϑ * (Real.smoothTransition r - 1 / 2))) ≤ M ϑ :=
    hF.monotone hs.2
  have hG1 := A_integral_sin_sign h hs
  have hG2 := A_integral_sin_bound h hs
  rw [eucDist, A_juncArc_sub, A_euclideanLength_frame, Real.sqrt_le_left hε.le]
  have hX : (juncLen ε ϑ * (∫ r in (0 : ℝ)..s, Real.cos (ϑ * (Real.smoothTransition r - 1 / 2))) -
      ε * Real.cos (ϑ / 2)) ^ 2 ≤ (ε * Real.cos (ϑ / 2)) ^ 2 := by
    apply sq_le_sq'
    · nlinarith [mul_nonneg hℓ.le hF0]
    · nlinarith [mul_le_mul_of_nonneg_left hF1 hℓ.le]
  have hZ := A_Z_sq_le hε h0 h hℓ hℓ2 hG1 hG2
  calc _ ≤ (ε * Real.cos (ϑ / 2)) ^ 2 + (ε * Real.sin (ϑ / 2)) ^ 2 := add_le_add hX hZ
    _ = ε ^ 2 := by rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]

/-- interior points of the arc are strictly inside the disc -/
theorem juncArc_mem_open_disc {A0 : Plane} {ε θu ϑ : ℝ} (hε : 0 < ε) (h0 : ϑ ≠ 0)
    (h : |ϑ| < Real.pi) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    eucDist (juncArc A0 ε θu ϑ s) (A0 + ε • dirOf θu) < ε := by
  have hℓ := juncLen_pos hε h
  have hℓM := A_juncLen_mul_M (ε := ε) h
  have hℓ2 := A_juncLen_le hε h
  have hF := A_F_strictMono h
  have hF0 : 0 < ∫ r in (0 : ℝ)..s, Real.cos (ϑ * (Real.smoothTransition r - 1 / 2)) := by
    have := hF hs.1
    simp only [intervalIntegral.integral_same] at this
    exact this
  have hF1 : (∫ r in (0 : ℝ)..s, Real.cos (ϑ * (Real.smoothTransition r - 1 / 2))) < M ϑ :=
    hF hs.2
  have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have hG1 := A_integral_sin_sign h hs'
  have hG2 := A_integral_sin_bound h hs'
  rw [eucDist, A_juncArc_sub, A_euclideanLength_frame, Real.sqrt_lt' hε]
  have hX : (juncLen ε ϑ * (∫ r in (0 : ℝ)..s, Real.cos (ϑ * (Real.smoothTransition r - 1 / 2))) -
      ε * Real.cos (ϑ / 2)) ^ 2 < (ε * Real.cos (ϑ / 2)) ^ 2 := by
    apply sq_lt_sq'
    · nlinarith [mul_pos hℓ hF0]
    · nlinarith [mul_lt_mul_of_pos_left hF1 hℓ]
  have hZ := A_Z_sq_le hε h0 h hℓ hℓ2 hG1 hG2
  calc _ < (ε * Real.cos (ϑ / 2)) ^ 2 + (ε * Real.sin (ϑ / 2)) ^ 2 := add_lt_add_of_lt_of_le hX hZ
    _ = ε ^ 2 := by rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]

/-- the arc is simple: its bisector coordinate is strictly increasing (sm-3:3807-3811) -/
theorem juncArc_injOn {A0 : Plane} {ε θu ϑ : ℝ} (hε : 0 < ε) (h0 : ϑ ≠ 0) (h : |ϑ| < Real.pi) :
    InjOn (juncArc A0 ε θu ϑ) (Icc 0 1) := by
  -- (`h0` is not needed: strict monotonicity of the bisector coordinate holds for every `|ϑ| < π`)
  have _ := h0
  intro s₁ _ s₂ _ he
  have hℓ := juncLen_pos hε h
  have hF := A_F_strictMono h
  have e : juncArc A0 ε θu ϑ s₁ - (A0 + ε • dirOf θu) =
      juncArc A0 ε θu ϑ s₂ - (A0 + ε • dirOf θu) := by rw [he]
  rw [A_juncArc_sub, A_juncArc_sub] at e
  have e2 := congrArg (fun v => planeDot v (dirOf (θu + ϑ / 2))) e
  simp only [A_planeDot_frame] at e2
  have e3 : juncLen ε ϑ * (∫ r in (0 : ℝ)..s₁, Real.cos (ϑ * (Real.smoothTransition r - 1 / 2))) =
      juncLen ε ϑ * (∫ r in (0 : ℝ)..s₂, Real.cos (ϑ * (Real.smoothTransition r - 1 / 2))) := by
    linarith
  exact hF.injective (mul_left_cancel₀ hℓ.ne' e3)

/-! ### Unit G — the global curve: angles, subdivision, `Θ`, `L_ε` -/

section global

variable {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ}

/-- `|ϑ_j| < π` and `ϑ_j ≠ 0` -/
theorem turn_bounds (h : Admissible C D ε) (j : ZMod C.k) : turn C j ≠ 0 ∧ |turn C j| < Real.pi :=
  ⟨h.turn_ne j, abs_lt.mpr (principalAngle_bounds (D.regular j))⟩

/-- (G1 helper) `planeComplex (dirOf α) = e^{iα}` -/
theorem G1_planeComplex_dirOf (α : ℝ) : planeComplex (dirOf α) = Complex.exp (α * Complex.I) := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]; rfl
  · rw [Complex.exp_ofReal_mul_I_im]; rfl

/-- (G1 helper) polar form `w = |w| · dirOf (arg w)` -/
theorem G1_smul_dirOf_arg (w : Plane) :
    euclideanLength w • dirOf (Complex.arg (planeComplex w)) = w := by
  apply planeComplex_injective
  rw [planeComplex_smul, G1_planeComplex_dirOf, Complex.real_smul, euclideanLength,
    Complex.norm_mul_exp_arg_mul_I]

/-- (G1 helper) `dirOf (arg w) = w/|w|` for `w ≠ 0` -/
theorem G1_dirOf_arg {w : Plane} (hw : w ≠ 0) :
    dirOf (Complex.arg (planeComplex w)) = normalize w := by
  have h := normalize_smul_dirOf (euclideanLength_pos hw) (Complex.arg (planeComplex w))
  rw [G1_smul_dirOf_arg] at h
  exact h.symm

/-- (G1 helper) `dirOf` depends on the angle modulo `2π` only -/
theorem G1_dirOf_congr {α β : ℝ} (h : (α : Real.Angle) = β) : dirOf α = dirOf β := by
  have hc : Real.cos α = Real.cos β := by rw [← Real.Angle.cos_coe, h, Real.Angle.cos_coe]
  have hs : Real.sin α = Real.sin β := by rw [← Real.Angle.sin_coe, h, Real.Angle.sin_coe]
  simp only [dirOf, hc, hs]

/-- (G1 helper) `θu j ≡ arg δ_{j−1}` modulo `2π` (induction with `principalAngle_coe_angle`) -/
theorem G1_θu_coe_angle (hreg : Regular C.P) (j : ℕ) :
    ((θu C j : ℝ) : Real.Angle) =
      ((planeComplex (edge C.P ((j : ZMod C.k) - 1))).arg : Real.Angle) := by
  induction j with
  | zero =>
    have h0 : Complex.arg (planeComplex (uDir C 0)) =
        Complex.arg (planeComplex (edge C.P ((0 : ZMod C.k) - 1))) := by
      unfold uDir normalize
      rw [planeComplex_smul, Complex.real_smul,
        Complex.arg_real_mul _ (inv_pos.mpr (euclideanLength_pos (hreg 0).1))]
    show ((Complex.arg (planeComplex (uDir C 0)) : ℝ) : Real.Angle) = _
    rw [h0, Nat.cast_zero]
  | succ j ih =>
    show ((θu C j + turn C j : ℝ) : Real.Angle) = _
    rw [Real.Angle.coe_add, ih]
    unfold turn principalTurn
    rw [principalAngle_coe_angle (hreg j).1 (hreg j).2.1]
    have hj : ((j + 1 : ℕ) : ZMod C.k) - 1 = (j : ZMod C.k) := by push_cast; ring
    rw [hj]
    abel

/-- `dirOf (θu j) = u_j` (induction: `v_j = u_j · e^{iϑ_j}` by the definition of the principal turn) -/
theorem dirOf_θu (hreg : Regular C.P) (j : ℕ) : dirOf (θu C j) = uDir C j := by
  unfold uDir
  rw [G1_dirOf_congr (G1_θu_coe_angle hreg j), G1_dirOf_arg (hreg j).1]

/-- `dirOf (θu j + ϑ_j) = v_j` -/
theorem dirOf_θu_add_turn (hreg : Regular C.P) (j : ℕ) : dirOf (θu C j + turn C j) = vDir C j := by
  have h : ((θu C j + turn C j : ℝ) : Real.Angle) =
      ((planeComplex (edge C.P (j : ZMod C.k))).arg : Real.Angle) := by
    rw [Real.Angle.coe_add, G1_θu_coe_angle hreg j]
    unfold turn principalTurn
    rw [principalAngle_coe_angle (hreg j).1 (hreg j).2.1]
    abel
  unfold vDir
  rw [G1_dirOf_congr h, G1_dirOf_arg (hreg j).2.1]

/-- `θu k − θu 0 = Σ ϑ_j = 2π rot(L)` -/
theorem θu_last : θu C C.k = θu C 0 + 2 * Real.pi * rotationNumber C.P := by
  have key : ∀ n : ℕ, θu C n = θu C 0 + ∑ j ∈ Finset.range n, turn C j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      show θu C n + turn C n = _
      rw [ih, Finset.sum_range_succ, add_assoc]
  rw [key, sum_range_natCast_eq_sum_zmod (turn C), two_pi_mul_rotationNumber]
  rfl

theorem uDir_succ (j : ℕ) : uDir C (j + 1 : ℕ) = vDir C j := by
  unfold uDir vDir
  congr 2
  push_cast
  ring

theorem ℓ_pos (h : Admissible C D ε) (j : ℕ) : 0 < ℓ C ε j :=
  juncLen_pos h.ε_pos (turn_bounds h j).2

/-- `ε < |δ_j|/3`, so the straight part has positive length and the two sub-segments are disjoint -/
theorem three_mul_lt_edgeLength (h : Admissible C D ε) (j : ZMod C.k) :
    3 * ε < euclideanLength (edge C.P j) := by
  have h1 : ηℓ C ≤ euclideanLength (edge C.P j) :=
    Finset.inf'_le (fun i => euclideanLength (edge C.P i)) (Finset.mem_univ j)
  have h2 := h.ε_lt
  unfold clearance at h2
  have h3 := min_le_right (min (ηv C) (ηe C)) (min (ηℓ C) (ηX C))
  have h4 := min_le_left (ηℓ C) (ηX C)
  linarith

theorem str_pos (h : Admissible C D ε) {j : ℕ} (_hj : j < C.k) : 0 < str C ε j := by
  unfold str
  linarith [three_mul_lt_edgeLength h (j : ZMod C.k), h.ε_pos]

theorem Λ_pos (h : Admissible C D ε) : 0 < Λ C ε :=
  Finset.sum_pos (fun j hj => add_pos (ℓ_pos h j) (str_pos h (Finset.mem_range.mp hj)))
    ⟨0, Finset.mem_range.mpr (by have := C.hk; omega)⟩

theorem a_zero : a C ε 0 = 0 := by
  simp [a]

theorem a_last (h : Admissible C D ε) : a C ε C.k = 1 := by
  show Λ C ε / Λ C ε = 1
  exact div_self (Λ_pos h).ne'

theorem a_lt_b (h : Admissible C D ε) (j : ℕ) : a C ε j < b C ε j := by
  simp only [b]
  linarith [div_pos (ℓ_pos h j) (Λ_pos h)]

theorem b_lt_a (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) : b C ε j < a C ε (j + 1) := by
  simp only [a, b, Finset.sum_range_succ, add_div]
  linarith [div_pos (str_pos h hj) (Λ_pos h)]

theorem b_sub_a (j : ℕ) : b C ε j - a C ε j = ℓ C ε j / Λ C ε := by
  simp [b]

/-- `θu n = θu 0 + Σ_{j<n} ϑ_j` -/
theorem G2_θu_eq (n : ℕ) : θu C n = θu C 0 + ∑ j ∈ Finset.range n, turn C j := by
  induction n with
  | zero => simp
  | succ n ih =>
    show θu C n + turn C n = _
    rw [ih, Finset.sum_range_succ, add_assoc]

/-- `Σ_{j<k} ϑ_j = 2π rot(L)` -/
theorem G2_sum_turn : ∑ j ∈ Finset.range C.k, turn C j = 2 * Real.pi * rotationNumber C.P := by
  have h := θu_last (C := C)
  rw [G2_θu_eq] at h
  linarith

/-- `str j > 0` for every index (the edge index is read mod `k`) -/
theorem G2_str_pos (h : Admissible C D ε) (j : ℕ) : 0 < str C ε j := by
  unfold str
  linarith [three_mul_lt_edgeLength h (j : ZMod C.k), h.ε_pos]

theorem G2_a_succ (j : ℕ) : a C ε (j + 1) = a C ε j + (ℓ C ε j + str C ε j) / Λ C ε := by
  simp only [a, Finset.sum_range_succ, add_div]

theorem G2_a_strictMono (h : Admissible C D ε) : StrictMono (a C ε) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [G2_a_succ]
  linarith [div_pos (add_pos (ℓ_pos h j) (G2_str_pos h j)) (Λ_pos h)]

theorem G2_a_nonneg (h : Admissible C D ε) (j : ℕ) : 0 ≤ a C ε j := by
  rw [← a_zero (C := C) (ε := ε)]
  exact (G2_a_strictMono h).monotone (Nat.zero_le j)

theorem G2_a_le_one (h : Admissible C D ε) {j : ℕ} (hj : j ≤ C.k) : a C ε j ≤ 1 := by
  rw [← a_last h]
  exact (G2_a_strictMono h).monotone hj

theorem G2_b_le_a (h : Admissible C D ε) {i j : ℕ} (hij : i < j) : b C ε i ≤ a C ε j := by
  have h1 : a C ε (i + 1) - b C ε i = str C ε i / Λ C ε := by
    rw [G2_a_succ, b, add_div]; ring
  have h2 : b C ε i < a C ε (i + 1) := by
    linarith [div_pos (G2_str_pos h i) (Λ_pos h)]
  exact h2.le.trans ((G2_a_strictMono h).monotone hij)

theorem G2_b_le_one (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) : b C ε j ≤ 1 :=
  (G2_b_le_a h hj).trans (a_last h).le

theorem G2_b_le_b (h : Admissible C D ε) {i j : ℕ} (hij : i ≤ j) : b C ε i ≤ b C ε j := by
  rcases hij.lt_or_eq with hlt | heq
  · exact (G2_b_le_a h hlt).trans (a_lt_b h j).le
  · rw [heq]

/-- a term of `Θ` whose argument is at or before the junction start vanishes -/
theorem G2_term_of_le (h : Admissible C D ε) {x : ℝ} {i : ℕ} (hx : x ≤ a C ε i) :
    turn C i * Real.smoothTransition ((x - a C ε i) * Λ C ε / ℓ C ε i) = 0 := by
  have h0 : (x - a C ε i) * Λ C ε / ℓ C ε i ≤ 0 :=
    div_nonpos_iff.mpr (Or.inr ⟨mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (Λ_pos h).le,
      (ℓ_pos h i).le⟩)
  rw [Real.smoothTransition.zero_of_nonpos h0, mul_zero]

/-- the profile argument at the end of the junction is exactly `1` (= `junction_arg_b` below) -/
theorem G2_arg_b (h : Admissible C D ε) (i : ℕ) : (b C ε i - a C ε i) * Λ C ε / ℓ C ε i = 1 := by
  rw [b_sub_a, div_mul_cancel₀ _ (Λ_pos h).ne', div_self (ℓ_pos h i).ne']

/-- a term of `Θ` whose argument is at or after the junction end is the full turn -/
theorem G2_term_of_ge (h : Admissible C D ε) {x : ℝ} {i : ℕ} (hx : b C ε i ≤ x) :
    turn C i * Real.smoothTransition ((x - a C ε i) * Λ C ε / ℓ C ε i) = turn C i := by
  have h1 : (1 : ℝ) ≤ (x - a C ε i) * Λ C ε / ℓ C ε i := by
    rw [← G2_arg_b h i]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (Λ_pos h).le) (ℓ_pos h i).le
  rw [Real.smoothTransition.one_of_one_le h1, mul_one]

theorem G2_sum_of_nonpos (h : Admissible C D ε) {x : ℝ} (hx : x ≤ 0) :
    ∑ i ∈ Finset.range C.k,
      turn C i * Real.smoothTransition ((x - a C ε i) * Λ C ε / ℓ C ε i) = 0 :=
  Finset.sum_eq_zero fun i _ => G2_term_of_le h (hx.trans (G2_a_nonneg h i))

theorem G2_sum_of_ge (h : Admissible C D ε) {x : ℝ} (hx : b C ε (C.k - 1) ≤ x) :
    ∑ i ∈ Finset.range C.k,
      turn C i * Real.smoothTransition ((x - a C ε i) * Λ C ε / ℓ C ε i) =
      2 * Real.pi * rotationNumber C.P := by
  rw [← G2_sum_turn]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ C.k - 1 := by have := Finset.mem_range.mp hi; omega
  exact G2_term_of_ge h ((G2_b_le_b h hi').trans hx)

theorem G2_sum_junction (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) {x : ℝ}
    (hx : x ∈ Icc (a C ε j) (b C ε j)) :
    ∑ i ∈ Finset.range C.k,
      turn C i * Real.smoothTransition ((x - a C ε i) * Λ C ε / ℓ C ε i) =
      ∑ i ∈ Finset.range j, turn C i +
        turn C j * Real.smoothTransition ((x - a C ε j) * Λ C ε / ℓ C ε j) := by
  rw [← Finset.sum_range_add_sum_Ico _ (show j + 1 ≤ C.k from hj), Finset.sum_range_succ]
  have h1 : ∑ i ∈ Finset.Ico (j + 1) C.k,
      turn C i * Real.smoothTransition ((x - a C ε i) * Λ C ε / ℓ C ε i) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : j < i := by have := (Finset.mem_Ico.mp hi).1; omega
    exact G2_term_of_le h (hx.2.trans (G2_b_le_a h hi'))
  have h2 : ∑ i ∈ Finset.range j,
      turn C i * Real.smoothTransition ((x - a C ε i) * Λ C ε / ℓ C ε i) =
      ∑ i ∈ Finset.range j, turn C i :=
    Finset.sum_congr rfl fun i hi =>
      G2_term_of_ge h ((G2_b_le_a h (Finset.mem_range.mp hi)).trans hx.1)
  rw [h1, h2, add_zero]

theorem G2_sum_straight (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) {x : ℝ}
    (hx : x ∈ Icc (b C ε j) (a C ε (j + 1))) :
    ∑ i ∈ Finset.range C.k,
      turn C i * Real.smoothTransition ((x - a C ε i) * Λ C ε / ℓ C ε i) =
      ∑ i ∈ Finset.range (j + 1), turn C i := by
  rw [← Finset.sum_range_add_sum_Ico _ (show j + 1 ≤ C.k from hj)]
  have h1 : ∑ i ∈ Finset.Ico (j + 1) C.k,
      turn C i * Real.smoothTransition ((x - a C ε i) * Λ C ε / ℓ C ε i) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    exact G2_term_of_le h (hx.2.trans ((G2_a_strictMono h).monotone (Finset.mem_Ico.mp hi).1))
  have h2 : ∑ i ∈ Finset.range (j + 1),
      turn C i * Real.smoothTransition ((x - a C ε i) * Λ C ε / ℓ C ε i) =
      ∑ i ∈ Finset.range (j + 1), turn C i :=
    Finset.sum_congr rfl fun i hi =>
      G2_term_of_ge h ((G2_b_le_b h (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).trans hx.1)
  rw [h1, h2, add_zero]

/-- on the closed interval `[m, m+1]`, `Θ` is the smooth expression with `⌊t⌋ = m`, `fract t = t − m`
(at `t = m + 1` both readings agree because `Σ ϑ_j = 2π rot`) -/
theorem G2_Θ_eq (h : Admissible C D ε) (m : ℤ) {t : ℝ} (ht : t ∈ Icc (m : ℝ) (m + 1)) :
    Θ C ε t = θu C 0 + 2 * Real.pi * rotationNumber C.P * m +
      ∑ i ∈ Finset.range C.k,
        turn C i * Real.smoothTransition ((t - m - a C ε i) * Λ C ε / ℓ C ε i) := by
  rcases ht.2.lt_or_eq with hlt | heq
  · have hfl : ⌊t⌋ = m := Int.floor_eq_iff.mpr ⟨ht.1, hlt⟩
    unfold Θ
    rw [← Int.self_sub_floor, hfl]
  · have hfl : ⌊t⌋ = m + 1 := by rw [heq, Int.floor_add_one, Int.floor_intCast]
    have hfr : Int.fract t = 0 := by rw [heq, Int.fract_add_one, Int.fract_intCast]
    have hk : C.k - 1 < C.k := by have := C.hk; omega
    have htm : t - m = 1 := by linarith
    unfold Θ
    rw [hfl, hfr, G2_sum_of_nonpos h le_rfl, htm, G2_sum_of_ge h (G2_b_le_one h hk)]
    push_cast
    ring

/-- the local expression of `Θ` is `C^∞` -/
theorem G2_G_smooth (m : ℤ) : ContDiff ℝ ∞ (fun t : ℝ =>
    θu C 0 + 2 * Real.pi * rotationNumber C.P * m +
      ∑ i ∈ Finset.range C.k,
        turn C i * Real.smoothTransition ((t - m - a C ε i) * Λ C ε / ℓ C ε i)) := by
  refine contDiff_const.add (ContDiff.sum fun i _ => contDiff_const.mul
    (Real.smoothTransition.contDiff.comp ?_))
  exact (((contDiff_id.sub contDiff_const).sub contDiff_const).mul contDiff_const).div_const _

/-- `Θ` is `C^∞` (locally, near every point, it is one of the smooth expressions
`θu j + ϑ_j φ((t − m − a j)Λ/ℓ_j)`; the floor and fract are locally affine or absorbed by
`φ = 0` on `(−∞,0]`, `φ = 1` on `[1,∞)`) -/
theorem Θ_smooth (h : Admissible C D ε) : ContDiff ℝ ∞ (Θ C ε) := by
  rw [contDiff_iff_contDiffAt]
  intro t₀
  have hk : C.k - 1 < C.k := by have := C.hk; omega
  have hk1 : C.k - 1 + 1 = C.k := by have := C.hk; omega
  have hδ : b C ε (C.k - 1) < 1 := by
    have := b_lt_a h hk
    rwa [hk1, a_last h] at this
  refine (G2_G_smooth (C := C) (ε := ε) ⌊t₀⌋).contDiffAt.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem
    (Ioo_mem_nhds (a := (⌊t₀⌋ : ℝ) - (1 - b C ε (C.k - 1))) (b := (⌊t₀⌋ : ℝ) + 1) ?_ ?_) ?_
  · linarith [Int.floor_le t₀]
  · exact Int.lt_floor_add_one t₀
  · intro t ht
    show Θ C ε t = _
    rcases le_or_gt (⌊t₀⌋ : ℝ) t with hle | hlt
    · exact G2_Θ_eq h ⌊t₀⌋ ⟨hle, ht.2.le⟩
    · have hb0 : 0 ≤ b C ε (C.k - 1) := (G2_a_nonneg h _).trans (a_lt_b h _).le
      have hfl : ⌊t⌋ = ⌊t₀⌋ - 1 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith [ht.1], by push_cast; linarith⟩
      have hfr : Int.fract t = t - ((⌊t₀⌋ - 1 : ℤ) : ℝ) := by rw [← Int.self_sub_floor, hfl]
      beta_reduce
      unfold Θ
      rw [hfr, hfl, G2_sum_of_ge h (x := t - ((⌊t₀⌋ - 1 : ℤ) : ℝ)) (by push_cast; linarith [ht.1]),
        G2_sum_of_nonpos h (x := t - (⌊t₀⌋ : ℝ)) (by linarith)]
      push_cast
      ring

/-- `Θ (t + 1) = Θ t + 2π rot(L)` -/
theorem Θ_add_one (t : ℝ) : Θ C ε (t + 1) = Θ C ε t + 2 * Real.pi * rotationNumber C.P := by
  unfold Θ
  rw [Int.floor_add_one, Int.fract_add_one]
  push_cast
  ring

/-- on the junction at corner `j`, `Θ` is the junction lift -/
theorem Θ_on_junction (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (a C ε j) (b C ε j)) : Θ C ε t = liftAt C ε j t := by
  have h0 : t ∈ Icc (((0 : ℤ) : ℝ)) (((0 : ℤ) : ℝ) + 1) := by
    rw [Int.cast_zero, zero_add]
    exact ⟨(G2_a_nonneg h j).trans ht.1, ht.2.trans (G2_b_le_one h hj)⟩
  rw [G2_Θ_eq h 0 h0]
  simp only [Int.cast_zero, sub_zero, mul_zero, add_zero]
  rw [G2_sum_junction h hj ht, liftAt, G2_θu_eq j]
  ring

/-- on the straight part along edge `j`, `Θ` is the constant `θu (j+1)` -/
theorem Θ_on_straight (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (b C ε j) (a C ε (j + 1))) : Θ C ε t = θu C (j + 1) := by
  have h0 : t ∈ Icc (((0 : ℤ) : ℝ)) (((0 : ℤ) : ℝ) + 1) := by
    rw [Int.cast_zero, zero_add]
    exact ⟨((G2_a_nonneg h j).trans (a_lt_b h j).le).trans ht.1,
      ht.2.trans (G2_a_le_one h (show j + 1 ≤ C.k from hj))⟩
  rw [G2_Θ_eq h 0 h0]
  simp only [Int.cast_zero, sub_zero, mul_zero, add_zero]
  rw [G2_sum_straight h hj ht, G2_θu_eq (j + 1)]

theorem tangentField_periodic (hreg : Regular C.P) : Function.Periodic (tangentField C ε) 1 := by
  intro t
  obtain ⟨m, hm⟩ := rotationNumber_integer hreg
  show dirOf (Θ C ε (t + 1)) = dirOf (Θ C ε t)
  rw [Θ_add_one, hm]
  unfold dirOf
  have e : Θ C ε t + 2 * Real.pi * (m : ℝ) = Θ C ε t + (m : ℝ) * (2 * Real.pi) := by ring
  rw [e, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem tangentField_smooth (h : Admissible C D ε) : ContDiff ℝ ∞ (tangentField C ε) := by
  unfold tangentField dirOf
  exact (Real.contDiff_cos.comp (Θ_smooth h)).prodMk (Real.contDiff_sin.comp (Θ_smooth h))

theorem tangentField_unit (t : ℝ) : euclideanLength (tangentField C ε t) = 1 := dirOf_unit _

theorem hasDerivAt_curveMap (h : Admissible C D ε) (t : ℝ) :
    HasDerivAt (curveMap C ε) (Λ C ε • tangentField C ε t) t := by
  have hc : Continuous (tangentField C ε) := (tangentField_smooth h).continuous
  have h1 : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, tangentField C ε s) (tangentField C ε t) t :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  exact (h1.const_smul (Λ C ε)).const_add (A0 C ε 0)

theorem curveMap_smooth (h : Admissible C D ε) : ContDiff ℝ ∞ (curveMap C ε) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (hasDerivAt_curveMap h t).differentiableAt, ?_⟩
  have e : deriv (curveMap C ε) = fun t => Λ C ε • tangentField C ε t :=
    funext fun t => (hasDerivAt_curveMap h t).deriv
  rw [e]
  exact (contDiff_const (c := Λ C ε)).smul (tangentField_smooth h)

theorem deriv_curveMap (h : Admissible C D ε) (t : ℝ) :
    deriv (curveMap C ε) t = Λ C ε • tangentField C ε t :=
  (hasDerivAt_curveMap h t).deriv

/-- on the junction, the tangent field is the abstract junction direction in the profile parameter -/
theorem G2_tangentField_junction (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (a C ε j) (b C ε j)) :
    tangentField C ε t = juncDir (θu C j) (turn C j) ((t - a C ε j) * Λ C ε / ℓ C ε j) := by
  unfold tangentField
  rw [Θ_on_junction h hj ht]
  rfl

/-- the substitution `r = (s − a j)Λ/ℓ_j` on the junction, up to any `t ∈ [a j, b j]` -/
theorem G2_integral_junction_upto (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (a C ε j) (b C ε j)) :
    (∫ s in a C ε j..t, tangentField C ε s) =
      (ℓ C ε j / Λ C ε) •
        ∫ r in (0 : ℝ)..((t - a C ε j) * Λ C ε / ℓ C ε j), juncDir (θu C j) (turn C j) r := by
  have hΛ := Λ_pos h
  have hℓ := ℓ_pos h j
  have hc : Λ C ε / ℓ C ε j ≠ 0 := (div_pos hΛ hℓ).ne'
  have h1 : (∫ s in a C ε j..t, tangentField C ε s) =
      ∫ s in a C ε j..t, juncDir (θu C j) (turn C j)
        ((Λ C ε / ℓ C ε j) * s - (Λ C ε / ℓ C ε j) * a C ε j) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    rw [G2_tangentField_junction h hj ⟨hs.1, hs.2.trans ht.2⟩]
    congr 1
    ring
  rw [h1, intervalIntegral.integral_comp_mul_sub _ hc, inv_div, sub_self,
    show Λ C ε / ℓ C ε j * t - Λ C ε / ℓ C ε j * a C ε j = (t - a C ε j) * Λ C ε / ℓ C ε j by ring]

/-- the integral of the tangent field over the junction at corner `j` -/
theorem integral_tangentField_junction (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) :
    (∫ s in a C ε j..b C ε j, tangentField C ε s) = (ε / Λ C ε) • (uDir C j + vDir C j) := by
  rw [G2_integral_junction_upto h hj (right_mem_Icc.mpr (a_lt_b h j).le), G2_arg_b h j]
  have hθ := (turn_bounds h (j : ZMod C.k)).2
  have key := juncArc_one (A0 := A0 C ε j) (ε := ε) (θu := θu C j) (ϑ := turn C j) hθ
  unfold juncArc at key
  have key' : ℓ C ε j • (∫ r in (0 : ℝ)..1, juncDir (θu C j) (turn C j) r) =
      ε • (dirOf (θu C j) + dirOf (θu C j + turn C j)) := add_left_cancel key
  rw [dirOf_θu D.regular j, dirOf_θu_add_turn D.regular j] at key'
  simp only [div_eq_inv_mul, mul_smul, key']

/-- on the straight part along edge `j`, the tangent field is the constant `v_j` -/
theorem G2_tangentField_straight (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (b C ε j) (a C ε (j + 1))) : tangentField C ε t = vDir C j := by
  unfold tangentField
  rw [Θ_on_straight h hj ht]
  exact dirOf_θu_add_turn D.regular j

/-- the integral over the straight part, up to any `t ∈ [b j, a (j+1)]` -/
theorem G2_integral_straight_upto (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (b C ε j) (a C ε (j + 1))) :
    (∫ s in b C ε j..t, tangentField C ε s) = (t - b C ε j) • vDir C j := by
  rw [← intervalIntegral.integral_const]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht.1] at hs
  exact G2_tangentField_straight h hj ⟨hs.1, hs.2.trans ht.2⟩

/-- the integral over the straight part along edge `j` -/
theorem integral_tangentField_straight (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) :
    (∫ s in b C ε j..a C ε (j + 1), tangentField C ε s) = (str C ε j / Λ C ε) • vDir C j := by
  rw [G2_integral_straight_upto h hj (right_mem_Icc.mpr (b_lt_a h hj).le)]
  congr 1
  rw [G2_a_succ, b, add_div]
  ring

/-- `curveMap t = curveMap s + Λ ∫_s^t T` -/
theorem G2_curveMap_eq_add (h : Admissible C D ε) (s t : ℝ) :
    curveMap C ε t = curveMap C ε s + Λ C ε • ∫ r in s..t, tangentField C ε r := by
  have hc : Continuous (tangentField C ε) := (tangentField_smooth h).continuous
  unfold curveMap
  rw [add_assoc, ← smul_add, intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 s) (hc.intervalIntegrable s t)]

/-- `|δ_j| v_j = δ_j` -/
theorem G2_edgeLength_smul_vDir (h : Admissible C D ε) (j : ℕ) :
    euclideanLength (edge C.P j) • vDir C j = edge C.P j := by
  have hedge : edge C.P (j : ZMod C.k) ≠ 0 := by
    intro h0
    have := three_mul_lt_edgeLength h (j : ZMod C.k)
    rw [h0, euclideanLength_formula] at this
    norm_num at this
    linarith [h.ε_pos]
  unfold vDir normalize
  rw [smul_smul, mul_inv_cancel₀ (euclideanLength_pos hedge).ne', one_smul]

/-- `curveMap (a j) = A₀(j)` for `j ≤ k`, by induction along the pieces -/
theorem G2_curveMap_a_aux (h : Admissible C D ε) :
    ∀ j, j ≤ C.k → curveMap C ε (a C ε j) = A0 C ε j := by
  intro j
  induction j with
  | zero => intro _; rw [a_zero]; simp [curveMap]
  | succ j ih =>
    intro hj
    have hj' : j < C.k := hj
    have hc : Continuous (tangentField C ε) := (tangentField_smooth h).continuous
    have hΛ := (Λ_pos h).ne'
    rw [G2_curveMap_eq_add h (a C ε j), ih hj'.le,
      ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ (b C ε j))
        (hc.intervalIntegrable _ _),
      integral_tangentField_junction h hj', integral_tangentField_straight h hj',
      smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hΛ, mul_div_cancel₀ _ hΛ]
    unfold A0
    rw [uDir_succ]
    have hs : str C ε j • vDir C j = edge C.P j - (2 * ε) • vDir C j := by
      rw [str, sub_smul, G2_edgeLength_smul_vDir h j]
    rw [hs, edge, Nat.cast_succ]
    module

/-- the total displacement vanishes: `Σ_j [ε(u_j + v_j) + (|δ_j| − 2ε) v_j] = Σ_j δ_j = 0` -/
theorem integral_tangentField_period (h : Admissible C D ε) :
    (∫ s in (0 : ℝ)..1, tangentField C ε s) = 0 := by
  have h1 := G2_curveMap_a_aux h C.k le_rfl
  rw [a_last h] at h1
  have h2 : A0 C ε C.k = A0 C ε 0 := by
    simp [A0, uDir]
  rw [h2] at h1
  unfold curveMap at h1
  have h3 : Λ C ε • ∫ s in (0 : ℝ)..1, tangentField C ε s = 0 :=
    add_left_cancel (h1.trans (add_zero _).symm)
  exact (smul_eq_zero.mp h3).resolve_left (Λ_pos h).ne'

theorem curveMap_periodic (h : Admissible C D ε) : Function.Periodic (curveMap C ε) 1 := by
  intro t
  have hc : Continuous (tangentField C ε) := (tangentField_smooth h).continuous
  have h1 : (∫ s in (0 : ℝ)..t, tangentField C ε s) + ∫ s in t..(t + 1), tangentField C ε s =
      ∫ s in (0 : ℝ)..(t + 1), tangentField C ε s :=
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 t)
      (hc.intervalIntegrable t (t + 1))
  have h2 := (tangentField_periodic (C := C) (ε := ε) D.regular).intervalIntegral_add_eq t 0
  rw [zero_add, integral_tangentField_period h] at h2
  show A0 C ε 0 + Λ C ε • ∫ s in (0 : ℝ)..(t + 1), tangentField C ε s =
    A0 C ε 0 + Λ C ε • ∫ s in (0 : ℝ)..t, tangentField C ε s
  rw [← h1, h2, add_zero]

theorem curveMap_a (h : Admissible C D ε) {j : ℕ} (hj : j ≤ C.k) : curveMap C ε (a C ε j) = A0 C ε j := by
  exact G2_curveMap_a_aux h j hj

theorem curveMap_b (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) : curveMap C ε (b C ε j) = A1 C ε j := by
  rw [G2_curveMap_eq_add h (a C ε j), curveMap_a h hj.le, integral_tangentField_junction h hj,
    smul_smul, mul_div_cancel₀ _ (Λ_pos h).ne']
  unfold A0 A1
  module

/-- on the junction the curve is the abstract junction arc (substitution `s = (t − a j)Λ/ℓ_j`) -/
theorem curveMap_on_junction (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (a C ε j) (b C ε j)) :
    curveMap C ε t =
      juncArc (A0 C ε j) ε (θu C j) (turn C j) ((t - a C ε j) * Λ C ε / ℓ C ε j) := by
  rw [G2_curveMap_eq_add h (a C ε j), curveMap_a h hj.le, G2_integral_junction_upto h hj ht,
    smul_smul, mul_div_cancel₀ _ (Λ_pos h).ne']
  rfl

/-- on the straight part the curve runs straight at speed `Λ` -/
theorem curveMap_on_straight (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (b C ε j) (a C ε (j + 1))) :
    curveMap C ε t = A1 C ε j + (Λ C ε * (t - b C ε j)) • vDir C j := by
  rw [G2_curveMap_eq_add h (b C ε j), curveMap_b h hj, G2_integral_straight_upto h hj ht, smul_smul]

/-! #### the junction lifts `liftAt` -/

theorem liftAt_smooth (j : ℕ) : ContDiff ℝ ∞ (liftAt C ε j) := by
  unfold liftAt
  exact contDiff_const.add (contDiff_const.mul (Real.smoothTransition.contDiff.comp
    (((contDiff_id.sub contDiff_const).mul contDiff_const).div_const _)))

theorem liftAt_const_left (h : Admissible C D ε) (j : ℕ) {t : ℝ} (ht : t ≤ a C ε j) :
    liftAt C ε j t = liftAt C ε j (a C ε j) := by
  have hΛ := Λ_pos h
  have hℓ := ℓ_pos h j
  have h0 : (t - a C ε j) * Λ C ε / ℓ C ε j ≤ 0 := by
    have : t - a C ε j ≤ 0 := sub_nonpos.mpr ht
    exact div_nonpos_iff.mpr (Or.inr ⟨by nlinarith, hℓ.le⟩)
  unfold liftAt
  rw [Real.smoothTransition.zero_of_nonpos h0, sub_self, zero_mul, zero_div,
    Real.smoothTransition.zero]

/-- the profile argument at the end of the junction is exactly `1` -/
theorem junction_arg_b (h : Admissible C D ε) (j : ℕ) :
    (b C ε j - a C ε j) * Λ C ε / ℓ C ε j = 1 := by
  rw [b_sub_a, div_mul_cancel₀ _ (Λ_pos h).ne', div_self (ℓ_pos h j).ne']

theorem liftAt_const_right (h : Admissible C D ε) (j : ℕ) {t : ℝ} (ht : b C ε j ≤ t) :
    liftAt C ε j t = liftAt C ε j (b C ε j) := by
  have h1 : (1 : ℝ) ≤ (b C ε j - a C ε j) * Λ C ε / ℓ C ε j := (junction_arg_b h j).ge
  have h2 : (1 : ℝ) ≤ (t - a C ε j) * Λ C ε / ℓ C ε j :=
    h1.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (Λ_pos h).le) (ℓ_pos h j).le)
  unfold liftAt
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2]

theorem liftAt_a (j : ℕ) : liftAt C ε j (a C ε j) = θu C j := by
  simp [liftAt, Real.smoothTransition.zero]

theorem liftAt_b (h : Admissible C D ε) (j : ℕ) : liftAt C ε j (b C ε j) = θu C j + turn C j := by
  unfold liftAt
  rw [junction_arg_b h j, Real.smoothTransition.one, mul_one]

/-- (G3 helper) the profile argument `(t − a j)Λ/ℓ_j` is strictly increasing in `t` -/
theorem G3_junction_arg_lt (h : Admissible C D ε) (j : ℕ) {s t : ℝ} (hst : s < t) :
    (s - a C ε j) * Λ C ε / ℓ C ε j < (t - a C ε j) * Λ C ε / ℓ C ε j :=
  div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (by linarith) (Λ_pos h)) (ℓ_pos h j)

/-- (G3 helper) on the junction `[a j, b j]` the profile argument lies in `[0, 1]` -/
theorem G3_junction_arg_mem_Icc (h : Admissible C D ε) (j : ℕ) {t : ℝ}
    (ht : t ∈ Icc (a C ε j) (b C ε j)) : (t - a C ε j) * Λ C ε / ℓ C ε j ∈ Icc (0 : ℝ) 1 := by
  have hΛ := Λ_pos h
  have hℓ := ℓ_pos h j
  refine ⟨div_nonneg (mul_nonneg (sub_nonneg.mpr ht.1) hΛ.le) hℓ.le, ?_⟩
  rw [← junction_arg_b h j]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith [ht.2]) hΛ.le) hℓ.le

/-- (G3 helper) on the open junction `(a j, b j)` the profile argument lies in `(0, 1)` -/
theorem G3_junction_arg_mem_Ioo (h : Admissible C D ε) (j : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (a C ε j) (b C ε j)) : (t - a C ε j) * Λ C ε / ℓ C ε j ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨div_pos (mul_pos (sub_pos.mpr ht.1) (Λ_pos h)) (ℓ_pos h j), ?_⟩
  rw [← junction_arg_b h j]
  exact G3_junction_arg_lt h j ht.2

theorem liftAt_strictMonoOn (h : Admissible C D ε) {j : ℕ} (hpos : 0 < turn C j) :
    StrictMonoOn (liftAt C ε j) (Icc (a C ε j) (b C ε j)) := by
  intro s hs t ht hst
  have hφ := smoothTransition_strictMonoOn (G3_junction_arg_mem_Icc h j hs)
    (G3_junction_arg_mem_Icc h j ht) (G3_junction_arg_lt h j hst)
  have := mul_lt_mul_of_pos_left hφ hpos
  unfold liftAt
  linarith

theorem liftAt_strictAntiOn (h : Admissible C D ε) {j : ℕ} (hneg : turn C j < 0) :
    StrictAntiOn (liftAt C ε j) (Icc (a C ε j) (b C ε j)) := by
  intro s hs t ht hst
  have hφ := smoothTransition_strictMonoOn (G3_junction_arg_mem_Icc h j hs)
    (G3_junction_arg_mem_Icc h j ht) (G3_junction_arg_lt h j hst)
  have := mul_lt_mul_of_neg_left hφ hneg
  unfold liftAt
  linarith

/-- (G3 helper) the derivative of the junction lift: `ϑ_j φ'((t − a j)Λ/ℓ_j) · Λ/ℓ_j` -/
theorem G3_hasDerivAt_liftAt (j : ℕ) (t : ℝ) :
    HasDerivAt (liftAt C ε j)
      (turn C j * (deriv Real.smoothTransition ((t - a C ε j) * Λ C ε / ℓ C ε j) *
        (1 * Λ C ε / ℓ C ε j))) t := by
  have hg : HasDerivAt (fun t => (t - a C ε j) * Λ C ε / ℓ C ε j) (1 * Λ C ε / ℓ C ε j) t :=
    (((hasDerivAt_id t).sub_const (a C ε j)).mul_const (Λ C ε)).div_const (ℓ C ε j)
  have hφ : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((t - a C ε j) * Λ C ε / ℓ C ε j))
      ((t - a C ε j) * Λ C ε / ℓ C ε j) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  exact ((hφ.comp t hg).const_mul (turn C j)).const_add (θu C j)

theorem deriv_liftAt_ne_zero (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Ioo (a C ε j) (b C ε j)) : deriv (liftAt C ε j) t ≠ 0 := by
  have _ := hj -- `hj` is not needed: the lift is defined for every `j`
  rw [(G3_hasDerivAt_liftAt j t).deriv]
  obtain ⟨hs0, hs1⟩ := G3_junction_arg_mem_Ioo h j ht
  have h1 : deriv Real.smoothTransition ((t - a C ε j) * Λ C ε / ℓ C ε j) ≠ 0 :=
    (deriv_smoothTransition_pos hs0 hs1).ne'
  have h2 : 1 * Λ C ε / ℓ C ε j ≠ 0 := by
    rw [one_mul]; exact (div_pos (Λ_pos h) (ℓ_pos h j)).ne'
  exact mul_ne_zero (turn_bounds h j).1 (mul_ne_zero h1 h2)

/-- the unit tangent is `dirOf ∘ Θ` -/
theorem normalize_deriv_curveMap (h : Admissible C D ε) (t : ℝ) :
    normalize (deriv (curveMap C ε) t) = tangentField C ε t := by
  rw [deriv_curveMap h]
  exact normalize_smul_dirOf (Λ_pos h) _

theorem liftAt_isLiftOn (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) :
    IsLiftOn (fun t => normalize (deriv (curveMap C ε) t)) (liftAt C ε j) (a C ε j) (b C ε j) := by
  refine ⟨(liftAt_smooth j).continuous.continuousOn, fun t ht => ?_⟩
  show normalize (deriv (curveMap C ε) t) = _
  rw [normalize_deriv_curveMap h, tangentField, Θ_on_junction h hj ht]
  rfl

/-- (G3 helper) two values of the junction lift differ by less than `π`: both lie between
`θu j` and `θu j + ϑ_j` (the profile takes values in `[0,1]`) and `|ϑ_j| < π` -/
theorem G3_abs_liftAt_sub_lt_pi (h : Admissible C D ε) (j : ℕ) (s t : ℝ) :
    |liftAt C ε j s - liftAt C ε j t| < Real.pi := by
  have hπ := (turn_bounds h j).2
  have e : liftAt C ε j s - liftAt C ε j t =
      turn C j * (Real.smoothTransition ((s - a C ε j) * Λ C ε / ℓ C ε j) -
        Real.smoothTransition ((t - a C ε j) * Λ C ε / ℓ C ε j)) := by
    unfold liftAt; ring
  have hle : |Real.smoothTransition ((s - a C ε j) * Λ C ε / ℓ C ε j) -
      Real.smoothTransition ((t - a C ε j) * Λ C ε / ℓ C ε j)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Real.smoothTransition.nonneg ((s - a C ε j) * Λ C ε / ℓ C ε j),
      Real.smoothTransition.le_one ((s - a C ε j) * Λ C ε / ℓ C ε j),
      Real.smoothTransition.nonneg ((t - a C ε j) * Λ C ε / ℓ C ε j),
      Real.smoothTransition.le_one ((t - a C ε j) * Λ C ε / ℓ C ε j)]
  rw [e, abs_mul]
  calc |turn C j| * |Real.smoothTransition ((s - a C ε j) * Λ C ε / ℓ C ε j) -
        Real.smoothTransition ((t - a C ε j) * Λ C ε / ℓ C ε j)|
      ≤ |turn C j| * 1 := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    _ = |turn C j| := mul_one _
    _ < Real.pi := hπ

theorem tangent_injOn_junction (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) :
    InjOn (fun t => normalize (deriv (curveMap C ε) t)) (Icc (a C ε j) (b C ε j)) := by
  intro s hs t ht hst
  have hl := liftAt_isLiftOn h hj
  have e1 : normalize (deriv (curveMap C ε) s) = dirOf (liftAt C ε j s) := hl.2 s hs
  have e2 : normalize (deriv (curveMap C ε) t) = dirOf (liftAt C ε j t) := hl.2 t ht
  have he : dirOf (liftAt C ε j s) = dirOf (liftAt C ε j t) := by
    rw [← e1, ← e2]; exact hst
  have heq : liftAt C ε j s = liftAt C ε j t :=
    dirOf_injOn_of_lt_pi (G3_abs_liftAt_sub_lt_pi h j s t) he
  have hinj : InjOn (liftAt C ε j) (Icc (a C ε j) (b C ε j)) := by
    rcases lt_or_gt_of_ne (h.turn_ne j) with hneg | hpos
    · exact (liftAt_strictAntiOn h hneg).injOn
    · exact (liftAt_strictMonoOn h hpos).injOn
  exact hinj hs ht heq

end global

/-! ### Unit E — the clearance and the disc package on the polygon alone (sm-3:3822-3846) -/

section discs

variable {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ}

/-- `planeComplex` is additive. -/
theorem E_planeComplex_add (u v : Plane) :
    planeComplex (u + v) = planeComplex u + planeComplex v := rfl

theorem E_planeComplex_sub (u v : Plane) :
    planeComplex (u - v) = planeComplex u - planeComplex v := rfl

/-- the Euclidean distance is the distance of `ℂ` through `planeComplex` -/
theorem E_eucDist_eq (p q : Plane) : eucDist p q = dist (planeComplex p) (planeComplex q) := by
  rw [eucDist, euclideanLength, E_planeComplex_sub, Complex.dist_eq]

theorem E_eucDist_comm (p q : Plane) : eucDist p q = eucDist q p := by
  rw [E_eucDist_eq, E_eucDist_eq, dist_comm]

theorem E_eucDist_triangle (p q r : Plane) : eucDist p r ≤ eucDist p q + eucDist q r := by
  rw [E_eucDist_eq, E_eucDist_eq, E_eucDist_eq]
  exact dist_triangle _ _ _

theorem E_eucDist_add_left (p v : Plane) : eucDist (p + v) p = euclideanLength v := by
  rw [eucDist, add_sub_cancel_left]

theorem E_eucDist_sub_left (p v : Plane) : eucDist (p - v) p = euclideanLength v := by
  rw [eucDist, sub_sub_cancel_left, euclideanLength, planeComplex_neg, norm_neg]
  rfl

/-- the product (sup) distance is at most the Euclidean one -/
theorem E_dist_le_eucDist (p q : Plane) : dist p q ≤ eucDist p q := by
  rw [E_eucDist_eq, Complex.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_le (Complex.abs_re_le_norm (planeComplex p - planeComplex q))
    (Complex.abs_im_le_norm (planeComplex p - planeComplex q))

/-- the Euclidean distance is at most the sum of the coordinate distances -/
theorem E_eucDist_le_add (p q : Plane) : eucDist p q ≤ |p.1 - q.1| + |p.2 - q.2| := by
  rw [E_eucDist_eq, Complex.dist_eq]
  exact Complex.norm_le_abs_re_add_abs_im (planeComplex p - planeComplex q)

theorem E_continuous_eucDist (q : Plane) : Continuous fun p => eucDist p q := by
  simp only [E_eucDist_eq]
  exact continuous_planeComplex.dist continuous_const

/-- `far p S ≤ eucDist p q` for `q ∈ S` -/
theorem E_far_le (p q : Plane) {S : Set Plane} (hq : q ∈ S) : far p S ≤ eucDist p q := by
  rw [far, E_eucDist_eq]
  exact Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem _ hq)

/-- `far` is positive on a nonempty compact set not containing the point -/
theorem E_far_pos (p : Plane) {S : Set Plane} (hS : IsCompact S) (hne : S.Nonempty)
    (hp : p ∉ S) : 0 < far p S := by
  rw [far]
  refine (IsClosed.notMem_iff_infDist_pos (hS.image continuous_planeComplex).isClosed
    (hne.image _)).mp ?_
  rintro ⟨q, hq, hpq⟩
  rw [planeComplex_injective hpq] at hq
  exact hp hq

/-- edges of a generic polygon are nonzero (`Regular`) -/
theorem E_edge_ne_zero (gen : (Shadow.single C).Generic) (i : ZMod C.k) : edge C.P i ≠ 0 := by
  have hreg : Regular C.P := gen.regular 0
  exact (hreg i).2.1

/-- `2 ≠ 0` in `ZMod k` for `k ≥ 3` -/
theorem E_two_ne_zero (C : PolyComp) : (2 : ZMod C.k) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod C.k) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (ZMod C.k) C.k] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  have := C.hk
  omega

/-- the edge `i + 1` is not incident to the corner `i` -/
theorem E_not_incident_succ (i : ZMod C.k) : ¬ incident i (i + 1) := by
  rintro (h | h)
  · apply E_two_ne_zero C
    have h1 : (1 : ZMod C.k) = -1 := by
      rw [sub_eq_add_neg] at h
      exact add_left_cancel h
    rw [← one_add_one_eq_two]
    exact eq_neg_iff_add_eq_zero.mp h1
  · exact one_ne_zero (add_eq_left.mp h)

/-- a corner is off every non-incident edge (`tail_off`) -/
theorem E_corner_notMem_edge (gen : (Shadow.single C).Generic) {i j : ZMod C.k}
    (h : ¬ incident i j) : C.P i ∉ edgeSegment C.P j :=
  gen.tail_off ⟨0, i⟩ ⟨0, j⟩ (by rw [Shadow.incidentTail_mk_iff]; exact h)

/-- the corners of a generic polygon are distinct -/
theorem E_corner_injective (gen : (Shadow.single C).Generic) : Function.Injective C.P := by
  intro i j hij
  by_contra hne
  by_cases hji : i = j + 1
  · apply E_edge_ne_zero gen j
    rw [edge, ← hji, hij, sub_self]
  · have hinc : ¬ incident i j := by
      rintro (h | h)
      · exact hji (by rw [h, sub_add_cancel])
      · exact hne h.symm
    apply E_corner_notMem_edge gen hinc
    exact ⟨0, le_rfl, zero_le_one, by rw [hij, edgePoint_zero]⟩

/-- a double point of the polygon is not a corner -/
theorem E_crossingPoint_ne_corner (gen : (Shadow.single C).Generic)
    (x : (Shadow.single C).Crossing) (i : ZMod C.k) :
    (Shadow.single C).crossingPoint x ≠ C.P i := by
  intro heq
  obtain ⟨s, t, hx, -, -⟩ := x.2
  have hs : s ∈ x.val := by rw [hx]; exact Finset.mem_insert_self _ _
  obtain ⟨c, j⟩ := s
  obtain rfl : c = 0 := Subsingleton.elim c 0
  obtain ⟨r, hr0, hr1, hr⟩ := gen.crossingPoint_mem_interior x hs
  have hr' : C.P i = edgePoint C.P j r := heq ▸ hr
  by_cases hinc : incident i j
  · rcases hinc with h | h
    · -- `j = i - 1`: the corner is the head of edge `j`
      subst h
      have h1 : edgePoint C.P (i - 1) 1 = edgePoint C.P (i - 1) r := by
        rw [edgePoint_one, sub_add_cancel]; exact hr'
      exact hr1.ne' (edgePoint_injective (E_edge_ne_zero gen _) h1)
    · -- `j = i`: the corner is the tail of edge `j`
      subst h
      have h1 : edgePoint C.P j 0 = edgePoint C.P j r := by
        rw [edgePoint_zero]; exact hr'
      exact hr0.ne (edgePoint_injective (E_edge_ne_zero gen _) h1)
  · exact E_corner_notMem_edge gen hinc ⟨r, hr0.le, hr1.le, hr'⟩

/-- closed edge segments are compact -/
theorem E_edgeSegment_isCompact {n : ℕ} (P : LabelledTuple n) (j : ZMod n) :
    IsCompact (edgeSegment P j) := by
  have : edgeSegment P j = edgePoint P j '' Set.Icc 0 1 := by
    ext p
    constructor
    · rintro ⟨t, h0, h1, rfl⟩
      exact ⟨t, ⟨h0, h1⟩, rfl⟩
    · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
      exact ⟨t, h0, h1, rfl⟩
  rw [this]
  exact isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))

theorem E_ηv_pos (gen : (Shadow.single C).Generic) : 0 < ηv C := by
  rw [ηv, Finset.lt_inf'_iff]
  intro i _
  apply E_far_pos
  · exact ((Set.finite_range C.P).subset
      (fun p hp => by obtain ⟨j, -, hp⟩ := hp; exact ⟨j, hp.symm⟩)).isCompact
  · obtain ⟨j, hj⟩ := exists_ne i
    exact ⟨C.P j, j, hj, rfl⟩
  · rintro ⟨j, hj, hp⟩
    exact hj (E_corner_injective gen hp).symm

theorem E_ηe_pos (gen : (Shadow.single C).Generic) : 0 < ηe C := by
  rw [ηe, Finset.lt_inf'_iff]
  intro i _
  apply E_far_pos
  · exact (Set.toFinite _).isCompact_biUnion (fun j _ => E_edgeSegment_isCompact C.P j)
  · exact ⟨C.P (i + 1), Set.mem_biUnion (x := i + 1) (E_not_incident_succ i)
      ⟨0, le_rfl, zero_le_one, by rw [edgePoint_zero]⟩⟩
  · intro hmem
    rw [nonIncidentEdges, Set.mem_iUnion₂] at hmem
    obtain ⟨j, hj, hmem⟩ := hmem
    exact E_corner_notMem_edge gen hj hmem

theorem E_ηℓ_pos (gen : (Shadow.single C).Generic) : 0 < ηℓ C := by
  rw [ηℓ, Finset.lt_inf'_iff]
  intro i _
  exact euclideanLength_pos (E_edge_ne_zero gen i)

theorem E_crossingPts_isCompact : IsCompact (crossingPts C) :=
  ((Set.finite_range (Shadow.single C).crossingPoint).subset
    (fun p hp => by obtain ⟨x, hp⟩ := hp; exact ⟨x, hp.symm⟩)).isCompact

theorem E_ηX_pos (gen : (Shadow.single C).Generic) : 0 < ηX C := by
  by_cases hne : Nonempty (Shadow.single C).Crossing
  · rw [ηX, ite_eq_left hne, Finset.lt_inf'_iff]
    intro i _
    apply E_far_pos _ E_crossingPts_isCompact
    · obtain ⟨x⟩ := hne
      exact ⟨_, x, rfl⟩
    · rintro ⟨x, hx⟩
      exact E_crossingPoint_ne_corner gen x i hx.symm
  · rw [ηX, ite_eq_right hne]
    exact E_ηℓ_pos gen

theorem clearance_pos (gen : (Shadow.single C).Generic) : 0 < clearance C := by
  unfold clearance
  exact mul_pos (by norm_num)
    (lt_min (lt_min (E_ηv_pos gen) (E_ηe_pos gen)) (lt_min (E_ηℓ_pos gen) (E_ηX_pos gen)))

/-- `3 ε₀(L) ≤ η_v, η_e, η_ℓ, η_X` -/
theorem E_three_mul_clearance_le :
    3 * clearance C ≤ ηv C ∧ 3 * clearance C ≤ ηe C ∧ 3 * clearance C ≤ ηℓ C ∧
      3 * clearance C ≤ ηX C := by
  unfold clearance
  have h1 := min_le_left (min (ηv C) (ηe C)) (min (ηℓ C) (ηX C))
  have h2 := min_le_right (min (ηv C) (ηe C)) (min (ηℓ C) (ηX C))
  have h3 := min_le_left (ηv C) (ηe C)
  have h4 := min_le_right (ηv C) (ηe C)
  have h5 := min_le_left (ηℓ C) (ηX C)
  have h6 := min_le_right (ηℓ C) (ηX C)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- the disc is the `planeComplex`-preimage of a closed Euclidean ball -/
theorem E_cornerDisc_eq_preimage (i : ZMod C.k) :
    cornerDisc C ε i = planeComplex ⁻¹' Metric.closedBall (planeComplex (C.P i)) ε := by
  ext p
  simp only [cornerDisc, Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, E_eucDist_eq]

theorem E_cornerDisc_convex (i : ZMod C.k) : Convex ℝ (cornerDisc C ε i) := by
  rw [E_cornerDisc_eq_preimage]
  exact (convex_closedBall _ _).is_linear_preimage ⟨E_planeComplex_add, planeComplex_smul⟩

theorem E_cornerDisc_isClosed (i : ZMod C.k) : IsClosed (cornerDisc C ε i) :=
  isClosed_le (E_continuous_eucDist _) continuous_const

theorem E_cornerDisc_subset_closedBall (i : ZMod C.k) :
    cornerDisc C ε i ⊆ Metric.closedBall (C.P i) ε := by
  intro p hp
  rw [Metric.mem_closedBall]
  exact (E_dist_le_eucDist p _).trans hp

theorem E_mem_interior_cornerDisc (hε : 0 < ε) (i : ZMod C.k) :
    C.P i ∈ interior (cornerDisc C ε i) := by
  rw [mem_interior_iff_mem_nhds]
  refine Filter.mem_of_superset (Metric.ball_mem_nhds _ (half_pos hε)) ?_
  intro p hp
  rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff] at hp
  show eucDist p (C.P i) ≤ ε
  have := E_eucDist_le_add p (C.P i)
  linarith [hp.1, hp.2]

theorem cornerDisc_isDisc (hε : 0 < ε) (i : ZMod C.k) : IsDisc (cornerDisc C ε i) := by
  exact ⟨E_cornerDisc_convex i,
    Metric.isCompact_of_isClosed_isBounded (E_cornerDisc_isClosed i)
      (Metric.isBounded_closedBall.subset (E_cornerDisc_subset_closedBall i)),
    ⟨C.P i, E_mem_interior_cornerDisc hε i⟩⟩

theorem mem_interior_cornerDisc (hε : 0 < ε) (i : ZMod C.k) : C.P i ∈ interior (cornerDisc C ε i) := by
  exact E_mem_interior_cornerDisc hε i

theorem cornerDisc_disjoint (h : Admissible C D ε) {i j : ZMod C.k} (hij : i ≠ j) :
    Disjoint (cornerDisc C ε i) (cornerDisc C ε j) := by
  rw [Set.disjoint_left]
  intro p hpi hpj
  have hpi' : eucDist p (C.P i) ≤ ε := hpi
  have hpj' : eucDist p (C.P j) ≤ ε := hpj
  have h1 : ηv C ≤ far (C.P i) (otherCorners C i) := by
    unfold ηv; exact Finset.inf'_le _ (Finset.mem_univ i)
  have h2 : far (C.P i) (otherCorners C i) ≤ eucDist (C.P i) (C.P j) :=
    E_far_le _ _ ⟨j, hij.symm, rfl⟩
  have h3 := E_eucDist_triangle (C.P i) p (C.P j)
  rw [E_eucDist_comm (C.P i) p] at h3
  have h4 := (E_three_mul_clearance_le (C := C)).1
  have h5 := h.ε_lt
  have h6 := h.ε_pos
  linarith

theorem cornerDisc_disjoint_edge (h : Admissible C D ε) {i j : ZMod C.k} (hij : ¬ incident i j) :
    Disjoint (cornerDisc C ε i) (edgeSegment C.P j) := by
  rw [Set.disjoint_left]
  intro p hpi hpj
  have hpi' : eucDist p (C.P i) ≤ ε := hpi
  have h1 : ηe C ≤ far (C.P i) (nonIncidentEdges C i) := by
    unfold ηe; exact Finset.inf'_le _ (Finset.mem_univ i)
  have h2 : far (C.P i) (nonIncidentEdges C i) ≤ eucDist (C.P i) p :=
    E_far_le _ _ (Set.mem_biUnion (x := j) hij hpj)
  rw [E_eucDist_comm] at h2
  have h4 := (E_three_mul_clearance_le (C := C)).2.1
  have h5 := h.ε_lt
  have h6 := h.ε_pos
  linarith

/-- `η_X ≤ |x − q_i|` for every double point `x` -/
theorem E_ηX_le (i : ZMod C.k) (x : (Shadow.single C).Crossing) :
    ηX C ≤ eucDist ((Shadow.single C).crossingPoint x) (C.P i) := by
  rw [ηX, ite_eq_left ⟨x⟩, E_eucDist_comm]
  exact (Finset.inf'_le _ (Finset.mem_univ i)).trans (E_far_le _ _ ⟨x, rfl⟩)

theorem E_three_mul_lt_dist_crossing (h : Admissible C D ε) (i : ZMod C.k)
    (x : (Shadow.single C).Crossing) :
    3 * ε < eucDist ((Shadow.single C).crossingPoint x) (C.P i) := by
  have h1 := E_ηX_le i x
  have h4 := (E_three_mul_clearance_le (C := C)).2.2.2
  have h5 := h.ε_lt
  linarith

theorem crossingPoint_notMem_cornerDisc (h : Admissible C D ε) (i : ZMod C.k)
    (x : D.toDiagram.Γ.Crossing) : D.toDiagram.Γ.crossingPoint x ∉ cornerDisc C ε i := by
  intro hmem
  have hmem' : eucDist (D.toDiagram.Γ.crossingPoint x) (C.P i) ≤ ε := hmem
  have h1 := E_three_mul_lt_dist_crossing h i x
  have h2 := h.ε_pos
  linarith

/-- `ε ≤ |δ_i|` at an admissible `ε` -/
theorem E_ε_le_edgeLength (h : Admissible C D ε) (i : ZMod C.k) :
    ε ≤ euclideanLength (edge C.P i) := by
  have h1 : ηℓ C ≤ euclideanLength (edge C.P i) := by
    unfold ηℓ; exact Finset.inf'_le _ (Finset.mem_univ i)
  have h4 := (E_three_mul_clearance_le (C := C)).2.2.1
  have h5 := h.ε_lt
  have h6 := h.ε_pos
  linarith

theorem cornerDisc_inter_edge_out (h : Admissible C D ε) (i : ZMod C.k) :
    cornerDisc C ε i ∩ edgeSegment C.P i = subsegOut C ε i := by
  have hne : edge C.P i ≠ 0 := E_edge_ne_zero D.generic i
  have hlen : 0 < euclideanLength (edge C.P i) := euclideanLength_pos hne
  have hεlen := E_ε_le_edgeLength h i
  ext p
  constructor
  · rintro ⟨hp, t, ht0, ht1, rfl⟩
    have hp' : eucDist (edgePoint C.P i t) (C.P i) ≤ ε := hp
    rw [edgePoint, E_eucDist_add_left, euclideanLength_smul, abs_of_nonneg ht0] at hp'
    refine ⟨t * euclideanLength (edge C.P i), mul_nonneg ht0 hlen.le, hp', ?_⟩
    rw [edgePoint, normalize, smul_smul, mul_assoc, mul_inv_cancel₀ hlen.ne', mul_one]
  · rintro ⟨r, hr0, hrε, rfl⟩
    refine ⟨?_, r / euclideanLength (edge C.P i), div_nonneg hr0 hlen.le, ?_, ?_⟩
    · show eucDist (C.P i + r • normalize (edge C.P i)) (C.P i) ≤ ε
      rw [E_eucDist_add_left, euclideanLength_smul, abs_of_nonneg hr0,
        euclideanLength_normalize hne, mul_one]
      exact hrε
    · rw [div_le_one hlen]
      exact hrε.trans hεlen
    · rw [edgePoint, normalize, smul_smul, div_eq_mul_inv]

theorem cornerDisc_inter_edge_in (h : Admissible C D ε) (i : ZMod C.k) :
    cornerDisc C ε i ∩ edgeSegment C.P (i - 1) = subsegIn C ε i := by
  have hne : edge C.P (i - 1) ≠ 0 := E_edge_ne_zero D.generic (i - 1)
  have hlen : 0 < euclideanLength (edge C.P (i - 1)) := euclideanLength_pos hne
  have hεlen := E_ε_le_edgeLength h (i - 1)
  -- the incoming edge, parametrised from its head `q_i`
  have hpt : ∀ t : ℝ, edgePoint C.P (i - 1) t = C.P i - (1 - t) • edge C.P (i - 1) := by
    intro t
    have he : edge C.P (i - 1) = C.P i - C.P (i - 1) := by rw [edge, sub_add_cancel]
    rw [edgePoint, he]
    module
  ext p
  constructor
  · rintro ⟨hp, t, ht0, ht1, rfl⟩
    have hp' : eucDist (edgePoint C.P (i - 1) t) (C.P i) ≤ ε := hp
    rw [hpt, E_eucDist_sub_left, euclideanLength_smul, abs_of_nonneg (by linarith)] at hp'
    refine ⟨(1 - t) * euclideanLength (edge C.P (i - 1)), mul_nonneg (by linarith) hlen.le, hp', ?_⟩
    rw [hpt, normalize, smul_smul, mul_assoc, mul_inv_cancel₀ hlen.ne', mul_one]
  · rintro ⟨r, hr0, hrε, rfl⟩
    refine ⟨?_, 1 - r / euclideanLength (edge C.P (i - 1)), ?_, ?_, ?_⟩
    · show eucDist (C.P i - r • normalize (edge C.P (i - 1))) (C.P i) ≤ ε
      rw [E_eucDist_sub_left, euclideanLength_smul, abs_of_nonneg hr0,
        euclideanLength_normalize hne, mul_one]
      exact hrε
    · rw [sub_nonneg, div_le_one hlen]
      exact hrε.trans hεlen
    · linarith [div_nonneg hr0 hlen.le]
    · rw [hpt, sub_sub_cancel, normalize, smul_smul, div_eq_mul_inv]

/-- a double point is more than `3ε` from every corner -/
theorem three_mul_lt_dist_crossing (h : Admissible C D ε) (i : ZMod C.k)
    (x : D.toDiagram.Γ.Crossing) : 3 * ε < eucDist (D.toDiagram.Γ.crossingPoint x) (C.P i) := by
  exact E_three_mul_lt_dist_crossing h i x

end discs

/-! ### Unit X — double points of the rounded curve and the carried diagram (sm-3:3847-3860) -/

section doubles

variable {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (h : Admissible C D ε)
include h

/-! #### Unit X helpers: vectors, the subdivision, the straight parts as edge points -/

omit h in
theorem X_smul_normalize {v : Plane} (hv : v ≠ 0) : euclideanLength v • normalize v = v := by
  unfold normalize
  rw [smul_smul, mul_inv_cancel₀ (euclideanLength_pos hv).ne', one_smul]

omit h in
theorem X_det_smul_smul (r r' : ℝ) (u w : Plane) : det (r • u) (r' • w) = (r * r') * det u w := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

omit h in
theorem X_eucDist_add_smul_normalize (p : Plane) (r : ℝ) {v : Plane} (hv : v ≠ 0) :
    eucDist (p + r • normalize v) p = |r| := by
  rw [eucDist, add_sub_cancel_left, euclideanLength_smul, euclideanLength_normalize hv, mul_one]

omit h in
theorem X_eucDist_self (p : Plane) : eucDist p p = 0 := by
  rw [eucDist, sub_self]
  simp [euclideanLength, planeComplex_zero]

omit h in
theorem X_edgePoint_eq_add_smul_normalize (i : ZMod C.k) (r : ℝ) :
    edgePoint C.P i (r / euclideanLength (edge C.P i)) = C.P i + r • normalize (edge C.P i) := by
  unfold edgePoint normalize
  rw [div_eq_mul_inv, mul_smul]

omit h in
theorem X_edge_ne_zero (hreg : Regular C.P) (i : ZMod C.k) : edge C.P i ≠ 0 := (hreg i).2.1

omit h in
theorem X_P_succ (i : ZMod C.k) : C.P (i + 1) = C.P i + edge C.P i := by
  rw [edge, add_sub_cancel]

omit h in
/-- the two vertices of edge `i` are at Euclidean distances `s|δ_i|` and `(1−s)|δ_i|` from
`edgePoint i s` -/
theorem X_eucDist_edgePoint (i : ZMod C.k) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    eucDist (edgePoint C.P i s) (C.P i) = s * euclideanLength (edge C.P i) ∧
    eucDist (edgePoint C.P i s) (C.P (i + 1)) = (1 - s) * euclideanLength (edge C.P i) := by
  constructor
  · rw [edgePoint, eucDist, add_sub_cancel_left, euclideanLength_smul, abs_of_nonneg hs0]
  · have e : s • edge C.P i - edge C.P i = (s - 1) • edge C.P i := by rw [sub_smul, one_smul]
    rw [edgePoint, X_P_succ, eucDist, add_sub_add_left_eq_sub, e, euclideanLength_smul,
      abs_of_nonpos (by linarith), neg_sub]

omit h in
theorem X_A0_add_smul_dirOf (hreg : Regular C.P) (j : ℕ) :
    A0 C ε j + ε • dirOf (θu C j) = C.P j := by
  rw [dirOf_θu hreg j, A0, sub_add_cancel]

omit h in
theorem X_a_succ_sub_b (j : ℕ) : a C ε (j + 1) - b C ε j = str C ε j / Λ C ε := by
  simp only [a, b, Finset.sum_range_succ, add_div]
  ring

theorem X_str_pos (j : ℕ) : 0 < str C ε j := by
  unfold str
  linarith [three_mul_lt_edgeLength h (j : ZMod C.k), h.ε_pos]

theorem X_a_mono {i j : ℕ} (hij : i ≤ j) : a C ε i ≤ a C ε j := by
  unfold a
  apply div_le_div_of_nonneg_right _ (Λ_pos h).le
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
    (fun m _ _ => (add_pos (ℓ_pos h m) (X_str_pos h m)).le)

theorem X_a_nonneg (j : ℕ) : 0 ≤ a C ε j := by
  have := X_a_mono h (Nat.zero_le j)
  rwa [a_zero] at this

theorem X_a_le_one {j : ℕ} (hj : j ≤ C.k) : a C ε j ≤ 1 := by
  have := X_a_mono h hj
  rwa [a_last h] at this

/-- the straight part along edge `j`: `q_j + (ε + Λ(t − b j)) · δ_j/|δ_j|` -/
theorem X_curveMap_straight {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (b C ε j) (a C ε (j + 1))) :
    curveMap C ε t = C.P j + (ε + Λ C ε * (t - b C ε j)) • normalize (edge C.P j) := by
  rw [curveMap_on_straight h hj ht, A1, vDir, add_assoc, ← add_smul]

/-- on the closed straight part the distance from `q_j` is between `ε` and `|δ_j| − ε` -/
theorem X_straight_dist_bounds {j : ℕ} {t : ℝ}
    (ht : t ∈ Icc (b C ε j) (a C ε (j + 1))) :
    ε ≤ ε + Λ C ε * (t - b C ε j) ∧
      ε + Λ C ε * (t - b C ε j) ≤ euclideanLength (edge C.P j) - ε := by
  have hΛ := Λ_pos h
  have h1 : 0 ≤ Λ C ε * (t - b C ε j) := mul_nonneg hΛ.le (sub_nonneg.mpr ht.1)
  have h2 : Λ C ε * (t - b C ε j) ≤ str C ε j := by
    have := X_a_succ_sub_b (C := C) (ε := ε) j
    have h3 : t - b C ε j ≤ str C ε j / Λ C ε := by linarith [ht.2]
    calc Λ C ε * (t - b C ε j) ≤ Λ C ε * (str C ε j / Λ C ε) := by gcongr
      _ = str C ε j := mul_div_cancel₀ _ hΛ.ne'
  unfold str at h2
  constructor <;> linarith

/-- on the open straight part the bounds are strict -/
theorem X_straight_dist_bounds_strict {j : ℕ} {t : ℝ}
    (ht : t ∈ Ioo (b C ε j) (a C ε (j + 1))) :
    ε < ε + Λ C ε * (t - b C ε j) ∧
      ε + Λ C ε * (t - b C ε j) < euclideanLength (edge C.P j) - ε := by
  have hΛ := Λ_pos h
  have h1 : 0 < Λ C ε * (t - b C ε j) := mul_pos hΛ (sub_pos.mpr ht.1)
  have h2 : Λ C ε * (t - b C ε j) < str C ε j := by
    have := X_a_succ_sub_b (C := C) (ε := ε) j
    have h3 : t - b C ε j < str C ε j / Λ C ε := by linarith [ht.2]
    calc Λ C ε * (t - b C ε j) < Λ C ε * (str C ε j / Λ C ε) := by gcongr
      _ = str C ε j := mul_div_cancel₀ _ hΛ.ne'
  unfold str at h2
  constructor <;> linarith

/-- the straight part lies on the closed edge segment -/
theorem X_curveMap_straight_mem_edgeSegment {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (b C ε j) (a C ε (j + 1))) : curveMap C ε t ∈ edgeSegment C.P j := by
  have hv := X_edge_ne_zero D.regular (j : ZMod C.k)
  have hlen := euclideanLength_pos hv
  obtain ⟨h1, h2⟩ := X_straight_dist_bounds h ht
  refine ⟨(ε + Λ C ε * (t - b C ε j)) / euclideanLength (edge C.P j), ?_, ?_, ?_⟩
  · exact div_nonneg (by linarith [h.ε_pos]) hlen.le
  · rw [div_le_one hlen]
    linarith [h.ε_pos]
  · rw [X_edgePoint_eq_add_smul_normalize, X_curveMap_straight h hj ht]

/-- the distance of a straight-part point from its edge's tail -/
theorem X_eucDist_straight {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (b C ε j) (a C ε (j + 1))) :
    eucDist (curveMap C ε t) (C.P j) = ε + Λ C ε * (t - b C ε j) := by
  have hv := X_edge_ne_zero D.regular (j : ZMod C.k)
  rw [X_curveMap_straight h hj ht, X_eucDist_add_smul_normalize _ _ hv,
    abs_of_pos (by linarith [(X_straight_dist_bounds h ht).1, h.ε_pos])]

/-! #### Unit X helpers: the junction arcs -/

/-- the profile argument of a junction parameter lies in `[0,1]` -/
theorem X_junction_param_mem {j : ℕ} {t : ℝ} (ht : t ∈ Icc (a C ε j) (b C ε j)) :
    (t - a C ε j) * Λ C ε / ℓ C ε j ∈ Icc (0 : ℝ) 1 := by
  have hℓ := ℓ_pos h j
  have hΛ := Λ_pos h
  constructor
  · exact div_nonneg (mul_nonneg (sub_nonneg.mpr ht.1) hΛ.le) hℓ.le
  · rw [div_le_one hℓ]
    have h1 : t - a C ε j ≤ ℓ C ε j / Λ C ε := by
      have := b_sub_a (C := C) (ε := ε) j
      linarith [ht.2]
    calc (t - a C ε j) * Λ C ε ≤ (ℓ C ε j / Λ C ε) * Λ C ε := by gcongr
      _ = ℓ C ε j := div_mul_cancel₀ _ hΛ.ne'

/-- the junction at corner `j` is embedded (`juncArc_injOn` through the affine substitution) -/
theorem X_junction_injOn {j : ℕ} (hj : j < C.k) : InjOn (curveMap C ε) (Icc (a C ε j) (b C ε j)) := by
  intro s hs t ht hst
  have hℓ := ℓ_pos h j
  have hΛ := Λ_pos h
  have hst' : juncArc (A0 C ε j) ε (θu C j) (turn C j) ((s - a C ε j) * Λ C ε / ℓ C ε j) =
      juncArc (A0 C ε j) ε (θu C j) (turn C j) ((t - a C ε j) * Λ C ε / ℓ C ε j) := by
    rw [← curveMap_on_junction h hj hs, ← curveMap_on_junction h hj ht]
    exact hst
  have heq := juncArc_injOn h.ε_pos (turn_bounds h j).1 (turn_bounds h j).2
    (X_junction_param_mem h hs) (X_junction_param_mem h ht) hst'
  rw [div_eq_div_iff hℓ.ne' hℓ.ne'] at heq
  have h2 := mul_right_cancel₀ hℓ.ne' heq
  have h3 := mul_right_cancel₀ hΛ.ne' h2
  linarith

theorem curveMap_junction_mem_disc {j : ℕ} (hj : j < C.k) {t : ℝ} (ht : t ∈ Icc (a C ε j) (b C ε j)) :
    curveMap C ε t ∈ cornerDisc C ε j := by
  have hs := X_junction_param_mem h ht
  rw [curveMap_on_junction h hj ht]
  have := juncArc_mem_disc (A0 := A0 C ε j) (θu := θu C j) h.ε_pos (turn_bounds h j).1
    (turn_bounds h j).2 hs
  rw [X_A0_add_smul_dirOf D.regular j] at this
  exact this

theorem curveMap_straight_notMem_discs {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Ioo (b C ε j) (a C ε (j + 1))) : curveMap C ε t ∉ ⋃ i, cornerDisc C ε i := by
  intro hmem
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  have hv := X_edge_ne_zero D.regular (j : ZMod C.k)
  have ht' : t ∈ Icc (b C ε j) (a C ε (j + 1)) := ⟨ht.1.le, ht.2.le⟩
  obtain ⟨h1, h2⟩ := X_straight_dist_bounds_strict h ht
  by_cases hinc : incident i (j : ZMod C.k)
  · rcases hinc with hji | hji
    · -- `i = j + 1`: the distance from the head of the edge is `|δ_j| − r > ε`
      have hi' : i = (j : ZMod C.k) + 1 := by rw [hji]; ring
      rw [hi'] at hi
      have hP := X_P_succ (C := C) (j : ZMod C.k)
      have hd : eucDist (curveMap C ε t) (C.P ((j : ZMod C.k) + 1)) =
          euclideanLength (edge C.P j) - (ε + Λ C ε * (t - b C ε j)) := by
        have e : (ε + Λ C ε * (t - b C ε j)) • normalize (edge C.P j) - edge C.P j =
            (ε + Λ C ε * (t - b C ε j) - euclideanLength (edge C.P j)) • normalize (edge C.P j) := by
          rw [sub_smul, X_smul_normalize hv]
        rw [X_curveMap_straight h hj ht', hP, eucDist, add_sub_add_left_eq_sub, e,
          euclideanLength_smul, euclideanLength_normalize hv, mul_one, abs_of_neg (by linarith [h.ε_pos]),
          neg_sub]
      have hle : eucDist (curveMap C ε t) (C.P ((j : ZMod C.k) + 1)) ≤ ε := hi
      linarith
    · -- `i = j`: the distance from the tail is `r > ε`
      rw [← hji] at hi
      have hle : eucDist (curveMap C ε t) (C.P j) ≤ ε := hi
      rw [X_eucDist_straight h hj ht'] at hle
      linarith
  · exact Set.disjoint_left.mp (cornerDisc_disjoint_edge h hinc) hi
      (X_curveMap_straight_mem_edgeSegment h hj ht')

/-- the fundamental period is covered by the closed junction intervals and the open straight
intervals (the leaf `cover`, needed already here) -/
theorem X_cover {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    (∃ j < C.k, t ∈ Icc (a C ε j) (b C ε j)) ∨ ∃ j < C.k, t ∈ Ioo (b C ε j) (a C ε (j + 1)) := by
  have hex : ∃ n, t < a C ε n := ⟨C.k, by rw [a_last h]; exact ht.2⟩
  have hm : t < a C ε (Nat.find hex) := Nat.find_spec hex
  have hmk : Nat.find hex ≤ C.k := Nat.find_min' hex (by rw [a_last h]; exact ht.2)
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, a_zero] at hm
    exact absurd hm (not_lt.mpr ht.1)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hjk : j < C.k := by omega
  have haj : a C ε j ≤ t := not_lt.mp (Nat.find_min hex (by omega))
  rw [hj] at hm
  by_cases htb : t ≤ b C ε j
  · exact Or.inl ⟨j, hjk, haj, htb⟩
  · exact Or.inr ⟨j, hjk, not_le.mp htb, hm⟩

/-- (a): outside the discs the rounded curve and the polygon have the same points -/
theorem range_curveMap_outside {p : Plane} (hp : p ∉ ⋃ i, cornerDisc C ε i) :
    p ∈ range (curveMap C ε) ↔ p ∈ polygonImage C := by
  have hp' : ∀ i, ε < eucDist p (C.P i) :=
    fun i => not_le.mp (fun hle => hp (Set.mem_iUnion.mpr ⟨i, hle⟩))
  constructor
  · rintro ⟨t, rfl⟩
    have hfr : curveMap C ε (Int.fract t) = curveMap C ε t := by
      rw [← Int.self_sub_floor, ← mul_one ((⌊t⌋ : ℤ) : ℝ)]
      exact (curveMap_periodic h).sub_int_mul_eq ⌊t⌋
    rw [← hfr] at hp' ⊢
    rcases X_cover h ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩ with ⟨j, hj, hj'⟩ | ⟨j, hj, hj'⟩
    · exact absurd (curveMap_junction_mem_disc h hj hj') (not_le.mpr (hp' j))
    · exact Set.mem_iUnion.mpr
        ⟨j, X_curveMap_straight_mem_edgeSegment h hj ⟨hj'.1.le, hj'.2.le⟩⟩
  · intro hmem
    obtain ⟨i, s, hs0, hs1, hps⟩ := Set.mem_iUnion.mp hmem
    have hv := X_edge_ne_zero D.regular i
    have hlen := euclideanLength_pos hv
    obtain ⟨hd1, hd2⟩ := X_eucDist_edgePoint (C := C) i hs0 hs1
    have h1 := hp' i
    have h2 := hp' (i + 1)
    rw [hps, hd1] at h1
    rw [hps, hd2] at h2
    have hjk : i.val < C.k := ZMod.val_lt i
    have hji : ((i.val : ℕ) : ZMod C.k) = i := ZMod.natCast_zmod_val i
    have hΛ := Λ_pos h
    have hstr : str C ε i.val = euclideanLength (edge C.P i) - 2 * ε := by rw [str, hji]
    have hab := X_a_succ_sub_b (C := C) (ε := ε) i.val
    refine ⟨b C ε i.val + (s * euclideanLength (edge C.P i) - ε) / Λ C ε, ?_⟩
    have ht : b C ε i.val + (s * euclideanLength (edge C.P i) - ε) / Λ C ε ∈
        Icc (b C ε i.val) (a C ε (i.val + 1)) := by
      constructor
      · linarith [div_nonneg (by linarith : 0 ≤ s * euclideanLength (edge C.P i) - ε) hΛ.le]
      · have : (s * euclideanLength (edge C.P i) - ε) / Λ C ε ≤ str C ε i.val / Λ C ε := by
          apply div_le_div_of_nonneg_right _ hΛ.le
          rw [hstr]
          linarith
        linarith
    rw [X_curveMap_straight h hjk ht, hps, edgePoint, hji]
    congr 1
    have : ε + Λ C ε * (b C ε i.val + (s * euclideanLength (edge C.P i) - ε) / Λ C ε - b C ε i.val) =
        s * euclideanLength (edge C.P i) := by
      rw [add_sub_cancel_left, mul_div_cancel₀ _ hΛ.ne']
      ring
    rw [this, mul_smul, X_smul_normalize hv]

/-! #### Unit X helpers: the occurrences -/

omit h in
/-- the crossing point of an occurrence, as a point of its strand's edge -/
theorem X_crossingPoint_eq (v : D.toDiagram.Γ.Visit) :
    D.toDiagram.Γ.crossingPoint v.1 =
      edgePoint C.P (D.label v) (D.toDiagram.crossingParam v.1 v.2.2) :=
  (D.toDiagram.crossingParam_spec v.1 v.2.2).2.2

omit h in
/-- the accepted traversal coordinate of an occurrence: edge label plus crossing parameter -/
theorem X_visitCoord_eq (v : D.toDiagram.Γ.Visit) :
    D.toDiagram.visitCoord v = ((D.label v).val : ℝ) + D.toDiagram.crossingParam v.1 v.2.2 := rfl

omit h in
theorem X_label_val_lt (v : D.toDiagram.Γ.Visit) : (D.label v).val < C.k := ZMod.val_lt _

omit h in
theorem X_label_cast (v : D.toDiagram.Γ.Visit) : (((D.label v).val : ℕ) : ZMod C.k) = D.label v :=
  ZMod.natCast_zmod_val _

/-- the crossing point is more than `ε` (indeed `3ε`) from both ends of its edge: `ε < c|δ| < |δ| − ε` -/
theorem X_crossingParam_bounds (v : D.toDiagram.Γ.Visit) :
    ε < D.toDiagram.crossingParam v.1 v.2.2 * euclideanLength (edge C.P (D.label v)) ∧
      D.toDiagram.crossingParam v.1 v.2.2 * euclideanLength (edge C.P (D.label v)) <
        euclideanLength (edge C.P (D.label v)) - ε := by
  have hc0 : 0 ≤ D.toDiagram.crossingParam v.1 v.2.2 := (D.toDiagram.crossingParam_spec v.1 v.2.2).1
  have hc1 : D.toDiagram.crossingParam v.1 v.2.2 ≤ 1 := (D.toDiagram.crossingParam_spec v.1 v.2.2).2.1
  obtain ⟨hd1, hd2⟩ := X_eucDist_edgePoint (C := C) (D.label v) hc0 hc1
  have h1 := three_mul_lt_dist_crossing h (D.label v) v.1
  have h2 := three_mul_lt_dist_crossing h (D.label v + 1) v.1
  rw [X_crossingPoint_eq v, hd1] at h1
  rw [X_crossingPoint_eq v, hd2, sub_mul, one_mul] at h2
  constructor <;> linarith [h.ε_pos]

/-- the occurrence parameter lies strictly inside the straight part of its edge -/
theorem τ_mem_straight (v : D.toDiagram.Γ.Visit) :
    τ C ε D v ∈ Ioo (b C ε (D.label v).val) (a C ε ((D.label v).val + 1)) := by
  obtain ⟨h1, h2⟩ := X_crossingParam_bounds h v
  have hΛ := Λ_pos h
  have hstr : str C ε (D.label v).val = euclideanLength (edge C.P (D.label v)) - 2 * ε := by
    rw [str, X_label_cast]
  have hab := X_a_succ_sub_b (C := C) (ε := ε) (D.label v).val
  unfold τ
  constructor
  · have : 0 < (D.toDiagram.crossingParam v.1 v.2.2 * euclideanLength (edge C.P (D.label v)) - ε) /
        Λ C ε := div_pos (by linarith) hΛ
    linarith
  · have : (D.toDiagram.crossingParam v.1 v.2.2 * euclideanLength (edge C.P (D.label v)) - ε) /
        Λ C ε < str C ε (D.label v).val / Λ C ε :=
      div_lt_div_of_pos_right (by rw [hstr]; linarith) hΛ
    linarith

theorem τ_mem_Ico (v : D.toDiagram.Γ.Visit) : τ C ε D v ∈ Ico (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := τ_mem_straight h v
  have ha0 := X_a_nonneg h (D.label v).val
  have ha1 := X_a_le_one h (X_label_val_lt v)
  constructor
  · linarith [a_lt_b h (D.label v).val]
  · linarith

theorem curveMap_τ (v : D.toDiagram.Γ.Visit) :
    curveMap C ε (τ C ε D v) = D.toDiagram.Γ.crossingPoint v.1 := by
  have hmem := τ_mem_straight h v
  have hv := X_edge_ne_zero D.regular (D.label v)
  have hΛ := Λ_pos h
  rw [X_curveMap_straight h (X_label_val_lt v) ⟨hmem.1.le, hmem.2.le⟩, X_crossingPoint_eq v,
    X_label_cast, edgePoint]
  congr 1
  have : ε + Λ C ε * (τ C ε D v - b C ε (D.label v).val) =
      D.toDiagram.crossingParam v.1 v.2.2 * euclideanLength (edge C.P (D.label v)) := by
    unfold τ
    rw [add_sub_cancel_left, mul_div_cancel₀ _ hΛ.ne']
    ring
  rw [this, mul_smul, X_smul_normalize hv]

theorem deriv_curveMap_τ (v : D.toDiagram.Γ.Visit) :
    ∃ r : ℝ, 0 < r ∧ deriv (curveMap C ε) (τ C ε D v) = r • edge C.P (D.label v) := by
  have hmem := τ_mem_straight h v
  have hv := X_edge_ne_zero D.regular (D.label v)
  refine ⟨Λ C ε * (euclideanLength (edge C.P (D.label v)))⁻¹,
    mul_pos (Λ_pos h) (inv_pos.mpr (euclideanLength_pos hv)), ?_⟩
  rw [deriv_curveMap h, tangentField, Θ_on_straight h (X_label_val_lt v) ⟨hmem.1.le, hmem.2.le⟩,
    dirOf_θu D.regular, uDir_succ, vDir, X_label_cast, normalize, mul_smul]

omit h in
/-- two occurrences with the same crossing and the same edge label coincide -/
theorem X_visit_ext {v w : D.toDiagram.Γ.Visit} (h1 : v.1 = w.1) (h2 : D.label v = D.label w) :
    v = w := by
  obtain ⟨x, ⟨s, hs⟩⟩ := v
  obtain ⟨y, ⟨t, ht⟩⟩ := w
  change x = y at h1
  subst h1
  change s.2 = t.2 at h2
  have hst : s = t :=
    (Shadow.single_strand_eta C s).symm.trans
      ((congrArg (fun a : ZMod C.k => (⟨0, a⟩ : (Shadow.single C).Strand)) h2).trans
        (Shadow.single_strand_eta C t))
  subst hst
  rfl

/-- occurrences on different edges are traversed in the order of their edge labels -/
theorem X_τ_lt_of_label_lt {v w : D.toDiagram.Γ.Visit} (hlt : (D.label v).val < (D.label w).val) :
    τ C ε D v < τ C ε D w := by
  have hv := τ_mem_straight h v
  have hw := τ_mem_straight h w
  have := X_a_mono h (Nat.succ_le_of_lt hlt)
  linarith [hv.2, hw.1, a_lt_b h (D.label w).val]

/-- occurrences with the same edge label have the same `τ` only if they are the same occurrence -/
theorem X_τ_eq_of_label_eq {v w : D.toDiagram.Γ.Visit} (hlab : D.label v = D.label w)
    (hvw : τ C ε D v = τ C ε D w) : v = w := by
  have hΛ := Λ_pos h
  have hL := euclideanLength_pos (X_edge_ne_zero D.regular (D.label w))
  have hc : D.toDiagram.crossingParam v.1 v.2.2 = D.toDiagram.crossingParam w.1 w.2.2 := by
    unfold τ at hvw
    rw [hlab] at hvw
    have h1 := add_left_cancel hvw
    rw [div_left_inj' hΛ.ne', sub_left_inj, mul_left_inj' hL.ne'] at h1
    exact h1
  have hpt : D.toDiagram.Γ.crossingPoint v.1 = D.toDiagram.Γ.crossingPoint w.1 := by
    rw [X_crossingPoint_eq v, X_crossingPoint_eq w, hlab, hc]
  exact X_visit_ext (D.generic.crossingPoint_injective hpt) hlab

theorem τ_injective : Function.Injective (τ C ε D) := by
  intro v w hvw
  rcases lt_trichotomy (D.label v).val (D.label w).val with hlt | heq | hgt
  · exact absurd hvw (X_τ_lt_of_label_lt h hlt).ne
  · exact X_τ_eq_of_label_eq h (ZMod.val_injective _ heq) hvw
  · exact absurd hvw (X_τ_lt_of_label_lt h hgt).ne'

/-! #### Unit X helpers: the double points -/

omit h in
/-- consecutive edges of a regular polygon meet only at their common vertex (re-proof of
`regular_adjacent_meet`, SM/CS3.lean, which is not in the import closure of this file) -/
theorem X_regular_adjacent_meet (hQ : Regular C.P) (i : ZMod C.k) {x : Plane}
    (hx : x ∈ edgeSegment C.P i) (hx' : x ∈ edgeSegment C.P (i + 1)) : x = C.P (i + 1) := by
  obtain ⟨s, hs0, hs1, hs⟩ := hx
  obtain ⟨t, ht0, ht1, ht⟩ := hx'
  have hreg : RegularPair (edge C.P i) (edge C.P (i + 1)) := by
    have h := hQ (i + 1)
    rwa [add_sub_cancel_right] at h
  have h1 : C.P i + s • edge C.P i = C.P (i + 1) + t • edge C.P (i + 1) := hs.symm.trans ht
  by_cases hd : det (edge C.P i) (edge C.P (i + 1)) = 0
  · obtain ⟨c, hc, hce⟩ := (principalAngle_eq_zero_iff hreg.1 hreg.2.1).mp
      ((principalAngle_zero_iff_det_zero hreg).mpr hd)
    have hE : C.P (i + 1) = C.P i + edge C.P i := by simp [edge]
    have h3 : edgePoint C.P i s = edgePoint C.P i (1 + t * c) := by
      simp only [edgePoint]
      rw [h1, hce, hE, smul_smul, add_smul, one_smul, add_assoc]
    have hs' : s = 1 + t * c := edgePoint_injective hreg.1 h3
    have htc : t * c = 0 := by nlinarith [mul_nonneg ht0 hc.le]
    have ht0' : t = 0 := (mul_eq_zero.mp htc).resolve_right hc.ne'
    rw [ht, ht0', edgePoint_zero]
  · have h2 : C.P i + (1 : ℝ) • edge C.P i = C.P (i + 1) + (0 : ℝ) • edge C.P (i + 1) := by
      rw [one_smul, zero_smul, add_zero]
      simp only [edge]
      abel
    obtain ⟨rfl, -⟩ := intersection_parameters_unique hd h1 h2
    rw [hs, edgePoint_one]

theorem X_center_mem_cornerDisc (i : ZMod C.k) : C.P i ∈ cornerDisc C ε i := by
  show eucDist (C.P i) (C.P i) ≤ ε
  rw [X_eucDist_self]
  exact h.ε_pos.le

/-- two junction parameters with the same image coincide (one disc: embedded arc; two discs:
disjoint) -/
theorem X_junction_junction {i j : ℕ} (hi : i < C.k) {s : ℝ} (hsi : s ∈ Icc (a C ε i) (b C ε i))
    (hj : j < C.k) {t : ℝ} (htj : t ∈ Icc (a C ε j) (b C ε j))
    (he : curveMap C ε s = curveMap C ε t) : s = t := by
  by_cases hij : i = j
  · subst hij
    exact X_junction_injOn h hi hsi htj he
  · exfalso
    have hij' : (i : ZMod C.k) ≠ (j : ZMod C.k) := by
      intro heq
      apply hij
      have := congrArg ZMod.val heq
      rwa [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at this
    have h1 := curveMap_junction_mem_disc h hi hsi
    have h2 := curveMap_junction_mem_disc h hj htj
    rw [he] at h1
    exact Set.disjoint_left.mp (cornerDisc_disjoint h hij') h1 h2

/-- a point of the straight part along edge `j`, as an edge point with its parameter -/
theorem X_curveMap_straight_eq_edgePoint {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (b C ε j) (a C ε (j + 1))) :
    curveMap C ε t =
      edgePoint C.P j ((ε + Λ C ε * (t - b C ε j)) / euclideanLength (edge C.P j)) := by
  rw [X_edgePoint_eq_add_smul_normalize]
  exact X_curveMap_straight h hj ht

/-- two straight-part parameters on the same edge with the same image coincide -/
theorem X_straight_same_edge {i : ℕ} (hi : i < C.k) {s t : ℝ}
    (hsi : s ∈ Icc (b C ε i) (a C ε (i + 1))) (hti : t ∈ Icc (b C ε i) (a C ε (i + 1)))
    (he : curveMap C ε s = curveMap C ε t) : s = t := by
  have h1 := X_eucDist_straight h hi hsi
  have h2 := X_eucDist_straight h hi hti
  rw [he] at h1
  have h3 : Λ C ε * (s - b C ε i) = Λ C ε * (t - b C ε i) := by linarith
  have h4 := mul_left_cancel₀ (Λ_pos h).ne' h3
  linarith

/-- a common point of the open straight parts of two distinct edges is a crossing of `L`, traversed
at the two occurrence parameters -/
theorem X_straight_straight {i j : ℕ} (hi : i < C.k) {s : ℝ}
    (hsi : s ∈ Ioo (b C ε i) (a C ε (i + 1))) (hj : j < C.k) {t : ℝ}
    (htj : t ∈ Ioo (b C ε j) (a C ε (j + 1))) (hne : s ≠ t)
    (he : curveMap C ε s = curveMap C ε t) :
    ∃ v : D.toDiagram.Γ.Visit, s = τ C ε D v ∧ t = τ C ε D (D.toDiagram.twin v) := by
  have hΛ := Λ_pos h
  have hvi := X_edge_ne_zero D.regular (i : ZMod C.k)
  have hvj := X_edge_ne_zero D.regular (j : ZMod C.k)
  have hsi' : s ∈ Icc (b C ε i) (a C ε (i + 1)) := ⟨hsi.1.le, hsi.2.le⟩
  have htj' : t ∈ Icc (b C ε j) (a C ε (j + 1)) := ⟨htj.1.le, htj.2.le⟩
  have hps : curveMap C ε s ∈ edgeSegment C.P i := X_curveMap_straight_mem_edgeSegment h hi hsi'
  have hpt : curveMap C ε t ∈ edgeSegment C.P j := X_curveMap_straight_mem_edgeSegment h hj htj'
  have hnot : curveMap C ε s ∉ ⋃ m, cornerDisc C ε m := curveMap_straight_notMem_discs h hi hsi
  by_cases hij : i = j
  · subst hij
    exact absurd (X_straight_same_edge h hi hsi' htj' he) hne
  have hij' : (i : ZMod C.k) ≠ (j : ZMod C.k) := by
    intro heq
    apply hij
    have := congrArg ZMod.val heq
    rwa [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at this
  by_cases hadj : adjacent (i : ZMod C.k) (j : ZMod C.k)
  · -- consecutive edges meet only at the common vertex, which lies in its disc
    exfalso
    rcases hadj with h1 | h1 | h1
    · have hij1 : (i : ZMod C.k) = (j : ZMod C.k) + 1 := by linear_combination -h1
      have hps' : curveMap C ε s ∈ edgeSegment C.P ((j : ZMod C.k) + 1) := by
        rw [← hij1]; exact hps
      have hpt' : curveMap C ε s ∈ edgeSegment C.P j := by rw [he]; exact hpt
      have hx := X_regular_adjacent_meet D.regular (j : ZMod C.k) hpt' hps'
      exact hnot (Set.mem_iUnion.mpr ⟨_, by rw [hx]; exact X_center_mem_cornerDisc h _⟩)
    · exact hij' (sub_eq_zero.mp h1).symm
    · have hij1 : (j : ZMod C.k) = (i : ZMod C.k) + 1 := by linear_combination h1
      have hpt' : curveMap C ε s ∈ edgeSegment C.P ((i : ZMod C.k) + 1) := by
        rw [← hij1, he]; exact hpt
      have hx := X_regular_adjacent_meet D.regular (i : ZMod C.k) hps hpt'
      exact hnot (Set.mem_iUnion.mpr ⟨_, by rw [hx]; exact X_center_mem_cornerDisc h _⟩)
  · -- non-adjacent edges meeting: a crossing of the shadow `single C`
    let si : (Shadow.single C).Strand := ⟨0, (i : ZMod C.k)⟩
    let sj : (Shadow.single C).Strand := ⟨0, (j : ZMod C.k)⟩
    have hna : ¬ (Shadow.single C).Adjacent si sj :=
      fun hadj' => hadj ((Shadow.single_adjacent_iff C si sj).mp hadj')
    have hmeet : ((Shadow.single C).seg si ∩ (Shadow.single C).seg sj).Nonempty :=
      ⟨curveMap C ε s, hps, by rw [he]; exact hpt⟩
    let x : (Shadow.single C).Crossing := ⟨{si, sj}, (Shadow.single C).isCrossing_pair hna hmeet⟩
    have hsi_mem : si ∈ x.val := Finset.mem_insert_self _ _
    have hsj_mem : sj ∈ x.val := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hp : curveMap C ε s = (Shadow.single C).crossingPoint x := by
      apply D.generic.common_point_unique x
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hps
      · rw [Finset.mem_singleton.mp hu, he]
        exact hpt
    have hsj_ne : sj ≠ si := fun heq => hij' (congrArg (Shadow.singleStrandEquiv C) heq).symm
    have hother : (Shadow.single C).other x hsi_mem = sj :=
      ((Shadow.single C).eq_other_of_mem_of_ne x hsi_mem hsj_mem hsj_ne).symm
    let v : D.toDiagram.Γ.Visit := ⟨x, ⟨si, hsi_mem⟩⟩
    have hlab : D.label v = (i : ZMod C.k) := rfl
    have hlab2 : D.label (D.toDiagram.twin v) = (j : ZMod C.k) :=
      congrArg (Shadow.singleStrandEquiv C) hother
    -- the crossing parameters are the straight-part parameters
    have hcp : (Shadow.single C).crossingPoint x =
        edgePoint C.P i (D.toDiagram.crossingParam v.1 v.2.2) := X_crossingPoint_eq v
    have hcp2 : (Shadow.single C).crossingPoint x =
        edgePoint C.P j (D.toDiagram.crossingParam (D.toDiagram.twin v).1
          (D.toDiagram.twin v).2.2) := by
      have := X_crossingPoint_eq (D.toDiagram.twin v)
      rwa [hlab2] at this
    have hparam : D.toDiagram.crossingParam v.1 v.2.2 =
        (ε + Λ C ε * (s - b C ε i)) / euclideanLength (edge C.P i) := by
      apply edgePoint_injective hvi
      rw [← hcp, ← hp]
      exact X_curveMap_straight_eq_edgePoint h hi hsi'
    have hparam2 : D.toDiagram.crossingParam (D.toDiagram.twin v).1 (D.toDiagram.twin v).2.2 =
        (ε + Λ C ε * (t - b C ε j)) / euclideanLength (edge C.P j) := by
      apply edgePoint_injective hvj
      rw [← hcp2, ← hp, he]
      exact X_curveMap_straight_eq_edgePoint h hj htj'
    refine ⟨v, ?_, ?_⟩
    · unfold τ
      rw [hlab, ZMod.val_natCast_of_lt hi, hparam,
        div_mul_cancel₀ _ (euclideanLength_pos hvi).ne', add_sub_cancel_left,
        mul_div_cancel_left₀ _ hΛ.ne', add_sub_cancel]
    · unfold τ
      rw [hlab2, ZMod.val_natCast_of_lt hj, hparam2,
        div_mul_cancel₀ _ (euclideanLength_pos hvj).ne', add_sub_cancel_left,
        mul_div_cancel_left₀ _ hΛ.ne', add_sub_cancel]

/-- every double point of the rounded curve is a crossing of `L`, traversed at the two occurrence
parameters (the junctions are simple and meet nothing else; the straight parts are sub-segments of
the edges) -/
theorem doubles_curveMap {s t : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) (hne : s ≠ t)
    (he : curveMap C ε s = curveMap C ε t) :
    ∃ v : D.toDiagram.Γ.Visit, s = τ C ε D v ∧ t = τ C ε D (D.toDiagram.twin v) := by
  rcases X_cover h hs with ⟨i, hi, hsi⟩ | ⟨i, hi, hsi⟩ <;>
    rcases X_cover h ht with ⟨j, hj, htj⟩ | ⟨j, hj, htj⟩
  · exact absurd (X_junction_junction h hi hsi hj htj he) hne
  · exfalso
    apply curveMap_straight_notMem_discs h hj htj
    rw [← he]
    exact Set.mem_iUnion.mpr ⟨i, curveMap_junction_mem_disc h hi hsi⟩
  · exfalso
    apply curveMap_straight_notMem_discs h hi hsi
    rw [he]
    exact Set.mem_iUnion.mpr ⟨j, curveMap_junction_mem_disc h hj htj⟩
  · exact X_straight_straight h hi hsi hj htj hne he

theorem transverse_τ (v : D.toDiagram.Γ.Visit) :
    det (deriv (curveMap C ε) (τ C ε D v))
      (deriv (curveMap C ε) (τ C ε D (D.toDiagram.twin v))) ≠ 0 := by
  obtain ⟨r, hr, hd⟩ := deriv_curveMap_τ h v
  obtain ⟨r', hr', hd'⟩ := deriv_curveMap_τ h (D.toDiagram.twin v)
  rw [hd, hd', X_det_smul_smul]
  refine mul_ne_zero (mul_pos hr hr').ne' ?_
  exact D.generic.transverse _ _ ((Shadow.single C).not_adjacent_other v.1 v.2.2)
    ((Shadow.single C).seg_inter_other_nonempty v.1 v.2.2)

/-- `τ` is a strictly increasing function of the accepted traversal coordinate `visitCoord`
(both are lexicographic in (edge label, crossing parameter)) -/
theorem X_τ_lt_iff (v w : D.toDiagram.Γ.Visit) :
    τ C ε D v < τ C ε D w ↔ D.toDiagram.visitCoord v < D.toDiagram.visitCoord w := by
  have hΛ := Λ_pos h
  have hc0v : 0 ≤ D.toDiagram.crossingParam v.1 v.2.2 := (D.toDiagram.crossingParam_spec v.1 v.2.2).1
  have hc1v : D.toDiagram.crossingParam v.1 v.2.2 < 1 := D.toDiagram.crossingParam_lt_one v.1 v.2.2
  have hc0w : 0 ≤ D.toDiagram.crossingParam w.1 w.2.2 := (D.toDiagram.crossingParam_spec w.1 w.2.2).1
  have hc1w : D.toDiagram.crossingParam w.1 w.2.2 < 1 := D.toDiagram.crossingParam_lt_one w.1 w.2.2
  rw [X_visitCoord_eq v, X_visitCoord_eq w]
  rcases lt_trichotomy (D.label v).val (D.label w).val with hlt | heq | hgt
  · have hcast : ((D.label v).val : ℝ) + 1 ≤ (D.label w).val := by exact_mod_cast hlt
    exact iff_of_true (X_τ_lt_of_label_lt h hlt) (by linarith)
  · have heq' : D.label v = D.label w := ZMod.val_injective _ heq
    have hL := euclideanLength_pos (X_edge_ne_zero D.regular (D.label w))
    unfold τ
    rw [heq', add_lt_add_iff_left, add_lt_add_iff_left, div_lt_div_iff_of_pos_right hΛ,
      sub_lt_sub_iff_right, mul_lt_mul_iff_of_pos_right hL]
  · have hcast : ((D.label w).val : ℝ) + 1 ≤ (D.label v).val := by exact_mod_cast hgt
    exact iff_of_false (not_lt.mpr (X_τ_lt_of_label_lt h hgt).le) (not_lt.mpr (by linarith))

/-- the cyclic order of the occurrences along the rounded circle is that of `D` (`τ` is a strictly
increasing function of the accepted `visitCoord`) -/
theorem order_τ (v w z : D.toDiagram.Γ.Visit) :
    (cycBetween (τ C ε D v) (τ C ε D w) (τ C ε D z) ↔
      cycBetween (D.toDiagram.visitCoord v) (D.toDiagram.visitCoord w)
        (D.toDiagram.visitCoord z)) := by
  unfold cycBetween
  rw [X_τ_lt_iff h v w, X_τ_lt_iff h w z, X_τ_lt_iff h z v]

/-- the smooth crossing sign is the polygonal one (velocities are positive multiples of the edge
directions) -/
theorem sign_τ (x : D.toDiagram.Γ.Crossing) :
    SignType.sign (det (deriv (curveMap C ε) (τ C ε D (D.toDiagram.overVisit x)))
      (deriv (curveMap C ε) (τ C ε D (D.toDiagram.underVisit x)))) = D.toDiagram.sign x := by
  obtain ⟨r, hr, hd⟩ := deriv_curveMap_τ h (D.toDiagram.overVisit x)
  obtain ⟨r', hr', hd'⟩ := deriv_curveMap_τ h (D.toDiagram.underVisit x)
  rw [hd, hd', X_det_smul_smul, sign_mul, sign_pos (mul_pos hr hr'), one_mul]
  rfl

/-- the fundamental period is covered by the closed junction intervals and the open straight
intervals -/
theorem cover {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    (∃ j < C.k, t ∈ Icc (a C ε j) (b C ε j)) ∨ ∃ j < C.k, t ∈ Ioo (b C ε j) (a C ε (j + 1)) := by
  exact X_cover h ht

/-! #### Unit X helpers: flatness at the ends of the junctions -/

omit h in
/-- a `C^∞` plane curve constant on an open set has all derivatives of order `≥ 1` vanishing on
the closure of that set (the `m`-th derivative is continuous and `0` on the open set) -/
theorem X_iteratedDeriv_eq_zero_of_eqOn_open {f : ℝ → Plane} (hf : ContDiff ℝ ∞ f) {s : Set ℝ}
    (hs : IsOpen s) {c : Plane} (hc : ∀ t ∈ s, f t = c) {m : ℕ} (hm : 1 ≤ m) {x : ℝ}
    (hx : x ∈ closure s) : iteratedDeriv m f x = 0 := by
  have h1 : Set.EqOn (iteratedDeriv m f) (iteratedDeriv m (fun _ => c)) s :=
    Set.EqOn.iteratedDeriv_of_isOpen (fun t ht => hc t ht) hs m
  have h2 : Set.EqOn (iteratedDeriv m f) (iteratedDeriv m (fun _ => c)) (closure s) :=
    h1.closure (hf.continuous_iteratedDeriv m (by exact_mod_cast le_top))
      (contDiff_const.continuous_iteratedDeriv m (by exact_mod_cast le_top))
  rw [h2 hx, iteratedDeriv_const]
  have : m ≠ 0 := by omega
  simp [this]

theorem X_contDiff_deriv_curveMap : ContDiff ℝ ∞ (deriv (curveMap C ε)) :=
  (contDiff_infty_iff_deriv.mp (curveMap_smooth h)).2

/-- on the straight part along edge `j` the velocity is the constant `Λ • v_j` -/
theorem X_deriv_curveMap_straight {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (b C ε j) (a C ε (j + 1))) :
    deriv (curveMap C ε) t = Λ C ε • dirOf (θu C (j + 1)) := by
  rw [deriv_curveMap h, tangentField, Θ_on_straight h hj ht]

/-- flatness of order `≥ 2` at the end `b j` of the junction (the straight part after it) -/
theorem X_iteratedDeriv_curveMap_b {j : ℕ} (hj : j < C.k) {m : ℕ} (hm : 2 ≤ m) :
    iteratedDeriv m (curveMap C ε) (b C ε j) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [iteratedDeriv_succ']
  apply X_iteratedDeriv_eq_zero_of_eqOn_open (X_contDiff_deriv_curveMap h)
    (s := Ioo (b C ε j) (a C ε (j + 1))) isOpen_Ioo (c := Λ C ε • dirOf (θu C (j + 1)))
    (fun t ht => X_deriv_curveMap_straight h hj ⟨ht.1.le, ht.2.le⟩) (by omega)
  rw [closure_Ioo (b_lt_a h hj).ne]
  exact ⟨le_rfl, (b_lt_a h hj).le⟩

/-- (b) "the junction meeting the straight edges flat to infinite order": all derivatives of the
curve of order `≥ 2` vanish at the start of a junction (`deriv curveMap = Λ • tangentField`, and
`tangentField` is constant on the open straight part before `a j` — by periodicity for `j = 0` —
so `iteratedDeriv (m−1) tangentField (a j) = 0` by the general left-flatness lemma, localised) -/
theorem iteratedDeriv_curveMap_a {j : ℕ} (hj : j < C.k) {m : ℕ} (hm : 2 ≤ m) :
    iteratedDeriv m (curveMap C ε) (a C ε j) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [iteratedDeriv_succ']
  have hn : 1 ≤ n := by omega
  rcases j with _ | i
  · -- the start of the junction at `q_0`: the straight part along edge `k−1`, shifted by one period
    obtain ⟨i, hi⟩ : ∃ i, C.k = i + 1 := ⟨C.k - 1, by have := C.hk; omega⟩
    have hik : i < C.k := by omega
    have hlt := b_lt_a h hik
    have h1 : a C ε (i + 1) = 1 := by rw [← hi, a_last h]
    rw [a_zero]
    apply X_iteratedDeriv_eq_zero_of_eqOn_open (X_contDiff_deriv_curveMap h)
      (s := Ioo (b C ε i - 1) 0) isOpen_Ioo (c := Λ C ε • dirOf (θu C (i + 1))) ?_ hn
    · rw [closure_Ioo (by linarith : b C ε i - 1 ≠ 0)]
      exact ⟨by linarith, le_rfl⟩
    · intro t ht
      have ht' : t + 1 ∈ Icc (b C ε i) (a C ε (i + 1)) := by
        rw [h1]
        constructor <;> linarith [ht.1, ht.2]
      rw [deriv_curveMap h, ← tangentField_periodic (C := C) (ε := ε) D.regular t, tangentField,
        Θ_on_straight h hik ht']
  · -- the start of the junction at `q_{i+1}`: the straight part along edge `i`
    have hik : i < C.k := by omega
    apply X_iteratedDeriv_eq_zero_of_eqOn_open (X_contDiff_deriv_curveMap h)
      (s := Ioo (b C ε i) (a C ε (i + 1))) isOpen_Ioo (c := Λ C ε • dirOf (θu C (i + 1)))
      (fun t ht => X_deriv_curveMap_straight h hik ⟨ht.1.le, ht.2.le⟩) hn
    rw [closure_Ioo (b_lt_a h hik).ne]
    exact ⟨(b_lt_a h hik).le, le_rfl⟩

/-- … and at its end (the straight part after `b j`) -/
theorem iteratedDeriv_curveMap_b {j : ℕ} (hj : j < C.k) {m : ℕ} (hm : 2 ≤ m) :
    iteratedDeriv m (curveMap C ε) (b C ε j) = 0 := by
  exact X_iteratedDeriv_curveMap_b h hj hm

end doubles

/-! ## 9. Assembly: the rounded loop, the carried diagram, the witness, the row -/

section assembly

variable {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (h : Admissible C D ε)

include h in
theorem curveMap_speed (t : ℝ) : euclideanLength (deriv (curveMap C ε) t) = Λ C ε := by
  rw [deriv_curveMap h, euclideanLength_smul, tangentField_unit, mul_one, abs_of_pos (Λ_pos h)]

include h in
theorem curveMap_regular (t : ℝ) : deriv (curveMap C ε) t ≠ 0 := by
  intro h0
  have h1 := curveMap_speed h t
  rw [h0] at h1
  have : euclideanLength (0 : Plane) = 0 := by simp [euclideanLength, planeComplex_zero]
  exact (Λ_pos h).ne' (h1.symm.trans this)

/-- the rounded curve as a `SmoothRegularLoop` (accepted `SmoothLoop` + regularity) — the
"one curve" of cf:thm-carrierfloor (A) -/
def roundedLoop : SmoothRegularLoop where
  γ := curveMap C ε
  smooth := curveMap_smooth h
  periodic := curveMap_periodic h
  regular := curveMap_regular h

theorem roundedLoop_γ : (roundedLoop h).γ = curveMap C ε := rfl

theorem roundedLoop_speed (t : ℝ) : euclideanLength (deriv (roundedLoop h).γ t) = Λ C ε :=
  curveMap_speed h t

theorem roundedLoop_regular (t : ℝ) : deriv (roundedLoop h).γ t ≠ 0 := curveMap_regular h t

/-- the rounded curve in the accepted `C¹` class -/
def roundedCurve : ClosedC1Curve := (roundedLoop h).toClosedC1Curve

theorem roundedCurve_tangent (t : ℝ) :
    (roundedCurve h).tangentLoop.T t = normalize (deriv (curveMap C ε) t) := rfl

/-- (d) from the accepted corner-rounding clause of cf:lem-turnlift
(`rot_eq_rotationNumber_of_rounding`): junction lifts `liftAt` of increment `ϑ_j`, constant
tangent `v_j` on the straight parts. -/
theorem rot_roundedCurve : (roundedCurve h).rot = rotationNumber C.P := by
  refine rot_eq_rotationNumber_of_rounding C.P (roundedCurve h) (a C ε) (b C ε) a_zero (a_last h)
    (fun k _ => (a_lt_b h k).le) (fun k hk => (b_lt_a h hk).le) (fun k hk => ?_) (fun k hk s hs => ?_)
  · refine ⟨liftAt C ε k, liftAt_isLiftOn h hk, ?_⟩
    rw [liftAt_b h, liftAt_a]
    simp [turn]
  · rw [roundedCurve_tangent, normalize_deriv_curveMap h, tangentField, Θ_on_straight h hk hs,
      dirOf_θu D.regular, uDir_succ]
    rfl

/-- the diagram `D` carried by the rounded curve -/
def roundedCarried : Carried (roundedLoop h) D.toDiagram where
  one := rfl
  τ := τ C ε D
  τ_mem := τ_mem_Ico h
  τ_inj := τ_injective h
  τ_eval := curveMap_τ h
  doubles := fun _ _ hs ht hne he => doubles_curveMap h hs ht hne he
  transverse := transverse_τ h
  order := order_τ h
  sign_eq := sign_τ h

/-- (c) "the same double points": from the carried record -/
theorem doublePoints_roundedLoop :
    SmoothRegularLoop.doublePoints (roundedLoop h).γ =
      {p | ∃ x : D.toDiagram.Γ.Crossing, p = D.toDiagram.Γ.crossingPoint x} := by
  ext p
  constructor
  · rintro ⟨s, t, hs, ht, hne, rfl, hts⟩
    obtain ⟨v, rfl, -⟩ := doubles_curveMap h hs ht hne hts.symm
    exact ⟨v.1, curveMap_τ h v⟩
  · rintro ⟨x, rfl⟩
    refine ⟨τ C ε D (D.toDiagram.overVisit x), τ C ε D (D.toDiagram.twin (D.toDiagram.overVisit x)),
      τ_mem_Ico h _, τ_mem_Ico h _, fun he => ?_, curveMap_τ h _, curveMap_τ h _⟩
    exact D.toDiagram.twin_ne _ (τ_injective h he).symm

/-- the rounding record `Round(L, D, ε) = (L_ε, D_ε)` at an admissible `ε`: every clause read from
the chain -/
def roundedWitness : RoundingWitness C D ε where
  Lε := roundedLoop h
  speed := Λ C ε
  speed_pos := Λ_pos h
  const_speed := roundedLoop_speed h
  carried := roundedCarried h
  a := a C ε
  b := b C ε
  a_zero := a_zero
  a_last := a_last h
  a_lt_b := fun j _ => a_lt_b h j
  b_lt_a := fun j hj => b_lt_a h hj
  junction_start := fun j hj => curveMap_a h hj.le
  junction_end := fun j hj => curveMap_b h hj
  straight := fun j hj t ht => by
    rw [roundedLoop_γ, curveMap_on_straight h hj ht, curveMap_b h hj]
    rfl
  outside := fun p hp => range_curveMap_outside h hp
  θ := liftAt C ε
  θ_smooth := fun j _ => liftAt_smooth j
  θ_lift := fun j hj => liftAt_isLiftOn h hj
  θ_const_left := fun j _ t ht => liftAt_const_left h j ht
  θ_const_right := fun j _ t ht => liftAt_const_right h j ht
  tangent_start := fun j hj => by
    have hl : normalize (deriv (curveMap C ε) (a C ε j)) =
        (Real.cos (liftAt C ε j (a C ε j)), Real.sin (liftAt C ε j (a C ε j))) :=
      (liftAt_isLiftOn h hj).2 (a C ε j) ⟨le_rfl, (a_lt_b h j).le⟩
    show normalize (deriv (curveMap C ε) (a C ε j)) = _
    rw [hl, liftAt_a]
    exact dirOf_θu D.regular j
  tangent_end := fun j hj => by
    have hl : normalize (deriv (curveMap C ε) (b C ε j)) =
        (Real.cos (liftAt C ε j (b C ε j)), Real.sin (liftAt C ε j (b C ε j))) :=
      (liftAt_isLiftOn h hj).2 (b C ε j) ⟨(a_lt_b h j).le, le_rfl⟩
    show normalize (deriv (curveMap C ε) (b C ε j)) = _
    rw [hl, liftAt_b h]
    exact dirOf_θu_add_turn D.regular j
  θ_sweep := fun j _ => by rw [liftAt_b h, liftAt_a]; simp [turn]
  θ_range := fun j _ t ht => by
    rcases lt_or_gt_of_ne (h.turn_ne j) with hneg | hpos
    · have hm := (liftAt_strictAntiOn h hneg).antitoneOn
      exact Set.mem_uIcc.mpr (Or.inr ⟨hm ht ⟨(a_lt_b h j).le, le_rfl⟩ ht.2,
        hm ⟨le_rfl, (a_lt_b h j).le⟩ ht ht.1⟩)
    · have hm := (liftAt_strictMonoOn h hpos).monotoneOn
      exact Set.mem_uIcc.mpr (Or.inl ⟨hm ⟨le_rfl, (a_lt_b h j).le⟩ ht ht.1,
        hm ht ⟨(a_lt_b h j).le, le_rfl⟩ ht.2⟩)
  θ_strict := fun j _ => ⟨fun hp => liftAt_strictMonoOn h hp, fun hn => liftAt_strictAntiOn h hn⟩
  θ_unique := fun j _ β hβ => by
    have hc : ContinuousOn (liftAt C ε j) (uIcc (a C ε j) (b C ε j)) :=
      (liftAt_smooth j).continuous.continuousOn
    obtain ⟨t, ht, hβ'⟩ := intermediate_value_uIcc hc hβ
    rw [uIcc_of_le (a_lt_b h j).le] at ht
    have hinj : InjOn (liftAt C ε j) (Icc (a C ε j) (b C ε j)) := by
      rcases lt_or_gt_of_ne (h.turn_ne j) with hneg | hpos
      · exact (liftAt_strictAntiOn h hneg).injOn
      · exact (liftAt_strictMonoOn h hpos).injOn
    exact ⟨t, ⟨ht, hβ'⟩, fun t' ht' => hinj ht'.1 ht (ht'.2.trans hβ'.symm)⟩
  direction_once := fun j hj => tangent_injOn_junction h hj
  immersion := fun j hj t ht => deriv_liftAt_ne_zero h hj ht
  flat_ends := fun j _ m hm =>
    ⟨iteratedDeriv_eq_zero_of_const_left (liftAt_smooth j) (fun t ht => liftAt_const_left h j ht) hm,
      iteratedDeriv_eq_zero_of_const_right (liftAt_smooth j) (fun t ht => liftAt_const_right h j ht) hm⟩
  flat_ends_curve := fun j hj m hm => ⟨iteratedDeriv_curveMap_a h hj hm, iteratedDeriv_curveMap_b h hj hm⟩
  same_double_points := doublePoints_roundedLoop h
  same_strands := fun v => τ_mem_straight h v
  same_strand_dir := fun v => deriv_curveMap_τ h v
  same_signs := fun x => (roundedCarried h).smoothSign_eq x
  same_writhe := (roundedCarried h).smoothWrithe_eq
  rot_eq := rot_roundedCurve h
  disc_isDisc := cornerDisc_isDisc h.ε_pos
  disc_disjoint := fun i j hij => cornerDisc_disjoint h hij
  disc_center := mem_interior_cornerDisc h.ε_pos
  disc_off_nonincident := fun i j hij => cornerDisc_disjoint_edge h hij
  disc_no_double := fun i x => crossingPoint_notMem_cornerDisc h i x
  disc_meets_out := cornerDisc_inter_edge_out h
  disc_meets_in := cornerDisc_inter_edge_in h
  disc_contains_modification := fun j hj t ht => curveMap_junction_mem_disc h hj ht
  disc_only_modification := fun j hj t ht hmem => by
    rcases cover h ht with ⟨i, hi, hti⟩ | ⟨i, hi, hti⟩
    · by_cases hij : i = j
      · subst hij; exact hti
      · exfalso
        have hi' := curveMap_junction_mem_disc h hi hti
        have hij' : (i : ZMod C.k) ≠ (j : ZMod C.k) := by
          intro heq
          apply hij
          have := congrArg ZMod.val heq
          rwa [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at this
        exact Set.disjoint_left.mp (cornerDisc_disjoint h hij') hi' hmem
    · exact absurd (Set.mem_iUnion.mpr ⟨(j : ZMod C.k), hmem⟩) (curveMap_straight_notMem_discs h hi hti)
  junction_embedded := fun j hj s hs t ht hst => by
    have hℓ := ℓ_pos h j
    have hΛ := Λ_pos h
    have hmem : ∀ r ∈ Icc (a C ε j) (b C ε j), (r - a C ε j) * Λ C ε / ℓ C ε j ∈ Icc (0 : ℝ) 1 := by
      intro r hr
      constructor
      · exact div_nonneg (mul_nonneg (sub_nonneg.mpr hr.1) hΛ.le) hℓ.le
      · rw [div_le_one hℓ]
        have h1 : r - a C ε j ≤ ℓ C ε j / Λ C ε := by
          have := b_sub_a (C := C) (ε := ε) j
          linarith [hr.2]
        calc (r - a C ε j) * Λ C ε ≤ (ℓ C ε j / Λ C ε) * Λ C ε := by gcongr
          _ = ℓ C ε j := div_mul_cancel₀ _ hΛ.ne'
    have hst' : juncArc (A0 C ε j) ε (θu C j) (turn C j) ((s - a C ε j) * Λ C ε / ℓ C ε j) =
        juncArc (A0 C ε j) ε (θu C j) (turn C j) ((t - a C ε j) * Λ C ε / ℓ C ε j) := by
      rw [← curveMap_on_junction h hj hs, ← curveMap_on_junction h hj ht]
      exact hst
    have heq := juncArc_injOn h.ε_pos (turn_bounds h j).1 (turn_bounds h j).2 (hmem s hs) (hmem t ht) hst'
    rw [div_eq_div_iff hℓ.ne' hℓ.ne'] at heq
    have h2 := mul_right_cancel₀ hℓ.ne' heq
    have h3 := mul_right_cancel₀ hΛ.ne' h2
    linarith
  straight_off_discs := fun j hj t ht => curveMap_straight_notMem_discs h hj ht

end assembly

end CornerRounding

/-! ## 10. The row from the chain -/

open CornerRounding in
/-- cf:lem-rounding, assembled from the chain: the clearance is the printed `ε₀(L)`, the witness the
printed construction; the clause fields are projections of `RoundingWitness`. -/
theorem cf_lem_rounding : RoundingData where
  exists_clearance := fun C hturn gen =>
    ⟨clearance C, clearance_pos gen, fun D ε hε hε₀ =>
      ⟨roundedWitness (C := C) (D := D) (ε := ε) ⟨hturn, hε, hε₀⟩⟩⟩
  smooth_regular_carried := fun _ _ _ W => ⟨W.smooth, W.periodic, W.regular, ⟨W.carried⟩⟩
  a := fun _ _ _ W => ⟨W.outside, W.straight⟩
  b := fun _ _ _ W j hj =>
    ⟨W.disc_contains_modification j hj, W.θ_smooth j hj, W.θ_lift j hj, W.const_speed,
      W.tangent_start j hj, W.tangent_end j hj, W.θ_sweep j hj, W.θ_range j hj, (W.θ_strict j hj).1,
      (W.θ_strict j hj).2, W.θ_unique j hj, W.direction_once j hj, W.immersion j hj,
      W.flat_ends j hj, W.flat_ends_curve j hj, W.θ_const_left j hj, W.θ_const_right j hj⟩
  c := fun _ _ _ W =>
    ⟨W.same_double_points, fun v => ⟨W.same_strands v, W.same_strand_dir v⟩, W.same_signs,
      W.same_writhe⟩
  d := fun _ _ _ W => W.rot_eq
  e := fun _ _ _ W =>
    ⟨W.disc_isDisc, W.disc_disjoint, W.disc_center, W.disc_off_nonincident, W.disc_no_double,
      W.disc_meets_out, W.disc_meets_in, W.disc_contains_modification, W.disc_only_modification,
      W.junction_embedded, W.straight_off_discs⟩

end

end SM
