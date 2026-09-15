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
construction (§7), the chain of leaf lemmas (§8, `sorry`), the assembly (§9, proved) and the row (§10, proved).
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
  closed plane curve L_ε, and a diagram D_ε carried by it, with these properties [(a)-(e)]." -/
  exists_clearance : ∀ (C : PolyComp) (D : PolygonDiagram C), (∀ i, principalTurn C.P i ≠ 0) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → Nonempty (RoundingWitness C D ε)
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
      Nonempty (RoundingWitness C (PolygonDiagram.ofDiagram D hD) ε) :=
  h.exists_clearance C _ hturn

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

/-! ## 8. The chain of lemmas (all `sorry`; unit split in PLAN_FINAL.md §5)

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
  sorry

/-- `φ' > 0` on `(0,1)` -/
theorem deriv_smoothTransition_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    0 < deriv Real.smoothTransition t := by
  sorry

/-- A `C^∞` function constant on `(−∞, x]` has all derivatives of order `≥ 1` vanishing at `x`
(the value at `x` is the limit from the left of the continuous `m`-th derivative, which is `0`
on the open half-line). -/
theorem iteratedDeriv_eq_zero_of_const_left {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {x c : ℝ}
    (h : ∀ t ≤ x, f t = c) {m : ℕ} (hm : 1 ≤ m) : iteratedDeriv m f x = 0 := by
  sorry

/-- the mirror statement on `[x, ∞)` -/
theorem iteratedDeriv_eq_zero_of_const_right {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {x c : ℝ}
    (h : ∀ t, x ≤ t → f t = c) {m : ℕ} (hm : 1 ≤ m) : iteratedDeriv m f x = 0 := by
  sorry

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
  sorry

theorem contDiff_juncAngle (θu ϑ : ℝ) : ContDiff ℝ ∞ (juncAngle θu ϑ) := by
  unfold juncAngle
  exact contDiff_const.add (contDiff_const.mul Real.smoothTransition.contDiff)

theorem contDiff_juncDir (θu ϑ : ℝ) : ContDiff ℝ ∞ (juncDir θu ϑ) := by
  unfold juncDir dirOf
  exact (Real.contDiff_cos.comp (contDiff_juncAngle θu ϑ)).prodMk
    (Real.contDiff_sin.comp (contDiff_juncAngle θu ϑ))

/-- `M(ϑ) > 0` for `|ϑ| < π`: the integrand is `≥ cos(ϑ/2) > 0` -/
theorem M_pos {ϑ : ℝ} (h : |ϑ| < Real.pi) : 0 < M ϑ := by
  sorry

theorem juncLen_pos {ε ϑ : ℝ} (hε : 0 < ε) (h : |ϑ| < Real.pi) : 0 < juncLen ε ϑ := by
  sorry

/-- the printed `m(φ)` points along the bisector: `∫₀¹ juncDir = (M(ϑ)/(2cos(ϑ/2))) • (u + v)`
(symmetry `φ(1−s) = 1 − φ(s)` kills the transverse component) -/
theorem integral_juncDir {θu ϑ : ℝ} (h : |ϑ| < Real.pi) :
    (∫ s in (0 : ℝ)..1, juncDir θu ϑ s) =
      (M ϑ / (2 * Real.cos (ϑ / 2))) • (dirOf θu + dirOf (θu + ϑ)) := by
  sorry

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

/-- the arc lies in the closed triangle `A₀ q A₁`, hence in the closed `ε`-disc about `q = A₀ + εu`
(the two cone inequalities and the chord inequality, sm-3:3762-3806) -/
theorem juncArc_mem_disc {A0 : Plane} {ε θu ϑ : ℝ} (hε : 0 < ε) (h0 : ϑ ≠ 0) (h : |ϑ| < Real.pi)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    eucDist (juncArc A0 ε θu ϑ s) (A0 + ε • dirOf θu) ≤ ε := by
  sorry

/-- interior points of the arc are strictly inside the disc -/
theorem juncArc_mem_open_disc {A0 : Plane} {ε θu ϑ : ℝ} (hε : 0 < ε) (h0 : ϑ ≠ 0)
    (h : |ϑ| < Real.pi) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    eucDist (juncArc A0 ε θu ϑ s) (A0 + ε • dirOf θu) < ε := by
  sorry

/-- the arc is simple: its bisector coordinate is strictly increasing (sm-3:3807-3811) -/
theorem juncArc_injOn {A0 : Plane} {ε θu ϑ : ℝ} (hε : 0 < ε) (h0 : ϑ ≠ 0) (h : |ϑ| < Real.pi) :
    InjOn (juncArc A0 ε θu ϑ) (Icc 0 1) := by
  sorry

/-! ### Unit G — the global curve: angles, subdivision, `Θ`, `L_ε` -/

section global

variable {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ}

/-- `|ϑ_j| < π` and `ϑ_j ≠ 0` -/
theorem turn_bounds (h : Admissible C D ε) (j : ZMod C.k) : turn C j ≠ 0 ∧ |turn C j| < Real.pi :=
  ⟨h.turn_ne j, abs_lt.mpr (principalAngle_bounds (D.regular j))⟩

/-- `dirOf (θu j) = u_j` (induction: `v_j = u_j · e^{iϑ_j}` by the definition of the principal turn) -/
theorem dirOf_θu (hreg : Regular C.P) (j : ℕ) : dirOf (θu C j) = uDir C j := by
  sorry

/-- `dirOf (θu j + ϑ_j) = v_j` -/
theorem dirOf_θu_add_turn (hreg : Regular C.P) (j : ℕ) : dirOf (θu C j + turn C j) = vDir C j := by
  sorry

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
  sorry

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

/-- `Θ` is `C^∞` (locally, near every point, it is one of the smooth expressions
`θu j + ϑ_j φ((t − m − a j)Λ/ℓ_j)`; the floor and fract are locally affine or absorbed by
`φ = 0` on `(−∞,0]`, `φ = 1` on `[1,∞)`) -/
theorem Θ_smooth (h : Admissible C D ε) : ContDiff ℝ ∞ (Θ C ε) := by
  sorry

/-- `Θ (t + 1) = Θ t + 2π rot(L)` -/
theorem Θ_add_one (t : ℝ) : Θ C ε (t + 1) = Θ C ε t + 2 * Real.pi * rotationNumber C.P := by
  unfold Θ
  rw [Int.floor_add_one, Int.fract_add_one]
  push_cast
  ring

/-- on the junction at corner `j`, `Θ` is the junction lift -/
theorem Θ_on_junction (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (a C ε j) (b C ε j)) : Θ C ε t = liftAt C ε j t := by
  sorry

/-- on the straight part along edge `j`, `Θ` is the constant `θu (j+1)` -/
theorem Θ_on_straight (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (b C ε j) (a C ε (j + 1))) : Θ C ε t = θu C (j + 1) := by
  sorry

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

/-- the integral of the tangent field over the junction at corner `j` -/
theorem integral_tangentField_junction (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) :
    (∫ s in a C ε j..b C ε j, tangentField C ε s) = (ε / Λ C ε) • (uDir C j + vDir C j) := by
  sorry

/-- the integral over the straight part along edge `j` -/
theorem integral_tangentField_straight (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) :
    (∫ s in b C ε j..a C ε (j + 1), tangentField C ε s) = (str C ε j / Λ C ε) • vDir C j := by
  sorry

/-- the total displacement vanishes: `Σ_j [ε(u_j + v_j) + (|δ_j| − 2ε) v_j] = Σ_j δ_j = 0` -/
theorem integral_tangentField_period (h : Admissible C D ε) :
    (∫ s in (0 : ℝ)..1, tangentField C ε s) = 0 := by
  sorry

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
  sorry

theorem curveMap_b (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) : curveMap C ε (b C ε j) = A1 C ε j := by
  sorry

/-- on the junction the curve is the abstract junction arc (substitution `s = (t − a j)Λ/ℓ_j`) -/
theorem curveMap_on_junction (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (a C ε j) (b C ε j)) :
    curveMap C ε t =
      juncArc (A0 C ε j) ε (θu C j) (turn C j) ((t - a C ε j) * Λ C ε / ℓ C ε j) := by
  sorry

/-- on the straight part the curve runs straight at speed `Λ` -/
theorem curveMap_on_straight (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Icc (b C ε j) (a C ε (j + 1))) :
    curveMap C ε t = A1 C ε j + (Λ C ε * (t - b C ε j)) • vDir C j := by
  sorry

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

theorem liftAt_strictMonoOn (h : Admissible C D ε) {j : ℕ} (hpos : 0 < turn C j) :
    StrictMonoOn (liftAt C ε j) (Icc (a C ε j) (b C ε j)) := by
  sorry

theorem liftAt_strictAntiOn (h : Admissible C D ε) {j : ℕ} (hneg : turn C j < 0) :
    StrictAntiOn (liftAt C ε j) (Icc (a C ε j) (b C ε j)) := by
  sorry

theorem deriv_liftAt_ne_zero (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Ioo (a C ε j) (b C ε j)) : deriv (liftAt C ε j) t ≠ 0 := by
  sorry

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

theorem tangent_injOn_junction (h : Admissible C D ε) {j : ℕ} (hj : j < C.k) :
    InjOn (fun t => normalize (deriv (curveMap C ε) t)) (Icc (a C ε j) (b C ε j)) := by
  sorry

end global

/-! ### Unit E — the clearance and the disc package on the polygon alone (sm-3:3822-3846) -/

section discs

variable {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ}

theorem clearance_pos (gen : (Shadow.single C).Generic) : 0 < clearance C := by
  sorry

theorem cornerDisc_isDisc (hε : 0 < ε) (i : ZMod C.k) : IsDisc (cornerDisc C ε i) := by
  sorry

theorem mem_interior_cornerDisc (hε : 0 < ε) (i : ZMod C.k) : C.P i ∈ interior (cornerDisc C ε i) := by
  sorry

theorem cornerDisc_disjoint (h : Admissible C D ε) {i j : ZMod C.k} (hij : i ≠ j) :
    Disjoint (cornerDisc C ε i) (cornerDisc C ε j) := by
  sorry

theorem cornerDisc_disjoint_edge (h : Admissible C D ε) {i j : ZMod C.k} (hij : ¬ incident i j) :
    Disjoint (cornerDisc C ε i) (edgeSegment C.P j) := by
  sorry

theorem crossingPoint_notMem_cornerDisc (h : Admissible C D ε) (i : ZMod C.k)
    (x : D.toDiagram.Γ.Crossing) : D.toDiagram.Γ.crossingPoint x ∉ cornerDisc C ε i := by
  sorry

theorem cornerDisc_inter_edge_out (h : Admissible C D ε) (i : ZMod C.k) :
    cornerDisc C ε i ∩ edgeSegment C.P i = subsegOut C ε i := by
  sorry

theorem cornerDisc_inter_edge_in (h : Admissible C D ε) (i : ZMod C.k) :
    cornerDisc C ε i ∩ edgeSegment C.P (i - 1) = subsegIn C ε i := by
  sorry

/-- a double point is more than `3ε` from every corner -/
theorem three_mul_lt_dist_crossing (h : Admissible C D ε) (i : ZMod C.k)
    (x : D.toDiagram.Γ.Crossing) : 3 * ε < eucDist (D.toDiagram.Γ.crossingPoint x) (C.P i) := by
  sorry

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
  exists_clearance := fun C D hturn =>
    ⟨clearance C, clearance_pos D.generic, fun ε hε hε₀ =>
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
