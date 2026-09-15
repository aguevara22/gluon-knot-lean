import SM.FrontSmooth
import SM.TurnLift
import SM.LinkDiagramRecord
import SM.LinkPositiveLift

/-! # SM cf:lem-rounding — corner rounding of a polygonal diagram (FIXED-STATEMENT candidate A)

Source: reference/SM/sm-3-statesum.tex:3644-3700 (statement), 3701-3869 (proof).  Architect A
(model-first), 2026-09-14.  Plan: work/drafts/rounding/PLAN_A.md; skeleton: Skeleton_A.lean.
Check: `cd work/lean && lake env lean ../drafts/rounding/Rounding_statement_A.lean`.

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

## Printed notion → Lean (model decision, PLAN_A.md §1)

| printed | Lean |
|---|---|
| closed polygon `L` with corners `q_i`, edges `δ_i = q_{i+1} − q_i` | `C : PolyComp` (accepted def:polygon object with `3 ≤ k`), `L = C.P : LabelledTuple C.k`, corners `C.P i`, edges `edge C.P i` |
| "oriented diagram whose underlying plane curve is L": over/under at each double point; finitely many transversal double points, none a corner, no corner on a non-incident edge | `PolygonDiagram C`: the accepted one-component `Diagram` on the shadow `Shadow.single C` (its `Shadow.Generic` is exactly the printed list: `regular`, `tail_off`, `transverse`, `no_triple`; the over strand is the over/under assignment) |
| "the principal turns of L all exist and are nonzero" | `Regular C.P` (in `Generic`) and `∀ i, principalTurn C.P i ≠ 0` |
| "clearance ε₀(L) > 0 … for every ε ∈ (0, ε₀(L))" | `∃ ε₀, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ → Nonempty (RoundingWitness C D ε)` (Q3: the clearance is quantified in the conclusion; the explicit value ⅓·min{η_v,η_e,η_ℓ,η_X} is the proof's witness, exported as `clearance` in the skeleton) |
| "a C^∞ regular closed plane curve L_ε" | `Lε : SmoothLoop` (accepted `C^∞` 1-periodic loop, FrontSmooth.lean) with `regular : ∀ t, deriv Lε.γ t ≠ 0`; the accepted `ClosedC1Curve` is `Lε.toClosedC1Curve regular` (no second smooth-curve class) |
| "a diagram D_ε carried by it" | `Carried Lε D.toDiagram` (FR-1 for immersed circles: the polygonal `Diagram` carries the named record of the smooth curve — occurrences realised at parameters `τ`, pairing, cyclic order, over/under from the polygonal record, signs read from velocities); `D_ε` *is* `D`, which is what (c) asserts |
| the unit tangent, arclength, tangent-angle lift, `rot` | `normalize (deriv Lε.γ t)` (= `tangentLoop.T`), constant speed `speed` (so arclength = `speed · Δt`), `IsLiftOn` (TurnLift.lean), `ClosedC1Curve.rot` (TurningNumber.lean), `rotationNumber` (lem:rot) |
| "the discs of radius ε about the corners" (closed, (e)) | `cornerDisc C ε i = {p | euclideanLength (p − C.P i) ≤ ε}` (Euclidean; `IsDisc` is the accepted clean-disc vocabulary, LinkMoves.lean) |
| "the two sub-segments of length ε at q_i" | `subsegOut C ε i`, `subsegIn C ε i` |
| "the modification made at q_i" | the junction arc `Lε.γ '' Icc (a k) (b k)` of the subdivision `a b : ℕ → ℝ` (junction at corner `k` on `[a k, b k]`, straight along edge `k` on `[b k, a (k+1)]`, the pattern of the accepted `rot_eq_rotationNumber_of_rounding`) |

One structure field per printed sub-clause in `RoundingWitness`; one bundle field per printed
sentence/clause in `RoundingData`; main declaration `SM.cf_lem_rounding : RoundingData`. -/

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
`regular` ("the principal turns of L all exist"). -/
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

/-! ## 3. A diagram carried by a `C^∞` regular closed curve (the smooth-diagram model)

FR-1 instantiated for immersed circles (sm-3:337-343 "a diagram here is a finite polygonal
immersion, or a regular smooth immersion …"; lem:gauss-pl-model "the crossing names, the four-ray
orders, the traversal direction and the over/under designations are retained"): the polygonal
one-component `Diagram X` is *carried by* the regular smooth loop `γ` when every occurrence of `X`
is realised at a parameter `τ v` of `γ` at the crossing point, the double points of `γ` are exactly
these pairs (paired by `X.twin`), the branches are transverse, the cyclic order of the occurrences
along the circle is that of `X`, and the over/under assignment is `X`'s — so that the crossing sign
of the smooth diagram (`sgn det` of the over velocity followed by the under velocity, def:positive-lift)
is `X.sign`.  This is the one smooth-diagram notion for cf:lem-rounding, cf:lem-curl and
cf:thm-carrierfloor; the front block's `SmoothFront.Marking` is the same reading with the front's
slope rule for over/under (a front is not a `SmoothLoop` with `regular`: it has cusps and the
`no_vertical` clause, so the two structures cannot be one). -/
structure Carried (γ : SmoothLoop) (X : Diagram) where
  /-- "regular": an immersion -/
  regular : ∀ t, deriv γ.γ t ≠ 0
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

variable {γ : SmoothLoop} {X : Diagram} (c : Carried γ X)

/-- the crossing sign of the smooth diagram at `x`: `sgn det(velocity_over, velocity_under)` -/
def smoothSign (x : X.Γ.Crossing) : SignType :=
  SignType.sign (det (deriv γ.γ (c.τ (X.overVisit x))) (deriv γ.γ (c.τ (X.underVisit x))))

/-- the writhe of the smooth diagram -/
def smoothWrithe : ℤ := ∑ x : X.Γ.Crossing, (c.smoothSign x : ℤ)

theorem smoothSign_eq (x : X.Γ.Crossing) : c.smoothSign x = X.sign x := c.sign_eq x

theorem smoothWrithe_eq : c.smoothWrithe = X.writhe := by
  unfold smoothWrithe Diagram.writhe
  exact Finset.sum_congr rfl fun x _ => by rw [c.smoothSign_eq]

/-- the set of double points of `γ` (as points of the plane) -/
def doublePoints (γ : SmoothLoop) : Set Plane :=
  {p | ∃ s t : ℝ, s ∈ Set.Ico (0 : ℝ) 1 ∧ t ∈ Set.Ico (0 : ℝ) 1 ∧ s ≠ t ∧ γ.γ s = p ∧ γ.γ t = p}

end Carried

/-! ## 4. The rounding witness: one field per printed sub-clause -/

/-- The data returned by cf:lem-rounding at a clearance-admissible `ε`: the curve `L_ε`, the
carried diagram (which is `D`), the subdivision of the parameter circle into junctions and straight
parts, the tangent-angle lifts of the junctions, and one Prop field per printed sub-clause of
(a)-(e).  The parameter is arclength up to the constant factor `speed` (so the printed arclength
`σ` along the junction at corner `k` is `speed · (t − a k)`, its length `ℓ = speed · (b k − a k)`). -/
structure RoundingWitness (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) where
  /-- "a C^∞ regular closed plane curve L_ε": the accepted `C^∞` 1-periodic loop … -/
  Lε : SmoothLoop
  /-- … which is regular -/
  regular : ∀ t, deriv Lε.γ t ≠ 0
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
  /-- (b) "sweeping an arc of length exactly |ϑ_i| and no more": the lift increment is `ϑ_i`
  (with the strict monotonicity below, the swept arc is exactly the closed arc of length `|ϑ_i|`) -/
  θ_sweep : ∀ j < C.k, θ j (b j) - θ j (a j) = principalTurn C.P j
  /-- (b) "the unit tangent moves strictly monotonically, in the sense of sgn ϑ_i" -/
  θ_strict : ∀ j < C.k,
    (0 < principalTurn C.P j → StrictMonoOn (θ j) (Set.Icc (a j) (b j))) ∧
    (principalTurn C.P j < 0 → StrictAntiOn (θ j) (Set.Icc (a j) (b j)))
  /-- (b) "attaining each direction of that arc": every angle of the swept arc is attained … -/
  θ_attained : ∀ j < C.k, ∀ β ∈ Set.uIcc (θ j (a j)) (θ j (b j)),
    ∃ t ∈ Set.Icc (a j) (b j), θ j t = β
  /-- (b) "… at exactly one parameter": the unit tangent is injective on the closed junction -/
  direction_once : ∀ j < C.k, Set.InjOn (fun t => normalize (deriv Lε.γ t)) (Set.Icc (a j) (b j))
  /-- (b) "the unit-tangent map is an immersion on the open junction arc: parametrized by
  arclength, its angular derivative is nonzero at every interior parameter" (the parameter is
  arclength up to the factor `speed > 0`) -/
  immersion : ∀ j < C.k, ∀ t ∈ Set.Ioo (a j) (b j), deriv (θ j) t ≠ 0
  /-- (b) "while at the two ends it and all its derivatives vanish, the junction meeting the
  straight edges flat to infinite order" -/
  flat_ends : ∀ j < C.k, ∀ m : ℕ, 1 ≤ m →
    iteratedDeriv m (θ j) (a j) = 0 ∧ iteratedDeriv m (θ j) (b j) = 0
  /-- (c) "L_ε has the same double points as L": the double points of `L_ε` are exactly the
  crossing points of `L` -/
  same_double_points :
    Carried.doublePoints Lε = {p | ∃ x : D.toDiagram.Γ.Crossing, p = D.toDiagram.Γ.crossingPoint x}
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
  rot_eq : (Lε.toClosedC1Curve regular).rot = rotationNumber C.P
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
  /-- (e) the modification is only there: the open straight parts avoid every disc -/
  straight_off_discs : ∀ j < C.k, ∀ t ∈ Set.Ioo (b j) (a (j + 1)), Lε.γ t ∉ ⋃ i, cornerDisc C ε i

namespace RoundingWitness

variable {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε)

/-- the rounded curve in the accepted `C¹` class (cf:def-turning) -/
def curve : ClosedC1Curve := W.Lε.toClosedC1Curve W.regular

/-- the unit tangent `T = γ'/|γ'|` -/
def T : ℝ → Plane := fun t => normalize (deriv W.Lε.γ t)

theorem T_eq_tangentLoop : W.T = W.curve.tangentLoop.T := rfl

theorem rot_curve : W.curve.rot = rotationNumber C.P := W.rot_eq

theorem smooth : ContDiff ℝ ∞ W.Lε.γ := W.Lε.smooth

theorem periodic : Function.Periodic W.Lε.γ 1 := W.Lε.periodic

end RoundingWitness

/-! ## 5. The row bundle: one field per printed sentence / clause -/

/-- cf:lem-rounding (sm-3:3644-3700), one field per printed sentence or clause; the objects are
those of `RoundingWitness`.  Model decisions: PLAN_A.md §1 (input `PolygonDiagram`, output
`SmoothLoop` + `Carried`, discs `cornerDisc`, subdivision `a b`). -/
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
    (0 < principalTurn C.P j → StrictMonoOn (W.θ j) (Set.Icc (W.a j) (W.b j))) ∧
    (principalTurn C.P j < 0 → StrictAntiOn (W.θ j) (Set.Icc (W.a j) (W.b j))) ∧
    (∀ β ∈ Set.uIcc (W.θ j (W.a j)) (W.θ j (W.b j)), ∃ t ∈ Set.Icc (W.a j) (W.b j), W.θ j t = β) ∧
    Set.InjOn W.T (Set.Icc (W.a j) (W.b j)) ∧
    (∀ t ∈ Set.Ioo (W.a j) (W.b j), deriv (W.θ j) t ≠ 0) ∧
    (∀ m : ℕ, 1 ≤ m → iteratedDeriv m (W.θ j) (W.a j) = 0 ∧ iteratedDeriv m (W.θ j) (W.b j) = 0) ∧
    (∀ t ≤ W.a j, W.θ j t = W.θ j (W.a j)) ∧ (∀ t, W.b j ≤ t → W.θ j t = W.θ j (W.b j))
  /-- (c) "L_ε has the same double points as L, with the same strands, the same over/under
  assignment and hence the same crossing signs and the same writhe." -/
  c : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (W : RoundingWitness C D ε),
    Carried.doublePoints W.Lε =
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
    (∀ j < C.k, ∀ t ∈ Set.Ioo (W.b j) (W.a (j + 1)), W.Lε.γ t ∉ ⋃ i, cornerDisc C ε i)

/-- cf:lem-rounding. -/
theorem cf_lem_rounding : RoundingData := by
  sorry

end

end SM
