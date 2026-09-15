import SM.FrontSmooth
import SM.TurnLift
import SM.LinkDiagramRecord
import SM.LinkMoves
import SM.PolynomialBlock
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # SM cf:lem-curl — exact negative-curl replacement (FIXED-STATEMENT, candidate B)

Source: reference/SM/sm-3-statesum.tex:3870-3889 (statement), 3890-4278 (proof); consumer
cf:thm-carrierfloor sm-3:4282-4330, use at 4438-4455.  Architect B (literal smooth reading),
2026-09-14.  Decision record: work/drafts/curl/PLAN_B.md; chain and assembly: Skeleton_B.lean.
Check: `cd work/lean && lake env lean ../drafts/curl/Statements_B.lean`.

## The printed statement (sm-3:3870-3889, clause by clause)

"Here rot is as in Lemma lem:rot for polygons and Definition cf:def-turning for closed C¹ regular
curves. Let F be a connected C^∞ immersed circle in the plane — one component, with finitely many
transverse double points and no triple points — given with an oriented diagram, and let p be a
point of F at which the tangent points in a fixed direction u, isolated among such points, lying in
an embedded arc of F that contains no double point and along which the tangent turns strictly
positively. Then F may be modified inside a disc Δ meeting the rest of the diagram only in that arc,
so that the resulting diagram F'
(i) is again such an oriented diagram, satisfies P_{F'}(a,z) = P_F(a,z), and has the same double
points outside Δ, with the same signs;
(ii) has no point of Δ at which the tangent equals u, and exactly one at which it equals −u;
(iii) has exactly one double point inside Δ, and it is negative;
(iv) satisfies rot(F') = rot(F) − 1 and w(F') = w(F) − 1."

## Printed notion → Lean (model decisions, PLAN_B.md §2)

| printed | Lean |
|---|---|
| "a connected C^∞ immersed circle … one component" | `F : SmoothRegularLoop` (cf:lem-rounding's output class: `SmoothLoop` = `C^∞`, period 1, FR-R1/FR-3; `regular`) |
| "with finitely many transverse double points and no triple points — given with an oriented diagram" | `X : Diagram` (accepted polygonal one-component diagram) with `Carried F X` (FR-R1: the smooth diagram is the polygonal `Diagram` carried by the loop; `doubles`/`τ_inj` exclude triple points, `transverse` is transversality) |
| "a point p of F at which the tangent points in a fixed direction u" | parameter `t₀`, `p = F.γ t₀`, `u` a unit vector, `normalize (deriv F.γ t₀) = u` |
| "isolated among such points" | `isolated` (no other tangent-`u` parameter in a neighbourhood of `t₀`) |
| "lying in an embedded arc of F that contains no double point" | parameter arc `[α, β] ∋ t₀`, `β − α < 1`, `arc_simple`: every passage of `F` through a point of the arc is a periodic copy of the arc's own passage (embedded, and no double point of `F` on it) |
| "along which the tangent turns strictly positively" | `turns_pos : 0 < det γ' γ''` on `[α, β]` (the printed `det(b', b'') > 0`, sm-3:3900) |
| "a disc Δ meeting the rest of the diagram only in that arc" | read on BOTH halves of the smooth diagram (FR-C1): a chart disc `Δ₀` (accepted `IsDisc`, `p ∈ interior Δ₀`) in which the curve is the arc (`Δ₀_curve`) and the polygon `X` is one crossing-free arc `arc0` in the same gap of the cyclic order (`Δ₀_cover`, `Δ₀_clean`, `Δ₀_no_crossing`, `compat`); the modification disc `Δ = curlDisc p r` is a closed Euclidean disc INSIDE `Δ₀` of preassigned radius `≤ ρ` (sm-3:4024-4028 "the disc is fixed first and the cuts afterwards", needed by the consumer's "choose each curl disc inside its rounding disc") |
| "F may be modified inside Δ" | cut parameters `s₋ < t₀ < s₊` in `(α, β)`; `F' = F` (with its derivative) on `[s₊, s₋ + 1]` (one period minus the open cut); the removed and the inserted sub-arcs lie in `Δ` |
| (i) "is again such an oriented diagram" | `F' : SmoothRegularLoop`, `X' : Diagram`, `Carried F' X'` |
| (i) "P_{F'} = P_F" | `P X' = P X` (accepted `P : Diagram → R`, SM/LocalPolynomial.lean:22), a corollary of the exported Reidemeister-I site `ri : RIData Δ₀ X X'` (accepted, LinkMoves.lean:569) through the accepted `P_reidemeister_I` (PolynomialBlock.lean:605) — the printed "being a single Reidemeister-I monogon" |
| (i) "the same double points outside Δ, with the same signs" | `doubles_outside` (as sets), `points_outside`/`signs_outside` through the outer-crossing bijection `ri.out.ψ` of the accepted `OutsideMatch` |
| (ii) | `no_tangent_u`, `one_tangent_neg_u` (`∃!` parameter in `[0,1)`) |
| (iii) | `double_in_disc_iff` (the double points of `F'` in `Δ` are exactly the kink point), `kink_negative` (sign = `sgn det(over velocity, under velocity)` of def:positive-lift, through `Carried.smoothSign`) |
| (iv) | `rot_eq : F'.toClosedC1Curve.rot = F.toClosedC1Curve.rot − 1` (cf:def-turning `rot`), `writhe_eq` on `Carried.smoothWrithe` |
| the mechanism of (iv) (sm-3:3911-3914, 4232-4251): the compatible lift increment of the replacement is the old one minus 2π, the old sweep lies in (0, π) | witness fields `θ`, `θ'` (`IsLiftOn` on the cut), `lift_init`, `θ_strictMono`, `sweep_old_pos`, `sweep_old_lt_pi`, `sweep_new` — exported (strictly more than the printed clauses, FR-C4) |

One structure field per printed sub-clause in `CurlWitness`; one bundle field per printed sentence /
clause in `CurlData` (the existence sentence carries the theorem); main declaration
`SM.cf_lem_curl : CurlData`.

PORT NOTE.  Section 0 below is a byte-identical copy of SM/Rounding.lean:70-222 (= the accepted
statement vocabulary of cf:lem-rounding, Rounding_statement_FINAL.lean §1-§4: `PolygonDiagram`,
`eucDist`/`cornerDisc`/`subsegOut`/`subsegIn`/`polygonImage`, `SmoothRegularLoop`, `Carried`).  It is
here only because `SM/Rounding.olean` is not yet built (2026-09-14) and drafts may not run
`lake build`; at port time delete §0 and add `import SM.Rounding`.  Nothing in §0 is new. -/

namespace SM

open Link
open scoped ContDiff

noncomputable section
open Classical

/-! ## 0. VOCABULARY COPY of SM/Rounding.lean:70-222 (delete at port time; see PORT NOTE) -/

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

/-! ## 1. The disc about `p` and the quarter turn -/

/-- "a disc Δ" / "a preassigned disc Δ about p" (sm-3:3878, 4031): the closed Euclidean disc of
radius `r` about `p`, with the Euclidean distance `eucDist` of the rounding vocabulary (not the
product metric). -/
def curlDisc (p : Plane) (r : ℝ) : Set Plane := {q | eucDist q p ≤ r}

/-- "J is the positive quarter turn" (sm-3:3968): `J (x, y) = (−y, x)`. -/
def Jrot (w : Plane) : Plane := (-w.2, w.1)

/-! ## 2. The site: the hypotheses of cf:lem-curl, one field per printed phrase -/

/-- The hypotheses of cf:lem-curl (sm-3:3873-3878) on a `C^∞` regular loop `F` carrying the
polygonal diagram `X` (FR-R1), one field per printed phrase, plus the chart disc `Δ₀` in which "the
rest of the diagram" is read on both halves of the smooth diagram (FR-C1, PLAN_B.md §2.3):
* `carried`: "given with an oriented diagram" — the accepted one-component `Diagram X` is carried by
  `F` (occurrences at parameters `τ`, double points = crossings paired by `twin`, transverse, cyclic
  order, over/under with sign consistency); `Carried.doubles` + `τ_inj` say "finitely many transverse
  double points and no triple points";
* `u`, `t₀`, `tangent_at`: "a point p of F at which the tangent points in a fixed direction u",
  `p = F.γ t₀`;
* `isolated`: "isolated among such points";
* `α β`, `arc_simple`: "lying in an embedded arc of F that contains no double point" — the
  parameter arc `[α, β] ∋ t₀`, shorter than the period, whose points are passed only by the arc
  itself (up to the period);
* `turns_pos`: "along which the tangent turns strictly positively" — `det(γ', γ'') > 0`;
* `Δ₀ …`: the chart disc: an accepted `IsDisc` with `p` in its interior, meeting the curve only in the
  arc (`Δ₀_curve`) and meeting the polygon `X` in exactly one crossing-free arc `arc0`
  (`Δ₀_cover`, `Δ₀_clean`, `Δ₀_no_crossing`: the accepted vocabulary of a Reidemeister-I site,
  LinkMoves.lean:569-588), which occupies the same gap between consecutive occurrences as the smooth
  arc (`compat`).  The consumer supplies `Δ₀ := ` the rounding disc `D_i` of cf:lem-rounding (e)
  (sm-3:4443-4445 "Choose each curl disc inside its corresponding rounding disc"). -/
structure CurlSite (F : SmoothRegularLoop) (X : Diagram) where
  /-- "given with an oriented diagram" (FR-R1): `X` carried by `F` -/
  carried : Carried F X
  /-- "a fixed direction u" -/
  u : Plane
  u_unit : euclideanLength u = 1
  /-- the parameter of "a point p of F" -/
  t₀ : ℝ
  /-- "at which the tangent points in a fixed direction u" -/
  tangent_at : normalize (deriv F.γ t₀) = u
  /-- "isolated among such points" -/
  isolated : ∃ δ : ℝ, 0 < δ ∧ ∀ t, |t - t₀| < δ → normalize (deriv F.γ t) = u → t = t₀
  /-- "lying in an embedded arc of F": the parameter arc `[α, β]` around `t₀` … -/
  α : ℝ
  β : ℝ
  α_lt : α < t₀
  lt_β : t₀ < β
  /-- … shorter than the period (an arc, not the whole circle) -/
  arc_short : β - α < 1
  /-- "an embedded arc of F that contains no double point": every passage of `F` through a point of
  the arc is a periodic copy of the arc's own passage -/
  arc_simple : ∀ t ∈ Set.Icc α β, ∀ s : ℝ, F.γ s = F.γ t → ∃ n : ℤ, s = t + n
  /-- "along which the tangent turns strictly positively": `det(γ', γ'') > 0` (sm-3:3900) -/
  turns_pos : ∀ t ∈ Set.Icc α β, 0 < det (deriv F.γ t) (deriv (deriv F.γ) t)
  /-- the chart disc `Δ₀` (FR-C1): an accepted disc … -/
  Δ₀ : Set Plane
  Δ₀_disc : IsDisc Δ₀
  /-- … about `p` … -/
  p_mem : F.γ t₀ ∈ interior Δ₀
  /-- … meeting the curve only in the arc ("a disc meeting the rest of the diagram only in that
  arc", smooth half) … -/
  Δ₀_curve : ∀ t, F.γ t ∈ Δ₀ → ∃ n : ℤ, t + n ∈ Set.Icc α β
  /-- … and meeting the polygonal diagram `X` in exactly one arc `arc0` (polygonal half) … -/
  arc0 : X.Γ.Arc
  Δ₀_cover : X.Γ.ArcCover Δ₀ {arc0}
  Δ₀_clean : Clean Δ₀ X
  /-- … which is crossing-free (no double point of the diagram in `Δ₀`) … -/
  Δ₀_no_crossing : ∀ x : X.Γ.Crossing, X.Γ.crossingPoint x ∉ Δ₀
  /-- … and lies in the same gap of the cyclic order of occurrences as the smooth arc: `arc0`
  is between the occurrences `v, w` iff `p` is -/
  compat : ∀ v w : X.Γ.Visit,
    (cycBetween (carried.τ v) (Int.fract t₀) (carried.τ w) ↔
      cycBetween (X.visitCoord v) (traversalKey arc0.start) (X.visitCoord w))

namespace CurlSite

variable {F : SmoothRegularLoop} {X : Diagram} (S : CurlSite F X)

/-- "a point p of F" -/
def p : Plane := F.γ S.t₀

/-- "v = −Ju, so that (v, u) is a positively oriented orthonormal basis" (sm-3:3968-3969) -/
def v : Plane := -Jrot S.u

/-- the unit tangent of `F` at `p` is `u` -/
theorem tangent_p : normalize (deriv F.γ S.t₀) = S.u := S.tangent_at

end CurlSite

/-! ## 3. The witness: one field per printed sub-clause of the conclusion -/

/-- The data returned by cf:lem-curl at a site `S` for a preassigned radius `ρ > 0`: the modified
curve `F'`, the polygonal diagram `X'` it carries (FR-R1), the modification disc `Δ = curlDisc p r`
(`r ≤ ρ`, inside the chart disc), the cut parameters, the tangent lifts of the removed and inserted
sub-arcs (the mechanism of (iv), sm-3:3911-3914 and 4232-4251), the Reidemeister-I site of the
polygonal half, and one Prop field per printed sub-clause of (i)-(iv). -/
structure CurlWitness {F : SmoothRegularLoop} {X : Diagram} (S : CurlSite F X) (ρ : ℝ) where
  /-- "the resulting diagram F'": the modified `C^∞` regular closed curve -/
  F' : SmoothRegularLoop
  /-- (i) "is again such an oriented diagram": the polygonal diagram carried by `F'` (FR-R1) -/
  X' : Diagram
  carried' : Carried F' X'
  /-- "inside a disc Δ": `Δ = curlDisc p r`, a closed Euclidean disc of radius `r ≤ ρ` about `p`
  ("the disc is fixed first and the cuts afterwards", sm-3:4024-4028) … -/
  r : ℝ
  r_pos : 0 < r
  r_le : r ≤ ρ
  disc_isDisc : IsDisc (curlDisc S.p r)
  p_in_disc : S.p ∈ interior (curlDisc S.p r)
  /-- … inside the chart disc … -/
  disc_sub : curlDisc S.p r ⊆ S.Δ₀
  /-- … "meeting the rest of the diagram only in that arc" (smooth half: the curve meets `Δ` only in
  the open arc; polygonal half: `disc_sub` and the site) -/
  disc_meets_arc : ∀ t, F.γ t ∈ curlDisc S.p r → ∃ n : ℤ, t + n ∈ Set.Ioo S.α S.β
  /-- the cuts `sm < t₀ < sp` — the printed `s₋ < 0 < s₊`, `p_± = γ(s_±)` (sm-3:3979-3984) -/
  sm : ℝ
  sp : ℝ
  α_lt_cut : S.α < sm
  cut_lt_t₀ : sm < S.t₀
  t₀_lt_cut : S.t₀ < sp
  cut_lt_β : sp < S.β
  /-- "F may be modified inside a disc Δ": the removed sub-arc lies in `Δ` … -/
  old_in_disc : ∀ t ∈ Set.Icc sm sp, F.γ t ∈ curlDisc S.p r
  /-- … the inserted sub-arc lies in `Δ` … -/
  new_in_disc : ∀ t ∈ Set.Icc sm sp, F'.γ t ∈ curlDisc S.p r
  /-- … and `F'` is `F` elsewhere: on `[sp, sm + 1]` (one period minus the open cut), as a
  parametrised curve … -/
  unchanged : ∀ t ∈ Set.Icc sp (sm + 1), F'.γ t = F.γ t
  /-- … with its velocity -/
  unchanged_deriv : ∀ t ∈ Set.Icc sp (sm + 1), deriv F'.γ t = deriv F.γ t
  /-- the tangent-angle lift of the removed sub-arc ("the old central arc … its lifted sweep
  θ(sp) − θ(sm) lying in (0, π)", sm-3:4247-4249) … -/
  θ : ℝ → ℝ
  θ_lift : IsLiftOn (fun t => normalize (deriv F.γ t)) θ sm sp
  /-- … the old arc turns strictly positively … -/
  θ_strictMono : StrictMonoOn θ (Set.Icc sm sp)
  sweep_old_pos : 0 < θ sp - θ sm
  sweep_old_lt_pi : θ sp - θ sm < Real.pi
  /-- … and the compatible lift of the inserted sub-arc ("compatible tangent lifts with equal
  initial values", cf:lem-turnlift (iii)) … -/
  θ' : ℝ → ℝ
  θ'_lift : IsLiftOn (fun t => normalize (deriv F'.γ t)) θ' sm sp
  lift_init : θ' sm = θ sm
  /-- … "its compatible lift increment is the old one minus 2π" (sm-3:3912-3913) -/
  sweep_new : θ' sp - θ' sm = (θ sp - θ sm) - 2 * Real.pi
  /-- (i) polygonal half: `X'` is obtained from `X` by a Reidemeister-I move inside the chart disc
  ("being a single Reidemeister-I monogon", sm-3:3923-3924; the accepted `RIData`, FR-C1) … -/
  ri : RIData S.Δ₀ X X'
  /-- … whose kink is the double point of `F'` inside `Δ` -/
  kink_point : X'.Γ.crossingPoint ri.kink ∈ curlDisc S.p r
  /-- (i) "satisfies P_{F'}(a,z) = P_F(a,z)" -/
  P_eq : P X' = P X
  /-- (i) "has the same double points outside Δ" (as points of the plane) … -/
  doubles_outside : ∀ q, q ∉ curlDisc S.p r →
    (q ∈ SmoothRegularLoop.doublePoints F'.γ ↔ q ∈ SmoothRegularLoop.doublePoints F.γ)
  /-- … the outer crossings correspond (the accepted outside match `ri.out.ψ`) with the same double
  points … -/
  points_outside : ∀ x : X.OuterCrossing S.Δ₀,
    X'.Γ.crossingPoint (ri.out.ψ x).1 = X.Γ.crossingPoint x.1
  /-- … "with the same signs" (the smooth crossing signs of the carried diagrams) -/
  signs_outside : ∀ x : X.OuterCrossing S.Δ₀,
    carried'.smoothSign (ri.out.ψ x).1 = S.carried.smoothSign x.1
  /-- (ii) "has no point of Δ at which the tangent equals u" -/
  no_tangent_u : ∀ t, F'.γ t ∈ curlDisc S.p r → normalize (deriv F'.γ t) ≠ S.u
  /-- (ii) "and exactly one at which it equals −u" (one parameter of the fundamental period) -/
  one_tangent_neg_u : ∃! t, t ∈ Set.Ico (0 : ℝ) 1 ∧ F'.γ t ∈ curlDisc S.p r ∧
    normalize (deriv F'.γ t) = -S.u
  /-- (iii) "has exactly one double point inside Δ": the double points of `F'` in `Δ` are exactly the
  kink point -/
  double_in_disc_iff : ∀ q ∈ curlDisc S.p r,
    (q ∈ SmoothRegularLoop.doublePoints F'.γ ↔ q = X'.Γ.crossingPoint ri.kink)
  /-- (iii) "and it is negative": `sgn det(over velocity, under velocity) = −1` (def:positive-lift,
  read on the carried diagram) -/
  kink_negative : carried'.smoothSign ri.kink = -1
  /-- (iv) "rot(F') = rot(F) − 1" (cf:def-turning `rot` on both sides) -/
  rot_eq : F'.toClosedC1Curve.rot = F.toClosedC1Curve.rot - 1
  /-- (iv) "w(F') = w(F) − 1" (the writhe of the smooth diagrams) -/
  writhe_eq : carried'.smoothWrithe = S.carried.smoothWrithe - 1

namespace CurlWitness

variable {F : SmoothRegularLoop} {X : Diagram} {S : CurlSite F X} {ρ : ℝ} (W : CurlWitness S ρ)

/-- the modification disc `Δ` -/
def Δ : Set Plane := curlDisc S.p W.r

/-- the modified curve in the accepted `C¹` class (cf:def-turning) -/
def curve : ClosedC1Curve := W.F'.toClosedC1Curve

theorem rot_curve : W.curve.rot = F.toClosedC1Curve.rot - 1 := W.rot_eq

/-- the polygonal half of (i): `X'` is Reidemeister-I equivalent to `X` (the accepted move relation) -/
theorem ri_rel : RI X W.X' := ⟨S.Δ₀, Or.inl ⟨W.ri⟩⟩

/-- the polygonal writhe changes by `−1` too (`Carried.smoothWrithe_eq`) -/
theorem writhe_polygonal : W.X'.writhe = X.writhe - 1 := by
  rw [← W.carried'.smoothWrithe_eq, ← S.carried.smoothWrithe_eq]
  exact W.writhe_eq

/-- the polygonal sign of the kink is negative (`Carried.smoothSign_eq`) -/
theorem kink_sign_polygonal : W.X'.sign W.ri.kink = -1 := by
  rw [← W.carried'.smoothSign_eq]
  exact W.kink_negative

theorem smooth : ContDiff ℝ ∞ W.F'.γ := W.F'.smooth

theorem periodic : Function.Periodic W.F'.γ 1 := W.F'.periodic

theorem regular : ∀ t, deriv W.F'.γ t ≠ 0 := W.F'.regular

end CurlWitness

/-! ## 4. The row bundle: one field per printed sentence / clause -/

/-- cf:lem-curl (sm-3:3870-3889), one field per printed sentence or clause; the objects are those of
`CurlSite` and `CurlWitness`.  The existence sentence (`exists_curl`) carries the theorem; the
clause fields state how each printed clause reads on a witness (projections of `CurlWitness`, so the
fixed content of (i)-(iv) is the field list of that structure, as for cf:lem-rounding FR-R5).
Model decisions: PLAN_B.md §2. -/
structure CurlData : Prop where
  /-- "Then F may be modified inside a disc Δ meeting the rest of the diagram only in that arc, so
  that the resulting diagram F' [(i)-(iv)]" — for every preassigned radius `ρ > 0` (the consumer's
  "choose each curl disc inside its corresponding rounding disc", sm-3:4443-4445). -/
  exists_curl : ∀ (F : SmoothRegularLoop) (X : Diagram) (S : CurlSite F X) (ρ : ℝ), 0 < ρ →
    Nonempty (CurlWitness S ρ)
  /-- "F may be modified inside a disc Δ meeting the rest of the diagram only in that arc": `Δ` is a
  disc about `p` inside the chart disc, meets the curve only in the open arc, contains the removed and
  the inserted sub-arcs, and `F' = F` (with velocity) outside the cut. -/
  modified_inside_disc : ∀ (F : SmoothRegularLoop) (X : Diagram) (S : CurlSite F X) (ρ : ℝ)
      (W : CurlWitness S ρ),
    IsDisc W.Δ ∧ S.p ∈ interior W.Δ ∧ W.r ≤ ρ ∧ W.Δ ⊆ S.Δ₀ ∧
    (∀ t, F.γ t ∈ W.Δ → ∃ n : ℤ, t + n ∈ Set.Ioo S.α S.β) ∧
    (∀ t ∈ Set.Icc W.sm W.sp, F.γ t ∈ W.Δ ∧ W.F'.γ t ∈ W.Δ) ∧
    (∀ t ∈ Set.Icc W.sp (W.sm + 1), W.F'.γ t = F.γ t ∧ deriv W.F'.γ t = deriv F.γ t)
  /-- (i) "is again such an oriented diagram, satisfies P_{F'}(a,z) = P_F(a,z), and has the same
  double points outside Δ, with the same signs" -/
  i : ∀ (F : SmoothRegularLoop) (X : Diagram) (S : CurlSite F X) (ρ : ℝ) (W : CurlWitness S ρ),
    (ContDiff ℝ ∞ W.F'.γ ∧ Function.Periodic W.F'.γ 1 ∧ (∀ t, deriv W.F'.γ t ≠ 0) ∧
      Nonempty (Carried W.F' W.X')) ∧
    RI X W.X' ∧ P W.X' = P X ∧
    (∀ q, q ∉ W.Δ →
      (q ∈ SmoothRegularLoop.doublePoints W.F'.γ ↔ q ∈ SmoothRegularLoop.doublePoints F.γ)) ∧
    (∀ x : X.OuterCrossing S.Δ₀,
      W.X'.Γ.crossingPoint (W.ri.out.ψ x).1 = X.Γ.crossingPoint x.1 ∧
      W.carried'.smoothSign (W.ri.out.ψ x).1 = S.carried.smoothSign x.1)
  /-- (ii) "has no point of Δ at which the tangent equals u, and exactly one at which it equals −u" -/
  ii : ∀ (F : SmoothRegularLoop) (X : Diagram) (S : CurlSite F X) (ρ : ℝ) (W : CurlWitness S ρ),
    (∀ t, W.F'.γ t ∈ W.Δ → normalize (deriv W.F'.γ t) ≠ S.u) ∧
    (∃! t, t ∈ Set.Ico (0 : ℝ) 1 ∧ W.F'.γ t ∈ W.Δ ∧ normalize (deriv W.F'.γ t) = -S.u)
  /-- (iii) "has exactly one double point inside Δ, and it is negative" -/
  iii : ∀ (F : SmoothRegularLoop) (X : Diagram) (S : CurlSite F X) (ρ : ℝ) (W : CurlWitness S ρ),
    (∀ q ∈ W.Δ,
      (q ∈ SmoothRegularLoop.doublePoints W.F'.γ ↔ q = W.X'.Γ.crossingPoint W.ri.kink)) ∧
    W.X'.Γ.crossingPoint W.ri.kink ∈ W.Δ ∧
    W.carried'.smoothSign W.ri.kink = -1 ∧ W.X'.sign W.ri.kink = -1
  /-- (iv) "satisfies rot(F') = rot(F) − 1 and w(F') = w(F) − 1" (the mechanism exported: the
  compatible lift increment of the inserted arc is the old one, which lies in (0, π), minus 2π) -/
  iv : ∀ (F : SmoothRegularLoop) (X : Diagram) (S : CurlSite F X) (ρ : ℝ) (W : CurlWitness S ρ),
    W.curve.rot = F.toClosedC1Curve.rot - 1 ∧
    W.carried'.smoothWrithe = S.carried.smoothWrithe - 1 ∧ W.X'.writhe = X.writhe - 1 ∧
    (IsLiftOn (fun t => normalize (deriv F.γ t)) W.θ W.sm W.sp ∧
      IsLiftOn (fun t => normalize (deriv W.F'.γ t)) W.θ' W.sm W.sp ∧ W.θ' W.sm = W.θ W.sm ∧
      StrictMonoOn W.θ (Set.Icc W.sm W.sp) ∧
      0 < W.θ W.sp - W.θ W.sm ∧ W.θ W.sp - W.θ W.sm < Real.pi ∧
      W.θ' W.sp - W.θ' W.sm = (W.θ W.sp - W.θ W.sm) - 2 * Real.pi)

/-- The clause fields are projections of the witness: any proof of the existence sentence is a
proof of the whole bundle (FR-R5 pattern). -/
theorem CurlData.of_exists
    (h : ∀ (F : SmoothRegularLoop) (X : Diagram) (S : CurlSite F X) (ρ : ℝ), 0 < ρ →
      Nonempty (CurlWitness S ρ)) : CurlData where
  exists_curl := h
  modified_inside_disc := fun _ _ _ _ W =>
    ⟨W.disc_isDisc, W.p_in_disc, W.r_le, W.disc_sub, W.disc_meets_arc,
      fun t ht => ⟨W.old_in_disc t ht, W.new_in_disc t ht⟩,
      fun t ht => ⟨W.unchanged t ht, W.unchanged_deriv t ht⟩⟩
  i := fun _ _ _ _ W =>
    ⟨⟨W.smooth, W.periodic, W.regular, ⟨W.carried'⟩⟩, W.ri_rel, W.P_eq, W.doubles_outside,
      fun x => ⟨W.points_outside x, W.signs_outside x⟩⟩
  ii := fun _ _ _ _ W => ⟨W.no_tangent_u, W.one_tangent_neg_u⟩
  iii := fun _ _ _ _ W =>
    ⟨W.double_in_disc_iff, W.kink_point, W.kink_negative, W.kink_sign_polygonal⟩
  iv := fun _ _ _ _ W =>
    ⟨W.rot_curve, W.writhe_eq, W.writhe_polygonal,
      W.θ_lift, W.θ'_lift, W.lift_init, W.θ_strictMono, W.sweep_old_pos, W.sweep_old_lt_pi,
      W.sweep_new⟩

/-- cf:lem-curl. -/
theorem cf_lem_curl : CurlData := by
  sorry

end

end SM
