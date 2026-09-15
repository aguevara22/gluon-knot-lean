import SM.FrontSmooth
import SM.TurnLift
import SM.LinkDiagramRecord
import SM.LinkMoves
import SM.PolynomialBlock
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # SM cf:lem-curl — exact negative-curl replacement (SKELETON, candidate B)

Source: reference/SM/sm-3-statesum.tex:3870-3889 (statement), 3890-4278 (proof); consumer
cf:thm-carrierfloor sm-3:4282-4330, use at 4438-4455.  Architect B (literal smooth reading),
2026-09-14.  Decision record: work/drafts/curl/PLAN_B.md; chain and assembly: Skeleton_B.lean.
SKELETON: the statement text of Statements_B.lean verbatim (§0-§4), then the construction (§5),
the chain of leaf lemmas (§6, all `sorry`), the assembly (§7, proved) and the row (§8, proved from the
chain).  Check: `cd work/lean && lake env lean ../drafts/curl/Skeleton_B.lean`.

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


/-! ## 5. The construction (printed proof, sm-3:3892-4280), as explicit definitions

The printed proof works in the rational model `b`, `c` on `[−2, 2]`, fits it affinely into the cut
`[p₋, p₊]` of the positive-turn chart (`A`, `B = (ℓ/12)A`, `Φ`), and repairs the two `C¹` joins by
collars that are graphs `h = (1 − φ_λ) f + φ_λ g` over the longitudinal coordinate `η`, with the
transition profile `φ = Real.smoothTransition` of cf:lem-rounding (sm-3:4105).  The objects that are
formulas are definitions here; the objects that are choices (the cuts, the collar widths, the
`C^∞` reparametrisation of the glued arc onto `[s₋, s₊]`) are packaged in the chain structures of §6. -/

namespace Curl

variable {F : SmoothRegularLoop} {X : Diagram} (S : CurlSite F X)

/-- the transverse coordinate `ξ(s) = ⟨γ(s) − p, v⟩` of the positive-turn chart (sm-3:3970-3972) -/
def ξ (t : ℝ) : ℝ := planeDot (F.γ t - S.p) S.v

/-- the longitudinal coordinate `η(s) = ⟨γ(s) − p, u⟩` -/
def η (t : ℝ) : ℝ := planeDot (F.γ t - S.p) S.u

/-- the rational model of the old arc, `b(t) = (3(t² + 7)/11, −3t)` (sm-3:3892) -/
def bModel (t : ℝ) : Plane := (3 * (t ^ 2 + 7) / 11, -3 * t)

/-- the rational model of the replacement, `c(t) = (t² − 1, t − t³)` (sm-3:3893) -/
def cModel (t : ℝ) : Plane := (t ^ 2 - 1, t - t ^ 3)

/-- the model frame `v₀ = (−1, 0)`, `u₀ = (0, −1)` (sm-3:3988-3989) -/
def v₀ : Plane := (-1, 0)
def u₀ : Plane := (0, -1)

/-- `q = 4/11` (sm-3:3989) -/
def qFit : ℝ := 4 / 11

/-- `H = 2ac/(bc + ad)` (sm-3:4001-4003) -/
def Hfit (a b c d : ℝ) : ℝ := 2 * a * c / (b * c + a * d)

/-- `x = H/q` -/
def xFit (a b c d : ℝ) : ℝ := Hfit a b c d / qFit

/-- `y = (bc − ad)/(q(bc + ad))` -/
def yFit (a b c d : ℝ) : ℝ := (b * c - a * d) / (qFit * (b * c + a * d))

/-- the linear map `A` with `A u₀ = u`, `A v₀ = x v + y u` (sm-3:4007), written on the standard
coordinates of the model plane (`z = −z₁ v₀ − z₂ u₀`) -/
def Amap (u v : Plane) (x y : ℝ) (z : Plane) : Plane := (-z.1) • (x • v + y • u) + (-z.2) • u

/-- `Φ(z) = p₋ + B(z − b(−2))`, `B = (ℓ/12) A` (sm-3:4024-4026) -/
def Φmap (pm : Plane) (ℓ : ℝ) (u v : Plane) (x y : ℝ) (z : Plane) : Plane :=
  pm + (ℓ / 12) • Amap u v x y (z - bModel (-2))

/-- the inserted arc `Φ ∘ c` on `[−2, 2]` (sm-3:4056) -/
def insArc (pm : Plane) (ℓ : ℝ) (u v : Plane) (x y : ℝ) (t : ℝ) : Plane :=
  Φmap pm ℓ u v x y (cModel t)

/-- the collar `h = (1 − φ_λ) f + φ_λ g`, `φ_λ(η) = φ((η − η₋)/λ)`, `φ = Real.smoothTransition`
(sm-3:4098-4105); at `p₊` the same formula with the roles of `f` and `g` exchanged (sm-3:4176-4180) -/
def collar (f g : ℝ → ℝ) (e0 lam : ℝ) (t : ℝ) : ℝ :=
  (1 - Real.smoothTransition ((t - e0) / lam)) * f t + Real.smoothTransition ((t - e0) / lam) * g t

end Curl

/-! ## 6. The chain of lemmas (all `sorry`; unit split in PLAN_B.md §5) -/

namespace Curl

open Set

variable {F : SmoothRegularLoop} {X : Diagram} (S : CurlSite F X)

/-! ### Unit D — the modification disc -/

/-- `Δ` is an accepted disc (compact, convex, nonempty interior) -/
theorem isDisc_curlDisc (p : Plane) {r : ℝ} (hr : 0 < r) : IsDisc (curlDisc p r) := by
  sorry

/-- `p` is interior to `Δ` -/
theorem mem_interior_curlDisc (p : Plane) {r : ℝ} (hr : 0 < r) : p ∈ interior (curlDisc p r) := by
  sorry

/-- a Euclidean disc about an interior point of an accepted disc lies inside it for small radius -/
theorem exists_curlDisc_subset {U : Set Plane} {p : Plane} (hp : p ∈ interior U) :
    ∃ r : ℝ, 0 < r ∧ curlDisc p r ⊆ U := by
  sorry

/-! ### Unit M — the rational model (sm-3:3893-3924, 4204-4215): pure algebra -/

/-- `b(±2) = c(±2) = (3, ∓6)` -/
theorem model_endpoints : bModel 2 = (3, -6) ∧ bModel (-2) = (3, 6) ∧
    cModel 2 = (3, -6) ∧ cModel (-2) = (3, 6) := by
  sorry

theorem deriv_bModel (t : ℝ) : deriv bModel t = (6 * t / 11, -3) := by
  sorry

theorem deriv_cModel (t : ℝ) : deriv cModel t = (2 * t, 1 - 3 * t ^ 2) := by
  sorry

/-- "the endpoint tangent rays agree up to positive scale: `b'(±2) = (3/11) c'(±2)`" -/
theorem deriv_model_endpoints :
    deriv bModel 2 = (3 / 11 : ℝ) • deriv cModel 2 ∧
      deriv bModel (-2) = (3 / 11 : ℝ) • deriv cModel (-2) := by
  sorry

/-- "the old arc turns strictly positively": `det(b', b'') = 18/11` -/
theorem det_bModel (t : ℝ) : det (deriv bModel t) (deriv (deriv bModel) t) = 18 / 11 := by
  sorry

/-- "the replacement turns strictly negatively": `det(c', c'') = −2(1 + 3t²)` -/
theorem det_cModel (t : ℝ) :
    det (deriv cModel t) (deriv (deriv cModel) t) = -2 * (1 + 3 * t ^ 2) := by
  sorry

/-- "in each arc the first derivative has vanishing first component only at `t = 0`" -/
theorem model_vertical_iff (t : ℝ) :
    ((deriv bModel t).1 = 0 ↔ t = 0) ∧ ((deriv cModel t).1 = 0 ↔ t = 0) := by
  sorry

/-- `b'(0) = (0, −3) ∈ ℝ_{>0} u₀`, `c'(0) = (0, 1) = −u₀` -/
theorem deriv_model_zero : deriv bModel 0 = (0, -3) ∧ deriv cModel 0 = (0, 1) := by
  sorry

/-- "if `c(s) = c(t)` then `s = ±t`, and the second coordinate forces `2t(1 − t²) = 0`": the only
pair of distinct parameters is `{−1, 1}` -/
theorem cModel_double {s t : ℝ} (h : cModel s = cModel t) (hne : s ≠ t) :
    (s = 1 ∧ t = -1) ∨ (s = -1 ∧ t = 1) := by
  sorry

/-- "exactly one double point, `c(−1) = c(1) = (0, 0)`, `c'(−1) = (−2, −2)`, `c'(1) = (2, −2)`" -/
theorem cModel_doublePoint : cModel 1 = 0 ∧ cModel (-1) = 0 ∧
    deriv cModel (-1) = (-2, -2) ∧ deriv cModel 1 = (2, -2) := by
  sorry

/-- "putting the later branch over the earlier one makes it negative: `det(c'(1), c'(−1)) = −8`" -/
theorem det_cModel_branches : det (deriv cModel 1) (deriv cModel (-1)) = -8 := by
  sorry

/-- "the model's transverse excess over its endpoint chord is `4 − t² > 0` for `−2 < t < 2`"
(transverse coordinate `−(c t).1 = 1 − t²`, equal to `−3` at both ends) -/
theorem cModel_excess (t : ℝ) : -(cModel t).1 - (-3) = 4 - t ^ 2 := by
  sorry

/-! ### Unit A — the affine fit, quantitatively (sm-3:3987-4028): algebra of `A` -/

theorem Amap_u₀ (u v : Plane) (x y : ℝ) : Amap u v x y u₀ = u := by
  sorry

theorem Amap_v₀ (u v : Plane) (x y : ℝ) : Amap u v x y v₀ = x • v + y • u := by
  sorry

theorem Amap_add (u v : Plane) (x y : ℝ) (z w : Plane) :
    Amap u v x y (z + w) = Amap u v x y z + Amap u v x y w := by
  sorry

theorem Amap_smul (u v : Plane) (x y : ℝ) (r : ℝ) (z : Plane) :
    Amap u v x y (r • z) = r • Amap u v x y z := by
  sorry

/-- "`A(q v₀ + u₀) = (H/a) T₋`" with `T₋ = a v + b u` -/
theorem Amap_ray_minus (u v : Plane) {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    Amap u v (xFit a b c d) (yFit a b c d) (qFit • v₀ + u₀) =
      (Hfit a b c d / a) • (a • v + b • u) := by
  sorry

/-- "`A(−q v₀ + u₀) = (H/c) T₊`" with `T₊ = −c v + d u` -/
theorem Amap_ray_plus (u v : Plane) {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    Amap u v (xFit a b c d) (yFit a b c d) ((-qFit) • v₀ + u₀) =
      (Hfit a b c d / c) • ((-c) • v + d • u) := by
  sorry

/-- "`det A = x = 2ac/(q(bc + ad)) > 0`" (in the positively oriented orthonormal frame `(v, u)`) -/
theorem det_Amap (u v : Plane) (hvu : det v u = 1) (x y : ℝ) :
    det (Amap u v x y v₀) (Amap u v x y u₀) = x := by
  sorry

theorem xFit_pos {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    0 < xFit a b c d := by
  sorry

/-- "`1 − (qy)² = 4abcd/(bc + ad)² > 0`, so `|y| < 1/q` uniformly: the map `A` stays bounded" -/
theorem one_sub_qy_sq {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    1 - (qFit * yFit a b c d) ^ 2 = 4 * a * b * c * d / (b * c + a * d) ^ 2 ∧
      0 < 1 - (qFit * yFit a b c d) ^ 2 := by
  sorry

/-- "the two outer determinants are `det(q v₀ + u₀, −q v₀ + u₀) = 2q > 0` and
`det(T₋, T₊) = ad + bc > 0`, so the ordered-ray condition holds; it is computed, not inferred" -/
theorem orderedRay_condition (u v : Plane) (hvu : det v u = 1) {a b c d : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    det (qFit • v₀ + u₀) ((-qFit) • v₀ + u₀) = 2 * qFit ∧
      det (a • v + b • u) ((-c) • v + d • u) = a * d + b * c := by
  sorry

/-! ### Unit C — the positive-turn chart and the cuts (sm-3:3959-3987) -/

/-- the signed curvature of a regular curve is the angular speed of its unit tangent:
`det(T, T') = det(γ', γ'')/|γ'|²` -/
theorem det_normalize_deriv {γ : ℝ → Plane} {t : ℝ} (h : ContDiff ℝ ∞ γ) (hreg : deriv γ t ≠ 0) :
    det (normalize (deriv γ t)) (deriv (fun s => normalize (deriv γ s)) t) =
      det (deriv γ t) (deriv (deriv γ) t) / euclideanLength (deriv γ t) ^ 2 := by
  sorry

/-- a `C^∞` unit-vector path on an interval has a `C^∞` tangent-angle lift whose derivative is the
angular speed `det(T, T')` (sm-3:3963-3966 "a continuous strictly increasing lift θ") -/
theorem exists_smooth_lift {T : ℝ → Plane} (hT : ContDiff ℝ ∞ T) (h1 : ∀ t, euclideanLength (T t) = 1)
    (t₀ θ₀ : ℝ) (h0 : T t₀ = (Real.cos θ₀, Real.sin θ₀)) :
    ∃ θ : ℝ → ℝ, ContDiff ℝ ∞ θ ∧ θ t₀ = θ₀ ∧ (∀ t, T t = (Real.cos (θ t), Real.sin (θ t))) ∧
      ∀ t, deriv θ t = det (T t) (deriv T t) := by
  sorry

/-- The positive-turn chart and the cuts, at the preassigned radius `ρ` (sm-3:3959-3987 and
4029-4033 "the disc is fixed first and the cuts afterwards"): the modification disc
`Δ = curlDisc p r`, `r ≤ ρ`, inside `Δ₀`, meeting the curve only in the chart interval
`(a₁, b₁) ⊂ (α, β)` on which the strictly increasing lift `θ` satisfies `|θ − θ(t₀)| < π/2`; the cuts
`s₋ < t₀ < s₊` with `ξ(s₋) = ξ(s₊)`, `p₊ − p₋ = ℓ u`, `ℓ > 0`; the removed arc inside `Δ`; the central
arc strictly above the level `ξ(s₋)`, the retained tails strictly below it; `η` strictly increasing. -/
structure Cuts (S : CurlSite F X) (ρ : ℝ) where
  r : ℝ
  r_pos : 0 < r
  r_le : r ≤ ρ
  disc_sub : curlDisc S.p r ⊆ S.Δ₀
  a₁ : ℝ
  b₁ : ℝ
  α_lt_a₁ : S.α < a₁
  a₁_lt_t₀ : a₁ < S.t₀
  t₀_lt_b₁ : S.t₀ < b₁
  b₁_lt_β : b₁ < S.β
  /-- the disc meets the curve only in the chart interval -/
  disc_meets : ∀ t, F.γ t ∈ curlDisc S.p r → ∃ n : ℤ, t + n ∈ Ioo a₁ b₁
  /-- the lift of the unit tangent on the chart interval … -/
  θ : ℝ → ℝ
  θ_lift : IsLiftOn (fun t => normalize (deriv F.γ t)) θ a₁ b₁
  θ_strictMono : StrictMonoOn θ (Icc a₁ b₁)
  /-- … with `|θ − θ(t₀)| < π/2` ("after shrinking the chart") -/
  θ_bound : ∀ t ∈ Icc a₁ b₁, |θ t - θ S.t₀| < Real.pi / 2
  /-- the cuts -/
  sm : ℝ
  sp : ℝ
  a₁_lt_sm : a₁ < sm
  sm_lt_t₀ : sm < S.t₀
  t₀_lt_sp : S.t₀ < sp
  sp_lt_b₁ : sp < b₁
  /-- "unique cuts `s₋ < 0 < s₊` with `ξ(s₋) = ξ(s₊)`" -/
  ξ_eq : ξ S sm = ξ S sp
  /-- "`p₊ − p₋ = ℓ u`, `ℓ > 0`" -/
  ℓ : ℝ
  ℓ_pos : 0 < ℓ
  chord : F.γ sp - F.γ sm = ℓ • S.u
  /-- the removed arc lies in `Δ` -/
  old_in_disc : ∀ t ∈ Icc sm sp, F.γ t ∈ curlDisc S.p r
  /-- "the central arc lies strictly in `ξ > ξ(s₋)`" -/
  central_above : ∀ t ∈ Ioo sm sp, ξ S sm < ξ S t
  /-- "both retained tails lie strictly in `ξ < ξ(s₋)`" -/
  tails_below : ∀ t ∈ Icc a₁ b₁, t < sm ∨ sp < t → ξ S t < ξ S sm
  /-- "`η` increases throughout" -/
  η_strictMono : StrictMonoOn (η S) (Icc a₁ b₁)
  /-- the tangent coefficients `T₋ = a v + b u`, `T₊ = −c v + d u`, all positive (sm-3:3994-3997) -/
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  d_pos : 0 < d
  T_minus : normalize (deriv F.γ sm) = a • S.v + b • S.u
  T_plus : normalize (deriv F.γ sp) = (-c) • S.v + d • S.u

/-- the cuts exist at every preassigned radius (Unit C) -/
theorem exists_cuts (ρ : ℝ) (hρ : 0 < ρ) : Nonempty (Cuts S ρ) := by
  sorry

/-! ### Unit I — the inserted arc `Φ ∘ c` (sm-3:3987-4043, 4204-4215) -/

/-- The inserted arc at the cuts `K`: `Φ ∘ c` with `x, y` the fit coefficients of `K`, and the facts
the proof establishes about it: same endpoints and endpoint tangent rays as the removed arc, inside
`Δ`, exactly one double point (`t = ±1`, negative with the later branch over), no tangent `u`, exactly
one tangent `−u` (`t = 0`), interior strictly above the level `ξ(s₋)` ("only the model's own double
point is created"), and its compatible tangent lift has increment the old one minus `2π`
(sm-3:3911-3914, 4232-4251 via cf:lem-turnlift (iii)). -/
structure InsertedArc {ρ : ℝ} (K : Cuts S ρ) where
  x : ℝ
  y : ℝ
  x_def : x = xFit K.a K.b K.c K.d
  y_def : y = yFit K.a K.b K.c K.d
  /-- `Φ(b(−2)) = p₋`, `Φ(b(2)) = p₊` -/
  start : insArc (F.γ K.sm) K.ℓ S.u S.v x y (-2) = F.γ K.sm
  stop : insArc (F.γ K.sm) K.ℓ S.u S.v x y 2 = F.γ K.sp
  /-- "the endpoint tangent rays match with positive scale" -/
  ray_start : ∃ r : ℝ, 0 < r ∧ deriv (insArc (F.γ K.sm) K.ℓ S.u S.v x y) (-2) = r • deriv F.γ K.sm
  ray_stop : ∃ r : ℝ, 0 < r ∧ deriv (insArc (F.γ K.sm) K.ℓ S.u S.v x y) 2 = r • deriv F.γ K.sp
  regular : ∀ t ∈ Icc (-2 : ℝ) 2, deriv (insArc (F.γ K.sm) K.ℓ S.u S.v x y) t ≠ 0
  /-- "the whole inserted arc lies in the preassigned disc" -/
  in_disc : ∀ t ∈ Icc (-2 : ℝ) 2, insArc (F.γ K.sm) K.ℓ S.u S.v x y t ∈ curlDisc S.p K.r
  /-- the double point `Φ(0, 0)` at `t = ±1`, negative -/
  double : insArc (F.γ K.sm) K.ℓ S.u S.v x y 1 = insArc (F.γ K.sm) K.ℓ S.u S.v x y (-1)
  double_unique : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
    insArc (F.γ K.sm) K.ℓ S.u S.v x y s = insArc (F.γ K.sm) K.ℓ S.u S.v x y t →
      s = t ∨ (s = 1 ∧ t = -1) ∨ (s = -1 ∧ t = 1)
  det_neg : det (deriv (insArc (F.γ K.sm) K.ℓ S.u S.v x y) 1)
    (deriv (insArc (F.γ K.sm) K.ℓ S.u S.v x y) (-1)) < 0
  /-- (ii) in the model: no tangent `u`, exactly one tangent `−u` -/
  no_u : ∀ t ∈ Icc (-2 : ℝ) 2, normalize (deriv (insArc (F.γ K.sm) K.ℓ S.u S.v x y) t) ≠ S.u
  neg_u_iff : ∀ t ∈ Icc (-2 : ℝ) 2,
    (normalize (deriv (insArc (F.γ K.sm) K.ℓ S.u S.v x y) t) = -S.u ↔ t = 0)
  /-- "the inserted interior lies strictly in `ξ > ξ(s₋)`": transverse excess `(ℓx/12)(4 − t²) > 0` -/
  excess : ∀ t ∈ Ioo (-2 : ℝ) 2,
    planeDot (insArc (F.γ K.sm) K.ℓ S.u S.v x y t - S.p) S.v = ξ S K.sm + K.ℓ * x / 12 * (4 - t ^ 2)
  /-- the compatible lift of the inserted arc and its increment (the old one minus `2π`) -/
  θc : ℝ → ℝ
  θc_lift : IsLiftOn (fun t => normalize (deriv (insArc (F.γ K.sm) K.ℓ S.u S.v x y) t)) θc (-2) 2
  θc_init : θc (-2) = K.θ K.sm
  θc_sweep : θc 2 - θc (-2) = (K.θ K.sp - K.θ K.sm) - 2 * Real.pi

/-- the inserted arc exists at every cut (Unit I) -/
theorem exists_insertedArc {ρ : ℝ} (K : Cuts S ρ) : Nonempty (InsertedArc S K) := by
  sorry

/-! ### Unit G1 — the collar as a graph, the three properties (sm-3:4067-4200) -/

/-- (1) "It is `C^∞`": the collar is smooth for smooth `f`, `g` -/
theorem collar_contDiff {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (e0 : ℝ)
    {lam : ℝ} (hlam : 0 < lam) : ContDiff ℝ ∞ (collar f g e0 lam) := by
  sorry

/-- "`h` agrees with `f` to infinite order at `η₋`": the collar is `f` on the left half-line … -/
theorem collar_eq_left {f g : ℝ → ℝ} {e0 lam t : ℝ} (hlam : 0 < lam) (ht : t ≤ e0) :
    collar f g e0 lam t = f t := by
  sorry

/-- … "and with `g` to infinite order at `η₋ + λ`": it is `g` on the right half-line -/
theorem collar_eq_right {f g : ℝ → ℝ} {e0 lam t : ℝ} (hlam : 0 < lam) (ht : e0 + lam ≤ t) :
    collar f g e0 lam t = g t := by
  sorry

/-- (2) "No tangent of the collar equals `u`, and no smallness condition is needed": with
`0 < f' < g'` and `f ≤ g` on the collar, `h' ≥ f' > 0` pointwise (sm-3:4118-4137) -/
theorem deriv_collar_pos {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {e0 lam : ℝ}
    (hlam : 0 < lam) (hf' : ∀ t ∈ Icc e0 (e0 + lam), 0 < deriv f t)
    (hfg' : ∀ t ∈ Icc e0 (e0 + lam), deriv f t < deriv g t)
    (hfg : ∀ t ∈ Icc e0 (e0 + lam), f t ≤ g t) :
    ∀ t ∈ Icc e0 (e0 + lam), deriv f t ≤ deriv (collar f g e0 lam) t := by
  sorry

/-- (2') the mirrored collar at `p₊`: with `g' < f' < 0` and `f ≤ g`, `h' ≤ f' < 0` (sm-3:4164-4200;
here `collar g f` runs from the inserted arc `g` into the old arc `f`) -/
theorem deriv_collar_neg {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {e0 lam : ℝ}
    (hlam : 0 < lam) (hf' : ∀ t ∈ Icc e0 (e0 + lam), deriv f t < 0)
    (hgf' : ∀ t ∈ Icc e0 (e0 + lam), deriv g t < deriv f t)
    (hfg : ∀ t ∈ Icc e0 (e0 + lam), f t ≤ g t) :
    ∀ t ∈ Icc e0 (e0 + lam), deriv (collar g f e0 lam) t ≤ deriv f t := by
  sorry

/-- (3) "Pointwise `f ≤ h ≤ g` on the collar" -/
theorem collar_between {f g : ℝ → ℝ} {e0 lam t : ℝ} (hfg : f t ≤ g t) :
    f t ≤ collar f g e0 lam t ∧ collar f g e0 lam t ≤ g t := by
  sorry

/-- the collar's tangent angle stays in `(−π/2, 0)` and takes at its ends the angles of the two
arcs: a graph `t ↦ (h t) • v + t • u` with `h' > 0` has unit tangent `≠ ±u` and its lift on the collar
has increment equal to the difference of the endpoint angles (the "lift concatenation" of (3),
sm-3:4150-4158) — stated for any graph with positive slope -/
theorem graph_lift_increment {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (u v : Plane)
    (hu : euclideanLength u = 1) (hvu : v = -Jrot u) {e0 e1 : ℝ} (he : e0 ≤ e1)
    (hpos : ∀ t ∈ Icc e0 e1, 0 < deriv h t) :
    ∃ θ : ℝ → ℝ, IsLiftOn (fun t => normalize (deriv (fun s => (h s) • v + s • u) t)) θ e0 e1 ∧
      (∀ t ∈ Icc e0 e1, normalize (deriv (fun s => (h s) • v + s • u) t) ≠ u ∧
        normalize (deriv (fun s => (h s) • v + s • u) t) ≠ -u) := by
  sorry

/-! ### Unit G2 — the glued loop (sm-3:4044-4200): `F'` -/

/-- The modified loop `F'`: `F` outside the open cut, the inserted arc (reparametrised) in the
middle of the cut, the two collars near the cuts; with the facts the proof establishes: `C^∞` regular
(it is a `SmoothRegularLoop`), inside `Δ` on the cut, exactly one double point on the cut (the
model's, at `s₁ < s₂`, negative), the inserted arc meets the rest of the curve only at its ends, (ii)
on the cut, and the compatible lift with increment the old one minus `2π` ("the total tangent
winding is unchanged by the insertion of the collars", sm-3:4155-4158). -/
structure GluedLoop {ρ : ℝ} (K : Cuts S ρ) where
  ins : InsertedArc S K
  F' : SmoothRegularLoop
  /-- `F' = F` outside the open cut, over one period … -/
  unchanged : ∀ t ∈ Icc K.sp (K.sm + 1), F'.γ t = F.γ t
  /-- … with its velocity -/
  unchanged_deriv : ∀ t ∈ Icc K.sp (K.sm + 1), deriv F'.γ t = deriv F.γ t
  /-- the collar widths -/
  lam : ℝ
  lam' : ℝ
  lam_pos : 0 < lam
  lam'_pos : 0 < lam'
  lam_lt : K.sm + lam < K.sp - lam'
  /-- the middle of the cut is the inserted arc, up to an increasing `C^∞` change of parameter -/
  ψ : ℝ → ℝ
  ψ_smooth : ContDiff ℝ ∞ ψ
  ψ_mono : StrictMonoOn ψ (Icc (K.sm + lam) (K.sp - lam'))
  middle : ∀ t ∈ Icc (K.sm + lam) (K.sp - lam'),
    F'.γ t = insArc (F.γ K.sm) K.ℓ S.u S.v ins.x ins.y (ψ t)
  /-- the inserted sub-arc lies in `Δ` -/
  new_in_disc : ∀ t ∈ Icc K.sm K.sp, F'.γ t ∈ curlDisc S.p K.r
  /-- the double point of the cut: `F'(s₁) = F'(s₂)`, `s₁ < s₂` in the open cut … -/
  s₁ : ℝ
  s₂ : ℝ
  s₁_mem : s₁ ∈ Ioo K.sm K.sp
  s₂_mem : s₂ ∈ Ioo K.sm K.sp
  s₁_lt_s₂ : s₁ < s₂
  double : F'.γ s₁ = F'.γ s₂
  /-- … interior to `Δ` (positive transverse excess, sm-3:4029-4043) … -/
  double_interior : F'.γ s₁ ∈ interior (curlDisc S.p K.r)
  /-- … negative with the later branch over: `det(F'(s₂)', F'(s₁)') < 0` -/
  det_neg : det (deriv F'.γ s₂) (deriv F'.γ s₁) < 0
  /-- … and the only one on the cut -/
  double_unique : ∀ s ∈ Icc K.sm K.sp, ∀ t ∈ Icc K.sm K.sp, F'.γ s = F'.γ t →
    s = t ∨ (s = s₁ ∧ t = s₂) ∨ (s = s₂ ∧ t = s₁)
  /-- "they meet only at the two joins": the open cut meets the rest of the curve nowhere -/
  cut_off_rest : ∀ s ∈ Ioo K.sm K.sp, ∀ t ∈ Icc K.sp (K.sm + 1), F'.γ s ≠ F'.γ t
  /-- (ii) on the cut -/
  no_u : ∀ t ∈ Icc K.sm K.sp, normalize (deriv F'.γ t) ≠ S.u
  one_neg_u : ∃! t, t ∈ Icc K.sm K.sp ∧ normalize (deriv F'.γ t) = -S.u
  /-- the compatible lift of the inserted sub-arc -/
  θ' : ℝ → ℝ
  θ'_lift : IsLiftOn (fun t => normalize (deriv F'.γ t)) θ' K.sm K.sp
  lift_init : θ' K.sm = K.θ K.sm
  sweep_new : θ' K.sp - θ' K.sm = (K.θ K.sp - K.θ K.sm) - 2 * Real.pi

/-- the glued loop exists (Unit G2, from Units I and G1) -/
theorem exists_gluedLoop {ρ : ℝ} (K : Cuts S ρ) (I : InsertedArc S K) :
    ∃ G : GluedLoop S K, G.ins = I := by
  sorry

/-! ### Unit K — the polygonal half: a kink inserted in a disc (FR-C1; the RI site) -/

/-- Kink insertion into a one-component polygonal diagram inside a disc `U` in which it has exactly
one crossing-free arc: the new diagram `X'`, the Reidemeister-I site (accepted `RIData`), the kink
at the prescribed point `q` with prescribed strand directions `d₁` (first passage) and `d₂` (second
passage), the second passage over. -/
structure KinkInsertion (X : Diagram) (U : Set Plane) (a : X.Γ.Arc) (q d₁ d₂ : Plane) where
  X' : Diagram
  ri : RIData U X X'
  /-- the replaced arc is the given one -/
  a_eq : ri.a = a
  kink_point : X'.Γ.crossingPoint ri.kink = q
  first : X'.Γ.Strand
  second : X'.Γ.Strand
  first_mem : first ∈ ri.kink.val
  second_mem : second ∈ ri.kink.val
  first_ne : first ≠ second
  over_second : X'.overStrand ri.kink = second
  dir_first : ∃ r : ℝ, 0 < r ∧ X'.Γ.dir first = r • d₁
  dir_second : ∃ r : ℝ, 0 < r ∧ X'.Γ.dir second = r • d₂
  /-- the first passage precedes the second along the kinked arc -/
  first_before : ri.a'.Before (X'.visitPt ⟨ri.kink, ⟨first, first_mem⟩⟩)
    (X'.visitPt ⟨ri.kink, ⟨second, second_mem⟩⟩)
  /-- the induced map on the occurrences of `X` (over to over, under to under, through the outer
  crossing bijection of the accepted outside match) … -/
  φV : X.Γ.Visit → X'.Γ.Visit
  φV_over : ∀ x : X.OuterCrossing U, φV (X.overVisit x.1) = X'.overVisit (ri.out.ψ x).1
  φV_under : ∀ x : X.OuterCrossing U, φV (X.underVisit x.1) = X'.underVisit (ri.out.ψ x).1
  /-- … every occurrence of `X'` is an old one or one of the two kink occurrences … -/
  φV_surj : ∀ v' : X'.Γ.Visit, (∃ v, φV v = v') ∨
    v' = ⟨ri.kink, ⟨first, first_mem⟩⟩ ∨ v' = ⟨ri.kink, ⟨second, second_mem⟩⟩
  /-- … the cyclic order of the old occurrences is preserved (the accepted `RIData` does not say so;
  the explicit construction does) … -/
  order_old : ∀ v w z : X.Γ.Visit,
    (cycBetween (X.visitCoord v) (X.visitCoord w) (X.visitCoord z) ↔
      cycBetween (X'.visitCoord (φV v)) (X'.visitCoord (φV w)) (X'.visitCoord (φV z)))
  /-- … the kink occurrences sit where the arc `a` was … -/
  order_kink : ∀ v w : X.Γ.Visit,
    (cycBetween (X.visitCoord v) (traversalKey a.start) (X.visitCoord w) ↔
      cycBetween (X'.visitCoord (φV v)) (X'.visitCoord ⟨ri.kink, ⟨first, first_mem⟩⟩)
        (X'.visitCoord (φV w)))
  /-- … consecutively, first then second -/
  order_kink_pair : ∀ v : X.Γ.Visit,
    cycBetween (X'.visitCoord ⟨ri.kink, ⟨first, first_mem⟩⟩)
      (X'.visitCoord ⟨ri.kink, ⟨second, second_mem⟩⟩) (X'.visitCoord (φV v))

/-- the kink insertion exists (Unit K; the polygonal analogue of the smooth construction, all
inside the convex disc `U`, which contains no other strand) -/
theorem exists_kinkInsertion (X : Diagram) (hX : X.Γ.c = 1) {U : Set Plane} (hU : IsDisc U)
    (hclean : Clean U X) {a : X.Γ.Arc} (hcover : X.Γ.ArcCover U {a})
    (hno : ∀ x : X.Γ.Crossing, X.Γ.crossingPoint x ∉ U) {q : Plane} (hq : q ∈ interior U)
    {d₁ d₂ : Plane} (hd : det d₂ d₁ ≠ 0) : Nonempty (KinkInsertion X U a q d₁ d₂) := by
  sorry

/-- the outer crossings of a Reidemeister-I site keep their double points (from the accepted
`OutsideMatch`: `eval_eq` at the over occurrence) -/
theorem _root_.SM.Link.RIData.crossingPoint_ψ {U : Set Plane} {D D' : Diagram} (h : RIData U D D')
    (x : D.OuterCrossing U) : D'.Γ.crossingPoint (h.out.ψ x).1 = D.Γ.crossingPoint x.1 := by
  sorry

/-- the outer crossings of a Reidemeister-I site keep their signs (from `dir_pos` at both
occurrences, the crossing point being strictly outside `U` by `Clean`) -/
theorem _root_.SM.Link.RIData.sign_ψ {U : Set Plane} {D D' : Diagram} (h : RIData U D D') (x : D.OuterCrossing U) :
    D'.sign (h.out.ψ x).1 = D.sign x.1 := by
  sorry

/-- the writhe of a Reidemeister-I site: the outer crossings correspond with the same signs and the
kink is the only inner one -/
theorem _root_.SM.Link.RIData.writhe_eq {U : Set Plane} {D D' : Diagram} (h : RIData U D D') :
    D'.writhe = D.writhe + (D'.sign h.kink : ℤ) := by
  sorry

/-! ### Unit R — the record: `X'` is carried by `F'` -/

/-- The carried record of the modified diagram, with the facts the assembly needs: the outer
crossings keep their smooth signs, the kink is negative, the smooth writhe drops by one. -/
structure CarriedKink {ρ : ℝ} (K : Cuts S ρ) (G : GluedLoop S K)
    (Kk : KinkInsertion X S.Δ₀ S.arc0 (G.F'.γ G.s₁) (deriv G.F'.γ G.s₁) (deriv G.F'.γ G.s₂)) where
  carried' : Carried G.F' Kk.X'
  signs_outside : ∀ x : X.OuterCrossing S.Δ₀,
    carried'.smoothSign (Kk.ri.out.ψ x).1 = S.carried.smoothSign x.1
  kink_negative : carried'.smoothSign Kk.ri.kink = -1
  writhe_eq : carried'.smoothWrithe = S.carried.smoothWrithe - 1

/-- the record exists (Unit R): occurrences of `X` at their old parameters (`F' = F` there), the kink
occurrences at `s₁ < s₂`; `Carried.order` from `compat` and the position of the kinked arc;
`sign_eq` from `dir_first`/`dir_second`/`over_second` and `det_neg` -/
theorem exists_carriedKink {ρ : ℝ} (K : Cuts S ρ) (G : GluedLoop S K)
    (Kk : KinkInsertion X S.Δ₀ S.arc0 (G.F'.γ G.s₁) (deriv G.F'.γ G.s₁) (deriv G.F'.γ G.s₂)) :
    Nonempty (CarriedKink S K G Kk) := by
  sorry

/-! ### Unit T — the rotation (sm-3:4232-4251 through cf:lem-turnlift (iii-b)) -/

/-- Arc replacement on a cut: if `F'` agrees with `F` (with velocity) on `[s₊, s₋ + 1]`, then
`rot F' − rot F = (Δ' − Δ)/2π` for tangent lifts on the cut — the accepted
`rot_sub_rot_of_replace` after a seam shift to `s₋` (`tw_shift`), with `ψ = id` on the common arc -/
theorem rot_sub_of_cut (F F' : SmoothRegularLoop) {sm sp : ℝ} (h : sm < sp) (h1 : sp < sm + 1)
    (hunch : ∀ t ∈ Icc sp (sm + 1), F'.γ t = F.γ t)
    (hderiv : ∀ t ∈ Icc sp (sm + 1), deriv F'.γ t = deriv F.γ t) {θ θ' : ℝ → ℝ}
    (hθ : IsLiftOn (fun t => normalize (deriv F.γ t)) θ sm sp)
    (hθ' : IsLiftOn (fun t => normalize (deriv F'.γ t)) θ' sm sp) :
    F'.toClosedC1Curve.rot - F.toClosedC1Curve.rot =
      ((θ' sp - θ' sm) - (θ sp - θ sm)) / (2 * Real.pi) := by
  sorry

/-! ### Unit X — the global clauses from the pieces -/

/-- (i) the double points outside `Δ` are unchanged: outside the cut `F' = F`, the cut lies in `Δ`,
and the old arc through `Δ` carried no double point -/
theorem doubles_outside_of_pieces {ρ : ℝ} (K : Cuts S ρ) (G : GluedLoop S K) :
    ∀ q, q ∉ curlDisc S.p K.r →
      (q ∈ SmoothRegularLoop.doublePoints G.F'.γ ↔ q ∈ SmoothRegularLoop.doublePoints F.γ) := by
  sorry

/-- (iii) the double points of `F'` in `Δ` are exactly the kink point -/
theorem double_in_disc_iff_of_pieces {ρ : ℝ} (K : Cuts S ρ) (G : GluedLoop S K) :
    ∀ q ∈ curlDisc S.p K.r, (q ∈ SmoothRegularLoop.doublePoints G.F'.γ ↔ q = G.F'.γ G.s₁) := by
  sorry

/-- (ii) no tangent `u` in `Δ`: on the cut by `GluedLoop.no_u`, on the retained tails because the
lift is strictly monotone with `|θ − θ(t₀)| < π/2` and `t₀` is removed -/
theorem no_tangent_u_of_pieces {ρ : ℝ} (K : Cuts S ρ) (G : GluedLoop S K) :
    ∀ t, G.F'.γ t ∈ curlDisc S.p K.r → normalize (deriv G.F'.γ t) ≠ S.u := by
  sorry

/-- (ii) exactly one tangent `−u` in `Δ` (one parameter of the fundamental period): the one of the
cut; the retained tails have angles in `(−π/2, π/2)` about `u` -/
theorem one_tangent_neg_u_of_pieces {ρ : ℝ} (K : Cuts S ρ) (G : GluedLoop S K) :
    ∃! t, t ∈ Ico (0 : ℝ) 1 ∧ G.F'.γ t ∈ curlDisc S.p K.r ∧ normalize (deriv G.F'.γ t) = -S.u := by
  sorry

end Curl

/-! ## 7. Assembly: the witness from the chain -/

namespace Curl

open Set

variable {F : SmoothRegularLoop} {X : Diagram} (S : CurlSite F X)

section assembly

variable {ρ : ℝ} (K : Cuts S ρ) (G : GluedLoop S K)

/-- the kink-insertion data for the double point of `G` -/
theorem exists_kink_of_glued : Nonempty (KinkInsertion X S.Δ₀ S.arc0 (G.F'.γ G.s₁)
    (deriv G.F'.γ G.s₁) (deriv G.F'.γ G.s₂)) := by
  refine exists_kinkInsertion X S.carried.one S.Δ₀_disc S.Δ₀_clean S.Δ₀_cover ?_ ?_ ?_
  · intro x hx
    exact S.Δ₀_no_crossing x hx
  · exact interior_mono K.disc_sub G.double_interior
  · exact ne_of_lt G.det_neg

/-- restriction of an interval lift to a sub-interval -/
theorem _root_.SM.IsLiftOn.mono {T : ℝ → Plane} {θ : ℝ → ℝ} {a b a' b' : ℝ} (h : IsLiftOn T θ a b)
    (ha : a ≤ a') (hb : b' ≤ b) : IsLiftOn T θ a' b' :=
  ⟨h.1.mono (Icc_subset_Icc ha hb), fun s hs => h.2 s (Icc_subset_Icc ha hb hs)⟩

/-- the witness assembled from the chain -/
noncomputable def witness
    (Kk : KinkInsertion X S.Δ₀ S.arc0 (G.F'.γ G.s₁) (deriv G.F'.γ G.s₁) (deriv G.F'.γ G.s₂))
    (R : CarriedKink S K G Kk) : CurlWitness S ρ where
  F' := G.F'
  X' := Kk.X'
  carried' := R.carried'
  r := K.r
  r_pos := K.r_pos
  r_le := K.r_le
  disc_isDisc := isDisc_curlDisc S.p K.r_pos
  p_in_disc := mem_interior_curlDisc S.p K.r_pos
  disc_sub := K.disc_sub
  disc_meets_arc := by
    intro t ht
    obtain ⟨n, hn⟩ := K.disc_meets t ht
    exact ⟨n, lt_trans K.α_lt_a₁ hn.1, lt_trans hn.2 K.b₁_lt_β⟩
  sm := K.sm
  sp := K.sp
  α_lt_cut := lt_trans K.α_lt_a₁ K.a₁_lt_sm
  cut_lt_t₀ := K.sm_lt_t₀
  t₀_lt_cut := K.t₀_lt_sp
  cut_lt_β := lt_trans K.sp_lt_b₁ K.b₁_lt_β
  old_in_disc := K.old_in_disc
  new_in_disc := G.new_in_disc
  unchanged := G.unchanged
  unchanged_deriv := G.unchanged_deriv
  θ := K.θ
  θ_lift := K.θ_lift.mono K.a₁_lt_sm.le K.sp_lt_b₁.le
  θ_strictMono := K.θ_strictMono.mono (Icc_subset_Icc K.a₁_lt_sm.le K.sp_lt_b₁.le)
  sweep_old_pos := by
    have hsm : K.sm ∈ Icc K.a₁ K.b₁ := ⟨K.a₁_lt_sm.le, (lt_trans K.sm_lt_t₀ K.t₀_lt_sp).le.trans K.sp_lt_b₁.le⟩
    have hsp : K.sp ∈ Icc K.a₁ K.b₁ := ⟨K.a₁_lt_sm.le.trans (lt_trans K.sm_lt_t₀ K.t₀_lt_sp).le, K.sp_lt_b₁.le⟩
    have := K.θ_strictMono hsm hsp (lt_trans K.sm_lt_t₀ K.t₀_lt_sp)
    linarith
  sweep_old_lt_pi := by
    have hsm : K.sm ∈ Icc K.a₁ K.b₁ := ⟨K.a₁_lt_sm.le, (lt_trans K.sm_lt_t₀ K.t₀_lt_sp).le.trans K.sp_lt_b₁.le⟩
    have hsp : K.sp ∈ Icc K.a₁ K.b₁ := ⟨K.a₁_lt_sm.le.trans (lt_trans K.sm_lt_t₀ K.t₀_lt_sp).le, K.sp_lt_b₁.le⟩
    have h1 := K.θ_bound K.sm hsm
    have h2 := K.θ_bound K.sp hsp
    rw [abs_lt] at h1 h2
    linarith
  θ' := G.θ'
  θ'_lift := G.θ'_lift
  lift_init := G.lift_init
  sweep_new := G.sweep_new
  ri := Kk.ri
  kink_point := by
    rw [Kk.kink_point]
    exact G.new_in_disc G.s₁ ⟨G.s₁_mem.1.le, G.s₁_mem.2.le⟩
  P_eq := P_reidemeister_I ⟨S.Δ₀, Or.inr ⟨Kk.ri⟩⟩
  doubles_outside := doubles_outside_of_pieces S K G
  points_outside := fun x => Kk.ri.crossingPoint_ψ x
  signs_outside := R.signs_outside
  no_tangent_u := no_tangent_u_of_pieces S K G
  one_tangent_neg_u := one_tangent_neg_u_of_pieces S K G
  double_in_disc_iff := by
    intro q hq
    rw [Kk.kink_point]
    exact double_in_disc_iff_of_pieces S K G q hq
  kink_negative := R.kink_negative
  rot_eq := by
    have h := rot_sub_of_cut F G.F' (lt_trans K.sm_lt_t₀ K.t₀_lt_sp) ?_ G.unchanged G.unchanged_deriv
      (K.θ_lift.mono K.a₁_lt_sm.le K.sp_lt_b₁.le) G.θ'_lift
    · rw [G.sweep_new] at h
      have hpi : (2 * Real.pi) ≠ 0 := by positivity
      have : (K.θ K.sp - K.θ K.sm - 2 * Real.pi - (K.θ K.sp - K.θ K.sm)) / (2 * Real.pi) = -1 := by
        field_simp
        ring
      rw [this] at h
      linarith
    · have h1 : K.sp < S.β := lt_trans K.sp_lt_b₁ K.b₁_lt_β
      have h2 : S.α < K.sm := lt_trans K.α_lt_a₁ K.a₁_lt_sm
      have h3 := S.arc_short
      linarith
  writhe_eq := R.writhe_eq

end assembly

/-- the existence sentence from the chain -/
theorem exists_witness (ρ : ℝ) (hρ : 0 < ρ) : Nonempty (CurlWitness S ρ) := by
  obtain ⟨K⟩ := exists_cuts S ρ hρ
  obtain ⟨I⟩ := exists_insertedArc S K
  obtain ⟨G, -⟩ := exists_gluedLoop S K I
  obtain ⟨Kk⟩ := exists_kink_of_glued S K G
  obtain ⟨R⟩ := exists_carriedKink S K G Kk
  exact ⟨witness S K G Kk R⟩

end Curl

/-! ## 8. The row from the chain -/

/-- cf:lem-curl, assembled from the chain (§6-§7): the clause fields are projections of
`CurlWitness` (`CurlData.of_exists`). -/
theorem cf_lem_curl : CurlData :=
  CurlData.of_exists fun _ _ S ρ hρ => Curl.exists_witness S ρ hρ

end

end SM

#print axioms SM.cf_lem_curl
