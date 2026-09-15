import SM.FrontSmooth
import SM.TurnLift
import SM.LinkDiagramRecord
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # SM cf:lem-rounding (row 97) — FIXED-STATEMENT candidate B (proof-first architecture)

Source: reference/SM/sm-3-statesum.tex:3644-3700 (statement), 3701-3869 (proof).  Design record:
work/drafts/rounding/PLAN_B.md.  Architect B, 2026-09-14.

## Printed statement (sm-3:3644-3657, verbatim modulo notation)

"Let L be a closed polygon with corners q₁,…,q_c, and let D be an oriented diagram whose underlying
plane curve is L — L together with an over/under assignment at each of its double points. Assume the
principal turns of L all exist and are *nonzero*; that L has finitely many double points, all
transversal, none of them a corner; and that no corner of L lies on an edge of L other than the two
incident to it. Then there is a *clearance* ε₀(L) > 0 such that for every ε ∈ (0, ε₀(L)) there is a
C^∞ regular closed plane curve L_ε, and a diagram D_ε carried by it, with these properties [(a)–(e)]."

## Model decisions (fidelity argument per clause in PLAN_B.md §1)

* **The polygon and its diagram.** `L : LabelledTuple n` (def:polygon, `3 ≤ n`) and `D : Diagram`
  (the accepted polygonal oriented-diagram class, SM/LinkDiagram.lean) with
  `D.Γ = Shadow.single ⟨n, hn, L⟩`: "an oriented diagram whose underlying plane curve is L".  The
  printed hypotheses "finitely many double points, all transversal, none a corner; no corner on a
  non-incident edge" are exactly the genericity clauses of `D.generic : D.Γ.Generic` (`transverse`,
  `tail_off`, `no_triple`; finiteness is automatic for finitely many edges), and "the principal turns
  all exist" is `Generic.regular`; the only hypothesis not carried by `Diagram` is "nonzero", taken
  as `∀ i, principalTurn L i ≠ 0`.  (PLAN_B.md §1, H-1.)
* **The smooth curve.** "C^∞ regular closed plane curve" = a `SmoothLoop` (SM/FrontSmooth.lean:
  `ContDiff ℝ ∞`, 1-periodic — the accepted FR-3 reading of "smooth") whose velocity never vanishes:
  `SmoothRegularLoop`.  Its rotation is that of the accepted `ClosedC1Curve` it induces
  (`SmoothLoop.toClosedC1Curve`, SM/TurningNumber.lean) — no second notion of `rot`.
* **The carried diagram (FR-1).** "a diagram D_ε carried by L_ε": D_ε is a *polygonal* `Diagram`
  read on the smooth curve through a carrying record `Carries γ D_ε` (the one-component analogue of
  the accepted `SmoothFront.Marking`: occurrences ↔ parameters, positions, strand directions, cyclic
  order; over/under bits and signs are those of the polygonal diagram).  Here D_ε := D itself, which is
  what clause (c) asserts ("the same double points, the same strands, the same over/under assignment
  and hence the same crossing signs and the same writhe") and what the consumer
  cf:thm-carrierfloor(C) reads ("the rounded diagram and the original polygonal diagram have the same
  named record", sm-3:4430-4432).  This is the accepted layer's reading of every smooth diagram
  (AUTHOR_NOTES "Front block: representation adopted", FR-1).
* **The construction is named.** The witnesses are explicit definitions — `roundedCurve L ε`
  (the printed junction `γ_ℓ` at every corner, glued to the straight edges) and `clearance L`
  (the printed `ε₀(L) = ⅓ min{η_v, η_e, η_ℓ, η_X}`) — because cf:thm-carrierfloor(A) (sm-3:4291-4303)
  reads this lemma's proof as returning *one* curve and *one* diagram `Round(L, D, ε)`.  The bundle
  `RoundingData` has one field per printed clause about these witnesses; the printed existential form
  is the corollary `RoundingData.printed` below (proved here, no sorry).
* **Clause (b)** is read on the explicit tangent-angle lift `θ_i(t) = θ_{u_i} + ϑ_i φ(σ/ℓ_i)` of the
  unit tangent on the junction interval (the printed formula, sm-3:3688-3690), with the accepted
  `IsLiftOn` (SM/TurnLift.lean): strict monotonicity in the sense of `sgn ϑ_i`, increment exactly
  `ϑ_i`, values within the swept arc ("and no more"), each angle of the arc at exactly one parameter,
  the unit-tangent map injective, `deriv θ ≠ 0` on the open junction interval (immersion), all
  derivatives of `θ` of order ≥ 1 vanishing at the two ends and all derivatives of the curve of order
  ≥ 2 vanishing there (flat to infinite order); the parameter is arclength rescaled to period 1
  (constant speed `total L ε`).
* **Clause (e)** uses the round closed disc `roundDisc (L k) ε` (Euclidean length) and the accepted
  `IsDisc` (SM/LinkMoves.lean, the clean-disc vocabulary).

## Printed → Lean

| printed | Lean |
|---|---|
| φ(t) = f(t)/(f(t)+f(1−t)), f(t) = e^{−1/t} (t>0), 0 (t≤0) | `profile := Real.smoothTransition` (Mathlib: `expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))`, definitionally the printed formula) |
| u = δ_{i−1}/|δ_{i−1}|, v = δ_i/|δ_i| | `cornerIn L k`, `cornerOut L k` (`normalize (edge L (k-1))`, `normalize (edge L k)`) |
| ϑ_i | `cornerTurn L k := principalTurn L k` |
| θ_u (an argument of u) | `cornerArg L k := (planeComplex (edge L (k-1))).arg`; along the traversal `cumArg L k = θ_{u_0} + Σ_{j<k} ϑ_j` (an argument of `cornerIn L k`) |
| A₀ = q_i − εu, A₁ = q_i + εv | `A0 L ε k`, `A1 L ε k` |
| tangent angle θ_u + ϑ_i φ(σ/ℓ) | `junctionAngle θ₀ ϑ ℓ σ` |
| γ_ℓ(s) = A₀ + ∫₀^s (cos, sin)(θ_u + ϑ_i φ(t/ℓ)) dt | `junctionCurve A₀ θ₀ ϑ ℓ s` |
| m(φ), ℓ = ε|u+v|/|m(φ)| | `junctionMean θ₀ ϑ`, `junctionLength ε θ₀ ϑ` |
| the rounded curve L_ε (arclength σ, period Λ, rescaled to period 1) | `roundedArc L ε σ`, `roundedCurve L ε t := roundedArc L ε (Λ · fract t)` with `Λ = total L ε` |
| the junction at q_i, parameters | `Icc (jStart L ε k) (jEnd L ε k)`; the straight part along edge k: `Icc (jEnd L ε k) (jStart L ε (k+1))` |
| ε₀(L) = ⅓ min{η_v, η_e, η_ℓ, η_X} | `clearance L := ⅓ · sInf (clearanceSet L)` (the four finite families of distances, with the harmless cap 1 so that an empty family reads as "+∞") |
| disc of radius ε about q_i | `roundDisc (L k) ε` |
| D_ε carried by L_ε | `Carries (roundedCurve L ε) D` |

Reuse (grep-verified, see PLAN_B.md §3): `SmoothLoop`, `SmoothLoop.toClosedC1Curve` (SM/FrontSmooth),
`ClosedC1Curve`, `rot`, `normalize`, `euclideanLength`, `planeComplex` (SM/TurningNumber,
SM/EuclideanPlane), `IsLiftOn` and `rot_eq_rotationNumber_of_rounding` (SM/TurnLift), `principalTurn`,
`Regular`, `rotationNumber` (SM/RegularLocus, SM/RotationNumber), `edge`, `edgeSegment`, `incident`
(SM/Polygon), `Crossing`, `crossingPoint` (SM/Crossings), `Diagram`, `Shadow.single`, `Shadow.dir`,
`Shadow.seg`, `Shadow.crossingPoint`, `Diagram.sign`, `Diagram.writhe`, `Diagram.overVisit`,
`Diagram.underVisit` (SM/LinkDiagram), `Diagram.visitCoord` (SM/LinkDiagramRecord), `IsDisc`
(SM/LinkMoves). -/

namespace SM

open Link Set
open scoped ContDiff

noncomputable section

namespace Rounding

/-! ## 0. Plane vocabulary -/

/-- The unit vector of angle `θ`: `(cos θ, sin θ)`. -/
def unitDir (θ : ℝ) : Plane := (Real.cos θ, Real.sin θ)

/-- "the disc of radius `r` about `q`": the closed round disc, in the Euclidean length of the
accepted plane (`euclideanLength`, SM/EuclideanPlane.lean; note `Plane = ℝ × ℝ` carries the sup
metric, so `Metric.closedBall` would be a square). -/
def roundDisc (q : Plane) (r : ℝ) : Set Plane := {x | euclideanLength (x - q) ≤ r}

/-- A double point of a 1-periodic curve, as an ordered pair of distinct parameters of the
fundamental period with the same image. -/
def IsDoublePt (γ : ℝ → Plane) (s t : ℝ) : Prop :=
  s ∈ Ico (0 : ℝ) 1 ∧ t ∈ Ico (0 : ℝ) 1 ∧ s ≠ t ∧ γ s = γ t

/-! ## 1. C^∞ regular closed plane curves -/

/-- "a C^∞ regular closed plane curve": a `SmoothLoop` (SM/FrontSmooth.lean: `C^∞`, 1-periodic)
whose velocity never vanishes. -/
structure SmoothRegularLoop extends SmoothLoop where
  /-- regular: `γ' ≠ 0` everywhere -/
  regular : ∀ t, deriv γ t ≠ 0

/-- The accepted closed `C¹` regular curve of a `C^∞` regular loop (SM/TurningNumber.lean), whose
`rot` is the rotation of cf:def-turning. -/
def SmoothRegularLoop.toClosedC1Curve (c : SmoothRegularLoop) : ClosedC1Curve :=
  c.toSmoothLoop.toClosedC1Curve c.regular

@[simp] theorem SmoothRegularLoop.toClosedC1Curve_γ (c : SmoothRegularLoop) :
    c.toClosedC1Curve.γ = c.γ := rfl

/-! ## 2. A diagram carried by a smooth closed curve (FR-1) -/

/-- "a diagram `D` carried by" the closed curve `γ` (1-periodic): the one-component polygonal
`Diagram D` (SM/LinkDiagram.lean) read on the smooth curve — the one-component analogue of the
accepted `SmoothFront.Marking` (SM/FrontSmooth.lean, FR-1).  Each crossing occurrence `v` of `D`
(a crossing together with one of its two strands) is met by `γ` at a parameter `par v` of the
fundamental period: there `γ` is at the crossing point and runs in the direction of the strand;
every double point of `γ` arises this way from the two occurrences of one crossing; and the cyclic
order of the occurrences along `γ` is that of `D` (`visitCoord`, SM/LinkDiagramRecord.lean).  The
over/under bits are those of `D` (`D.overStrand`), read on the curve as: the over branch at the
crossing `x` is the branch through `par (D.overVisit x)`; the crossing signs and the writhe of the
carried diagram are `Carries.sign`, `Carries.writhe` below. -/
structure Carries (γ : ℝ → Plane) (D : Diagram) where
  /-- one component -/
  one_component : D.Γ.c = 1
  /-- the parameter of each crossing occurrence -/
  par : D.Γ.Visit → ℝ
  /-- in the fundamental period -/
  par_mem : ∀ v, par v ∈ Ico (0 : ℝ) 1
  /-- the curve is at the crossing point -/
  par_eval : ∀ v, γ (par v) = D.Γ.crossingPoint v.1
  /-- and runs in the direction of the occurrence's strand -/
  par_dir : ∀ v, ∃ r : ℝ, 0 < r ∧ deriv γ (par v) = r • D.Γ.dir v.2.1
  /-- distinct occurrences, distinct parameters -/
  par_injective : Function.Injective par
  /-- every double point of the curve is a crossing of `D`: its two parameters are the parameters of
  the two occurrences of one crossing -/
  double_par : ∀ s t, IsDoublePt γ s t →
    ∃ v w : D.Γ.Visit, v.1 = w.1 ∧ v ≠ w ∧ par v = s ∧ par w = t
  /-- the cyclic order of the occurrences along the curve is that of the diagram -/
  par_order : ∀ v w, D.visitCoord v < D.visitCoord w ↔ par v < par w

namespace Carries

variable {γ : ℝ → Plane} {D : Diagram}

/-- The crossing sign of the carried diagram at `x`: the over-first tangent determinant sign of the
smooth branches, `sgn det(γ'(over), γ'(under))` (def:positive-lift, sm-3:328-331). -/
def sign (rec : Carries γ D) (x : D.Γ.Crossing) : SignType :=
  SignType.sign (det (deriv γ (rec.par (D.overVisit x))) (deriv γ (rec.par (D.underVisit x))))

/-- The writhe of the carried diagram: the sum of its crossing signs. -/
def writhe (rec : Carries γ D) : ℤ := ∑ x : D.Γ.Crossing, (rec.sign x : ℤ)

end Carries

/-! ## 3. The construction (sm-3:3701-3742): profile, junction, corner data, clearance -/

/-- "the transition profile φ(t) = f(t)/(f(t)+f(1−t)), f(t) = e^{−1/t} (t > 0), 0 (t ≤ 0)"
(sm-3:3705-3710): Mathlib's `Real.smoothTransition`, which is definitionally
`expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))` with
`expNegInvGlue x = if x ≤ 0 then 0 else exp (-x⁻¹)`. -/
def profile : ℝ → ℝ := Real.smoothTransition

/-- The tangent angle along a junction of length `ℓ` from the direction of angle `θ₀`, turning by
`ϑ`: `θ₀ + ϑ φ(σ/ℓ)` (sm-3:3689-3690, 3738). -/
def junctionAngle (θ₀ ϑ ℓ σ : ℝ) : ℝ := θ₀ + ϑ * profile (σ / ℓ)

/-- The unit tangent of the junction. -/
def junctionTangent (θ₀ ϑ ℓ σ : ℝ) : Plane := unitDir (junctionAngle θ₀ ϑ ℓ σ)

/-- `m(φ) = ∫₀¹ (cos(θ_u + ϑφ), sin(θ_u + ϑφ)) dt` (sm-3:3764-3765). -/
def junctionMean (θ₀ ϑ : ℝ) : Plane :=
  (∫ t in (0 : ℝ)..1, Real.cos (θ₀ + ϑ * profile t),
   ∫ t in (0 : ℝ)..1, Real.sin (θ₀ + ϑ * profile t))

/-- The junction length `ℓ = ε |u+v| / |m(φ)|` (sm-3:3770-3771), with `u = (cos θ₀, sin θ₀)` and
`v = (cos (θ₀+ϑ), sin (θ₀+ϑ))`. -/
def junctionLength (ε θ₀ ϑ : ℝ) : ℝ :=
  ε * euclideanLength (unitDir θ₀ + unitDir (θ₀ + ϑ)) / euclideanLength (junctionMean θ₀ ϑ)

/-- The junction arc `γ_ℓ(s) = A₀ + ∫₀^s (cos, sin)(θ_u + ϑ φ(t/ℓ)) dt` (sm-3:3738-3742), defined for
every real `s` (for `s ≤ 0` it is the straight line of direction `u` through `A₀`, for `s ≥ ℓ` the
straight line of direction `v` through `γ_ℓ(ℓ)`). -/
def junctionCurve (A₀ : Plane) (θ₀ ϑ ℓ σ : ℝ) : Plane :=
  (A₀.1 + ∫ τ in (0 : ℝ)..σ, Real.cos (junctionAngle θ₀ ϑ ℓ τ),
   A₀.2 + ∫ τ in (0 : ℝ)..σ, Real.sin (junctionAngle θ₀ ϑ ℓ τ))

variable {n : ℕ} [NeZero n]

/-- `ϑ_k`, the principal turn at the corner `q_k = L k` (between the edges `k−1` and `k`). -/
def cornerTurn (L : LabelledTuple n) (k : ℕ) : ℝ := principalTurn L (k : ZMod n)

/-- `u = δ_{k−1}/|δ_{k−1}|`, the unit direction of the edge arriving at `q_k`. -/
def cornerIn (L : LabelledTuple n) (k : ℕ) : Plane := normalize (edge L ((k : ZMod n) - 1))

/-- `v = δ_k/|δ_k|`, the unit direction of the edge leaving `q_k`. -/
def cornerOut (L : LabelledTuple n) (k : ℕ) : Plane := normalize (edge L (k : ZMod n))

/-- `θ_u`, an argument of the arriving direction `u` at `q_k`. -/
def cornerArg (L : LabelledTuple n) (k : ℕ) : ℝ := (planeComplex (edge L ((k : ZMod n) - 1))).arg

/-- The tangent angle carried along the traversal to the corner `q_k`: `θ_{u_0} + Σ_{j<k} ϑ_j`, an
argument of `cornerIn L k` (each junction turns by `ϑ_j`, each straight edge by `0`). -/
def cumArg (L : LabelledTuple n) (k : ℕ) : ℝ :=
  cornerArg L 0 + ∑ j ∈ Finset.range k, cornerTurn L j

/-- `|δ_k|`, the length of the edge `k`. -/
def edgeLen (L : LabelledTuple n) (k : ℕ) : ℝ := euclideanLength (edge L (k : ZMod n))

/-- `A₀ = q_k − ε u` (sm-3:3703). -/
def A0 (L : LabelledTuple n) (ε : ℝ) (k : ℕ) : Plane := L (k : ZMod n) - ε • cornerIn L k

/-- `A₁ = q_k + ε v` (sm-3:3703). -/
def A1 (L : LabelledTuple n) (ε : ℝ) (k : ℕ) : Plane := L (k : ZMod n) + ε • cornerOut L k

/-- `ℓ_k`, the length of the junction at `q_k`. -/
def arcLen (L : LabelledTuple n) (ε : ℝ) (k : ℕ) : ℝ :=
  junctionLength ε (cumArg L k) (cornerTurn L k)

/-- Arclength bookkeeping: `cum L ε k` is the arclength at which the junction at `q_k` begins
(the junction at `q_0` begins at `0`); the junction occupies `[cum k, cum k + ℓ_k]` and the straight
part along the edge `k` (of length `|δ_k| − 2ε`) follows. -/
def cum (L : LabelledTuple n) (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => cum L ε k + arcLen L ε k + (edgeLen L k - 2 * ε)

/-- The arclength at which the junction at `q_k` ends. -/
def cumEnd (L : LabelledTuple n) (ε : ℝ) (k : ℕ) : ℝ := cum L ε k + arcLen L ε k

/-- `Λ`, the total length of the rounded curve. -/
def total (L : LabelledTuple n) (ε : ℝ) : ℝ := cum L ε n

/-- The tangent angle of the rounded curve as a function of arclength `σ`:
`θ_{u_0} + Σ_k ϑ_k φ((σ − cum k)/ℓ_k)`; on the junction at `q_k` it is `cumArg L k + ϑ_k φ(…)`
(the earlier profiles are `1`, the later ones `0`), on the straight parts it is constant. -/
def globalAngle (L : LabelledTuple n) (ε σ : ℝ) : ℝ :=
  cornerArg L 0 + ∑ k ∈ Finset.range n, cornerTurn L k * profile ((σ - cum L ε k) / arcLen L ε k)

/-- The rounded curve by arclength: `A₀(q_0) + ∫₀^σ (cos, sin)(globalAngle)`. -/
def roundedArc (L : LabelledTuple n) (ε σ : ℝ) : Plane :=
  ((A0 L ε 0).1 + ∫ τ in (0 : ℝ)..σ, Real.cos (globalAngle L ε τ),
   (A0 L ε 0).2 + ∫ τ in (0 : ℝ)..σ, Real.sin (globalAngle L ε τ))

/-- **The rounded curve `L_ε`** (period 1; the parameter `t` is arclength divided by `Λ`). -/
def roundedCurve (L : LabelledTuple n) (ε t : ℝ) : Plane :=
  roundedArc L ε (total L ε * Int.fract t)

/-- The parameter at which the junction at `q_k` begins. -/
def jStart (L : LabelledTuple n) (ε : ℝ) (k : ℕ) : ℝ := cum L ε k / total L ε

/-- The parameter at which the junction at `q_k` ends. -/
def jEnd (L : LabelledTuple n) (ε : ℝ) (k : ℕ) : ℝ := cumEnd L ε k / total L ε

/-- The printed tangent-angle lift on the junction at `q_k` (sm-3:3688-3690), in the period-1
parameter: `θ_u + ϑ_k φ(σ/ℓ_k)` with `σ = Λ t − cum k`. -/
def junctionLift (L : LabelledTuple n) (ε : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  cumArg L k + cornerTurn L k * profile ((total L ε * t - cum L ε k) / arcLen L ε k)

/-- The four families of distances of the clearance (sm-3:3819-3826): `η_v` (distances between
distinct corners), `η_e` (distance from a corner to a non-incident closed edge; `Metric.infDist` in
the sup metric of `Plane`, which is at most the Euclidean distance), `η_ℓ` (edge lengths), `η_X`
(distances from corners to double points).  The element `1` caps the minimum so that an empty family
("min over an empty index set is +∞", sm-3:3829) is harmless. -/
def clearanceSet (L : LabelledTuple n) : Set ℝ :=
  {1} ∪ range (fun p : {p : ZMod n × ZMod n // p.1 ≠ p.2} => euclideanLength (L p.1.2 - L p.1.1))
    ∪ range (fun p : {p : ZMod n × ZMod n // ¬ incident p.1 p.2} =>
        Metric.infDist (L p.1.1) (edgeSegment L p.1.2))
    ∪ range (fun k : ZMod n => euclideanLength (edge L k))
    ∪ range (fun p : ZMod n × Crossing L => euclideanLength (crossingPoint p.2 - L p.1))

/-- **The clearance `ε₀(L) = ⅓ min{η_v, η_e, η_ℓ, η_X}`** (sm-3:3827-3828). -/
def clearance (L : LabelledTuple n) : ℝ := (1 / 3) * sInf (clearanceSet L)

/-! ## 4. The five printed clauses, for a curve `γ` at the data `(L, D, ε)` -/

/-- **(a)** "`L_ε` coincides with `L` outside the union of the discs of radius `ε` about the corners":
on the straight parameter interval of the edge `k` the curve is the arclength traversal of that edge
from `A₁(q_k)` to `A₀(q_{k+1})`, and the trace of `L_ε` outside the discs is the trace of `L` outside
the discs. -/
def ClauseA (L : LabelledTuple n) (ε : ℝ) (γ : ℝ → Plane) : Prop :=
  (∀ k < n, ∀ t ∈ Icc (jEnd L ε k) (jStart L ε (k + 1)),
    γ t = A1 L ε k + (total L ε * t - cumEnd L ε k) • cornerOut L k) ∧
  {x | x ∈ range γ ∧ ∀ k : ZMod n, x ∉ roundDisc (L k) ε} =
    {x | (∃ k : ZMod n, x ∈ edgeSegment L k) ∧ ∀ k : ZMod n, x ∉ roundDisc (L k) ε}

/-- **(b)** "Inside the disc about `q_i` the unit tangent moves *strictly* monotonically, in the sense
of `sgn ϑ_i`, from `δ_{i−1}/|δ_{i−1}|` to `δ_i/|δ_i|`, sweeping an arc of length exactly `|ϑ_i|` and no
more, and attaining each direction of that arc at exactly one parameter.  Moreover the unit-tangent
map is an *immersion* on the open junction arc: parametrized by arclength, its angular derivative
is nonzero at every interior parameter, while at the two ends it and all its derivatives vanish,
the junction meeting the straight edges flat to infinite order."  Read on the junction parameter
interval `[jStart k, jEnd k]` (the parameters at which the curve is inside the disc, clause (e)),
with the unit tangent `T t = normalize (deriv γ t)`, the printed lift `θ = junctionLift L ε k`
(`θ_u + ϑ_i φ(σ/ℓ)`), and the parameter arclength rescaled to period `1` (constant speed
`total L ε`). -/
def ClauseB (L : LabelledTuple n) (ε : ℝ) (γ : ℝ → Plane) : Prop :=
  (∀ t, euclideanLength (deriv γ t) = total L ε) ∧
  ∀ k < n,
    IsLiftOn (fun t => normalize (deriv γ t)) (junctionLift L ε k) (jStart L ε k) (jEnd L ε k) ∧
    normalize (deriv γ (jStart L ε k)) = cornerIn L k ∧
    normalize (deriv γ (jEnd L ε k)) = cornerOut L k ∧
    junctionLift L ε k (jEnd L ε k) - junctionLift L ε k (jStart L ε k) = cornerTurn L k ∧
    (0 < cornerTurn L k → StrictMonoOn (junctionLift L ε k) (Icc (jStart L ε k) (jEnd L ε k))) ∧
    (cornerTurn L k < 0 → StrictAntiOn (junctionLift L ε k) (Icc (jStart L ε k) (jEnd L ε k))) ∧
    (∀ t ∈ Icc (jStart L ε k) (jEnd L ε k),
      junctionLift L ε k t ∈ uIcc (junctionLift L ε k (jStart L ε k)) (junctionLift L ε k (jEnd L ε k))) ∧
    (∀ ψ ∈ uIcc (junctionLift L ε k (jStart L ε k)) (junctionLift L ε k (jEnd L ε k)),
      ∃! t, t ∈ Icc (jStart L ε k) (jEnd L ε k) ∧ junctionLift L ε k t = ψ) ∧
    InjOn (fun t => normalize (deriv γ t)) (Icc (jStart L ε k) (jEnd L ε k)) ∧
    ContDiff ℝ ∞ (junctionLift L ε k) ∧
    (∀ t ∈ Ioo (jStart L ε k) (jEnd L ε k), deriv (junctionLift L ε k) t ≠ 0) ∧
    (∀ m : ℕ, 1 ≤ m →
      iteratedDeriv m (junctionLift L ε k) (jStart L ε k) = 0 ∧
      iteratedDeriv m (junctionLift L ε k) (jEnd L ε k) = 0) ∧
    (∀ m : ℕ, 2 ≤ m → iteratedDeriv m γ (jStart L ε k) = 0 ∧ iteratedDeriv m γ (jEnd L ε k) = 0)

/-- **(c)** "`L_ε` has the same double points as `L`, with the same strands, the same over/under
assignment and hence the same crossing signs and the same writhe": the double points of the curve
are exactly the crossing points of `D` (whose shadow is `L`); for every carrying record each
occurrence is met on its own strand, running in the strand's direction (the same strands); the
over/under assignment is that of `D` (FR-1: `D_ε = D`), so that the smooth crossing signs
(`sgn det(γ'(over), γ'(under))`) are the signs of `D` and the writhe is the writhe of `D`. -/
def ClauseC (D : Diagram) (γ : ℝ → Plane) : Prop :=
  {p | ∃ s t, IsDoublePt γ s t ∧ p = γ s} = range D.Γ.crossingPoint ∧
  (∀ rec : Carries γ D, ∀ v : D.Γ.Visit,
    γ (rec.par v) ∈ D.Γ.seg v.2.1 ∧ ∃ r : ℝ, 0 < r ∧ deriv γ (rec.par v) = r • D.Γ.dir v.2.1) ∧
  (∀ rec : Carries γ D, ∀ x : D.Γ.Crossing, rec.sign x = D.sign x) ∧
  (∀ rec : Carries γ D, rec.writhe = D.writhe)

/-- **(d)** "`rot(L_ε) = rot(L)`": for the closed `C¹` regular curve structure on `γ`
(cf:def-turning) and the polygon's rotation of lem:rot (`rotationNumber`). -/
def ClauseD (L : LabelledTuple n) (γ : ℝ → Plane) : Prop :=
  ∀ c : ClosedC1Curve, c.γ = γ → c.rot = rotationNumber L

/-- **(e)** "There are pairwise disjoint closed discs `D_1, …, D_c`, one about each corner `q_i`, such
that each `D_i` meets no edge of `L` that is not incident to `q_i`, contains no double point of `L`,
meets the two incident edges exactly in the two sub-segments of length `ε` at `q_i`, and contains the
whole of the modification made at `q_i`" — the discs are `roundDisc (L k) ε`; "the modification made
at `q_i`" is the junction arc, parameters `[jStart k, jEnd k]`, which is the whole of the curve inside
the disc and is an embedded arc ("its consumer asks for a disc meeting the diagram in one embedded
arc"). -/
def ClauseE (L : LabelledTuple n) (ε : ℝ) (γ : ℝ → Plane) : Prop :=
  ∀ k < n,
    IsDisc (roundDisc (L (k : ZMod n)) ε) ∧
    L (k : ZMod n) ∈ interior (roundDisc (L (k : ZMod n)) ε) ∧
    (∀ k' : ZMod n, (k : ZMod n) ≠ k' →
      Disjoint (roundDisc (L (k : ZMod n)) ε) (roundDisc (L k') ε)) ∧
    (∀ j : ZMod n, ¬ incident (k : ZMod n) j →
      Disjoint (roundDisc (L (k : ZMod n)) ε) (edgeSegment L j)) ∧
    (∀ x : Crossing L, crossingPoint x ∉ roundDisc (L (k : ZMod n)) ε) ∧
    roundDisc (L (k : ZMod n)) ε ∩ edgeSegment L ((k : ZMod n) - 1) =
      {x | ∃ s ∈ Icc (0 : ℝ) ε, x = L (k : ZMod n) - s • cornerIn L k} ∧
    roundDisc (L (k : ZMod n)) ε ∩ edgeSegment L (k : ZMod n) =
      {x | ∃ s ∈ Icc (0 : ℝ) ε, x = L (k : ZMod n) + s • cornerOut L k} ∧
    (∀ t ∈ Icc (jStart L ε k) (jEnd L ε k), γ t ∈ roundDisc (L (k : ZMod n)) ε) ∧
    (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ roundDisc (L (k : ZMod n)) ε → t ∈ Icc (jStart L ε k) (jEnd L ε k)) ∧
    InjOn γ (Icc (jStart L ε k) (jEnd L ε k))

end Rounding

open Rounding

/-! ## 5. The row bundle: one field per printed clause, about the named construction -/

/-- cf:lem-rounding (sm-3:3644-3700), one field per printed clause.  Hypotheses in every field:
`L : LabelledTuple n` a closed polygon (`3 ≤ n`), `D : Diagram` with `D.Γ = Shadow.single ⟨n, hn, L⟩`
("an oriented diagram whose underlying plane curve is L"; its genericity clauses are the printed
"finitely many double points, all transversal, none of them a corner; no corner on a non-incident
edge" and "the principal turns all exist"), and `∀ i, principalTurn L i ≠ 0` ("nonzero").  The
witnesses are the named construction: the clearance `clearance L`, the curve `roundedCurve L ε`, and
the diagram `D` itself (FR-1), as read by cf:thm-carrierfloor(A) ("the construction … returns one
curve and one diagram", sm-3:4291-4303).  The printed existential form is `RoundingData.printed`. -/
structure RoundingData : Prop where
  /-- "Then there is a clearance `ε₀(L) > 0`": the printed `ε₀(L) = ⅓ min{η_v, η_e, η_ℓ, η_X}` is
  positive. -/
  clearance_pos : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (L : LabelledTuple n) (D : Diagram),
    D.Γ = Shadow.single ⟨n, hn, L⟩ → (∀ i, principalTurn L i ≠ 0) → 0 < clearance L
  /-- "for every `ε ∈ (0, ε₀(L))` there is a `C^∞` regular closed plane curve `L_ε`": the rounded
  curve is `C^∞`, 1-periodic and regular. -/
  curve : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (L : LabelledTuple n) (D : Diagram),
    D.Γ = Shadow.single ⟨n, hn, L⟩ → (∀ i, principalTurn L i ≠ 0) →
    ∀ ε : ℝ, 0 < ε → ε < clearance L →
      ContDiff ℝ ∞ (roundedCurve L ε) ∧ Function.Periodic (roundedCurve L ε) 1 ∧
        ∀ t, deriv (roundedCurve L ε) t ≠ 0
  /-- "and a diagram `D_ε` carried by it": the diagram `D` is carried by the rounded curve (FR-1). -/
  diagram : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (L : LabelledTuple n) (D : Diagram),
    D.Γ = Shadow.single ⟨n, hn, L⟩ → (∀ i, principalTurn L i ≠ 0) →
    ∀ ε : ℝ, 0 < ε → ε < clearance L → Nonempty (Carries (roundedCurve L ε) D)
  /-- (a) "`L_ε` coincides with `L` outside the union of the discs of radius `ε` about the
  corners." -/
  a : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (L : LabelledTuple n) (D : Diagram),
    D.Γ = Shadow.single ⟨n, hn, L⟩ → (∀ i, principalTurn L i ≠ 0) →
    ∀ ε : ℝ, 0 < ε → ε < clearance L → ClauseA L ε (roundedCurve L ε)
  /-- (b) "Inside the disc about `q_i` the unit tangent moves strictly monotonically, in the sense
  of `sgn ϑ_i`, from `δ_{i−1}/|δ_{i−1}|` to `δ_i/|δ_i|`, sweeping an arc of length exactly `|ϑ_i|`
  and no more, and attaining each direction of that arc at exactly one parameter.  Moreover the
  unit-tangent map is an immersion on the open junction arc: parametrized by arclength, its angular
  derivative is nonzero at every interior parameter, while at the two ends it and all its
  derivatives vanish, the junction meeting the straight edges flat to infinite order." -/
  b : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (L : LabelledTuple n) (D : Diagram),
    D.Γ = Shadow.single ⟨n, hn, L⟩ → (∀ i, principalTurn L i ≠ 0) →
    ∀ ε : ℝ, 0 < ε → ε < clearance L → ClauseB L ε (roundedCurve L ε)
  /-- (c) "`L_ε` has the same double points as `L`, with the same strands, the same over/under
  assignment and hence the same crossing signs and the same writhe." -/
  c : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (L : LabelledTuple n) (D : Diagram),
    D.Γ = Shadow.single ⟨n, hn, L⟩ → (∀ i, principalTurn L i ≠ 0) →
    ∀ ε : ℝ, 0 < ε → ε < clearance L → ClauseC D (roundedCurve L ε)
  /-- (d) "`rot(L_ε) = rot(L)`." -/
  d : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (L : LabelledTuple n) (D : Diagram),
    D.Γ = Shadow.single ⟨n, hn, L⟩ → (∀ i, principalTurn L i ≠ 0) →
    ∀ ε : ℝ, 0 < ε → ε < clearance L → ClauseD L (roundedCurve L ε)
  /-- (e) "The disc package is returned.  There are pairwise disjoint closed discs `D_1, …, D_c`, one
  about each corner `q_i`, such that each `D_i` meets no edge of `L` that is not incident to `q_i`,
  contains no double point of `L`, meets the two incident edges exactly in the two sub-segments of
  length `ε` at `q_i`, and contains the whole of the modification made at `q_i`." -/
  e : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (L : LabelledTuple n) (D : Diagram),
    D.Γ = Shadow.single ⟨n, hn, L⟩ → (∀ i, principalTurn L i ≠ 0) →
    ∀ ε : ℝ, 0 < ε → ε < clearance L → ClauseE L ε (roundedCurve L ε)

/-- The printed existential form of cf:lem-rounding, from the bundle: "there is a clearance
`ε₀(L) > 0` such that for every `ε ∈ (0, ε₀(L))` there is a `C^∞` regular closed plane curve `L_ε`,
and a diagram `D_ε` carried by it, with (a)–(e)" — with `D_ε = D` (FR-1). -/
theorem RoundingData.printed (h : RoundingData) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (L : LabelledTuple n) (D : Diagram) (hD : D.Γ = Shadow.single ⟨n, hn, L⟩)
    (hturn : ∀ i, principalTurn L i ≠ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ Lε : SmoothRegularLoop, Nonempty (Carries Lε.γ D) ∧
        ClauseA L ε Lε.γ ∧ ClauseB L ε Lε.γ ∧ ClauseC D Lε.γ ∧ ClauseD L Lε.γ ∧ ClauseE L ε Lε.γ := by
  refine ⟨clearance L, h.clearance_pos hn L D hD hturn, fun ε hε0 hε1 => ?_⟩
  obtain ⟨hsmooth, hper, hreg⟩ := h.curve hn L D hD hturn ε hε0 hε1
  exact ⟨⟨⟨roundedCurve L ε, hsmooth, hper⟩, hreg⟩, h.diagram hn L D hD hturn ε hε0 hε1,
    h.a hn L D hD hturn ε hε0 hε1, h.b hn L D hD hturn ε hε0 hε1, h.c hn L D hD hturn ε hε0 hε1,
    h.d hn L D hD hturn ε hε0 hε1, h.e hn L D hD hturn ε hε0 hε1⟩

-- ROW THEOREM (the skeleton replaces this line with the assembled proof)
/-- cf:lem-rounding. -/
theorem cf_lem_rounding : RoundingData := by sorry

end

end SM
