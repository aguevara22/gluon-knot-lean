import SM.FrontSmooth
import SM.TurnLift
import SM.LinkDiagramRecord
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # SM cf:lem-rounding (row 97) — SKELETON B (statement + chain of lemmas, proofs `sorry`; the row proved from the chain)

The statement part below is byte-identical to Rounding_statement_B.lean (sections 0-5); the chain
follows the marker "Skeleton B — the chain of lemmas".

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


/-! ###################################################################################
# Skeleton B — the chain of lemmas (every proof `sorry`), and the row assembled from it

Units (PLAN_B.md §4): P = profile, J = one junction, C = corner data / clearance / discs,
G = global assembly, E = clauses (a) (b) (d) (e), D = the carried diagram and clause (c),
R = the row.  Hypotheses of the polygon units are bundled in `Admissible`.
################################################################################### -/

namespace Rounding

/-! ## Unit P — the transition profile `φ = Real.smoothTransition` (sm-3:3705-3721) -/

theorem profile_zero_of_nonpos {t : ℝ} (h : t ≤ 0) : profile t = 0 :=
  Real.smoothTransition.zero_of_nonpos h

theorem profile_one_of_one_le {t : ℝ} (h : 1 ≤ t) : profile t = 1 :=
  Real.smoothTransition.one_of_one_le h

theorem profile_nonneg (t : ℝ) : 0 ≤ profile t := Real.smoothTransition.nonneg t

theorem profile_le_one (t : ℝ) : profile t ≤ 1 := Real.smoothTransition.le_one t

theorem profile_pos_of_pos {t : ℝ} (h : 0 < t) : 0 < profile t :=
  Real.smoothTransition.pos_of_pos h

theorem profile_lt_one_of_lt_one {t : ℝ} (h : t < 1) : profile t < 1 :=
  Real.smoothTransition.lt_one_of_lt_one h

theorem contDiff_profile : ContDiff ℝ ∞ profile := Real.smoothTransition.contDiff

theorem continuous_profile : Continuous profile := Real.smoothTransition.continuous

/-- P1 "It satisfies φ(1−t) = 1 − φ(t), by inspection of the formula" (sm-3:3716). -/
theorem profile_symm (t : ℝ) : profile (1 - t) = 1 - profile t := by sorry

/-- P2 "it is strictly increasing on (0,1)" (sm-3:3716-3722): for `0 ≤ s < t ≤ 1`,
`f(s) f(1−t) < f(t) f(1−s)` since `1/t + 1/(1−s) < 1/s + 1/(1−t)` (no derivatives needed). -/
theorem profile_strictMonoOn : StrictMonoOn profile (Icc 0 1) := by sorry

/-- P3 the derivative of `f = expNegInvGlue` (Mathlib `hasDerivAt_polynomial_eval_inv_mul` with
`p = 1`): `f'(t) = t⁻² f(t)` for every `t`. -/
theorem hasDerivAt_expNegInvGlue (t : ℝ) :
    HasDerivAt expNegInvGlue ((t⁻¹) ^ 2 * expNegInvGlue t) t := by sorry

/-- P3 the printed derivative formula (sm-3:3719-3720):
`φ' = (f'(t) f(1−t) + f(t) f'(1−t)) / (f(t)+f(1−t))²`. -/
theorem hasDerivAt_profile (t : ℝ) :
    HasDerivAt profile
      (((t⁻¹) ^ 2 * expNegInvGlue t * expNegInvGlue (1 - t) +
          expNegInvGlue t * ((1 - t)⁻¹) ^ 2 * expNegInvGlue (1 - t)) /
        (expNegInvGlue t + expNegInvGlue (1 - t)) ^ 2) t := by sorry

/-- P3 `φ' > 0` on `(0,1)`, "both terms of the numerator being positive there" (sm-3:3721). -/
theorem deriv_profile_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : 0 < deriv profile t := by sorry

/-- P4 (helper) A `C^∞` function constant to the left of `a` has all derivatives of order `≥ 1`
vanishing at `a`: `iteratedDeriv m g` is continuous and vanishes on `Iio a`. -/
theorem iteratedDeriv_eq_zero_of_const_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : ContDiff ℝ ∞ g) {a : ℝ} {c : E} (hc : ∀ x, x < a → g x = c) {m : ℕ}
    (hm : 1 ≤ m) : iteratedDeriv m g a = 0 := by sorry

theorem iteratedDeriv_eq_zero_of_const_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : ContDiff ℝ ∞ g) {a : ℝ} {c : E} (hc : ∀ x, a < x → g x = c) {m : ℕ}
    (hm : 1 ≤ m) : iteratedDeriv m g a = 0 := by sorry

/-- P4 (helper) A `C^∞` curve affine to the left of `a` has all derivatives of order `≥ 2`
vanishing at `a`. -/
theorem iteratedDeriv_eq_zero_of_affine_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : ContDiff ℝ ∞ g) {a : ℝ} {c w : E} (hc : ∀ x < a, g x = c + x • w) {m : ℕ}
    (hm : 2 ≤ m) : iteratedDeriv m g a = 0 := by sorry

theorem iteratedDeriv_eq_zero_of_affine_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : ContDiff ℝ ∞ g) {a : ℝ} {c w : E} (hc : ∀ x, a < x → g x = c + x • w) {m : ℕ}
    (hm : 2 ≤ m) : iteratedDeriv m g a = 0 := by sorry

/-- P4 "Every derivative of φ vanishes at 0 and at 1" (sm-3:3722-3723). -/
theorem iteratedDeriv_profile_zero {m : ℕ} (hm : 1 ≤ m) : iteratedDeriv m profile 0 = 0 :=
  iteratedDeriv_eq_zero_of_const_left contDiff_profile (c := 0)
    (fun _ hx => profile_zero_of_nonpos hx.le) hm

theorem iteratedDeriv_profile_one {m : ℕ} (hm : 1 ≤ m) : iteratedDeriv m profile 1 = 0 :=
  iteratedDeriv_eq_zero_of_const_right contDiff_profile (c := 1)
    (fun _ hx => profile_one_of_one_le hx.le) hm

/-- P5 (helper) The primitive of a continuous function has that function as derivative
(FTC, `intervalIntegral.integral_hasDerivAt_right`). -/
theorem hasDerivAt_primitive {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (fun x => ∫ τ in (0 : ℝ)..x, f τ) (f x) x := by sorry

/-- P5 (helper) The primitive of a `C^∞` function is `C^∞` (`contDiff_succ_iff_deriv` +
`hasDerivAt_primitive`, or `contDiff_infty_iff_deriv`). -/
theorem contDiff_primitive {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => ∫ τ in (0 : ℝ)..x, f τ) := by sorry

/-! ## Unit J — one junction (sm-3:3701-3818), abstract data `θ₀ ϑ ε`, `0 < |ϑ| < π` -/

section Junction

variable (θ₀ ϑ ε ℓ : ℝ) (A₀ : Plane)

theorem euclideanLength_unitDir (θ : ℝ) : euclideanLength (unitDir θ) = 1 := by sorry

theorem normalize_unitDir (θ : ℝ) : normalize (unitDir θ) = unitDir θ := by sorry

theorem unitDir_add_two_pi_int (θ : ℝ) (m : ℤ) : unitDir (θ + 2 * Real.pi * m) = unitDir θ := by
  sorry

theorem unitDir_ne_zero (θ : ℝ) : unitDir θ ≠ 0 := by sorry

/-- `unitDir` is injective on angles less than `π` apart (used for "each direction at exactly one
parameter"). -/
theorem unitDir_injOn_uIcc {θ₁ θ₂ : ℝ} (h : |θ₂ - θ₁| < Real.pi) :
    InjOn unitDir (uIcc θ₁ θ₂) := by sorry

theorem contDiff_junctionAngle (hℓ : ℓ ≠ 0) : ContDiff ℝ ∞ (junctionAngle θ₀ ϑ ℓ) := by sorry

theorem junctionAngle_of_nonpos (hℓ : 0 < ℓ) {σ : ℝ} (hσ : σ ≤ 0) :
    junctionAngle θ₀ ϑ ℓ σ = θ₀ := by sorry

theorem junctionAngle_of_le (hℓ : 0 < ℓ) {σ : ℝ} (hσ : ℓ ≤ σ) :
    junctionAngle θ₀ ϑ ℓ σ = θ₀ + ϑ := by sorry

/-- J-angle "with φ strictly increasing on (0,1) the tangent angle θ_u + ϑ_i φ(t/ℓ) is strictly
monotone across the junction" (sm-3:3733-3735), in the sense of `sgn ϑ`. -/
theorem junctionAngle_strictMonoOn (hℓ : 0 < ℓ) (hϑ : 0 < ϑ) :
    StrictMonoOn (junctionAngle θ₀ ϑ ℓ) (Icc 0 ℓ) := by sorry

theorem junctionAngle_strictAntiOn (hℓ : 0 < ℓ) (hϑ : ϑ < 0) :
    StrictAntiOn (junctionAngle θ₀ ϑ ℓ) (Icc 0 ℓ) := by sorry

/-- "sweeping an arc of length exactly |ϑ_i| and no more". -/
theorem junctionAngle_mem_uIcc (hℓ : 0 < ℓ) {σ : ℝ} (hσ : σ ∈ Icc 0 ℓ) :
    junctionAngle θ₀ ϑ ℓ σ ∈ uIcc θ₀ (θ₀ + ϑ) := by sorry

/-- "attaining each direction of that arc at exactly one parameter" (monotonicity + IVT). -/
theorem junctionAngle_existsUnique (hℓ : 0 < ℓ) (hϑ : ϑ ≠ 0) {ψ : ℝ} (hψ : ψ ∈ uIcc θ₀ (θ₀ + ϑ)) :
    ∃! σ, σ ∈ Icc 0 ℓ ∧ junctionAngle θ₀ ϑ ℓ σ = ψ := by sorry

/-- "its angular derivative … ϑ_i φ'(σ/ℓ)/ℓ ≠ 0 for 0 < σ < ℓ" (sm-3:3689-3690). -/
theorem deriv_junctionAngle_ne_zero (hℓ : 0 < ℓ) (hϑ : ϑ ≠ 0) {σ : ℝ} (hσ : σ ∈ Ioo 0 ℓ) :
    deriv (junctionAngle θ₀ ϑ ℓ) σ ≠ 0 := by sorry

/-- Flatness of the angle at the two ends (`P4` helpers: constant on `Iio 0`, on `Ioi ℓ`). -/
theorem iteratedDeriv_junctionAngle_zero (hℓ : 0 < ℓ) {m : ℕ} (hm : 1 ≤ m) :
    iteratedDeriv m (junctionAngle θ₀ ϑ ℓ) 0 = 0 :=
  iteratedDeriv_eq_zero_of_const_left (contDiff_junctionAngle θ₀ ϑ ℓ hℓ.ne') (c := θ₀)
    (fun _ hx => junctionAngle_of_nonpos θ₀ ϑ ℓ hℓ hx.le) hm

theorem iteratedDeriv_junctionAngle_length (hℓ : 0 < ℓ) {m : ℕ} (hm : 1 ≤ m) :
    iteratedDeriv m (junctionAngle θ₀ ϑ ℓ) ℓ = 0 :=
  iteratedDeriv_eq_zero_of_const_right (contDiff_junctionAngle θ₀ ϑ ℓ hℓ.ne') (c := θ₀ + ϑ)
    (fun _ hx => junctionAngle_of_le θ₀ ϑ ℓ hℓ hx.le) hm

theorem junctionTangent_injOn (hℓ : 0 < ℓ) (hϑ0 : ϑ ≠ 0) (hϑπ : |ϑ| < Real.pi) :
    InjOn (junctionTangent θ₀ ϑ ℓ) (Icc 0 ℓ) := by sorry

/-- "γ_ℓ is a unit-speed C^∞ arc" (sm-3:3743): its derivative is the unit tangent. -/
theorem hasDerivAt_junctionCurve (hℓ : ℓ ≠ 0) (σ : ℝ) :
    HasDerivAt (junctionCurve A₀ θ₀ ϑ ℓ) (junctionTangent θ₀ ϑ ℓ σ) σ := by sorry

theorem deriv_junctionCurve (hℓ : ℓ ≠ 0) (σ : ℝ) :
    deriv (junctionCurve A₀ θ₀ ϑ ℓ) σ = junctionTangent θ₀ ϑ ℓ σ :=
  (hasDerivAt_junctionCurve θ₀ ϑ ℓ A₀ hℓ σ).deriv

theorem contDiff_junctionCurve (hℓ : ℓ ≠ 0) : ContDiff ℝ ∞ (junctionCurve A₀ θ₀ ϑ ℓ) := by sorry

theorem junctionCurve_zero : junctionCurve A₀ θ₀ ϑ ℓ 0 = A₀ := by sorry

/-- Before the junction the curve is the straight line of direction `u` through `A₀`. -/
theorem junctionCurve_of_nonpos (hℓ : 0 < ℓ) {σ : ℝ} (hσ : σ ≤ 0) :
    junctionCurve A₀ θ₀ ϑ ℓ σ = A₀ + σ • unitDir θ₀ := by sorry

/-- After the junction the curve is the straight line of direction `v` through `γ_ℓ(ℓ)`. -/
theorem junctionCurve_of_le (hℓ : 0 < ℓ) {σ : ℝ} (hσ : ℓ ≤ σ) :
    junctionCurve A₀ θ₀ ϑ ℓ σ = junctionCurve A₀ θ₀ ϑ ℓ ℓ + (σ - ℓ) • unitDir (θ₀ + ϑ) := by sorry

/-- Flatness of the curve at the two ends: all derivatives of order `≥ 2` vanish ("the junction
meeting the straight edges flat to infinite order"). -/
theorem iteratedDeriv_junctionCurve_zero (hℓ : 0 < ℓ) {m : ℕ} (hm : 2 ≤ m) :
    iteratedDeriv m (junctionCurve A₀ θ₀ ϑ ℓ) 0 = 0 :=
  iteratedDeriv_eq_zero_of_affine_left (contDiff_junctionCurve θ₀ ϑ ℓ A₀ hℓ.ne') (c := A₀)
    (w := unitDir θ₀) (fun _ hx => junctionCurve_of_nonpos θ₀ ϑ ℓ A₀ hℓ hx.le) hm

theorem iteratedDeriv_junctionCurve_length (hℓ : 0 < ℓ) {m : ℕ} (hm : 2 ≤ m) :
    iteratedDeriv m (junctionCurve A₀ θ₀ ϑ ℓ) ℓ = 0 := by
  refine iteratedDeriv_eq_zero_of_affine_right (contDiff_junctionCurve θ₀ ϑ ℓ A₀ hℓ.ne')
    (c := junctionCurve A₀ θ₀ ϑ ℓ ℓ - ℓ • unitDir (θ₀ + ϑ)) (w := unitDir (θ₀ + ϑ)) ?_ hm
  intro x hx
  rw [junctionCurve_of_le θ₀ ϑ ℓ A₀ hℓ hx.le, sub_smul]
  abel

/-- J1 "The symmetry φ(1−t) = 1−φ(t) makes … m(φ) point along u+v" (sm-3:3765-3768): the mean is a
positive multiple of the bisector direction `unitDir (θ₀ + ϑ/2)`, with coefficient
`∫₀¹ cos(ϑ(φ(t) − ½)) dt`. -/
theorem junctionMean_eq :
    junctionMean θ₀ ϑ =
      (∫ t in (0 : ℝ)..1, Real.cos (ϑ * (profile t - 1 / 2))) • unitDir (θ₀ + ϑ / 2) := by sorry

/-- J1 "|m(φ)| > 0 because all the directions integrated lie in a closed angular interval of width
|ϑ_i| < π" (sm-3:3768-3770): the coefficient is at least `cos(ϑ/2) > 0`. -/
theorem cos_half_le_junctionMean_coeff (hϑπ : |ϑ| < Real.pi) :
    Real.cos (ϑ / 2) ≤ ∫ t in (0 : ℝ)..1, Real.cos (ϑ * (profile t - 1 / 2)) := by sorry

theorem cos_half_pos (hϑπ : |ϑ| < Real.pi) : 0 < Real.cos (ϑ / 2) := by sorry

/-- J2 `u + v = 2 cos(ϑ/2) · (bisector)`. -/
theorem unitDir_add_unitDir : unitDir θ₀ + unitDir (θ₀ + ϑ) = (2 * Real.cos (ϑ / 2)) • unitDir (θ₀ + ϑ / 2) := by
  sorry

theorem euclideanLength_unitDir_add (hϑπ : |ϑ| < Real.pi) :
    euclideanLength (unitDir θ₀ + unitDir (θ₀ + ϑ)) = 2 * Real.cos (ϑ / 2) := by sorry

/-- J3 the junction length is positive … -/
theorem junctionLength_pos (hε : 0 < ε) (hϑπ : |ϑ| < Real.pi) : 0 < junctionLength ε θ₀ ϑ := by
  sorry

/-- J3 … and at most `2ε` (since `|m(φ)| ≥ cos(ϑ/2)` and `|u+v| = 2cos(ϑ/2)`). -/
theorem junctionLength_le (hε : 0 < ε) (hϑπ : |ϑ| < Real.pi) : junctionLength ε θ₀ ϑ ≤ 2 * ε := by
  sorry

/-- J6 "Taking ℓ = ε|u+v|/|m(φ)| makes the endpoint exactly A₁" (sm-3:3770-3771):
`γ_ℓ(ℓ) = A₀ + ℓ m(φ) = A₀ + ε(u+v)` (substitution `t = τ/ℓ`, `intervalIntegral.integral_comp_div`). -/
theorem junctionCurve_end (hε : 0 < ε) (hϑπ : |ϑ| < Real.pi) :
    junctionCurve A₀ θ₀ ϑ (junctionLength ε θ₀ ϑ) (junctionLength ε θ₀ ϑ) =
      A₀ + ε • (unitDir θ₀ + unitDir (θ₀ + ϑ)) := by sorry

/-- J7 "the arc lies in the triangle A₀ q_i A₁ … and T_i lies in the closed disc of radius ε about
q_i" (sm-3:3772-3818).  Proof-first route: in the bisector frame `(w, z)` the coordinate
`x_w = ⟨γ − q, w⟩` is strictly increasing (derivative `cos β ≥ cos(ϑ/2) > 0`) from `−ε cos(ϑ/2)` to
`ε cos(ϑ/2)`, and `|x_z| ≤ ε |sin(ϑ/2)|` (the chord inequality `sgn ϑ · ∫₀^σ sin β ≤ 0` from the sign
pattern of `β` and `∫₀^ℓ sin β = 0`, and the lower bound from `|∫₀^σ sin β| ≤ ℓ |sin(ϑ/2)| ≤ 2ε |sin(ϑ/2)|`);
hence `|γ − q|² ≤ ε²`. -/
theorem junctionCurve_mem_roundDisc (hε : 0 < ε) (hϑ0 : ϑ ≠ 0) (hϑπ : |ϑ| < Real.pi) {σ : ℝ}
    (hσ : σ ∈ Icc 0 (junctionLength ε θ₀ ϑ)) :
    junctionCurve A₀ θ₀ ϑ (junctionLength ε θ₀ ϑ) σ ∈ roundDisc (A₀ + ε • unitDir θ₀) ε := by sorry

/-- J7' interior points of the junction are strictly inside the disc (`|x_w| < ε cos(ϑ/2)`). -/
theorem junctionCurve_lt_of_mem_Ioo (hε : 0 < ε) (hϑ0 : ϑ ≠ 0) (hϑπ : |ϑ| < Real.pi) {σ : ℝ}
    (hσ : σ ∈ Ioo 0 (junctionLength ε θ₀ ϑ)) :
    euclideanLength (junctionCurve A₀ θ₀ ϑ (junctionLength ε θ₀ ϑ) σ - (A₀ + ε • unitDir θ₀)) < ε := by
  sorry

/-- J9 outside the junction parameters the (straight) curve is outside the disc. -/
theorem junctionCurve_notMem_roundDisc (hε : 0 < ε) (hϑπ : |ϑ| < Real.pi) {σ : ℝ}
    (hσ : σ ∉ Icc 0 (junctionLength ε θ₀ ϑ)) :
    junctionCurve A₀ θ₀ ϑ (junctionLength ε θ₀ ϑ) σ ∉ roundDisc (A₀ + ε • unitDir θ₀) ε := by sorry

/-- J8 "Its bisector coordinate has derivative cos β(σ) ≥ cos α > 0.  Thus that coordinate is
strictly increasing and the junction arc is injective" (sm-3:3808-3811) — on all of `ℝ`. -/
theorem junctionCurve_injective (hℓ : 0 < ℓ) (hϑπ : |ϑ| < Real.pi) :
    Function.Injective (junctionCurve A₀ θ₀ ϑ ℓ) := by sorry

end Junction

/-! ## Unit C — corner data, the clearance, the discs (sm-3:3819-3840) -/

section Corner

variable (C : PolyComp)

/-- The one-component diagram on the polygon `C` with over-strand data `ovr`. -/
abbrev mkSingle (gen : (Shadow.single C).Generic)
    (ovr : (Shadow.single C).Crossing → (Shadow.single C).Strand) (mem : ∀ x, ovr x ∈ x.val) :
    Diagram := ⟨Shadow.single C, gen, ovr, mem⟩

/-- The hypotheses of the row for the polygon `C.P` and the radius `ε`: `D` generic (the printed
"finitely many double points, all transversal, none a corner; no corner on a non-incident edge"
and "the principal turns exist"), nonzero turns, and `0 < ε < ε₀(L)`. -/
structure Admissible (ε : ℝ) : Prop where
  gen : (Shadow.single C).Generic
  turn : ∀ i, principalTurn C.P i ≠ 0
  pos : 0 < ε
  lt : ε < clearance C.P

variable {C}

/-- H-1: the polygon of a generic one-component shadow is regular ("the principal turns all
exist"). -/
theorem regular_of_generic (gen : (Shadow.single C).Generic) : Regular C.P := gen.regular ⟨0, Nat.one_pos⟩

/-- H-1: "no corner of L lies on an edge of L other than the two incident to it" (`Generic.tail_off`
through `single_incidentTail_iff`). -/
theorem corner_notMem_edge_of_generic (gen : (Shadow.single C).Generic) {i j : ZMod C.k}
    (h : ¬ incident i j) : C.P i ∉ edgeSegment C.P j := by sorry

/-- H-1: distinct corners are distinct points (`tail_off` + regularity). -/
theorem corner_injective_of_generic (gen : (Shadow.single C).Generic) : Function.Injective C.P := by
  sorry

/-- H-1: "none of them a corner": a double point of `L` is no corner. -/
theorem crossingPoint_ne_corner_of_generic (gen : (Shadow.single C).Generic) (x : Crossing C.P)
    (i : ZMod C.k) : crossingPoint x ≠ C.P i := by sorry

/-- H-1: a double point lies in the interior of each of its two edges and at Euclidean distance at
least `3 ε₀` from every corner — the crossing-point family of the clearance. -/
theorem crossingPoint_mem_edgeInterior_of_generic (gen : (Shadow.single C).Generic)
    (x : Crossing C.P) {i : ZMod C.k} (hi : i ∈ x.val) : crossingPoint x ∈ edgeInterior C.P i := by
  sorry

theorem cornerTurn_ne_zero (hturn : ∀ i, principalTurn C.P i ≠ 0) (k : ℕ) : cornerTurn C.P k ≠ 0 :=
  hturn _

/-- "Since 0 < |ϑ_i| < π" (sm-3:3701): `principalAngle_bounds`. -/
theorem abs_cornerTurn_lt_pi (hL : Regular C.P) (k : ℕ) : |cornerTurn C.P k| < Real.pi := by sorry

/-- `cornerArg` is an argument of the arriving unit direction (`Complex.norm_mul_exp_arg_mul_I`). -/
theorem unitDir_cornerArg (hL : Regular C.P) (k : ℕ) : unitDir (cornerArg C.P k) = cornerIn C.P k := by
  sorry

/-- Turning the arriving direction by the principal turn gives the leaving direction
(`principalAngle_coe_angle`, `Real.Angle.angle_eq_iff_two_pi_dvd_sub`). -/
theorem unitDir_add_cornerTurn (hL : Regular C.P) {θ : ℝ} {k : ℕ} (hθ : unitDir θ = cornerIn C.P k) :
    unitDir (θ + cornerTurn C.P k) = cornerOut C.P k := by sorry

theorem cornerIn_succ (k : ℕ) : cornerIn C.P (k + 1) = cornerOut C.P k := by sorry

theorem cumArg_zero : cumArg C.P 0 = cornerArg C.P 0 := by simp [cumArg]

theorem cumArg_succ (k : ℕ) : cumArg C.P (k + 1) = cumArg C.P k + cornerTurn C.P k := by
  simp [cumArg, Finset.sum_range_succ, add_assoc]

/-- The carried angle `cumArg k` is an argument of `cornerIn k` for every `k` (induction). -/
theorem unitDir_cumArg (hL : Regular C.P) (k : ℕ) : unitDir (cumArg C.P k) = cornerIn C.P k := by sorry

theorem unitDir_cumArg_add (hL : Regular C.P) (k : ℕ) :
    unitDir (cumArg C.P k + cornerTurn C.P k) = cornerOut C.P k :=
  unitDir_add_cornerTurn hL (unitDir_cumArg hL k)

/-- `Σ_k ϑ_k = 2π rot(L)` (`two_pi_mul_rotationNumber`, `sum_range_natCast_eq_sum_zmod`). -/
theorem cumArg_count (hL : Regular C.P) :
    cumArg C.P C.k = cornerArg C.P 0 + 2 * Real.pi * rotationNumber C.P := by sorry

theorem edgeLen_pos (hL : Regular C.P) (k : ℕ) : 0 < edgeLen C.P k := by sorry

theorem edge_eq_edgeLen_smul (hL : Regular C.P) (k : ℕ) :
    edge C.P (k : ZMod C.k) = edgeLen C.P k • cornerOut C.P k := by sorry

/-- The straight part after the junction at `q_k` ends at `A₀(q_{k+1})`:
`A₁(q_k) + (|δ_k| − 2ε) v_k = A₀(q_{k+1})`. -/
theorem A1_add_straight (hL : Regular C.P) (ε : ℝ) (k : ℕ) :
    A1 C.P ε k + (edgeLen C.P k - 2 * ε) • cornerOut C.P k = A0 C.P ε (k + 1) := by sorry

/-- The Euclidean length is a norm on `Plane` (through `planeComplex`): the triangle inequality. -/
theorem euclideanLength_add_le (x y : Plane) :
    euclideanLength (x + y) ≤ euclideanLength x + euclideanLength y := by sorry

theorem euclideanLength_sub_rev (x y : Plane) : euclideanLength (x - y) = euclideanLength (y - x) := by
  sorry

/-- The sup distance of `Plane = ℝ × ℝ` is at most the Euclidean length. -/
theorem dist_le_euclideanLength (x y : Plane) : dist x y ≤ euclideanLength (x - y) := by sorry

theorem clearanceSet_finite (L : LabelledTuple C.k) : (clearanceSet L).Finite := by sorry

theorem clearanceSet_nonempty (L : LabelledTuple C.k) : (clearanceSet L).Nonempty :=
  ⟨1, by simp [clearanceSet]⟩

/-- "Every listed quantity is positive" (sm-3:3830-3834): corners distinct, corners off non-incident
closed edges (compact, so positive `infDist`), edges nonzero, double points off corners. -/
theorem clearanceSet_pos (gen : (Shadow.single C).Generic) {d : ℝ} (hd : d ∈ clearanceSet C.P) :
    0 < d := by sorry

theorem clearance_pos (gen : (Shadow.single C).Generic) : 0 < clearance C.P := by sorry

theorem three_clearance_le {d : ℝ} (hd : d ∈ clearanceSet C.P) : 3 * clearance C.P ≤ d := by sorry

theorem three_clearance_le_dist_corners {i k : ZMod C.k} (h : i ≠ k) :
    3 * clearance C.P ≤ euclideanLength (C.P k - C.P i) :=
  three_clearance_le (by simp only [clearanceSet, mem_union, mem_range]; exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨(i, k), h⟩, rfl⟩))))

theorem three_clearance_le_infDist {i j : ZMod C.k} (h : ¬ incident i j) :
    3 * clearance C.P ≤ Metric.infDist (C.P i) (edgeSegment C.P j) :=
  three_clearance_le (by simp only [clearanceSet, mem_union, mem_range]; exact Or.inl (Or.inl (Or.inr ⟨⟨(i, j), h⟩, rfl⟩)))

theorem three_clearance_le_edgeLen (k : ℕ) : 3 * clearance C.P ≤ edgeLen C.P k :=
  three_clearance_le (by simp only [clearanceSet, mem_union, mem_range]; exact Or.inl (Or.inr ⟨(k : ZMod C.k), rfl⟩))

theorem three_clearance_le_dist_crossing (i : ZMod C.k) (x : Crossing C.P) :
    3 * clearance C.P ≤ euclideanLength (crossingPoint x - C.P i) :=
  three_clearance_le (by simp only [clearanceSet, mem_union, mem_range]; exact Or.inr ⟨(i, x), rfl⟩)

/-- The round disc is a disc in the accepted sense (`IsDisc`: convex, compact, nonempty interior). -/
theorem isDisc_roundDisc (q : Plane) {r : ℝ} (hr : 0 < r) : IsDisc (roundDisc q r) := by sorry

theorem mem_interior_roundDisc (q : Plane) {r : ℝ} (hr : 0 < r) : q ∈ interior (roundDisc q r) := by
  sorry

theorem mem_roundDisc_iff (q x : Plane) (r : ℝ) : x ∈ roundDisc q r ↔ euclideanLength (x - q) ≤ r :=
  Iff.rfl

/-- Two round `ε`-discs about points more than `2ε` apart are disjoint. -/
theorem roundDisc_disjoint {q q' : Plane} {ε : ℝ} (h : 2 * ε < euclideanLength (q' - q)) :
    Disjoint (roundDisc q ε) (roundDisc q' ε) := by sorry

/-- "each D_i meets no edge not incident to q_i" (`η_e`). -/
theorem roundDisc_disjoint_edge (gen : (Shadow.single C).Generic) {ε : ℝ} (hε : ε < clearance C.P)
    {i j : ZMod C.k} (h : ¬ incident i j) : Disjoint (roundDisc (C.P i) ε) (edgeSegment C.P j) := by
  sorry

/-- "each D_i contains no double point" (`η_X`). -/
theorem crossingPoint_notMem_roundDisc {ε : ℝ} (hε : ε < clearance C.P) (i : ZMod C.k)
    (x : Crossing C.P) : crossingPoint x ∉ roundDisc (C.P i) ε := by sorry

/-- "each D_i meets the two incident edges exactly in the two sub-segments of length ε at q_i":
the arriving edge. -/
theorem roundDisc_inter_edge_in (hL : Regular C.P) {ε : ℝ} (hε : 0 < ε) (k : ℕ)
    (hεl : ε ≤ edgeLen C.P (k - 1)) :
    roundDisc (C.P (k : ZMod C.k)) ε ∩ edgeSegment C.P ((k : ZMod C.k) - 1) =
      {x | ∃ s ∈ Icc (0 : ℝ) ε, x = C.P (k : ZMod C.k) - s • cornerIn C.P k} := by sorry

/-- … and the leaving edge. -/
theorem roundDisc_inter_edge_out (hL : Regular C.P) {ε : ℝ} (hε : 0 < ε) (k : ℕ)
    (hεl : ε ≤ edgeLen C.P k) :
    roundDisc (C.P (k : ZMod C.k)) ε ∩ edgeSegment C.P (k : ZMod C.k) =
      {x | ∃ s ∈ Icc (0 : ℝ) ε, x = C.P (k : ZMod C.k) + s • cornerOut C.P k} := by sorry

end Corner

/-! ## Unit G — the global curve (sm-3:3738-3742 at every corner, glued along the edges) -/

section Global

variable {C : PolyComp} {ε : ℝ} (h : Admissible C ε)
include h

theorem Admissible.regular : Regular C.P := regular_of_generic h.gen

theorem arcLen_pos (k : ℕ) : 0 < arcLen C.P ε k :=
  junctionLength_pos _ _ _ h.pos (abs_cornerTurn_lt_pi h.regular k)

theorem arcLen_le (k : ℕ) : arcLen C.P ε k ≤ 2 * ε :=
  junctionLength_le _ _ _ h.pos (abs_cornerTurn_lt_pi h.regular k)

theorem straight_pos (k : ℕ) : 0 < edgeLen C.P k - 2 * ε := by
  have := three_clearance_le_edgeLen (C := C) k
  have := h.lt
  have := h.pos
  linarith

omit h in
theorem cum_zero : cum C.P ε 0 = 0 := rfl

omit h in
theorem cum_succ (k : ℕ) : cum C.P ε (k + 1) = cumEnd C.P ε k + (edgeLen C.P k - 2 * ε) := rfl

theorem cum_lt_cumEnd (k : ℕ) : cum C.P ε k < cumEnd C.P ε k := by
  unfold cumEnd; linarith [arcLen_pos h k]

theorem cumEnd_lt_cum_succ (k : ℕ) : cumEnd C.P ε k < cum C.P ε (k + 1) := by
  rw [cum_succ]; linarith [straight_pos h k]

theorem cum_strictMono : StrictMono (cum C.P ε) := by sorry

theorem cum_nonneg (k : ℕ) : 0 ≤ cum C.P ε k := by sorry

theorem total_pos : 0 < total C.P ε := by sorry

theorem cumEnd_lt_total {k : ℕ} (hk : k < C.k) : cumEnd C.P ε k < total C.P ε := by sorry

/-- G2 "on the junction at q_k the global angle is the printed junction angle": the earlier
profiles equal `1`, the later ones `0` (`Finset.sum_range_succ` splitting). -/
theorem globalAngle_zone {k : ℕ} (hk : k < C.k) {σ : ℝ} (hσ : σ ∈ Icc (cum C.P ε k) (cum C.P ε (k + 1))) :
    globalAngle C.P ε σ =
      junctionAngle (cumArg C.P k) (cornerTurn C.P k) (arcLen C.P ε k) (σ - cum C.P ε k) := by sorry

/-- G2' the same formula holds on the closed straight part before the junction (there both sides
equal `cumArg k`), so on `[cumEnd (k−1), cum (k+1)]`. -/
theorem globalAngle_zone_left {k : ℕ} (hk : k < C.k) (hk0 : 0 < k) {σ : ℝ}
    (hσ : σ ∈ Icc (cumEnd C.P ε (k - 1)) (cum C.P ε (k + 1))) :
    globalAngle C.P ε σ =
      junctionAngle (cumArg C.P k) (cornerTurn C.P k) (arcLen C.P ε k) (σ - cum C.P ε k) := by sorry

theorem globalAngle_of_nonpos {σ : ℝ} (hσ : σ ≤ 0) : globalAngle C.P ε σ = cornerArg C.P 0 := by sorry

theorem globalAngle_of_total_le {σ : ℝ} (hσ : total C.P ε ≤ σ) : globalAngle C.P ε σ = cumArg C.P C.k := by
  sorry

theorem contDiff_globalAngle : ContDiff ℝ ∞ (globalAngle C.P ε) := by sorry

theorem hasDerivAt_roundedArc (σ : ℝ) :
    HasDerivAt (roundedArc C.P ε) (unitDir (globalAngle C.P ε σ)) σ := by sorry

theorem contDiff_roundedArc : ContDiff ℝ ∞ (roundedArc C.P ε) := by sorry

/-- G5 on the zone of `q_k` (junction + following straight part) the rounded arc is the junction
curve at `q_k` started at `A₀(q_k)`: same value at `cum k` (induction on `k` through
`A1_add_straight` and `junctionCurve_end`) and same derivative (`globalAngle_zone`). -/
theorem roundedArc_zone {k : ℕ} (hk : k < C.k) {σ : ℝ} (hσ : σ ∈ Icc (cum C.P ε k) (cum C.P ε (k + 1))) :
    roundedArc C.P ε σ =
      junctionCurve (A0 C.P ε k) (cumArg C.P k) (cornerTurn C.P k) (arcLen C.P ε k) (σ - cum C.P ε k) := by
  sorry

theorem roundedArc_cum {k : ℕ} (hk : k ≤ C.k) : roundedArc C.P ε (cum C.P ε k) = A0 C.P ε k := by sorry

/-- G6 closure: `L_ε(Λ) = A₀(q_0)`, "the total displacement is Σ δ_k = 0". -/
theorem roundedArc_total : roundedArc C.P ε (total C.P ε) = A0 C.P ε 0 := by sorry

/-- G7 the seam: on the last straight part the arc is the (backward extended) junction curve at
`q_0` shifted by `Λ`. -/
theorem roundedArc_seam {σ : ℝ} (hσ : σ ∈ Icc (cumEnd C.P ε (C.k - 1)) (total C.P ε)) :
    roundedArc C.P ε σ =
      junctionCurve (A0 C.P ε 0) (cumArg C.P 0) (cornerTurn C.P 0) (arcLen C.P ε 0) (σ - total C.P ε) := by
  sorry

omit h in
theorem roundedCurve_periodic : Function.Periodic (roundedCurve C.P ε) 1 := by
  intro t; simp [roundedCurve, Int.fract_add_one]

omit h in
theorem roundedCurve_eq_arc {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    roundedCurve C.P ε t = roundedArc C.P ε (total C.P ε * t) := by
  simp [roundedCurve, Int.fract_eq_self.mpr ht]

/-- G8 near a non-integer parameter the curve is the arc composed with an affine map. -/
theorem roundedCurve_eventuallyEq_arc {t : ℝ} (ht : Int.fract t ≠ 0) :
    roundedCurve C.P ε =ᶠ[nhds t] fun s => roundedArc C.P ε (total C.P ε * (s - ⌊t⌋)) := by sorry

/-- G8 near an integer parameter (the seam) the curve is the junction curve at `q_0`. -/
theorem roundedCurve_eventuallyEq_seam (m : ℤ) :
    roundedCurve C.P ε =ᶠ[nhds (m : ℝ)] fun s =>
      junctionCurve (A0 C.P ε 0) (cumArg C.P 0) (cornerTurn C.P 0) (arcLen C.P ε 0)
        (total C.P ε * (s - m)) := by sorry

theorem contDiff_roundedCurve : ContDiff ℝ ∞ (roundedCurve C.P ε) := by sorry

theorem hasDerivAt_roundedCurve (t : ℝ) :
    HasDerivAt (roundedCurve C.P ε)
      (total C.P ε • unitDir (globalAngle C.P ε (total C.P ε * Int.fract t))) t := by sorry

theorem deriv_roundedCurve (t : ℝ) :
    deriv (roundedCurve C.P ε) t = total C.P ε • unitDir (globalAngle C.P ε (total C.P ε * Int.fract t)) :=
  (hasDerivAt_roundedCurve h t).deriv

theorem deriv_roundedCurve_ne_zero (t : ℝ) : deriv (roundedCurve C.P ε) t ≠ 0 := by sorry

theorem euclideanLength_deriv_roundedCurve (t : ℝ) :
    euclideanLength (deriv (roundedCurve C.P ε) t) = total C.P ε := by sorry

theorem normalize_deriv_roundedCurve (t : ℝ) :
    normalize (deriv (roundedCurve C.P ε) t) = unitDir (globalAngle C.P ε (total C.P ε * Int.fract t)) := by
  sorry

omit h in
theorem jStart_zero : jStart C.P ε 0 = 0 := by
  show cum C.P ε 0 / total C.P ε = 0
  rw [show cum C.P ε 0 = 0 from rfl, zero_div]

theorem jStart_count : jStart C.P ε C.k = 1 := by
  unfold jStart total; exact div_self (total_pos h).ne'

theorem jStart_lt_jEnd (k : ℕ) : jStart C.P ε k < jEnd C.P ε k := by
  unfold jStart jEnd; exact div_lt_div_of_pos_right (cum_lt_cumEnd h k) (total_pos h)

theorem jEnd_lt_jStart_succ (k : ℕ) : jEnd C.P ε k < jStart C.P ε (k + 1) := by
  unfold jStart jEnd; exact div_lt_div_of_pos_right (cumEnd_lt_cum_succ h k) (total_pos h)

theorem jStart_nonneg (k : ℕ) : 0 ≤ jStart C.P ε k := by
  unfold jStart; exact div_nonneg (cum_nonneg h k) (total_pos h).le

theorem jEnd_lt_one {k : ℕ} (hk : k < C.k) : jEnd C.P ε k < 1 := by
  unfold jEnd; rw [div_lt_one (total_pos h)]; exact cumEnd_lt_total h hk

/-- G9 on the junction parameter interval the curve is the junction curve at `q_k`. -/
theorem roundedCurve_junction {k : ℕ} (hk : k < C.k) {t : ℝ} (ht : t ∈ Icc (jStart C.P ε k) (jEnd C.P ε k)) :
    roundedCurve C.P ε t =
      junctionCurve (A0 C.P ε k) (cumArg C.P k) (cornerTurn C.P k) (arcLen C.P ε k)
        (total C.P ε * t - cum C.P ε k) := by sorry

/-- G9 on the straight parameter interval the curve is the arclength traversal of the edge `k`. -/
theorem roundedCurve_straight {k : ℕ} (hk : k < C.k) {t : ℝ}
    (ht : t ∈ Icc (jEnd C.P ε k) (jStart C.P ε (k + 1))) :
    roundedCurve C.P ε t = A1 C.P ε k + (total C.P ε * t - cumEnd C.P ε k) • cornerOut C.P k := by sorry

omit h in
theorem junctionLift_eq (k : ℕ) (t : ℝ) :
    junctionLift C.P ε k t =
      junctionAngle (cumArg C.P k) (cornerTurn C.P k) (arcLen C.P ε k) (total C.P ε * t - cum C.P ε k) := rfl

/-- G10 the unit tangent on the junction is `unitDir (junctionLift k)`. -/
theorem tangent_junction {k : ℕ} (hk : k < C.k) {t : ℝ} (ht : t ∈ Icc (jStart C.P ε k) (jEnd C.P ε k)) :
    normalize (deriv (roundedCurve C.P ε) t) = unitDir (junctionLift C.P ε k t) := by sorry

/-- G10 the unit tangent on the straight part is the edge direction. -/
theorem tangent_straight {k : ℕ} (hk : k < C.k) {t : ℝ}
    (ht : t ∈ Icc (jEnd C.P ε k) (jStart C.P ε (k + 1))) :
    normalize (deriv (roundedCurve C.P ε) t) = cornerOut C.P k := by sorry

/-- The fundamental period is covered by the junction intervals and the open straight intervals. -/
theorem cover {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    (∃ k < C.k, t ∈ Icc (jStart C.P ε k) (jEnd C.P ε k)) ∨
      ∃ k < C.k, t ∈ Ioo (jEnd C.P ε k) (jStart C.P ε (k + 1)) := by sorry

end Global

/-! ## Unit E — clauses (a), (b), (d), (e) from the construction -/

section Clauses

variable {C : PolyComp} {ε : ℝ} (h : Admissible C ε)
include h

/-- The junction at `q_k` lies in the disc about `q_k` (J7 transported by `roundedCurve_junction`;
`A₀ + ε u = q_k`). -/
theorem roundedCurve_junction_mem_roundDisc {k : ℕ} (hk : k < C.k) {t : ℝ}
    (ht : t ∈ Icc (jStart C.P ε k) (jEnd C.P ε k)) :
    roundedCurve C.P ε t ∈ roundDisc (C.P (k : ZMod C.k)) ε := by sorry

/-- A point of an open straight part is outside every disc: at distance `> ε` from the two ends
of its edge and `> 2ε` from every other corner (`η_v`, `η_e`). -/
theorem roundedCurve_straight_notMem_roundDisc {k : ℕ} (hk : k < C.k) {t : ℝ}
    (ht : t ∈ Ioo (jEnd C.P ε k) (jStart C.P ε (k + 1))) (i : ZMod C.k) :
    roundedCurve C.P ε t ∉ roundDisc (C.P i) ε := by sorry

/-- "contains the whole of the modification made at q_i", and nothing else of the curve
(the consumer's "disc meeting the diagram in one embedded arc"). -/
theorem roundedCurve_mem_roundDisc_iff {k : ℕ} (hk : k < C.k) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    roundedCurve C.P ε t ∈ roundDisc (C.P (k : ZMod C.k)) ε ↔ t ∈ Icc (jStart C.P ε k) (jEnd C.P ε k) := by
  sorry

theorem roundedCurve_injOn_junction {k : ℕ} (hk : k < C.k) :
    InjOn (roundedCurve C.P ε) (Icc (jStart C.P ε k) (jEnd C.P ε k)) := by sorry

/-- (a), trace form: the trace of `L_ε` outside the discs is the trace of `L` outside the discs. -/
theorem trace_eq_outside_discs :
    {x | x ∈ range (roundedCurve C.P ε) ∧ ∀ k : ZMod C.k, x ∉ roundDisc (C.P k) ε} =
      {x | (∃ k : ZMod C.k, x ∈ edgeSegment C.P k) ∧ ∀ k : ZMod C.k, x ∉ roundDisc (C.P k) ε} := by sorry

theorem clauseA : ClauseA C.P ε (roundedCurve C.P ε) :=
  ⟨fun _ hk _ ht => roundedCurve_straight h hk ht, trace_eq_outside_discs h⟩

theorem clauseB : ClauseB C.P ε (roundedCurve C.P ε) := by sorry

/-- (d) by the accepted `rot_eq_rotationNumber_of_rounding` (cf:lem-turnlift (iii-a)) with the
subdivision `jStart`, `jEnd`, the lifts `junctionLift` (clause (b)) and the straight tangents
(`tangent_straight`). -/
theorem clauseD : ClauseD C.P (roundedCurve C.P ε) := by sorry

theorem clauseE : ClauseE C.P ε (roundedCurve C.P ε) := by sorry

end Clauses

/-! ## Unit D — the carried diagram and clause (c) (sm-3:3841-3848) -/

section CarriedDiagram

variable {C : PolyComp} {ε : ℝ} (h : Admissible C ε)
  (ovr : (Shadow.single C).Crossing → (Shadow.single C).Strand) (mem : ∀ x, ovr x ∈ x.val)

/-- The parameter of `L_ε` at which the occurrence `v` (crossing `v.1`, strand = edge `v.2.1.2`
with crossing parameter `τ`) is met: `(cumEnd j + τ |δ_j| − ε)/Λ` (the crossing point is at distance
`τ|δ_j|` from `q_j` along the edge, the straight part starts `ε` after `q_j`). -/
def crossingPar (v : (mkSingle C h.gen ovr mem).Γ.Visit) : ℝ :=
  (cumEnd C.P ε v.2.1.2.val + (mkSingle C h.gen ovr mem).crossingParam v.1 v.2.2 * edgeLen C.P v.2.1.2.val - ε) /
    total C.P ε

include h

/-- D1 every double point of `L` is at distance `> ε` from the two ends of each of its edges, so it
lies on the straight parts (`η_X`). -/
theorem crossingPar_mem (v : (mkSingle C h.gen ovr mem).Γ.Visit) :
    crossingPar h ovr mem v ∈ Ico (0 : ℝ) 1 := by sorry

theorem crossingPar_mem_straight (v : (mkSingle C h.gen ovr mem).Γ.Visit) :
    crossingPar h ovr mem v ∈
      Ioo (jEnd C.P ε v.2.1.2.val) (jStart C.P ε (v.2.1.2.val + 1)) := by sorry

theorem roundedCurve_crossingPar (v : (mkSingle C h.gen ovr mem).Γ.Visit) :
    roundedCurve C.P ε (crossingPar h ovr mem v) = (mkSingle C h.gen ovr mem).Γ.crossingPoint v.1 := by
  sorry

theorem deriv_roundedCurve_crossingPar (v : (mkSingle C h.gen ovr mem).Γ.Visit) :
    ∃ r : ℝ, 0 < r ∧ deriv (roundedCurve C.P ε) (crossingPar h ovr mem v) =
      r • (mkSingle C h.gen ovr mem).Γ.dir v.2.1 := by sorry

theorem crossingPar_injective : Function.Injective (crossingPar h ovr mem) := by sorry

/-- D2 the order of the occurrences along `L_ε` is their traversal order in `D`: `visitCoord v =
j.val + τ` and `crossingPar v = (cumEnd j + τ|δ_j| − ε)/Λ` are both lexicographic in `(j, τ)`. -/
theorem crossingPar_order (v w : (mkSingle C h.gen ovr mem).Γ.Visit) :
    (mkSingle C h.gen ovr mem).visitCoord v < (mkSingle C h.gen ovr mem).visitCoord w ↔
      crossingPar h ovr mem v < crossingPar h ovr mem w := by sorry

/-- D3 "no double point is created or destroyed" (sm-3:3838-3840): a double point of `L_ε` has both
parameters on open straight parts (a junction point is alone in its disc, and its disc meets the
rest of the curve only at its two ends, `roundedCurve_mem_roundDisc_iff` + injectivity), hence is a
common point of two edges of `L`, off the corners; adjacent edges meet only at their common corner
(`regular_adjacent_meet`), so the two edges are remote and the point is a crossing of `L`, whose
two occurrences have these parameters. -/
theorem double_eq_crossingPar {s t : ℝ} (hst : IsDoublePt (roundedCurve C.P ε) s t) :
    ∃ v w : (mkSingle C h.gen ovr mem).Γ.Visit, v.1 = w.1 ∧ v ≠ w ∧
      crossingPar h ovr mem v = s ∧ crossingPar h ovr mem w = t := by sorry

/-- The carrying record `Round(L, D, ε)` — "the diagram data are inherited" (sm-3:4368). -/
def carries : Carries (roundedCurve C.P ε) (mkSingle C h.gen ovr mem) where
  one_component := rfl
  par := crossingPar h ovr mem
  par_mem := crossingPar_mem h ovr mem
  par_eval := roundedCurve_crossingPar h ovr mem
  par_dir := deriv_roundedCurve_crossingPar h ovr mem
  par_injective := crossingPar_injective h ovr mem
  double_par := fun _ _ hst => double_eq_crossingPar h ovr mem hst
  par_order := crossingPar_order h ovr mem

omit h in
/-- Generic facts about any carrying record: the smooth sign at a crossing is the diagram's sign
(the branch directions are positive multiples of the strand directions, `det` is bilinear), so the
writhes agree. -/
theorem Carries.sign_eq {γ : ℝ → Plane} {D : Diagram} (rec : Carries γ D) (x : D.Γ.Crossing) :
    rec.sign x = D.sign x := by sorry

omit h in
theorem Carries.writhe_eq {γ : ℝ → Plane} {D : Diagram} (rec : Carries γ D) : rec.writhe = D.writhe := by
  unfold Carries.writhe Diagram.writhe
  exact Finset.sum_congr rfl fun x _ => by rw [rec.sign_eq x]

omit h in
/-- The parameter of an occurrence lies on the occurrence's strand (from `par_eval`: the crossing
point is on both strands, `Shadow.crossingPoint_mem`). -/
theorem Carries.mem_seg {γ : ℝ → Plane} {D : Diagram} (rec : Carries γ D) (v : D.Γ.Visit) :
    γ (rec.par v) ∈ D.Γ.seg v.2.1 := by
  rw [rec.par_eval]; exact D.Γ.crossingPoint_mem v.1 v.2.2

/-- (c), first conjunct: the double points of `L_ε` are exactly the crossing points of `D`
(`double_eq_crossingPar` and, conversely, each crossing's two occurrences give a double point). -/
theorem doublePoints_eq_crossingPoints :
    {p | ∃ s t, IsDoublePt (roundedCurve C.P ε) s t ∧ p = roundedCurve C.P ε s} =
      range (mkSingle C h.gen ovr mem).Γ.crossingPoint := by sorry

theorem clauseC : ClauseC (mkSingle C h.gen ovr mem) (roundedCurve C.P ε) :=
  ⟨doublePoints_eq_crossingPoints h ovr mem,
    fun rec v => ⟨rec.mem_seg v, rec.par_dir v⟩,
    fun rec x => rec.sign_eq x,
    fun rec => rec.writhe_eq⟩

end CarriedDiagram

end Rounding

open Rounding

/-! ## Unit R — the row from the chain -/

/-- Destructuring the diagram hypothesis: a `Diagram` whose shadow is `Shadow.single ⟨n, hn, L⟩` is
`mkSingle ⟨n, hn, L⟩ gen ovr mem` for its own data, and the row hypotheses give `Admissible`. -/
theorem cf_lem_rounding : RoundingData := by
  refine
    { clearance_pos := ?_, curve := ?_, diagram := ?_, a := ?_, b := ?_, c := ?_, d := ?_, e := ?_ }
  · intro n _ hn L D hD hturn
    obtain ⟨Γ, gen, ovr, mem⟩ := D
    simp only at hD
    subst hD
    exact clearance_pos (C := ⟨n, hn, L⟩) gen
  · intro n _ hn L D hD hturn ε hε0 hε1
    obtain ⟨Γ, gen, ovr, mem⟩ := D
    simp only at hD
    subst hD
    have h : Admissible ⟨n, hn, L⟩ ε := ⟨gen, hturn, hε0, hε1⟩
    exact ⟨contDiff_roundedCurve (C := ⟨n, hn, L⟩) h, roundedCurve_periodic (C := ⟨n, hn, L⟩),
      deriv_roundedCurve_ne_zero (C := ⟨n, hn, L⟩) h⟩
  · intro n _ hn L D hD hturn ε hε0 hε1
    obtain ⟨Γ, gen, ovr, mem⟩ := D
    simp only at hD
    subst hD
    have h : Admissible ⟨n, hn, L⟩ ε := ⟨gen, hturn, hε0, hε1⟩
    exact ⟨carries (C := ⟨n, hn, L⟩) h ovr mem⟩
  · intro n _ hn L D hD hturn ε hε0 hε1
    obtain ⟨Γ, gen, ovr, mem⟩ := D
    simp only at hD
    subst hD
    have h : Admissible ⟨n, hn, L⟩ ε := ⟨gen, hturn, hε0, hε1⟩
    exact clauseA (C := ⟨n, hn, L⟩) h
  · intro n _ hn L D hD hturn ε hε0 hε1
    obtain ⟨Γ, gen, ovr, mem⟩ := D
    simp only at hD
    subst hD
    have h : Admissible ⟨n, hn, L⟩ ε := ⟨gen, hturn, hε0, hε1⟩
    exact clauseB (C := ⟨n, hn, L⟩) h
  · intro n _ hn L D hD hturn ε hε0 hε1
    obtain ⟨Γ, gen, ovr, mem⟩ := D
    simp only at hD
    subst hD
    have h : Admissible ⟨n, hn, L⟩ ε := ⟨gen, hturn, hε0, hε1⟩
    exact clauseC (C := ⟨n, hn, L⟩) h ovr mem
  · intro n _ hn L D hD hturn ε hε0 hε1
    obtain ⟨Γ, gen, ovr, mem⟩ := D
    simp only at hD
    subst hD
    have h : Admissible ⟨n, hn, L⟩ ε := ⟨gen, hturn, hε0, hε1⟩
    exact clauseD (C := ⟨n, hn, L⟩) h
  · intro n _ hn L D hD hturn ε hε0 hε1
    obtain ⟨Γ, gen, ovr, mem⟩ := D
    simp only at hD
    subst hD
    have h : Admissible ⟨n, hn, L⟩ ε := ⟨gen, hturn, hε0, hε1⟩
    exact clauseE (C := ⟨n, hn, L⟩) h

end

end SM
