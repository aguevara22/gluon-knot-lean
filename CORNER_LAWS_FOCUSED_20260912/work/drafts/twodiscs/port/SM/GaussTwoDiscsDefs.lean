-- Ported <HH:MM>Z 2026-09-19 from work/drafts/twodiscs/W2_Assembled.lean by the pod executor (files prepared by the U12 assembler)
import SM.EmbeddedRotation
import SM.LinkMoves
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.SetTheory.Cardinal.Finite
import SM.DeletedTuple
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.Baire.CompleteMetrizable

/-! # Row 57 lem:gauss-two-discs — definitions (frozen statement part §1-§4)

Written 2026-09-19 (D-AUTH-20260919 G-09: row 57 un-deferred).  Source:
reference/SM/sm-3-statesum.tex:428-436 (statement), 437-542 (proof).  Plan: PLAN_A.md (same
directory), which records the fidelity risks FR-TD-1..6 of PLDISCS_FEASIBILITY.md §2.5 and the new
ones FR-TD-7..12 with the reading chosen here.  Ported to work/lean as the module chain `SM.GaussTwoDiscsDefs → …PL → …Ears → …Ambient → …Extension → SM.GaussTwoDiscs`.
The frozen text (`Statements_FINAL.lean`, checked by `check_57_identity.py`): the DEFS block is this module's `namespace SM … §4`; the BUNDLE and THM blocks are in `SM.GaussTwoDiscs`.

Printed statement, clause by clause (memo §2.1 numbering):
* 57a "A simple polygonal circle in the oriented sphere has exactly two complementary regions"
* 57b "and both closures are PL discs."
* 57c "Finite prescribed positive PL boundary maps between such discs extend to positive PL disc maps."
* 57d "A continuous positive boundary map also extends to a topological disc map."
* 57e "The statement includes the exterior region."

Readings fixed here (details in PLAN_A.md §2):
* circle = `Embedded P` (accepted, SM/EmbeddedRotation.lean), its image `embeddedPolygonImage P = ⋃ edgeSegment`;
* sphere = `OnePoint Plane`, oriented by the plane's `det`; the point at infinity is the printed
  "one point off the curve" (sm-3:439);
* regions = connected components of the complement in the sphere (`ConnectedComponents`,
  `connectedComponentIn`); the exterior region is the component of `∞`;
* PL structure of the sphere = the printed two-disc model (sm-3:440-456): the square `Q_L` with the
  plane's straight structure, capped by a second square `Q_1` carried to the exterior of `Q_L` by the
  sup-norm radial inversion `capInvFun L` (orientation-preserving, affine on the seam);
* PL disc = image of a convex compact set with nonempty interior (`Link.IsDisc`, LinkMoves.lean:100) under
  a homeomorphism affine with positive determinant on every triangle of a finite straight
  triangulation (`Triangulation`, `IsPositivePLOn`);
* boundary maps are given in traversal coordinates by a lift `φ : ℝ → ℝ` (`traversal`, accepted);
  "positive" = orientation-preserving for the induced boundary orientations of the two discs, which
  for the traversal of `P` around region `s` is `traversalPositiveFor P s` (left turn = bounded region
  on the left, as in the accepted `EmbeddedRotationData.orientation`); "finite PL" = affine between
  finitely many marks of one period (`IsFinitePL`, the `rexB_pl` pattern). -/

/-! ## Provenance and assembly history

`W2_Assembled.lean` (work/drafts/twodiscs, 20 912 lines, 92 leaves, all proved) = `Skeleton_FINAL.lean`
(= `Statements_FINAL.lean` + the leaf statements `U<k>_…` of units U1-U11 + the assembly of the row and of the
three consumer bridges from the leaves) + the wave-1 unit files `W1_U1, W1_U2, W1_U3, W1_U4, W1_U10, W1_U11`
+ the wave-2 unit files `W2_U5, W2_U6, W2_U7, W2_U8, W2_U9`, merged by alignment (each unit's `u<k>h_` helpers
sit where that unit put them, immediately before the leaf that uses them; every leaf carries the body of the
unit that closed it; imports are the union).  Four leaf statements were corrected under rule 3 (marked
`Assembly correction (wave k, rule 3)` in their docstrings): `U3_isPositivePLFromPlane_inv` (+ `hL : 0 < L`,
false for `L ≤ 0`), `U4_polygonImage_ear` (+ `hP`, `hac`, `hstrict`, false without them), `U5_exists_ear_homeo`
(+ `hcut`, false for a reflex ear) and `U5_pushforward_edges` (replaced by the corrected form proved by U5,
false as first stated: kernel-checked counterexample `u5h_pushforward_edges_false`); the only call site
affected (`U10_pl_extension`) was patched.  Reports: W1_ASSEMBLY_REPORT.md, W2_ASSEMBLY_REPORT.md, PORT_REPORT.md.
Axioms of `SM.lem_gauss_two_discs`: `[propext, Classical.choice, Quot.sound]`.

Module chain (each imports the previous): `SM.GaussTwoDiscsDefs` (this file: frozen §1-§4),
`SM.GaussTwoDiscsPL` (U1-U3: convex/affine toolkit, triangulations, refinement, chart algebra),
`SM.GaussTwoDiscsEars` (U4: ear triangulation of an embedded polygon), `SM.GaussTwoDiscsAmbient`
(U5-U9: ear-cut homeomorphism, ambient parametrisation, the two regions and their PL-disc closures,
orientation), `SM.GaussTwoDiscsExtension` (U10-U11: PL and topological extension of boundary maps),
`SM.GaussTwoDiscs` (the §5 bundle `GaussTwoDiscsData`, the row `lem_gauss_two_discs`, the §6 bridges). -/


namespace SM

open Set OnePoint

variable {n : ℕ}

/-! ## §1 The circle and its two complementary regions in the sphere -/

/-- The polygonal circle `C` in the plane: the union of the edge segments (def:polygon vocabulary;
for `Embedded P` it is the simple closed curve `range (traversal P)`). -/
def embeddedPolygonImage (P : LabelledTuple n) : Set Plane := ⋃ i, edgeSegment P i

/-- The oriented sphere (sm-3:430 "in the oriented sphere"): the one-point compactification of the
plane, oriented by the plane's `det`. -/
abbrev Sphere : Type := OnePoint Plane

/-- The circle as a subset of the sphere. -/
def sphereCircle (P : LabelledTuple n) : Set Sphere := ((↑) : Plane → Sphere) '' embeddedPolygonImage P

/-- The complement of the circle in the sphere (its connected components are the printed
"complementary regions"). -/
def sphereComplement (P : LabelledTuple n) : Set Sphere := (sphereCircle P)ᶜ

/-- The exterior region: the complementary region containing the point at infinity
(sm-3:434 "the exterior region"; sm-3:448-456 "the actual one-point-compactified exterior"). -/
def exteriorRegion (P : LabelledTuple n) : Set Sphere :=
  connectedComponentIn (sphereComplement P) ∞

/-- The interior (bounded) region: the rest of the complement; by 57a it is one connected region. -/
def interiorRegion (P : LabelledTuple n) : Set Sphere := sphereComplement P \ exteriorRegion P

/-- Which of the two complementary regions. -/
inductive Side
  | inner
  | outer

/-- The two regions by side. -/
def regionOf (P : LabelledTuple n) : Side → Set Sphere
  | .inner => interiorRegion P
  | .outer => exteriorRegion P

/-! ## §2 Straight triangulations and positive PL maps in the plane (new vocabulary) -/

/-- A straight, positively oriented, nondegenerate triangle of the plane. -/
structure Triangle where
  /-- the three vertices, in positive (counterclockwise) order -/
  v : Fin 3 → Plane
  pos : 0 < det (v 1 - v 0) (v 2 - v 0)

/-- The closed triangle spanned by the vertices. -/
def Triangle.carrier (T : Triangle) : Set Plane := convexHull ℝ (range T.v)

/-- A finite straight triangulation of a plane set `X`: finitely many straight triangles covering
exactly `X`, any two of which meet in a common face (the convex hull of their common vertices:
empty, a vertex, an edge, or the whole triangle). -/
structure Triangulation (X : Set Plane) where
  faces : Set Triangle
  finite : faces.Finite
  cover : (⋃ T ∈ faces, T.carrier) = X
  inter : ∀ T ∈ faces, ∀ T' ∈ faces,
    T.carrier ∩ T'.carrier = convexHull ℝ (range T.v ∩ range T'.v)

/-- `f` agrees with an affine map of the plane on `S`. -/
def AffineOn (f : Plane → Plane) (S : Set Plane) : Prop :=
  ∃ (M : Plane →ₗ[ℝ] Plane) (b : Plane), ∀ x ∈ S, f x = M x + b

/-- `f` is affine on the triangle `T` with positive determinant (orientation-preserving). -/
def IsPositiveAffineOn (f : Plane → Plane) (T : Triangle) : Prop :=
  AffineOn f T.carrier ∧ 0 < det (f (T.v 1) - f (T.v 0)) (f (T.v 2) - f (T.v 0))

/-- `f` is positive PL with respect to the triangulation `K`: affine with positive determinant on
each of its triangles. -/
def IsPositivePLOn (f : Plane → Plane) {X : Set Plane} (K : Triangulation X) : Prop :=
  ∀ T ∈ K.faces, IsPositiveAffineOn f T

/-- `f` restricts to a homeomorphism of `S` onto `S'`. -/
def IsHomeoOnto {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (S : Set α) (S' : Set β) (f : α → β) : Prop :=
  ∃ e : S ≃ₜ S', ∀ z : S, (e z : β) = f z

/-- **PL disc in the plane** (sm-3:431 "PL discs"): the image of a convex compact set with nonempty
interior (`Link.IsDisc`, LinkMoves.lean:100, the accepted convex model disc) under a homeomorphism that is affine with
positive determinant on each triangle of a finite straight triangulation of the model. -/
def IsPLDisc (S : Set Plane) : Prop :=
  ∃ (D : Set Plane) (K : Triangulation D) (g : Plane → Plane),
    Link.IsDisc D ∧ IsPositivePLOn g K ∧ IsHomeoOnto D S g

/-! ## §3 The PL structure of the sphere: the printed two-disc model (sm-3:440-456)

The rectangle is the square `Q_L = {|x₁|, |x₂| ≤ L}` with the plane's straight structure (chart
`false`, the coercion `Plane → Sphere`).  The cap is the square `Q_1`, carried onto the closed
exterior of `Q_L` together with `∞` by the sup-norm radial inversion
`capInvFun L y = (L / ‖y‖_∞²) • (y₁, −y₂)` (chart `true`; `0 ↦ ∞`).  It is a homeomorphism of
`Q_1 \ {0}` onto `{‖x‖_∞ ≥ L}`, self-inverse up to the scale, direction-preserving up to the
reflection `y₂ ↦ −y₂` (which makes it orientation-preserving, so that "positive" means `det > 0`
in either chart), and on the seam `‖y‖_∞ = 1` it is the affine map `y ↦ L • (y₁, −y₂)`.  The
printed version uses the Euclidean radial map `ru ↦ (R(u)/r)u` onto the unit disc (sm-3:449-452);
the sup-norm version is the same construction in the square's own gauge and glues affinely
(FR-TD-7). -/

/-- The sup norm `‖x‖_∞ = max |x₁| |x₂|` of the plane (written out, instance-free). -/
def supNorm (x : Plane) : ℝ := max |x.1| |x.2|

/-- The closed square of half-width `L` about the origin. -/
def square (L : ℝ) : Set Plane := {x | supNorm x ≤ L}

/-- The polygon lies strictly inside the model square `Q_L` (sm-3:439 "inside a large rectangle"). -/
def InsideModel (L : ℝ) (P : LabelledTuple n) : Prop := ∀ i, supNorm (P i) < L

/-- Sup-norm radial inversion across `∂Q_L`, composed with the reflection `y₂ ↦ −y₂`. -/
noncomputable def capInvFun (L : ℝ) (y : Plane) : Plane := (L / supNorm y ^ 2) • (y.1, -y.2)

/-- The cap chart of the two-disc model at scale `L`: `Q_1 → Sphere`, `0 ↦ ∞`. -/
noncomputable def capChart (L : ℝ) (y : Plane) : Sphere :=
  if y = 0 then ∞ else ((capInvFun L y : Plane) : Sphere)

/-- The two charts of the model: `false` = the plane chart on `Q_L`, `true` = the cap chart on `Q_1`. -/
noncomputable def modelChart (L : ℝ) : Bool → Plane → Sphere
  | false => fun x => (x : Sphere)
  | true => capChart L

/-- The chart domains. -/
def modelDomain (L : ℝ) : Bool → Set Plane
  | false => square L
  | true => square 1

/-- Plane coordinates of a finite point of the sphere (junk value `0` at `∞`). -/
def planeOf : Sphere → Plane
  | ∞ => 0
  | (x : Plane) => x

/-- The inverse charts (junk outside the chart images). -/
noncomputable def modelChartInv (L : ℝ) : Bool → Sphere → Plane
  | false => planeOf
  | true => fun z => match z with
    | ∞ => 0
    | (x : Plane) => capInvFun L x

/-- The part of `S ⊆ Sphere` seen in chart `b`, in chart coordinates. -/
def chartPart (L : ℝ) (b : Bool) (S : Set Sphere) : Set Plane :=
  modelDomain L b ∩ modelChart L b ⁻¹' S

/-- `f : Sphere → Plane` is positive PL on `S` (model at scale `L`): in each chart, `S` carries a
finite straight triangulation on whose triangles `f ∘ chart` is affine with positive determinant. -/
def IsPositivePLToPlane (L : ℝ) (S : Set Sphere) (f : Sphere → Plane) : Prop :=
  ∀ b : Bool, ∃ K : Triangulation (chartPart L b S), IsPositivePLOn (f ∘ modelChart L b) K

/-- **PL disc in the sphere with boundary `B`** (model at scale `L`): `S` is carried onto a convex
compact plane set with nonempty interior by a homeomorphism that is positive PL in the model
charts and carries `B` onto the frontier of the model; the circle `B` lies in the closed region `S`
(`B ⊆ S`).  For `S` inside the plane chart this is `IsPLDisc` of its plane trace (bridge
`isPLDisc_of_isPLDiscSphere` below). -/
def IsPLDiscSphere (L : ℝ) (S B : Set Sphere) : Prop :=
  ∃ (D : Set Plane) (f : Sphere → Plane),
    Link.IsDisc D ∧ B ⊆ S ∧ IsHomeoOnto S D f ∧ f '' B = frontier D ∧ IsPositivePLToPlane L S f

/-- `F : Sphere → Sphere` is positive PL from `S` (model `L`) to the sphere with model `L'`: in
each source chart, `S` carries a finite straight triangulation each of whose triangles is sent by
`F` into the image of a single target chart, where `F` read in the two charts is affine with
positive determinant. -/
def IsPositivePLSphereMap (L L' : ℝ) (S : Set Sphere) (F : Sphere → Sphere) : Prop :=
  ∀ b : Bool, ∃ K : Triangulation (chartPart L b S), ∀ T ∈ K.faces, ∃ b' : Bool,
    (∀ x ∈ T.carrier, F (modelChart L b x) ∈ modelChart L' b' '' modelDomain L' b') ∧
    IsPositiveAffineOn (modelChartInv L' b' ∘ F ∘ modelChart L b) T

/-! ## §4 Boundary maps in traversal coordinates (sm-3:431-434) -/

/-- `φ` is piecewise affine with finitely many pieces on one period `[0, n]`
(sm-3:431 "finite prescribed ... PL": marks `0 = a 0 < a 1 < ⋯ < a m = n`, affine between them; the
accepted `rexB_pl` pattern of def:gauss-record). -/
def IsFinitePL (n : ℕ) (φ : ℝ → ℝ) : Prop :=
  ∃ (m : ℕ) (a : ℕ → ℝ), a 0 = 0 ∧ a m = n ∧ (∀ j < m, a j < a (j + 1)) ∧
    ∀ j < m, ∃ c d : ℝ, ∀ x ∈ Icc (a j) (a (j + 1)), φ x = c * x + d

/-- The traversal of `P` runs positively around the region `s` (the region on its left): for the
interior region iff `rotationNumber P > 0` (counterclockwise traversal, the accepted reading "left
turn = bounded region on the left" of `EmbeddedRotationData.orientation`), for the exterior region
iff `rotationNumber P < 0`.  This is the *induced-boundary-orientation* convention: the boundary of
an oriented disc is oriented so that the disc lies on its left, and for the sphere oriented by the
plane's `det` the two regions induce opposite orientations on the common circle.  The definition
is meaningful because the accepted `cb_embedded_rotation.pm_one` gives `rotationNumber P = ±1` for
`Embedded P`, so `0 < rotationNumber P` (counterclockwise) and `rotationNumber P < 0` (clockwise)
are the only two cases and exactly one of them holds. -/
def traversalPositiveFor [NeZero n] (P : LabelledTuple n) (s : Side) : Prop :=
  (0 < rotationNumber P ↔ s = Side.inner)

/-- A **positive boundary map** from `∂(region s of P)` to `∂(region s' of P')`, given in traversal
coordinates by its lift `φ : ℝ → ℝ` (`β (traversal P x) = traversal P' (φ x)`): continuous, strictly
monotone, of degree one, and orientation-preserving for the induced boundary orientations — `φ`
increases when the two traversals run positively around their regions together or negatively
together, and decreases otherwise (sm-3:431-434 "positive"). -/
structure IsPositiveBoundaryLift [NeZero n] {n' : ℕ} [NeZero n'] (P : LabelledTuple n) (s : Side)
    (P' : LabelledTuple n') (s' : Side) (φ : ℝ → ℝ) : Prop where
  continuous : Continuous φ
  same : (traversalPositiveFor P s ↔ traversalPositiveFor P' s') →
    StrictMono φ ∧ ∀ x, φ (x + n) = φ x + n'
  opposite : ¬ (traversalPositiveFor P s ↔ traversalPositiveFor P' s') →
    StrictAnti φ ∧ ∀ x, φ (x + n) = φ x - n'



end SM
