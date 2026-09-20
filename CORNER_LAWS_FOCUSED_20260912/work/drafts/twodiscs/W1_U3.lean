import SM.EmbeddedRotation
import SM.LinkMoves
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.SetTheory.Cardinal.Finite
import SM.DeletedTuple
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.Baire.CompleteMetrizable

/-! ### Skeleton note (U0, 2026-09-19)

`Skeleton_FINAL.lean` = `Statements_FINAL.lean` (frozen; the definitions block, the bundle
`GaussTwoDiscsData` and the row-theorem header are byte-identical, enforced by
`check_57_identity.py`) + the LEAF statements of units U1-U11 (all `sorry`, names prefixed `U<k>_`)
+ the assembly of `lem_gauss_two_discs` and of the three consumer bridges from the leaves.  When
every leaf is closed the row closes with no further glue.  Plan: PLAN_FINAL.md §3.3; report:
SKELETON_REPORT.md. -/

/-! # Row 57 lem:gauss-two-discs — statement draft A (architect A, fidelity first)

Written 2026-09-19 (D-AUTH-20260919 G-09: row 57 un-deferred).  Source:
reference/SM/sm-3-statesum.tex:428-436 (statement), 437-542 (proof).  Plan: PLAN_A.md (same
directory), which records the fidelity risks FR-TD-1..6 of PLDISCS_FEASIBILITY.md §2.5 and the new
ones FR-TD-7..12 with the reading chosen here.  Not a module of work/lean; every leaf is `sorry`.
Check: `cd work/lean && lake env lean ../drafts/twodiscs/Statements_A.lean`.

Printed statement, clause by clause (memo §2.1 numbering):
* 57a "A simple polygonal circle in the oriented sphere has exactly two complementary regions"
* 57b "and both closures are PL discs."
* 57c "Finite prescribed positive PL boundary maps between such discs extend to positive PL disc maps."
* 57d "A continuous positive boundary map also extends to a topological disc map."
* 57e "The statement includes the exterior region."

Readings fixed here (details in PLAN_A.md §2):
* circle = `Embedded P` (accepted, SM/EmbeddedRotation.lean), its image `polygonImage P = ⋃ edgeSegment`;
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

namespace SM

open Set OnePoint

variable {n : ℕ}

/-! ## §1 The circle and its two complementary regions in the sphere -/

/-- The polygonal circle `C` in the plane: the union of the edge segments (def:polygon vocabulary;
for `Embedded P` it is the simple closed curve `range (traversal P)`). -/
def polygonImage (P : LabelledTuple n) : Set Plane := ⋃ i, edgeSegment P i

/-- The oriented sphere (sm-3:430 "in the oriented sphere"): the one-point compactification of the
plane, oriented by the plane's `det`. -/
abbrev Sphere : Type := OnePoint Plane

/-- The circle as a subset of the sphere. -/
def sphereCircle (P : LabelledTuple n) : Set Sphere := ((↑) : Plane → Sphere) '' polygonImage P

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


/-! ## §L Leaves of the proof units (skeleton; every leaf is `sorry`)

Naming: `U<k>_<name>` for unit `U<k>` of PLAN_FINAL §3.3 (lanes: A = U1-U3, B = U4, C = U10/U11
convex models, then the sequential chain U5 → U6 → U7 → U9 → U8 → U10/U11).  Each docstring names
the printed step of sm-3:437-542 it renders. -/

/-! ### U1 (lane A) — convex/affine toolkit -/

/-- The triangle with vertices `f (T.v i)` for a positive affine `f` (its determinant clause is the
positivity field). -/
def Triangle.map (f : Plane → Plane) (T : Triangle) (h : IsPositiveAffineOn f T) : Triangle :=
  ⟨f ∘ T.v, h.2⟩

/-- `K'` refines `K`: every face of `K'` lies in a face of `K`. -/
def Triangulation.Refines {X : Set Plane} (K' K : Triangulation X) : Prop :=
  ∀ T' ∈ K'.faces, ∃ T ∈ K.faces, T'.carrier ⊆ T.carrier

/-- U1 (sm-3:440 "straight structure"): a triangle is compact. -/
theorem U1_triangle_isCompact (T : Triangle) : IsCompact T.carrier := by
  sorry

/-- U1: a triangle is convex. -/
theorem U1_triangle_convex (T : Triangle) : Convex ℝ T.carrier := by
  sorry

/-- U1: a nondegenerate triangle has nonempty interior. -/
theorem U1_triangle_interior_nonempty (T : Triangle) : (interior T.carrier).Nonempty := by
  sorry

/-- U1 (sm-3:431 "PL discs", model disc): a triangle is a `Link.IsDisc`. -/
theorem U1_triangle_isDisc (T : Triangle) : Link.IsDisc T.carrier := by
  sorry

/-- U1 (sm-3:439 "large rectangle"): the square `Q_L` is a `Link.IsDisc`. -/
theorem U1_square_isDisc {L : ℝ} (hL : 0 < L) : Link.IsDisc (square L) := by
  sorry

/-- U1: membership in a positively oriented triangle by the three `det` signs. -/
theorem U1_mem_carrier_iff_det (T : Triangle) (x : Plane) :
    x ∈ T.carrier ↔ 0 ≤ det (T.v 1 - T.v 0) (x - T.v 0) ∧ 0 ≤ det (T.v 2 - T.v 1) (x - T.v 1) ∧
      0 ≤ det (T.v 0 - T.v 2) (x - T.v 2) := by
  sorry

/-- U1: the frontier of a triangle is the union of its three edges. -/
theorem U1_frontier_triangle (T : Triangle) :
    frontier T.carrier = ⋃ i : Fin 3, segment ℝ (T.v i) (T.v (i + 1)) := by
  sorry

/-- U1 (sm-3:486-489 "regions"): the interior of a convex set with nonempty interior is connected. -/
theorem U1_interior_convex_isConnected {S : Set Plane} (hS : Convex ℝ S)
    (hne : (interior S).Nonempty) : IsConnected (interior S) := by
  sorry

/-- U1 (sm-3:486-489, the exterior): the complement of a compact convex set in the plane is
connected. -/
theorem U1_compl_compact_convex_isConnected {S : Set Plane} (hS : Convex ℝ S) (hc : IsCompact S) :
    IsConnected Sᶜ := by
  sorry

/-- U1: `AffineOn` is stable under composition. -/
theorem U1_affineOn_comp {f g : Plane → Plane} {S S' : Set Plane} (hf : AffineOn f S)
    (hg : AffineOn g S') (h : f '' S ⊆ S') : AffineOn (g ∘ f) S := by
  sorry

/-- U1: `AffineOn` restricts to subsets. -/
theorem U1_affineOn_mono {f : Plane → Plane} {S S' : Set Plane} (hf : AffineOn f S) (h : S' ⊆ S) :
    AffineOn f S' := by
  sorry

/-- U1: an affine map on a triangle with positive determinant is positive on every sub-triangle. -/
theorem U1_isPositiveAffineOn_mono {f : Plane → Plane} {T T' : Triangle}
    (hf : IsPositiveAffineOn f T) (h : T'.carrier ⊆ T.carrier) : IsPositiveAffineOn f T' := by
  sorry

/-- U1 (sm-3:535-537, positivity multiplicative): composition of positive affine maps is positive. -/
theorem U1_isPositiveAffineOn_comp {f g : Plane → Plane} {T : Triangle}
    (hf : IsPositiveAffineOn f T) (hg : IsPositiveAffineOn g (T.map f hf)) :
    IsPositiveAffineOn (g ∘ f) T := by
  sorry

/-- U1: the affine map of the plane sending the vertices of `T` to three prescribed points. -/
theorem U1_exists_affine_of_triangle (T : Triangle) (w : Fin 3 → Plane) :
    ∃ f : Plane → Plane, AffineOn f univ ∧ ∀ i, f (T.v i) = w i := by
  sorry

/-- U1: the affine map of `U1_exists_affine_of_triangle` is positive on `T` iff the image triple is
positively oriented. -/
theorem U1_isPositiveAffineOn_of_det {f : Plane → Plane} (T : Triangle) (hf : AffineOn f univ)
    (hpos : 0 < det (f (T.v 1) - f (T.v 0)) (f (T.v 2) - f (T.v 0))) : IsPositiveAffineOn f T := by
  sorry

/-- U1 (pasting lemma): a map continuous on each of finitely many closed sets is continuous on
their union. -/
theorem U1_continuousOn_iUnion_of_finite {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {ι : Type*} [Finite ι] {C : ι → Set α} {f : α → β} (hC : ∀ i, IsClosed (C i))
    (hf : ∀ i, ContinuousOn f (C i)) : ContinuousOn f (⋃ i, C i) := by
  sorry

/-- U1: `IsHomeoOnto` composes. -/
theorem U1_isHomeoOnto_comp {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] {S : Set α} {S' : Set β} {S'' : Set γ} {f : α → β} {g : β → γ}
    (hf : IsHomeoOnto S S' f) (hg : IsHomeoOnto S' S'' g) : IsHomeoOnto S S'' (g ∘ f) := by
  sorry

/-- U1: `IsHomeoOnto` inverts (any left inverse on `S` is a homeomorphism `S' → S`). -/
theorem U1_isHomeoOnto_inv {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} {g : β → α} (hf : IsHomeoOnto S S' f)
    (hg : ∀ x ∈ S, g (f x) = x) : IsHomeoOnto S' S g := by
  sorry

/-- U1: `IsHomeoOnto` restricts to a subset and its image. -/
theorem U1_isHomeoOnto_restrict {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} (hf : IsHomeoOnto S S' f) {A : Set α} (hA : A ⊆ S) :
    IsHomeoOnto A (f '' A) f := by
  sorry

/-- U1: a plane homeomorphism is `IsHomeoOnto` any set onto its image. -/
theorem U1_isHomeoOnto_of_homeomorph (H : Plane ≃ₜ Plane) (A : Set Plane) :
    IsHomeoOnto A (H '' A) H := by
  sorry

/-- U1: a set is `IsHomeoOnto` its coercion image in the sphere. -/
theorem U1_isHomeoOnto_coe (A : Set Plane) :
    IsHomeoOnto A (((↑) : Plane → Sphere) '' A) ((↑) : Plane → Sphere) := by
  sorry

/-! ### U2 (lane A) — triangulation basics -/

/-- U2: the edge `i` of `T` (from `T.v i` to `T.v (i+1)`). -/
def Triangle.edgeSeg (T : Triangle) (i : Fin 3) : Set Plane := segment ℝ (T.v i) (T.v (i + 1))

/-- U2: the set `X` of a triangulation is compact. -/
theorem U2_isCompact_of_triangulation {X : Set Plane} (K : Triangulation X) : IsCompact X := by
  sorry

/-- U2 (sm-3:440-443, the empty part of a chart): the empty set has a triangulation. -/
theorem U2_triangulation_empty : Nonempty (Triangulation (∅ : Set Plane)) := by
  sorry

/-- U2: a triangle is triangulated by itself. -/
theorem U2_triangulation_triangle (T : Triangle) : Nonempty (Triangulation T.carrier) := by
  sorry

/-- U2 (sm-3:440 "triangulate the rectangle"): the square `Q_L` has a triangulation. -/
theorem U2_triangulation_square {L : ℝ} (hL : 0 < L) : Nonempty (Triangulation (square L)) := by
  sorry

/-- U2: a refinement carries positive PL maps (positivity is inherited by sub-triangles). -/
theorem U2_isPositivePLOn_of_refines {X : Set Plane} {K K' : Triangulation X} {f : Plane → Plane}
    (hf : IsPositivePLOn f K) (h : K'.Refines K) : IsPositivePLOn f K' := by
  sorry

/-- U2 (fan refinement): a face may be replaced by its fan from an interior point. -/
theorem U2_refine_fan {X : Set Plane} (K : Triangulation X) {T : Triangle} (hT : T ∈ K.faces)
    {o : Plane} (ho : o ∈ interior T.carrier) :
    ∃ K' : Triangulation X, K'.Refines K ∧
      (∀ T' ∈ K.faces, T'.carrier ≠ T.carrier → T' ∈ K'.faces) ∧
      (∀ i : Fin 3, ∃ T' ∈ K'.faces, T'.carrier = convexHull ℝ {o, T.v i, T.v (i + 1)}) := by
  sorry

/-- U2 (edge split): an edge lying in exactly one face may be subdivided at an interior point. -/
theorem U2_refine_edge_split {X : Set Plane} (K : Triangulation X) {T : Triangle} (hT : T ∈ K.faces)
    (i : Fin 3) (huniq : ∀ T' ∈ K.faces, T.edgeSeg i ⊆ T'.carrier → T'.carrier = T.carrier)
    {p : Plane} (hp : p ∈ openSegment ℝ (T.v i) (T.v (i + 1))) :
    ∃ K' : Triangulation X, K'.Refines K ∧
      (∀ T' ∈ K.faces, T'.carrier ≠ T.carrier → T' ∈ K'.faces) ∧
      (∃ T₁ ∈ K'.faces, T₁.carrier = convexHull ℝ {T.v i, p, T.v (i + 2)}) ∧
      (∃ T₂ ∈ K'.faces, T₂.carrier = convexHull ℝ {p, T.v (i + 1), T.v (i + 2)}) := by
  sorry

/-- U2 (positive distance): the faces not containing `x` stay at positive distance from `x`. -/
theorem U2_exists_ball_disjoint_faces {X : Set Plane} (K : Triangulation X) (x : Plane) :
    ∃ ε > 0, ∀ T ∈ K.faces, x ∉ T.carrier → Disjoint (Metric.ball x ε) T.carrier := by
  sorry

/-- U2 (local structure): near `x ∈ X` the set `X` is the union of the faces containing `x`. -/
theorem U2_local_structure {X : Set Plane} (K : Triangulation X) {x : Plane} (hx : x ∈ X) :
    ∃ ε > 0, Metric.ball x ε ∩ X = Metric.ball x ε ∩ ⋃ T ∈ {T ∈ K.faces | x ∈ T.carrier}, T.carrier := by
  sorry

/-- U2 (sm-3:490-491 "single boundary"): an edge lying in exactly one face is in the frontier. -/
theorem U2_edgeSeg_subset_frontier {X : Set Plane} (K : Triangulation X) {T : Triangle}
    (hT : T ∈ K.faces) (i : Fin 3)
    (huniq : ∀ T' ∈ K.faces, T.edgeSeg i ⊆ T'.carrier → T'.carrier = T.carrier) :
    T.edgeSeg i ⊆ frontier X := by
  sorry

/-- U2: the open faces lie in the interior of `X`. -/
theorem U2_interior_face_subset_interior {X : Set Plane} (K : Triangulation X) {T : Triangle}
    (hT : T ∈ K.faces) : interior T.carrier ⊆ interior X := by
  sorry

/-- U2: an open edge shared by two distinct faces lies in the interior of `X`. -/
theorem U2_openSegment_subset_interior_of_two_faces {X : Set Plane} (K : Triangulation X)
    {T T' : Triangle} (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) (hne : T.carrier ≠ T'.carrier)
    (i : Fin 3) (h : T.edgeSeg i ⊆ T'.carrier) : openSegment ℝ (T.v i) (T.v (i + 1)) ⊆ interior X := by
  sorry

/-- U2: the frontier of `X` is the union of the edges lying in exactly one face. -/
theorem U2_frontier_eq_iUnion_boundary_edges {X : Set Plane} (K : Triangulation X) :
    frontier X = ⋃ T ∈ K.faces, ⋃ i : Fin 3,
      ⋃ (_ : ∀ T' ∈ K.faces, T.edgeSeg i ⊆ T'.carrier → T'.carrier = T.carrier), T.edgeSeg i := by
  sorry

/-- U2 (pushforward): the image triangulation under a positive PL homeomorphism of the plane. -/
theorem U2_pushforward {X : Set Plane} (K : Triangulation X) (H : Plane ≃ₜ Plane)
    (hH : IsPositivePLOn H K) :
    ∃ K' : Triangulation (H '' X), (∀ T ∈ K.faces, ∃ hT : IsPositiveAffineOn H T, T.map H hT ∈ K'.faces) ∧
      ∀ T' ∈ K'.faces, ∃ T ∈ K.faces, T'.carrier = H '' T.carrier := by
  sorry

/-- U2 (inverse): the inverse of a positive PL homeomorphism is positive PL on the pushforward. -/
theorem U2_inverse_isPositivePLOn {X : Set Plane} (K : Triangulation X) (H : Plane ≃ₜ Plane)
    (hH : IsPositivePLOn H K) :
    ∃ K' : Triangulation (H '' X), IsPositivePLOn H.symm K' := by
  sorry

/-- U2 (sm-3:520-523, the disc parametrisation is a homeomorphism): a face-wise positive affine map
that is injective on `X` is a homeomorphism of `X` onto its image (compactness). -/
theorem U2_isHomeoOnto_of_isPositivePLOn {X : Set Plane} (K : Triangulation X) {f : Plane → Plane}
    (hf : IsPositivePLOn f K) (hinj : InjOn f X) : IsHomeoOnto X (f '' X) f := by
  sorry

/-- U2: a positive PL map is continuous on `X`. -/
theorem U2_continuousOn_of_isPositivePLOn {X : Set Plane} (K : Triangulation X) {f : Plane → Plane}
    (hf : IsPositivePLOn f K) : ContinuousOn f X := by
  sorry

/-! ### U3 (lane A) — overlay / common refinement -/

/-- U3: `g : Plane → Sphere` is positive PL from the plane set `D` into the sphere with model `L'`:
`D` carries a triangulation each of whose faces is sent into one target chart image, where `g` read
in that chart is positive affine (the inverse-parametrisation side of `IsPositivePLSphereMap`). -/
def IsPositivePLFromPlane (L' : ℝ) (D : Set Plane) (g : Plane → Sphere) : Prop :=
  ∃ K : Triangulation D, ∀ T ∈ K.faces, ∃ b' : Bool,
    (∀ x ∈ T.carrier, g x ∈ modelChart L' b' '' modelDomain L' b') ∧
    IsPositiveAffineOn (modelChartInv L' b' ∘ g) T


/-! ### U3 helpers (u3h_): plane algebra and barycentric coordinates -/

theorem u3h_planeDot_add (p x y : Plane) : planeDot p (x + y) = planeDot p x + planeDot p y := by
  simp [planeDot]; ring

theorem u3h_planeDot_smul (p : Plane) (a : ℝ) (x : Plane) : planeDot p (a • x) = a * planeDot p x := by
  simp [planeDot]; ring

theorem u3h_planeDot_sub (p x y : Plane) : planeDot p (x - y) = planeDot p x - planeDot p y := by
  simp [planeDot]; ring

theorem u3h_planeDot_neg_left (p x : Plane) : planeDot (-p) x = -planeDot p x := by
  simp [planeDot]; ring

theorem u3h_planeDot_zero_left (x : Plane) : planeDot 0 x = 0 := by
  simp [planeDot]

theorem u3h_planeDot_combo (p x y : Plane) (a b : ℝ) :
    planeDot p (a • x + b • y) = a * planeDot p x + b * planeDot p y := by
  rw [u3h_planeDot_add, u3h_planeDot_smul, u3h_planeDot_smul]

theorem u3h_convex_le (p : Plane) (r : ℝ) : Convex ℝ {x : Plane | planeDot p x ≤ r} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq] at *
  rw [u3h_planeDot_combo]
  have h1 : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem u3h_convex_ge (p : Plane) (r : ℝ) : Convex ℝ {x : Plane | r ≤ planeDot p x} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq] at *
  rw [u3h_planeDot_combo]
  have h1 : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem u3h_convex_eq (p : Plane) (r : ℝ) : Convex ℝ {x : Plane | planeDot p x = r} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq] at *
  rw [u3h_planeDot_combo, hx, hy]; linear_combination r * hab

theorem u3h_range_v (T : Triangle) : range T.v = {T.v 0, T.v 1, T.v 2} := by
  ext y; constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

/-- Membership in a triangle by three weights. -/
theorem u3h_mem_carrier_iff (T : Triangle) (x : Plane) :
    x ∈ T.carrier ↔ ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧
      a • T.v 0 + b • T.v 1 + c • T.v 2 = x := by
  constructor
  · intro hx
    unfold Triangle.carrier at hx
    rw [u3h_range_v, convexHull_insert (by simp), convexHull_pair, mem_convexJoin] at hx
    obtain ⟨a₀, ha₀, y, hy, hxy⟩ := hx
    rw [mem_singleton_iff] at ha₀; subst ha₀
    obtain ⟨γ, δ, hγ, hδ, hγδ, rfl⟩ := hy
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hxy
    refine ⟨α, β * γ, β * δ, hα, mul_nonneg hβ hγ, mul_nonneg hβ hδ, ?_, ?_⟩
    · linear_combination hαβ + β * hγδ
    · simp only [smul_add, mul_smul]; abel
  · rintro ⟨a, b, c, ha, hb, hc, habc, rfl⟩
    refine mem_convexHull_of_exists_fintype (ι := Fin 3) ![a, b, c] T.v ?_ ?_ (fun i => ⟨i, rfl⟩) ?_
    · intro i; fin_cases i <;> simpa
    · simp [Fin.sum_univ_three]; linarith
    · simp [Fin.sum_univ_three]

/-- Barycentric coordinates are unique (nondegeneracy). -/
theorem u3h_bary_unique (T : Triangle) {a b c a' b' c' : ℝ}
    (h : a • T.v 0 + b • T.v 1 + c • T.v 2 = a' • T.v 0 + b' • T.v 1 + c' • T.v 2)
    (hs : a + b + c = a' + b' + c') : a = a' ∧ b = b' ∧ c = c' := by
  have hD := T.pos
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
  unfold det at hD
  simp only [Prod.fst_sub, Prod.snd_sub] at hD
  have E1 : (b - b') * ((T.v 1).1 - (T.v 0).1) + (c - c') * ((T.v 2).1 - (T.v 0).1) = 0 := by
    linear_combination h1 - (T.v 0).1 * hs
  have E2 : (b - b') * ((T.v 1).2 - (T.v 0).2) + (c - c') * ((T.v 2).2 - (T.v 0).2) = 0 := by
    linear_combination h2 - (T.v 0).2 * hs
  have hb : (b - b') * (((T.v 1).1 - (T.v 0).1) * ((T.v 2).2 - (T.v 0).2)
      - ((T.v 1).2 - (T.v 0).2) * ((T.v 2).1 - (T.v 0).1)) = 0 := by
    linear_combination ((T.v 2).2 - (T.v 0).2) * E1 - ((T.v 2).1 - (T.v 0).1) * E2
  have hc : (c - c') * (((T.v 1).1 - (T.v 0).1) * ((T.v 2).2 - (T.v 0).2)
      - ((T.v 1).2 - (T.v 0).2) * ((T.v 2).1 - (T.v 0).1)) = 0 := by
    linear_combination ((T.v 1).1 - (T.v 0).1) * E2 - ((T.v 1).2 - (T.v 0).2) * E1
  rcases mul_eq_zero.1 hb with hb | hb
  · rcases mul_eq_zero.1 hc with hc | hc
    · refine ⟨by linarith, by linarith, by linarith⟩
    · linarith
  · linarith

theorem u3h_pos_cyc (T : Triangle) (i : Fin 3) :
    0 < det (T.v (i + 1) - T.v i) (T.v (i + 2) - T.v i) := by
  have h := T.pos
  fin_cases i
  · simpa using h
  · have : det (T.v 2 - T.v 1) (T.v 0 - T.v 1) = det (T.v 1 - T.v 0) (T.v 2 - T.v 0) := by
      simp [det]; ring
    simpa [this] using h
  · have : det (T.v 0 - T.v 2) (T.v 1 - T.v 2) = det (T.v 1 - T.v 0) (T.v 2 - T.v 0) := by
      simp [det]; ring
    simpa [this] using h

theorem u3h_v01 (T : Triangle) : T.v 0 ≠ T.v 1 := by
  intro h
  have := u3h_bary_unique T (a := 1) (b := 0) (c := 0) (a' := 0) (b' := 1) (c' := 0)
    (by simp [h]) (by norm_num)
  norm_num at this

theorem u3h_v02 (T : Triangle) : T.v 0 ≠ T.v 2 := by
  intro h
  have := u3h_bary_unique T (a := 1) (b := 0) (c := 0) (a' := 0) (b' := 0) (c' := 1)
    (by simp [h]) (by norm_num)
  norm_num at this

theorem u3h_v12 (T : Triangle) : T.v 1 ≠ T.v 2 := by
  intro h
  have := u3h_bary_unique T (a := 0) (b := 1) (c := 0) (a' := 0) (b' := 0) (c' := 1)
    (by simp [h]) (by norm_num)
  norm_num at this

theorem u3h_v_injective (T : Triangle) : Function.Injective T.v := by
  have h01 := u3h_v01 T; have h02 := u3h_v02 T; have h12 := u3h_v12 T
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢
  all_goals first | exact (h01 h).elim | exact (h02 h).elim | exact (h12 h).elim | exact (h01 h.symm).elim | exact (h02 h.symm).elim | exact (h12 h.symm).elim

/-- A vertex different from `T.v i` is `T.v (i+1)` or `T.v (i+2)`. -/
theorem u3h_other (T : Triangle) (i j : Fin 3) (h : T.v j ≠ T.v i) :
    T.v j = T.v (i + 1) ∨ T.v j = T.v (i + 2) := by
  fin_cases i <;> fin_cases j <;> simp_all

/-- No vertex lies on the segment of the other two. -/
theorem u3h_v_not_mem_segment (T : Triangle) (i : Fin 3) :
    T.v i ∉ segment ℝ (T.v (i + 1)) (T.v (i + 2)) := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk] <;>
    rintro ⟨α, β, hα, hβ, hαβ, h⟩
  · have := u3h_bary_unique T (a := 0) (b := α) (c := β) (a' := 1) (b' := 0) (c' := 0)
      (by simpa using h) (by linarith)
    norm_num at this
  · have := u3h_bary_unique T (a := β) (b := 0) (c := α) (a' := 0) (b' := 1) (c' := 0)
      (by simpa [add_comm] using h) (by linarith)
    norm_num at this
  · have := u3h_bary_unique T (a := α) (b := β) (c := 0) (a' := 0) (b' := 0) (c' := 1)
      (by simpa using h) (by linarith)
    norm_num at this

/-- Two edges meet only in their common vertex. -/
theorem u3h_segment_inter (T : Triangle) (i : Fin 3) {x : Plane}
    (h1 : x ∈ segment ℝ (T.v i) (T.v (i + 1))) (h2 : x ∈ segment ℝ (T.v (i + 1)) (T.v (i + 2))) :
    x = T.v (i + 1) := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk] at h1 h2 ⊢ <;>
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := h1 <;> obtain ⟨γ, δ, hγ, hδ, hγδ, h⟩ := h2
  · have := u3h_bary_unique T (a := 0) (b := γ) (c := δ) (a' := α) (b' := β) (c' := 0)
      (by simpa using h) (by linarith)
    obtain ⟨rfl, rfl, rfl⟩ := this
    have hγ1 : γ = 1 := by linarith
    simp [hγ1]
  · have := u3h_bary_unique T (a := δ) (b := 0) (c := γ) (a' := 0) (b' := α) (c' := β)
      (by simpa [add_comm] using h) (by linarith)
    obtain ⟨rfl, rfl, rfl⟩ := this
    have hγ1 : γ = 1 := by linarith
    simp [hγ1]
  · have := u3h_bary_unique T (a := γ) (b := δ) (c := 0) (a' := β) (b' := 0) (c' := α)
      (by simpa [add_comm] using h) (by linarith)
    obtain ⟨rfl, rfl, rfl⟩ := this
    have hγ1 : γ = 1 := by linarith
    simp [hγ1]

/-- A vertex in the convex hull of a set of vertices is one of them. -/
theorem u3h_v_mem_convexHull (T : Triangle) {S : Set Plane} (hS : S ⊆ range T.v) (i : Fin 3)
    (h : T.v i ∈ convexHull ℝ S) : T.v i ∈ S := by
  by_contra hn
  have hsub : S ⊆ {T.v (i + 1), T.v (i + 2)} := by
    intro y hy
    obtain ⟨j, rfl⟩ := hS hy
    have hne : T.v j ≠ T.v i := fun e => hn (e ▸ hy)
    rcases u3h_other T i j hne with e | e <;> simp [e]
  have := convexHull_mono hsub h
  rw [convexHull_pair] at this
  exact u3h_v_not_mem_segment T i this

/-- The three vertices are not all on one line (for a genuine line). -/
theorem u3h_not_all_on_line (T : Triangle) {p : Plane} {r : ℝ} (hp : p ≠ 0)
    (h : ∀ i, planeDot p (T.v i) = r) : False := by
  have hD := T.pos
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  unfold det at hD; unfold planeDot at h0 h1 h2
  simp only [Prod.fst_sub, Prod.snd_sub] at hD
  have e1 : p.1 * (((T.v 1).1 - (T.v 0).1) * ((T.v 2).2 - (T.v 0).2)
      - ((T.v 1).2 - (T.v 0).2) * ((T.v 2).1 - (T.v 0).1)) = 0 := by
    linear_combination ((T.v 2).2 - (T.v 0).2) * (h1 - h0) - ((T.v 1).2 - (T.v 0).2) * (h2 - h0)
  have e2 : p.2 * (((T.v 1).1 - (T.v 0).1) * ((T.v 2).2 - (T.v 0).2)
      - ((T.v 1).2 - (T.v 0).2) * ((T.v 2).1 - (T.v 0).1)) = 0 := by
    linear_combination ((T.v 1).1 - (T.v 0).1) * (h2 - h0) - ((T.v 2).1 - (T.v 0).1) * (h1 - h0)
  rcases mul_eq_zero.1 e1 with e1 | e1
  · rcases mul_eq_zero.1 e2 with e2 | e2
    · exact hp (Prod.ext e1 e2)
    · linarith
  · linarith

theorem u3h_carrier_subset_le (T : Triangle) {p : Plane} {r : ℝ}
    (h : ∀ i, planeDot p (T.v i) ≤ r) : T.carrier ⊆ {x | planeDot p x ≤ r} :=
  convexHull_min (by rintro _ ⟨i, rfl⟩; exact h i) (u3h_convex_le p r)

theorem u3h_carrier_subset_ge (T : Triangle) {p : Plane} {r : ℝ}
    (h : ∀ i, r ≤ planeDot p (T.v i)) : T.carrier ⊆ {x | r ≤ planeDot p x} :=
  convexHull_min (by rintro _ ⟨i, rfl⟩; exact h i) (u3h_convex_ge p r)

/-- The face of a triangle on a supporting line is the hull of the vertices on the line. -/
theorem u3h_carrier_inter_line (T : Triangle) {p : Plane} {r : ℝ}
    (h : ∀ i, planeDot p (T.v i) ≤ r) :
    T.carrier ∩ {x | planeDot p x = r} = convexHull ℝ (range T.v ∩ {x | planeDot p x = r}) := by
  apply Subset.antisymm
  · rintro x ⟨hx, hxr⟩
    simp only [mem_ofPred_eq] at hxr
    obtain ⟨a, b, c, ha, hb, hc, habc, rfl⟩ := (u3h_mem_carrier_iff T x).1 hx
    have hsum : a * (r - planeDot p (T.v 0)) + b * (r - planeDot p (T.v 1))
        + c * (r - planeDot p (T.v 2)) = 0 := by
      rw [u3h_planeDot_add, u3h_planeDot_combo, u3h_planeDot_smul] at hxr
      linear_combination r * habc - hxr
    have t0 : 0 ≤ a * (r - planeDot p (T.v 0)) := mul_nonneg ha (by linarith [h 0])
    have t1 : 0 ≤ b * (r - planeDot p (T.v 1)) := mul_nonneg hb (by linarith [h 1])
    have t2 : 0 ≤ c * (r - planeDot p (T.v 2)) := mul_nonneg hc (by linarith [h 2])
    have z0 : a = 0 ∨ planeDot p (T.v 0) = r := by
      rcases mul_eq_zero.1 (show a * (r - planeDot p (T.v 0)) = 0 by linarith) with e | e
      · exact Or.inl e
      · exact Or.inr (by linarith)
    have z1 : b = 0 ∨ planeDot p (T.v 1) = r := by
      rcases mul_eq_zero.1 (show b * (r - planeDot p (T.v 1)) = 0 by linarith) with e | e
      · exact Or.inl e
      · exact Or.inr (by linarith)
    have z2 : c = 0 ∨ planeDot p (T.v 2) = r := by
      rcases mul_eq_zero.1 (show c * (r - planeDot p (T.v 2)) = 0 by linarith) with e | e
      · exact Or.inl e
      · exact Or.inr (by linarith)
    -- some vertex is on the line
    have hex : ∃ i₀, planeDot p (T.v i₀) = r := by
      by_contra hno
      push Not at hno
      have a0 : a = 0 := z0.resolve_right (hno 0)
      have b0 : b = 0 := z1.resolve_right (hno 1)
      have c0 : c = 0 := z2.resolve_right (hno 2)
      linarith
    obtain ⟨i₀, hi₀⟩ := hex
    classical
    let z : Fin 3 → Plane := fun i => if planeDot p (T.v i) = r then T.v i else T.v i₀
    have hz : ∀ i, z i ∈ range T.v ∩ {x | planeDot p x = r} := by
      intro i
      simp only [z]
      split_ifs with hi
      · exact ⟨⟨i, rfl⟩, hi⟩
      · exact ⟨⟨i₀, rfl⟩, hi₀⟩
    have hw : ∀ i, (![a, b, c] : Fin 3 → ℝ) i • z i = (![a, b, c] : Fin 3 → ℝ) i • T.v i := by
      intro i
      simp only [z]
      split_ifs with hi
      · rfl
      · fin_cases i
        · simp [z0.resolve_right hi]
        · simp [z1.resolve_right hi]
        · simp [z2.resolve_right hi]
    refine mem_convexHull_of_exists_fintype (ι := Fin 3) ![a, b, c] z ?_ ?_ hz ?_
    · intro i; fin_cases i <;> simpa
    · simp [Fin.sum_univ_three]; linarith
    · simp only [Fin.sum_univ_three, hw]; simp
  · apply convexHull_min
    · rintro x ⟨hx, hxr⟩
      exact ⟨subset_convexHull ℝ _ hx, hxr⟩
    · exact (convex_convexHull ℝ _).inter (u3h_convex_eq p r)

theorem u3h_line_neg (p : Plane) (r : ℝ) :
    {x : Plane | planeDot (-p) x = -r} = {x | planeDot p x = r} := by
  ext x; simp only [mem_ofPred_eq, u3h_planeDot_neg_left]; constructor <;> intro h <;> linarith

theorem u3h_carrier_inter_line' (T : Triangle) {p : Plane} {r : ℝ}
    (h : ∀ i, r ≤ planeDot p (T.v i)) :
    T.carrier ∩ {x | planeDot p x = r} = convexHull ℝ (range T.v ∩ {x | planeDot p x = r}) := by
  rw [← u3h_line_neg p r]
  exact u3h_carrier_inter_line T (p := -p) (r := -r) (fun i => by
    rw [u3h_planeDot_neg_left]; linarith [h i])

/-! ### U3 helpers: separation of faces -/

theorem u3h_dual_eq (f : StrongDual ℝ Plane) (x : Plane) :
    f x = planeDot (f ((1 : ℝ), (0 : ℝ)), f ((0 : ℝ), (1 : ℝ))) x := by
  have hx : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add, map_smul, map_smul]
  simp [planeDot, mul_comm]

/-- Hahn–Banach for a compact convex body and a convex set missing its interior. -/
theorem u3h_separate_of_disjoint {A B : Set Plane} (hA : Convex ℝ A) (hAc : IsCompact A)
    (hAi : (interior A).Nonempty) (hB : Convex ℝ B) (hBne : B.Nonempty)
    (hdisj : Disjoint (interior A) B) :
    ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧ (∀ x ∈ A, planeDot p x ≤ r) ∧ ∀ x ∈ B, r ≤ planeDot p x := by
  obtain ⟨f, u, hf1, hf2⟩ := geometric_hahn_banach_open hA.interior isOpen_interior hB hdisj
  refine ⟨(f ((1 : ℝ), (0 : ℝ)), f ((0 : ℝ), (1 : ℝ))), u, ?_, ?_, ?_⟩
  · intro hp
    obtain ⟨a, ha⟩ := hAi
    obtain ⟨b, hb⟩ := hBne
    have h1 := hf1 a ha
    have h2 := hf2 b hb
    rw [u3h_dual_eq, hp, u3h_planeDot_zero_left] at h1 h2
    linarith
  · intro x hx
    rw [← u3h_dual_eq]
    have hcl : closure (interior A) = A := by
      rw [hA.closure_interior_eq_closure_of_nonempty_interior hAi, hAc.isClosed.closure_eq]
    have hx' : x ∈ closure (interior A) := by rw [hcl]; exact hx
    exact closure_minimal (fun y hy => (hf1 y hy).le) (isClosed_le f.continuous continuous_const) hx'
  · intro x hx
    rw [← u3h_dual_eq]
    exact hf2 x hx

/-- If a vertex of `T` is not a vertex of `T'`, the interior of `T` misses `T'`. -/
theorem u3h_interior_disjoint_of_vertex {X : Set Plane} (K : Triangulation X) {T T' : Triangle}
    (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) (i : Fin 3) (hi : T.v i ∉ range T'.v) :
    Disjoint (interior T.carrier) T'.carrier := by
  have hinter := K.inter T hT T' hT'
  have hsub : range T.v ∩ range T'.v ⊆ {T.v (i + 1), T.v (i + 2)} := by
    rintro y ⟨⟨j, rfl⟩, hy'⟩
    have hne : T.v j ≠ T.v i := fun e => hi (e ▸ hy')
    rcases u3h_other T i j hne with e | e <;> simp [e]
  have hfr : T.carrier ∩ T'.carrier ⊆ frontier T.carrier := by
    rw [hinter, U1_frontier_triangle]
    intro y hy
    have := convexHull_mono hsub hy
    rw [convexHull_pair] at this
    refine mem_iUnion.2 ⟨i + 1, ?_⟩
    have e : i + 1 + 1 = i + 2 := by fin_cases i <;> rfl
    rw [e]; exact this
  rw [Set.disjoint_left]
  intro y hy hy'
  have hyT : y ∈ T.carrier := interior_subset hy
  exact (Set.disjoint_left.1 disjoint_interior_frontier) hy (hfr ⟨hyT, hy'⟩)

/-- Two faces of a triangulation with distinct carriers are separated by a line. -/
theorem u3h_faces_separated {X : Set Plane} (K : Triangulation X) {T T' : Triangle}
    (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) (hne : T.carrier ≠ T'.carrier) :
    ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧ (∀ i, planeDot p (T.v i) ≤ r) ∧ ∀ i, r ≤ planeDot p (T'.v i) := by
  have key : ∀ (S S' : Triangle), S ∈ K.faces → S' ∈ K.faces → (∃ i, S.v i ∉ range S'.v) →
      ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧ (∀ i, planeDot p (S.v i) ≤ r) ∧ ∀ i, r ≤ planeDot p (S'.v i) := by
    intro S S' hS hS' ⟨i, hi⟩
    obtain ⟨p, r, hp, h1, h2⟩ := u3h_separate_of_disjoint (U1_triangle_convex S)
      (U1_triangle_isCompact S) (U1_triangle_interior_nonempty S) (U1_triangle_convex S')
      ⟨S'.v 0, subset_convexHull ℝ _ ⟨0, rfl⟩⟩ (u3h_interior_disjoint_of_vertex K hS hS' i hi)
    exact ⟨p, r, hp, fun j => h1 _ (subset_convexHull ℝ _ ⟨j, rfl⟩),
      fun j => h2 _ (subset_convexHull ℝ _ ⟨j, rfl⟩)⟩
  by_cases h : ∃ i, T.v i ∉ range T'.v
  · exact key T T' hT hT' h
  · push Not at h
    have h' : ∃ i, T'.v i ∉ range T.v := by
      by_contra h'
      push Not at h'
      apply hne
      have : range T.v = range T'.v := by
        apply Subset.antisymm
        · rintro _ ⟨i, rfl⟩; exact h i
        · rintro _ ⟨i, rfl⟩; exact h' i
      unfold Triangle.carrier; rw [this]
    obtain ⟨p, r, hp, h1, h2⟩ := key T' T hT' hT h'
    refine ⟨-p, -r, neg_ne_zero.2 hp, fun i => ?_, fun i => ?_⟩
    · rw [u3h_planeDot_neg_left]; linarith [h2 i]
    · rw [u3h_planeDot_neg_left]; linarith [h1 i]

/-- Separated triangles meet inside their faces on the separating line. -/
theorem u3h_inter_of_separated (Δ Δ' : Triangle) {p : Plane} {r : ℝ}
    (h : ∀ i, planeDot p (Δ.v i) ≤ r) (h' : ∀ i, r ≤ planeDot p (Δ'.v i)) :
    Δ.carrier ∩ Δ'.carrier = convexHull ℝ (range Δ.v ∩ {x | planeDot p x = r}) ∩
      convexHull ℝ (range Δ'.v ∩ {x | planeDot p x = r}) := by
  rw [← u3h_carrier_inter_line Δ h, ← u3h_carrier_inter_line' Δ' h']
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hx'⟩
    have h1 := u3h_carrier_subset_le Δ h hx
    have h2 := u3h_carrier_subset_ge Δ' h' hx'
    simp only [mem_ofPred_eq] at h1 h2
    exact ⟨⟨hx, le_antisymm h1 h2⟩, hx', le_antisymm h1 h2⟩
  · rintro ⟨⟨hx, _⟩, hx', _⟩
    exact ⟨hx, hx'⟩

/-- The vertices of a triangle on a genuine line: none, or a pair (possibly repeated). -/
theorem u3h_vertices_on_line (Δ : Triangle) {p : Plane} {r : ℝ} (hp : p ≠ 0) :
    range Δ.v ∩ {x | planeDot p x = r} = ∅ ∨
      ∃ a b : Plane, a ∈ range Δ.v ∧ b ∈ range Δ.v ∧ planeDot p a = r ∧ planeDot p b = r ∧
        range Δ.v ∩ {x | planeDot p x = r} = {a, b} := by
  have hnot : ¬ (planeDot p (Δ.v 0) = r ∧ planeDot p (Δ.v 1) = r ∧ planeDot p (Δ.v 2) = r) := by
    rintro ⟨h0, h1, h2⟩
    exact u3h_not_all_on_line Δ hp (fun i => by fin_cases i <;> assumption)
  by_cases h0 : planeDot p (Δ.v 0) = r <;> by_cases h1 : planeDot p (Δ.v 1) = r <;>
    by_cases h2 : planeDot p (Δ.v 2) = r
  · exact absurd ⟨h0, h1, h2⟩ hnot
  · refine Or.inr ⟨Δ.v 0, Δ.v 1, ⟨0, rfl⟩, ⟨1, rfl⟩, h0, h1, ?_⟩
    ext x; simp only [u3h_range_v, mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨(rfl | rfl | rfl), hx⟩ <;> simp_all
    · rintro (rfl | rfl) <;> simp_all
  · refine Or.inr ⟨Δ.v 0, Δ.v 2, ⟨0, rfl⟩, ⟨2, rfl⟩, h0, h2, ?_⟩
    ext x; simp only [u3h_range_v, mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨(rfl | rfl | rfl), hx⟩ <;> simp_all
    · rintro (rfl | rfl) <;> simp_all
  · refine Or.inr ⟨Δ.v 0, Δ.v 0, ⟨0, rfl⟩, ⟨0, rfl⟩, h0, h0, ?_⟩
    ext x; simp only [u3h_range_v, mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨(rfl | rfl | rfl), hx⟩ <;> simp_all
    · rintro (rfl | rfl) <;> simp_all
  · refine Or.inr ⟨Δ.v 1, Δ.v 2, ⟨1, rfl⟩, ⟨2, rfl⟩, h1, h2, ?_⟩
    ext x; simp only [u3h_range_v, mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨(rfl | rfl | rfl), hx⟩ <;> simp_all
    · rintro (rfl | rfl) <;> simp_all
  · refine Or.inr ⟨Δ.v 1, Δ.v 1, ⟨1, rfl⟩, ⟨1, rfl⟩, h1, h1, ?_⟩
    ext x; simp only [u3h_range_v, mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨(rfl | rfl | rfl), hx⟩ <;> simp_all
    · rintro (rfl | rfl) <;> simp_all
  · refine Or.inr ⟨Δ.v 2, Δ.v 2, ⟨2, rfl⟩, ⟨2, rfl⟩, h2, h2, ?_⟩
    ext x; simp only [u3h_range_v, mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨(rfl | rfl | rfl), hx⟩ <;> simp_all
    · rintro (rfl | rfl) <;> simp_all
  · left
    ext x; simp only [u3h_range_v, mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq,
      mem_empty_iff_false, iff_false, not_and]
    rintro (rfl | rfl | rfl) <;> assumption

/-! ### U3 helpers: coordinates on a line and segment combinatorics -/

/-- A direction vector of the lines `planeDot p x = r`. -/
def u3h_dir (p : Plane) : Plane := (-p.2, p.1)

theorem u3h_planeDot_dir_self (p : Plane) :
    planeDot (u3h_dir p) (u3h_dir p) = p.1 ^ 2 + p.2 ^ 2 := by
  simp [u3h_dir, planeDot]; ring

theorem u3h_dir_pos {p : Plane} (hp : p ≠ 0) : 0 < planeDot (u3h_dir p) (u3h_dir p) := by
  rw [u3h_planeDot_dir_self]
  have : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
    by_contra h; push Not at h; exact hp (Prod.ext h.1 h.2)
  rcases this with h | h
  · have := mul_self_pos.2 h; nlinarith [sq_nonneg p.2]
  · have := mul_self_pos.2 h; nlinarith [sq_nonneg p.1]

/-- Two points of a line differ by a multiple of the direction. -/
theorem u3h_on_line_eq {p : Plane} (hp : p ≠ 0) {r : ℝ} {x y : Plane} (hx : planeDot p x = r)
    (hy : planeDot p y = r) :
    x = y + (planeDot (u3h_dir p) (x - y) / planeDot (u3h_dir p) (u3h_dir p)) • u3h_dir p := by
  have hN := u3h_dir_pos hp
  have hw : p.1 * (x.1 - y.1) + p.2 * (x.2 - y.2) = 0 := by
    unfold planeDot at hx hy; linarith
  have key : x - y = (planeDot (u3h_dir p) (x - y) / planeDot (u3h_dir p) (u3h_dir p)) • u3h_dir p := by
    rw [u3h_planeDot_dir_self] at hN ⊢
    ext
    · simp only [Prod.smul_fst, smul_eq_mul, u3h_dir, planeDot, Prod.fst_sub, Prod.snd_sub]
      rw [div_mul_eq_mul_div, eq_div_iff hN.ne']
      linear_combination p.1 * hw
    · simp only [Prod.smul_snd, smul_eq_mul, u3h_dir, planeDot, Prod.fst_sub, Prod.snd_sub]
      rw [div_mul_eq_mul_div, eq_div_iff hN.ne']
      linear_combination p.2 * hw
  rw [← key]; abel

theorem u3h_coord_injOn {p : Plane} (hp : p ≠ 0) {r : ℝ} {x y : Plane} (hx : planeDot p x = r)
    (hy : planeDot p y = r) (h : planeDot (u3h_dir p) x = planeDot (u3h_dir p) y) : x = y := by
  have := u3h_on_line_eq hp hx hy
  rw [u3h_planeDot_sub, h, sub_self, zero_div, zero_smul, add_zero] at this
  exact this

theorem u3h_mem_segment_iff_coord {p : Plane} (hp : p ≠ 0) {r : ℝ} {a b x : Plane}
    (ha : planeDot p a = r) (hb : planeDot p b = r) (hx : planeDot p x = r) :
    x ∈ segment ℝ a b ↔
      planeDot (u3h_dir p) x ∈ segment ℝ (planeDot (u3h_dir p) a) (planeDot (u3h_dir p) b) := by
  constructor
  · rintro ⟨α, β, hα, hβ, hαβ, rfl⟩
    exact ⟨α, β, hα, hβ, hαβ, by rw [u3h_planeDot_combo, smul_eq_mul, smul_eq_mul]⟩
  · rintro ⟨α, β, hα, hβ, hαβ, h⟩
    have hy : planeDot p (α • a + β • b) = r := by
      rw [u3h_planeDot_combo, ha, hb]; linear_combination r * hαβ
    have : α • a + β • b = x :=
      u3h_coord_injOn hp hy hx (by rw [u3h_planeDot_combo]; exact h)
    exact ⟨α, β, hα, hβ, hαβ, this⟩

theorem u3h_real_comb_ordered {a1 a2 b1 b2 ξ : ℝ} (_ha : a1 ≤ a2) (_hb : b1 ≤ b2)
    (hξa : ξ ∈ Icc a1 a2) (hξb : ξ ∈ Icc b1 b2)
    (hA : ∀ y, (y = b1 ∨ y = b2) → y ∈ Icc a1 a2 → (y = a1 ∨ y = a2))
    (hB : ∀ y, (y = a1 ∨ y = a2) → y ∈ Icc b1 b2 → (y = b1 ∨ y = b2)) :
    ∃ u v : ℝ, ((u = a1 ∨ u = a2) ∧ (u = b1 ∨ u = b2)) ∧ ((v = a1 ∨ v = a2) ∧ (v = b1 ∨ v = b2)) ∧
      u ≤ ξ ∧ ξ ≤ v := by
  obtain ⟨h1, h2⟩ := hξa; obtain ⟨h3, h4⟩ := hξb
  rcases le_total a1 b1 with hab | hab <;> rcases le_total a2 b2 with hcd | hcd
  · exact ⟨b1, a2, ⟨hA b1 (Or.inl rfl) ⟨hab, by linarith⟩, Or.inl rfl⟩,
      ⟨Or.inr rfl, hB a2 (Or.inr rfl) ⟨by linarith, hcd⟩⟩, h3, h2⟩
  · exact ⟨b1, b2, ⟨hA b1 (Or.inl rfl) ⟨hab, by linarith⟩, Or.inl rfl⟩,
      ⟨hA b2 (Or.inr rfl) ⟨by linarith, hcd⟩, Or.inr rfl⟩, h3, h4⟩
  · exact ⟨a1, a2, ⟨Or.inl rfl, hB a1 (Or.inl rfl) ⟨hab, by linarith⟩⟩,
      ⟨Or.inr rfl, hB a2 (Or.inr rfl) ⟨by linarith, hcd⟩⟩, h1, h2⟩
  · exact ⟨a1, b2, ⟨Or.inl rfl, hB a1 (Or.inl rfl) ⟨hab, by linarith⟩⟩,
      ⟨hA b2 (Or.inr rfl) ⟨by linarith, hcd⟩, Or.inr rfl⟩, h1, h4⟩

theorem u3h_real_comb {a1 a2 b1 b2 ξ : ℝ} (hξa : ξ ∈ segment ℝ a1 a2) (hξb : ξ ∈ segment ℝ b1 b2)
    (hA : ∀ y, (y = b1 ∨ y = b2) → y ∈ segment ℝ a1 a2 → (y = a1 ∨ y = a2))
    (hB : ∀ y, (y = a1 ∨ y = a2) → y ∈ segment ℝ b1 b2 → (y = b1 ∨ y = b2)) :
    ∃ u v : ℝ, ((u = a1 ∨ u = a2) ∧ (u = b1 ∨ u = b2)) ∧ ((v = a1 ∨ v = a2) ∧ (v = b1 ∨ v = b2)) ∧
      ξ ∈ segment ℝ u v := by
  rcases le_total a1 a2 with h12 | h12 <;> rcases le_total b1 b2 with h34 | h34
  · have ea : segment ℝ a1 a2 = Icc a1 a2 := segment_eq_Icc h12
    have eb : segment ℝ b1 b2 = Icc b1 b2 := segment_eq_Icc h34
    rw [ea] at hξa hA; rw [eb] at hξb hB
    obtain ⟨u, v, hu, hv, huξ, hξv⟩ := u3h_real_comb_ordered h12 h34 hξa hξb hA hB
    exact ⟨u, v, hu, hv, by rw [segment_eq_Icc (huξ.trans hξv)]; exact ⟨huξ, hξv⟩⟩
  · have ea : segment ℝ a1 a2 = Icc a1 a2 := segment_eq_Icc h12
    have eb : segment ℝ b1 b2 = Icc b2 b1 := by rw [segment_symm]; exact segment_eq_Icc h34
    rw [ea] at hξa hA; rw [eb] at hξb hB
    obtain ⟨u, v, hu, hv, huξ, hξv⟩ := u3h_real_comb_ordered h12 h34 hξa hξb
      (fun y hy => hA y hy.symm) (fun y hy hyI => (hB y hy hyI).symm)
    exact ⟨u, v, ⟨hu.1, hu.2.symm⟩, ⟨hv.1, hv.2.symm⟩,
      by rw [segment_eq_Icc (huξ.trans hξv)]; exact ⟨huξ, hξv⟩⟩
  · have ea : segment ℝ a1 a2 = Icc a2 a1 := by rw [segment_symm]; exact segment_eq_Icc h12
    have eb : segment ℝ b1 b2 = Icc b1 b2 := segment_eq_Icc h34
    rw [ea] at hξa hA; rw [eb] at hξb hB
    obtain ⟨u, v, hu, hv, huξ, hξv⟩ := u3h_real_comb_ordered h12 h34 hξa hξb
      (fun y hy hyI => (hA y hy hyI).symm) (fun y hy => hB y hy.symm)
    exact ⟨u, v, ⟨hu.1.symm, hu.2⟩, ⟨hv.1.symm, hv.2⟩,
      by rw [segment_eq_Icc (huξ.trans hξv)]; exact ⟨huξ, hξv⟩⟩
  · have ea : segment ℝ a1 a2 = Icc a2 a1 := by rw [segment_symm]; exact segment_eq_Icc h12
    have eb : segment ℝ b1 b2 = Icc b2 b1 := by rw [segment_symm]; exact segment_eq_Icc h34
    rw [ea] at hξa hA; rw [eb] at hξb hB
    obtain ⟨u, v, hu, hv, huξ, hξv⟩ := u3h_real_comb_ordered h12 h34 hξa hξb
      (fun y hy hyI => (hA y hy.symm hyI).symm) (fun y hy hyI => (hB y hy.symm hyI).symm)
    exact ⟨u, v, ⟨hu.1.symm, hu.2.symm⟩, ⟨hv.1.symm, hv.2.symm⟩,
      by rw [segment_eq_Icc (huξ.trans hξv)]; exact ⟨huξ, hξv⟩⟩

/-- Two segments on a line whose endpoints are compatible meet in the hull of the common endpoints. -/
theorem u3h_segment_inter_segment {p : Plane} {r : ℝ} (hp : p ≠ 0) {a1 a2 b1 b2 : Plane}
    (ha1 : planeDot p a1 = r) (ha2 : planeDot p a2 = r) (hb1 : planeDot p b1 = r)
    (hb2 : planeDot p b2 = r)
    (hA : ∀ y, (y = b1 ∨ y = b2) → y ∈ segment ℝ a1 a2 → (y = a1 ∨ y = a2))
    (hB : ∀ y, (y = a1 ∨ y = a2) → y ∈ segment ℝ b1 b2 → (y = b1 ∨ y = b2)) :
    segment ℝ a1 a2 ∩ segment ℝ b1 b2 = convexHull ℝ ({a1, a2} ∩ {b1, b2} : Set Plane) := by
  apply Subset.antisymm
  · rintro x ⟨hxa, hxb⟩
    have hx : planeDot p x = r := (u3h_convex_eq p r).segment_subset ha1 ha2 hxa
    have hxa' := (u3h_mem_segment_iff_coord hp ha1 ha2 hx).1 hxa
    have hxb' := (u3h_mem_segment_iff_coord hp hb1 hb2 hx).1 hxb
    have hA' : ∀ y, (y = planeDot (u3h_dir p) b1 ∨ y = planeDot (u3h_dir p) b2) →
        y ∈ segment ℝ (planeDot (u3h_dir p) a1) (planeDot (u3h_dir p) a2) →
        (y = planeDot (u3h_dir p) a1 ∨ y = planeDot (u3h_dir p) a2) := by
      rintro y (rfl | rfl) hy
      · rcases hA b1 (Or.inl rfl) ((u3h_mem_segment_iff_coord hp ha1 ha2 hb1).2 hy) with e | e <;>
          simp [e]
      · rcases hA b2 (Or.inr rfl) ((u3h_mem_segment_iff_coord hp ha1 ha2 hb2).2 hy) with e | e <;>
          simp [e]
    have hB' : ∀ y, (y = planeDot (u3h_dir p) a1 ∨ y = planeDot (u3h_dir p) a2) →
        y ∈ segment ℝ (planeDot (u3h_dir p) b1) (planeDot (u3h_dir p) b2) →
        (y = planeDot (u3h_dir p) b1 ∨ y = planeDot (u3h_dir p) b2) := by
      rintro y (rfl | rfl) hy
      · rcases hB a1 (Or.inl rfl) ((u3h_mem_segment_iff_coord hp hb1 hb2 ha1).2 hy) with e | e <;>
          simp [e]
      · rcases hB a2 (Or.inr rfl) ((u3h_mem_segment_iff_coord hp hb1 hb2 ha2).2 hy) with e | e <;>
          simp [e]
    obtain ⟨u, v, ⟨hu1, hu2⟩, ⟨hv1, hv2⟩, hξ⟩ := u3h_real_comb hxa' hxb' hA' hB'
    have pick : ∀ w : ℝ, (w = planeDot (u3h_dir p) a1 ∨ w = planeDot (u3h_dir p) a2) →
        (w = planeDot (u3h_dir p) b1 ∨ w = planeDot (u3h_dir p) b2) →
        ∃ W : Plane, W ∈ ({a1, a2} ∩ {b1, b2} : Set Plane) ∧ planeDot p W = r ∧
          planeDot (u3h_dir p) W = w := by
      rintro w (rfl | rfl) h2
      · refine ⟨a1, ⟨by simp, ?_⟩, ha1, rfl⟩
        rcases h2 with h | h
        · simp [u3h_coord_injOn hp ha1 hb1 h]
        · simp [u3h_coord_injOn hp ha1 hb2 h]
      · refine ⟨a2, ⟨by simp, ?_⟩, ha2, rfl⟩
        rcases h2 with h | h
        · simp [u3h_coord_injOn hp ha2 hb1 h]
        · simp [u3h_coord_injOn hp ha2 hb2 h]
    obtain ⟨U, hU, hUr, hUκ⟩ := pick u hu1 hu2
    obtain ⟨V, hV, hVr, hVκ⟩ := pick v hv1 hv2
    have : x ∈ segment ℝ U V :=
      (u3h_mem_segment_iff_coord hp hUr hVr hx).2 (by rw [hUκ, hVκ]; exact hξ)
    exact segment_subset_convexHull hU hV this
  · apply convexHull_min
    · rintro y ⟨hy1, hy2⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hy1 hy2
      refine ⟨?_, ?_⟩
      · rcases hy1 with rfl | rfl
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _
      · rcases hy2 with rfl | rfl
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _
    · exact (convex_segment _ _).inter (convex_segment _ _)

/-- **Gluing criterion**: a family of triangles, pairwise separated when distinct, in which every
vertex of one triangle lying in another is a vertex of it, has face-to-face intersections. -/
theorem u3h_inter_of_family {F : Set Triangle}
    (hsep : ∀ Δ ∈ F, ∀ Δ' ∈ F, Δ.carrier ≠ Δ'.carrier → ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧
      (∀ i, planeDot p (Δ.v i) ≤ r) ∧ ∀ i, r ≤ planeDot p (Δ'.v i))
    (hvert : ∀ Δ ∈ F, ∀ Δ' ∈ F, ∀ j, Δ'.v j ∈ Δ.carrier → Δ'.v j ∈ range Δ.v) :
    ∀ Δ ∈ F, ∀ Δ' ∈ F, Δ.carrier ∩ Δ'.carrier = convexHull ℝ (range Δ.v ∩ range Δ'.v) := by
  intro Δ hΔ Δ' hΔ'
  by_cases hc : Δ.carrier = Δ'.carrier
  · have hr : range Δ.v = range Δ'.v := by
      apply Subset.antisymm
      · rintro _ ⟨j, rfl⟩
        exact hvert Δ' hΔ' Δ hΔ j (hc ▸ subset_convexHull ℝ _ ⟨j, rfl⟩)
      · rintro _ ⟨j, rfl⟩
        exact hvert Δ hΔ Δ' hΔ' j (hc.symm ▸ subset_convexHull ℝ _ ⟨j, rfl⟩)
    rw [← hc, inter_self, hr, inter_self]; exact hc
  obtain ⟨p, r, hp, h1, h2⟩ := hsep Δ hΔ Δ' hΔ' hc
  rw [u3h_inter_of_separated Δ Δ' h1 h2]
  have hcommon : ∀ w, w ∈ range Δ.v → w ∈ range Δ'.v → planeDot p w = r := by
    rintro w ⟨i, rfl⟩ hw'
    obtain ⟨j, hj⟩ := hw'
    have := h2 j; rw [hj] at this
    exact le_antisymm (h1 i) this
  rcases u3h_vertices_on_line Δ (r := r) hp with hA | ⟨a1, a2, ha1, ha2, ha1r, ha2r, hA⟩
  · rw [hA, convexHull_empty, empty_inter]
    have : range Δ.v ∩ range Δ'.v = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro w ⟨hw, hw'⟩
      have : w ∈ range Δ.v ∩ {x | planeDot p x = r} := ⟨hw, hcommon w hw hw'⟩
      rw [hA] at this; exact this
    rw [this, convexHull_empty]
  rcases u3h_vertices_on_line Δ' (r := r) hp with hB | ⟨b1, b2, hb1, hb2, hb1r, hb2r, hB⟩
  · rw [hB, convexHull_empty, inter_empty]
    have : range Δ.v ∩ range Δ'.v = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro w ⟨hw, hw'⟩
      have : w ∈ range Δ'.v ∩ {x | planeDot p x = r} := ⟨hw', hcommon w hw hw'⟩
      rw [hB] at this; exact this
    rw [this, convexHull_empty]
  rw [hA, hB, convexHull_pair, convexHull_pair]
  have hA' : ∀ y, (y = b1 ∨ y = b2) → y ∈ segment ℝ a1 a2 → (y = a1 ∨ y = a2) := by
    intro y hy hys
    have hyΔ : y ∈ Δ.carrier :=
      segment_subset_convexHull ha1 ha2 hys
    have hy' : y ∈ range Δ'.v := by rcases hy with rfl | rfl <;> assumption
    have hyr : planeDot p y = r := by rcases hy with rfl | rfl <;> assumption
    obtain ⟨j, rfl⟩ := hy'
    have := hvert Δ hΔ Δ' hΔ' j hyΔ
    have hmem : Δ'.v j ∈ range Δ.v ∩ {x | planeDot p x = r} := ⟨this, hyr⟩
    rw [hA] at hmem
    simpa using hmem
  have hB' : ∀ y, (y = a1 ∨ y = a2) → y ∈ segment ℝ b1 b2 → (y = b1 ∨ y = b2) := by
    intro y hy hys
    have hyΔ : y ∈ Δ'.carrier :=
      segment_subset_convexHull hb1 hb2 hys
    have hy' : y ∈ range Δ.v := by rcases hy with rfl | rfl <;> assumption
    have hyr : planeDot p y = r := by rcases hy with rfl | rfl <;> assumption
    obtain ⟨j, rfl⟩ := hy'
    have := hvert Δ' hΔ' Δ hΔ j hyΔ
    have hmem : Δ.v j ∈ range Δ'.v ∩ {x | planeDot p x = r} := ⟨this, hyr⟩
    rw [hB] at hmem
    simpa using hmem
  rw [u3h_segment_inter_segment hp ha1r ha2r hb1r hb2r hA' hB']
  congr 1
  apply Subset.antisymm
  · rintro w ⟨hw1, hw2⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hw1 hw2
    refine ⟨?_, ?_⟩
    · rcases hw1 with rfl | rfl <;> assumption
    · rcases hw2 with rfl | rfl <;> assumption
  · rintro w ⟨hw, hw'⟩
    have hr := hcommon w hw hw'
    have m1 : w ∈ range Δ.v ∩ {x | planeDot p x = r} := ⟨hw, hr⟩
    have m2 : w ∈ range Δ'.v ∩ {x | planeDot p x = r} := ⟨hw', hr⟩
    rw [hA] at m1; rw [hB] at m2
    exact ⟨m1, m2⟩

/-! ### U3 helpers: splitting one triangle along one line -/

theorem u3h_mem_carrier_of_homog (T : Triangle) {a b c s : ℝ} {x : Plane} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hs : 0 < s) (hsum : a + b + c = s)
    (h : a • T.v 0 + b • T.v 1 + c • T.v 2 = s • x) : x ∈ T.carrier := by
  rw [u3h_mem_carrier_iff]
  refine ⟨a / s, b / s, c / s, div_nonneg ha hs.le, div_nonneg hb hs.le, div_nonneg hc hs.le, ?_, ?_⟩
  · rw [← add_div, ← add_div, hsum, div_self hs.ne']
  · have : (a / s) • T.v 0 + (b / s) • T.v 1 + (c / s) • T.v 2 =
        s⁻¹ • (a • T.v 0 + b • T.v 1 + c • T.v 2) := by
      simp only [smul_add, smul_smul, div_eq_inv_mul]
    rw [this, h, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

theorem u3h_not_mem_of_lt (Δ : Triangle) {p : Plane} {r : ℝ} (h : ∀ i, planeDot p (Δ.v i) ≤ r)
    {w : Plane} (hw : r < planeDot p w) : w ∉ Δ.carrier :=
  fun hm => absurd (u3h_carrier_subset_le Δ h hm) (not_le.2 hw)

theorem u3h_not_mem_of_gt (Δ : Triangle) {p : Plane} {r : ℝ} (h : ∀ i, r ≤ planeDot p (Δ.v i))
    {w : Plane} (hw : planeDot p w < r) : w ∉ Δ.carrier :=
  fun hm => absurd (u3h_carrier_subset_ge Δ h hm) (not_le.2 hw)

theorem u3h_det_eq_planeDot (u w : Plane) : det u w = planeDot (u3h_dir u) w := by
  simp [det, planeDot, u3h_dir]; ring

theorem u3h_dir_ne_zero {u : Plane} (hu : u ≠ 0) : u3h_dir u ≠ 0 := by
  intro h
  apply hu
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp [u3h_dir] at h1 h2
  exact Prod.ext h2 h1

theorem u3h_inter_self_face (Δ : Triangle) :
    Δ.carrier ∩ Δ.carrier = convexHull ℝ (range Δ.v ∩ range Δ.v) := by
  rw [inter_self, inter_self]; rfl

/-- The crossing point of the line `planeDot p x = r` with the segment `[A, B]`. -/
noncomputable def u3h_cross (p : Plane) (r : ℝ) (A B : Plane) : Plane :=
  (1 - (r - planeDot p A) / (planeDot p B - planeDot p A)) • A +
    ((r - planeDot p A) / (planeDot p B - planeDot p A)) • B

theorem u3h_cross_spec (p : Plane) (r : ℝ) {A B : Plane} (hAB : planeDot p A ≠ planeDot p B) :
    ∃ α : ℝ, u3h_cross p r A B = (1 - α) • A + α • B ∧
      α * (planeDot p B - planeDot p A) = r - planeDot p A :=
  ⟨_, rfl, div_mul_cancel₀ _ (sub_ne_zero.2 hAB.symm)⟩

theorem u3h_cross_param_pos {hA hB r α : ℝ} (hopp : (hA < r ∧ r < hB) ∨ (hB < r ∧ r < hA))
    (hα : α * (hB - hA) = r - hA) : 0 < α ∧ α < 1 := by
  rcases hopp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hd : 0 < hB - hA := by linarith
    constructor
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith
  · have hd : hB - hA < 0 := by linarith
    constructor
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith

theorem u3h_mem_openSegment_of_param {A B : Plane} {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    (1 - α) • A + α • B ∈ openSegment ℝ A B :=
  ⟨1 - α, α, by linarith, h0, by ring, rfl⟩

theorem u3h_mem_segment_of_param {A B : Plane} {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    (1 - α) • A + α • B ∈ segment ℝ A B :=
  ⟨1 - α, α, by linarith, h0, by ring, rfl⟩

theorem u3h_planeDot_param (p A B : Plane) (α : ℝ) :
    planeDot p ((1 - α) • A + α • B) = planeDot p A + α * (planeDot p B - planeDot p A) := by
  rw [u3h_planeDot_combo]; ring

theorem u3h_cross_unique {p : Plane} {r : ℝ} {A B : Plane} (hAB : planeDot p A ≠ planeDot p B)
    {α : ℝ} (hα : α * (planeDot p B - planeDot p A) = r - planeDot p A) {x : Plane}
    (hx : x ∈ openSegment ℝ A B) (hxr : planeDot p x = r) : x = (1 - α) • A + α • B := by
  obtain ⟨a, b, _, _, hab, rfl⟩ := hx
  have hab' : a = 1 - b := by linarith
  subst hab'
  rw [u3h_planeDot_param] at hxr
  have : (b - α) * (planeDot p B - planeDot p A) = 0 := by linear_combination hxr - hα
  rcases mul_eq_zero.1 this with h | h
  · have : b = α := by linarith
    rw [this]
  · exact absurd (sub_eq_zero.1 h) hAB.symm

/-- Opposite strict signs at the two ends of edge `i`. -/
def u3h_Opp (T : Triangle) (p : Plane) (r : ℝ) (i : Fin 3) : Prop :=
  (planeDot p (T.v i) < r ∧ r < planeDot p (T.v (i + 1))) ∨
    (r < planeDot p (T.v i) ∧ planeDot p (T.v (i + 1)) < r)

/-- Specification of the pieces of `T` cut by the line `planeDot p x = r`. -/
structure u3h_SplitSpec (T : Triangle) (p : Plane) (r : ℝ) (F : Set Triangle) : Prop where
  finite : F.Finite
  cover : (⋃ Δ ∈ F, Δ.carrier) = T.carrier
  inter : ∀ Δ ∈ F, ∀ Δ' ∈ F, Δ.carrier ∩ Δ'.carrier = convexHull ℝ (range Δ.v ∩ range Δ'.v)
  side : ∀ Δ ∈ F, (∀ j, planeDot p (Δ.v j) ≤ r) ∨ (∀ j, r ≤ planeDot p (Δ.v j))
  vert : ∀ Δ ∈ F, ∀ j, (∃ i, Δ.v j = T.v i) ∨
    (∃ i, Δ.v j ∈ openSegment ℝ (T.v i) (T.v (i + 1)) ∧ planeDot p (Δ.v j) = r ∧ u3h_Opp T p r i)
  old : ∀ i, ∃ Δ ∈ F, ∃ j, Δ.v j = T.v i
  cross : ∀ i, u3h_Opp T p r i → ∀ x ∈ openSegment ℝ (T.v i) (T.v (i + 1)), planeDot p x = r →
    ∃ Δ ∈ F, ∃ j, Δ.v j = x

theorem u3h_split_one_sided (T : Triangle) (p : Plane) (r : ℝ)
    (h : (∀ j, planeDot p (T.v j) ≤ r) ∨ (∀ j, r ≤ planeDot p (T.v j))) :
    u3h_SplitSpec T p r {T} where
  finite := finite_singleton T
  cover := by simp
  inter := by
    intro Δ hΔ Δ' hΔ'
    rw [mem_singleton_iff] at hΔ hΔ'; subst hΔ; subst hΔ'
    exact u3h_inter_self_face _
  side := by intro Δ hΔ; rw [mem_singleton_iff] at hΔ; subst hΔ; exact h
  vert := by intro Δ hΔ j; rw [mem_singleton_iff] at hΔ; subst hΔ; exact Or.inl ⟨j, rfl⟩
  old := fun i => ⟨T, mem_singleton T, i, rfl⟩
  cross := by
    intro i hi
    exfalso
    rcases h with h | h <;> rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith [h (i + 1)]
    · linarith [h i]
    · linarith [h i]
    · linarith [h (i + 1)]

theorem u3h_Opp_neg (T : Triangle) (p : Plane) (r : ℝ) (i : Fin 3) :
    u3h_Opp T (-p) (-r) i ↔ u3h_Opp T p r i := by
  unfold u3h_Opp
  simp only [u3h_planeDot_neg_left]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · right; constructor <;> linarith
    · left; constructor <;> linarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · right; constructor <;> linarith
    · left; constructor <;> linarith

theorem u3h_SplitSpec_neg {T : Triangle} {p : Plane} {r : ℝ} {F : Set Triangle}
    (h : u3h_SplitSpec T (-p) (-r) F) : u3h_SplitSpec T p r F where
  finite := h.finite
  cover := h.cover
  inter := h.inter
  side := by
    intro Δ hΔ
    rcases h.side Δ hΔ with hs | hs
    · right; intro j; have := hs j; rw [u3h_planeDot_neg_left] at this; linarith
    · left; intro j; have := hs j; rw [u3h_planeDot_neg_left] at this; linarith
  vert := by
    intro Δ hΔ j
    rcases h.vert Δ hΔ j with hv | ⟨i, h1, h2, h3⟩
    · exact Or.inl hv
    · refine Or.inr ⟨i, h1, ?_, (u3h_Opp_neg T p r i).1 h3⟩
      rw [u3h_planeDot_neg_left] at h2; linarith
  old := h.old
  cross := by
    intro i hi x hx hxr
    exact h.cross i ((u3h_Opp_neg T p r i).2 hi) x hx (by rw [u3h_planeDot_neg_left, hxr])

/-- Cyclic rotation of the vertex list. -/
def u3h_rot (T : Triangle) (k : Fin 3) : Triangle where
  v := fun j => T.v (j + k)
  pos := by
    show 0 < det (T.v (1 + k) - T.v (0 + k)) (T.v (2 + k) - T.v (0 + k))
    rw [zero_add, add_comm (1 : Fin 3) k, add_comm (2 : Fin 3) k]
    exact u3h_pos_cyc T k

@[simp] theorem u3h_rot_v (T : Triangle) (k j : Fin 3) : (u3h_rot T k).v j = T.v (j + k) := rfl

theorem u3h_fin3_a : ∀ i k : Fin 3, i - k + k = i := by decide
theorem u3h_fin3_b : ∀ i k : Fin 3, i + 1 + k = i + k + 1 := by decide
theorem u3h_fin3_c : ∀ i k : Fin 3, i - k + 1 + k = i + 1 := by decide

theorem u3h_rot_range (T : Triangle) (k : Fin 3) : range (u3h_rot T k).v = range T.v := by
  ext y; constructor
  · rintro ⟨j, rfl⟩; exact ⟨j + k, rfl⟩
  · rintro ⟨j, rfl⟩; exact ⟨j - k, by rw [u3h_rot_v, u3h_fin3_a]⟩

theorem u3h_rot_carrier (T : Triangle) (k : Fin 3) : (u3h_rot T k).carrier = T.carrier := by
  unfold Triangle.carrier; rw [u3h_rot_range]

theorem u3h_Opp_rot (T : Triangle) (p : Plane) (r : ℝ) (k i : Fin 3) :
    u3h_Opp (u3h_rot T k) p r i ↔ u3h_Opp T p r (i + k) := by
  unfold u3h_Opp; simp only [u3h_rot_v]; rw [u3h_fin3_b]

theorem u3h_SplitSpec_rot {T : Triangle} {p : Plane} {r : ℝ} {F : Set Triangle} (k : Fin 3)
    (h : u3h_SplitSpec (u3h_rot T k) p r F) : u3h_SplitSpec T p r F where
  finite := h.finite
  cover := by rw [h.cover, u3h_rot_carrier]
  inter := h.inter
  side := h.side
  vert := by
    intro Δ hΔ j
    rcases h.vert Δ hΔ j with ⟨i, hi⟩ | ⟨i, h1, h2, h3⟩
    · exact Or.inl ⟨i + k, hi⟩
    · refine Or.inr ⟨i + k, ?_, h2, (u3h_Opp_rot T p r k i).1 h3⟩
      rw [u3h_rot_v, u3h_rot_v, u3h_fin3_b] at h1; exact h1
  old := by
    intro i
    obtain ⟨Δ, hΔ, j, hj⟩ := h.old (i - k)
    exact ⟨Δ, hΔ, j, by rw [hj, u3h_rot_v, u3h_fin3_a]⟩
  cross := by
    intro i hi x hx hxr
    have hi' : u3h_Opp (u3h_rot T k) p r (i - k) := by rw [u3h_Opp_rot, u3h_fin3_a]; exact hi
    refine h.cross (i - k) hi' x ?_ hxr
    rw [u3h_rot_v, u3h_rot_v, u3h_fin3_a, u3h_fin3_c]; exact hx

theorem u3h_exists_param (p : Plane) (r : ℝ) {A B : Plane} (hAB : planeDot p A ≠ planeDot p B) :
    ∃ α : ℝ, α * (planeDot p B - planeDot p A) = r - planeDot p A :=
  ⟨_, div_mul_cancel₀ _ (sub_ne_zero.2 hAB.symm)⟩

/-- Vector identities used for the pieces (all by `ring`). -/
theorem u3h_det_split1 (v0 v1 v2 : Plane) (α : ℝ) :
    det (v1 - v0) (((1 - α) • v1 + α • v2) - v0) = α * det (v1 - v0) (v2 - v0) := by
  simp [det]; ring

theorem u3h_det_split2 (v0 v1 v2 : Plane) (α : ℝ) :
    det (((1 - α) • v1 + α • v2) - v0) (v2 - v0) = (1 - α) * det (v1 - v0) (v2 - v0) := by
  simp [det]; ring

theorem u3h_det_split3 (v0 v1 v2 : Plane) (α : ℝ) :
    det (((1 - α) • v1 + α • v2) - v0) (v1 - v0) = -(α * det (v1 - v0) (v2 - v0)) := by
  simp [det]; ring

/-- Pattern B at index 0: `v 0` on the line, `v 1` strictly above, `v 2` strictly below. -/
theorem u3h_splitB0 (T : Triangle) (p : Plane) (r : ℝ) (h0 : planeDot p (T.v 0) = r)
    (h1 : r < planeDot p (T.v 1)) (h2 : planeDot p (T.v 2) < r) :
    ∃ F : Set Triangle, u3h_SplitSpec T p r F := by
  have hAB : planeDot p (T.v 1) ≠ planeDot p (T.v 2) := by linarith
  obtain ⟨α, hα⟩ := u3h_exists_param p r hAB
  obtain ⟨hα0, hα1⟩ := u3h_cross_param_pos (Or.inr ⟨h2, h1⟩) hα
  set P : Plane := (1 - α) • T.v 1 + α • T.v 2 with hPdef
  have hPr : planeDot p P = r := by rw [hPdef, u3h_planeDot_param]; linear_combination hα
  have hPmem : P ∈ openSegment ℝ (T.v 1) (T.v 2) := u3h_mem_openSegment_of_param hα0 hα1
  have hPT : P ∈ T.carrier :=
    segment_subset_convexHull (mem_range_self 1) (mem_range_self 2) (openSegment_subset_segment ℝ _ _ hPmem)
  have hD := T.pos
  have pos1 : 0 < det (T.v 1 - T.v 0) (P - T.v 0) := by
    rw [hPdef, u3h_det_split1]; exact mul_pos hα0 hD
  have pos2 : 0 < det (P - T.v 0) (T.v 2 - T.v 0) := by
    rw [hPdef, u3h_det_split2]; exact mul_pos (by linarith) hD
  have neg3 : det (P - T.v 0) (T.v 1 - T.v 0) < 0 := by
    rw [hPdef, u3h_det_split3]; linarith [mul_pos hα0 hD]
  obtain ⟨Δ1, e1⟩ : ∃ Δ : Triangle, Δ.v = ![T.v 0, T.v 1, P] :=
    ⟨Triangle.mk ![T.v 0, T.v 1, P] pos1, rfl⟩
  obtain ⟨Δ2, e2⟩ : ∃ Δ : Triangle, Δ.v = ![T.v 0, P, T.v 2] :=
    ⟨Triangle.mk ![T.v 0, P, T.v 2] pos2, rfl⟩
  have d10 : Δ1.v 0 = T.v 0 := by rw [e1]; rfl
  have d11 : Δ1.v 1 = T.v 1 := by rw [e1]; rfl
  have d12 : Δ1.v 2 = P := by rw [e1]; rfl
  have d20 : Δ2.v 0 = T.v 0 := by rw [e2]; rfl
  have d21 : Δ2.v 1 = P := by rw [e2]; rfl
  have d22 : Δ2.v 2 = T.v 2 := by rw [e2]; rfl
  -- the separating line through `v 0` and `P`
  have hP0 : P - T.v 0 ≠ 0 := by
    intro h
    have : P = T.v 0 := sub_eq_zero.1 h
    apply u3h_v_not_mem_segment T 0
    rw [← this]
    simpa using openSegment_subset_segment ℝ _ _ hPmem
  set p' := u3h_dir (P - T.v 0) with hp'def
  set r' := planeDot p' (T.v 0) with hr'def
  have hp' : p' ≠ 0 := u3h_dir_ne_zero hP0
  have hq : ∀ w, planeDot p' w - r' = det (P - T.v 0) (w - T.v 0) := fun w => by
    rw [u3h_det_eq_planeDot, u3h_planeDot_sub]
  have hq0 : planeDot p' (T.v 0) = r' := rfl
  have hqP : planeDot p' P = r' := by
    have := hq P
    rw [show det (P - T.v 0) (P - T.v 0) = 0 by simp [det]; ring] at this
    linarith
  have hv2 : r' < planeDot p' (T.v 2) := by linarith [hq (T.v 2)]
  have hv1 : planeDot p' (T.v 1) < r' := by linarith [hq (T.v 1)]
  have s1 : ∀ i, planeDot p' (Δ1.v i) ≤ r' := by
    intro i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, d10]; linarith
    · simp only [Fin.mk_one, Fin.isValue, d11]; linarith
    · simp only [Fin.reduceFinMk, d12]; linarith
  have s2 : ∀ i, r' ≤ planeDot p' (Δ2.v i) := by
    intro i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, d20]; linarith
    · simp only [Fin.mk_one, Fin.isValue, d21]; linarith
    · simp only [Fin.reduceFinMk, Fin.isValue, d22]; linarith
  have hΔ1T : Δ1.carrier ⊆ T.carrier := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨j, rfl⟩; fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, d10]; exact subset_convexHull ℝ _ ⟨0, rfl⟩
    · simp only [Fin.mk_one, Fin.isValue, d11]; exact subset_convexHull ℝ _ ⟨1, rfl⟩
    · simp only [Fin.reduceFinMk, d12]; exact hPT
  have hΔ2T : Δ2.carrier ⊆ T.carrier := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨j, rfl⟩; fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, d20]; exact subset_convexHull ℝ _ ⟨0, rfl⟩
    · simp only [Fin.mk_one, Fin.isValue, d21]; exact hPT
    · simp only [Fin.reduceFinMk, Fin.isValue, d22]; exact subset_convexHull ℝ _ ⟨2, rfl⟩
  refine ⟨{Δ1, Δ2}, ?_⟩
  refine
    { finite := toFinite _
      cover := ?_
      inter := ?_
      side := ?_
      vert := ?_
      old := ?_
      cross := ?_ }
  · rw [biUnion_pair]
    apply Subset.antisymm (union_subset hΔ1T hΔ2T)
    intro x hx
    obtain ⟨a, b, c, ha, hb, hc, habc, rfl⟩ := (u3h_mem_carrier_iff T x).1 hx
    rcases le_total (c * (1 - α)) (b * α) with hcb | hcb
    · left
      refine u3h_mem_carrier_of_homog Δ1 (a := a * α) (b := b * α - c * (1 - α)) (c := c) (s := α)
        (mul_nonneg ha hα0.le) (by linarith) hc hα0 (by linear_combination α * habc) ?_
      rw [d10, d11, d12, hPdef]
      ext <;> simp <;> ring
    · right
      refine u3h_mem_carrier_of_homog Δ2 (a := a * (1 - α)) (b := b) (c := c * (1 - α) - b * α)
        (s := 1 - α) (mul_nonneg ha (by linarith)) hb (by linarith) (by linarith)
        (by linear_combination (1 - α) * habc) ?_
      rw [d20, d21, d22, hPdef]
      ext <;> simp <;> ring
  · apply u3h_inter_of_family
    · rintro Δ (rfl | rfl) Δ' (rfl | rfl) hne
      · exact absurd rfl hne
      · exact ⟨p', r', hp', s1, s2⟩
      · refine ⟨-p', -r', neg_ne_zero.2 hp', fun i => ?_, fun i => ?_⟩
        · rw [u3h_planeDot_neg_left]; linarith [s2 i]
        · rw [u3h_planeDot_neg_left]; linarith [s1 i]
      · exact absurd rfl hne
    · rintro Δ (rfl | rfl) Δ' (rfl | rfl) j hj
      · exact ⟨j, rfl⟩
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, d20] at hj ⊢; exact ⟨0, d10⟩
        · simp only [Fin.mk_one, Fin.isValue, d21] at hj ⊢; exact ⟨2, d12⟩
        · simp only [Fin.reduceFinMk, Fin.isValue, d22] at hj ⊢
          exact absurd hj (u3h_not_mem_of_lt Δ s1 hv2)
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, d10] at hj ⊢; exact ⟨0, d20⟩
        · simp only [Fin.mk_one, Fin.isValue, d11] at hj ⊢
          exact absurd hj (u3h_not_mem_of_gt Δ s2 hv1)
        · simp only [Fin.reduceFinMk, d12] at hj ⊢; exact ⟨1, d21⟩
      · exact ⟨j, rfl⟩
  · rintro Δ (rfl | rfl)
    · right; intro j; fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, d10]; linarith
      · simp only [Fin.mk_one, Fin.isValue, d11]; linarith
      · simp only [Fin.reduceFinMk, d12]; linarith
    · left; intro j; fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, d20]; linarith
      · simp only [Fin.mk_one, Fin.isValue, d21]; linarith
      · simp only [Fin.reduceFinMk, Fin.isValue, d22]; linarith
  · have hOpp1 : u3h_Opp T p r 1 := Or.inr ⟨h1, by simpa using h2⟩
    rintro Δ (rfl | rfl) j
    · fin_cases j
      · exact Or.inl ⟨0, d10⟩
      · exact Or.inl ⟨1, d11⟩
      · refine Or.inr ⟨1, ?_, by simpa [d12] using hPr, hOpp1⟩
        simp only [Fin.reduceFinMk, d12]; simpa using hPmem
    · fin_cases j
      · exact Or.inl ⟨0, d20⟩
      · refine Or.inr ⟨1, ?_, by simpa [d21] using hPr, hOpp1⟩
        simp only [Fin.mk_one, Fin.isValue, d21]; simpa using hPmem
      · exact Or.inl ⟨2, d22⟩
  · intro i; fin_cases i
    · exact ⟨Δ1, by simp, 0, d10⟩
    · exact ⟨Δ1, by simp, 1, d11⟩
    · exact ⟨Δ2, by simp, 2, d22⟩
  · intro i hi x hx hxr
    fin_cases i
    · exfalso; rcases hi with ⟨a1, _⟩ | ⟨a1, _⟩ <;> simp at a1 <;> linarith
    · refine ⟨Δ1, by simp, 2, ?_⟩
      rw [d12, hPdef]
      exact (u3h_cross_unique hAB hα (by simpa using hx) hxr).symm
    · exfalso; rcases hi with ⟨_, a2⟩ | ⟨_, a2⟩ <;> simp at a2 <;> linarith

theorem u3h_det_A1 (v0 v1 v2 : Plane) (α β : ℝ) :
    det (((1 - α) • v0 + α • v1) - v0) (((1 - β) • v2 + β • v0) - v0) =
      (α * (1 - β)) * det (v1 - v0) (v2 - v0) := by
  simp [det]; ring

theorem u3h_det_A2 (v0 v1 v2 : Plane) (α : ℝ) :
    det (v1 - ((1 - α) • v0 + α • v1)) (v2 - ((1 - α) • v0 + α • v1)) =
      (1 - α) * det (v1 - v0) (v2 - v0) := by
  simp [det]; ring

theorem u3h_det_A3 (v0 v1 v2 : Plane) (α β : ℝ) :
    det (v2 - ((1 - α) • v0 + α • v1)) (((1 - β) • v2 + β • v0) - ((1 - α) • v0 + α • v1)) =
      (α * β) * det (v1 - v0) (v2 - v0) := by
  simp [det]; ring

theorem u3h_det_A4 (v0 v1 v2 : Plane) (α : ℝ) :
    det (v2 - ((1 - α) • v0 + α • v1)) (v1 - ((1 - α) • v0 + α • v1)) =
      -((1 - α) * det (v1 - v0) (v2 - v0)) := by
  simp [det]; ring

/-- Pattern A at index 0: `v 0` strictly above the line, `v 1`, `v 2` strictly below. -/
theorem u3h_splitA0 (T : Triangle) (p : Plane) (r : ℝ) (h0 : r < planeDot p (T.v 0))
    (h1 : planeDot p (T.v 1) < r) (h2 : planeDot p (T.v 2) < r) :
    ∃ F : Set Triangle, u3h_SplitSpec T p r F := by
  have hAB1 : planeDot p (T.v 0) ≠ planeDot p (T.v 1) := by linarith
  have hp0 : p ≠ 0 := by
    rintro rfl; rw [u3h_planeDot_zero_left] at h0 h1; linarith
  have hAB2 : planeDot p (T.v 2) ≠ planeDot p (T.v 0) := by linarith
  obtain ⟨α, hα⟩ := u3h_exists_param p r hAB1
  obtain ⟨β, hβ⟩ := u3h_exists_param p r hAB2
  obtain ⟨hα0, hα1⟩ := u3h_cross_param_pos (Or.inr ⟨h1, h0⟩) hα
  obtain ⟨hβ0, hβ1⟩ := u3h_cross_param_pos (Or.inl ⟨h2, h0⟩) hβ
  have hγ : (1 - β) * (planeDot p (T.v 2) - planeDot p (T.v 0)) = r - planeDot p (T.v 0) := by
    linear_combination hβ
  set P : Plane := (1 - α) • T.v 0 + α • T.v 1 with hPdef
  set Q : Plane := (1 - β) • T.v 2 + β • T.v 0 with hQdef
  have hPr : planeDot p P = r := by rw [hPdef, u3h_planeDot_param]; linear_combination hα
  have hQr : planeDot p Q = r := by rw [hQdef, u3h_planeDot_param]; linear_combination hβ
  have hPmem : P ∈ openSegment ℝ (T.v 0) (T.v 1) := u3h_mem_openSegment_of_param hα0 hα1
  have hQmem : Q ∈ openSegment ℝ (T.v 2) (T.v 0) := u3h_mem_openSegment_of_param hβ0 hβ1
  have hPT : P ∈ T.carrier :=
    segment_subset_convexHull (mem_range_self 0) (mem_range_self 1)
      (openSegment_subset_segment ℝ _ _ hPmem)
  have hQT : Q ∈ T.carrier :=
    segment_subset_convexHull (mem_range_self 2) (mem_range_self 0)
      (openSegment_subset_segment ℝ _ _ hQmem)
  have hD := T.pos
  have pos1 : 0 < det (P - T.v 0) (Q - T.v 0) := by
    rw [hPdef, hQdef, u3h_det_A1]; exact mul_pos (mul_pos hα0 (by linarith)) hD
  have pos2 : 0 < det (T.v 1 - P) (T.v 2 - P) := by
    rw [hPdef, u3h_det_A2]; exact mul_pos (by linarith) hD
  have pos3 : 0 < det (T.v 2 - P) (Q - P) := by
    rw [hPdef, hQdef, u3h_det_A3]; exact mul_pos (mul_pos hα0 hβ0) hD
  have neg4 : det (T.v 2 - P) (T.v 1 - P) < 0 := by
    rw [hPdef, u3h_det_A4]; linarith [mul_pos (show (0:ℝ) < 1 - α by linarith) hD]
  obtain ⟨Δ1, e1⟩ : ∃ Δ : Triangle, Δ.v = ![T.v 0, P, Q] := ⟨Triangle.mk ![T.v 0, P, Q] pos1, rfl⟩
  obtain ⟨Δ2, e2⟩ : ∃ Δ : Triangle, Δ.v = ![P, T.v 1, T.v 2] :=
    ⟨Triangle.mk ![P, T.v 1, T.v 2] pos2, rfl⟩
  obtain ⟨Δ3, e3⟩ : ∃ Δ : Triangle, Δ.v = ![P, T.v 2, Q] := ⟨Triangle.mk ![P, T.v 2, Q] pos3, rfl⟩
  have d10 : Δ1.v 0 = T.v 0 := by rw [e1]; rfl
  have d11 : Δ1.v 1 = P := by rw [e1]; rfl
  have d12 : Δ1.v 2 = Q := by rw [e1]; rfl
  have d20 : Δ2.v 0 = P := by rw [e2]; rfl
  have d21 : Δ2.v 1 = T.v 1 := by rw [e2]; rfl
  have d22 : Δ2.v 2 = T.v 2 := by rw [e2]; rfl
  have d30 : Δ3.v 0 = P := by rw [e3]; rfl
  have d31 : Δ3.v 1 = T.v 2 := by rw [e3]; rfl
  have d32 : Δ3.v 2 = Q := by rw [e3]; rfl
  -- signs with respect to the cutting line
  have s1 : ∀ i, r ≤ planeDot p (Δ1.v i) := by
    intro i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, d10]; linarith
    · simp only [Fin.mk_one, Fin.isValue, d11]; linarith
    · simp only [Fin.reduceFinMk, d12]; linarith
  have s2 : ∀ i, planeDot p (Δ2.v i) ≤ r := by
    intro i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, d20]; linarith
    · simp only [Fin.mk_one, Fin.isValue, d21]; linarith
    · simp only [Fin.reduceFinMk, d22]; linarith
  have s3 : ∀ i, planeDot p (Δ3.v i) ≤ r := by
    intro i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, d30]; linarith
    · simp only [Fin.mk_one, Fin.isValue, d31]; linarith
    · simp only [Fin.reduceFinMk, d32]; linarith
  -- the diagonal line through `P` and `v 2`
  have hP2 : T.v 2 - P ≠ 0 := by
    intro h
    have : T.v 2 = P := sub_eq_zero.1 h
    apply u3h_v_not_mem_segment T 2
    rw [this]
    simpa using openSegment_subset_segment ℝ _ _ hPmem
  set p'' := u3h_dir (T.v 2 - P) with hp''def
  set r'' := planeDot p'' P with hr''def
  have hp'' : p'' ≠ 0 := u3h_dir_ne_zero hP2
  have hq : ∀ w, planeDot p'' w - r'' = det (T.v 2 - P) (w - P) := fun w => by
    rw [u3h_det_eq_planeDot, u3h_planeDot_sub]
  have hqP : planeDot p'' P = r'' := rfl
  have hq2 : planeDot p'' (T.v 2) = r'' := by
    have := hq (T.v 2)
    rw [show det (T.v 2 - P) (T.v 2 - P) = 0 by simp [det]; ring] at this
    linarith
  have hqQ : r'' < planeDot p'' Q := by linarith [hq Q]
  have hq1 : planeDot p'' (T.v 1) < r'' := by linarith [hq (T.v 1)]
  have t2 : ∀ i, planeDot p'' (Δ2.v i) ≤ r'' := by
    intro i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, d20]; linarith
    · simp only [Fin.mk_one, Fin.isValue, d21]; linarith
    · simp only [Fin.reduceFinMk, d22]; linarith
  have t3 : ∀ i, r'' ≤ planeDot p'' (Δ3.v i) := by
    intro i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, d30]; linarith
    · simp only [Fin.mk_one, Fin.isValue, d31]; linarith
    · simp only [Fin.reduceFinMk, d32]; linarith
  have hΔ1T : Δ1.carrier ⊆ T.carrier := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨j, rfl⟩; fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, d10]; exact subset_convexHull ℝ _ ⟨0, rfl⟩
    · simp only [Fin.mk_one, Fin.isValue, d11]; exact hPT
    · simp only [Fin.reduceFinMk, d12]; exact hQT
  have hΔ2T : Δ2.carrier ⊆ T.carrier := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨j, rfl⟩; fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, d20]; exact hPT
    · simp only [Fin.mk_one, Fin.isValue, d21]; exact subset_convexHull ℝ _ ⟨1, rfl⟩
    · simp only [Fin.reduceFinMk, d22]; exact subset_convexHull ℝ _ ⟨2, rfl⟩
  have hΔ3T : Δ3.carrier ⊆ T.carrier := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨j, rfl⟩; fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, d30]; exact hPT
    · simp only [Fin.mk_one, Fin.isValue, d31]; exact subset_convexHull ℝ _ ⟨2, rfl⟩
    · simp only [Fin.reduceFinMk, d32]; exact hQT
  refine ⟨{Δ1, Δ2, Δ3}, ?_⟩
  refine
    { finite := toFinite _
      cover := ?_
      inter := ?_
      side := ?_
      vert := ?_
      old := ?_
      cross := ?_ }
  · rw [biUnion_insert, biUnion_pair]
    apply Subset.antisymm (union_subset hΔ1T (union_subset hΔ2T hΔ3T))
    intro x hx
    obtain ⟨a, b, c, ha, hb, hc, habc, rfl⟩ := (u3h_mem_carrier_iff T x).1 hx
    have habc' : a = 1 - b - c := by linarith
    subst habc'
    have hx' : planeDot p ((1 - b - c) • T.v 0 + b • T.v 1 + c • T.v 2) =
        (1 - b - c) * planeDot p (T.v 0) + b * planeDot p (T.v 1) + c * planeDot p (T.v 2) := by
      rw [u3h_planeDot_add, u3h_planeDot_combo, u3h_planeDot_smul]
    have key : (planeDot p ((1 - b - c) • T.v 0 + b • T.v 1 + c • T.v 2) - r) * (α * (1 - β)) =
        (r - planeDot p (T.v 0)) * (b * (1 - β) + c * α - α * (1 - β)) := by
      rw [hx']
      linear_combination (b * (1 - β)) * hα + (c * α) * hγ
    have hpos : 0 < α * (1 - β) := mul_pos hα0 (by linarith)
    rcases le_total r (planeDot p ((1 - b - c) • T.v 0 + b • T.v 1 + c • T.v 2)) with hxr | hxr
    · left
      have hS : b * (1 - β) + c * α - α * (1 - β) ≤ 0 := by
        by_contra hS; push Not at hS
        have := mul_nonneg (sub_nonneg.2 hxr) hpos.le
        nlinarith
      refine u3h_mem_carrier_of_homog Δ1 (a := α * (1 - β) - b * (1 - β) - c * α)
        (b := b * (1 - β)) (c := c * α) (s := α * (1 - β)) (by linarith)
        (mul_nonneg hb (by linarith)) (mul_nonneg hc hα0.le) hpos (by ring) ?_
      rw [d10, d11, d12, hPdef, hQdef]
      ext <;> simp <;> ring
    · have hS : 0 ≤ b * (1 - β) + c * α - α * (1 - β) := by
        by_contra hS; push Not at hS
        have := mul_nonneg (sub_nonneg.2 hxr) hpos.le
        nlinarith
      rcases le_total ((1 - b - c) * α) (b * (1 - α)) with hab | hab
      · right; left
        refine u3h_mem_carrier_of_homog Δ2 (a := 1 - b - c) (b := b * (1 - α) - (1 - b - c) * α)
          (c := c * (1 - α)) (s := 1 - α) ha (by linarith) (mul_nonneg hc (by linarith)) (by linarith)
          (by ring) ?_
        rw [d20, d21, d22, hPdef]
        ext <;> simp <;> ring
      · right; right
        refine u3h_mem_carrier_of_homog Δ3 (a := b * β) (b := b * (1 - β) + c * α - α * (1 - β))
          (c := (1 - b - c) * α - b * (1 - α)) (s := α * β) (mul_nonneg hb hβ0.le) hS (by linarith)
          (mul_pos hα0 hβ0) (by ring) ?_
        rw [d30, d31, d32, hPdef, hQdef]
        ext <;> simp <;> ring
  · apply u3h_inter_of_family
    · rintro Δ (rfl | rfl | rfl) Δ' (rfl | rfl | rfl) hne
      · exact absurd rfl hne
      · refine ⟨-p, -r, ?_, fun i => ?_, fun i => ?_⟩
        · exact neg_ne_zero.2 hp0
        · rw [u3h_planeDot_neg_left]; linarith [s1 i]
        · rw [u3h_planeDot_neg_left]; linarith [s2 i]
      · refine ⟨-p, -r, ?_, fun i => ?_, fun i => ?_⟩
        · exact neg_ne_zero.2 hp0
        · rw [u3h_planeDot_neg_left]; linarith [s1 i]
        · rw [u3h_planeDot_neg_left]; linarith [s3 i]
      · exact ⟨p, r, hp0, s2, s1⟩
      · exact absurd rfl hne
      · exact ⟨p'', r'', hp'', t2, t3⟩
      · exact ⟨p, r, hp0, s3, s1⟩
      · refine ⟨-p'', -r'', neg_ne_zero.2 hp'', fun i => ?_, fun i => ?_⟩
        · rw [u3h_planeDot_neg_left]; linarith [t3 i]
        · rw [u3h_planeDot_neg_left]; linarith [t2 i]
      · exact absurd rfl hne
    · rintro Δ (rfl | rfl | rfl) Δ' (rfl | rfl | rfl) j hj
      · exact ⟨j, rfl⟩
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, d20] at hj ⊢; exact ⟨1, d11⟩
        · simp only [Fin.mk_one, Fin.isValue, d21] at hj ⊢
          exact absurd hj (u3h_not_mem_of_gt Δ s1 h1)
        · simp only [Fin.reduceFinMk, d22] at hj ⊢
          exact absurd hj (u3h_not_mem_of_gt Δ s1 h2)
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, d30] at hj ⊢; exact ⟨1, d11⟩
        · simp only [Fin.mk_one, Fin.isValue, d31] at hj ⊢
          exact absurd hj (u3h_not_mem_of_gt Δ s1 h2)
        · simp only [Fin.reduceFinMk, d32] at hj ⊢; exact ⟨2, d12⟩
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, d10] at hj ⊢
          exact absurd hj (u3h_not_mem_of_lt Δ s2 h0)
        · simp only [Fin.mk_one, Fin.isValue, d11] at hj ⊢; exact ⟨0, d20⟩
        · simp only [Fin.reduceFinMk, d12] at hj ⊢
          exact absurd hj (u3h_not_mem_of_lt Δ t2 hqQ)
      · exact ⟨j, rfl⟩
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, d30] at hj ⊢; exact ⟨0, d20⟩
        · simp only [Fin.mk_one, Fin.isValue, d31] at hj ⊢; exact ⟨2, d22⟩
        · simp only [Fin.reduceFinMk, d32] at hj ⊢
          exact absurd hj (u3h_not_mem_of_lt Δ t2 hqQ)
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, d10] at hj ⊢
          exact absurd hj (u3h_not_mem_of_lt Δ s3 h0)
        · simp only [Fin.mk_one, Fin.isValue, d11] at hj ⊢; exact ⟨0, d30⟩
        · simp only [Fin.reduceFinMk, d12] at hj ⊢; exact ⟨2, d32⟩
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, d20] at hj ⊢; exact ⟨0, d30⟩
        · simp only [Fin.mk_one, Fin.isValue, d21] at hj ⊢
          exact absurd hj (u3h_not_mem_of_gt Δ t3 hq1)
        · simp only [Fin.reduceFinMk, d22] at hj ⊢; exact ⟨1, d31⟩
      · exact ⟨j, rfl⟩
  · rintro Δ (rfl | rfl | rfl)
    · exact Or.inr s1
    · exact Or.inl s2
    · exact Or.inl s3
  · have hOpp0 : u3h_Opp T p r 0 := Or.inr ⟨h0, by simpa using h1⟩
    have hOpp2 : u3h_Opp T p r 2 := Or.inl ⟨h2, by simpa using h0⟩
    have hPv : ∀ (Δ : Triangle) (j : Fin 3), Δ.v j = P → (∃ i, Δ.v j = T.v i) ∨
        (∃ i, Δ.v j ∈ openSegment ℝ (T.v i) (T.v (i + 1)) ∧ planeDot p (Δ.v j) = r ∧ u3h_Opp T p r i) := by
      intro Δ j hj
      refine Or.inr ⟨0, ?_, by rw [hj]; exact hPr, hOpp0⟩
      rw [hj]; simpa using hPmem
    have hQv : ∀ (Δ : Triangle) (j : Fin 3), Δ.v j = Q → (∃ i, Δ.v j = T.v i) ∨
        (∃ i, Δ.v j ∈ openSegment ℝ (T.v i) (T.v (i + 1)) ∧ planeDot p (Δ.v j) = r ∧ u3h_Opp T p r i) := by
      intro Δ j hj
      refine Or.inr ⟨2, ?_, by rw [hj]; exact hQr, hOpp2⟩
      rw [hj]; simpa using hQmem
    rintro Δ (rfl | rfl | rfl) j
    · fin_cases j
      · exact Or.inl ⟨0, d10⟩
      · exact hPv _ _ d11
      · exact hQv _ _ d12
    · fin_cases j
      · exact hPv _ _ d20
      · exact Or.inl ⟨1, d21⟩
      · exact Or.inl ⟨2, d22⟩
    · fin_cases j
      · exact hPv _ _ d30
      · exact Or.inl ⟨2, d31⟩
      · exact hQv _ _ d32
  · intro i; fin_cases i
    · exact ⟨Δ1, by simp, 0, d10⟩
    · exact ⟨Δ2, by simp, 1, d21⟩
    · exact ⟨Δ2, by simp, 2, d22⟩
  · intro i hi x hx hxr
    fin_cases i
    · refine ⟨Δ1, by simp, 1, ?_⟩
      rw [d11, hPdef]
      exact (u3h_cross_unique hAB1 hα (by simpa using hx) hxr).symm
    · exfalso; rcases hi with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> simp at a1 a2 <;> linarith
    · refine ⟨Δ1, by simp, 2, ?_⟩
      rw [d12, hQdef]
      exact (u3h_cross_unique hAB2 hβ (by simpa using hx) hxr).symm

/-- Every triangle splits along every line. -/
theorem u3h_split_exists (T : Triangle) (p : Plane) (r : ℝ) :
    ∃ F : Set Triangle, u3h_SplitSpec T p r F := by
  by_cases hone : (∀ j, planeDot p (T.v j) ≤ r) ∨ (∀ j, r ≤ planeDot p (T.v j))
  · exact ⟨{T}, u3h_split_one_sided T p r hone⟩
  have key : ∀ (S : Triangle),
      (r < planeDot p (S.v 0) ∧ planeDot p (S.v 1) < r ∧ planeDot p (S.v 2) < r) ∨
      (planeDot p (S.v 0) < r ∧ r < planeDot p (S.v 1) ∧ r < planeDot p (S.v 2)) ∨
      (planeDot p (S.v 0) = r ∧ r < planeDot p (S.v 1) ∧ planeDot p (S.v 2) < r) ∨
      (planeDot p (S.v 0) = r ∧ planeDot p (S.v 1) < r ∧ r < planeDot p (S.v 2)) →
      ∃ F, u3h_SplitSpec S p r F := by
    rintro S (⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩)
    · exact u3h_splitA0 S p r a b c
    · obtain ⟨F, hF⟩ := u3h_splitA0 S (-p) (-r) (by rw [u3h_planeDot_neg_left]; linarith)
        (by rw [u3h_planeDot_neg_left]; linarith) (by rw [u3h_planeDot_neg_left]; linarith)
      exact ⟨F, u3h_SplitSpec_neg hF⟩
    · exact u3h_splitB0 S p r a b c
    · obtain ⟨F, hF⟩ := u3h_splitB0 S (-p) (-r) (by rw [u3h_planeDot_neg_left]; linarith)
        (by rw [u3h_planeDot_neg_left]; linarith) (by rw [u3h_planeDot_neg_left]; linarith)
      exact ⟨F, u3h_SplitSpec_neg hF⟩
  suffices ∃ k : Fin 3, ∃ F, u3h_SplitSpec (u3h_rot T k) p r F by
    obtain ⟨k, F, hF⟩ := this; exact ⟨F, u3h_SplitSpec_rot k hF⟩
  rcases lt_trichotomy (planeDot p (T.v 0)) r with h0 | h0 | h0 <;>
    rcases lt_trichotomy (planeDot p (T.v 1)) r with h1 | h1 | h1 <;>
    rcases lt_trichotomy (planeDot p (T.v 2)) r with h2 | h2 | h2
  all_goals first
    | (refine absurd (Or.inl fun j => ?_) hone
       fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk] <;> linarith)
    | (refine absurd (Or.inr fun j => ?_) hone
       fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk] <;> linarith)
    | (refine ⟨0, key _ (Or.inl ⟨?_, ?_, ?_⟩)⟩ <;> [simpa using h0; simpa using h1; simpa using h2])
    | (refine ⟨0, key _ (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))⟩ <;>
        [simpa using h0; simpa using h1; simpa using h2])
    | (refine ⟨0, key _ (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)))⟩ <;>
        [simpa using h0; simpa using h1; simpa using h2])
    | (refine ⟨0, key _ (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩)))⟩ <;>
        [simpa using h0; simpa using h1; simpa using h2])
    | (refine ⟨1, key _ (Or.inl ⟨?_, ?_, ?_⟩)⟩ <;> [simpa using h1; simpa using h2; simpa using h0])
    | (refine ⟨1, key _ (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))⟩ <;>
        [simpa using h1; simpa using h2; simpa using h0])
    | (refine ⟨1, key _ (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)))⟩ <;>
        [simpa using h1; simpa using h2; simpa using h0])
    | (refine ⟨1, key _ (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩)))⟩ <;>
        [simpa using h1; simpa using h2; simpa using h0])
    | (refine ⟨2, key _ (Or.inl ⟨?_, ?_, ?_⟩)⟩ <;> [simpa using h2; simpa using h0; simpa using h1])
    | (refine ⟨2, key _ (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))⟩ <;>
        [simpa using h2; simpa using h0; simpa using h1])
    | (refine ⟨2, key _ (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)))⟩ <;>
        [simpa using h2; simpa using h0; simpa using h1])
    | (refine ⟨2, key _ (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩)))⟩ <;>
        [simpa using h2; simpa using h0; simpa using h1])

/-! ### U3 helpers: canonical pieces and the one-line refinement -/

/-- A vertex is an extreme point of the triangle. -/
theorem u3h_v_extreme (T : Triangle) (i : Fin 3) : T.v i ∈ Set.extremePoints ℝ T.carrier := by
  refine ⟨subset_convexHull ℝ _ ⟨i, rfl⟩, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hmem
  obtain ⟨a1, b1, c1, ha1, hb1, hc1, s1, rfl⟩ := (u3h_mem_carrier_iff T x₁).1 hx₁
  obtain ⟨a2, b2, c2, ha2, hb2, hc2, s2, rfl⟩ := (u3h_mem_carrier_iff T x₂).1 hx₂
  obtain ⟨t1, t2, ht1, ht2, ht, hx⟩ := hmem
  have hx' : (t1 * a1 + t2 * a2) • T.v 0 + (t1 * b1 + t2 * b2) • T.v 1 + (t1 * c1 + t2 * c2) • T.v 2
      = T.v i := by
    rw [← hx]; simp only [smul_add, add_smul, mul_smul]; abel
  fin_cases i
  · have hu := u3h_bary_unique T (a' := 1) (b' := 0) (c' := 0) (by simpa using hx') (by nlinarith)
    obtain ⟨_, e2, e3⟩ := hu
    have : b1 = 0 ∧ b2 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg ht1.le hb1, mul_nonneg ht2.le hb2,
        mul_nonneg ht1.le hc1, mul_nonneg ht2.le hc2]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := this
    have e1 : a1 = 1 := by linarith
    have e1' : a2 = 1 := by linarith
    subst e1 e1'; simp
  · have hu := u3h_bary_unique T (a' := 0) (b' := 1) (c' := 0) (by simpa using hx') (by nlinarith)
    obtain ⟨e1, _, e3⟩ := hu
    have : a1 = 0 ∧ a2 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg ht1.le ha1, mul_nonneg ht2.le ha2,
        mul_nonneg ht1.le hc1, mul_nonneg ht2.le hc2]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := this
    have e1 : b1 = 1 := by linarith
    have e1' : b2 = 1 := by linarith
    subst e1 e1'; simp
  · have hu := u3h_bary_unique T (a' := 0) (b' := 0) (c' := 1) (by simpa using hx') (by nlinarith)
    obtain ⟨e1, e2, _⟩ := hu
    have : a1 = 0 ∧ a2 = 0 ∧ b1 = 0 ∧ b2 = 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg ht1.le ha1, mul_nonneg ht2.le ha2,
        mul_nonneg ht1.le hb1, mul_nonneg ht2.le hb2]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := this
    have e1 : c1 = 1 := by linarith
    have e1' : c2 = 1 := by linarith
    subst e1 e1'; simp

/-- Triangles with the same carrier have the same vertex set. -/
theorem u3h_range_eq_of_carrier_eq {T T' : Triangle} (h : T.carrier = T'.carrier) :
    range T.v = range T'.v := by
  have key : ∀ (S S' : Triangle), S.carrier = S'.carrier → range S.v ⊆ range S'.v := by
    rintro S S' hSS' _ ⟨i, rfl⟩
    have := u3h_v_extreme S i
    rw [hSS'] at this
    exact extremePoints_convexHull_subset this
  exact Subset.antisymm (key T T' h) (key T' T h.symm)

def u3h_defaultTri : Triangle where
  v := ![((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))]
  pos := by
    show (0 : ℝ) < det (((1 : ℝ), (0 : ℝ)) - ((0 : ℝ), (0 : ℝ))) (((0 : ℝ), (1 : ℝ)) - ((0 : ℝ), (0 : ℝ)))
    simp [det]

/-- A canonical triangle with a given carrier (when one exists). -/
noncomputable def u3h_canonTri (S : Set Plane) : Triangle := by
  classical exact if h : ∃ T : Triangle, T.carrier = S then h.choose else u3h_defaultTri

theorem u3h_canonTri_carrier (T : Triangle) : (u3h_canonTri T.carrier).carrier = T.carrier := by
  unfold u3h_canonTri
  rw [dif_pos ⟨T, rfl⟩]
  exact Exists.choose_spec (⟨T, rfl⟩ : ∃ T' : Triangle, T'.carrier = T.carrier)

theorem u3h_canonTri_range (T : Triangle) : range (u3h_canonTri T.carrier).v = range T.v :=
  u3h_range_eq_of_carrier_eq (u3h_canonTri_carrier T)

/-- The pieces of a triangle along a line; they depend only on the carrier. -/
noncomputable def u3h_pieces (S : Set Plane) (p : Plane) (r : ℝ) : Set Triangle :=
  (u3h_split_exists (u3h_canonTri S) p r).choose

theorem u3h_pieces_spec (S : Set Plane) (p : Plane) (r : ℝ) :
    u3h_SplitSpec (u3h_canonTri S) p r (u3h_pieces S p r) :=
  (u3h_split_exists (u3h_canonTri S) p r).choose_spec

/-- The pieces form a triangulation of the triangle. -/
def u3h_SplitSpec.toTriangulation {T : Triangle} {p : Plane} {r : ℝ} {F : Set Triangle}
    (h : u3h_SplitSpec T p r F) : Triangulation T.carrier :=
  ⟨F, h.finite, h.cover, h.inter⟩

theorem u3h_SplitSpec.subset {T : Triangle} {p : Plane} {r : ℝ} {F : Set Triangle}
    (h : u3h_SplitSpec T p r F) {Δ : Triangle} (hΔ : Δ ∈ F) : Δ.carrier ⊆ T.carrier := by
  rw [← h.cover]; exact subset_biUnion_of_mem (u := fun Δ => Δ.carrier) hΔ

theorem u3h_fin3_d : ∀ i : Fin 3, i + 2 + 1 = i := by decide
theorem u3h_fin3_e : ∀ i : Fin 3, i + 2 + 2 = i + 1 := by decide
theorem u3h_fin3_adj : ∀ a b : Fin 3, a ≠ b → b = a + 1 ∨ a = b + 1 := by decide
theorem u3h_fin3_ne : ∀ i : Fin 3, i ≠ i + 1 := by decide
theorem u3h_fin3_f : ∀ i : Fin 3, i + 1 + 1 = i + 2 := by decide
theorem u3h_fin3_g : ∀ i : Fin 3, i + 1 + 2 = i := by decide

/-- A point of an open edge in the hull of a set of vertices forces both ends into the set. -/
theorem u3h_endpoints_mem (C : Triangle) {S : Set Plane} (hS : S ⊆ range C.v) (i : Fin 3) {w : Plane}
    (hw : w ∈ openSegment ℝ (C.v i) (C.v (i + 1))) (hwS : w ∈ convexHull ℝ S) :
    C.v i ∈ S ∧ C.v (i + 1) ∈ S := by
  have hne : C.v i ≠ C.v (i + 1) := fun e => u3h_fin3_ne i (u3h_v_injective C e)
  have hws : w ∈ segment ℝ (C.v i) (C.v (i + 1)) := openSegment_subset_segment ℝ _ _ hw
  constructor
  · by_contra hn
    have hsub : S ⊆ {C.v (i + 1), C.v (i + 2)} := by
      intro y hy
      obtain ⟨j, rfl⟩ := hS hy
      have hne' : C.v j ≠ C.v i := fun e => hn (e ▸ hy)
      rcases u3h_other C i j hne' with e | e <;> simp [e]
    have := convexHull_mono hsub hwS
    rw [convexHull_pair] at this
    have hw' := u3h_segment_inter C i hws this
    rw [hw'] at hw
    exact hne ((right_mem_openSegment_iff).1 hw)
  · by_contra hn
    have hsub : S ⊆ {C.v (i + 2), C.v (i + 2 + 1)} := by
      intro y hy
      obtain ⟨j, rfl⟩ := hS hy
      have hne' : C.v j ≠ C.v (i + 1) := fun e => hn (e ▸ hy)
      rcases u3h_other C (i + 1) j hne' with e | e
      · rw [u3h_fin3_d]; simp [e, u3h_fin3_f]
      · rw [u3h_fin3_d]; simp [e, u3h_fin3_g]
    have := convexHull_mono hsub hwS
    rw [convexHull_pair] at this
    have hw' := u3h_segment_inter C (i + 2) this (by rw [u3h_fin3_d, u3h_fin3_e]; exact hws)
    rw [u3h_fin3_d] at hw'
    rw [hw'] at hw
    exact hne ((left_mem_openSegment_iff).1 hw)

/-- Compatibility: a vertex of a piece of `T'` lying in `T` is a vertex of a piece of `T`. -/
theorem u3h_compat {X : Set Plane} (K : Triangulation X) (p : Plane) (r : ℝ) {T T' : Triangle}
    (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) {Δ' : Triangle} (hΔ' : Δ' ∈ u3h_pieces T'.carrier p r)
    (j : Fin 3) (hw : Δ'.v j ∈ T.carrier) :
    ∃ Δ₂ ∈ u3h_pieces T.carrier p r, Δ'.v j ∈ range Δ₂.v := by
  by_cases hc : T.carrier = T'.carrier
  · rw [hc]; exact ⟨Δ', hΔ', j, rfl⟩
  set w := Δ'.v j with hwdef
  have spec := u3h_pieces_spec T.carrier p r
  have spec' := u3h_pieces_spec T'.carrier p r
  set C := u3h_canonTri T.carrier with hCdef
  set C' := u3h_canonTri T'.carrier with hC'def
  have hCr : range C.v = range T.v := u3h_canonTri_range T
  have hC'r : range C'.v = range T'.v := u3h_canonTri_range T'
  have hwT' : w ∈ T'.carrier := by
    rw [← u3h_canonTri_carrier T']
    exact spec'.subset hΔ' (subset_convexHull ℝ _ ⟨j, rfl⟩)
  have hwF : w ∈ convexHull ℝ (range T.v ∩ range T'.v) := by
    rw [← K.inter T hT T' hT']; exact ⟨hw, hwT'⟩
  have hS0 : range T.v ∩ range T'.v ⊆ range T'.v := inter_subset_right
  rcases spec'.vert Δ' hΔ' j with ⟨i, hi⟩ | ⟨i, hi1, hi2, hi3⟩
  · have hw' : w ∈ range T'.v := by rw [← hC'r]; exact ⟨i, hi.symm⟩
    obtain ⟨i', hi'⟩ := hw'
    have hmem := u3h_v_mem_convexHull T' hS0 i' (by rw [hi']; exact hwF)
    have hwT : w ∈ range C.v := by rw [hCr, ← hi']; exact hmem.1
    obtain ⟨i'', hi''⟩ := hwT
    obtain ⟨Δ₂, hΔ₂, j₂, hj₂⟩ := spec.old i''
    exact ⟨Δ₂, hΔ₂, j₂, by rw [hj₂, hi'']⟩
  · have hS0' : range T.v ∩ range T'.v ⊆ range C'.v := by rw [hC'r]; exact inter_subset_right
    obtain ⟨hA, hB⟩ := u3h_endpoints_mem C' hS0' i hi1 hwF
    have hA' : C'.v i ∈ range C.v := by rw [hCr]; exact hA.1
    have hB' : C'.v (i + 1) ∈ range C.v := by rw [hCr]; exact hB.1
    obtain ⟨a, ha⟩ := hA'
    obtain ⟨b, hb⟩ := hB'
    have hab : a ≠ b := by
      intro e; subst e
      exact u3h_fin3_ne i (u3h_v_injective C' (ha.symm.trans hb))
    rcases u3h_fin3_adj a b hab with e | e
    · subst e
      have hOpp : u3h_Opp C p r a := by
        unfold u3h_Opp at hi3 ⊢; rw [ha, hb]; exact hi3
      refine spec.cross a hOpp w ?_ hi2
      rw [ha, hb]; exact hi1
    · subst e
      have hOpp : u3h_Opp C p r b := by
        unfold u3h_Opp at hi3 ⊢; rw [ha, hb]
        rcases hi3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr ⟨h2, h1⟩
        · exact Or.inl ⟨h2, h1⟩
      refine spec.cross b hOpp w ?_ hi2
      rw [ha, hb, openSegment_symm]; exact hi1

/-- Refinement along one line. -/
theorem u3h_refine_one_line {X : Set Plane} (K : Triangulation X) (p : Plane) (r : ℝ) :
    ∃ K' : Triangulation X, K'.Refines K ∧ (∀ Δ ∈ K'.faces,
      Δ.carrier ⊆ {x | planeDot p x ≤ r} ∨ Δ.carrier ⊆ {x | r ≤ planeDot p x}) ∧
      ∀ Δ ∈ K'.faces, ∀ j, (∃ T ∈ K.faces, Δ.v j ∈ range T.v) ∨ planeDot p (Δ.v j) = r := by
  set F : Set Triangle := ⋃ T ∈ K.faces, u3h_pieces T.carrier p r with hFdef
  have hmem : ∀ Δ, Δ ∈ F ↔ ∃ T : Triangle, T ∈ K.faces ∧ Δ ∈ u3h_pieces T.carrier p r := by
    intro Δ; simp only [hFdef, mem_iUnion, exists_prop]
  have hsubT : ∀ T : Triangle, ∀ Δ ∈ u3h_pieces T.carrier p r, Δ.carrier ⊆ T.carrier := by
    intro T Δ hΔ
    have := (u3h_pieces_spec T.carrier p r).subset hΔ
    rwa [u3h_canonTri_carrier] at this
  have hfin : F.Finite := K.finite.biUnion (fun T _ => (u3h_pieces_spec T.carrier p r).finite)
  have hcover : (⋃ Δ ∈ F, Δ.carrier) = X := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨Δ, hΔ, hx⟩ := mem_iUnion₂.1 hx
      obtain ⟨T, hT, hΔT⟩ := (hmem Δ).1 hΔ
      rw [← K.cover]
      exact mem_iUnion₂.2 ⟨T, hT, hsubT T Δ hΔT hx⟩
    · intro x hx
      rw [← K.cover] at hx
      obtain ⟨T, hT, hxT⟩ := mem_iUnion₂.1 hx
      have spec := u3h_pieces_spec T.carrier p r
      have hxT' : x ∈ (u3h_canonTri T.carrier).carrier := by rwa [u3h_canonTri_carrier]
      rw [← spec.cover] at hxT'
      obtain ⟨Δ, hΔ, hxΔ⟩ := mem_iUnion₂.1 hxT'
      exact mem_iUnion₂.2 ⟨Δ, (hmem Δ).2 ⟨T, hT, hΔ⟩, hxΔ⟩
  have hinter : ∀ Δ ∈ F, ∀ Δ' ∈ F,
      Δ.carrier ∩ Δ'.carrier = convexHull ℝ (range Δ.v ∩ range Δ'.v) := by
    apply u3h_inter_of_family
    · intro Δ hΔ Δ' hΔ' hne
      obtain ⟨T, hT, hΔT⟩ := (hmem Δ).1 hΔ
      obtain ⟨T', hT', hΔT'⟩ := (hmem Δ').1 hΔ'
      by_cases hc : T.carrier = T'.carrier
      · rw [← hc] at hΔT'
        exact u3h_faces_separated (u3h_pieces_spec T.carrier p r).toTriangulation hΔT hΔT' hne
      · obtain ⟨q, s, hq, h1, h2⟩ := u3h_faces_separated K hT hT' hc
        refine ⟨q, s, hq, fun i => ?_, fun i => ?_⟩
        · exact u3h_carrier_subset_le T h1 (hsubT T Δ hΔT (subset_convexHull ℝ _ ⟨i, rfl⟩))
        · exact u3h_carrier_subset_ge T' h2 (hsubT T' Δ' hΔT' (subset_convexHull ℝ _ ⟨i, rfl⟩))
    · intro Δ hΔ Δ' hΔ' j hj
      obtain ⟨T, hT, hΔT⟩ := (hmem Δ).1 hΔ
      obtain ⟨T', hT', hΔT'⟩ := (hmem Δ').1 hΔ'
      have hwT : Δ'.v j ∈ T.carrier := hsubT T Δ hΔT hj
      obtain ⟨Δ₂, hΔ₂, j₂, hj₂⟩ := u3h_compat K p r hT hT' hΔT' j hwT
      have spec := u3h_pieces_spec T.carrier p r
      have hmem2 : Δ'.v j ∈ convexHull ℝ (range Δ.v ∩ range Δ₂.v) := by
        rw [← spec.inter Δ hΔT Δ₂ hΔ₂]
        exact ⟨hj, by rw [← hj₂]; exact subset_convexHull ℝ _ ⟨j₂, rfl⟩⟩
      have := u3h_v_mem_convexHull Δ₂ (S := range Δ.v ∩ range Δ₂.v) inter_subset_right j₂
        (by rw [hj₂]; exact hmem2)
      rw [hj₂] at this
      exact this.1
  refine ⟨⟨F, hfin, hcover, hinter⟩, ?_, ?_, ?_⟩
  · intro Δ hΔ
    obtain ⟨T, hT, hΔT⟩ := (hmem Δ).1 hΔ
    exact ⟨T, hT, hsubT T Δ hΔT⟩
  · intro Δ hΔ
    obtain ⟨T, hT, hΔT⟩ := (hmem Δ).1 hΔ
    rcases (u3h_pieces_spec T.carrier p r).side Δ hΔT with h | h
    · exact Or.inl (u3h_carrier_subset_le Δ h)
    · exact Or.inr (u3h_carrier_subset_ge Δ h)
  · intro Δ hΔ j
    obtain ⟨T, hT, hΔT⟩ := (hmem Δ).1 hΔ
    rcases (u3h_pieces_spec T.carrier p r).vert Δ hΔT j with ⟨i, hi⟩ | ⟨i, _, h2, _⟩
    · left; refine ⟨T, hT, ?_⟩; rw [← u3h_canonTri_range T]; exact ⟨i, hi.symm⟩
    · right; exact h2

theorem u3h_refines_trans {X : Set Plane} {K K' K'' : Triangulation X} (h1 : K''.Refines K')
    (h2 : K'.Refines K) : K''.Refines K := by
  intro T hT
  obtain ⟨T₁, hT₁, hsub⟩ := h1 T hT
  obtain ⟨T₀, hT₀, hsub'⟩ := h2 T₁ hT₁
  exact ⟨T₀, hT₀, hsub.trans hsub'⟩

theorem u3h_refine_along_lines {X : Set Plane} (K : Triangulation X) {m : ℕ} (a : Fin m → Plane)
    (c : Fin m → ℝ) :
    ∃ K' : Triangulation X, K'.Refines K ∧ (∀ T' ∈ K'.faces, ∀ j,
      T'.carrier ⊆ {x | planeDot (a j) x ≤ c j} ∨ T'.carrier ⊆ {x | c j ≤ planeDot (a j) x}) ∧
      ∀ T' ∈ K'.faces, ∀ i, (∃ T ∈ K.faces, T'.v i ∈ range T.v) ∨
        ∃ j, planeDot (a j) (T'.v i) = c j := by
  induction m generalizing K with
  | zero =>
    exact ⟨K, fun T hT => ⟨T, hT, subset_rfl⟩, fun T' _ j => j.elim0,
      fun T' hT' i => Or.inl ⟨T', hT', i, rfl⟩⟩
  | succ m ih =>
    obtain ⟨K₁, hK₁, h₁, v₁⟩ := ih K (fun j => a j.castSucc) (fun j => c j.castSucc)
    obtain ⟨K₂, hK₂, h₂, v₂⟩ := u3h_refine_one_line K₁ (a (Fin.last m)) (c (Fin.last m))
    refine ⟨K₂, u3h_refines_trans hK₂ hK₁, ?_, ?_⟩
    · intro T hT j
      obtain ⟨T₁, hT₁, hsub⟩ := hK₂ T hT
      refine Fin.lastCases ?_ (fun j => ?_) j
      · exact h₂ T hT
      · rcases h₁ T₁ hT₁ j with h | h
        · exact Or.inl (hsub.trans h)
        · exact Or.inr (hsub.trans h)
    · intro T hT i
      rcases v₂ T hT i with ⟨T₁, hT₁, ⟨k, hk⟩⟩ | h
      · rcases v₁ T₁ hT₁ k with ⟨T₀, hT₀, hk'⟩ | ⟨j, hj⟩
        · exact Or.inl ⟨T₀, hT₀, hk ▸ hk'⟩
        · exact Or.inr ⟨j.castSucc, hk ▸ hj⟩
      · exact Or.inr ⟨Fin.last m, h⟩

/-! ### U3 helpers: edge lines of a face, and refining so that faces map into faces -/

/-- Normal vector of edge `l` of `T` (inward side is `≥ u3h_edgeC`). -/
def u3h_edgeN (T : Triangle) (l : Fin 3) : Plane := u3h_dir (T.v (l + 1) - T.v l)

def u3h_edgeC (T : Triangle) (l : Fin 3) : ℝ := planeDot (u3h_edgeN T l) (T.v l)

theorem u3h_edge_eval (T : Triangle) (l : Fin 3) (x : Plane) :
    planeDot (u3h_edgeN T l) x - u3h_edgeC T l = det (T.v (l + 1) - T.v l) (x - T.v l) := by
  rw [u3h_edgeC, u3h_edgeN, u3h_det_eq_planeDot, u3h_planeDot_sub]

theorem u3h_edge_v0 (T : Triangle) (l : Fin 3) : planeDot (u3h_edgeN T l) (T.v l) = u3h_edgeC T l := rfl

theorem u3h_edge_v1 (T : Triangle) (l : Fin 3) :
    planeDot (u3h_edgeN T l) (T.v (l + 1)) = u3h_edgeC T l := by
  have := u3h_edge_eval T l (T.v (l + 1))
  rw [show det (T.v (l + 1) - T.v l) (T.v (l + 1) - T.v l) = 0 by simp [det]; ring] at this
  linarith

theorem u3h_edge_v2 (T : Triangle) (l : Fin 3) :
    u3h_edgeC T l < planeDot (u3h_edgeN T l) (T.v (l + 2)) := by
  have := u3h_edge_eval T l (T.v (l + 2))
  linarith [u3h_pos_cyc T l]

theorem u3h_edge_vertices (T : Triangle) (l i : Fin 3) :
    u3h_edgeC T l ≤ planeDot (u3h_edgeN T l) (T.v i) := by
  rcases u3h_fin3_cases l i with e | e | e
  · rw [e, u3h_edge_v0]
  · rw [e, u3h_edge_v1]
  · rw [e]; exact (u3h_edge_v2 T l).le
where
  u3h_fin3_cases : ∀ l i : Fin 3, i = l ∨ i = l + 1 ∨ i = l + 2 := by decide

theorem u3h_mem_iff_edges (T : Triangle) (x : Plane) :
    x ∈ T.carrier ↔ ∀ l, u3h_edgeC T l ≤ planeDot (u3h_edgeN T l) x := by
  rw [U1_mem_carrier_iff_det]
  have e0 : planeDot (u3h_edgeN T 0) x - u3h_edgeC T 0 = det (T.v 1 - T.v 0) (x - T.v 0) :=
    u3h_edge_eval T 0 x
  have e1 : planeDot (u3h_edgeN T 1) x - u3h_edgeC T 1 = det (T.v 2 - T.v 1) (x - T.v 1) :=
    u3h_edge_eval T 1 x
  have e2 : planeDot (u3h_edgeN T 2) x - u3h_edgeC T 2 = det (T.v 0 - T.v 2) (x - T.v 2) :=
    u3h_edge_eval T 2 x
  constructor
  · rintro ⟨h0, h1, h2⟩ l
    fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue]; linarith
    · simp only [Fin.mk_one, Fin.isValue]; linarith
    · simp only [Fin.reduceFinMk]; linarith
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2
    exact ⟨by linarith, by linarith, by linarith⟩

/-- The edge `l` is the face of `T` on its edge line. -/
theorem u3h_carrier_inter_edgeLine (T : Triangle) (l : Fin 3) :
    T.carrier ∩ {x | planeDot (u3h_edgeN T l) x = u3h_edgeC T l} ⊆ segment ℝ (T.v l) (T.v (l + 1)) := by
  rw [u3h_carrier_inter_line' T (u3h_edge_vertices T l)]
  have hsub : range T.v ∩ {x | planeDot (u3h_edgeN T l) x = u3h_edgeC T l} ⊆ {T.v l, T.v (l + 1)} := by
    rintro _ ⟨⟨i, rfl⟩, hi⟩
    simp only [mem_ofPred_eq] at hi
    rcases u3h_edge_vertices.u3h_fin3_cases l i with e | e | e
    · simp [e]
    · simp [e]
    · exfalso; rw [e] at hi; linarith [u3h_edge_v2 T l]
  intro x hx
  have := convexHull_mono hsub hx
  rwa [convexHull_pair] at this

/-- An interior point of a face is strictly inside every edge line. -/
theorem u3h_interior_strict (T : Triangle) {y : Plane} (hy : y ∈ T.carrier)
    (hfr : y ∉ frontier T.carrier) (l : Fin 3) : u3h_edgeC T l < planeDot (u3h_edgeN T l) y := by
  have hle := (u3h_mem_iff_edges T y).1 hy l
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hfr
    rw [U1_frontier_triangle]
    exact mem_iUnion.2 ⟨l, u3h_carrier_inter_edgeLine T l ⟨hy, h.symm⟩⟩

/-- **P15**: a triangle inside `Y`, on one side of every edge line of every face of a triangulation
of `Y`, lies in a single face. -/
theorem u3h_subset_face_of_sides {Y : Set Plane} (K' : Triangulation Y) (S : Triangle)
    (hSY : S.carrier ⊆ Y)
    (hside : ∀ T' ∈ K'.faces, ∀ l, (∀ i, planeDot (u3h_edgeN T' l) (S.v i) ≤ u3h_edgeC T' l) ∨
      (∀ i, u3h_edgeC T' l ≤ planeDot (u3h_edgeN T' l) (S.v i))) :
    ∃ T' ∈ K'.faces, S.carrier ⊆ T'.carrier := by
  haveI : Finite ↥K'.faces := K'.finite.to_subtype
  have hd : Dense (⋂ T' : ↥K'.faces, (frontier (T' : Triangle).carrier)ᶜ) := by
    apply dense_iInter_of_isOpen
    · intro T'; exact isClosed_frontier.isOpen_compl
    · intro T'
      rw [← interior_eq_empty_iff_dense_compl]
      exact interior_frontier (U1_triangle_isCompact _).isClosed
  obtain ⟨y, hyS, hyI⟩ := hd.inter_open_nonempty (interior S.carrier) isOpen_interior
    (U1_triangle_interior_nonempty S)
  have hyY : y ∈ Y := hSY (interior_subset hyS)
  rw [← K'.cover] at hyY
  obtain ⟨T', hT', hyT'⟩ := mem_iUnion₂.1 hyY
  have hyfr : y ∉ frontier T'.carrier := by
    have := mem_iInter.1 hyI ⟨T', hT'⟩
    exact this
  refine ⟨T', hT', fun x hx => ?_⟩
  rw [u3h_mem_iff_edges]
  intro l
  rcases hside T' hT' l with h | h
  · exfalso
    have h1 := u3h_carrier_subset_le S h (interior_subset hyS)
    have h2 := u3h_interior_strict T' hyT' hyfr l
    simp only [mem_ofPred_eq] at h1
    linarith
  · exact u3h_carrier_subset_ge S h hx

/-- The image of a face under a map affine on it. -/
theorem u3h_image_carrier (T : Triangle) {f : Plane → Plane} (h : IsPositiveAffineOn f T) :
    f '' T.carrier = (T.map f h).carrier := by
  obtain ⟨M, b, hMb⟩ := h.1
  have hv : ∀ i, (T.map f h).v i = f (T.v i) := fun i => rfl
  have h0 := hMb _ (subset_convexHull ℝ _ ⟨0, rfl⟩)
  have h1 := hMb _ (subset_convexHull ℝ _ ⟨1, rfl⟩)
  have h2 := hMb _ (subset_convexHull ℝ _ ⟨2, rfl⟩)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, b', c, ha, hb, hc, habc, rfl⟩ := (u3h_mem_carrier_iff T x).1 hx
    rw [u3h_mem_carrier_iff]
    refine ⟨a, b', c, ha, hb, hc, habc, ?_⟩
    have hmem : a • T.v 0 + b' • T.v 1 + c • T.v 2 ∈ T.carrier := hx
    have hb3 : a • b + b' • b + c • b = b := by rw [← add_smul, ← add_smul, habc, one_smul]
    simp only [hv]
    rw [hMb _ hmem, h0, h1, h2]
    simp only [map_add, map_smul, smul_add]
    conv_rhs => rw [← hb3]
    abel
  · intro hy
    obtain ⟨a, b', c, ha, hb, hc, habc, rfl⟩ := (u3h_mem_carrier_iff (T.map f h) y).1 hy
    have hmem : a • T.v 0 + b' • T.v 1 + c • T.v 2 ∈ T.carrier :=
      (u3h_mem_carrier_iff T _).2 ⟨a, b', c, ha, hb, hc, habc, rfl⟩
    have hb3 : a • b + b' • b + c • b = b := by rw [← add_smul, ← add_smul, habc, one_smul]
    refine ⟨_, hmem, ?_⟩
    simp only [hv]
    rw [hMb _ hmem, h0, h1, h2]
    simp only [map_add, map_smul, smul_add]
    conv_lhs => rw [← hb3]
    abel

theorem u3h_isPositiveAffineOn_congr {f g : Plane → Plane} {T : Triangle}
    (h : ∀ x ∈ T.carrier, f x = g x) (hf : IsPositiveAffineOn f T) : IsPositiveAffineOn g T := by
  obtain ⟨⟨M, b, hMb⟩, hpos⟩ := hf
  refine ⟨⟨M, b, fun x hx => by rw [← h x hx]; exact hMb x hx⟩, ?_⟩
  rw [← h _ (subset_convexHull ℝ _ ⟨0, rfl⟩), ← h _ (subset_convexHull ℝ _ ⟨1, rfl⟩),
    ← h _ (subset_convexHull ℝ _ ⟨2, rfl⟩)]
  exact hpos

/-- The pulled-back normal: `planeDot (u3h_pull M q) x = planeDot q (M x)`. -/
def u3h_pull (M : Plane →ₗ[ℝ] Plane) (q : Plane) : Plane :=
  (planeDot q (M ((1 : ℝ), (0 : ℝ))), planeDot q (M ((0 : ℝ), (1 : ℝ))))

theorem u3h_pull_eval (M : Plane →ₗ[ℝ] Plane) (q x : Plane) :
    planeDot (u3h_pull M q) x = planeDot q (M x) := by
  have hx : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_rhs => rw [hx]
  rw [map_add, map_smul, map_smul, u3h_planeDot_combo]
  simp [u3h_pull, planeDot]; ring

theorem u3h_refine_along_lines_finite {X : Set Plane} (K : Triangulation X) {ι : Type}
    [Finite ι] (a : ι → Plane) (c : ι → ℝ) :
    ∃ K' : Triangulation X, K'.Refines K ∧ (∀ T' ∈ K'.faces, ∀ j,
      T'.carrier ⊆ {x | planeDot (a j) x ≤ c j} ∨ T'.carrier ⊆ {x | c j ≤ planeDot (a j) x}) ∧
      ∀ T' ∈ K'.faces, ∀ i, (∃ T ∈ K.faces, T'.v i ∈ range T.v) ∨
        ∃ j, planeDot (a j) (T'.v i) = c j := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨K', h1, h2, h3⟩ := u3h_refine_along_lines K (a ∘ e.symm) (c ∘ e.symm)
  refine ⟨K', h1, fun T' hT' j => ?_, fun T' hT' i => ?_⟩
  · have := h2 T' hT' (e j)
    simpa using this
  · rcases h3 T' hT' i with h | ⟨j, hj⟩
    · exact Or.inl h
    · exact Or.inr ⟨e.symm j, hj⟩

/-- Refine `K` so that every new face `T'' ⊆ T` is carried by `φ T` into one face of `K' T`. -/
theorem u3h_refine_map_into_dep {X : Set Plane} (K : Triangulation X) (φ : ↥K.faces → Plane → Plane)
    (Y : ↥K.faces → Set Plane) (K' : ∀ T : ↥K.faces, Triangulation (Y T))
    (hφ : ∀ T : ↥K.faces, IsPositiveAffineOn (φ T) T.1)
    (hY : ∀ T : ↥K.faces, φ T '' T.1.carrier ⊆ Y T) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ ∀ T'' ∈ K''.faces, ∃ T : ↥K.faces,
      T''.carrier ⊆ T.1.carrier ∧ ∃ T' ∈ (K' T).faces, φ T '' T''.carrier ⊆ T'.carrier := by
  classical
  haveI : Finite ↥K.faces := K.finite.to_subtype
  have hMb : ∀ T : ↥K.faces, ∃ (M : Plane →ₗ[ℝ] Plane) (b : Plane),
      ∀ x ∈ T.1.carrier, φ T x = M x + b := fun T => (hφ T).1
  choose M b hMb using hMb
  haveI : ∀ T : ↥K.faces, Finite ↥(K' T).faces := fun T => (K' T).finite.to_subtype
  let ι := Σ T : ↥K.faces, ↥(K' T).faces × Fin 3
  let a : ι → Plane := fun i => u3h_pull (M i.1) (u3h_edgeN i.2.1.1 i.2.2)
  let c : ι → ℝ := fun i => u3h_edgeC i.2.1.1 i.2.2 - planeDot (u3h_edgeN i.2.1.1 i.2.2) (b i.1)
  obtain ⟨K'', hK'', hside, -⟩ := u3h_refine_along_lines_finite K a c
  refine ⟨K'', hK'', fun T'' hT'' => ?_⟩
  obtain ⟨T₀, hT₀, hsub⟩ := hK'' T'' hT''
  let T : ↥K.faces := ⟨T₀, hT₀⟩
  refine ⟨T, hsub, ?_⟩
  have hφ'' : IsPositiveAffineOn (φ T) T'' := U1_isPositiveAffineOn_mono (hφ T) hsub
  have hSc : (T''.map (φ T) hφ'').carrier = φ T '' T''.carrier := (u3h_image_carrier T'' hφ'').symm
  have hSY : (T''.map (φ T) hφ'').carrier ⊆ Y T := by
    rw [hSc]; exact (image_mono hsub).trans (hY T)
  have hsides : ∀ T' ∈ (K' T).faces, ∀ l,
      (∀ i, planeDot (u3h_edgeN T' l) ((T''.map (φ T) hφ'').v i) ≤ u3h_edgeC T' l) ∨
      (∀ i, u3h_edgeC T' l ≤ planeDot (u3h_edgeN T' l) ((T''.map (φ T) hφ'').v i)) := by
    intro T' hT' l
    have key : ∀ i, planeDot (u3h_edgeN T' l) ((T''.map (φ T) hφ'').v i) - u3h_edgeC T' l =
        planeDot (a ⟨T, ⟨T', hT'⟩, l⟩) (T''.v i) - c ⟨T, ⟨T', hT'⟩, l⟩ := by
      intro i
      have hvi : T''.v i ∈ T₀.carrier := hsub (subset_convexHull ℝ _ ⟨i, rfl⟩)
      show planeDot (u3h_edgeN T' l) (φ T (T''.v i)) - u3h_edgeC T' l = _
      rw [hMb T _ hvi]
      simp only [a, c]
      rw [u3h_planeDot_add, u3h_pull_eval]; ring
    rcases hside T'' hT'' ⟨T, ⟨T', hT'⟩, l⟩ with h | h
    · left; intro i
      have := h (subset_convexHull ℝ _ ⟨i, rfl⟩)
      simp only [mem_ofPred_eq] at this
      linarith [key i]
    · right; intro i
      have := h (subset_convexHull ℝ _ ⟨i, rfl⟩)
      simp only [mem_ofPred_eq] at this
      linarith [key i]
  obtain ⟨T', hT', hST'⟩ := u3h_subset_face_of_sides (K' T) _ hSY hsides
  exact ⟨T', hT', by rw [← hSc]; exact hST'⟩

theorem u3h_refine_map_into {X Y : Set Plane} (K : Triangulation X) (K' : Triangulation Y)
    {f : Plane → Plane} (hf : ∀ T ∈ K.faces, IsPositiveAffineOn f T) (h : f '' X ⊆ Y) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ ∀ T'' ∈ K''.faces, ∃ T ∈ K.faces,
      T''.carrier ⊆ T.carrier ∧ ∃ T' ∈ K'.faces, f '' T''.carrier ⊆ T'.carrier := by
  have hX : ∀ T : ↥K.faces, T.1.carrier ⊆ X := fun T => by
    have := subset_biUnion_of_mem (u := fun T : Triangle => T.carrier) T.2
    rwa [K.cover] at this
  obtain ⟨K'', h1, h2⟩ := u3h_refine_map_into_dep K (fun _ => f) (fun _ => Y) (fun _ => K')
    (fun T => hf T.1 T.2) (fun T => (image_mono (hX T)).trans h)
  refine ⟨K'', h1, fun T'' hT'' => ?_⟩
  obtain ⟨T, hsub, T', hT', himg⟩ := h2 T'' hT''
  exact ⟨T.1, T.2, hsub, T', hT', himg⟩

theorem u3h_chartPart_image {L : ℝ} {S : Set Sphere} {D : Set Plane} {f : Sphere → Plane}
    (hfD : f '' S ⊆ D) (b : Bool) : (f ∘ modelChart L b) '' chartPart L b S ⊆ D := by
  rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
  exact hfD ⟨modelChart L b x, hx, rfl⟩

/-- U3 (sm-3:462-466 "subdivide"): a triangulation can be refined so that every face lies on one
side of each of finitely many lines `{x | ⟪a j, x⟫ = c j}`. -/
theorem U3_refine_along_lines {X : Set Plane} (K : Triangulation X) {m : ℕ} (a : Fin m → Plane)
    (c : Fin m → ℝ) :
    ∃ K' : Triangulation X, K'.Refines K ∧ ∀ T' ∈ K'.faces, ∀ j,
      T'.carrier ⊆ {x | planeDot (a j) x ≤ c j} ∨ T'.carrier ⊆ {x | c j ≤ planeDot (a j) x} := by
  obtain ⟨K', h1, h2, -⟩ := u3h_refine_along_lines K a c
  exact ⟨K', h1, h2⟩

/-- U3: a triangulation can be refined so that every face lies in one face of a second
triangulation of a superset. -/
theorem U3_refine_into {X Y : Set Plane} (K : Triangulation X) (K' : Triangulation Y) (h : X ⊆ Y) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ ∀ T'' ∈ K''.faces, ∃ T' ∈ K'.faces, T''.carrier ⊆ T'.carrier := by
  have hid : ∀ T ∈ K.faces, IsPositiveAffineOn id T :=
    fun T _ => ⟨⟨LinearMap.id, 0, fun x _ => by simp⟩, T.pos⟩
  obtain ⟨K'', h1, h2⟩ := u3h_refine_map_into K K' hid (by rw [image_id]; exact h)
  refine ⟨K'', h1, fun T'' hT'' => ?_⟩
  obtain ⟨T, _, _, T', hT', himg⟩ := h2 T'' hT''
  exact ⟨T', hT', by rw [image_id] at himg; exact himg⟩

/-- U3 (common refinement): two triangulations of the same set have a common refinement. -/
theorem U3_common_refinement {X : Set Plane} (K K' : Triangulation X) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ K''.Refines K' := by
  obtain ⟨K'', h1, h2⟩ := U3_refine_into K K' subset_rfl
  exact ⟨K'', h1, h2⟩

/-- U3 (sm-3:535-537, composition): the composite of positive PL maps is positive PL on a
refinement of the source triangulation. -/
theorem U3_isPositivePLOn_comp {X Y : Set Plane} (K : Triangulation X) (K' : Triangulation Y)
    {f g : Plane → Plane} (hf : IsPositivePLOn f K) (hg : IsPositivePLOn g K') (h : f '' X ⊆ Y) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ IsPositivePLOn (g ∘ f) K'' := by
  obtain ⟨K'', h1, h2⟩ := u3h_refine_map_into K K' hf h
  refine ⟨K'', h1, fun T'' hT'' => ?_⟩
  obtain ⟨T, hT, hsub, T', hT', himg⟩ := h2 T'' hT''
  have hf'' : IsPositiveAffineOn f T'' := U1_isPositiveAffineOn_mono (hf T hT) hsub
  have hg' : IsPositiveAffineOn g (T''.map f hf'') :=
    U1_isPositiveAffineOn_mono (hg T' hT') (by rw [← u3h_image_carrier T'' hf'']; exact himg)
  exact U1_isPositiveAffineOn_comp hf'' hg'

/-- U3 (chart bookkeeping, FR-TD-14): a positive PL map to the plane followed by a positive PL map
from the plane into the sphere is a positive PL sphere map. -/
theorem U3_isPositivePLSphereMap_comp {L L' : ℝ} {S : Set Sphere} {D : Set Plane}
    {f : Sphere → Plane} {g : Plane → Sphere} (hf : IsPositivePLToPlane L S f) (hfD : f '' S ⊆ D)
    (hg : IsPositivePLFromPlane L' D g) : IsPositivePLSphereMap L L' S (g ∘ f) := by
  intro b
  obtain ⟨Kb, hKb⟩ := hf b
  obtain ⟨Kg, hKg⟩ := hg
  obtain ⟨K'', _, h2⟩ := u3h_refine_map_into Kb Kg hKb (u3h_chartPart_image hfD b)
  refine ⟨K'', fun T'' hT'' => ?_⟩
  obtain ⟨T, hT, hsub, Tg, hTg, himg'⟩ := h2 T'' hT''
  obtain ⟨b', hmem, hpos⟩ := hKg Tg hTg
  refine ⟨b', fun x hx => hmem _ (himg' ⟨x, hx, rfl⟩), ?_⟩
  have hf'' : IsPositiveAffineOn (f ∘ modelChart L b) T'' :=
    U1_isPositiveAffineOn_mono (hKb T hT) hsub
  have hg' : IsPositiveAffineOn (modelChartInv L' b' ∘ g) (T''.map _ hf'') :=
    U1_isPositiveAffineOn_mono hpos (by rw [← u3h_image_carrier T'' hf'']; exact himg')
  exact u3h_isPositiveAffineOn_congr (fun x _ => rfl) (U1_isPositiveAffineOn_comp hf'' hg')


/-! ### U3 helpers: chart algebra for the model (any `L ≠ 0`) -/

theorem u3h_supNorm_nonneg (y : Plane) : 0 ≤ supNorm y := le_max_of_le_left (abs_nonneg _)

theorem u3h_supNorm_eq_zero {y : Plane} (h : supNorm y = 0) : y = 0 := by
  unfold supNorm at h
  have h1 : |y.1| ≤ 0 := by rw [← h]; exact le_max_left _ _
  have h2 : |y.2| ≤ 0 := by rw [← h]; exact le_max_right _ _
  exact Prod.ext (abs_nonpos_iff.1 h1) (abs_nonpos_iff.1 h2)

theorem u3h_supNorm_pos {y : Plane} (h : y ≠ 0) : 0 < supNorm y :=
  lt_of_le_of_ne (u3h_supNorm_nonneg y) (fun e => h (u3h_supNorm_eq_zero e.symm))

theorem u3h_supNorm_smul (c : ℝ) (y : Plane) : supNorm (c • y) = |c| * supNorm y := by
  unfold supNorm
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul]
  rcases le_total |y.1| |y.2| with h | h
  · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h (abs_nonneg c))]
  · rw [max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left h (abs_nonneg c))]

theorem u3h_supNorm_swap (y : Plane) : supNorm (y.1, -y.2) = supNorm y := by
  unfold supNorm; simp [abs_neg]

theorem u3h_capInvFun_capInvFun {L : ℝ} (hL : L ≠ 0) {y : Plane} (hy : y ≠ 0) :
    capInvFun L (capInvFun L y) = y := by
  have hN := u3h_supNorm_pos hy
  have hw : supNorm (capInvFun L y) = |L / supNorm y ^ 2| * supNorm y := by
    rw [capInvFun, u3h_supNorm_smul, u3h_supNorm_swap]
  rw [capInvFun, hw]
  simp only [capInvFun]
  ext
  · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_pow, sq_abs]
    field_simp
  · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_pow, sq_abs]
    field_simp

theorem u3h_chartInv_chart {L : ℝ} (hL : L ≠ 0) (b : Bool) (y : Plane) :
    modelChartInv L b (modelChart L b y) = y := by
  cases b
  · rfl
  · show modelChartInv L true (capChart L y) = y
    unfold capChart
    split_ifs with h
    · subst h; rfl
    · show capInvFun L (capInvFun L y) = y
      exact u3h_capInvFun_capInvFun hL h

theorem u3h_chart_chartInv {L : ℝ} (hL : L ≠ 0) (b : Bool) {z : Sphere}
    (hz : z ∈ modelChart L b '' modelDomain L b) : modelChart L b (modelChartInv L b z) = z := by
  obtain ⟨y, _, rfl⟩ := hz
  rw [u3h_chartInv_chart hL]

theorem u3h_chartInv_mem {L : ℝ} (hL : L ≠ 0) (b : Bool) {z : Sphere}
    (hz : z ∈ modelChart L b '' modelDomain L b) : modelChartInv L b z ∈ modelDomain L b := by
  obtain ⟨y, hy, rfl⟩ := hz
  rw [u3h_chartInv_chart hL]; exact hy

/-- At `L = 0` both chart inverses vanish on the chart images. -/
theorem u3h_chartInv_zero (b : Bool) {z : Sphere} (hz : z ∈ modelChart 0 b '' modelDomain 0 b) :
    modelChartInv 0 b z = 0 := by
  obtain ⟨y, hy, rfl⟩ := hz
  cases b
  · have : y = 0 := u3h_supNorm_eq_zero (le_antisymm hy (u3h_supNorm_nonneg y))
    subst this; rfl
  · show modelChartInv 0 true (capChart 0 y) = 0
    unfold capChart
    split_ifs with h
    · rfl
    · show capInvFun 0 (capInvFun 0 y) = 0
      simp [capInvFun]

theorem u3h_face_subset_chartPart {L : ℝ} {b : Bool} {S : Set Sphere}
    (K : Triangulation (chartPart L b S)) {T : Triangle} (hT : T ∈ K.faces) :
    T.carrier ⊆ chartPart L b S := by
  have := subset_biUnion_of_mem (u := fun T : Triangle => T.carrier) hT
  rwa [K.cover] at this


/-- U3: a positive PL sphere map followed by a positive PL map to the plane is positive PL to the
plane. -/
theorem U3_isPositivePLToPlane_comp {L L' : ℝ} {S S' : Set Sphere} {F : Sphere → Sphere}
    {f : Sphere → Plane} (hF : IsPositivePLSphereMap L L' S F) (hFS : F '' S ⊆ S')
    (hf : IsPositivePLToPlane L' S' f) : IsPositivePLToPlane L S (f ∘ F) := by
  intro b
  obtain ⟨Kb, hKb⟩ := hF b
  by_cases hL' : L' = 0
  · refine ⟨Kb, fun T hT => ?_⟩
    exfalso
    obtain ⟨b', hmem, hpos⟩ := hKb T hT
    subst hL'
    have h0 : ∀ i, (modelChartInv 0 b' ∘ F ∘ modelChart L b) (T.v i) = 0 := fun i =>
      u3h_chartInv_zero b' (hmem _ (subset_convexHull ℝ _ ⟨i, rfl⟩))
    have := hpos.2
    rw [h0 0, h0 1, h0 2] at this
    simp [det] at this
  choose b' hmem hpos using hKb
  choose Kf hKf using hf
  have hsubS : ∀ T : ↥Kb.faces, ∀ x ∈ T.1.carrier, modelChart L b x ∈ S := fun T x hx =>
    (u3h_face_subset_chartPart Kb T.2 hx).2
  obtain ⟨K'', _, h2⟩ := u3h_refine_map_into_dep Kb
    (fun T => modelChartInv L' (b' T.1 T.2) ∘ F ∘ modelChart L b)
    (fun T => chartPart L' (b' T.1 T.2) S') (fun T => Kf (b' T.1 T.2)) (fun T => hpos T.1 T.2)
    (by
      rintro T _ ⟨x, hx, rfl⟩
      have hz := hmem T.1 T.2 x hx
      refine ⟨u3h_chartInv_mem hL' _ hz, ?_⟩
      show modelChart L' (b' T.1 T.2) (modelChartInv L' (b' T.1 T.2) (F (modelChart L b x))) ∈ S'
      rw [u3h_chart_chartInv hL' _ hz]
      exact hFS ⟨_, hsubS T x hx, rfl⟩)
  refine ⟨K'', fun T'' hT'' => ?_⟩
  obtain ⟨T, hsub, T', hT', himg⟩ := h2 T'' hT''
  have hφ'' : IsPositiveAffineOn (modelChartInv L' (b' T.1 T.2) ∘ F ∘ modelChart L b) T'' :=
    U1_isPositiveAffineOn_mono (hpos T.1 T.2) hsub
  have hψ : IsPositiveAffineOn (f ∘ modelChart L' (b' T.1 T.2)) (T''.map _ hφ'') :=
    U1_isPositiveAffineOn_mono (hKf (b' T.1 T.2) T' hT')
      (by rw [← u3h_image_carrier T'' hφ'']; exact himg)
  refine u3h_isPositiveAffineOn_congr (fun x hx => ?_) (U1_isPositiveAffineOn_comp hφ'' hψ)
  show f (modelChart L' (b' T.1 T.2) (modelChartInv L' (b' T.1 T.2) (F (modelChart L b x)))) =
    f (F (modelChart L b x))
  rw [u3h_chart_chartInv hL' _ (hmem T.1 T.2 x (hsub hx))]

/-- U3: a positive PL map to the plane followed by a positive PL plane map is positive PL to the
plane. -/
theorem U3_isPositivePLToPlane_comp_plane {L : ℝ} {S : Set Sphere} {D : Set Plane}
    (K : Triangulation D) {f : Sphere → Plane} {g : Plane → Plane} (hf : IsPositivePLToPlane L S f)
    (hfD : f '' S ⊆ D) (hg : IsPositivePLOn g K) : IsPositivePLToPlane L S (g ∘ f) := by
  intro b
  obtain ⟨Kb, hKb⟩ := hf b
  obtain ⟨K'', _, hK''⟩ := U3_isPositivePLOn_comp Kb K hKb hg (u3h_chartPart_image hfD b)
  exact ⟨K'', hK''⟩


/-! ### U3 helpers: the model square, its seam, and inverses of affine maps -/

theorem u3h_norm_eq_supNorm (x : Plane) : ‖x‖ = supNorm x := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; rfl

theorem u3h_interior_square_subset (q : ℝ) : interior (square q) ⊆ {x | supNorm x < q} := by
  intro x hx
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
  obtain ⟨δ, hδ, hball⟩ := hx
  simp only [mem_ofPred_eq]
  by_cases hx0 : x = 0
  · subst hx0
    have hmem : ((δ / 2, 0) : Plane) ∈ square q := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, u3h_norm_eq_supNorm]
      rw [show supNorm ((δ / 2, 0) : Plane) = δ / 2 by
        simp [supNorm, abs_of_pos (half_pos hδ), (half_pos hδ).le]]
      linarith
    have : supNorm ((δ / 2, 0) : Plane) ≤ q := hmem
    have h2 : supNorm ((δ / 2, 0) : Plane) = δ / 2 := by
      simp [supNorm, abs_of_pos (half_pos hδ), (half_pos hδ).le]
    rw [h2] at this
    simp [supNorm]; linarith
  · have hN := u3h_supNorm_pos hx0
    set N := supNorm x with hN'
    have hmem : (1 + δ / (2 * N)) • x ∈ square q := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, u3h_norm_eq_supNorm]
      have : (1 + δ / (2 * N)) • x - x = (δ / (2 * N)) • x := by
        rw [add_smul, one_smul, add_sub_cancel_left]
      rw [this, u3h_supNorm_smul, abs_of_pos (by positivity), ← hN']
      field_simp
      try norm_num
    have : supNorm ((1 + δ / (2 * N)) • x) ≤ q := hmem
    rw [u3h_supNorm_smul, abs_of_pos (by positivity), ← hN'] at this
    have : N + δ / 2 ≤ q := by
      have e : (1 + δ / (2 * N)) * N = N + δ / 2 := by field_simp; try ring
      linarith
    linarith

theorem u3h_face_interior_supNorm_lt {L : ℝ} {b : Bool} {S : Set Sphere}
    (K : Triangulation (chartPart L b S)) {T : Triangle} (hT : T ∈ K.faces) {x : Plane}
    (hx : x ∈ interior T.carrier) : supNorm x < (if b then 1 else L) := by
  have h1 := U2_interior_face_subset_interior K hT hx
  have h2 : chartPart L b S ⊆ square (if b then 1 else L) := by
    intro y hy; cases b <;> exact hy.1
  exact u3h_interior_square_subset _ (interior_mono h2 h1)

theorem u3h_extreme_coord {a b s q t : ℝ} (ha : |a| ≤ q) (hb : |b| ≤ q) (ht0 : 0 < t) (ht1 : t < 1)
    (hs : s = (1 - t) * a + t * b) (hsq : |s| = q) : a = s ∧ b = s := by
  rw [abs_le] at ha hb
  rcases abs_eq (by linarith [abs_nonneg s] : (0 : ℝ) ≤ q) |>.1 hsq with h | h
  · constructor <;> nlinarith
  · constructor <;> nlinarith

theorem u3h_between_neg {a b s t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hs : s = (1 - t) * a + t * b)
    (hab : a ≠ b) : (a - s) * (b - s) < 0 := by
  have e : (a - s) * (b - s) = -(t * (1 - t) * (a - b) ^ 2) := by rw [hs]; ring
  rw [e]
  have : 0 < (a - b) ^ 2 := by
    have : a - b ≠ 0 := sub_ne_zero.2 hab
    positivity
  have : 0 < t * (1 - t) := mul_pos ht0 (by linarith)
  nlinarith

/-- **Claim V**: a point of a face on the boundary of the square, with the face on one side of a
line through it that is transversal to the sides, is a vertex. -/
theorem u3h_seam_vertex {q : ℝ} (T : Triangle) (hT : T.carrier ⊆ square q) {s : Plane}
    (hs : s ∈ T.carrier) (hsq : supNorm s = q) {p : Plane} (hp1 : p.1 ≠ 0) (hp2 : p.2 ≠ 0)
    (hside : (∀ i, planeDot p (T.v i) ≤ planeDot p s) ∨ (∀ i, planeDot p s ≤ planeDot p (T.v i))) :
    s ∈ range T.v := by
  have hnot : s ∉ interior T.carrier := fun h => by
    have := u3h_interior_square_subset q (interior_mono hT h)
    simp only [mem_ofPred_eq] at this; linarith
  have hfr : s ∈ frontier T.carrier := ⟨subset_closure hs, hnot⟩
  rw [U1_frontier_triangle] at hfr
  obtain ⟨i, hi⟩ := mem_iUnion.1 hfr
  obtain ⟨α, β, hα, hβ, hαβ, hsab⟩ := hi
  by_cases hβ0 : β = 0
  · subst hβ0
    have : α = 1 := by linarith
    subst this; exact ⟨i, by simpa using hsab⟩
  by_cases hα0 : α = 0
  · subst hα0
    have : β = 1 := by linarith
    subst this; exact ⟨i + 1, by simpa using hsab⟩
  exfalso
  have ht0 : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
  have ht1 : β < 1 := by
    have : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
    linarith
  have hα' : α = 1 - β := by linarith
  subst hα'
  set a := T.v i with ha
  set b := T.v (i + 1) with hb
  have haQ : a ∈ square q := hT (subset_convexHull ℝ _ ⟨i, rfl⟩)
  have hbQ : b ∈ square q := hT (subset_convexHull ℝ _ ⟨i + 1, rfl⟩)
  have hab : a ≠ b := fun e => u3h_fin3_ne i (u3h_v_injective T e)
  have hs1 : s.1 = (1 - β) * a.1 + β * b.1 := by rw [← hsab]; simp
  have hs2 : s.2 = (1 - β) * a.2 + β * b.2 := by rw [← hsab]; simp
  have haQ' : |a.1| ≤ q ∧ |a.2| ≤ q := ⟨le_trans (le_max_left _ _) haQ, le_trans (le_max_right _ _) haQ⟩
  have hbQ' : |b.1| ≤ q ∧ |b.2| ≤ q := ⟨le_trans (le_max_left _ _) hbQ, le_trans (le_max_right _ _) hbQ⟩
  have hsi : planeDot p a - planeDot p s = p.1 * (a.1 - s.1) + p.2 * (a.2 - s.2) := by
    simp [planeDot]; ring
  have hsj : planeDot p b - planeDot p s = p.1 * (b.1 - s.1) + p.2 * (b.2 - s.2) := by
    simp [planeDot]; ring
  have hopp : (planeDot p a - planeDot p s) * (planeDot p b - planeDot p s) < 0 := by
    rcases max_choice |s.1| |s.2| with h | h
    · have hq1 : |s.1| = q := by rw [← h]; exact hsq
      obtain ⟨e1, e2⟩ := u3h_extreme_coord haQ'.1 hbQ'.1 ht0 ht1 hs1 hq1
      have hne : a.2 ≠ b.2 := fun e => hab (Prod.ext (e1.trans e2.symm) e)
      have := u3h_between_neg ht0 ht1 hs2 hne
      rw [hsi, hsj, e1, e2, sub_self, mul_zero, zero_add, zero_add]
      have hp := mul_self_pos.2 hp2
      nlinarith
    · have hq2 : |s.2| = q := by rw [← h]; exact hsq
      obtain ⟨e1, e2⟩ := u3h_extreme_coord haQ'.2 hbQ'.2 ht0 ht1 hs2 hq2
      have hne : a.1 ≠ b.1 := fun e => hab (Prod.ext e (e1.trans e2.symm))
      have := u3h_between_neg ht0 ht1 hs1 hne
      rw [hsi, hsj, e1, e2, sub_self, mul_zero, add_zero, add_zero]
      have hp := mul_self_pos.2 hp1
      nlinarith
  rcases hside with h | h
  · have h1 := h i; have h2 := h (i + 1)
    rw [← ha] at h1; rw [← hb] at h2
    nlinarith
  · have h1 := h i; have h2 := h (i + 1)
    rw [← ha] at h1; rw [← hb] at h2
    nlinarith

theorem u3h_supNorm_capInvFun {L : ℝ} (hL : 0 < L) {x : Plane} (hx : x ≠ 0) :
    supNorm (capInvFun L x) = L / supNorm x := by
  have hN := u3h_supNorm_pos hx
  rw [capInvFun, u3h_supNorm_smul, u3h_supNorm_swap, abs_of_pos (by positivity)]
  field_simp

theorem u3h_capInvFun_ne_zero {L : ℝ} (hL : 0 < L) {x : Plane} (hx : x ≠ 0) : capInvFun L x ≠ 0 := by
  intro h
  have := u3h_supNorm_capInvFun hL hx
  rw [h] at this
  have hN := u3h_supNorm_pos hx
  have : (0 : ℝ) = L / supNorm x := by simpa [supNorm] using this
  have : 0 < L / supNorm x := by positivity
  linarith

/-- The two charts cover the sphere. -/
theorem u3h_sphere_cover {L : ℝ} (hL : 0 < L) (z : Sphere) :
    ∃ b : Bool, z ∈ modelChart L b '' modelDomain L b := by
  induction z using OnePoint.rec with
  | infty =>
    refine ⟨true, 0, ?_, ?_⟩
    · show supNorm 0 ≤ 1; simp [supNorm]
    · show capChart L 0 = ∞; simp [capChart]
  | coe x =>
    by_cases hx : supNorm x ≤ L
    · exact ⟨false, x, hx, rfl⟩
    · push Not at hx
      have hx0 : x ≠ 0 := by
        rintro rfl; simp [supNorm] at hx; linarith
      refine ⟨true, capInvFun L x, ?_, ?_⟩
      · show supNorm (capInvFun L x) ≤ 1
        rw [u3h_supNorm_capInvFun hL hx0]
        have := u3h_supNorm_pos hx0
        rw [div_le_one this]; exact hx.le
      · show capChart L (capInvFun L x) = (x : Sphere)
        unfold capChart
        rw [if_neg (u3h_capInvFun_ne_zero hL hx0), u3h_capInvFun_capInvFun hL.ne' hx0]

/-- The seam: a point in both chart images. -/
theorem u3h_seam {L : ℝ} (hL : 0 < L) {x y : Plane} (hx : x ∈ square L) (hy1 : y ∈ square 1)
    (h : ((x : Plane) : Sphere) = capChart L y) :
    y ≠ 0 ∧ x = capInvFun L y ∧ supNorm x = L ∧ supNorm y = 1 := by
  unfold capChart at h
  split_ifs at h with hy
  · exact absurd h (by simp)
  · have hxy : x = capInvFun L y := OnePoint.coe_eq_coe.1 h
    have hNy := u3h_supNorm_pos hy
    have hsx : supNorm x = L / supNorm y := by rw [hxy]; exact u3h_supNorm_capInvFun hL hy
    have hxL : supNorm x ≤ L := hx
    have hy1' : supNorm y ≤ 1 := hy1
    have hge : L ≤ L / supNorm y := by
      rw [le_div_iff₀ hNy]; nlinarith
    have hxL' : supNorm x = L := by linarith
    refine ⟨hy, hxy, hxL', ?_⟩
    have : L / supNorm y = L := by linarith
    field_simp at this
    nlinarith

theorem u3h_linear_decomp (M : Plane →ₗ[ℝ] Plane) (u : Plane) :
    M u = u.1 • M ((1 : ℝ), (0 : ℝ)) + u.2 • M ((0 : ℝ), (1 : ℝ)) := by
  conv_lhs => rw [show u = u.1 • ((1 : ℝ), (0 : ℝ)) + u.2 • ((0 : ℝ), (1 : ℝ)) by ext <;> simp]
  rw [map_add, map_smul, map_smul]

theorem u3h_det_map (M : Plane →ₗ[ℝ] Plane) (u w : Plane) :
    det (M u) (M w) = det (M ((1 : ℝ), (0 : ℝ))) (M ((0 : ℝ), (1 : ℝ))) * det u w := by
  rw [u3h_linear_decomp M u, u3h_linear_decomp M w]
  simp [det]; ring

/-- A linear map of the plane with nonzero determinant has a linear left inverse. -/
theorem u3h_exists_linear_inverse (M : Plane →ₗ[ℝ] Plane)
    (hM : det (M ((1 : ℝ), (0 : ℝ))) (M ((0 : ℝ), (1 : ℝ))) ≠ 0) :
    ∃ N : Plane →ₗ[ℝ] Plane, ∀ x, N (M x) = x := by
  set a := (M ((1 : ℝ), (0 : ℝ))).1 with ha
  set c := (M ((1 : ℝ), (0 : ℝ))).2 with hc
  set b := (M ((0 : ℝ), (1 : ℝ))).1 with hb
  set d := (M ((0 : ℝ), (1 : ℝ))).2 with hd
  have hdet : a * d - c * b ≠ 0 := by simpa [det] using hM
  let N : Plane →ₗ[ℝ] Plane :=
    { toFun := fun y => ((d * y.1 - b * y.2) / (a * d - c * b), (-c * y.1 + a * y.2) / (a * d - c * b))
      map_add' := by intro y z; ext <;> simp <;> ring
      map_smul' := by intro r y; ext <;> simp <;> ring }
  refine ⟨N, fun x => ?_⟩
  have hx : M x = (a * x.1 + b * x.2, c * x.1 + d * x.2) := by
    rw [u3h_linear_decomp M x]; ext <;> simp [ha, hb, hc, hd] <;> ring
  ext
  · simp only [N, hx, LinearMap.coe_mk, AddHom.coe_mk]
    rw [div_eq_iff hdet]; ring
  · simp only [N, hx, LinearMap.coe_mk, AddHom.coe_mk]
    rw [div_eq_iff hdet]; ring

/-- The inverse of a positive affine map on a face is affine on the image face. -/
theorem u3h_affine_inverse (T : Triangle) {f : Plane → Plane} (h : IsPositiveAffineOn f T)
    {g : Plane → Plane} (hg : ∀ x ∈ T.carrier, g (f x) = x) :
    IsPositiveAffineOn g (T.map f h) := by
  obtain ⟨⟨M, b, hMb⟩, hpos⟩ := id h
  have hv : ∀ i, (T.map f h).v i = f (T.v i) := fun i => rfl
  have hdetM : det (M ((1 : ℝ), (0 : ℝ))) (M ((0 : ℝ), (1 : ℝ))) ≠ 0 := by
    intro h0
    have e : f (T.v 1) - f (T.v 0) = M (T.v 1 - T.v 0) := by
      rw [hMb _ (subset_convexHull ℝ _ ⟨1, rfl⟩), hMb _ (subset_convexHull ℝ _ ⟨0, rfl⟩), map_sub]
      abel
    have e' : f (T.v 2) - f (T.v 0) = M (T.v 2 - T.v 0) := by
      rw [hMb _ (subset_convexHull ℝ _ ⟨2, rfl⟩), hMb _ (subset_convexHull ℝ _ ⟨0, rfl⟩), map_sub]
      abel
    rw [e, e', u3h_det_map, h0, zero_mul] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨N, hN⟩ := u3h_exists_linear_inverse M hdetM
  refine ⟨⟨N, -N b, ?_⟩, ?_⟩
  · intro y hy
    rw [← u3h_image_carrier T h] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hg x hx, hMb x hx, map_add, hN]; abel
  · simp only [hv]
    rw [hg _ (subset_convexHull ℝ _ ⟨0, rfl⟩), hg _ (subset_convexHull ℝ _ ⟨1, rfl⟩),
      hg _ (subset_convexHull ℝ _ ⟨2, rfl⟩)]
    exact T.pos

theorem u3h_continuous_planeDot (p : Plane) : Continuous (planeDot p) := by
  unfold planeDot; fun_prop

theorem u3h_mem_interior_iff (Δ : Triangle) (y : Plane) :
    y ∈ interior Δ.carrier ↔ ∀ l, u3h_edgeC Δ l < planeDot (u3h_edgeN Δ l) y := by
  constructor
  · intro hy l
    exact u3h_interior_strict Δ (interior_subset hy)
      (fun h => (Set.disjoint_left.1 disjoint_interior_frontier) hy h) l
  · intro h
    have hopen : IsOpen {y : Plane | ∀ l, u3h_edgeC Δ l < planeDot (u3h_edgeN Δ l) y} := by
      have : {y : Plane | ∀ l, u3h_edgeC Δ l < planeDot (u3h_edgeN Δ l) y} =
          ⋂ l, {y | u3h_edgeC Δ l < planeDot (u3h_edgeN Δ l) y} := by ext; simp
      rw [this]
      exact isOpen_iInter_of_finite fun l => isOpen_lt continuous_const (u3h_continuous_planeDot _)
    exact interior_maximal (fun y hy => (u3h_mem_iff_edges Δ y).2 fun l => (hy l).le) hopen h

theorem u3h_detM_pos (T : Triangle) {φ : Plane → Plane} (h : IsPositiveAffineOn φ T)
    {M : Plane →ₗ[ℝ] Plane} {c : Plane} (hMc : ∀ x ∈ T.carrier, φ x = M x + c) :
    0 < det (M ((1 : ℝ), (0 : ℝ))) (M ((0 : ℝ), (1 : ℝ))) := by
  have hpos := h.2
  have e : ∀ i, φ (T.v i) - φ (T.v 0) = M (T.v i - T.v 0) := fun i => by
    rw [hMc _ (subset_convexHull ℝ _ ⟨i, rfl⟩), hMc _ (subset_convexHull ℝ _ ⟨0, rfl⟩), map_sub]
    abel
  rw [e 1, e 2, u3h_det_map] at hpos
  by_contra hn; push Not at hn
  nlinarith [T.pos, mul_nonpos_of_nonpos_of_nonneg hn T.pos.le]

/-- An affine map on a face carries interior points to interior points of the image, and only them. -/
theorem u3h_interior_map (T : Triangle) {φ : Plane → Plane} (h : IsPositiveAffineOn φ T) {t : Plane}
    (ht : t ∈ T.carrier) : φ t ∈ interior (T.map φ h).carrier ↔ t ∈ interior T.carrier := by
  obtain ⟨M, c, hMc⟩ := id h.1
  have hv : ∀ i, (T.map φ h).v i = φ (T.v i) := fun i => rfl
  have hdetM := u3h_detM_pos T h hMc
  have key : ∀ l, planeDot (u3h_edgeN (T.map φ h) l) (φ t) - u3h_edgeC (T.map φ h) l =
      det (M ((1 : ℝ), (0 : ℝ))) (M ((0 : ℝ), (1 : ℝ))) *
        (planeDot (u3h_edgeN T l) t - u3h_edgeC T l) := by
    intro l
    rw [u3h_edge_eval, u3h_edge_eval, hv, hv]
    have hvl : ∀ k, T.v k ∈ T.carrier := fun k => subset_convexHull ℝ (range T.v) (mem_range_self k)
    have e1 : φ (T.v (l + 1)) - φ (T.v l) = M (T.v (l + 1) - T.v l) := by
      rw [hMc _ (hvl (l + 1)), hMc _ (hvl l), map_sub]
      abel
    have e2 : φ t - φ (T.v l) = M (t - T.v l) := by
      rw [hMc _ ht, hMc _ (hvl l), map_sub]; abel
    rw [e1, e2, u3h_det_map]
  rw [u3h_mem_interior_iff, u3h_mem_interior_iff]
  constructor
  · intro H l
    have k := key l
    have := H l
    by_contra hn; push Not at hn
    have := mul_nonpos_of_nonneg_of_nonpos hdetM.le (sub_nonpos.2 hn)
    linarith
  · intro H l
    have k := key l
    have := mul_pos hdetM (sub_pos.2 (H l))
    linarith

theorem u3h_triangulation_vertex {X : Set Plane} (K : Triangulation X) {T T' : Triangle}
    (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) (j : Fin 3) (h : T'.v j ∈ T.carrier) :
    T'.v j ∈ range T.v := by
  have hmem : T'.v j ∈ convexHull ℝ (range T.v ∩ range T'.v) := by
    rw [← K.inter T hT T' hT']; exact ⟨h, subset_convexHull ℝ _ ⟨j, rfl⟩⟩
  exact (u3h_v_mem_convexHull T' inter_subset_right j hmem).1

theorem u3h_interior_disjoint_or {X : Set Plane} (K : Triangulation X) {T T' : Triangle}
    (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) (hne : T.carrier ≠ T'.carrier) :
    Disjoint (interior T.carrier) T'.carrier ∨ Disjoint (interior T'.carrier) T.carrier := by
  by_cases h : ∃ i, T.v i ∉ range T'.v
  · obtain ⟨i, hi⟩ := h; exact Or.inl (u3h_interior_disjoint_of_vertex K hT hT' i hi)
  · push Not at h
    have h' : ∃ i, T'.v i ∉ range T.v := by
      by_contra h'; push Not at h'
      apply hne
      have : range T.v = range T'.v := Subset.antisymm (by rintro _ ⟨i, rfl⟩; exact h i)
        (by rintro _ ⟨i, rfl⟩; exact h' i)
      unfold Triangle.carrier; rw [this]
    obtain ⟨i, hi⟩ := h'
    exact Or.inr (u3h_interior_disjoint_of_vertex K hT' hT i hi)

theorem u3h_sep_of_disj (Δ Δ' : Triangle) (h : Disjoint (interior Δ.carrier) Δ'.carrier) :
    ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧ (∀ i, planeDot p (Δ.v i) ≤ r) ∧ ∀ i, r ≤ planeDot p (Δ'.v i) := by
  obtain ⟨p, r, hp, h1, h2⟩ := u3h_separate_of_disjoint (convex_convexHull ℝ _)
    (U1_triangle_isCompact Δ) (U1_triangle_interior_nonempty Δ) (convex_convexHull ℝ _)
    ⟨Δ'.v 0, subset_convexHull ℝ (range Δ'.v) (mem_range_self 0)⟩ h
  exact ⟨p, r, hp, fun j => h1 _ (subset_convexHull ℝ _ ⟨j, rfl⟩),
    fun j => h2 _ (subset_convexHull ℝ _ ⟨j, rfl⟩)⟩

theorem u3h_sep_of_disj_or (Δ Δ' : Triangle)
    (h : Disjoint (interior Δ.carrier) Δ'.carrier ∨ Disjoint (interior Δ'.carrier) Δ.carrier) :
    ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧ (∀ i, planeDot p (Δ.v i) ≤ r) ∧ ∀ i, r ≤ planeDot p (Δ'.v i) := by
  rcases h with h | h
  · exact u3h_sep_of_disj Δ Δ' h
  · obtain ⟨p, r, hp, h1, h2⟩ := u3h_sep_of_disj Δ' Δ h
    refine ⟨-p, -r, neg_ne_zero.2 hp, fun i => ?_, fun i => ?_⟩
    · rw [u3h_planeDot_neg_left]; linarith [h2 i]
    · rw [u3h_planeDot_neg_left]; linarith [h1 i]

theorem u3h_capInvFun_seam {L : ℝ} {y : Plane} (hy : supNorm y = 1) :
    capInvFun L y = L • (y.1, -y.2) := by
  simp [capInvFun, hy]

theorem u3h_planeDot_11 (x : Plane) : planeDot ((1 : ℝ), (1 : ℝ)) x = x.1 + x.2 := by
  simp [planeDot]

theorem u3h_planeDot_1m1 (x : Plane) : planeDot ((1 : ℝ), (-1 : ℝ)) x = x.1 - x.2 := by
  simp [planeDot]; ring

/-- **Corrected inverse leaf** (rule 3): `U3_isPositivePLFromPlane_inv` with the hypothesis `0 < L`
added.  The leaf as stated is false at `L ≤ 0` (see the report). -/
theorem u3h_isPositivePLFromPlane_inv {L : ℝ} (hL : 0 < L) {S : Set Sphere} {D : Set Plane}
    {f : Sphere → Plane} (_hD : Link.IsDisc D) (hf : IsHomeoOnto S D f)
    (hpl : IsPositivePLToPlane L S f) :
    ∃ g : Plane → Sphere, IsPositivePLFromPlane L D g ∧ (∀ z ∈ S, g (f z) = z) ∧
      ∀ x ∈ D, f (g x) = x := by
  classical
  obtain ⟨e, he⟩ := hf
  let g : Plane → Sphere := fun x => if h : x ∈ D then ((e.symm ⟨x, h⟩ : S) : Sphere) else ∞
  have hfD : ∀ z ∈ S, f z ∈ D := fun z hz => by rw [← he ⟨z, hz⟩]; exact (e ⟨z, hz⟩).2
  have hgf : ∀ z ∈ S, g (f z) = z := by
    intro z hz
    simp only [g, dif_pos (hfD z hz)]
    have : (⟨f z, hfD z hz⟩ : D) = e ⟨z, hz⟩ := Subtype.ext (he ⟨z, hz⟩).symm
    rw [this, Homeomorph.symm_apply_apply]
  have hgS : ∀ x ∈ D, g x ∈ S := fun x hx => by
    simp only [g, dif_pos hx]; exact (e.symm ⟨x, hx⟩).2
  have hfg : ∀ x ∈ D, f (g x) = x := by
    intro x hx
    simp only [g, dif_pos hx]
    rw [← he, Homeomorph.apply_symm_apply]
  have hinj : ∀ z ∈ S, ∀ z' ∈ S, f z = f z' → z = z' := fun z hz z' hz' h => by
    rw [← hgf z hz, ← hgf z' hz', h]
  refine ⟨g, ?_, hgf, hfg⟩
  choose K hK using hpl
  -- the set of "sums" of all vertices (false chart: x₁ + x₂; true chart: L (y₁ - y₂))
  let V : Set ℝ := (⋃ T ∈ (K false).faces, range (fun i => (T.v i).1 + (T.v i).2)) ∪
    (⋃ T ∈ (K true).faces, range (fun i => L * ((T.v i).1 - (T.v i).2)))
  have hVfin : V.Finite :=
    ((K false).finite.biUnion fun T _ => finite_range _).union
      ((K true).finite.biUnion fun T _ => finite_range _)
  haveI : Finite ↥V := hVfin.to_subtype
  obtain ⟨Kf, hKf1, hKf2, hKf3⟩ := u3h_refine_along_lines_finite (K false)
    (fun _ : ↥V => ((1 : ℝ), (1 : ℝ))) (fun c => c.1)
  obtain ⟨Kt, hKt1, hKt2, hKt3⟩ := u3h_refine_along_lines_finite (K true)
    (fun _ : ↥V => ((1 : ℝ), (-1 : ℝ))) (fun c => c.1 / L)
  have hPLf : IsPositivePLOn (f ∘ modelChart L false) Kf :=
    U2_isPositivePLOn_of_refines (hK false) hKf1
  have hPLt : IsPositivePLOn (f ∘ modelChart L true) Kt :=
    U2_isPositivePLOn_of_refines (hK true) hKt1
  have hVf : ∀ T ∈ Kf.faces, ∀ i, (T.v i).1 + (T.v i).2 ∈ V := by
    intro T hT i
    rcases hKf3 T hT i with ⟨T₀, hT₀, ⟨k, hk⟩⟩ | ⟨c, hc⟩
    · left; exact mem_iUnion₂.2 ⟨T₀, hT₀, k, by show (T₀.v k).1 + (T₀.v k).2 = _; rw [hk]⟩
    · rw [u3h_planeDot_11] at hc; rw [hc]; exact c.2
  have hVt : ∀ T ∈ Kt.faces, ∀ i, L * ((T.v i).1 - (T.v i).2) ∈ V := by
    intro T hT i
    rcases hKt3 T hT i with ⟨T₀, hT₀, ⟨k, hk⟩⟩ | ⟨c, hc⟩
    · right; exact mem_iUnion₂.2 ⟨T₀, hT₀, k, by show L * ((T₀.v k).1 - (T₀.v k).2) = _; rw [hk]⟩
    · rw [u3h_planeDot_1m1] at hc; rw [hc, mul_div_cancel₀ _ hL.ne']; exact c.2
  have hsidef : ∀ T ∈ Kf.faces, ∀ c ∈ V, (∀ i, planeDot ((1 : ℝ), (1 : ℝ)) (T.v i) ≤ c) ∨
      (∀ i, c ≤ planeDot ((1 : ℝ), (1 : ℝ)) (T.v i)) := by
    intro T hT c hc
    rcases hKf2 T hT ⟨c, hc⟩ with h | h
    · left; intro i; exact h (subset_convexHull ℝ _ ⟨i, rfl⟩)
    · right; intro i; exact h (subset_convexHull ℝ _ ⟨i, rfl⟩)
  have hsidet : ∀ T ∈ Kt.faces, ∀ c ∈ V, (∀ i, planeDot ((1 : ℝ), (-1 : ℝ)) (T.v i) ≤ c / L) ∨
      (∀ i, c / L ≤ planeDot ((1 : ℝ), (-1 : ℝ)) (T.v i)) := by
    intro T hT c hc
    rcases hKt2 T hT ⟨c, hc⟩ with h | h
    · left; intro i; exact h (subset_convexHull ℝ _ ⟨i, rfl⟩)
    · right; intro i; exact h (subset_convexHull ℝ _ ⟨i, rfl⟩)
  -- the two refined chart triangulations, indexed by the chart
  let K' : ∀ b : Bool, Triangulation (chartPart L b S) := fun b =>
    Bool.casesOn (motive := fun b => Triangulation (chartPart L b S)) b Kf Kt
  have hK' : ∀ b, IsPositivePLOn (f ∘ modelChart L b) (K' b) := fun b => by
    cases b
    · exact hPLf
    · exact hPLt
  haveI : ∀ b, Finite ↥(K' b).faces := fun b => (K' b).finite.to_subtype
  let F : Set Triangle := ⋃ b : Bool,
    range (fun T : ↥(K' b).faces => T.1.map (f ∘ modelChart L b) (hK' b T.1 T.2))
  have hFmem : ∀ Δ, Δ ∈ F ↔ ∃ b, ∃ T : ↥(K' b).faces,
      T.1.map (f ∘ modelChart L b) (hK' b T.1 T.2) = Δ := by
    intro Δ; simp only [F, mem_iUnion, mem_range]
  have hFfin : F.Finite := finite_iUnion fun b => finite_range _
  have hcar : ∀ b (T : ↥(K' b).faces),
      (T.1.map (f ∘ modelChart L b) (hK' b T.1 T.2)).carrier = (f ∘ modelChart L b) '' T.1.carrier :=
    fun b T => (u3h_image_carrier T.1 (hK' b T.1 T.2)).symm
  have hsubC : ∀ b (T : ↥(K' b).faces), T.1.carrier ⊆ chartPart L b S :=
    fun b T => u3h_face_subset_chartPart (K' b) T.2
  have hchartS : ∀ b (T : ↥(K' b).faces), ∀ t ∈ T.1.carrier, modelChart L b t ∈ S :=
    fun b T t ht => (hsubC b T ht).2
  have hchartinj : ∀ b (t t' : Plane), modelChart L b t = modelChart L b t' → t = t' := by
    intro b t t' h
    rw [← u3h_chartInv_chart hL.ne' b t, h, u3h_chartInv_chart hL.ne']
  -- a point of the interior of one image face lying in another: chart coordinates agree
  have hmeet : ∀ (b b' : Bool) (T : ↥(K' b).faces) (T' : ↥(K' b').faces) (y : Plane),
      y ∈ interior (T.1.map (f ∘ modelChart L b) (hK' b T.1 T.2)).carrier →
      y ∈ (T'.1.map (f ∘ modelChart L b') (hK' b' T'.1 T'.2)).carrier →
      ∃ t ∈ interior T.1.carrier, ∃ t' ∈ T'.1.carrier, modelChart L b t = modelChart L b' t' := by
    intro b b' T T' y hy hy'
    have hy0 := interior_subset hy
    rw [hcar] at hy0 hy'
    obtain ⟨t, ht, rfl⟩ := hy0
    obtain ⟨t', ht', hft'⟩ := hy'
    refine ⟨t, (u3h_interior_map T.1 (hK' b T.1 T.2) ht).1 hy, t', ht', ?_⟩
    exact hinj _ (hchartS b T t ht) _ (hchartS b' T' t' ht') hft'.symm
  have hcover : (⋃ Δ ∈ F, Δ.carrier) = D := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨Δ, hΔ, hxΔ⟩ := mem_iUnion₂.1 hx
      obtain ⟨b, T, rfl⟩ := (hFmem Δ).1 hΔ
      rw [hcar] at hxΔ
      obtain ⟨t, ht, rfl⟩ := hxΔ
      exact hfD _ (hchartS b T t ht)
    · intro x hx
      obtain ⟨b, y, hy, hyz⟩ := u3h_sphere_cover hL (g x)
      have hyS : y ∈ chartPart L b S := ⟨hy, by show modelChart L b y ∈ S; rw [hyz]; exact hgS x hx⟩
      rw [← (K' b).cover] at hyS
      obtain ⟨T, hT, hyT⟩ := mem_iUnion₂.1 hyS
      refine mem_iUnion₂.2 ⟨_, (hFmem _).2 ⟨b, ⟨T, hT⟩, rfl⟩, ?_⟩
      rw [hcar b ⟨T, hT⟩]
      refine ⟨y, hyT, ?_⟩
      show f (modelChart L b y) = x
      rw [hyz, hfg x hx]
  have hsupf : ∀ (T : ↥(K' false).faces) {t : Plane}, t ∈ interior T.1.carrier → supNorm t < L :=
    fun T t ht => by simpa using u3h_face_interior_supNorm_lt (K' false) T.2 ht
  have hsupt : ∀ (T : ↥(K' true).faces) {t : Plane}, t ∈ interior T.1.carrier → supNorm t < 1 :=
    fun T t ht => by simpa using u3h_face_interior_supNorm_lt (K' true) T.2 ht
  have hsqf : ∀ (T : ↥(K' false).faces), T.1.carrier ⊆ square L := fun T t ht => (hsubC false T ht).1
  have hsqt : ∀ (T : ↥(K' true).faces), T.1.carrier ⊆ square 1 := fun T t ht => (hsubC true T ht).1
  -- separation of distinct image faces
  have hsep : ∀ Δ ∈ F, ∀ Δ' ∈ F, Δ.carrier ≠ Δ'.carrier → ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧
      (∀ i, planeDot p (Δ.v i) ≤ r) ∧ ∀ i, r ≤ planeDot p (Δ'.v i) := by
    intro Δ hΔ Δ' hΔ' hne
    obtain ⟨b, T, rfl⟩ := (hFmem Δ).1 hΔ
    obtain ⟨b', T', rfl⟩ := (hFmem Δ').1 hΔ'
    apply u3h_sep_of_disj_or
    by_cases hb : b = b'
    · subst hb
      have hne' : T.1.carrier ≠ T'.1.carrier := by
        intro h; apply hne; rw [hcar, hcar, h]
      rcases u3h_interior_disjoint_or (K' b) T.2 T'.2 hne' with h | h
      · left
        rw [Set.disjoint_left]
        intro y hy hy'
        obtain ⟨t, ht, t', ht', hc⟩ := hmeet b b T T' y hy hy'
        have := hchartinj b t t' hc
        subst this
        exact (Set.disjoint_left.1 h) ht ht'
      · right
        rw [Set.disjoint_left]
        intro y hy hy'
        obtain ⟨t, ht, t', ht', hc⟩ := hmeet b b T' T y hy hy'
        have := hchartinj b t t' hc
        subst this
        exact (Set.disjoint_left.1 h) ht ht'
    · left
      rw [Set.disjoint_left]
      intro y hy hy'
      obtain ⟨t, ht, t', ht', hc⟩ := hmeet b b' T T' y hy hy'
      cases b <;> cases b'
      · exact hb rfl
      · have hs := u3h_seam hL (hsqf T (interior_subset ht)) (hsqt T' ht') hc
        have := hsupf T ht
        linarith [hs.2.2.1]
      · have hs := u3h_seam hL (hsqf T' ht') (hsqt T (interior_subset ht)) hc.symm
        have := hsupt T ht
        linarith [hs.2.2.2]
      · exact hb rfl
  -- vertices of one image face lying in another are vertices of it
  have hvert : ∀ Δ ∈ F, ∀ Δ' ∈ F, ∀ j, Δ'.v j ∈ Δ.carrier → Δ'.v j ∈ range Δ.v := by
    intro Δ hΔ Δ' hΔ' j hj
    obtain ⟨b, T, rfl⟩ := (hFmem Δ).1 hΔ
    obtain ⟨b', T', rfl⟩ := (hFmem Δ').1 hΔ'
    rw [hcar] at hj
    obtain ⟨t, ht, hft⟩ := hj
    have hc : modelChart L b t = modelChart L b' (T'.1.v j) :=
      hinj _ (hchartS b T t ht) _ (hchartS b' T' _ (subset_convexHull ℝ _ ⟨j, rfl⟩)) hft
    suffices hrange : t ∈ range T.1.v by
      obtain ⟨i, rfl⟩ := hrange
      exact ⟨i, hft⟩
    cases b <;> cases b'
    · have := hchartinj false _ _ hc
      rw [this]
      exact u3h_triangulation_vertex (K' false) T.2 T'.2 j (this ▸ ht)
    · -- false / true: `t` is the seam image of the vertex `T'.v j`
      set y := T'.1.v j with hy
      have hyQ : y ∈ square 1 := hsqt T' (subset_convexHull ℝ _ ⟨j, rfl⟩)
      obtain ⟨_, hty, htL, hy1⟩ := u3h_seam hL (hsqf T ht) hyQ hc
      have ht' : t = L • (y.1, -y.2) := by rw [hty, u3h_capInvFun_seam hy1]
      have hsum : t.1 + t.2 = L * (y.1 - y.2) := by rw [ht']; simp; ring
      have hcV : t.1 + t.2 ∈ V := by rw [hsum]; exact hVt T'.1 T'.2 j
      refine u3h_seam_vertex T.1 (hsqf T) ht htL (p := ((1 : ℝ), (1 : ℝ))) one_ne_zero one_ne_zero ?_
      rw [u3h_planeDot_11]
      exact hsidef T.1 T.2 _ hcV
    · -- true / false
      set x := T'.1.v j with hx
      have hxQ : x ∈ square L := hsqf T' (subset_convexHull ℝ _ ⟨j, rfl⟩)
      obtain ⟨_, hxt, hxL, ht1⟩ := u3h_seam hL hxQ (hsqt T ht) hc.symm
      have hx' : x = L • (t.1, -t.2) := by rw [hxt, u3h_capInvFun_seam ht1]
      have hsum : x.1 + x.2 = L * (t.1 - t.2) := by rw [hx']; simp; ring
      have hcV : x.1 + x.2 ∈ V := hVf T'.1 T'.2 j
      refine u3h_seam_vertex T.1 (hsqt T) ht ht1 (p := ((1 : ℝ), (-1 : ℝ))) one_ne_zero
        (by norm_num) ?_
      rw [u3h_planeDot_1m1]
      have := hsidet T.1 T.2 _ hcV
      rw [hsum, mul_div_cancel_left₀ _ hL.ne'] at this
      exact this
    · have := hchartinj true _ _ hc
      rw [this]
      exact u3h_triangulation_vertex (K' true) T.2 T'.2 j (this ▸ ht)
  refine ⟨⟨F, hFfin, hcover, u3h_inter_of_family hsep hvert⟩, ?_⟩
  intro Δ hΔ
  obtain ⟨b, T, rfl⟩ := (hFmem Δ).1 hΔ
  refine ⟨b, ?_, ?_⟩
  · intro x hx
    rw [hcar] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    show g (f (modelChart L b t)) ∈ _
    rw [hgf _ (hchartS b T t ht)]
    exact ⟨t, (hsubC b T ht).1, rfl⟩
  · refine u3h_affine_inverse T.1 (hK' b T.1 T.2) (fun t ht => ?_)
    show modelChartInv L b (g (f (modelChart L b t))) = t
    rw [hgf _ (hchartS b T t ht), u3h_chartInv_chart hL.ne']

/-- U3 (inverse chart bookkeeping): the inverse of a positive PL parametrisation `f : S → D` (a
homeomorphism, positive PL in charts) is positive PL from the plane. -/
theorem U3_isPositivePLFromPlane_inv {L : ℝ} {S : Set Sphere} {D : Set Plane} {f : Sphere → Plane}
    (hD : Link.IsDisc D) (hf : IsHomeoOnto S D f) (hpl : IsPositivePLToPlane L S f) :
    ∃ g : Plane → Sphere, IsPositivePLFromPlane L D g ∧ (∀ z ∈ S, g (f z) = z) ∧
      ∀ x ∈ D, f (g x) = x := by
  sorry

/-! ### U4 (lane B) — ear triangulation of an embedded polygon (Meisters) -/

/-- U4: the ear triangle at vertex `j` (vertices `P (j-1), P j, P (j+1)`). -/
def earHull (P : LabelledTuple n) (j : ZMod n) : Set Plane :=
  convexHull ℝ {P (j - 1), P j, P (j + 1)}

/-- U4: the polygon image is compact. -/
theorem U4_polygonImage_isCompact [NeZero n] (P : LabelledTuple n) : IsCompact (polygonImage P) := by
  sorry

/-- U4: the traversal image is the polygon image. -/
theorem U4_range_traversal [NeZero n] (P : LabelledTuple n) : range (traversal P) = polygonImage P := by
  sorry

/-- U4 (sm-3:439 "inside a large rectangle"): some model square contains the polygon. -/
theorem U4_exists_insideModel [NeZero n] (P : LabelledTuple n) : ∃ L : ℝ, 0 < L ∧ InsideModel L P := by
  sorry

/-- U4: `InsideModel L P` puts the polygon image strictly inside `Q_L`. -/
theorem U4_polygonImage_subset_interior_square [NeZero n] {L : ℝ} (P : LabelledTuple n)
    (hL : InsideModel L P) : polygonImage P ⊆ interior (square L) ∧ 0 < L := by
  sorry

/-- U4: an embedded polygon has at least three vertices. -/
theorem U4_three_le_of_embedded [NeZero n] (P : LabelledTuple n) (hP : Embedded P) : 3 ≤ n := by
  sorry

/-- U4 (base case): an embedded triangle bounds its convex hull. -/
theorem U4_triangle_base (P : LabelledTuple 3) (hP : Embedded P) :
    det (P 1 - P 0) (P 2 - P 0) ≠ 0 ∧ polygonImage P = frontier (earHull P 1) := by
  sorry

/-- U4 (Meisters' two ears, sm-3:437-439 spirit): an embedded polygon with at least four vertices has
an ear: a vertex `j` with nonzero turn whose ear triangle meets the rest of the polygon exactly in
the diagonal, and whose deletion is again embedded. -/
theorem U4_exists_ear [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple (n + 1)) (hP : Embedded P) :
    ∃ j : ZMod (n + 1), Embedded (deleteVertex P j) ∧
      det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0 ∧
      earHull P j ∩ polygonImage (deleteVertex P j) = segment ℝ (P (j - 1)) (P (j + 1)) := by
  sorry

/-- U4 (ear-cut identity): the polygon image of `P` is that of the cut polygon with the diagonal
replaced by the two ear edges. -/
theorem U4_polygonImage_ear [NeZero n] (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) :
    polygonImage P = (polygonImage (deleteVertex P j) \ openSegment ℝ (P (j - 1)) (P (j + 1))) ∪
      segment ℝ (P (j - 1)) (P j) ∪ segment ℝ (P j) (P (j + 1)) := by
  sorry

/-- U4 (output, sm-3:437-443 "triangulate ... the polygon"): an embedded polygon bounds a compact
set `U` with a triangulation in which every edge of `P` is an edge of exactly one face, `frontier U`
is the circle, and `U` lies strictly inside every model square containing `P`. -/
theorem U4_exists_triangulation [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    ∃ (U : Set Plane) (K : Triangulation U), frontier U = polygonImage P ∧
      (∀ i, ∃ T ∈ K.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment P i) ∧
      (∀ i, ∀ T ∈ K.faces, ∀ T' ∈ K.faces, edgeSegment P i ⊆ T.carrier →
        edgeSegment P i ⊆ T'.carrier → T.carrier = T'.carrier) ∧
      ∀ L, InsideModel L P → U ⊆ interior (square L) := by
  sorry

/-! ### U5 (sequential) — the ear-cut ambient homeomorphism -/

/-- U5 (sm-3:437-443 realised ambiently, PLAN_FINAL §3.1): cutting an ear `j` of `P` is realised by
a positive PL homeomorphism `h` of the plane, the identity outside a compact subset of `int Q_L`,
carrying the region `U'` bounded by the cut polygon onto `U' ∪ ear` and the cut circle onto the
circle of `P`. -/
theorem U5_exists_ear_homeo [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple (n + 1)) (hP : Embedded P)
    (j : ZMod (n + 1)) (hP' : Embedded (deleteVertex P j))
    (hturn : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0)
    (hear : earHull P j ∩ polygonImage (deleteVertex P j) = segment ℝ (P (j - 1)) (P (j + 1)))
    (U' : Set Plane) (K' : Triangulation U') (hU' : frontier U' = polygonImage (deleteVertex P j))
    (hedge : ∀ T ∈ K'.faces, ∀ T' ∈ K'.faces, segment ℝ (P (j - 1)) (P (j + 1)) ⊆ T.carrier →
      segment ℝ (P (j - 1)) (P (j + 1)) ⊆ T'.carrier → T.carrier = T'.carrier)
    (hface : ∃ T ∈ K'.faces, ∃ k : Fin 3, T.edgeSeg k = segment ℝ (P (j - 1)) (P (j + 1)))
    {L : ℝ} (hL : InsideModel L P) (hU'L : U' ⊆ interior (square L)) :
    ∃ (h : Plane ≃ₜ Plane) (Kh : Triangulation (square L)) (Kin : Triangulation U'),
      IsPositivePLOn h Kh ∧ IsPositivePLOn h Kin ∧ Kin.Refines K' ∧
      (∀ x, L ≤ supNorm x → h x = x) ∧
      h '' U' = U' ∪ earHull P j ∧ h '' polygonImage (deleteVertex P j) = polygonImage P ∧
      frontier (U' ∪ earHull P j) = polygonImage P ∧ U' ∪ earHull P j ⊆ interior (square L) := by
  sorry

/-- U5: the ear-cut homeomorphism sends the faces of the refined triangulation `Kin` of `U'` to a
triangulation of `U' ∪ ear` in which every edge of `P` is an edge of exactly one face. -/
theorem U5_pushforward_edges [NeZero n] (P : LabelledTuple (n + 1)) (j : ZMod (n + 1))
    (U' : Set Plane) (Kin : Triangulation U') (h : Plane ≃ₜ Plane) (hh : IsPositivePLOn h Kin)
    (hU : h '' U' = U' ∪ earHull P j) (hC : h '' polygonImage (deleteVertex P j) = polygonImage P)
    (hedge' : ∀ i, ∃ T ∈ Kin.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment (deleteVertex P j) i)
    (huniq' : ∀ i, ∀ T ∈ Kin.faces, ∀ T' ∈ Kin.faces, edgeSegment (deleteVertex P j) i ⊆ T.carrier →
      edgeSegment (deleteVertex P j) i ⊆ T'.carrier → T.carrier = T'.carrier) :
    ∃ K : Triangulation (U' ∪ earHull P j),
      (∀ i, ∃ T ∈ K.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment P i) ∧
      ∀ i, ∀ T ∈ K.faces, ∀ T' ∈ K.faces, edgeSegment P i ⊆ T.carrier →
        edgeSegment P i ⊆ T'.carrier → T.carrier = T'.carrier := by
  sorry

/-! ### U6 (sequential) — 57a and 57e via the ambient parametrisation -/

/-- The ambient parametrisation of the bounded region (PLAN_FINAL §3.1): a base triangle `T₀` inside
`int Q_L` and a positive PL homeomorphism `H` of the plane (`H = h_m ∘ ⋯ ∘ h_1`), the identity
outside `int Q_L`, PL on a triangulation of `Q_L` and on one of `T₀`, with `H (∂T₀) = C`. -/
structure AmbientParam [NeZero n] (P : LabelledTuple n) (L : ℝ) where
  /-- the base triangle (the last 3-gon of the ear sequence) -/
  T₀ : Triangle
  /-- the composite ear-cut homeomorphism -/
  H : Plane ≃ₜ Plane
  /-- a triangulation of the model square on which `H` is positive PL -/
  K : Triangulation (square L)
  /-- a triangulation of the base triangle on which `H` is positive PL -/
  KT : Triangulation T₀.carrier
  pl : IsPositivePLOn H K
  plT : IsPositivePLOn H KT
  /-- `H` is the identity outside `int Q_L` -/
  fix : ∀ x, L ≤ supNorm x → H x = x
  inside : T₀.carrier ⊆ interior (square L)
  /-- `H (∂T₀) = C` -/
  boundary : H '' frontier T₀.carrier = polygonImage P

/-- U6 (sm-3:437-443, the ear induction assembled): every embedded polygon inside `Q_L` has an
ambient parametrisation. -/
theorem U6_exists_ambientParam [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) : Nonempty (AmbientParam P L) := by
  sorry

/-- U6: the complement of the frontier of a triangle has exactly the two components `int T₀`, `T₀ᶜ`. -/
theorem U6_compl_frontier_triangle (T : Triangle) :
    (frontier T.carrier)ᶜ = interior T.carrier ∪ (T.carrier)ᶜ ∧
      IsConnected (interior T.carrier) ∧ IsConnected (T.carrier)ᶜ ∧
      Disjoint (interior T.carrier) (T.carrier)ᶜ := by
  sorry

/-- U6 (sm-3:486-489 "the region of the point at infinity"): the exterior region is the image of
the complement of the base triangle together with `∞`. -/
theorem U6_exteriorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) {L : ℝ}
    (A : AmbientParam P L) :
    exteriorRegion P = ((↑) : Plane → Sphere) '' (A.H '' (A.T₀.carrier)ᶜ) ∪ {∞} := by
  sorry

/-- U6: the interior region is the image of the open base triangle. -/
theorem U6_interiorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) {L : ℝ}
    (A : AmbientParam P L) :
    interiorRegion P = ((↑) : Plane → Sphere) '' (A.H '' interior A.T₀.carrier) := by
  sorry

/-- U6: the interior region is open and connected in the sphere. -/
theorem U6_interiorRegion_isConnected [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    IsConnected (interiorRegion P) ∧ IsOpen (interiorRegion P) := by
  sorry

/-- U6 (57a, sm-3:430-431 / 486-489): exactly two complementary regions in the sphere. -/
theorem U6_two_regions [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    Nat.card (ConnectedComponents (sphereComplement P)) = 2 := by
  sorry

/-- U6 (57e, sm-3:434 / 448-456): the region of `∞` is the unbounded one, the other is a bounded
plane region. -/
theorem U6_exterior [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    ∞ ∈ exteriorRegion P ∧ (∀ z ∈ interiorRegion P, z ≠ ∞) ∧
      Bornology.IsBounded (((↑) : Plane → Sphere) ⁻¹' interiorRegion P) ∧
      ¬ Bornology.IsBounded (((↑) : Plane → Sphere) ⁻¹' exteriorRegion P) := by
  sorry

/-- U6 (bridge, plane form of 57a): the exterior region minus `∞` stays connected. -/
theorem U6_two_regions_plane [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    Nat.card (ConnectedComponents ((polygonImage P)ᶜ : Set Plane)) = 2 := by
  sorry

/-! ### U7 (sequential) — 57b for the interior region -/

/-- U7: the closed bounded region is `H (T₀)`. -/
theorem U7_closure_interiorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (A : AmbientParam P L) :
    closure (interiorRegion P) = ((↑) : Plane → Sphere) '' (A.H '' A.T₀.carrier) := by
  sorry

/-- U7 (sm-3:490-493, the interior disc): `H (T₀)` is a plane PL disc. -/
theorem U7_isPLDisc_image [NeZero n] (P : LabelledTuple n) {L : ℝ} (A : AmbientParam P L) :
    IsPLDisc (A.H '' A.T₀.carrier) := by
  sorry

/-- U7: the cap chart sees nothing of the closed bounded region. -/
theorem U7_chartPart_cap_empty [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) : chartPart L true (closure (interiorRegion P)) = ∅ := by
  sorry

/-- U7: `planeOf ∘ H⁻¹` is positive PL to the plane on the closed bounded region. -/
theorem U7_isPositivePLToPlane_inv [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) (A : AmbientParam P L) :
    IsPositivePLToPlane L (closure (interiorRegion P)) (A.H.symm ∘ planeOf) := by
  sorry

/-- U7 (57b interior, sm-3:431 / 490-493): the closure of the bounded region is a PL disc of the
sphere with boundary the circle. -/
theorem U7_pl_discs_inner [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (L : ℝ)
    (hL : InsideModel L P) : IsPLDiscSphere L (closure (regionOf P Side.inner)) (sphereCircle P) := by
  sorry

/-- U7 (bridge): a sphere PL disc lying in the plane chart is a plane PL disc. -/
theorem U7_isPLDisc_of_isPLDiscSphere {L : ℝ} {S B : Set Sphere} (hL : 0 < L)
    (hS : S ⊆ ((↑) : Plane → Sphere) '' square L) (h : IsPLDiscSphere L S B) :
    IsPLDisc (((↑) : Plane → Sphere) ⁻¹' S) := by
  sorry

/-- U7 (bridge): the closed bounded region, as a plane set, is a plane PL disc. -/
theorem U7_isPLDisc_closure_interior [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    IsPLDisc (((↑) : Plane → Sphere) ⁻¹' closure (interiorRegion P)) := by
  sorry

/-! ### U8 (sequential) — 57b for the exterior region -/

/-- U8 (chart algebra, PLAN_FINAL §4): the sup-norm inversion is an involution off `0`. -/
theorem U8_capInvFun_capInvFun {L : ℝ} (hL : 0 < L) {y : Plane} (hy : y ≠ 0) :
    capInvFun L (capInvFun L y) = y := by
  sorry

/-- U8: `‖capInvFun L y‖_∞ = L / ‖y‖_∞`. -/
theorem U8_supNorm_capInvFun {L : ℝ} (hL : 0 < L) {y : Plane} (hy : y ≠ 0) :
    supNorm (capInvFun L y) = L / supNorm y := by
  sorry

/-- U8 (sm-3:448-456 "the actual one-point-compactified exterior"): the cap chart is a homeomorphism
of `Q_1` onto the closed exterior of `Q_L` together with `∞`. -/
theorem U8_capChart_isHomeoOnto {L : ℝ} (hL : 0 < L) :
    IsHomeoOnto (square 1) (((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞}) (capChart L) := by
  sorry

/-- U8: on the seam `‖y‖_∞ = 1` the cap chart is the affine map `y ↦ L • (y₁, −y₂)`. -/
theorem U8_capInvFun_seam {L : ℝ} {y : Plane} (hy : supNorm y = 1) :
    capInvFun L y = L • (y.1, -y.2) := by
  sorry

/-- U8 (the 11-ray fan, PLAN_FINAL §3.3): the model exterior `Sphere \ int T₀` of a triangle inside
`int Q_L` is carried onto the square `Q_2` by a homeomorphism that is positive PL in the two model
charts and sends `∂T₀` onto `∂Q_2`. -/
theorem U8_exists_exterior_fan {L : ℝ} (hL : 0 < L) (T₀ : Triangle)
    (hT : T₀.carrier ⊆ interior (square L)) :
    ∃ g : Sphere → Plane,
      IsHomeoOnto (((↑) : Plane → Sphere) '' interior T₀.carrier)ᶜ (square 2) g ∧
      IsPositivePLToPlane L (((↑) : Plane → Sphere) '' interior T₀.carrier)ᶜ g ∧
      g '' (((↑) : Plane → Sphere) '' frontier T₀.carrier) = frontier (square 2) := by
  sorry

/-- U8: the closed exterior region is the sphere minus the open image triangle. -/
theorem U8_closure_exteriorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (A : AmbientParam P L) :
    closure (exteriorRegion P) = (((↑) : Plane → Sphere) '' (A.H '' interior A.T₀.carrier))ᶜ := by
  sorry

/-- U8: `H⁻¹` extended by the identity at `∞` is a positive PL sphere map (model `L` to model `L`)
on the closed exterior region. -/
theorem U8_isPositivePLSphereMap_inv [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) (A : AmbientParam P L) :
    IsPositivePLSphereMap L L (closure (exteriorRegion P)) (OnePoint.map A.H.symm) ∧
      IsHomeoOnto (closure (exteriorRegion P)) (((↑) : Plane → Sphere) '' interior A.T₀.carrier)ᶜ
        (OnePoint.map A.H.symm) := by
  sorry

/-- U8 (57b exterior, sm-3:431 / 448-456 / 490-493): the closure of the exterior region is a PL disc
of the sphere with boundary the circle. -/
theorem U8_pl_discs_outer [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (L : ℝ)
    (hL : InsideModel L P) : IsPLDiscSphere L (closure (regionOf P Side.outer)) (sphereCircle P) := by
  sorry

/-! ### U9 (sequential) — orientation bookkeeping (FR-TD-9) -/

/-- U9: the left normal `(−u₂, u₁)` of a direction `u`. -/
def leftNormal (u : Plane) : Plane := (-u.2, u.1)

/-- U9: the bounded region lies on the left of edge `i` (a short left normal from the midpoint of
the edge enters the interior region). -/
def InteriorOnLeft [NeZero n] (P : LabelledTuple n) (i : ZMod n) : Prop :=
  ∃ ε > 0, ∀ t ∈ Ioo (0 : ℝ) ε,
    (((1 / 2 : ℝ) • (P i + P (i + 1)) + t • leftNormal (edge P i) : Plane) : Sphere) ∈ interiorRegion P

/-- U9: `b` lies strictly between `a` and `c` in the counterclockwise cyclic order around `z`
(two-of-three `det` signs). -/
def CyclicPos (z a b c : Plane) : Prop :=
  (0 < det (a - z) (b - z) ∧ 0 < det (b - z) (c - z)) ∨
  (0 < det (b - z) (c - z) ∧ 0 < det (c - z) (a - z)) ∨
  (0 < det (c - z) (a - z) ∧ 0 < det (a - z) (b - z))

/-- U9: "interior on the left of edge `i`" is the sign of the face of the ear triangulation adjacent
to that edge; it is the same for all edges (consistency along the ear induction). -/
theorem U9_interiorOnLeft_consistent [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (i j : ZMod n) : InteriorOnLeft P i ↔ InteriorOnLeft P j := by
  sorry

/-- U9 (sm-3:4762-4764 read at a supporting vertex): at a supporting vertex with nonzero turn the
interior is on the left iff the turn is positive. -/
theorem U9_interiorOnLeft_iff_turn [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {N : Plane} {i : ZMod n} (hs : IsSupportingVertex P N i) (ht : principalTurn P i ≠ 0) :
    InteriorOnLeft P i ↔ 0 < principalTurn P i := by
  sorry

/-- U9 (with `cb_embedded_rotation.orientation`): the interior is on the left of the traversal iff
the rotation number is positive. -/
theorem U9_interiorOnLeft_iff_rotation [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (i : ZMod n) : InteriorOnLeft P i ↔ 0 < rotationNumber P := by
  sorry

/-- U9 (the convention of `traversalPositiveFor`, FR-TD-9): a positive PL parametrisation `f` of the
closed region `s` onto a convex model `D` carries the traversal, read around an interior point `z`,
to the counterclockwise cyclic order exactly when `traversalPositiveFor P s`. -/
theorem U9_traversalPositiveFor_iff_cyclicPos [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (s : Side) {L : ℝ} (hL : InsideModel L P) {D : Set Plane} {f : Sphere → Plane}
    (hD : Link.IsDisc D) (hf : IsHomeoOnto (closure (regionOf P s)) D f)
    (hB : f '' sphereCircle P = frontier D) (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    {z : Plane} (hz : z ∈ interior D) {x y w : ℝ} (hxy : x < y) (hyw : y < w) (hwx : w < x + n) :
    traversalPositiveFor P s ↔
      CyclicPos z (f ((traversal P x : Plane) : Sphere)) (f ((traversal P y : Plane) : Sphere))
        (f ((traversal P w : Plane) : Sphere)) := by
  sorry

/-- U9 (positivity of the boundary map, sm-3:431-434 "positive"): a positive boundary lift, read in
two positive parametrisations, preserves the counterclockwise cyclic order. -/
theorem U9_lift_preserves_cyclicPos [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {z z' : Plane} (hz : z ∈ interior D) (hz' : z' ∈ interior D') {φ : ℝ → ℝ}
    (hφ : IsPositiveBoundaryLift P s P' s' φ) {x y w : ℝ} (hxy : x < y) (hyw : y < w) (hwx : w < x + n)
    (h : CyclicPos z (f ((traversal P x : Plane) : Sphere)) (f ((traversal P y : Plane) : Sphere))
      (f ((traversal P w : Plane) : Sphere))) :
    CyclicPos z' (f' ((traversal P' (φ x) : Plane) : Sphere)) (f' ((traversal P' (φ y) : Plane) : Sphere))
      (f' ((traversal P' (φ w) : Plane) : Sphere)) := by
  sorry

/-! ### U10 (lane C convex model, then sequential) — 57c -/

/-- U10: `β` is finite PL on the frontier of `D`: affine on each of finitely many segments covering
`frontier D`. -/
def IsFinitePLOnFrontier (D : Set Plane) (β : Plane → Plane) : Prop :=
  ∃ s : Finset (Plane × Plane), (⋃ p ∈ s, segment ℝ p.1 p.2) = frontier D ∧
    ∀ p ∈ s, AffineOn β (segment ℝ p.1 p.2)

/-- U10: `β` preserves the counterclockwise cyclic order of `frontier D` around `z` (to that of
`frontier D'` around `z'`). -/
def PreservesCyclicPos (D : Set Plane) (z z' : Plane) (β : Plane → Plane) : Prop :=
  ∀ a ∈ frontier D, ∀ b ∈ frontier D, ∀ c ∈ frontier D,
    CyclicPos z a b c → CyclicPos z' (β a) (β b) (β c)

/-- U10 (sm-3:535-537, the fan extension on convex models): a finite positive PL homeomorphism
between the boundaries of two convex discs, preserving the cyclic order around interior points
`z ↦ z'`, extends to a positive PL homeomorphism of the discs (cone from `z` to `z'`). -/
theorem U10_fan_extension {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    {z z' : Plane} (hz : z ∈ interior D) (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβ : IsHomeoOnto (frontier D) (frontier D') β) (hpl : IsFinitePLOnFrontier D β)
    (hpos : PreservesCyclicPos D z z' β) :
    ∃ (K : Triangulation D) (F : Plane → Plane), IsPositivePLOn F K ∧ IsHomeoOnto D D' F ∧
      ∀ x ∈ frontier D, F x = β x := by
  sorry

/-- U10 (sm-3:431-433 "finite prescribed positive PL boundary maps" read in the models): a finite PL
positive boundary lift `φ`, conjugated by two positive PL disc parametrisations, is a finite PL
homeomorphism of the model frontiers preserving the cyclic order around suitable interior points. -/
theorem U10_boundary_map_of_lift [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) (hfin : IsFinitePL n φ) :
    ∃ (β : Plane → Plane) (z z' : Plane), z ∈ interior D ∧ z' ∈ interior D' ∧
      IsHomeoOnto (frontier D) (frontier D') β ∧ IsFinitePLOnFrontier D β ∧
      PreservesCyclicPos D z z' β ∧
      ∀ x : ℝ, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere) := by
  sorry

/-- U10 (57c, sm-3:431-433 / 535-537): finite positive PL boundary maps extend to positive PL disc
maps `F = Φ'⁻¹ ∘ Fan ∘ Φ`. -/
theorem U10_pl_extension [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (hn' : 3 ≤ n') (hP' : Embedded P')
    (s s' : Side) (L L' : ℝ) (hL : InsideModel L P) (hL' : InsideModel L' P')
    (φ : ℝ → ℝ) (hφ : IsPositiveBoundaryLift P s P' s' φ) (hfin : IsFinitePL n φ) :
    ∃ F : Sphere → Sphere,
      IsHomeoOnto (closure (regionOf P s)) (closure (regionOf P' s')) F ∧
      IsPositivePLSphereMap L L' (closure (regionOf P s)) F ∧
      ∀ x : ℝ, F ((traversal P x : Plane) : Sphere) = ((traversal P' (φ x) : Plane) : Sphere) := by
  sorry

/-! ### U11 (lane C convex model, then sequential) — 57d -/

/-- U11 (gauge coordinates): for a convex disc with `0` in its interior, the frontier is the gauge
level `1` and the disc is the sublevel `≤ 1`. -/
theorem U11_frontier_eq_gauge_one {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D) :
    frontier D = {x | gauge D x = 1} ∧ D = {x | gauge D x ≤ 1} := by
  sorry

/-- U11 (sm-3:537-542, the radial / Alexander extension on convex models): a homeomorphism between
the frontiers of two convex discs extends to a homeomorphism of the discs. -/
theorem U11_radial_extension {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    {β : Plane → Plane} (hβ : IsHomeoOnto (frontier D) (frontier D') β) :
    ∃ F : Plane → Plane, IsHomeoOnto D D' F ∧ ∀ x ∈ frontier D, F x = β x := by
  sorry

/-- U11 (sm-3:433-434 "continuous positive boundary map", FR-TD-10): a positive boundary lift `φ`,
conjugated by two disc parametrisations, is a homeomorphism of the model frontiers. -/
theorem U11_boundary_homeo_of_lift [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {D D' : Set Plane} {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    ∃ β : Plane → Plane, IsHomeoOnto (frontier D) (frontier D') β ∧
      ∀ x : ℝ, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere) := by
  sorry

/-- U11 (57d, sm-3:433-434 / 537-542): a continuous positive boundary map extends to a topological
disc map `F = Φ'⁻¹ ∘ A ∘ Φ` (the positivity hypothesis is kept as printed and unused, FR-TD-5). -/
theorem U11_top_extension [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (hn' : 3 ≤ n') (hP' : Embedded P')
    (s s' : Side) (φ : ℝ → ℝ) (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    ∃ F : Sphere → Sphere,
      IsHomeoOnto (closure (regionOf P s)) (closure (regionOf P' s')) F ∧
      ∀ x : ℝ, F ((traversal P x : Plane) : Sphere) = ((traversal P' (φ x) : Plane) : Sphere) := by
  sorry
/-! ## §5 The row: one field per printed clause -/

/-- **lem:gauss-two-discs** (sm-3:428-436), one field per printed clause; the model scale `L` is
any square containing the polygon (sm-3:439 "a large rectangle"), universally quantified.

Hypotheses of the row theorem `lem_gauss_two_discs`: `Embedded P` is the printed "simple polygonal
circle".  `hn : 3 ≤ n` is derivable from `Embedded P` (a simple closed polygon has at least three
vertices) but is kept for uniformity with row 104 (`cb_embedded_rotation`).  `Generic` is
deliberately *not* a hypothesis: flat vertices are in the domain (sm-3:4791), exactly as in row 104. -/
structure GaussTwoDiscsData [NeZero n] (P : LabelledTuple n) : Prop where
  /-- 57a (sm-3:430-431) "has exactly two complementary regions": the complement of the circle in
  the sphere has exactly two connected components. -/
  two_regions : Nat.card (ConnectedComponents (sphereComplement P)) = 2
  /-- 57b (sm-3:431) "both closures are PL discs": in every model square containing the polygon, the
  closure of each of the two regions is a PL disc of the sphere whose boundary is the circle. -/
  pl_discs : ∀ (s : Side) (L : ℝ), InsideModel L P →
    IsPLDiscSphere L (closure (regionOf P s)) (sphereCircle P)
  /-- 57c (sm-3:431-433) "Finite prescribed positive PL boundary maps between such discs extend to
  positive PL disc maps": for every second simple polygonal circle `P'`, every pair of regions and
  every finite positive PL boundary map (as a lift `φ`), there is a positive PL homeomorphism of the
  closures restricting to the prescribed boundary map. -/
  pl_extension : ∀ {n' : ℕ} [NeZero n'] (P' : LabelledTuple n'), 3 ≤ n' → Embedded P' →
    ∀ (s s' : Side) (L L' : ℝ), InsideModel L P → InsideModel L' P' →
    ∀ φ : ℝ → ℝ, IsPositiveBoundaryLift P s P' s' φ → IsFinitePL n φ →
    ∃ F : Sphere → Sphere,
      IsHomeoOnto (closure (regionOf P s)) (closure (regionOf P' s')) F ∧
      IsPositivePLSphereMap L L' (closure (regionOf P s)) F ∧
      ∀ x : ℝ, F ((traversal P x : Plane) : Sphere) = ((traversal P' (φ x) : Plane) : Sphere)
  /-- 57d (sm-3:433-434) "A continuous positive boundary map also extends to a topological disc
  map": a homeomorphism of the closures restricting to the prescribed boundary map (no PL claim). -/
  top_extension : ∀ {n' : ℕ} [NeZero n'] (P' : LabelledTuple n'), 3 ≤ n' → Embedded P' →
    ∀ (s s' : Side) (φ : ℝ → ℝ), IsPositiveBoundaryLift P s P' s' φ →
    ∃ F : Sphere → Sphere,
      IsHomeoOnto (closure (regionOf P s)) (closure (regionOf P' s')) F ∧
      ∀ x : ℝ, F ((traversal P x : Plane) : Sphere) = ((traversal P' (φ x) : Plane) : Sphere)
  /-- 57e (sm-3:434) "The statement includes the exterior region": the region of `∞` is one of the
  two regions (57b-57d above range over both sides), it is the unbounded one, and the other region
  is a bounded region of the plane. -/
  exterior : ∞ ∈ exteriorRegion P ∧ (∀ z ∈ interiorRegion P, z ≠ ∞) ∧
    Bornology.IsBounded (((↑) : Plane → Sphere) ⁻¹' interiorRegion P) ∧
    ¬ Bornology.IsBounded (((↑) : Plane → Sphere) ⁻¹' exteriorRegion P)

/-- **lem:gauss-two-discs** (row 57, sm-3:428-436). -/
theorem lem_gauss_two_discs [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    GaussTwoDiscsData P := by
  refine ⟨U6_two_regions hn P hP, ?_, ?_, ?_, U6_exterior hn P hP⟩
  · intro s L hL
    cases s with
    | inner => exact U7_pl_discs_inner hn P hP L hL
    | outer => exact U8_pl_discs_outer hn P hP L hL
  · intro n' _ P' hn' hP' s s' L L' hL hL' φ hφ hfin
    exact U10_pl_extension hn P hP P' hn' hP' s s' L L' hL hL' φ hφ hfin
  · intro n' _ P' hn' hP' s s' φ hφ
    exact U11_top_extension hn P hP P' hn' hP' s s' φ hφ

/-! ## §6 Bridges for consumers (not part of the row; assembled from the U6/U7 leaves) -/

/-- The plane form of 57a: the complement of the circle in the plane also has exactly two connected
components (the exterior region minus `∞` stays connected). -/
theorem two_regions_plane [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    Nat.card (ConnectedComponents ((polygonImage P)ᶜ : Set Plane)) = 2 :=
  U6_two_regions_plane hn P hP

/-- A sphere PL disc lying in the plane chart is a plane PL disc (its plane trace). -/
theorem isPLDisc_of_isPLDiscSphere {L : ℝ} {S B : Set Sphere} (hL : 0 < L)
    (hS : S ⊆ ((↑) : Plane → Sphere) '' square L) (h : IsPLDiscSphere L S B) :
    IsPLDisc (((↑) : Plane → Sphere) ⁻¹' S) :=
  U7_isPLDisc_of_isPLDiscSphere hL hS h

/-- The closure of the bounded region, as a plane set, is a plane PL disc. -/
theorem isPLDisc_closure_interior [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    IsPLDisc (((↑) : Plane → Sphere) ⁻¹' closure (interiorRegion P)) :=
  U7_isPLDisc_closure_interior hn P hP

end SM
