import SM.EmbeddedRotation
import SM.LinkMoves
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.SetTheory.Cardinal.Finite
import SM.DeletedTuple
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Join

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

/-- U3 (sm-3:462-466 "subdivide"): a triangulation can be refined so that every face lies on one
side of each of finitely many lines `{x | ⟪a j, x⟫ = c j}`. -/
theorem U3_refine_along_lines {X : Set Plane} (K : Triangulation X) {m : ℕ} (a : Fin m → Plane)
    (c : Fin m → ℝ) :
    ∃ K' : Triangulation X, K'.Refines K ∧ ∀ T' ∈ K'.faces, ∀ j,
      T'.carrier ⊆ {x | planeDot (a j) x ≤ c j} ∨ T'.carrier ⊆ {x | c j ≤ planeDot (a j) x} := by
  sorry

/-- U3: a triangulation can be refined so that every face lies in one face of a second
triangulation of a superset. -/
theorem U3_refine_into {X Y : Set Plane} (K : Triangulation X) (K' : Triangulation Y) (h : X ⊆ Y) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ ∀ T'' ∈ K''.faces, ∃ T' ∈ K'.faces, T''.carrier ⊆ T'.carrier := by
  sorry

/-- U3 (common refinement): two triangulations of the same set have a common refinement. -/
theorem U3_common_refinement {X : Set Plane} (K K' : Triangulation X) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ K''.Refines K' := by
  sorry

/-- U3 (sm-3:535-537, composition): the composite of positive PL maps is positive PL on a
refinement of the source triangulation. -/
theorem U3_isPositivePLOn_comp {X Y : Set Plane} (K : Triangulation X) (K' : Triangulation Y)
    {f g : Plane → Plane} (hf : IsPositivePLOn f K) (hg : IsPositivePLOn g K') (h : f '' X ⊆ Y) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ IsPositivePLOn (g ∘ f) K'' := by
  sorry

/-- U3 (chart bookkeeping, FR-TD-14): a positive PL map to the plane followed by a positive PL map
from the plane into the sphere is a positive PL sphere map. -/
theorem U3_isPositivePLSphereMap_comp {L L' : ℝ} {S : Set Sphere} {D : Set Plane}
    {f : Sphere → Plane} {g : Plane → Sphere} (hf : IsPositivePLToPlane L S f) (hfD : f '' S ⊆ D)
    (hg : IsPositivePLFromPlane L' D g) : IsPositivePLSphereMap L L' S (g ∘ f) := by
  sorry

/-- U3: a positive PL sphere map followed by a positive PL map to the plane is positive PL to the
plane. -/
theorem U3_isPositivePLToPlane_comp {L L' : ℝ} {S S' : Set Sphere} {F : Sphere → Sphere}
    {f : Sphere → Plane} (hF : IsPositivePLSphereMap L L' S F) (hFS : F '' S ⊆ S')
    (hf : IsPositivePLToPlane L' S' f) : IsPositivePLToPlane L S (f ∘ F) := by
  sorry

/-- U3: a positive PL map to the plane followed by a positive PL plane map is positive PL to the
plane. -/
theorem U3_isPositivePLToPlane_comp_plane {L : ℝ} {S : Set Sphere} {D : Set Plane}
    (K : Triangulation D) {f : Sphere → Plane} {g : Plane → Plane} (hf : IsPositivePLToPlane L S f)
    (hfD : f '' S ⊆ D) (hg : IsPositivePLOn g K) : IsPositivePLToPlane L S (g ∘ f) := by
  sorry

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

/-! ### U4 helpers (`u4h_`), 2026-09-19: the ear triangulation development.  Every helper is
placed here, immediately before the U4 leaves that use them.  See W1_U4_REPORT.md. -/

section U4A_block

/-- U4 helper: an edge segment is the Mathlib segment between consecutive vertices. -/
theorem u4h_edgeSegment_eq_segment (P : LabelledTuple n) (i : ZMod n) :
    edgeSegment P i = segment ℝ (P i) (P (i + 1)) := by
  rw [segment_eq_image]
  ext x
  simp only [edgeSegment, edgePoint, edge, Set.mem_ofPred_eq, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨t, ⟨ht0, ht1⟩, by module⟩
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    exact ⟨t, ht0, ht1, by module⟩

theorem u4h_isCompact_segment (x y : Plane) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

theorem u4h_isClosed_segment (x y : Plane) : IsClosed (segment ℝ x y) :=
  (u4h_isCompact_segment x y).isClosed

theorem u4h_polygonImage_isCompact [NeZero n] (P : LabelledTuple n) :
    IsCompact (polygonImage P) := by
  unfold polygonImage
  refine isCompact_iUnion fun i => ?_
  rw [u4h_edgeSegment_eq_segment]
  exact u4h_isCompact_segment _ _

theorem u4h_polygonImage_isClosed [NeZero n] (P : LabelledTuple n) :
    IsClosed (polygonImage P) := (u4h_polygonImage_isCompact P).isClosed

theorem u4h_edgePoint_mem_range_traversal [NeZero n] (P : LabelledTuple n) (i : ZMod n) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t < 1) : edgePoint P i t ∈ range (traversal P) := by
  refine ⟨(i.val : ℝ) + t, ?_⟩
  have hfl : ⌊(i.val : ℝ) + t⌋ = (i.val : ℤ) := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  have hfr : Int.fract ((i.val : ℝ) + t) = t := by
    rw [Int.fract, hfl]
    push_cast
    ring
  simp only [traversal, hfl, hfr, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem u4h_range_traversal [NeZero n] (P : LabelledTuple n) :
    range (traversal P) = polygonImage P := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Set.mem_iUnion.mpr ⟨_, Int.fract y, Int.fract_nonneg y, (Int.fract_lt_one y).le, rfl⟩
  · intro hx
    obtain ⟨i, t, ht0, ht1, rfl⟩ := Set.mem_iUnion.mp hx
    rcases ht1.lt_or_eq with ht1 | rfl
    · exact u4h_edgePoint_mem_range_traversal P i ht0 ht1
    · rw [edgePoint_one, ← edgePoint_zero P (i + 1)]
      exact u4h_edgePoint_mem_range_traversal P (i + 1) le_rfl zero_lt_one

theorem u4h_supNorm_eq_norm (x : Plane) : supNorm x = ‖x‖ := by
  simp [supNorm, Prod.norm_def, Real.norm_eq_abs]

theorem u4h_supNorm_nonneg (x : Plane) : 0 ≤ supNorm x := by
  rw [u4h_supNorm_eq_norm]; exact norm_nonneg x

theorem u4h_square_eq_closedBall (L : ℝ) : square L = Metric.closedBall 0 L := by
  ext x
  simp [square, u4h_supNorm_eq_norm, Metric.mem_closedBall, dist_zero_right]

theorem u4h_ball_subset_interior_square (L : ℝ) :
    Metric.ball (0 : Plane) L ⊆ interior (square L) := by
  rw [u4h_square_eq_closedBall]
  exact Metric.ball_subset_interior_closedBall

theorem u4h_mem_ball_of_supNorm_lt {L : ℝ} {x : Plane} (h : supNorm x < L) :
    x ∈ Metric.ball (0 : Plane) L := by
  rw [Metric.mem_ball, dist_zero_right, ← u4h_supNorm_eq_norm]; exact h

theorem u4h_exists_insideModel [NeZero n] (P : LabelledTuple n) :
    ∃ L : ℝ, 0 < L ∧ InsideModel L P := by
  obtain ⟨M, hM⟩ := (Set.finite_range fun i => supNorm (P i)).bddAbove
  refine ⟨M + 1, ?_, fun i => ?_⟩
  · have := hM ⟨0, rfl⟩
    have := u4h_supNorm_nonneg (P 0)
    linarith
  · have := hM ⟨i, rfl⟩
    linarith

theorem u4h_polygonImage_subset_ball [NeZero n] {L : ℝ} (P : LabelledTuple n)
    (hL : InsideModel L P) : polygonImage P ⊆ Metric.ball 0 L := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  rw [u4h_edgeSegment_eq_segment] at hi
  exact (convex_ball (0 : Plane) L).segment_subset (u4h_mem_ball_of_supNorm_lt (hL i))
    (u4h_mem_ball_of_supNorm_lt (hL (i + 1))) hi

theorem u4h_polygonImage_subset_interior_square [NeZero n] {L : ℝ} (P : LabelledTuple n)
    (hL : InsideModel L P) : polygonImage P ⊆ interior (square L) ∧ 0 < L := by
  refine ⟨(u4h_polygonImage_subset_ball P hL).trans (u4h_ball_subset_interior_square L), ?_⟩
  exact lt_of_le_of_lt (u4h_supNorm_nonneg (P 0)) (hL 0)

theorem u4h_three_le_of_embedded [NeZero n] (P : LabelledTuple n) (hP : Embedded P) : 3 ≤ n := by
  rcases n with _ | _ | _ | n
  · exact absurd rfl (NeZero.ne 0)
  · exfalso
    apply hP.edge_ne_zero 0
    have h : (0 : ZMod 1) + 1 = 0 := Subsingleton.elim _ _
    simp [edge, h]
  · exfalso
    have h01 : (0 : ZMod 2) + 1 = 1 := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have hc := hP.consecutive 0
    rw [h01, u4h_edgeSegment_eq_segment, u4h_edgeSegment_eq_segment, h01, h11,
      segment_symm ℝ (P 1) (P 0), Set.inter_self] at hc
    have hmem : P 0 ∈ segment ℝ (P 0) (P 1) := left_mem_segment ℝ _ _
    rw [hc] at hmem
    have h0 : P 0 = P 1 := hmem
    exact hP.edge_ne_zero 0 (by simp [edge, h01, h0])
  · omega

theorem u4h_start_mem_edgeSegment (P : LabelledTuple n) (i : ZMod n) : P i ∈ edgeSegment P i :=
  ⟨0, le_rfl, zero_le_one, (edgePoint_zero P i).symm⟩

theorem u4h_end_mem_edgeSegment (P : LabelledTuple n) (i : ZMod n) :
    P (i + 1) ∈ edgeSegment P i :=
  ⟨1, zero_le_one, le_rfl, (edgePoint_one P i).symm⟩

theorem u4h_edgeSegment_subset_polygonImage (P : LabelledTuple n) (i : ZMod n) :
    edgeSegment P i ⊆ polygonImage P := Set.subset_iUnion (fun i => edgeSegment P i) i

theorem u4h_vertex_mem_polygonImage (P : LabelledTuple n) (i : ZMod n) : P i ∈ polygonImage P :=
  u4h_edgeSegment_subset_polygonImage P i (u4h_start_mem_edgeSegment P i)

/-- U4 helper: an embedded polygon has pairwise distinct vertices. -/
theorem u4h_vertex_injective {P : LabelledTuple n} (hP : Embedded P) : Function.Injective P := by
  intro i j hij
  by_contra hne
  by_cases hadj : adjacent i j
  · rcases adjacent_distinct_cases hne hadj with h | h
    · apply hP.edge_ne_zero i
      rw [edge, ← h, hij, sub_self]
    · apply hP.edge_ne_zero j
      rw [edge, ← h, ← hij, sub_self]
  · have hi : P i ∈ edgeSegment P i := u4h_start_mem_edgeSegment P i
    have hj : P i ∈ edgeSegment P j := hij ▸ u4h_start_mem_edgeSegment P j
    exact Set.disjoint_left.mp (hP.remote_disjoint i j hadj) hi hj

/-- U4 helper: a vertex lying on an edge segment is one of its endpoints. -/
theorem u4h_incident_of_vertex_mem {P : LabelledTuple n} (hP : Embedded P) {k i : ZMod n}
    (hk : P k ∈ edgeSegment P i) : k = i ∨ k = i + 1 := by
  by_contra hne
  simp only [not_or] at hne
  by_cases hadj : adjacent k i
  · rcases adjacent_distinct_cases hne.1 hadj with h | h
    · -- `i = k + 1`: `P k ∈ E_k ∩ E_{k+1} = {P (k+1)}`.
      have hc := hP.consecutive k
      have hmem : P k ∈ edgeSegment P k ∩ edgeSegment P (k + 1) :=
        ⟨u4h_start_mem_edgeSegment P k, by rw [← h]; exact hk⟩
      rw [hc] at hmem
      have h0 : P k = P (k + 1) := hmem
      exact hP.edge_ne_zero k (by rw [edge, ← h0, sub_self])
    · exact hne.2 h
  · exact Set.disjoint_left.mp (hP.remote_disjoint k i hadj) (u4h_start_mem_edgeSegment P k) hk

end U4A_block

section U4B_block

/-! Barycentric / determinant toolkit for triangles `convexHull ℝ {a, b, c}` (U4 helpers). -/

theorem u4h_det_sub_right (u v w : Plane) : det u (v - w) = det u v - det u w := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem u4h_det_add_right (u v w : Plane) : det u (v + w) = det u v + det u w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem u4h_det_smul_right (u v : Plane) (t : ℝ) : det u (t • v) = t * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u4h_det_swap' (u v : Plane) : det u v = -det v u := by
  simp only [det]; ring

theorem u4h_det_self (u : Plane) : det u u = 0 := by simp only [det]; ring

theorem u4h_hull3_comm (a b c : Plane) :
    convexHull ℝ {a, b, c} = convexHull ℝ {a, c, b} := by
  rw [Set.pair_comm]

/-- Barycentric membership in the hull of three points. -/
theorem u4h_mem_hull3_iff (a b c x : Plane) :
    x ∈ convexHull ℝ {a, b, c} ↔
      ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧ x = α • a + β • b + γ • c := by
  rw [convexHull_insert (Set.insert_nonempty b {c}), convexHull_pair, mem_convexJoin]
  constructor
  · rintro ⟨a', ha', y, ⟨s, t, hs, ht, hst, rfl⟩, ⟨p, q, hp, hq, hpq, rfl⟩⟩
    rw [Set.mem_singleton_iff] at ha'
    subst ha'
    refine ⟨p, q * s, q * t, hp, mul_nonneg hq hs, mul_nonneg hq ht, ?_, ?_⟩
    · linear_combination hpq + q * hst
    · simp only [smul_add, smul_smul]; abel
  · rintro ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩
    refine ⟨a, Set.mem_singleton a, ?_⟩
    by_cases h0 : β + γ = 0
    · have hβ0 : β = 0 := by linarith
      have hγ0 : γ = 0 := by linarith
      refine ⟨b, left_mem_segment ℝ b c, α, 0, hα, le_rfl, by linarith, ?_⟩
      simp [hβ0, hγ0]
    · have hpos : 0 < β + γ := lt_of_le_of_ne (by linarith) (Ne.symm h0)
      refine ⟨(β / (β + γ)) • b + (γ / (β + γ)) • c,
        ⟨β / (β + γ), γ / (β + γ), div_nonneg hβ hpos.le, div_nonneg hγ hpos.le, ?_, rfl⟩,
        α, β + γ, hα, hpos.le, by linarith, ?_⟩
      · rw [← add_div, div_self h0]
      · rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ h0, mul_div_cancel₀ _ h0, add_assoc]

/-- The three sub-determinants sum to the full determinant. -/
theorem u4h_det_sum3 (a b c x : Plane) :
    det (b - a) (x - a) + det (c - b) (x - b) + det (a - c) (x - c) = det (b - a) (c - a) := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

/-- Membership in a positively oriented triangle by the three `det` signs. -/
theorem u4h_mem_hull3_iff_det {a b c : Plane} (hD : 0 < det (b - a) (c - a)) (x : Plane) :
    x ∈ convexHull ℝ {a, b, c} ↔
      0 ≤ det (b - a) (x - a) ∧ 0 ≤ det (c - b) (x - b) ∧ 0 ≤ det (a - c) (x - c) := by
  rw [u4h_mem_hull3_iff]
  constructor
  · rintro ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩
    have hα' : α = 1 - β - γ := by linarith
    subst hα'
    refine ⟨?_, ?_, ?_⟩
    · have e : det (b - a) ((1 - β - γ) • a + β • b + γ • c - a) = γ * det (b - a) (c - a) := by
        simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e]; exact mul_nonneg hγ hD.le
    · have e : det (c - b) ((1 - β - γ) • a + β • b + γ • c - b) =
          (1 - β - γ) * det (b - a) (c - a) := by
        simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e]; exact mul_nonneg hα hD.le
    · have e : det (a - c) ((1 - β - γ) • a + β • b + γ • c - c) = β * det (b - a) (c - a) := by
        simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e]; exact mul_nonneg hβ hD.le
  · rintro ⟨h1, h2, h3⟩
    have hD' : det (b - a) (c - a) ≠ 0 := hD.ne'
    refine ⟨det (c - b) (x - b) / det (b - a) (c - a), det (a - c) (x - c) / det (b - a) (c - a),
      det (b - a) (x - a) / det (b - a) (c - a), div_nonneg h2 hD.le, div_nonneg h3 hD.le,
      div_nonneg h1 hD.le, ?_, ?_⟩
    · rw [← add_div, ← add_div, div_eq_one_iff_eq hD']
      linear_combination u4h_det_sum3 a b c x
    · apply Prod.ext
      · have key : x.1 * det (b - a) (c - a) = det (c - b) (x - b) * a.1 +
            det (a - c) (x - c) * b.1 + det (b - a) (x - a) * c.1 := by
          simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
        simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div,
          eq_div_iff hD']
        exact key
      · have key : x.2 * det (b - a) (c - a) = det (c - b) (x - b) * a.2 +
            det (a - c) (x - c) * b.2 + det (b - a) (x - a) * c.2 := by
          simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
        simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div,
          eq_div_iff hD']
        exact key

/-- A point of the triangle with vanishing first sub-determinant lies on the edge `[a, b]`. -/
theorem u4h_mem_segment_of_det_eq_zero {a b c x : Plane} (hD : 0 < det (b - a) (c - a))
    (hx : x ∈ convexHull ℝ {a, b, c}) (h0 : det (b - a) (x - a) = 0) : x ∈ segment ℝ a b := by
  rw [u4h_mem_hull3_iff] at hx
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩ := hx
  have hα' : α = 1 - β - γ := by linarith
  subst hα'
  have e : det (b - a) ((1 - β - γ) • a + β • b + γ • c - a) = γ * det (b - a) (c - a) := by
    simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  rw [e] at h0
  have hγ0 : γ = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hD.ne'
  subst hγ0
  exact ⟨1 - β - 0, β, by linarith, hβ, by ring, by simp⟩

theorem u4h_det_segment_zero {a b x : Plane} (hx : x ∈ segment ℝ a b) : det (b - a) (x - a) = 0 := by
  rw [segment_eq_image] at hx
  obtain ⟨t, -, rfl⟩ := hx
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]; ring

/-- Two edges from a common vertex of a nondegenerate triangle meet only at that vertex. -/
theorem u4h_segment_inter_same_start {a b c : Plane} (hD : det (b - a) (c - a) ≠ 0) :
    segment ℝ a b ∩ segment ℝ a c = {a} := by
  ext x
  constructor
  · rintro ⟨hb, hc⟩
    rw [segment_eq_image] at hb hc
    obtain ⟨s, -, hs⟩ := hb
    obtain ⟨t, -, ht⟩ := hc
    simp only at hs ht
    have h1 : det (b - a) (x - a) = 0 := by
      rw [← hs]
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    have h2 : det (b - a) (x - a) = t * det (b - a) (c - a) := by
      rw [← ht]
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [h2] at h1
    have ht0 : t = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hD
    rw [ht0] at ht
    simp only [sub_zero, one_smul, zero_smul, add_zero] at ht
    exact ht.symm
  · intro hx
    have hx' : x = a := hx
    rw [hx']
    exact ⟨left_mem_segment ℝ a b, left_mem_segment ℝ a c⟩

theorem u4h_hull3_isCompact (a b c : Plane) : IsCompact (convexHull ℝ {a, b, c}) :=
  (Set.toFinite _).isCompact_convexHull ℝ

theorem u4h_hull3_isClosed (a b c : Plane) : IsClosed (convexHull ℝ {a, b, c}) :=
  (u4h_hull3_isCompact a b c).isClosed

theorem u4h_segment_subset_hull3 (a b c : Plane) : segment ℝ a b ⊆ convexHull ℝ {a, b, c} :=
  segment_subset_convexHull (by simp) (by simp)

theorem u4h_isLinearMap_det (u : Plane) : IsLinearMap ℝ (fun y : Plane => det u y) :=
  ⟨fun x y => u4h_det_add_right u x y, fun t x => by
    simp only [smul_eq_mul]; exact u4h_det_smul_right u x t⟩

theorem u4h_continuous_det (u : Plane) : Continuous (fun y : Plane => det u y) := by
  simp only [det]; fun_prop

end U4B_block

section U4C_block

/-! Topology of a nondegenerate triangle `convexHull ℝ {a, b, c}` (U4 helpers). -/

theorem u4h_hull3_rot (a b c : Plane) : convexHull ℝ {a, b, c} = convexHull ℝ {b, c, a} := by
  rw [Set.insert_comm, Set.pair_comm]

theorem u4h_det_rot1 (a b c : Plane) : det (c - b) (a - b) = det (b - a) (c - a) := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem u4h_det_rot2 (a b c : Plane) : det (a - c) (b - c) = det (b - a) (c - a) := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem u4h_continuous_det_sub (u p : Plane) : Continuous (fun y : Plane => det u (y - p)) :=
  (u4h_continuous_det u).comp (continuous_id.sub continuous_const)

theorem u4h_isOpen_det_pos (u p : Plane) : IsOpen {y : Plane | 0 < det u (y - p)} :=
  isOpen_lt continuous_const (u4h_continuous_det_sub u p)

theorem u4h_isClosed_det_nonneg (u p : Plane) : IsClosed {y : Plane | 0 ≤ det u (y - p)} :=
  isClosed_le continuous_const (u4h_continuous_det_sub u p)

theorem u4h_convex_det_pos (u p : Plane) : Convex ℝ {y : Plane | 0 < det u (y - p)} := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hp : s • p + t • p = p := by rw [← add_smul, hst, one_smul]
  have e : s • x + t • y - p = s • (x - p) + t • (y - p) := by
    calc s • x + t • y - p = s • x + t • y - (s • p + t • p) := by rw [hp]
      _ = s • (x - p) + t • (y - p) := by rw [smul_sub, smul_sub]; abel
  rw [e, u4h_det_add_right, u4h_det_smul_right, u4h_det_smul_right]
  rcases hs.lt_or_eq with hs | hs
  · exact add_pos_of_pos_of_nonneg (mul_pos hs hx) (mul_nonneg ht hy.le)
  · subst hs
    have ht1 : t = 1 := by linarith
    subst ht1
    simpa using hy

theorem u4h_isOpen_strict3 (a b c : Plane) :
    IsOpen {x : Plane | 0 < det (b - a) (x - a) ∧ 0 < det (c - b) (x - b) ∧
      0 < det (a - c) (x - c)} :=
  (u4h_isOpen_det_pos _ _).and ((u4h_isOpen_det_pos _ _).and (u4h_isOpen_det_pos _ _))

/-- A point with a nonpositive supporting determinant is not interior to a set on which that
determinant is nonnegative. -/
theorem u4h_not_mem_interior_of_det_nonpos {u w p x : Plane} {S : Set Plane}
    (hS : ∀ y ∈ S, 0 ≤ det u (y - p)) (hw : 0 < det u w) (hx : det u (x - p) ≤ 0) :
    x ∉ interior S := by
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  set δ : ℝ := ε / (2 * (‖w‖ + 1)) with hδ
  have hw1 : 0 < ‖w‖ + 1 := by positivity
  have hδpos : 0 < δ := by positivity
  have hy : x - δ • w ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos hδpos, hδ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  have h1 := hS _ (hball hy)
  rw [sub_right_comm, u4h_det_sub_right, u4h_det_smul_right] at h1
  nlinarith [mul_pos hδpos hw]

theorem u4h_interior_hull3 {a b c : Plane} (hD : 0 < det (b - a) (c - a)) :
    interior (convexHull ℝ {a, b, c}) =
      {x : Plane | 0 < det (b - a) (x - a) ∧ 0 < det (c - b) (x - b) ∧
        0 < det (a - c) (x - c)} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxm := interior_subset hx
    rw [u4h_mem_hull3_iff_det hD] at hxm
    obtain ⟨h1, h2, h3⟩ := hxm
    refine ⟨lt_of_le_of_ne h1 fun h => ?_, lt_of_le_of_ne h2 fun h => ?_,
      lt_of_le_of_ne h3 fun h => ?_⟩
    · exact u4h_not_mem_interior_of_det_nonpos (w := c - a)
        (fun y hy => ((u4h_mem_hull3_iff_det hD y).mp hy).1) hD h.symm.le hx
    · refine u4h_not_mem_interior_of_det_nonpos (w := a - b)
        (fun y hy => ((u4h_mem_hull3_iff_det hD y).mp hy).2.1) ?_ h.symm.le hx
      rw [u4h_det_rot1]; exact hD
    · refine u4h_not_mem_interior_of_det_nonpos (w := b - c)
        (fun y hy => ((u4h_mem_hull3_iff_det hD y).mp hy).2.2) ?_ h.symm.le hx
      rw [u4h_det_rot2]; exact hD
  · apply interior_maximal _ (u4h_isOpen_strict3 a b c)
    intro x hx
    rw [u4h_mem_hull3_iff_det hD]
    exact ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩

/-- On the closed triangle, `det (c - b) (x - b) = 0` means `x ∈ [b, c]`, and
`det (a - c) (x - c) = 0` means `x ∈ [c, a]` (rotations of `u4h_mem_segment_of_det_eq_zero`). -/
theorem u4h_mem_segment_of_det2_eq_zero {a b c x : Plane} (hD : 0 < det (b - a) (c - a))
    (hx : x ∈ convexHull ℝ {a, b, c}) (h0 : det (c - b) (x - b) = 0) : x ∈ segment ℝ b c := by
  rw [u4h_hull3_rot] at hx
  exact u4h_mem_segment_of_det_eq_zero (by rw [u4h_det_rot1]; exact hD) hx h0

theorem u4h_mem_segment_of_det3_eq_zero {a b c x : Plane} (hD : 0 < det (b - a) (c - a))
    (hx : x ∈ convexHull ℝ {a, b, c}) (h0 : det (a - c) (x - c) = 0) : x ∈ segment ℝ c a := by
  rw [u4h_hull3_rot, u4h_hull3_rot] at hx
  exact u4h_mem_segment_of_det_eq_zero (by rw [u4h_det_rot2]; exact hD) hx h0

theorem u4h_frontier_hull3 {a b c : Plane} (hD : 0 < det (b - a) (c - a)) :
    frontier (convexHull ℝ {a, b, c}) = segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a := by
  rw [(u4h_hull3_isClosed a b c).frontier_eq, u4h_interior_hull3 hD]
  ext x
  constructor
  · rintro ⟨hx, hnot⟩
    have hx' := hx
    rw [u4h_mem_hull3_iff_det hD] at hx'
    obtain ⟨h1, h2, h3⟩ := hx'
    simp only [Set.mem_ofPred_eq, not_and_or, not_lt] at hnot
    rcases hnot with h | h | h
    · exact Or.inl (Or.inl (u4h_mem_segment_of_det_eq_zero hD hx (le_antisymm h h1)))
    · exact Or.inl (Or.inr (u4h_mem_segment_of_det2_eq_zero hD hx (le_antisymm h h2)))
    · exact Or.inr (u4h_mem_segment_of_det3_eq_zero hD hx (le_antisymm h h3))
  · intro hx
    have hmem : x ∈ convexHull ℝ {a, b, c} := by
      rcases hx with (h | h) | h
      · exact u4h_segment_subset_hull3 a b c h
      · rw [u4h_hull3_rot]; exact u4h_segment_subset_hull3 b c a h
      · rw [u4h_hull3_rot, u4h_hull3_rot]; exact u4h_segment_subset_hull3 c a b h
    refine ⟨hmem, ?_⟩
    simp only [Set.mem_ofPred_eq, not_and_or, not_lt]
    rcases hx with (h | h) | h
    · exact Or.inl (u4h_det_segment_zero h).le
    · exact Or.inr (Or.inl (u4h_det_segment_zero h).le)
    · exact Or.inr (Or.inr (u4h_det_segment_zero h).le)

/-- Half-disc lemma at an interior point of the edge `[c, a]`: nearby points lie in the triangle
iff they lie on the closed side of the edge line containing `b`. -/
theorem u4h_halfdisc {a b c x : Plane} (hD : 0 < det (b - a) (c - a))
    (hx : x ∈ openSegment ℝ c a) :
    ∃ ε > 0, ∀ y, dist y x < ε →
      (y ∈ convexHull ℝ {a, b, c} ↔ 0 ≤ det (a - c) (y - c)) := by
  rw [openSegment_eq_image] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  have h1 : 0 < det (b - a) ((1 - t) • c + t • a - a) := by
    have e : det (b - a) ((1 - t) • c + t • a - a) = (1 - t) * det (b - a) (c - a) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos (by linarith) hD
  have h2 : 0 < det (c - b) ((1 - t) • c + t • a - b) := by
    have e : det (c - b) ((1 - t) • c + t • a - b) = t * det (b - a) (c - a) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos ht0 hD
  have hopen : IsOpen {y : Plane | 0 < det (b - a) (y - a) ∧ 0 < det (c - b) (y - b)} :=
    (u4h_isOpen_det_pos _ _).and (u4h_isOpen_det_pos _ _)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ⟨h1, h2⟩)
  refine ⟨ε, hε, fun y hy => ?_⟩
  have hy' := hball (Metric.mem_ball.mpr hy)
  rw [u4h_mem_hull3_iff_det hD]
  exact ⟨fun h => h.2.2, fun h => ⟨hy'.1.le, hy'.2.le, h⟩⟩

/-- The triangle minus the closed edge `[c, a]` is the convex set `T ∩ {det (a - c) (· - c) > 0}`. -/
theorem u4h_hull3_diff_edge {a b c : Plane} (hD : 0 < det (b - a) (c - a)) :
    convexHull ℝ {a, b, c} \ segment ℝ c a =
      convexHull ℝ {a, b, c} ∩ {y : Plane | 0 < det (a - c) (y - c)} := by
  ext y
  constructor
  · rintro ⟨hy, hns⟩
    refine ⟨hy, ?_⟩
    have h3 := ((u4h_mem_hull3_iff_det hD y).mp hy).2.2
    exact lt_of_le_of_ne h3 fun h => hns (u4h_mem_segment_of_det3_eq_zero hD hy h.symm)
  · rintro ⟨hy, hpos⟩
    refine ⟨hy, fun hs => ?_⟩
    have := u4h_det_segment_zero hs
    simp only [Set.mem_ofPred_eq] at hpos
    linarith

theorem u4h_convex_hull3_diff_edge {a b c : Plane} (hD : 0 < det (b - a) (c - a)) :
    Convex ℝ (convexHull ℝ {a, b, c} \ segment ℝ c a) := by
  rw [u4h_hull3_diff_edge hD]
  exact (convex_convexHull ℝ _).inter (u4h_convex_det_pos _ _)

/-! ### `Triangle` from a positively oriented triple -/

theorem u4h_range_fin3 {α : Type*} (f : Fin 3 → α) : Set.range f = {f 0, f 1, f 2} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

theorem u4h_carrier_eq (T : Triangle) : T.carrier = convexHull ℝ {T.v 0, T.v 1, T.v 2} := by
  rw [Triangle.carrier, u4h_range_fin3]

/-- The positively oriented triangle on `a, b, c`. -/
def u4h_mkTri (a b c : Plane) (h : 0 < det (b - a) (c - a)) : Triangle :=
  ⟨![a, b, c], by simpa using h⟩

@[simp] theorem u4h_mkTri_v0 (a b c : Plane) (h : 0 < det (b - a) (c - a)) :
    (u4h_mkTri a b c h).v 0 = a := rfl

@[simp] theorem u4h_mkTri_v1 (a b c : Plane) (h : 0 < det (b - a) (c - a)) :
    (u4h_mkTri a b c h).v 1 = b := rfl

@[simp] theorem u4h_mkTri_v2 (a b c : Plane) (h : 0 < det (b - a) (c - a)) :
    (u4h_mkTri a b c h).v 2 = c := rfl

theorem u4h_mkTri_carrier (a b c : Plane) (h : 0 < det (b - a) (c - a)) :
    (u4h_mkTri a b c h).carrier = convexHull ℝ {a, b, c} := by
  rw [u4h_carrier_eq]; rfl

theorem u4h_mkTri_range (a b c : Plane) (h : 0 < det (b - a) (c - a)) :
    Set.range (u4h_mkTri a b c h).v = {a, b, c} := by
  rw [u4h_range_fin3]; rfl

theorem u4h_mkTri_edgeSeg0 (a b c : Plane) (h : 0 < det (b - a) (c - a)) :
    (u4h_mkTri a b c h).edgeSeg 0 = segment ℝ a b := rfl

theorem u4h_mkTri_edgeSeg1 (a b c : Plane) (h : 0 < det (b - a) (c - a)) :
    (u4h_mkTri a b c h).edgeSeg 1 = segment ℝ b c := rfl

theorem u4h_mkTri_edgeSeg2 (a b c : Plane) (h : 0 < det (b - a) (c - a)) :
    (u4h_mkTri a b c h).edgeSeg 2 = segment ℝ c a := rfl

end U4C_block

section U4D_block

/-! Segment against a triangle, part 1 (U4 helpers): a segment whose points on the two
"polygon" edges are only the base vertices, and whose endpoints inside the triangle are only the
base vertices, has no point in the open triangle. -/

/-- A preconnected set meeting both `t` and `tᶜ` meets `frontier t`. -/
theorem u4h_preconnected_inter_frontier {α : Type*} [TopologicalSpace α] {s t : Set α}
    (hs : IsPreconnected s) (h1 : (s ∩ t).Nonempty) (h2 : (s \ t).Nonempty) :
    (s ∩ frontier t).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hsub : s ⊆ interior t ∪ interior tᶜ := by
    intro x hx
    by_cases hxt : x ∈ closure t
    · by_cases hxi : x ∈ interior t
      · exact Or.inl hxi
      · have hmem : x ∈ s ∩ frontier t := ⟨hx, hxt, hxi⟩
        rw [hne] at hmem
        exact hmem.elim
    · right
      rw [interior_compl]
      exact hxt
  rcases IsPreconnected.subset_or_subset isOpen_interior isOpen_interior
      ((disjoint_compl_right : Disjoint t tᶜ).mono interior_subset interior_subset) hsub hs
      with h | h
  · obtain ⟨x, hx, hxt⟩ := h2
    exact hxt (interior_subset (h hx))
  · obtain ⟨x, hx, hxt⟩ := h1
    exact (interior_subset (h hx) : x ∈ tᶜ) hxt

theorem u4h_mem_segment_iff_lin (s t x : Plane) :
    x ∈ segment ℝ s t ↔ ∃ l : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ x = s + l • (t - s) := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨l, ⟨h0, h1⟩, rfl⟩
    exact ⟨l, h0, h1, by module⟩
  · rintro ⟨l, h0, h1, rfl⟩
    exact ⟨l, ⟨h0, h1⟩, by module⟩

theorem u4h_lin_mem_segment (s t : Plane) {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) :
    s + l • (t - s) ∈ segment ℝ s t :=
  (u4h_mem_segment_iff_lin s t _).mpr ⟨l, h0, h1, rfl⟩

theorem u4h_det_lin (u r s t : Plane) (l : ℝ) :
    det u (s + l • (t - s) - r) = det u (s - r) + l * det u (t - s) := by
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]; ring

/-- The base vertices `p, r` are frontier points and have vanishing base determinant. -/
theorem u4h_det_base_zero (p r x : Plane) (hx : x = p ∨ x = r) : det (p - r) (x - r) = 0 := by
  rcases hx with rfl | rfl
  · exact u4h_det_self _
  · simp [det]

theorem u4h_base_mem_frontier {p q r : Plane} (hD : 0 < det (q - p) (r - p)) {x : Plane}
    (hx : x = p ∨ x = r) : x ∈ frontier (convexHull ℝ {p, q, r}) := by
  rw [u4h_frontier_hull3 hD]
  rcases hx with rfl | rfl
  · exact Or.inl (Or.inl (left_mem_segment ℝ _ _))
  · exact Or.inl (Or.inr (right_mem_segment ℝ _ _))

/-- Points of the segment on the frontier of the triangle have vanishing base determinant,
under the hypothesis that its points on the two side edges are base vertices. -/
theorem u4h_det_zero_of_frontier {p q r s t : Plane} (hD : 0 < det (q - p) (r - p))
    (H1 : segment ℝ s t ∩ (segment ℝ p q ∪ segment ℝ q r) ⊆ {p, r}) {z : Plane}
    (hz : z ∈ segment ℝ s t) (hzf : z ∈ frontier (convexHull ℝ {p, q, r})) :
    det (p - r) (z - r) = 0 := by
  rw [u4h_frontier_hull3 hD] at hzf
  rcases hzf with h | h
  · exact u4h_det_base_zero p r z (H1 ⟨hz, h⟩)
  · exact u4h_det_segment_zero h

/-- One-sided step: from an interior point `x` of the triangle on the segment, the sub-segment
towards an endpoint `e` contains a point `z ≠ x` of the segment with vanishing base determinant. -/
theorem u4h_exists_zero_towards {p q r s t x e : Plane} (hD : 0 < det (q - p) (r - p))
    (H1 : segment ℝ s t ∩ (segment ℝ p q ∪ segment ℝ q r) ⊆ {p, r})
    (He : e ∈ convexHull ℝ {p, q, r} → e = p ∨ e = r)
    (hes : e ∈ segment ℝ s t) (hx : x ∈ segment ℝ s t)
    (hxi : x ∈ interior (convexHull ℝ {p, q, r})) :
    ∃ z ∈ segment ℝ x e, z ≠ x ∧ det (p - r) (z - r) = 0 := by
  by_cases heT : e ∈ convexHull ℝ {p, q, r}
  · refine ⟨e, right_mem_segment ℝ x e, fun hex => ?_, u4h_det_base_zero p r e (He heT)⟩
    have := u4h_base_mem_frontier hD (He heT)
    rw [hex] at this
    exact (disjoint_interior_frontier.notMem_of_mem_left hxi) this
  · obtain ⟨z, hz, hzf⟩ := u4h_preconnected_inter_frontier (convex_segment x e).isPreconnected
      ⟨x, left_mem_segment ℝ x e, interior_subset hxi⟩ ⟨e, right_mem_segment ℝ x e, heT⟩
    have hzS : z ∈ segment ℝ s t := (convex_segment s t).segment_subset hx hes hz
    refine ⟨z, hz, fun hzx => ?_, u4h_det_zero_of_frontier hD H1 hzS hzf⟩
    rw [hzx] at hzf
    exact disjoint_interior_frontier.notMem_of_mem_left hxi hzf

/-- Claim A: no point of the segment lies in the open triangle. -/
theorem u4h_no_interior_point {p q r s t : Plane} (hD : 0 < det (q - p) (r - p))
    (H1 : segment ℝ s t ∩ (segment ℝ p q ∪ segment ℝ q r) ⊆ {p, r})
    (H2 : s ∈ convexHull ℝ {p, q, r} → s = p ∨ s = r)
    (H3 : t ∈ convexHull ℝ {p, q, r} → t = p ∨ t = r) (x : Plane) (hx : x ∈ segment ℝ s t) :
    x ∉ interior (convexHull ℝ {p, q, r}) := by
  intro hxi
  have hxpos : 0 < det (p - r) (x - r) := by
    rw [u4h_interior_hull3 hD] at hxi
    exact hxi.2.2
  obtain ⟨z1, hz1, hz1x, hg1⟩ :=
    u4h_exists_zero_towards hD H1 H2 (left_mem_segment ℝ s t) hx hxi
  obtain ⟨z2, hz2, hz2x, hg2⟩ :=
    u4h_exists_zero_towards hD H1 H3 (right_mem_segment ℝ s t) hx hxi
  obtain ⟨l, hl0, hl1, rfl⟩ := (u4h_mem_segment_iff_lin s t x).mp hx
  obtain ⟨α, hα0, -, hz1e⟩ := (u4h_mem_segment_iff_lin _ s z1).mp hz1
  obtain ⟨β, hβ0, -, hz2e⟩ := (u4h_mem_segment_iff_lin _ t z2).mp hz2
  have hαpos : 0 < α := by
    rcases hα0.lt_or_eq with h | h
    · exact h
    · subst h; exact absurd (by rw [hz1e]; simp) hz1x
  have hβpos : 0 < β := by
    rcases hβ0.lt_or_eq with h | h
    · exact h
    · subst h; exact absurd (by rw [hz2e]; simp) hz2x
  -- the base determinant along the line is affine in the parameter
  have e1 : det (p - r) (z1 - r) = det (p - r) (s + l • (t - s) - r) - α * l * det (p - r) (t - s) := by
    rw [hz1e]
    simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  have e2 : det (p - r) (z2 - r) = det (p - r) (s + l • (t - s) - r) + β * (1 - l) * det (p - r) (t - s) := by
    rw [hz2e]
    simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  rw [e1] at hg1
  rw [e2] at hg2
  -- `g x = α l D' = -β (1-l) D'` forces `D' = 0`, hence `g x = 0`
  have hl0' : 0 < l := by
    rcases hl0.lt_or_eq with h | h
    · exact h
    · exfalso
      subst h
      have hsT : s ∈ convexHull ℝ {p, q, r} := by simpa using interior_subset hxi
      have := u4h_base_mem_frontier hD (H2 hsT)
      exact disjoint_interior_frontier.notMem_of_mem_left hxi (by simpa using this)
  have hl1' : l < 1 := by
    rcases hl1.lt_or_eq with h | h
    · exact h
    · exfalso
      subst h
      have htT : t ∈ convexHull ℝ {p, q, r} := by simpa using interior_subset hxi
      have := u4h_base_mem_frontier hD (H3 htT)
      exact disjoint_interior_frontier.notMem_of_mem_left hxi (by simpa using this)
  have hsum : (α * l + β * (1 - l)) * det (p - r) (t - s) = 0 := by
    linear_combination hg2 - hg1
  have hcoef : 0 < α * l + β * (1 - l) := by
    have := mul_pos hαpos hl0'
    have := mul_pos hβpos (sub_pos.mpr hl1')
    linarith
  have hD0 : det (p - r) (t - s) = 0 := by
    rcases mul_eq_zero.mp hsum with h | h
    · exact absurd h hcoef.ne'
    · exact h
  rw [hD0] at hg1
  linarith

end U4D_block

section U4E_block

/-! Segment against a triangle, part 2 (U4 helpers): Claim B and the conclusion
`segment ∩ triangle ⊆ {p, r}`. -/

/-- Near an interior point of the edge `[c, a]` the two other sub-determinants are positive. -/
theorem u4h_near_open_edge {a b c x : Plane} (hD : 0 < det (b - a) (c - a))
    (hx : x ∈ openSegment ℝ c a) :
    ∃ ε > 0, ∀ y, dist y x < ε → 0 < det (b - a) (y - a) ∧ 0 < det (c - b) (y - b) := by
  rw [openSegment_eq_image] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  have h1 : 0 < det (b - a) ((1 - t) • c + t • a - a) := by
    have e : det (b - a) ((1 - t) • c + t • a - a) = (1 - t) * det (b - a) (c - a) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos (by linarith) hD
  have h2 : 0 < det (c - b) ((1 - t) • c + t • a - b) := by
    have e : det (c - b) ((1 - t) • c + t • a - b) = t * det (b - a) (c - a) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos ht0 hD
  have hopen : IsOpen {y : Plane | 0 < det (b - a) (y - a) ∧ 0 < det (c - b) (y - b)} :=
    (u4h_isOpen_det_pos _ _).and (u4h_isOpen_det_pos _ _)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ⟨h1, h2⟩)
  exact ⟨ε, hε, fun y hy => hball (Metric.mem_ball.mpr hy)⟩

/-- A point of the line `r + κ • u` between two of its points lies on their segment. -/
theorem u4h_line_point_mem_segment {r u s t : Plane} {σs σt κ : ℝ} (hs : s = r + σs • u)
    (ht : t = r + σt • u) (hκ : (σs ≤ κ ∧ κ ≤ σt) ∨ (σt ≤ κ ∧ κ ≤ σs)) :
    r + κ • u ∈ segment ℝ s t := by
  by_cases hst : σt = σs
  · have hκs : κ = σs := by rcases hκ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    rw [hκs, ← hs]
    exact left_mem_segment ℝ s t
  · have hne : σt - σs ≠ 0 := sub_ne_zero.mpr hst
    rw [u4h_mem_segment_iff_lin]
    refine ⟨(κ - σs) / (σt - σs), ?_, ?_, ?_⟩
    · rcases hκ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hlt : σs < σt := lt_of_le_of_ne (h1.trans h2) (Ne.symm hst)
        exact div_nonneg (by linarith) (by linarith)
      · have hlt : σt < σs := lt_of_le_of_ne (h1.trans h2) hst
        exact div_nonneg_of_nonpos (by linarith) (by linarith)
    · rcases hκ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hlt : σs < σt := lt_of_le_of_ne (h1.trans h2) (Ne.symm hst)
        rw [div_le_one (by linarith)]; linarith
      · have hlt : σt < σs := lt_of_le_of_ne (h1.trans h2) hst
        rw [div_le_one_of_neg (by linarith)]; linarith
    · rw [hs, ht]
      have e : r + σs • u + ((κ - σs) / (σt - σs)) • (r + σt • u - (r + σs • u)) =
          r + (σs + (κ - σs) / (σt - σs) * (σt - σs)) • u := by
        simp only [add_sub_add_left_eq_sub, ← sub_smul, smul_smul, add_smul]; abel
      rw [e, div_mul_cancel₀ _ hne]
      congr 2; ring

/-- Claim B, collinear sub-case: if the base determinant vanishes identically on the segment and
the segment meets the open base edge, both base vertices lie on the segment. -/
theorem u4h_collinear_case {p q r s t : Plane} (hD : 0 < det (q - p) (r - p))
    (H2 : s ∈ convexHull ℝ {p, q, r} → s = p ∨ s = r)
    (H3 : t ∈ convexHull ℝ {p, q, r} → t = p ∨ t = r)
    {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (hs0 : det (p - r) (s - r) = 0)
    (ht0 : det (p - r) (t - r) = 0) (hxo : s + l • (t - s) ∈ openSegment ℝ r p) :
    p ∈ segment ℝ s t ∧ r ∈ segment ℝ s t := by
  have hpr : p - r ≠ 0 := by
    intro h
    have : r = p := (sub_eq_zero.mp h).symm
    rw [this] at hD
    simp [det] at hD
  obtain ⟨σs, hs⟩ : ∃ σ : ℝ, s = r + σ • (p - r) :=
    ⟨_, by rw [← scalar_of_det_zero hpr hs0]; abel⟩
  obtain ⟨σt, ht⟩ : ∃ σ : ℝ, t = r + σ • (p - r) :=
    ⟨_, by rw [← scalar_of_det_zero hpr ht0]; abel⟩
  -- the parameter of `x` on the base line
  rw [openSegment_eq_image] at hxo
  obtain ⟨θ, ⟨hθ0, hθ1⟩, hθ⟩ := hxo
  simp only at hθ
  have hθ' : θ = σs + l * (σt - σs) := by
    have e1 : (1 - θ) • r + θ • p = r + θ • (p - r) := by module
    have e2 : s + l • (t - s) = r + (σs + l * (σt - σs)) • (p - r) := by
      rw [hs, ht]; module
    rw [e1, e2] at hθ
    have := smul_left_injective ℝ hpr (add_left_cancel hθ)
    exact this
  -- a point `r + σ • (p - r)` with `0 ≤ σ ≤ 1` lies in the triangle
  have hmemT : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → r + σ • (p - r) ∈ convexHull ℝ {p, q, r} := by
    intro σ h0 h1
    rw [u4h_hull3_rot, u4h_hull3_rot]
    exact u4h_segment_subset_hull3 r p q (u4h_lin_mem_segment r p h0 h1)
  have hσ : ∀ σ : ℝ, r + σ • (p - r) = p ∨ r + σ • (p - r) = r → σ = 1 ∨ σ = 0 := by
    intro σ h
    rcases h with h | h
    · left
      have : σ • (p - r) = (1 : ℝ) • (p - r) := by rw [one_smul]; exact eq_sub_of_add_eq' h
      exact smul_left_injective ℝ hpr this
    · right
      have : σ • (p - r) = (0 : ℝ) • (p - r) := by rw [zero_smul]; exact add_eq_left.mp h
      exact smul_left_injective ℝ hpr this
  have hs' : σs ≤ 0 ∨ 1 ≤ σs := by
    by_contra hc
    simp only [not_or, not_le] at hc
    rcases hσ σs (by rw [← hs]; exact H2 (by rw [hs]; exact hmemT σs hc.1.le hc.2.le)) with h | h
    · linarith
    · linarith
  have ht' : σt ≤ 0 ∨ 1 ≤ σt := by
    by_contra hc
    simp only [not_or, not_le] at hc
    rcases hσ σt (by rw [← ht]; exact H3 (by rw [ht]; exact hmemT σt hc.1.le hc.2.le)) with h | h
    · linarith
    · linarith
  have hcase : (σs ≤ 0 ∧ 1 ≤ σt) ∨ (σt ≤ 0 ∧ 1 ≤ σs) := by
    rcases hs' with h1 | h1 <;> rcases ht' with h2 | h2
    · exfalso; nlinarith
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exfalso; nlinarith
  have hp : p = r + (1 : ℝ) • (p - r) := by simp
  have hr : r = r + (0 : ℝ) • (p - r) := by simp
  constructor
  · rw [hp]
    apply u4h_line_point_mem_segment hs ht
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, h2⟩
    · exact Or.inr ⟨by linarith, h2⟩
  · rw [hr]
    apply u4h_line_point_mem_segment hs ht
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by linarith⟩
    · exact Or.inr ⟨h1, by linarith⟩

end U4E_block

section U4F_block

/-! Segment against a triangle, part 3 (U4 helpers): the conclusion. -/

theorem u4h_segment_inter_tri {p q r s t : Plane} (hD : 0 < det (q - p) (r - p))
    (H1 : segment ℝ s t ∩ (segment ℝ p q ∪ segment ℝ q r) ⊆ {p, r})
    (H2 : s ∈ convexHull ℝ {p, q, r} → s = p ∨ s = r)
    (H3 : t ∈ convexHull ℝ {p, q, r} → t = p ∨ t = r)
    (H5 : ¬ (p ∈ segment ℝ s t ∧ r ∈ segment ℝ s t)) :
    segment ℝ s t ∩ convexHull ℝ {p, q, r} ⊆ {p, r} := by
  rintro x ⟨hxS, hxT⟩
  by_contra hxpr
  have hxp : x ≠ p := by rintro rfl; exact hxpr (Set.mem_insert _ _)
  have hxr : x ≠ r := by rintro rfl; exact hxpr (Set.mem_insert_of_mem _ rfl)
  have hxni := u4h_no_interior_point hD H1 H2 H3 x hxS
  have hxf : x ∈ frontier (convexHull ℝ {p, q, r}) := ⟨subset_closure hxT, hxni⟩
  have hxrp : x ∈ segment ℝ r p := by
    rw [u4h_frontier_hull3 hD] at hxf
    rcases hxf with h | h
    · exact absurd (H1 ⟨hxS, h⟩) hxpr
    · exact h
  have hxo : x ∈ openSegment ℝ r p := mem_openSegment_of_ne_left_right hxr.symm hxp.symm hxrp
  have hg0 : det (p - r) (x - r) = 0 := u4h_det_segment_zero hxrp
  obtain ⟨l, hl0, hl1, hxl⟩ := (u4h_mem_segment_iff_lin s t x).mp hxS
  have hl0' : 0 < l := by
    rcases hl0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_smul, add_zero] at hxl
      subst hxl
      exact hxpr (H2 hxT)
  have hl1' : l < 1 := by
    rcases hl1.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [h, one_smul, add_sub_cancel] at hxl
      subst hxl
      exact hxpr (H3 hxT)
  have hlin := u4h_det_lin (p - r) r s t l
  rw [← hxl, hg0] at hlin
  by_cases hDl : det (p - r) (t - s) = 0
  · have hs0 : det (p - r) (s - r) = 0 := by rw [hDl] at hlin; linarith
    have ht0 : det (p - r) (t - r) = 0 := by
      have e : t - r = (s - r) + (t - s) := by abel
      rw [e, u4h_det_add_right, hs0, hDl, add_zero]
    exact H5 (u4h_collinear_case hD H2 H3 hl0' hl1' hs0 ht0 (hxl ▸ hxo))
  · obtain ⟨ε, hε, hnear⟩ := u4h_near_open_edge hD hxo
    have hts1 : 0 < ‖t - s‖ + 1 := by positivity
    set δ : ℝ := min (ε / (2 * (‖t - s‖ + 1))) (min l (1 - l)) with hδdef
    have hδ : 0 < δ := by
      apply lt_min (by positivity) (lt_min hl0' (by linarith))
    have hδl : δ ≤ l := (min_le_right _ _).trans (min_le_left _ _)
    have hδ1 : δ ≤ 1 - l := (min_le_right _ _).trans (min_le_right _ _)
    have hδε : δ * ‖t - s‖ < ε := by
      have h1 : δ ≤ ε / (2 * (‖t - s‖ + 1)) := min_le_left _ _
      have h2 : δ * ‖t - s‖ ≤ ε / (2 * (‖t - s‖ + 1)) * ‖t - s‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      have h3 : ε / (2 * (‖t - s‖ + 1)) * ‖t - s‖ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg (t - s)]
      linarith
    obtain ⟨η, hηabs, hηD⟩ : ∃ η : ℝ, |η| = δ ∧ 0 < η * det (p - r) (t - s) := by
      rcases lt_or_gt_of_ne hDl with h | h
      · exact ⟨-δ, by rw [abs_neg, abs_of_pos hδ], by nlinarith⟩
      · exact ⟨δ, abs_of_pos hδ, mul_pos hδ h⟩
    have hηle : -δ ≤ η ∧ η ≤ δ := abs_le.mp (le_of_eq hηabs)
    have hy0 : 0 ≤ l + η := by linarith [hηle.1]
    have hy1 : l + η ≤ 1 := by linarith [hηle.2]
    have hdist : dist (s + (l + η) • (t - s)) x < ε := by
      rw [hxl, dist_eq_norm]
      have e : s + (l + η) • (t - s) - (s + l • (t - s)) = η • (t - s) := by module
      rw [e, norm_smul, Real.norm_eq_abs, hηabs]
      exact hδε
    have hgy : 0 < det (p - r) (s + (l + η) • (t - s) - r) := by
      rw [u4h_det_lin]
      linear_combination hηD + hlin
    have hy' := hnear _ hdist
    have hyi : s + (l + η) • (t - s) ∈ interior (convexHull ℝ {p, q, r}) := by
      rw [u4h_interior_hull3 hD]
      exact ⟨hy'.1, hy'.2, hgy⟩
    exact u4h_no_interior_point hD H1 H2 H3 _ (u4h_lin_mem_segment s t hy0 hy1) hyi

/-! ### `ZMod` index facts for `4 ≤ n` -/


theorem u4h_natCast_ne_zero {k : ℕ} (hk0 : 0 < k) (hk : k < n) : (k : ZMod n) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd hk0 h) (not_le.mpr hk)

theorem u4h_one_ne_zero (hn : 4 ≤ n) : (1 : ZMod n) ≠ 0 := by
  have := u4h_natCast_ne_zero (n := n) (k := 1) (by norm_num) (by omega)
  simpa using this

theorem u4h_two_ne_zero (hn : 4 ≤ n) : (2 : ZMod n) ≠ 0 := by
  have := u4h_natCast_ne_zero (n := n) (k := 2) (by norm_num) (by omega)
  simpa using this

theorem u4h_three_ne_zero (hn : 4 ≤ n) : (3 : ZMod n) ≠ 0 := by
  have := u4h_natCast_ne_zero (n := n) (k := 3) (by norm_num) (by omega)
  simpa using this

theorem u4h_adjacent_iff (i k : ZMod n) : adjacent i k ↔ k = i - 1 ∨ k = i ∨ k = i + 1 := by
  unfold adjacent
  constructor
  · rintro (h | h | h)
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (Or.inl (by linear_combination h))
    · exact Or.inr (Or.inr (by linear_combination h))
  · rintro (h | h | h)
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (Or.inl (by linear_combination h))
    · exact Or.inr (Or.inr (by linear_combination h))

/-- `i` and `i + 2` are remote when `4 ≤ n`. -/
theorem u4h_remote_add_two (hn : 4 ≤ n) (i : ZMod n) : remote i (i + 2) := by
  rw [remote, u4h_adjacent_iff]
  rintro (h | h | h)
  · exact u4h_three_ne_zero hn (by linear_combination h)
  · exact u4h_two_ne_zero hn (by linear_combination h)
  · exact u4h_one_ne_zero hn (by linear_combination h)

theorem u4h_remote_sub_two (hn : 4 ≤ n) (i : ZMod n) : remote i (i - 2) := by
  have := u4h_remote_add_two hn (i - 2)
  rw [sub_add_cancel] at this
  exact remote_symm this

end U4F_block

section U4G_block

/-! The ear criterion for an embedded polygon (U4 helpers): a vertex `j` whose closed ear
triangle contains no vertex other than `j-1, j, j+1` is a strict ear. -/

/-- No vertex of `P` other than `j - 1, j, j + 1` lies in the closed ear triangle at `j`. -/
def u4h_VertexEmpty (P : LabelledTuple n) (j : ZMod n) : Prop :=
  ∀ k, P k ∈ earHull P j → k = j - 1 ∨ k = j ∨ k = j + 1

theorem u4h_edgeSegment_prev (P : LabelledTuple n) (j : ZMod n) :
    edgeSegment P (j - 1) = segment ℝ (P (j - 1)) (P j) := by
  rw [u4h_edgeSegment_eq_segment, sub_add_cancel]

/-- (F1) a non-ear edge meets the two ear edges only in the base vertices. -/
theorem u4h_edge_inter_ears {P : LabelledTuple n} (hP : Embedded P) {j k : ZMod n}
    (hk1 : k ≠ j - 1) (hk2 : k ≠ j) :
    edgeSegment P k ∩ (edgeSegment P (j - 1) ∪ edgeSegment P j) ⊆ {P (j - 1), P (j + 1)} := by
  rintro x ⟨hxk, hx⟩
  rcases hx with hx | hx
  · by_cases hadj : adjacent k (j - 1)
    · rcases adjacent_distinct_cases hk1 hadj with h | h
      · have hmem : x ∈ edgeSegment P k ∩ edgeSegment P (k + 1) := ⟨hxk, by rw [← h]; exact hx⟩
        rw [hP.consecutive k] at hmem
        have hx' : x = P (k + 1) := hmem
        rw [hx', ← h]
        exact Set.mem_insert _ _
      · exact absurd (by rw [h, sub_add_cancel]) hk2
    · exact (Set.disjoint_left.mp (hP.remote_disjoint k (j - 1) hadj) hxk hx).elim
  · by_cases hadj : adjacent k j
    · rcases adjacent_distinct_cases hk2 hadj with h | h
      · exact absurd (by rw [h, add_sub_cancel_right]) hk1
      · have hmem : x ∈ edgeSegment P j ∩ edgeSegment P (j + 1) := ⟨hx, by rw [← h]; exact hxk⟩
        rw [hP.consecutive j] at hmem
        exact Set.mem_insert_of_mem _ hmem
    · exact (Set.disjoint_left.mp (hP.remote_disjoint k j hadj) hxk hx).elim

/-- (F4) a non-ear edge does not contain both base vertices. -/
theorem u4h_not_both_ends {P : LabelledTuple n} (hP : Embedded P) (hn : 4 ≤ n) {j k : ZMod n}
    (hk1 : k ≠ j - 1) (hk2 : k ≠ j) :
    ¬ (P (j - 1) ∈ edgeSegment P k ∧ P (j + 1) ∈ edgeSegment P k) := by
  rintro ⟨ha, hc⟩
  rcases u4h_incident_of_vertex_mem hP ha with h | h
  · exact hk1 h.symm
  · rcases u4h_incident_of_vertex_mem hP hc with h' | h'
    · exact u4h_three_ne_zero hn (by linear_combination h' - h)
    · exact hk2 (add_right_cancel h'.symm)

/-- The ear criterion, edge form: a non-ear edge meets the (vertex-empty, nondegenerate) ear
triangle only in the base vertices. -/
theorem u4h_edge_inter_earHull {P : LabelledTuple n} (hP : Embedded P) (hn : 4 ≤ n) {j : ZMod n}
    (hdet : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0) (hV : u4h_VertexEmpty P j)
    {k : ZMod n} (hk1 : k ≠ j - 1) (hk2 : k ≠ j) :
    edgeSegment P k ∩ earHull P j ⊆ {P (j - 1), P (j + 1)} := by
  have hE1 := u4h_edgeSegment_prev P j
  have hE2 := u4h_edgeSegment_eq_segment P j
  have hEk := u4h_edgeSegment_eq_segment P k
  have H1 := u4h_edge_inter_ears hP hk1 hk2
  have H5 := u4h_not_both_ends hP hn hk1 hk2
  have H2 : P k ∈ earHull P j → P k = P (j + 1) := fun h => by
    rcases hV k h with h1 | h1 | h1
    · exact absurd h1 hk1
    · exact absurd h1 hk2
    · rw [h1]
  have H3 : P (k + 1) ∈ earHull P j → P (k + 1) = P (j - 1) := fun h => by
    rcases hV (k + 1) h with h1 | h1 | h1
    · rw [h1]
    · exact absurd (by linear_combination h1) hk1
    · exact absurd (add_right_cancel h1) hk2
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · -- negative orientation: the positive triple is `(c, b, a)`
    have hD : 0 < det (P j - P (j + 1)) (P (j - 1) - P (j + 1)) := by
      have e : det (P j - P (j + 1)) (P (j - 1) - P (j + 1)) =
          -det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) := by
        simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
      rw [e]; linarith
    have hset : earHull P j = convexHull ℝ {P (j + 1), P j, P (j - 1)} := by
      unfold earHull
      congr 1
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    intro x hx
    rw [hset] at hx
    rw [hEk] at hx
    have hres := u4h_segment_inter_tri hD ?_ ?_ ?_ ?_ hx
    · rcases hres with h | h
      · exact Set.mem_insert_of_mem _ h
      · exact h ▸ Set.mem_insert _ _
    · intro y hy
      have hy' : y ∈ edgeSegment P k ∩ (edgeSegment P (j - 1) ∪ edgeSegment P j) := by
        rw [hEk, hE1, hE2, segment_symm ℝ (P (j - 1)) (P j), segment_symm ℝ (P j) (P (j + 1))]
        exact ⟨hy.1, hy.2.symm⟩
      rcases H1 hy' with h | h
      · exact Set.mem_insert_of_mem _ h
      · exact h ▸ Set.mem_insert _ _
    · intro h
      exact Or.inl (H2 (by rw [hset]; exact h))
    · intro h
      exact Or.inr (H3 (by rw [hset]; exact h))
    · rintro ⟨h1, h2⟩
      exact H5 ⟨by rw [hEk]; exact h2, by rw [hEk]; exact h1⟩
  · -- positive orientation: the positive triple is `(a, b, c)`
    intro x hx
    unfold earHull at hx
    rw [hEk] at hx
    have hres := u4h_segment_inter_tri hpos ?_ ?_ ?_ ?_ hx
    · exact hres
    · intro y hy
      have hy' : y ∈ edgeSegment P k ∩ (edgeSegment P (j - 1) ∪ edgeSegment P j) := by
        rw [hEk, hE1, hE2]
        exact hy
      exact H1 hy'
    · intro h
      exact Or.inr (H2 h)
    · intro h
      exact Or.inl (H3 h)
    · rintro ⟨h1, h2⟩
      exact H5 ⟨by rw [hEk]; exact h1, by rw [hEk]; exact h2⟩

/-- Ear edges lie in the ear triangle. -/
theorem u4h_ear_edges_subset (P : LabelledTuple n) (j : ZMod n) :
    edgeSegment P (j - 1) ∪ edgeSegment P j ⊆ earHull P j := by
  rintro x (h | h)
  · rw [u4h_edgeSegment_prev] at h
    exact u4h_segment_subset_hull3 _ _ _ h
  · rw [u4h_edgeSegment_eq_segment] at h
    unfold earHull
    rw [u4h_hull3_rot]
    exact u4h_segment_subset_hull3 _ _ _ h

/-- **Ear criterion**: a vertex-empty nondegenerate ear triangle meets the polygon exactly in the
two ear edges. -/
theorem u4h_strict_ear_of_vertex_empty {P : LabelledTuple n} (hP : Embedded P) (hn : 4 ≤ n)
    {j : ZMod n} (hdet : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0)
    (hV : u4h_VertexEmpty P j) :
    earHull P j ∩ polygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxT, hxC⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxC
    by_cases hk1 : k = j - 1
    · exact Or.inl (hk1 ▸ hk)
    by_cases hk2 : k = j
    · exact Or.inr (hk2 ▸ hk)
    rcases u4h_edge_inter_earHull hP hn hdet hV hk1 hk2 ⟨hk, hxT⟩ with h | h
    · rw [h]; exact Or.inl (u4h_start_mem_edgeSegment P (j - 1))
    · rw [h]; exact Or.inr (u4h_end_mem_edgeSegment P j)
  · intro x hx
    refine ⟨u4h_ear_edges_subset P j hx, ?_⟩
    rcases hx with h | h
    · exact u4h_edgeSegment_subset_polygonImage P _ h
    · exact u4h_edgeSegment_subset_polygonImage P _ h

end U4G_block

section U4H_block

variable [NeZero n]

/-! Edges and polygon image of `deleteVertex` (U4 helpers). -/

theorem u4h_edgeSegment_deleteVertex (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) {i : ZMod n}
    (hi : i ≠ -1) : edgeSegment (deleteVertex P j) i = edgeSegment P (deletionIndex j i) := by
  simp only [edgeSegment, edgePoint_deleteVertex P j hi]

theorem u4h_edgeSegment_deleteVertex_last (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) :
    edgeSegment (deleteVertex P j) (-1) = segment ℝ (P (j - 1)) (P (j + 1)) := by
  rw [u4h_edgeSegment_eq_segment, neg_add_cancel, deleteVertex_last, deleteVertex_zero]

theorem u4h_deletionIndex_ne_prev_or_last (j : ZMod (n + 1)) (i : ZMod n) :
    deletionIndex j i ≠ j ∧ (i ≠ -1 → deletionIndex j i ≠ j - 1) :=
  ⟨deletionIndex_ne_deleted j i, fun hi => deletionIndex_ne_prev j hi⟩

/-- Membership in the polygon image of the cut polygon. -/
theorem u4h_mem_polygonImage_deleteVertex (P : LabelledTuple (n + 1)) (j : ZMod (n + 1))
    (x : Plane) :
    x ∈ polygonImage (deleteVertex P j) ↔
      (∃ k, k ≠ j - 1 ∧ k ≠ j ∧ x ∈ edgeSegment P k) ∨ x ∈ segment ℝ (P (j - 1)) (P (j + 1)) := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    by_cases hi1 : i = -1
    · subst hi1
      rw [u4h_edgeSegment_deleteVertex_last] at hi
      exact Or.inr hi
    · rw [u4h_edgeSegment_deleteVertex P j hi1] at hi
      exact Or.inl ⟨_, deletionIndex_ne_prev j hi1, deletionIndex_ne_deleted j i, hi⟩
  · rintro (⟨k, hk1, hk2, hk⟩ | hx)
    · obtain ⟨i, rfl⟩ := deletionIndex_exhaust j hk2
      have hi1 : i ≠ -1 := by
        rintro rfl
        exact hk1 (deletionIndex_last j)
      exact Set.mem_iUnion.mpr ⟨i, by rw [u4h_edgeSegment_deleteVertex P j hi1]; exact hk⟩
    · exact Set.mem_iUnion.mpr ⟨-1, by rw [u4h_edgeSegment_deleteVertex_last]; exact hx⟩

omit [NeZero n] in
theorem u4h_diag_subset_earHull (P : LabelledTuple n) (j : ZMod n) :
    segment ℝ (P (j - 1)) (P (j + 1)) ⊆ earHull P j := by
  unfold earHull
  rw [u4h_hull3_rot, u4h_hull3_rot, segment_symm]
  exact u4h_segment_subset_hull3 _ _ _

/-- A strict ear meets the cut polygon exactly in the diagonal. -/
theorem u4h_earHull_inter_polygonImage_delete {P : LabelledTuple (n + 1)} (hP : Embedded P)
    {j : ZMod (n + 1)}
    (hstrict : earHull P j ∩ polygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j) :
    earHull P j ∩ polygonImage (deleteVertex P j) = segment ℝ (P (j - 1)) (P (j + 1)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxT, hxC⟩
    rcases (u4h_mem_polygonImage_deleteVertex P j x).mp hxC with ⟨k, hk1, hk2, hk⟩ | hx
    · have hx' : x ∈ edgeSegment P (j - 1) ∪ edgeSegment P j := by
        rw [← hstrict]
        exact ⟨hxT, u4h_edgeSegment_subset_polygonImage P k hk⟩
      rcases u4h_edge_inter_ears hP hk1 hk2 ⟨hk, hx'⟩ with h | h
      · rw [h]; exact left_mem_segment ℝ _ _
      · rw [h]; exact right_mem_segment ℝ _ _
    · exact hx
  · intro x hx
    exact ⟨u4h_diag_subset_earHull P j hx,
      (u4h_mem_polygonImage_deleteVertex P j x).mpr (Or.inr hx)⟩

omit [NeZero n] in
/-- Points of a non-ear edge are not on the open diagonal (strict ear, `a ≠ c`). -/
theorem u4h_edge_disjoint_openDiag {P : LabelledTuple (n + 1)} (hP : Embedded P)
    {j : ZMod (n + 1)} (hac : P (j - 1) ≠ P (j + 1))
    (hstrict : earHull P j ∩ polygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j)
    {k : ZMod (n + 1)} (hk1 : k ≠ j - 1) (hk2 : k ≠ j) {x : Plane} (hk : x ∈ edgeSegment P k) :
    x ∉ openSegment ℝ (P (j - 1)) (P (j + 1)) := by
  intro hxo
  have hxT : x ∈ earHull P j :=
    u4h_diag_subset_earHull P j (openSegment_subset_segment ℝ _ _ hxo)
  have hx' : x ∈ edgeSegment P (j - 1) ∪ edgeSegment P j := by
    rw [← hstrict]
    exact ⟨hxT, u4h_edgeSegment_subset_polygonImage P k hk⟩
  rcases u4h_edge_inter_ears hP hk1 hk2 ⟨hk, hx'⟩ with h | h
  · rw [h] at hxo
    exact hac (left_mem_openSegment_iff.mp hxo)
  · rw [h] at hxo
    exact hac (right_mem_openSegment_iff.mp hxo)

/-- The ear-cut identity for the polygon image (the corrected form of `U4_polygonImage_ear`:
it needs `P` embedded, `j` a strict ear and `P (j-1) ≠ P (j+1)`). -/
theorem u4h_polygonImage_ear {P : LabelledTuple (n + 1)} (hP : Embedded P) {j : ZMod (n + 1)}
    (hac : P (j - 1) ≠ P (j + 1))
    (hstrict : earHull P j ∩ polygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j) :
    polygonImage P = (polygonImage (deleteVertex P j) \ openSegment ℝ (P (j - 1)) (P (j + 1))) ∪
      edgeSegment P (j - 1) ∪ edgeSegment P j := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    by_cases hk1 : k = j - 1
    · exact Or.inl (Or.inr (hk1 ▸ hk))
    by_cases hk2 : k = j
    · exact Or.inr (hk2 ▸ hk)
    refine Or.inl (Or.inl ⟨?_, u4h_edge_disjoint_openDiag hP hac hstrict hk1 hk2 hk⟩)
    exact (u4h_mem_polygonImage_deleteVertex P j x).mpr (Or.inl ⟨k, hk1, hk2, hk⟩)
  · rintro x ((⟨hxC, hxo⟩ | hx) | hx)
    · rcases (u4h_mem_polygonImage_deleteVertex P j x).mp hxC with ⟨k, -, -, hk⟩ | hxD
      · exact u4h_edgeSegment_subset_polygonImage P k hk
      · -- on the closed diagonal but not the open one: an endpoint
        rw [← insert_endpoints_openSegment] at hxD
        rcases hxD with h | h | h
        · rw [h]; exact u4h_vertex_mem_polygonImage P _
        · rw [h]; exact u4h_vertex_mem_polygonImage P _
        · exact absurd h hxo
    · exact u4h_edgeSegment_subset_polygonImage P _ hx
    · exact u4h_edgeSegment_subset_polygonImage P _ hx

end U4H_block

section U4I_block

/-! `deleteVertex` at a strict ear is embedded (U4 helpers). -/

theorem u4h_one_ne_zero' (hn : 2 ≤ n) : (1 : ZMod n) ≠ 0 := by
  have := u4h_natCast_ne_zero (n := n) (k := 1) (by norm_num) (by omega)
  simpa using this

theorem u4h_two_ne_zero' (hn : 3 ≤ n) : (2 : ZMod n) ≠ 0 := by
  have := u4h_natCast_ne_zero (n := n) (k := 2) (by norm_num) (by omega)
  simpa using this

theorem u4h_deletionIndex_neg_two [NeZero n] (hn : 2 ≤ n) (j : ZMod (n + 1)) :
    deletionIndex j (-2) = j - 2 := by
  have h2 : (-2 : ZMod n) ≠ -1 := fun h => u4h_one_ne_zero' hn (by linear_combination -h)
  have h := deletionIndex_next j h2
  rw [show (-2 : ZMod n) + 1 = -1 by ring, deletionIndex_last] at h
  linear_combination -h

/-- A non-ear edge meets the diagonal only in the base vertices (strict ear). -/
theorem u4h_edge_inter_diag {P : LabelledTuple n} (hP : Embedded P) {j : ZMod n}
    (hstrict : earHull P j ∩ polygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j)
    {k : ZMod n} (hk1 : k ≠ j - 1) (hk2 : k ≠ j) :
    edgeSegment P k ∩ segment ℝ (P (j - 1)) (P (j + 1)) ⊆ {P (j - 1), P (j + 1)} := by
  rintro x ⟨hk, hD⟩
  have hx' : x ∈ edgeSegment P (j - 1) ∪ edgeSegment P j := by
    rw [← hstrict]
    exact ⟨u4h_diag_subset_earHull P j hD, u4h_edgeSegment_subset_polygonImage P k hk⟩
  exact u4h_edge_inter_ears hP hk1 hk2 ⟨hk, hx'⟩

theorem u4h_eq_sub_two_of_mem {P : LabelledTuple n} (hP : Embedded P) {j k : ZMod n}
    (hk1 : k ≠ j - 1) (h : P (j - 1) ∈ edgeSegment P k) : k = j - 2 := by
  rcases u4h_incident_of_vertex_mem hP h with h' | h'
  · exact absurd h'.symm hk1
  · linear_combination -h'

theorem u4h_eq_add_one_of_mem {P : LabelledTuple n} (hP : Embedded P) {j k : ZMod n}
    (hk2 : k ≠ j) (h : P (j + 1) ∈ edgeSegment P k) : k = j + 1 := by
  rcases u4h_incident_of_vertex_mem hP h with h' | h'
  · exact h'.symm
  · exact absurd (add_right_cancel h').symm hk2

/-- **Cutting a strict ear keeps the polygon embedded.** -/
theorem u4h_embedded_deleteVertex [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple (n + 1)}
    (hP : Embedded P) {j : ZMod (n + 1)} (hac : P (j - 1) ≠ P (j + 1))
    (hstrict : earHull P j ∩ polygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j) :
    Embedded (deleteVertex P j) := by
  have hn4 : 4 ≤ n + 1 := by omega
  have h1n : (1 : ZMod n) ≠ 0 := u4h_one_ne_zero' (by omega)
  have h2n1 : (2 : ZMod (n + 1)) ≠ 0 := u4h_two_ne_zero hn4
  have h3n1 : (3 : ZMod (n + 1)) ≠ 0 := u4h_three_ne_zero hn4
  -- the two non-ear edges at the base vertices
  have hj2_1 : j - 2 ≠ j - 1 := fun h => u4h_one_ne_zero hn4 (by linear_combination -h)
  have hj2_2 : j - 2 ≠ j := fun h => h2n1 (by linear_combination -h)
  have hj1_1 : j + 1 ≠ j - 1 := fun h => h2n1 (by linear_combination h)
  have hj1_2 : j + 1 ≠ j := fun h => u4h_one_ne_zero hn4 (by linear_combination h)
  -- a non-ear edge of `P` is disjoint from the diagonal unless it ends at `a` or starts at `c`
  have hdisj : ∀ k, k ≠ j - 1 → k ≠ j → k ≠ j - 2 → k ≠ j + 1 →
      Disjoint (edgeSegment P k) (segment ℝ (P (j - 1)) (P (j + 1))) := by
    intro k hk1 hk2 hk3 hk4
    rw [Set.disjoint_left]
    intro x hxk hxD
    rcases u4h_edge_inter_diag hP hstrict hk1 hk2 ⟨hxk, hxD⟩ with h | h
    · exact hk3 (u4h_eq_sub_two_of_mem hP hk1 (h ▸ hxk))
    · exact hk4 (u4h_eq_add_one_of_mem hP hk2 (h ▸ hxk))
  refine ⟨fun i => ?_, fun i i' hr => ?_, fun i => ?_⟩
  · by_cases hi : i = -1
    · subst hi
      rw [edge_deleteVertex_last]
      exact sub_ne_zero.mpr (Ne.symm hac)
    · rw [edge_deleteVertex P j hi]
      exact hP.edge_ne_zero _
  · -- remote pairs
    have hadj_self : ∀ i : ZMod n, adjacent i i := fun i => Or.inr (Or.inl (sub_self i))
    by_cases hi : i = -1
    · subst hi
      have hi' : i' ≠ -1 := fun h => hr (h ▸ hadj_self _)
      rw [u4h_edgeSegment_deleteVertex_last, u4h_edgeSegment_deleteVertex P j hi']
      refine (hdisj _ (deletionIndex_ne_prev j hi') (deletionIndex_ne_deleted j i') ?_ ?_).symm
      · intro h
        rw [← u4h_deletionIndex_neg_two (by omega) j] at h
        have := deletionIndex_injective j h
        exact hr (by rw [u4h_adjacent_iff]; exact Or.inl (by rw [this]; ring))
      · intro h
        rw [← deletionIndex_zero j] at h
        have := deletionIndex_injective j h
        exact hr (by rw [this]; exact Or.inr (Or.inr (by ring)))
    · by_cases hi' : i' = -1
      · subst hi'
        rw [u4h_edgeSegment_deleteVertex_last, u4h_edgeSegment_deleteVertex P j hi]
        refine hdisj _ (deletionIndex_ne_prev j hi) (deletionIndex_ne_deleted j i) ?_ ?_
        · intro h
          rw [← u4h_deletionIndex_neg_two (by omega) j] at h
          have := deletionIndex_injective j h
          exact hr (by rw [this]; exact Or.inr (Or.inr (by ring)))
        · intro h
          rw [← deletionIndex_zero j] at h
          have := deletionIndex_injective j h
          exact hr (by rw [this]; exact Or.inl (by ring))
      · rw [u4h_edgeSegment_deleteVertex P j hi, u4h_edgeSegment_deleteVertex P j hi']
        apply hP.remote_disjoint
        rw [remote, u4h_adjacent_iff]
        rintro (h | h | h)
        · rw [eq_sub_iff_add_eq, ← deletionIndex_next j hi'] at h
          have := deletionIndex_injective j h
          exact hr (Or.inl (by linear_combination this))
        · exact hr (deletionIndex_injective j h ▸ hadj_self i)
        · rw [← deletionIndex_next j hi] at h
          have := deletionIndex_injective j h
          exact hr (Or.inr (Or.inr (by linear_combination this)))
  · -- consecutive pairs
    by_cases hi : i = -1
    · subst hi
      have h0 : (0 : ZMod n) ≠ -1 := fun h => h1n (by linear_combination h)
      rw [neg_add_cancel, u4h_edgeSegment_deleteVertex_last, u4h_edgeSegment_deleteVertex P j h0,
        deletionIndex_zero, deleteVertex_zero]
      ext x
      constructor
      · rintro ⟨hxD, hxk⟩
        rcases u4h_edge_inter_diag hP hstrict hj1_1 hj1_2 ⟨hxk, hxD⟩ with h | h
        · exfalso
          have := u4h_eq_sub_two_of_mem hP hj1_1 (h ▸ hxk)
          exact h3n1 (by linear_combination this)
        · exact h
      · intro hx
        have hx' : x = P (j + 1) := hx
        rw [hx']
        exact ⟨right_mem_segment ℝ _ _, u4h_start_mem_edgeSegment P (j + 1)⟩
    · by_cases hi1 : i + 1 = -1
      · have hi2 : i = -2 := by linear_combination hi1
        rw [hi1, u4h_edgeSegment_deleteVertex_last, u4h_edgeSegment_deleteVertex P j hi,
          deleteVertex_last, hi2, u4h_deletionIndex_neg_two (by omega) j]
        ext x
        constructor
        · rintro ⟨hxk, hxD⟩
          rcases u4h_edge_inter_diag hP hstrict hj2_1 hj2_2 ⟨hxk, hxD⟩ with h | h
          · exact h
          · exfalso
            have := u4h_eq_add_one_of_mem hP hj2_2 (h ▸ hxk)
            exact h3n1 (by linear_combination -this)
        · intro hx
          have hx' : x = P (j - 1) := hx
          rw [hx']
          refine ⟨?_, left_mem_segment ℝ _ _⟩
          have := u4h_end_mem_edgeSegment P (j - 2)
          rwa [show j - 2 + 1 = j - 1 by ring] at this
      · rw [u4h_edgeSegment_deleteVertex P j hi, u4h_edgeSegment_deleteVertex P j hi1,
          deletionIndex_next j hi, deleteVertex_apply, deletionIndex_next j hi]
        exact hP.consecutive _

end U4I_block

section U4J_block

/-! `Triangle` vertex facts and sub-face intersections (U4 helpers). -/

theorem u4h_tri_pos (T : Triangle) (k : Fin 3) :
    0 < det (T.v (k + 1) - T.v k) (T.v (k + 2) - T.v k) := by
  have h := T.pos
  fin_cases k
  · simpa using h
  · show 0 < det (T.v 2 - T.v 1) (T.v 0 - T.v 1)
    rw [u4h_det_rot1]; exact h
  · show 0 < det (T.v 0 - T.v 2) (T.v 1 - T.v 2)
    rw [u4h_det_rot2]; exact h

theorem u4h_tri_range_rot (T : Triangle) (k : Fin 3) :
    Set.range T.v = {T.v k, T.v (k + 1), T.v (k + 2)} := by
  rw [u4h_range_fin3]
  fin_cases k
  · rfl
  · show ({T.v 0, T.v 1, T.v 2} : Set Plane) = {T.v 1, T.v 2, T.v 0}
    exact u4h_hull3_rot_set _ _ _
  · show ({T.v 0, T.v 1, T.v 2} : Set Plane) = {T.v 2, T.v 0, T.v 1}
    rw [u4h_hull3_rot_set, u4h_hull3_rot_set]
where
  u4h_hull3_rot_set (a b c : Plane) : ({a, b, c} : Set Plane) = {b, c, a} := by
    rw [Set.insert_comm, Set.pair_comm]

theorem u4h_tri_carrier_rot (T : Triangle) (k : Fin 3) :
    T.carrier = convexHull ℝ {T.v k, T.v (k + 1), T.v (k + 2)} := by
  rw [Triangle.carrier, u4h_tri_range_rot T k]

theorem u4h_tri_edgeSeg_subset (T : Triangle) (k : Fin 3) : T.edgeSeg k ⊆ T.carrier := by
  rw [u4h_tri_carrier_rot T k]
  exact u4h_segment_subset_hull3 _ _ _

theorem u4h_tri_ne (T : Triangle) (k : Fin 3) : T.v k ≠ T.v (k + 1) := by
  intro h
  have := u4h_tri_pos T k
  rw [← h, sub_self] at this
  simp [det] at this

theorem u4h_tri_ne' (T : Triangle) (k : Fin 3) : T.v k ≠ T.v (k + 2) := by
  intro h
  have := u4h_tri_pos T k
  rw [← h, sub_self] at this
  simp [det] at this

theorem u4h_tri_injective (T : Triangle) : Function.Injective T.v := by
  intro i j hij
  by_contra hne
  fin_cases i <;> fin_cases j
  all_goals first
    | exact hne rfl
    | exact u4h_tri_ne T _ hij
    | exact u4h_tri_ne' T _ hij

/-- The apex `T.v (k+2)` is not on the line of the edge `k`. -/
theorem u4h_tri_apex_not_mem_edge (T : Triangle) (k : Fin 3) :
    T.v (k + 2) ∉ segment ℝ (T.v k) (T.v (k + 1)) := by
  intro h
  have := u4h_det_segment_zero h
  have hp := u4h_tri_pos T k
  rw [this] at hp
  exact lt_irrefl _ hp

/-- Sub-face lemma: for `W` a set of vertices of `T`, `hull W ∩ edge k = hull (W ∩ {ends of edge k})`. -/
theorem u4h_hull_inter_edge (T : Triangle) (k : Fin 3) {W : Set Plane}
    (hW : W ⊆ {T.v k, T.v (k + 1), T.v (k + 2)}) :
    convexHull ℝ W ∩ segment ℝ (T.v k) (T.v (k + 1)) =
      convexHull ℝ (W ∩ {T.v k, T.v (k + 1)}) := by
  set a := T.v k
  set b := T.v (k + 1)
  set c := T.v (k + 2)
  have hcab : c ∉ segment ℝ a b := u4h_tri_apex_not_mem_edge T k
  by_cases hc : c ∈ W
  · -- `W = insert c W0` with `W0 ⊆ {a, b}`
    set W0 := W ∩ {a, b} with hW0
    have hWeq : W = insert c W0 := by
      ext x
      constructor
      · intro hx
        rcases hW hx with h | h | h
        · exact Or.inr ⟨hx, Or.inl h⟩
        · exact Or.inr ⟨hx, Or.inr h⟩
        · exact Or.inl h
      · rintro (h | h)
        · rw [h]; exact hc
        · exact h.1
    apply Set.Subset.antisymm
    · rintro x ⟨hxW, hxe⟩
      by_cases hW0e : W0.Nonempty
      · rw [hWeq, convexHull_insert hW0e, mem_convexJoin] at hxW
        obtain ⟨c', hc', y, hy, hxy⟩ := hxW
        rw [Set.mem_singleton_iff] at hc'
        subst hc'
        rw [u4h_mem_segment_iff_lin] at hxy
        obtain ⟨l, hl0, hl1, rfl⟩ := hxy
        -- the edge determinant vanishes at `x` and at `y`, so `x = y` unless `l = 1`
        have hyW : y ∈ segment ℝ a b := by
          have : convexHull ℝ W0 ⊆ segment ℝ a b := by
            rw [← convexHull_pair]
            exact convexHull_mono Set.inter_subset_right
          exact this hy
        have hgx := u4h_det_segment_zero hxe
        have hgy := u4h_det_segment_zero hyW
        have hgc : det (b - a) (c - a) ≠ 0 := (u4h_tri_pos T k).ne'
        rw [u4h_det_lin] at hgx
        have hl : l = 1 := by
          have e : det (b - a) (y - c) = det (b - a) (y - a) - det (b - a) (c - a) := by
            simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
          rw [e, hgy] at hgx
          have h1 : (1 - l) * det (b - a) (c - a) = 0 := by linear_combination hgx
          rcases mul_eq_zero.mp h1 with h | h
          · linarith
          · exact absurd h hgc
        rw [hl, one_smul, add_sub_cancel]
        exact hy
      · rw [Set.not_nonempty_iff_eq_empty] at hW0e
        have hW1 : convexHull ℝ W = {c} := by
          rw [hWeq, hW0e]
          have : (insert c (∅ : Set Plane)) = {c} := by ext; simp
          rw [this]
          exact convexHull_singleton (𝕜 := ℝ) c
        rw [hW1, Set.mem_singleton_iff] at hxW
        rw [hxW] at hxe
        exact absurd hxe hcab
    · intro x hx
      refine ⟨convexHull_mono Set.inter_subset_left hx, ?_⟩
      rw [← convexHull_pair]
      exact convexHull_mono Set.inter_subset_right hx
  · have hWeq : W = W ∩ {a, b} := by
      ext x
      constructor
      · intro hx
        rcases hW hx with h | h | h
        · exact ⟨hx, Or.inl h⟩
        · exact ⟨hx, Or.inr h⟩
        · exact absurd (h ▸ hx) hc
      · exact fun h => h.1
    rw [← hWeq]
    apply Set.Subset.antisymm
    · exact Set.inter_subset_left
    · intro x hx
      refine ⟨hx, ?_⟩
      rw [← convexHull_pair]
      exact convexHull_mono (by rw [hWeq]; exact Set.inter_subset_right) hx

/-- A vertex of `T` lying in the hull of a set of vertices belongs to that set. -/
theorem u4h_vertex_mem_hull_iff (T : Triangle) {W : Set Plane} (hW : W ⊆ Set.range T.v)
    (j : Fin 3) : T.v j ∈ convexHull ℝ W ↔ T.v j ∈ W := by
  refine ⟨fun h => ?_, fun h => subset_convexHull ℝ W h⟩
  by_contra hj
  -- `W ⊆ {T.v (j+1), T.v (j+2)}`, so `T.v j` would lie on the opposite edge
  have hW' : W ⊆ {T.v (j + 1), T.v (j + 1 + 1)} := by
    intro x hx
    rw [u4h_tri_range_rot T (j + 1)] at hW
    rcases hW hx with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso
      rw [show j + 1 + 2 = j by fin_cases j <;> rfl] at h1
      exact hj (h1 ▸ hx)
  have hsub : convexHull ℝ W ⊆ segment ℝ (T.v (j + 1)) (T.v (j + 1 + 1)) := by
    rw [← convexHull_pair]; exact convexHull_mono hW'
  have := u4h_tri_apex_not_mem_edge T (j + 1)
  rw [show j + 1 + 2 = j by fin_cases j <;> rfl] at this
  exact this (hsub h)

end U4J_block

section U4K_block

/-! Gluing two triangulations along a common face-edge (U4 helpers). -/

theorem u4h_carrier_subset {X : Set Plane} (K : Triangulation X) {T : Triangle}
    (hT : T ∈ K.faces) : T.carrier ⊆ X := by
  rw [← K.cover]
  exact Set.subset_biUnion_of_mem (u := fun T : Triangle => T.carrier) hT

/-- The endpoints of a nondegenerate segment are determined by the segment. -/
theorem u4h_segment_endpoints {a b c d : Plane} (hab : a ≠ b)
    (h : segment ℝ a b = segment ℝ c d) : ({a, b} : Set Plane) = {c, d} := by
  have hc : c ∈ segment ℝ a b := h ▸ left_mem_segment ℝ c d
  have hd : d ∈ segment ℝ a b := h ▸ right_mem_segment ℝ c d
  have ha : a ∈ segment ℝ c d := h ▸ left_mem_segment ℝ a b
  have hb : b ∈ segment ℝ c d := h ▸ right_mem_segment ℝ a b
  obtain ⟨u, hu0, hu1, rfl⟩ := (u4h_mem_segment_iff_lin a b c).mp hc
  obtain ⟨w, hw0, hw1, rfl⟩ := (u4h_mem_segment_iff_lin a b d).mp hd
  obtain ⟨s, hs0, hs1, has⟩ := (u4h_mem_segment_iff_lin _ _ a).mp ha
  obtain ⟨t, ht0, ht1, hbt⟩ := (u4h_mem_segment_iff_lin _ _ b).mp hb
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  -- `a = a + (u + s (w - u)) • (b - a)` forces `u + s (w - u) = 0`
  have e1 : (u + s * (w - u)) • (b - a) = 0 := by
    have : a + (u + s * (w - u)) • (b - a) = a := by
      conv_rhs => rw [has]
      module
    exact add_eq_left.mp this
  have e2 : (u + t * (w - u)) • (b - a) = (1 : ℝ) • (b - a) := by
    have : a + (u + t * (w - u)) • (b - a) = a + (1 : ℝ) • (b - a) := by
      rw [one_smul, add_sub_cancel]
      conv_rhs => rw [hbt]
      module
    exact add_left_cancel this
  have k1 : u + s * (w - u) = 0 := by
    rcases smul_eq_zero.mp e1 with h | h
    · exact h
    · exact absurd h hba
  have k2 : u + t * (w - u) = 1 := smul_left_injective ℝ hba e2
  -- from `k1`, `k2`: `u = 0 ∧ w = 1` or `u = 1 ∧ w = 0`
  have hcases : (u = 0 ∧ w = 1) ∨ (u = 1 ∧ w = 0) := by
    by_cases hu : u = 0
    · subst hu
      left
      refine ⟨rfl, ?_⟩
      have k2' : t * w = 1 := by linarith
      nlinarith [mul_le_of_le_one_left hw0 ht1]
    · right
      have hwu : w < u := by
        by_contra hc
        have hc' : u ≤ w := not_lt.mp hc
        have : 0 ≤ s * (w - u) := mul_nonneg hs0 (by linarith)
        have : u ≤ 0 := by linarith
        exact hu (le_antisymm this hu0)
      have hu1' : u = 1 := by
        have : t * (w - u) ≤ 0 := by nlinarith
        linarith
      subst hu1'
      refine ⟨rfl, ?_⟩
      have h1 : s * (1 - w) = 1 := by linarith
      nlinarith [mul_le_of_le_one_left (by linarith : (0 : ℝ) ≤ 1 - w) hs1]
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp
  · simp only [one_smul, add_sub_cancel, zero_smul, add_zero]
    exact Set.pair_comm a b

/-- Intersection of hulls of subsets of a two-point set `{e1, e2}` lying among the vertices of a
triangle `F` (edge `k`). -/
theorem u4h_hull_inter_pair (F : Triangle) (k : Fin 3) {A A' : Set Plane}
    (hA : A ⊆ {F.v k, F.v (k + 1)}) (hA' : A' ⊆ {F.v k, F.v (k + 1)}) :
    convexHull ℝ A ∩ convexHull ℝ A' = convexHull ℝ (A ∩ A') := by
  have hpair3 : ({F.v k, F.v (k + 1)} : Set Plane) ⊆ {F.v k, F.v (k + 1), F.v (k + 2)} := by
    rintro x (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hAr : A ⊆ Set.range F.v := hA.trans (by rw [u4h_tri_range_rot F k]; exact hpair3)
  have hA3 : A ⊆ {F.v k, F.v (k + 1), F.v (k + 2)} := hA.trans hpair3
  have hne : F.v k ≠ F.v (k + 1) := u4h_tri_ne F k
  -- describe `A'` by which endpoints it contains
  have key : ∀ x, x ∈ A' → x = F.v k ∨ x = F.v (k + 1) := fun x hx => hA' hx
  by_cases h1 : F.v k ∈ A' <;> by_cases h2 : F.v (k + 1) ∈ A'
  · -- `A' = {F.v k, F.v (k+1)}`
    have hA'eq : A' = {F.v k, F.v (k + 1)} := by
      apply Set.Subset.antisymm hA'
      rintro x (rfl | rfl)
      · exact h1
      · exact h2
    rw [hA'eq, convexHull_pair, u4h_hull_inter_edge F k hA3]
  · have hA'eq : A' = {F.v k} := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases key x hx with h | h
        · exact h
        · exact absurd (h ▸ hx) h2
      · rintro x rfl; exact h1
    rw [hA'eq, convexHull_singleton]
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      rw [Set.mem_singleton_iff] at hx'
      subst hx'
      have := (u4h_vertex_mem_hull_iff F hAr k).mp hx
      exact subset_convexHull ℝ _ ⟨this, rfl⟩
    · intro hx
      have := convexHull_mono (Set.inter_subset_right (s := A)) hx
      rw [convexHull_singleton] at this
      exact ⟨convexHull_mono Set.inter_subset_left hx, this⟩
  · have hA'eq : A' = {F.v (k + 1)} := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases key x hx with h | h
        · exact absurd (h ▸ hx) h1
        · exact h
      · rintro x rfl; exact h2
    rw [hA'eq, convexHull_singleton]
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      rw [Set.mem_singleton_iff] at hx'
      subst hx'
      have := (u4h_vertex_mem_hull_iff F hAr (k + 1)).mp hx
      exact subset_convexHull ℝ _ ⟨this, rfl⟩
    · intro hx
      have := convexHull_mono (Set.inter_subset_right (s := A)) hx
      rw [convexHull_singleton] at this
      exact ⟨convexHull_mono Set.inter_subset_left hx, this⟩
  · have hA'eq : A' = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro x hx
      rcases key x hx with h | h
      · exact h1 (h ▸ hx)
      · exact h2 (h ▸ hx)
    rw [hA'eq, Set.inter_empty, convexHull_empty, Set.inter_empty]

/-- Sub-lemma A: a face `T` of `K` meets the edge `k` of another face `F` of `K` in the hull of
the vertices of `T` among that edge's endpoints. -/
theorem u4h_face_inter_edge {X : Set Plane} (K : Triangulation X) {T F : Triangle}
    (hT : T ∈ K.faces) (hF : F ∈ K.faces) (k : Fin 3) :
    T.carrier ∩ F.edgeSeg k = convexHull ℝ (Set.range T.v ∩ {F.v k, F.v (k + 1)}) := by
  have hW : Set.range T.v ∩ Set.range F.v ⊆ {F.v k, F.v (k + 1), F.v (k + 2)} := by
    rw [← u4h_tri_range_rot F k]; exact Set.inter_subset_right
  have e1 : T.carrier ∩ F.edgeSeg k =
      convexHull ℝ (Set.range T.v ∩ Set.range F.v) ∩ F.edgeSeg k := by
    apply Set.Subset.antisymm
    · rintro x ⟨hx, hxe⟩
      refine ⟨?_, hxe⟩
      rw [← K.inter T hT F hF]
      exact ⟨hx, u4h_tri_edgeSeg_subset F k hxe⟩
    · rintro x ⟨hx, hxe⟩
      exact ⟨convexHull_mono Set.inter_subset_left hx, hxe⟩
  rw [e1, Triangle.edgeSeg, u4h_hull_inter_edge F k hW]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, ?_⟩, h2⟩
    rw [u4h_tri_range_rot F k]
    rcases h2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end U4K_block

section U4L_block

/-! The glued triangulation and the region-data structure (U4 helpers). -/

theorem u4h_glue_inter {U1 U2 : Set Plane} (K1 : Triangulation U1) (K2 : Triangulation U2)
    {F1 : Triangle} (hF1 : F1 ∈ K1.faces) (k1 : Fin 3)
    {F2 : Triangle} (hF2 : F2 ∈ K2.faces) (k2 : Fin 3)
    (hedge : F2.edgeSeg k2 = F1.edgeSeg k1) (hinter : U1 ∩ U2 = F1.edgeSeg k1)
    {T T' : Triangle} (hT : T ∈ K1.faces) (hT' : T' ∈ K2.faces) :
    T.carrier ∩ T'.carrier = convexHull ℝ (Set.range T.v ∩ Set.range T'.v) := by
  have hends : ({F2.v k2, F2.v (k2 + 1)} : Set Plane) = {F1.v k1, F1.v (k1 + 1)} :=
    u4h_segment_endpoints (u4h_tri_ne F2 k2) hedge
  have hTe := u4h_face_inter_edge K1 hT hF1 k1
  have hT'e : T'.carrier ∩ F1.edgeSeg k1 =
      convexHull ℝ (Set.range T'.v ∩ {F1.v k1, F1.v (k1 + 1)}) := by
    rw [← hedge, u4h_face_inter_edge K2 hT' hF2 k2, hends]
  have hsub : T.carrier ∩ T'.carrier ⊆ F1.edgeSeg k1 := by
    rw [← hinter]
    exact Set.inter_subset_inter (u4h_carrier_subset K1 hT) (u4h_carrier_subset K2 hT')
  have e1 : T.carrier ∩ T'.carrier =
      (T.carrier ∩ F1.edgeSeg k1) ∩ (T'.carrier ∩ F1.edgeSeg k1) := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨hx.1, hsub hx⟩, ⟨hx.2, hsub hx⟩⟩
    · rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
      exact ⟨h1, h2⟩
  rw [e1, hTe, hT'e, u4h_hull_inter_pair F1 k1 Set.inter_subset_right Set.inter_subset_right]
  congr 1
  ext p
  constructor
  · rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hpe : p ∈ T.carrier ∩ F1.edgeSeg k1 := by
      obtain ⟨j, rfl⟩ := h1
      obtain ⟨j', hj'⟩ := h2
      refine ⟨subset_convexHull ℝ _ ⟨j, rfl⟩, hsub ⟨subset_convexHull ℝ _ ⟨j, rfl⟩, ?_⟩⟩
      rw [← hj']
      exact subset_convexHull ℝ _ ⟨j', rfl⟩
    rw [hTe] at hpe
    obtain ⟨j, rfl⟩ := h1
    have := (u4h_vertex_mem_hull_iff T Set.inter_subset_left j).mp hpe
    exact ⟨⟨⟨j, rfl⟩, this.2⟩, ⟨h2, this.2⟩⟩

/-- The glued triangulation of `U1 ∪ U2`. -/
def u4h_glueTri {U1 U2 : Set Plane} (K1 : Triangulation U1) (K2 : Triangulation U2)
    {F1 : Triangle} (hF1 : F1 ∈ K1.faces) (k1 : Fin 3)
    {F2 : Triangle} (hF2 : F2 ∈ K2.faces) (k2 : Fin 3)
    (hedge : F2.edgeSeg k2 = F1.edgeSeg k1) (hinter : U1 ∩ U2 = F1.edgeSeg k1) :
    Triangulation (U1 ∪ U2) where
  faces := K1.faces ∪ K2.faces
  finite := K1.finite.union K2.finite
  cover := by rw [Set.biUnion_union, K1.cover, K2.cover]
  inter := by
    intro T hT T' hT'
    rcases hT with hT | hT <;> rcases hT' with hT' | hT'
    · exact K1.inter T hT T' hT'
    · exact u4h_glue_inter K1 K2 hF1 k1 hF2 k2 hedge hinter hT hT'
    · rw [Set.inter_comm, Set.inter_comm (Set.range T.v)]
      exact u4h_glue_inter K1 K2 hF1 k1 hF2 k2 hedge hinter hT' hT
    · exact K2.inter T hT T' hT'

theorem u4h_glueTri_faces {U1 U2 : Set Plane} (K1 : Triangulation U1) (K2 : Triangulation U2)
    {F1 : Triangle} (hF1 : F1 ∈ K1.faces) (k1 : Fin 3)
    {F2 : Triangle} (hF2 : F2 ∈ K2.faces) (k2 : Fin 3)
    (hedge : F2.edgeSeg k2 = F1.edgeSeg k1) (hinter : U1 ∩ U2 = F1.edgeSeg k1) :
    (u4h_glueTri K1 K2 hF1 k1 hF2 k2 hedge hinter).faces = K1.faces ∪ K2.faces := rfl

/-! ### Basic facts about triangulated sets -/

theorem u4h_tri_isCompact (T : Triangle) : IsCompact T.carrier := by
  rw [u4h_carrier_eq]; exact u4h_hull3_isCompact _ _ _

theorem u4h_triangulation_isCompact {X : Set Plane} (K : Triangulation X) : IsCompact X := by
  rw [← K.cover]
  exact K.finite.isCompact_biUnion fun T _ => u4h_tri_isCompact T

theorem u4h_triangulation_isClosed {X : Set Plane} (K : Triangulation X) : IsClosed X :=
  (u4h_triangulation_isCompact K).isClosed

theorem u4h_tri_interior_nonempty (T : Triangle) : (interior T.carrier).Nonempty := by
  rw [u4h_carrier_eq, u4h_interior_hull3 T.pos]
  refine ⟨(1/3 : ℝ) • T.v 0 + (1/3 : ℝ) • T.v 1 + (1/3 : ℝ) • T.v 2, ?_, ?_, ?_⟩
  all_goals
    simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have := T.pos
    simp only [det, Prod.fst_sub, Prod.snd_sub] at this
    nlinarith

/-- A point of a triangulated set is a limit of interior points. -/
theorem u4h_triangulation_subset_closure_interior {X : Set Plane} (K : Triangulation X) :
    X ⊆ closure (interior X) := by
  intro x hx
  rw [← K.cover] at hx
  obtain ⟨T, hT, hxT⟩ := Set.mem_iUnion₂.mp hx
  have h1 : x ∈ closure (interior T.carrier) := by
    have hconv : Convex ℝ T.carrier := convex_convexHull ℝ _
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior (u4h_tri_interior_nonempty T)]
    exact subset_closure hxT
  exact closure_mono (interior_mono (u4h_carrier_subset K hT)) h1

theorem u4h_triangulation_closure_interior {X : Set Plane} (K : Triangulation X) :
    closure (interior X) = X :=
  Set.Subset.antisymm (closure_minimal interior_subset (u4h_triangulation_isClosed K))
    (u4h_triangulation_subset_closure_interior K)

/-- Region data for an embedded polygon: the invariants carried through the ear/split
induction (U4). -/
structure u4h_Region {n : ℕ} (P : LabelledTuple n) where
  U : Set Plane
  K : Triangulation U
  frontier_eq : frontier U = polygonImage P
  edge_face : ∀ i, ∃ T ∈ K.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment P i
  edge_unique : ∀ i, ∀ T ∈ K.faces, ∀ T' ∈ K.faces,
    edgeSegment P i ⊆ T.carrier → edgeSegment P i ⊆ T'.carrier → T.carrier = T'.carrier
  hull : U ⊆ convexHull ℝ (Set.range P)
  int_conn : IsPreconnected (interior U)
  σ : ℝ
  σ_pm : σ = 1 ∨ σ = -1
  side : ∀ i, ∀ T ∈ K.faces, ∀ k : Fin 3, T.edgeSeg k = edgeSegment P i →
    0 < σ * det (P (i + 1) - P i) (T.v (k + 2) - P i)
  count : (K.faces.image Triangle.carrier).ncard + 2 ≤ n

end U4L_block

section U4M_block

/-! The local structure of a region at the lexicographically least vertex (U4 helpers):
outside the cone of the two incident edges, nearby points are not in the region. -/

/-- Strict lexicographic order on the plane. -/
def u4h_Lex (x y : Plane) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

/-- The closed lexicographic half-plane above `p`. -/
def u4h_LexQ (p : Plane) : Set Plane := {x | p.1 < x.1 ∨ (p.1 = x.1 ∧ p.2 ≤ x.2)}

theorem u4h_convex_LexQ (p : Plane) : Convex ℝ (u4h_LexQ p) := by
  intro x hx y hy s t hs ht hst
  simp only [u4h_LexQ, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hx hy ⊢
  have hp1 : s * p.1 + t * p.1 = p.1 := by rw [← add_mul, hst, one_mul]
  have hp2 : s * p.2 + t * p.2 = p.2 := by rw [← add_mul, hst, one_mul]
  have hx1 : s * p.1 ≤ s * x.1 :=
    mul_le_mul_of_nonneg_left (by rcases hx with h | ⟨h, -⟩ <;> linarith) hs
  have hy1 : t * p.1 ≤ t * y.1 :=
    mul_le_mul_of_nonneg_left (by rcases hy with h | ⟨h, -⟩ <;> linarith) ht
  by_cases hlt : p.1 < s * x.1 + t * y.1
  · exact Or.inl hlt
  · right
    have heq : p.1 = s * x.1 + t * y.1 := le_antisymm (by linarith) (not_lt.mp hlt)
    refine ⟨heq, ?_⟩
    have hx1' : s * p.1 = s * x.1 := by linarith
    have hy1' : t * p.1 = t * y.1 := by linarith
    have hsx : s * p.2 ≤ s * x.2 := by
      rcases hs.lt_or_eq with hs' | hs'
      · have : p.1 = x.1 := mul_left_cancel₀ hs'.ne' hx1'
        rcases hx with h | ⟨-, h⟩
        · linarith
        · exact mul_le_mul_of_nonneg_left h hs
      · rw [← hs']; simp
    have hty : t * p.2 ≤ t * y.2 := by
      rcases ht.lt_or_eq with ht' | ht'
      · have : p.1 = y.1 := mul_left_cancel₀ ht'.ne' hy1'
        rcases hy with h | ⟨-, h⟩
        · linarith
        · exact mul_le_mul_of_nonneg_left h ht
      · rw [← ht']; simp
    linarith

theorem u4h_det_neg_left (u w : Plane) : det (-u) w = -det u w := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

theorem u4h_hull_subset_LexQ {P : LabelledTuple n} {v : ZMod n}
    (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) :
    convexHull ℝ (Set.range P) ⊆ u4h_LexQ (P v) := by
  apply convexHull_min _ (u4h_convex_LexQ _)
  rintro x ⟨k, rfl⟩
  by_cases hk : k = v
  · subst hk; right; exact ⟨rfl, le_rfl⟩
  · rcases hv k hk with h | ⟨h1, h2⟩
    · left; exact h
    · right; exact ⟨h1, h2.le⟩

/-- Edge vectors at the lexmin vertex are in the open lexicographic cone. -/
theorem u4h_edge_lexQ0 {P : LabelledTuple n} {v : ZMod n}
    (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) {k : ZMod n} (hk : k ≠ v) :
    0 < (P k - P v).1 ∨ ((P k - P v).1 = 0 ∧ 0 < (P k - P v).2) := by
  rcases hv k hk with h | ⟨h1, h2⟩
  · left; simp only [Prod.fst_sub]; linarith
  · right; simp only [Prod.fst_sub, Prod.snd_sub]; constructor <;> linarith

/-- Among the two directions `(-1, 1)`, `(-1, -1)` one lies strictly outside the cone spanned by
two vectors `u, u'` of the open lexicographic cone with `det u u' > 0`. -/
theorem u4h_exists_left_dir {u u' : Plane}
    (hu : 0 < u.1 ∨ (u.1 = 0 ∧ 0 < u.2)) (hu' : 0 < u'.1 ∨ (u'.1 = 0 ∧ 0 < u'.2))
    (hdet : 0 < det u u') :
    ∃ w : Plane, w.1 = -1 ∧ ‖w‖ = 1 ∧ (det u w < 0 ∨ 0 < det u' w) := by
  have hn1 : ‖((-1 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hn2 : ‖((-1 : ℝ), (-1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  by_cases h1 : det u (-1, 1) < 0 ∨ 0 < det u' (-1, 1)
  · exact ⟨(-1, 1), rfl, hn1, h1⟩
  by_cases h2 : det u (-1, -1) < 0 ∨ 0 < det u' (-1, -1)
  · exact ⟨(-1, -1), rfl, hn2, h2⟩
  exfalso
  simp only [not_or, not_lt, det] at h1 h2
  simp only [det] at hdet
  rcases hu with hu | ⟨hu1, hu2⟩ <;> rcases hu' with hu' | ⟨hu'1, hu'2⟩ <;> nlinarith

/-- **Local lexmin lemma.** Near the lexicographically least vertex `P v`, every point strictly
outside the closed cone of the two incident edge vectors `u, u'` (`det u u' > 0`) is outside
the region `U`. -/
theorem u4h_local_lexmin [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    {U : Set Plane} (hU : IsClosed U) (hfr : frontier U = polygonImage P)
    (hhull : U ⊆ convexHull ℝ (Set.range P)) {v : ZMod n}
    (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) {u u' : Plane}
    (hu : u = P (v - 1) - P v ∨ u = P (v + 1) - P v)
    (hu' : u' = P (v - 1) - P v ∨ u' = P (v + 1) - P v) (hdet : 0 < det u u') :
    ∃ ρ > 0, ∀ z, dist z (P v) < ρ → (det u (z - P v) < 0 ∨ 0 < det u' (z - P v)) → z ∉ U := by
  -- the other edges stay away from `P v`
  set C' : Set Plane := ⋃ k ∈ {k : ZMod n | k ≠ v - 1 ∧ k ≠ v}, edgeSegment P k with hC'
  have hC'closed : IsClosed C' := by
    refine (Set.toFinite _).isClosed_biUnion fun k _ => ?_
    rw [u4h_edgeSegment_eq_segment]; exact u4h_isClosed_segment _ _
  have hvC' : P v ∉ C' := by
    intro h
    obtain ⟨k, ⟨hk1, hk2⟩, hk⟩ := Set.mem_iUnion₂.mp h
    rcases u4h_incident_of_vertex_mem hP hk with h | h
    · exact hk2 h.symm
    · exact hk1 (by rw [h, add_sub_cancel_right])
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hC'closed.isOpen_compl.mem_nhds hvC')
  refine ⟨ρ, hρ, fun z hz hzS hzU => ?_⟩
  -- the two half-planes and the set `S`
  set A : Set Plane := {y | det u (y - P v) < 0} ∩ Metric.ball (P v) ρ with hA
  set B : Set Plane := {y | 0 < det u' (y - P v)} ∩ Metric.ball (P v) ρ with hB
  have hAeq : {y : Plane | det u (y - P v) < 0} = {y | 0 < det (-u) (y - P v)} := by
    ext y
    simp only [Set.mem_ofPred_eq, u4h_det_neg_left]
    exact ⟨fun h => by linarith, fun h => by linarith⟩
  have hAconv : Convex ℝ A := by
    rw [hA, hAeq]
    exact (u4h_convex_det_pos _ _).inter (convex_ball _ _)
  have hBconv : Convex ℝ B := (u4h_convex_det_pos _ _).inter (convex_ball _ _)
  -- a common point of `A` and `B`
  have huu' : u + u' ≠ 0 := by
    intro h
    have : u' = -u := eq_neg_of_add_eq_zero_right h
    have h0 : det u (-u) = 0 := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [this, h0] at hdet
    exact lt_irrefl _ hdet
  have hnorm : 0 < ‖u + u'‖ := norm_pos_iff.mpr huu'
  set z0 : Plane := P v - (ρ / (2 * ‖u + u'‖)) • (u + u') with hz0
  have hz0ball : z0 ∈ Metric.ball (P v) ρ := by
    rw [Metric.mem_ball, dist_eq_norm, hz0, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hz0 : z0 ∈ A ∩ B := by
    have hpos : 0 < ρ / (2 * ‖u + u'‖) := by positivity
    refine ⟨⟨?_, hz0ball⟩, ⟨?_, hz0ball⟩⟩
    · show det u (z0 - P v) < 0
      rw [hz0, sub_sub_cancel_left, ← neg_smul, u4h_det_smul_right, u4h_det_add_right,
        u4h_det_self, zero_add]
      nlinarith
    · show 0 < det u' (z0 - P v)
      rw [hz0, sub_sub_cancel_left, ← neg_smul, u4h_det_smul_right, u4h_det_add_right,
        u4h_det_self, add_zero, u4h_det_swap' u' u]
      nlinarith
  have hSconn : IsPreconnected (A ∪ B) :=
    IsPreconnected.union z0 hz0.1 hz0.2 hAconv.isPreconnected hBconv.isPreconnected
  -- `S` avoids the frontier
  have hSfr : ∀ y ∈ A ∪ B, y ∉ frontier U := by
    intro y hy hyf
    have hyball : y ∈ Metric.ball (P v) ρ := by rcases hy with h | h <;> exact h.2
    rw [hfr] at hyf
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hyf
    have hnot : ∀ w : Plane, (w = P (v - 1) - P v ∨ w = P (v + 1) - P v) → ∀ t : ℝ, 0 ≤ t →
        y = P v + t • w → False := by
      intro w hw t ht hy'
      have e1 : det u (y - P v) = t * det u w := by rw [hy', add_sub_cancel_left, u4h_det_smul_right]
      have e2 : det u' (y - P v) = t * det u' w := by
        rw [hy', add_sub_cancel_left, u4h_det_smul_right]
      have hw' : w = u ∨ w = u' := by
        rcases hw with hw | hw <;> rcases hu with hu | hu <;> rcases hu' with hu' | hu'
        all_goals first
          | exact Or.inl (hw.trans hu.symm)
          | exact Or.inr (hw.trans hu'.symm)
          | (exfalso
             have huu : u = u' := hu.trans hu'.symm
             rw [huu, u4h_det_self] at hdet
             exact lt_irrefl _ hdet)
      rcases hy with ⟨hyA, -⟩ | ⟨hyB, -⟩
      · have : det u (y - P v) < 0 := hyA
        rw [e1] at this
        rcases hw' with hw' | hw'
        · rw [hw', u4h_det_self] at this; simp at this
        · rw [hw'] at this; nlinarith
      · have : 0 < det u' (y - P v) := hyB
        rw [e2] at this
        rcases hw' with hw' | hw'
        · rw [hw', u4h_det_swap' u' u] at this; nlinarith
        · rw [hw', u4h_det_self] at this; simp at this
    by_cases hk1 : k = v - 1
    · subst hk1
      rw [u4h_edgeSegment_prev, segment_symm, u4h_mem_segment_iff_lin] at hk
      obtain ⟨t, ht0, -, hyt⟩ := hk
      exact hnot _ (Or.inl rfl) t ht0 hyt
    by_cases hk2 : k = v
    · subst hk2
      rw [u4h_edgeSegment_eq_segment, u4h_mem_segment_iff_lin] at hk
      obtain ⟨t, ht0, -, hyt⟩ := hk
      exact hnot _ (Or.inr rfl) t ht0 hyt
    exact hball hyball (Set.mem_iUnion₂.mpr ⟨k, ⟨hk1, hk2⟩, hk⟩)
  have hSsub : A ∪ B ⊆ interior U ∪ Uᶜ := by
    intro y hy
    by_cases hyU : y ∈ U
    · left
      by_contra hyi
      exact hSfr y hy ⟨subset_closure hyU, hyi⟩
    · right; exact hyU
  -- a point of `S` outside the hull
  have hQ0 : ∀ w : Plane, (w = P (v - 1) - P v ∨ w = P (v + 1) - P v) →
      0 < w.1 ∨ (w.1 = 0 ∧ 0 < w.2) := by
    rintro w (rfl | rfl)
    · exact u4h_edge_lexQ0 hv (by
        intro h; exact u4h_one_ne_zero' (n := n) (by omega) (by linear_combination -h))
    · exact u4h_edge_lexQ0 hv (by
        intro h; exact u4h_one_ne_zero' (n := n) (by omega) (by linear_combination h))
  obtain ⟨w, hw1, hwn, hw⟩ := u4h_exists_left_dir (hQ0 u hu) (hQ0 u' hu') hdet
  set z1 : Plane := P v + (ρ / 2) • w with hz1
  have hz1ball : z1 ∈ Metric.ball (P v) ρ := by
    rw [Metric.mem_ball, dist_eq_norm, hz1, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity), hwn, mul_one]
    linarith
  have hz1S : z1 ∈ A ∪ B := by
    rcases hw with hw | hw
    · left; refine ⟨?_, hz1ball⟩
      show det u (z1 - P v) < 0
      rw [hz1, add_sub_cancel_left, u4h_det_smul_right]; nlinarith
    · right; refine ⟨?_, hz1ball⟩
      show 0 < det u' (z1 - P v)
      rw [hz1, add_sub_cancel_left, u4h_det_smul_right]; nlinarith
  have hz1U : z1 ∉ U := by
    intro h
    have := u4h_hull_subset_LexQ hv (hhull h)
    simp only [u4h_LexQ, Set.mem_ofPred_eq, hz1, Prod.fst_add, Prod.smul_fst, smul_eq_mul, hw1]
      at this
    rcases this with h | ⟨h, -⟩ <;> linarith
  -- conclude
  have hzS' : z ∈ A ∪ B := by
    rcases hzS with h | h
    · exact Or.inl ⟨h, Metric.mem_ball.mpr hz⟩
    · exact Or.inr ⟨h, Metric.mem_ball.mpr hz⟩
  rcases IsPreconnected.subset_or_subset isOpen_interior hU.isOpen_compl
      (Set.disjoint_left.mpr fun y hy hy' => hy' (interior_subset hy)) hSsub hSconn with h | h
  · exact hz1U (interior_subset (h hz1S))
  · exact h hzS' hzU

end U4M_block

section U4N_block

/-! Corollaries of the local lexmin lemma (U4 helpers). -/

/-- An embedded polygon has a (strict) lexicographically least vertex. -/
theorem u4h_exists_lexmin [NeZero n] {P : LabelledTuple n} (hP : Embedded P) :
    ∃ v : ZMod n, ∀ k, k ≠ v → u4h_Lex (P v) (P k) := by
  obtain ⟨v, -, hv⟩ := Finset.exists_min_image Finset.univ
    (fun j : ZMod n => toLex ((P j).1, (P j).2)) Finset.univ_nonempty
  refine ⟨v, fun k hk => ?_⟩
  have h := hv k (Finset.mem_univ k)
  rw [Prod.Lex.le_iff] at h
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · right
    refine ⟨h1, lt_of_le_of_ne h2 fun h2' => hk ?_⟩
    exact u4h_vertex_injective hP (Prod.ext h1 h2').symm

/-- Two vectors of the open lexicographic cone with zero determinant are positive multiples. -/
theorem u4h_pos_multiple_of_det_zero {p q : Plane} (hp : 0 < p.1 ∨ (p.1 = 0 ∧ 0 < p.2))
    (hq : 0 < q.1 ∨ (q.1 = 0 ∧ 0 < q.2)) (h : det p q = 0) : ∃ l : ℝ, 0 < l ∧ q = l • p := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    rcases hp with h | ⟨-, h⟩ <;> simp at h
  obtain ⟨l, hl⟩ : ∃ l : ℝ, q = l • p := ⟨_, scalar_of_det_zero hp0 h⟩
  refine ⟨l, ?_, hl⟩
  rw [hl] at hq
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hq
  rcases hp with hp | ⟨hp1, hp2⟩ <;> rcases hq with hq | ⟨hq1, hq2⟩
  · exact pos_of_mul_pos_left hq hp.le
  · exfalso
    have hl0 : l = 0 := by
      rcases mul_eq_zero.mp hq1 with h | h
      · exact h
      · linarith
    rw [hl0] at hq2; simp at hq2
  · exfalso; rw [hp1] at hq; simp at hq
  · exact pos_of_mul_pos_left hq2 hp2.le

/-- At a vertex of an embedded polygon the two edge vectors are not parallel in the same
direction; at the lexmin vertex (both in the open lexicographic cone) this is `det ≠ 0`. -/
theorem u4h_lexmin_det_ne_zero [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    {v : ZMod n} (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) :
    det (P (v - 1) - P v) (P (v + 1) - P v) ≠ 0 := by
  intro h
  have h1 : (v - 1 : ZMod n) ≠ v := fun h => u4h_one_ne_zero' (n := n) (by omega)
    (by linear_combination -h)
  have h2 : (v + 1 : ZMod n) ≠ v := fun h => u4h_one_ne_zero' (n := n) (by omega)
    (by linear_combination h)
  obtain ⟨l, hl, hq⟩ := u4h_pos_multiple_of_det_zero (u4h_edge_lexQ0 hv h1) (u4h_edge_lexQ0 hv h2) h
  -- the point `P v + t • p` with `t = min 1 l` lies on both edges at `v`
  set p := P (v - 1) - P v with hp
  have hp0 : p ≠ 0 := sub_ne_zero.mpr (u4h_vertex_injective hP |>.ne h1)
  set t : ℝ := min 1 l with ht
  have ht0 : 0 < t := lt_min one_pos hl
  have hmem1 : P v + t • p ∈ edgeSegment P (v - 1) := by
    rw [u4h_edgeSegment_prev, segment_symm, u4h_mem_segment_iff_lin]
    exact ⟨t, ht0.le, min_le_left _ _, rfl⟩
  have hmem2 : P v + t • p ∈ edgeSegment P v := by
    rw [u4h_edgeSegment_eq_segment, u4h_mem_segment_iff_lin]
    refine ⟨t / l, div_nonneg ht0.le hl.le, (div_le_one hl).mpr (min_le_right _ _), ?_⟩
    rw [hq, smul_smul, div_mul_cancel₀ _ hl.ne']
  have hc := hP.consecutive (v - 1)
  rw [sub_add_cancel] at hc
  have : P v + t • p ∈ edgeSegment P (v - 1) ∩ edgeSegment P v := ⟨hmem1, hmem2⟩
  rw [hc] at this
  have h0 : t • p = 0 := add_eq_left.mp this
  rcases smul_eq_zero.mp h0 with h0 | h0
  · exact ht0.ne' h0
  · exact hp0 h0

/-- A strictly positive convex combination of the vertices of a positively oriented triple lies in
the interior of its hull. -/
theorem u4h_pos_comb_mem_interior {p0 p1 p2 : Plane} (hD : 0 < det (p1 - p0) (p2 - p0))
    {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsum : α + β + γ = 1) :
    α • p0 + β • p1 + γ • p2 ∈ interior (convexHull ℝ {p0, p1, p2}) := by
  rw [u4h_interior_hull3 hD]
  have hα' : α = 1 - β - γ := by linarith
  subst hα'
  refine ⟨?_, ?_, ?_⟩
  · have e : det (p1 - p0) ((1 - β - γ) • p0 + β • p1 + γ • p2 - p0) = γ * det (p1 - p0) (p2 - p0) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos hγ hD
  · have e : det (p2 - p1) ((1 - β - γ) • p0 + β • p1 + γ • p2 - p1) =
        (1 - β - γ) * det (p1 - p0) (p2 - p0) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos hα hD
  · have e : det (p0 - p2) ((1 - β - γ) • p0 + β • p1 + γ • p2 - p2) = β * det (p1 - p0) (p2 - p0) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos hβ hD

/-- The two ends of a face-edge equal to `segment a b` (`a ≠ b`), in one of two orders. -/
theorem u4h_face_edge_ends (T : Triangle) (k : Fin 3) {a b : Plane}
    (h : T.edgeSeg k = segment ℝ a b) :
    (T.v k = a ∧ T.v (k + 1) = b) ∨ (T.v k = b ∧ T.v (k + 1) = a) := by
  have hends : ({T.v k, T.v (k + 1)} : Set Plane) = {a, b} :=
    u4h_segment_endpoints (u4h_tri_ne T k) h
  have h1 : T.v k ∈ ({a, b} : Set Plane) := hends ▸ Set.mem_insert _ _
  have h2 : T.v (k + 1) ∈ ({a, b} : Set Plane) := hends ▸ Set.mem_insert_of_mem _ rfl
  have hne := u4h_tri_ne T k
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

/-- Points of a face are in the region. -/
theorem u4h_Region.face_subset {P : LabelledTuple n} (R : u4h_Region P) {T : Triangle}
    (hT : T ∈ R.K.faces) : T.carrier ⊆ R.U := u4h_carrier_subset R.K hT

theorem u4h_Region.isClosed {P : LabelledTuple n} (R : u4h_Region P) : IsClosed R.U :=
  u4h_triangulation_isClosed R.K

end U4N_block

section U4O_block

/-! (LL1) the side of a region is the turn sign at the lexmin vertex; (LL2) rays leaving the
lexmin vertex outside the edge cone leave the region (U4 helpers). -/

/-- (LL1) -/
theorem u4h_region_lexmin_turn [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (R : u4h_Region P) {v : ZMod n} (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) :
    0 < R.σ * det (P v - P (v - 1)) (P (v + 1) - P v) := by
  have hdet0 := u4h_lexmin_det_ne_zero hn hP hv
  obtain ⟨F, hF, k, hFk⟩ := R.edge_face (v - 1)
  have hside := R.side (v - 1) F hF k hFk
  rw [sub_add_cancel] at hside
  have e1 : det (P v - P (v - 1)) (F.v (k + 2) - P (v - 1)) =
      -det (P (v - 1) - P v) (F.v (k + 2) - P v) := by
    simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  rw [e1] at hside
  have egoal : det (P v - P (v - 1)) (P (v + 1) - P v) =
      -det (P (v - 1) - P v) (P (v + 1) - P v) := by
    simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  rw [egoal]
  by_contra hcon
  have hcon' : 0 ≤ R.σ * det (P (v - 1) - P v) (P (v + 1) - P v) := by linarith
  have hσ0 : R.σ ≠ 0 := by rcases R.σ_pm with h | h <;> rw [h] <;> norm_num
  have hpos : 0 < R.σ * det (P (v - 1) - P v) (P (v + 1) - P v) :=
    lt_of_le_of_ne hcon' (Ne.symm (mul_ne_zero hσ0 hdet0))
  -- the face at `E_{v-1}` and its vertex order
  rw [u4h_edgeSegment_prev] at hFk
  have hends := u4h_face_edge_ends F k hFk
  have hDk := u4h_tri_pos F k
  -- the interior point `b'` of `F`, close to `P v`, in the direction of the apex plus `p`
  have hbase : ∀ ρ > 0, ∃ ε : ℝ, 0 < ε ∧ ε < 1/3 ∧
      dist (P v + ε • (F.v (k + 2) - P v) + ε • (P (v - 1) - P v)) (P v) < ρ ∧
      P v + ε • (F.v (k + 2) - P v) + ε • (P (v - 1) - P v) ∈ interior F.carrier := by
    intro ρ hρ
    have hM : 0 < ‖F.v (k + 2) - P v‖ + ‖P (v - 1) - P v‖ + 1 := by positivity
    refine ⟨min (1/4) (ρ / (2 * (‖F.v (k + 2) - P v‖ + ‖P (v - 1) - P v‖ + 1))), ?_, ?_, ?_, ?_⟩
    · exact lt_min (by norm_num) (by positivity)
    · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    · set ε := min (1/4) (ρ / (2 * (‖F.v (k + 2) - P v‖ + ‖P (v - 1) - P v‖ + 1))) with hε
      have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
      have hεle : ε ≤ ρ / (2 * (‖F.v (k + 2) - P v‖ + ‖P (v - 1) - P v‖ + 1)) := min_le_right _ _
      rw [dist_eq_norm, add_assoc, add_sub_cancel_left]
      calc ‖ε • (F.v (k + 2) - P v) + ε • (P (v - 1) - P v)‖
          ≤ ‖ε • (F.v (k + 2) - P v)‖ + ‖ε • (P (v - 1) - P v)‖ := norm_add_le _ _
        _ = ε * (‖F.v (k + 2) - P v‖ + ‖P (v - 1) - P v‖) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hε0]; ring
        _ ≤ ρ / (2 * (‖F.v (k + 2) - P v‖ + ‖P (v - 1) - P v‖ + 1)) *
            (‖F.v (k + 2) - P v‖ + ‖P (v - 1) - P v‖) :=
          mul_le_mul_of_nonneg_right hεle (by positivity)
        _ < ρ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg (F.v (k + 2) - P v), norm_nonneg (P (v - 1) - P v)]
    · set ε := min (1/4) (ρ / (2 * (‖F.v (k + 2) - P v‖ + ‖P (v - 1) - P v‖ + 1))) with hε
      have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
      have hε1 : ε ≤ 1/4 := min_le_left _ _
      rw [u4h_tri_carrier_rot F k]
      rcases hends with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · have e : P v + ε • (F.v (k + 2) - P v) + ε • (P (v - 1) - P v) =
            ε • F.v k + (1 - 2 * ε) • F.v (k + 1) + ε • F.v (k + 2) := by
          rw [h0, h1]; module
        rw [e]
        exact u4h_pos_comb_mem_interior hDk hε0 (by linarith) hε0 (by ring)
      · have e : P v + ε • (F.v (k + 2) - P v) + ε • (P (v - 1) - P v) =
            (1 - 2 * ε) • F.v k + ε • F.v (k + 1) + ε • F.v (k + 2) := by
          rw [h0, h1]; module
        rw [e]
        exact u4h_pos_comb_mem_interior hDk (by linarith) hε0 hε0 (by ring)
  -- the determinant of `p` against `b' - P v`
  have hdetb' : ∀ ε : ℝ, det (P (v - 1) - P v)
      (P v + ε • (F.v (k + 2) - P v) + ε • (P (v - 1) - P v) - P v) =
      ε * det (P (v - 1) - P v) (F.v (k + 2) - P v) := by
    intro ε
    simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  rcases R.σ_pm with hσ | hσ
  · rw [hσ, one_mul] at hpos hside
    obtain ⟨ρ, hρ, hLL⟩ := u4h_local_lexmin hn hP R.isClosed R.frontier_eq R.hull hv
      (Or.inl rfl) (Or.inr rfl) hpos
    obtain ⟨ε, hε0, -, hdist, hint⟩ := hbase ρ hρ
    refine hLL _ hdist (Or.inl ?_) (R.face_subset hF (interior_subset hint))
    rw [hdetb']
    nlinarith
  · rw [hσ] at hpos hside
    have hpos' : 0 < det (P (v + 1) - P v) (P (v - 1) - P v) := by
      rw [u4h_det_swap']; linarith
    obtain ⟨ρ, hρ, hLL⟩ := u4h_local_lexmin hn hP R.isClosed R.frontier_eq R.hull hv
      (Or.inr rfl) (Or.inl rfl) hpos'
    obtain ⟨ε, hε0, -, hdist, hint⟩ := hbase ρ hρ
    refine hLL _ hdist (Or.inr ?_) (R.face_subset hF (interior_subset hint))
    rw [hdetb']
    nlinarith

/-- (LL2) -/
theorem u4h_lexmin_ray_outside [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    {U : Set Plane} (hU : IsClosed U) (hfr : frontier U = polygonImage P)
    (hhull : U ⊆ convexHull ℝ (Set.range P)) {v : ZMod n}
    (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) {w : Plane}
    (hw : (0 < det (P (v - 1) - P v) (P (v + 1) - P v) ∧
        (det (P (v - 1) - P v) w < 0 ∨ 0 < det (P (v + 1) - P v) w)) ∨
      (det (P (v - 1) - P v) (P (v + 1) - P v) < 0 ∧
        (det (P (v + 1) - P v) w < 0 ∨ 0 < det (P (v - 1) - P v) w))) :
    ∃ ρ > 0, ∀ t : ℝ, 0 < t → t < ρ → P v + t • w ∉ U := by
  have hw1 : 0 < ‖w‖ + 1 := by positivity
  rcases hw with ⟨hd, hw⟩ | ⟨hd, hw⟩
  · obtain ⟨ρ, hρ, hLL⟩ := u4h_local_lexmin hn hP hU hfr hhull hv (Or.inl rfl) (Or.inr rfl) hd
    refine ⟨ρ / (‖w‖ + 1), by positivity, fun t ht0 ht => hLL _ ?_ ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have := (lt_div_iff₀ hw1).mp ht
      nlinarith [norm_nonneg w]
    · rw [add_sub_cancel_left, u4h_det_smul_right, u4h_det_smul_right]
      rcases hw with h | h
      · exact Or.inl (mul_neg_of_pos_of_neg ht0 h)
      · exact Or.inr (mul_pos ht0 h)
  · have hd' : 0 < det (P (v + 1) - P v) (P (v - 1) - P v) := by rw [u4h_det_swap']; linarith
    obtain ⟨ρ, hρ, hLL⟩ := u4h_local_lexmin hn hP hU hfr hhull hv (Or.inr rfl) (Or.inl rfl) hd'
    refine ⟨ρ / (‖w‖ + 1), by positivity, fun t ht0 ht => hLL _ ?_ ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have := (lt_div_iff₀ hw1).mp ht
      nlinarith [norm_nonneg w]
    · rw [add_sub_cancel_left, u4h_det_smul_right, u4h_det_smul_right]
      rcases hw with h | h
      · exact Or.inl (mul_neg_of_pos_of_neg ht0 h)
      · exact Or.inr (mul_pos ht0 h)

end U4O_block

section U4P_block

/-! Sub-polygons along a diagonal (U4 helpers): the vertices `P i, P (i+1), …, P (i+m)` closed by
the diagonal from `P (i+m)` back to `P i`. -/

/-- The sub-polygon of `P` with vertices `P i, …, P (i + m)` (an `(m+1)`-gon). -/
def u4h_subPoly (P : LabelledTuple n) (i : ZMod n) (m : ℕ) : LabelledTuple (m + 1) :=
  fun k => P (i + (k.val : ZMod n))

theorem u4h_subPoly_apply (P : LabelledTuple n) (i : ZMod n) (m : ℕ) (k : ZMod (m + 1)) :
    u4h_subPoly P i m k = P (i + (k.val : ZMod n)) := rfl

theorem u4h_val_neg_one' (m : ℕ) : ((-1 : ZMod (m + 1))).val = m := ZMod.val_neg_one m

theorem u4h_val_lt_of_ne_neg_one {m : ℕ} {k : ZMod (m + 1)} (hk : k ≠ -1) : k.val < m := by
  have h := ZMod.val_lt k
  rcases Nat.lt_or_ge k.val m with h' | h'
  · exact h'
  · exfalso
    apply hk
    apply ZMod.val_injective
    rw [u4h_val_neg_one']
    omega

theorem u4h_val_add_one {m : ℕ} {k : ZMod (m + 1)} (hk : k ≠ -1) : (k + 1).val = k.val + 1 := by
  have h := u4h_val_lt_of_ne_neg_one hk
  rw [ZMod.val_add_of_lt]
  · rw [ZMod.val_one_eq_one_mod]
    rcases Nat.lt_or_ge 1 (m + 1) with h1 | h1
    · rw [Nat.mod_eq_of_lt h1]
    · omega
  · rw [ZMod.val_one_eq_one_mod]
    rcases Nat.lt_or_ge 1 (m + 1) with h1 | h1
    · rw [Nat.mod_eq_of_lt h1]; omega
    · omega

theorem u4h_subPoly_zero (P : LabelledTuple n) (i : ZMod n) (m : ℕ) :
    u4h_subPoly P i m 0 = P i := by
  simp [u4h_subPoly_apply]

theorem u4h_subPoly_last (P : LabelledTuple n) (i : ZMod n) (m : ℕ) :
    u4h_subPoly P i m (-1) = P (i + m) := by
  rw [u4h_subPoly_apply, u4h_val_neg_one']

theorem u4h_subPoly_edge (P : LabelledTuple n) (i : ZMod n) (m : ℕ) {k : ZMod (m + 1)}
    (hk : k ≠ -1) : edge (u4h_subPoly P i m) k = edge P (i + (k.val : ZMod n)) := by
  simp only [edge, u4h_subPoly_apply, u4h_val_add_one hk, Nat.cast_add, Nat.cast_one, add_assoc]

theorem u4h_subPoly_edgeSegment (P : LabelledTuple n) (i : ZMod n) (m : ℕ) {k : ZMod (m + 1)}
    (hk : k ≠ -1) : edgeSegment (u4h_subPoly P i m) k = edgeSegment P (i + (k.val : ZMod n)) := by
  simp only [edgeSegment, edgePoint, u4h_subPoly_edge P i m hk, u4h_subPoly_apply]

theorem u4h_subPoly_edgeSegment_last (P : LabelledTuple n) (i : ZMod n) (m : ℕ) :
    edgeSegment (u4h_subPoly P i m) (-1) = segment ℝ (P (i + m)) (P i) := by
  rw [u4h_edgeSegment_eq_segment, neg_add_cancel, u4h_subPoly_last, u4h_subPoly_zero]

/-- The natural-number offsets `s < m` index exactly the non-diagonal edges. -/
theorem u4h_subPoly_index_exhaust (m : ℕ) {s : ℕ} (hs : s < m) :
    ∃ k : ZMod (m + 1), k ≠ -1 ∧ k.val = s := by
  refine ⟨(s : ZMod (m + 1)), ?_, ZMod.val_natCast_of_lt (by omega)⟩
  intro h
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt (by omega), u4h_val_neg_one'] at this
  omega

/-- Membership in the polygon image of a sub-polygon. -/
theorem u4h_mem_polygonImage_subPoly (P : LabelledTuple n) (i : ZMod n) (m : ℕ) (x : Plane) :
    x ∈ polygonImage (u4h_subPoly P i m) ↔
      (∃ s : ℕ, s < m ∧ x ∈ edgeSegment P (i + s)) ∨ x ∈ segment ℝ (P (i + m)) (P i) := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    by_cases hk1 : k = -1
    · subst hk1
      rw [u4h_subPoly_edgeSegment_last] at hk
      exact Or.inr hk
    · rw [u4h_subPoly_edgeSegment P i m hk1] at hk
      exact Or.inl ⟨k.val, u4h_val_lt_of_ne_neg_one hk1, hk⟩
  · rintro (⟨s, hs, hx⟩ | hx)
    · obtain ⟨k, hk1, hks⟩ := u4h_subPoly_index_exhaust m hs
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      rw [u4h_subPoly_edgeSegment P i m hk1, hks]
      exact hx
    · exact Set.mem_iUnion.mpr ⟨-1, by rw [u4h_subPoly_edgeSegment_last]; exact hx⟩

theorem u4h_subPoly_range_subset (P : LabelledTuple n) (i : ZMod n) (m : ℕ) :
    Set.range (u4h_subPoly P i m) ⊆ Set.range P := by
  rintro x ⟨k, rfl⟩
  exact ⟨_, rfl⟩

/-- An integer of absolute value `< n` that vanishes in `ZMod n` is zero. -/
theorem u4h_int_cast_eq_zero {x : ℤ} (hx : |x| < n) (h : (x : ZMod n) = 0) : x = 0 :=
  Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd x n).mp h) hx

/-- Adjacency of the `P`-indices `i + s`, `i + s'` for small offsets. -/
theorem u4h_adjacent_offset {s s' : ℕ} (hs : s + 2 < n) (hs' : s' + 2 < n) (i : ZMod n) :
    adjacent (i + (s : ZMod n)) (i + (s' : ZMod n)) ↔ (s' = s + 1 ∨ s' = s ∨ s = s' + 1) := by
  have key : ∀ x : ℤ, |x| < n → (((x : ℤ) : ZMod n) = 0 ↔ x = 0) := fun x hx =>
    ⟨u4h_int_cast_eq_zero hx, fun h => by rw [h, Int.cast_zero]⟩
  rw [u4h_adjacent_iff]
  have e1 : (i + (s' : ZMod n) = i + (s : ZMod n) - 1) ↔ (((s' : ℤ) - s + 1 : ℤ) : ZMod n) = 0 := by
    push_cast; constructor <;> intro h <;> linear_combination h
  have e2 : (i + (s' : ZMod n) = i + (s : ZMod n)) ↔ (((s' : ℤ) - s : ℤ) : ZMod n) = 0 := by
    push_cast; constructor <;> intro h <;> linear_combination h
  have e3 : (i + (s' : ZMod n) = i + (s : ZMod n) + 1) ↔ (((s' : ℤ) - s - 1 : ℤ) : ZMod n) = 0 := by
    push_cast; constructor <;> intro h <;> linear_combination h
  rw [e1, e2, e3, key _ (by rw [abs_lt]; constructor <;> omega),
    key _ (by rw [abs_lt]; constructor <;> omega), key _ (by rw [abs_lt]; constructor <;> omega)]
  omega

/-- `i + s = i + s'` for offsets `< n` forces `s = s'`. -/
theorem u4h_offset_injective {s s' : ℕ} (hs : s < n) (hs' : s' < n) (i : ZMod n)
    (h : i + (s : ZMod n) = i + (s' : ZMod n)) : s = s' := by
  have h' : (((s : ℤ) - s' : ℤ) : ZMod n) = 0 := by push_cast; linear_combination h
  have := u4h_int_cast_eq_zero (by rw [abs_lt]; constructor <;> omega) h'
  omega

end U4P_block

section U4Q_block

/-! A sub-polygon along a clean diagonal is embedded (U4 helpers). -/

theorem u4h_Pi_mem_offset [NeZero n] {P : LabelledTuple n} (hP : Embedded P) {i : ZMod n}
    {m : ℕ} (hmn : m + 2 ≤ n) {s : ℕ} (hs : s < m) (h : P i ∈ edgeSegment P (i + (s : ZMod n))) :
    s = 0 := by
  rcases u4h_incident_of_vertex_mem hP h with h' | h'
  · have := u4h_offset_injective (s := 0) (s' := s) (by omega) (by omega) i (by simpa using h')
    omega
  · exfalso
    have := u4h_offset_injective (s := 0) (s' := s + 1) (by omega) (by omega) i
      (by rw [Nat.cast_add, Nat.cast_one, ← add_assoc]; simpa using h')
    omega

theorem u4h_Pim_mem_offset [NeZero n] {P : LabelledTuple n} (hP : Embedded P) {i : ZMod n}
    {m : ℕ} (hmn : m + 2 ≤ n) {s : ℕ} (hs : s < m)
    (h : P (i + (m : ZMod n)) ∈ edgeSegment P (i + (s : ZMod n))) : s + 1 = m := by
  rcases u4h_incident_of_vertex_mem hP h with h' | h'
  · have := u4h_offset_injective (s := m) (s' := s) (by omega) (by omega) i h'
    omega
  · have := u4h_offset_injective (s := m) (s' := s + 1) (by omega) (by omega) i
      (by rw [Nat.cast_add, Nat.cast_one, ← add_assoc]; exact h')
    omega

/-- A `P`-edge of the sub-polygon meets the diagonal only at its endpoints (clean diagonal). -/
theorem u4h_edge_inter_diag_subPoly {P : LabelledTuple n} {i : ZMod n} {m : ℕ}
    (hclean : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P i) (P (i + (m : ZMod n)))))
    (k : ZMod n) {x : Plane} (hx : x ∈ edgeSegment P k)
    (hD : x ∈ segment ℝ (P (i + (m : ZMod n))) (P i)) : x = P i ∨ x = P (i + (m : ZMod n)) := by
  rw [← insert_endpoints_openSegment] at hD
  rcases hD with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exfalso
    rw [openSegment_symm] at h
    exact Set.disjoint_left.mp (hclean k) hx h

theorem u4h_val_eq_zero_iff {m : ℕ} (k : ZMod (m + 1)) : k.val = 0 ↔ k = 0 := by
  constructor
  · intro h
    apply ZMod.val_injective
    rw [h, ZMod.val_zero]
  · rintro rfl
    exact ZMod.val_zero

theorem u4h_add_one_eq_neg_one {m : ℕ} {k : ZMod (m + 1)} (hk : k ≠ -1) (h : k.val + 1 = m) :
    k + 1 = -1 := by
  apply ZMod.val_injective
  rw [u4h_val_add_one hk, u4h_val_neg_one', h]

/-- **A sub-polygon along a clean diagonal is embedded.** -/
theorem u4h_subPoly_embedded [NeZero n] {P : LabelledTuple n} (hP : Embedded P) {i : ZMod n}
    {m : ℕ} (hm : 2 ≤ m) (hmn : m + 2 ≤ n)
    (hclean : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P i) (P (i + (m : ZMod n))))) :
    Embedded (u4h_subPoly P i m) := by
  have hDinter := u4h_edge_inter_diag_subPoly hclean
  have hm0 : (m : ZMod n) ≠ 0 := u4h_natCast_ne_zero (by omega) (by omega)
  have hPiPm : P i ≠ P (i + (m : ZMod n)) := by
    intro h
    have := u4h_vertex_injective hP h
    exact hm0 (by linear_combination -this)
  refine ⟨fun k => ?_, fun k l hr => ?_, fun k => ?_⟩
  · by_cases hk : k = -1
    · subst hk
      rw [edge, neg_add_cancel, u4h_subPoly_zero, u4h_subPoly_last]
      exact sub_ne_zero.mpr hPiPm
    · rw [u4h_subPoly_edge P i m hk]
      exact hP.edge_ne_zero _
  · -- remote pairs
    have hadj_self : ∀ j : ZMod (m + 1), adjacent j j := fun j => Or.inr (Or.inl (sub_self j))
    -- the diagonal against a `P`-edge with offset `s ∉ {0, m-1}`
    have hdiag : ∀ l : ZMod (m + 1), l ≠ -1 → remote (-1) l →
        Disjoint (edgeSegment (u4h_subPoly P i m) (-1)) (edgeSegment (u4h_subPoly P i m) l) := by
      intro l hl hr
      have hs := u4h_val_lt_of_ne_neg_one hl
      rw [u4h_subPoly_edgeSegment_last, u4h_subPoly_edgeSegment P i m hl, Set.disjoint_left]
      intro x hxD hxl
      rcases hDinter _ hxl hxD with h | h
      · have h0 := u4h_Pi_mem_offset hP hmn hs (h ▸ hxl)
        apply hr
        rw [(u4h_val_eq_zero_iff l).mp h0]
        exact Or.inr (Or.inr (by ring))
      · have h1 := u4h_Pim_mem_offset hP hmn hs (h ▸ hxl)
        apply hr
        have := u4h_add_one_eq_neg_one hl h1
        exact Or.inl (by linear_combination this)
    by_cases hk : k = -1
    · subst hk
      have hl : l ≠ -1 := fun h => hr (h ▸ hadj_self _)
      exact hdiag l hl hr
    · by_cases hl : l = -1
      · subst hl
        exact (hdiag k hk (remote_symm hr)).symm
      · rw [u4h_subPoly_edgeSegment P i m hk, u4h_subPoly_edgeSegment P i m hl]
        apply hP.remote_disjoint
        have hsk := u4h_val_lt_of_ne_neg_one hk
        have hsl := u4h_val_lt_of_ne_neg_one hl
        rw [remote, u4h_adjacent_offset (by omega) (by omega)]
        rintro (h | h | h)
        · apply hr
          have : l = k + 1 := ZMod.val_injective _ (by rw [u4h_val_add_one hk, h])
          exact Or.inr (Or.inr (by rw [this]; ring))
        · apply hr
          have : l = k := ZMod.val_injective _ h
          exact this ▸ hadj_self k
        · apply hr
          have : k = l + 1 := ZMod.val_injective _ (by rw [u4h_val_add_one hl, h])
          exact Or.inl (by rw [this]; ring)
  · -- consecutive pairs
    by_cases hk : k = -1
    · subst hk
      have h0 : (0 : ZMod (m + 1)) ≠ -1 := by
        intro h
        have := congrArg ZMod.val h
        rw [ZMod.val_zero, u4h_val_neg_one'] at this
        omega
      rw [neg_add_cancel, u4h_subPoly_edgeSegment_last, u4h_subPoly_edgeSegment P i m h0,
        u4h_subPoly_zero, ZMod.val_zero, Nat.cast_zero, add_zero]
      ext x
      constructor
      · rintro ⟨hxD, hxi⟩
        rcases hDinter _ hxi hxD with h | h
        · exact h
        · exfalso
          have := u4h_Pim_mem_offset hP hmn (s := 0) (by omega) (by simpa using h ▸ hxi)
          omega
      · intro hx
        have hx' : x = P i := hx
        rw [hx']
        exact ⟨right_mem_segment ℝ _ _, u4h_start_mem_edgeSegment P i⟩
    · by_cases hk1 : k + 1 = -1
      · have hs : k.val + 1 = m := by
          have := congrArg ZMod.val hk1
          rwa [u4h_val_add_one hk, u4h_val_neg_one'] at this
        rw [hk1, u4h_subPoly_edgeSegment_last, u4h_subPoly_edgeSegment P i m hk, u4h_subPoly_last]
        ext x
        constructor
        · rintro ⟨hxk, hxD⟩
          rcases hDinter _ hxk hxD with h | h
          · exfalso
            have := u4h_Pi_mem_offset hP hmn (u4h_val_lt_of_ne_neg_one hk) (h ▸ hxk)
            omega
          · exact h
        · intro hx
          have hx' : x = P (i + (m : ZMod n)) := hx
          rw [hx']
          refine ⟨?_, left_mem_segment ℝ _ _⟩
          have := u4h_end_mem_edgeSegment P (i + (k.val : ZMod n))
          rwa [add_assoc, ← Nat.cast_add_one, hs] at this
      · rw [u4h_subPoly_edgeSegment P i m hk, u4h_subPoly_edgeSegment P i m hk1,
          u4h_subPoly_apply, u4h_val_add_one hk, Nat.cast_succ, ← add_assoc]
        exact hP.consecutive _

end U4Q_block

section U4R_block

/-! Chains of polygon edges lie on one side of a closed set whose frontier they avoid
(U4 helpers). -/

/-- Extreme points of a segment: a strict convex combination of two segment points equal to an
endpoint forces both points to be that endpoint. -/
theorem u4h_segment_extreme {a b x y : Plane} (hx : x ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1) (h : s • x + t • y = a) :
    x = a := by
  obtain ⟨l, hl0, -, rfl⟩ := (u4h_mem_segment_iff_lin a b x).mp hx
  obtain ⟨l', hl'0, -, rfl⟩ := (u4h_mem_segment_iff_lin a b y).mp hy
  have e : s • (a + l • (b - a)) + t • (a + l' • (b - a)) = a + (s * l + t * l') • (b - a) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, ← add_smul, hst,
      one_smul]
  rw [e] at h
  have h0 : (s * l + t * l') • (b - a) = 0 := add_eq_left.mp h
  rcases smul_eq_zero.mp h0 with h0 | h0
  · have hl : l = 0 := by nlinarith
    rw [hl, zero_smul, add_zero]
  · rw [h0, smul_zero, add_zero]

/-- A segment minus a set of points all of which are endpoints is convex. -/
theorem u4h_convex_segment_diff {a b : Plane} {S : Set Plane}
    (hS : ∀ x ∈ S, x ∈ segment ℝ a b → x = a ∨ x = b) : Convex ℝ (segment ℝ a b \ S) := by
  intro x hx y hy s t hs ht hst
  refine ⟨(convex_segment a b) hx.1 hy.1 hs ht hst, fun hmem => ?_⟩
  have hz : s • x + t • y ∈ segment ℝ a b := (convex_segment a b) hx.1 hy.1 hs ht hst
  rcases hs.lt_or_eq with hs' | hs'
  · rcases ht.lt_or_eq with ht' | ht'
    · rcases hS _ hmem hz with h | h
      · have := u4h_segment_extreme hx.1 hy.1 hs' ht' hst h
        exact hx.2 (this ▸ h ▸ hmem)
      · rw [segment_symm] at hx hy hz
        have := u4h_segment_extreme hx.1 hy.1 hs' ht' hst h
        exact hx.2 (this ▸ h ▸ hmem)
    · have : s = 1 := by linarith
      subst this
      rw [← ht', zero_smul, add_zero, one_smul] at hmem
      exact hx.2 hmem
  · rw [← hs'] at hst
    have : t = 1 := by linarith
    subst this
    rw [← hs', zero_smul, zero_add, one_smul] at hmem
    exact hy.2 hmem

/-- A piece of a chain: an edge with (some of) its endpoints removed is convex. -/
theorem u4h_chain_piece_convex {P : LabelledTuple n} (hP : Embedded P) (k : ZMod n)
    (S : Set Plane) (hS : ∀ x ∈ S, ∃ j, P j = x) :
    Convex ℝ (edgeSegment P k \ S) := by
  rw [u4h_edgeSegment_eq_segment]
  apply u4h_convex_segment_diff
  intro x hxS hx
  obtain ⟨j, rfl⟩ := hS x hxS
  rw [← u4h_edgeSegment_eq_segment] at hx
  rcases u4h_incident_of_vertex_mem hP hx with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h])

/-- **Chain-side lemma.** The edges `E_{i+s}` (`s < m`), with the two chain ends removed, all lie
in the interior of `U` or all lie outside `U`, provided they avoid its frontier. -/
theorem u4h_chain_side [NeZero n] {P : LabelledTuple n} (hP : Embedded P) {i : ZMod n} {m : ℕ}
    (hmn : m + 2 ≤ n) {U : Set Plane} (hU : IsClosed U)
    (hfr : ∀ s : ℕ, s < m → ∀ x ∈ edgeSegment P (i + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) → x ∉ frontier U) :
    (∀ s : ℕ, s < m → ∀ x ∈ edgeSegment P (i + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) → x ∈ interior U) ∨
    (∀ s : ℕ, s < m → ∀ x ∈ edgeSegment P (i + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) → x ∉ U) := by
  set S : Set Plane := {P i, P (i + (m : ZMod n))} with hSdef
  have hSv : ∀ x ∈ S, ∃ j, P j = x := by
    rintro x (rfl | rfl)
    · exact ⟨i, rfl⟩
    · exact ⟨_, rfl⟩
  -- each piece is on one side
  have hpiece : ∀ s : ℕ, s < m →
      (edgeSegment P (i + (s : ZMod n)) \ S ⊆ interior U) ∨
      (edgeSegment P (i + (s : ZMod n)) \ S ⊆ Uᶜ) := by
    intro s hs
    have hconv := u4h_chain_piece_convex hP (i + (s : ZMod n)) S hSv
    have hsub : edgeSegment P (i + (s : ZMod n)) \ S ⊆ interior U ∪ Uᶜ := by
      rintro x ⟨hx, hxS⟩
      by_cases hxU : x ∈ U
      · left
        by_contra hxi
        exact hfr s hs x hx hxS ⟨subset_closure hxU, hxi⟩
      · right; exact hxU
    exact IsPreconnected.subset_or_subset isOpen_interior hU.isOpen_compl
      (Set.disjoint_left.mpr fun y hy hy' => hy' (interior_subset hy)) hsub
      hconv.isPreconnected
  -- consecutive pieces share the vertex `P (i + s + 1)`, which is not a chain end
  have hshared : ∀ s : ℕ, s + 1 < m →
      P (i + ((s + 1 : ℕ) : ZMod n)) ∈ edgeSegment P (i + (s : ZMod n)) \ S ∧
      P (i + ((s + 1 : ℕ) : ZMod n)) ∈ edgeSegment P (i + ((s + 1 : ℕ) : ZMod n)) \ S := by
    intro s hs
    have hnotS : P (i + ((s + 1 : ℕ) : ZMod n)) ∉ S := by
      rintro (h | h)
      · have := u4h_offset_injective (s := s + 1) (s' := 0) (by omega) (by omega) i
          (by rw [Nat.cast_zero, add_zero]; exact u4h_vertex_injective hP h)
        omega
      · have := u4h_offset_injective (s := s + 1) (s' := m) (by omega) (by omega) i
          (u4h_vertex_injective hP h)
        omega
    refine ⟨⟨?_, hnotS⟩, ⟨u4h_start_mem_edgeSegment P _, hnotS⟩⟩
    have := u4h_end_mem_edgeSegment P (i + (s : ZMod n))
    rwa [add_assoc, ← Nat.cast_add_one] at this
  by_cases h0 : edgeSegment P (i + ((0 : ℕ) : ZMod n)) \ S ⊆ interior U
  · left
    have key : ∀ s : ℕ, s < m → edgeSegment P (i + (s : ZMod n)) \ S ⊆ interior U := by
      intro s
      induction s with
      | zero => intro _; exact h0
      | succ s ih =>
        intro hs
        rcases hpiece (s + 1) hs with h | h
        · exact h
        · exfalso
          obtain ⟨h1, h2⟩ := hshared s hs
          exact h h2 (interior_subset (ih (by omega) h1))
    intro s hs x hx hxS
    exact key s hs ⟨hx, hxS⟩
  · right
    by_cases hm : m = 0
    · intro s hs; omega
    have h0' : edgeSegment P (i + ((0 : ℕ) : ZMod n)) \ S ⊆ Uᶜ := by
      rcases hpiece 0 (by omega) with h | h
      · exact absurd h h0
      · exact h
    have key : ∀ s : ℕ, s < m → edgeSegment P (i + (s : ZMod n)) \ S ⊆ Uᶜ := by
      intro s
      induction s with
      | zero => intro _; exact h0'
      | succ s ih =>
        intro hs
        rcases hpiece (s + 1) hs with h | h
        · exfalso
          obtain ⟨h1, h2⟩ := hshared s hs
          exact ih (by omega) h1 (interior_subset (h h2))
        · exact h
    intro s hs x hx hxS
    exact key s hs ⟨hx, hxS⟩

end U4R_block

section U4S_block

/-! The base case: the region of an embedded triangle (U4 helpers). -/

theorem u4h_zmod3_cases (i : ZMod 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  revert i; decide

theorem u4h_range_zmod3 (P : LabelledTuple 3) : Set.range P = {P 0, P 1, P 2} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    rcases u4h_zmod3_cases i with rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

/-- All three turns of a triangle have the same determinant. -/
theorem u4h_tri3_turn (P : LabelledTuple 3) (i : ZMod 3) :
    det (edge P (i - 1)) (edge P i) = det (P 1 - P 0) (P 2 - P 0) := by
  have h01 : (0 : ZMod 3) + 1 = 1 := by decide
  have h12 : (1 : ZMod 3) + 1 = 2 := by decide
  have h20 : (2 : ZMod 3) + 1 = 0 := by decide
  have hm0 : (0 : ZMod 3) - 1 = 2 := by decide
  have hm1 : (1 : ZMod 3) - 1 = 0 := by decide
  have hm2 : (2 : ZMod 3) - 1 = 1 := by decide
  rcases u4h_zmod3_cases i with rfl | rfl | rfl
  · rw [hm0]; simp only [edge, h20, h01]; simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  · rw [hm1]; simp only [edge, h01, h12]; simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  · rw [hm2]; simp only [edge, h12, h20]; simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

/-- An embedded triangle is nondegenerate. -/
theorem u4h_tri3_det_ne_zero (P : LabelledTuple 3) (hP : Embedded P) :
    det (P 1 - P 0) (P 2 - P 0) ≠ 0 := by
  obtain ⟨N, i, -, hturn⟩ := exists_supporting_vertex_turn_ne_zero (le_refl 3) hP
  have hreg := hP.regular (le_refl 3)
  intro hD
  apply hturn
  rw [principalTurn, principalAngle_zero_iff_det_zero (hreg i), u4h_tri3_turn, hD]

/-- The one-face triangulation of a triangle. -/
def u4h_singleTri (T : Triangle) : Triangulation T.carrier where
  faces := {T}
  finite := Set.finite_singleton T
  cover := by simp
  inter := by
    intro T1 h1 T2 h2
    rw [Set.mem_singleton_iff] at h1 h2
    subst h1; subst h2
    rw [Set.inter_self, Set.inter_self]; rfl

theorem u4h_edgeSegment_zmod3 (P : LabelledTuple 3) :
    edgeSegment P 0 = segment ℝ (P 0) (P 1) ∧ edgeSegment P 1 = segment ℝ (P 1) (P 2) ∧
      edgeSegment P 2 = segment ℝ (P 2) (P 0) := by
  have h01 : (0 : ZMod 3) + 1 = 1 := by decide
  have h12 : (1 : ZMod 3) + 1 = 2 := by decide
  have h20 : (2 : ZMod 3) + 1 = 0 := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [u4h_edgeSegment_eq_segment, h01]
  · rw [u4h_edgeSegment_eq_segment, h12]
  · rw [u4h_edgeSegment_eq_segment, h20]

theorem u4h_polygonImage_zmod3 (P : LabelledTuple 3) :
    polygonImage P = segment ℝ (P 0) (P 1) ∪ segment ℝ (P 1) (P 2) ∪ segment ℝ (P 2) (P 0) := by
  obtain ⟨h0, h1, h2⟩ := u4h_edgeSegment_zmod3 P
  ext x
  simp only [polygonImage, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    rcases u4h_zmod3_cases i with rfl | rfl | rfl
    · rw [h0] at hi; exact Or.inl (Or.inl hi)
    · rw [h1] at hi; exact Or.inl (Or.inr hi)
    · rw [h2] at hi; exact Or.inr hi
  · rintro ((h | h) | h)
    · exact ⟨0, h0 ▸ h⟩
    · exact ⟨1, h1 ▸ h⟩
    · exact ⟨2, h2 ▸ h⟩

/-- A region for an embedded triangle built from a face `T` whose vertices are the polygon's,
given the identification of the edges. -/
def u4h_triRegionOf (P : LabelledTuple 3) (T : Triangle)
    (hcar : T.carrier = convexHull ℝ {P 0, P 1, P 2})
    (hfr : frontier T.carrier = polygonImage P)
    (hedges : ∀ i : ZMod 3, ∃ k : Fin 3, T.edgeSeg k = edgeSegment P i)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hside : ∀ i : ZMod 3, ∀ k : Fin 3, T.edgeSeg k = edgeSegment P i →
      0 < σ * det (P (i + 1) - P i) (T.v (k + 2) - P i)) : u4h_Region P where
  U := T.carrier
  K := u4h_singleTri T
  frontier_eq := hfr
  edge_face := fun i => by
    obtain ⟨k, hk⟩ := hedges i
    exact ⟨T, rfl, k, hk⟩
  edge_unique := by
    intro i T1 h1 T2 h2 _ _
    have h1' : T1 = T := h1
    have h2' : T2 = T := h2
    rw [h1', h2']
  hull := by rw [hcar, u4h_range_zmod3]
  int_conn := (convex_convexHull ℝ _).interior.isPreconnected
  σ := σ
  σ_pm := hσ
  side := by
    intro i T1 h1 k hk
    have h1' : T1 = T := h1
    subst h1'
    exact hside i k hk
  count := by
    show (({T} : Set Triangle).image Triangle.carrier).ncard + 2 ≤ 3
    rw [Set.image_singleton, Set.ncard_singleton]

end U4S_block

section U4T_block

/-! The clean diagonal from the lexmin vertex to the farthest invader of its ear triangle
(U4 helpers). -/

/-- Height of `x` above the base line of the ear triangle at `v`, normalised to be positive at
`P v`. -/
def u4h_height (P : LabelledTuple n) (v : ZMod n) (x : Plane) : ℝ :=
  det (P (v + 1) - P (v - 1)) (x - P (v - 1)) * det (P (v + 1) - P (v - 1)) (P v - P (v - 1))

theorem u4h_height_lin (P : LabelledTuple n) (v : ZMod n) (s t : Plane) (l : ℝ) :
    u4h_height P v (s + l • (t - s)) = u4h_height P v s + l * (u4h_height P v t - u4h_height P v s) := by
  simp only [u4h_height, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u4h_height_comb (P : LabelledTuple n) (v : ZMod n) (s t : Plane) (l : ℝ) :
    u4h_height P v ((1 - l) • s + l • t) = (1 - l) * u4h_height P v s + l * u4h_height P v t := by
  simp only [u4h_height, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u4h_height_base (P : LabelledTuple n) (v : ZMod n) {x : Plane}
    (hx : x ∈ segment ℝ (P (v - 1)) (P (v + 1))) : u4h_height P v x = 0 := by
  rw [u4h_height, u4h_det_segment_zero hx, zero_mul]

theorem u4h_height_pos (P : LabelledTuple n) (v : ZMod n)
    (hdet : det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) ≠ 0) : 0 < u4h_height P v (P v) := by
  have : det (P (v + 1) - P (v - 1)) (P v - P (v - 1)) ≠ 0 := by
    rw [u4h_det_swap']; exact neg_ne_zero.mpr hdet
  rw [u4h_height]
  exact mul_self_pos.mpr this

/-- Barycentric description of points of the ear triangle. -/
theorem u4h_earHull_bary (P : LabelledTuple n) (v : ZMod n) {x : Plane} (hx : x ∈ earHull P v) :
    ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
      x = α • P (v - 1) + β • P v + γ • P (v + 1) :=
  (u4h_mem_hull3_iff _ _ _ x).mp hx

theorem u4h_height_bary (P : LabelledTuple n) (v : ZMod n) {α β γ : ℝ} (hsum : α + β + γ = 1) :
    u4h_height P v (α • P (v - 1) + β • P v + γ • P (v + 1)) = β * u4h_height P v (P v) := by
  have hα : α = 1 - β - γ := by linarith
  subst hα
  simp only [u4h_height, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- On the ear triangle the height is nonnegative, at most the height of the apex, and equal to
it only at the apex. -/
theorem u4h_height_le (P : LabelledTuple n) (v : ZMod n)
    (hdet : det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) ≠ 0) {x : Plane} (hx : x ∈ earHull P v) :
    0 ≤ u4h_height P v x ∧ u4h_height P v x ≤ u4h_height P v (P v) ∧
      (u4h_height P v x = u4h_height P v (P v) → x = P v) := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩ := u4h_earHull_bary P v hx
  have hpos := u4h_height_pos P v hdet
  rw [u4h_height_bary P v hsum]
  refine ⟨mul_nonneg hβ hpos.le, ?_, fun h => ?_⟩
  · nlinarith
  · have hβ1 : β = 1 := by
      have : (β - 1) * u4h_height P v (P v) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hpos.ne'
    have hα0 : α = 0 := by linarith
    have hγ0 : γ = 0 := by linarith
    rw [hα0, hβ1, hγ0]; simp

/-- The frontier of a nondegenerate ear triangle. -/
theorem u4h_frontier_earHull (P : LabelledTuple n) (v : ZMod n)
    (hdet : det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) ≠ 0) :
    frontier (earHull P v) =
      edgeSegment P (v - 1) ∪ edgeSegment P v ∪ segment ℝ (P (v - 1)) (P (v + 1)) := by
  rw [u4h_edgeSegment_prev, u4h_edgeSegment_eq_segment]
  rcases lt_or_gt_of_ne hdet with h | h
  · have h' : 0 < det (P (v + 1) - P (v - 1)) (P v - P (v - 1)) := by
      rw [u4h_det_swap']; linarith
    unfold earHull
    rw [u4h_hull3_comm, u4h_frontier_hull3 h', segment_symm ℝ (P (v + 1)) (P v),
      segment_symm ℝ (P v) (P (v - 1))]
    ext x; simp only [Set.mem_union]; tauto
  · unfold earHull
    rw [u4h_frontier_hull3 h, segment_symm ℝ (P (v + 1)) (P (v - 1))]

/-- The invaders of the ear triangle at `v`. -/
def u4h_Inv (P : LabelledTuple n) (v : ZMod n) : Set (ZMod n) :=
  {k | k ≠ v - 1 ∧ k ≠ v ∧ k ≠ v + 1 ∧ P k ∈ earHull P v}

/-- An affine functional has no strict maximum at an inner point of a segment. -/
theorem u4h_no_strict_max_on_segment (P : LabelledTuple n) (v : ZMod n) {s t x : Plane}
    (hx : x ∈ segment ℝ s t)
    (h1 : ∃ z ∈ segment ℝ x s, z ≠ x ∧ u4h_height P v z < u4h_height P v x)
    (h2 : ∃ z ∈ segment ℝ x t, z ≠ x ∧ u4h_height P v z < u4h_height P v x) : False := by
  obtain ⟨z1, hz1, hz1x, hg1⟩ := h1
  obtain ⟨z2, hz2, hz2x, hg2⟩ := h2
  obtain ⟨l, hl0, hl1, rfl⟩ := (u4h_mem_segment_iff_lin s t x).mp hx
  obtain ⟨α, hα0, -, rfl⟩ := (u4h_mem_segment_iff_lin _ s z1).mp hz1
  obtain ⟨β, hβ0, -, rfl⟩ := (u4h_mem_segment_iff_lin _ t z2).mp hz2
  have hαpos : 0 < α := by
    rcases hα0.lt_or_eq with h | h
    · exact h
    · subst h; exact absurd (by simp) hz1x
  have hβpos : 0 < β := by
    rcases hβ0.lt_or_eq with h | h
    · exact h
    · subst h; exact absurd (by simp) hz2x
  rw [u4h_height_lin] at hg1 hg2
  set Gs := u4h_height P v s with hGs
  set Gt := u4h_height P v t with hGt
  have hxeq : u4h_height P v (s + l • (t - s)) = Gs + l * (Gt - Gs) := u4h_height_lin P v s t l
  rw [hxeq] at hg1 hg2
  have h1 : Gs < Gs + l * (Gt - Gs) := by nlinarith
  have h2 : Gt < Gs + l * (Gt - Gs) := by nlinarith
  rcases hl1.lt_or_eq with hl1' | hl1'
  · have := mul_pos (sub_pos.mpr hl1') (sub_pos.mpr h1)
    have := mul_nonneg hl0 (sub_pos.mpr h2).le
    nlinarith
  · subst hl1'
    linarith

/-- **Clean diagonal.** If the ear triangle at `v` contains a vertex other than `v-1, v, v+1`,
then the farthest such vertex `w` gives a diagonal `(P v, P w)` met by no edge, and `P w - P v`
lies strictly inside the cone of the two edge vectors at `v`. -/
theorem u4h_exists_clean_invader [NeZero n] (hn : 4 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (v : ZMod n) (hdet : det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) ≠ 0)
    (hS : ∃ k, k ∈ u4h_Inv P v) :
    ∃ w, w ∈ u4h_Inv P v ∧
      (∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P v) (P w))) ∧
      (∃ α β : ℝ, 0 < α ∧ 0 < β ∧ P w - P v = α • (P (v - 1) - P v) + β • (P (v + 1) - P v)) := by
  classical
  obtain ⟨k0, hk0⟩ := hS
  obtain ⟨w, hw, hwmax⟩ := Finset.exists_max_image (Finset.univ.filter (· ∈ u4h_Inv P v))
    (fun k => u4h_height P v (P k)) ⟨k0, by simp [hk0]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hwmax
  obtain ⟨hw1, hw2, hw3, hwT⟩ := hw
  have hinj := u4h_vertex_injective hP
  -- the cone decomposition
  obtain ⟨la, lv, lc, hla, hlv, hlc, hsum, hPw⟩ := u4h_earHull_bary P v hwT
  have hcone : ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      P w - P v = α • (P (v - 1) - P v) + β • (P (v + 1) - P v) := by
    refine ⟨la, lc, ?_, ?_, ?_⟩
    · rcases hla.lt_or_eq with h | h
      · exact h
      · exfalso
        have hmem : P w ∈ edgeSegment P v := by
          rw [u4h_edgeSegment_eq_segment, hPw, ← h, zero_smul, zero_add]
          exact ⟨lv, lc, hlv, hlc, by linarith, rfl⟩
        rcases u4h_incident_of_vertex_mem hP hmem with h' | h'
        · exact hw2 h'
        · exact hw3 h'
    · rcases hlc.lt_or_eq with h | h
      · exact h
      · exfalso
        have hmem : P w ∈ edgeSegment P (v - 1) := by
          rw [u4h_edgeSegment_prev, hPw, ← h, zero_smul, add_zero]
          exact ⟨la, lv, hla, hlv, by linarith, rfl⟩
        rcases u4h_incident_of_vertex_mem hP hmem with h' | h'
        · exact hw1 h'
        · exact hw2 (by rw [h', sub_add_cancel])
    · rw [hPw]
      have hv' : lv = 1 - la - lc := by linarith
      rw [hv']; module
  refine ⟨w, ⟨hw1, hw2, hw3, hwT⟩, ?_, hcone⟩
  obtain ⟨α, β, hα, hβ, hcone'⟩ := hcone
  -- heights
  have hwlt : u4h_height P v (P w) < u4h_height P v (P v) := by
    obtain ⟨-, hle, heq⟩ := u4h_height_le P v hdet hwT
    exact lt_of_le_of_ne hle fun h => hw2 (hinj (heq h))
  have hwnn : 0 ≤ u4h_height P v (P w) := (u4h_height_le P v hdet hwT).1
  intro k
  rw [Set.disjoint_left]
  intro x hxk hxo
  rw [openSegment_eq_image] at hxo
  obtain ⟨t, ⟨ht0, ht1⟩, hxeq⟩ := hxo
  simp only at hxeq
  have hxh : u4h_height P v x = (1 - t) * u4h_height P v (P v) + t * u4h_height P v (P w) := by
    rw [← hxeq]; exact u4h_height_comb P v _ _ t
  have hxgt : u4h_height P v (P w) < u4h_height P v x := by rw [hxh]; nlinarith
  have hxpos : 0 < u4h_height P v x := by linarith
  have hvT : P v ∈ earHull P v := subset_convexHull ℝ _ (by simp)
  have hxT : x ∈ earHull P v := by
    rw [← hxeq]
    exact (convex_convexHull ℝ _) hvT hwT (by linarith) ht0.le (by ring)
  -- `k ∉ {v-1, v}`
  have hdetc : det (P (v + 1) - P v) (P w - P v) ≠ 0 := by
    rw [hcone', u4h_det_add_right, u4h_det_smul_right, u4h_det_smul_right, u4h_det_self,
      mul_zero, add_zero]
    have : det (P (v + 1) - P v) (P (v - 1) - P v) ≠ 0 := by
      have e : det (P (v + 1) - P v) (P (v - 1) - P v) =
          det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) := by
        simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
      rw [e]; exact hdet
    exact mul_ne_zero hα.ne' this
  have hdeta : det (P (v - 1) - P v) (P w - P v) ≠ 0 := by
    rw [hcone', u4h_det_add_right, u4h_det_smul_right, u4h_det_smul_right, u4h_det_self,
      mul_zero, zero_add]
    have : det (P (v - 1) - P v) (P (v + 1) - P v) ≠ 0 := by
      have e : det (P (v - 1) - P v) (P (v + 1) - P v) =
          -det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) := by
        simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
      rw [e]; exact neg_ne_zero.mpr hdet
    exact mul_ne_zero hβ.ne' this
  have hxv : x - P v = t • (P w - P v) := by rw [← hxeq]; module
  have hkv : k ≠ v := by
    rintro rfl
    rw [u4h_edgeSegment_eq_segment, u4h_mem_segment_iff_lin] at hxk
    obtain ⟨l, -, -, hl⟩ := hxk
    have : det (P (k + 1) - P k) (x - P k) = 0 := by
      rw [hl, add_sub_cancel_left, u4h_det_smul_right, u4h_det_self, mul_zero]
    rw [hxv, u4h_det_smul_right] at this
    rcases mul_eq_zero.mp this with h | h
    · exact ht0.ne' h
    · exact hdetc h
  have hkv1 : k ≠ v - 1 := by
    intro hk
    subst hk
    rw [u4h_edgeSegment_prev, segment_symm, u4h_mem_segment_iff_lin] at hxk
    obtain ⟨l, -, -, hl⟩ := hxk
    have : det (P (v - 1) - P v) (x - P v) = 0 := by
      rw [hl, add_sub_cancel_left, u4h_det_smul_right, u4h_det_self, mul_zero]
    rw [hxv, u4h_det_smul_right] at this
    rcases mul_eq_zero.mp this with h | h
    · exact ht0.ne' h
    · exact hdeta h
  -- both endpoints of `E_k` give lower points of the segment
  have hEk := u4h_edgeSegment_eq_segment P k
  have hside : ∀ e : Plane, e ∈ edgeSegment P k → (∃ j, P j = e) →
      ∃ z ∈ segment ℝ x e, z ≠ x ∧ u4h_height P v z < u4h_height P v x := by
    rintro e he ⟨j, rfl⟩
    by_cases heT : P j ∈ earHull P v
    · -- a vertex in the triangle: `v-1`, `v+1` or an invader
      have hj : u4h_height P v (P j) ≤ u4h_height P v (P w) := by
        by_cases hj1 : j = v - 1
        · subst hj1; rw [u4h_height_base P v (left_mem_segment ℝ _ _)]; exact hwnn
        by_cases hj3 : j = v + 1
        · subst hj3; rw [u4h_height_base P v (right_mem_segment ℝ _ _)]; exact hwnn
        by_cases hj2 : j = v
        · exfalso
          subst hj2
          rcases u4h_incident_of_vertex_mem hP he with h | h
          · exact hkv h.symm
          · exact hkv1 (by rw [h, add_sub_cancel_right])
        exact hwmax j ⟨hj1, hj2, hj3, heT⟩
      refine ⟨P j, right_mem_segment ℝ _ _, fun h => ?_, by linarith⟩
      rw [h] at hj; linarith
    · obtain ⟨z, hz, hzf⟩ := u4h_preconnected_inter_frontier (convex_segment x (P j)).isPreconnected
        ⟨x, left_mem_segment ℝ _ _, hxT⟩ ⟨P j, right_mem_segment ℝ _ _, heT⟩
      have hzk : z ∈ edgeSegment P k := by
        rw [hEk] at hxk he ⊢
        exact (convex_segment _ _).segment_subset hxk he hz
      have hz0 : u4h_height P v z = 0 := by
        rw [u4h_frontier_earHull P v hdet] at hzf
        rcases hzf with h | h
        · rcases u4h_edge_inter_ears hP hkv1 hkv ⟨hzk, h⟩ with h' | h'
          · rw [h']; exact u4h_height_base P v (left_mem_segment ℝ _ _)
          · rw [h']; exact u4h_height_base P v (right_mem_segment ℝ _ _)
        · exact u4h_height_base P v h
      refine ⟨z, hz, fun h => ?_, by rw [hz0]; exact hxpos⟩
      rw [h] at hz0; linarith
  rw [hEk] at hxk
  exact u4h_no_strict_max_on_segment P v hxk
    (hside (P k) (u4h_start_mem_edgeSegment P k) ⟨k, rfl⟩)
    (hside (P (k + 1)) (u4h_end_mem_edgeSegment P k) ⟨k + 1, rfl⟩)

end U4T_block

section U4U_block

/-! Splitting along a clean diagonal, part 1 (U4 helpers): the two chains and `U1 ∩ U2`. -/

theorem u4h_split_second_start [NeZero n] {m : ℕ} (hmn : m ≤ n) (i : ZMod n) :
    (i + (m : ZMod n)) + ((n - m : ℕ) : ZMod n) = i := by
  rw [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' hmn, ZMod.natCast_self, add_zero]

/-- Every index is `i + s` for a unique offset `s < n`. -/
theorem u4h_index_offset [NeZero n] (i k : ZMod n) : ∃ s : ℕ, s < n ∧ k = i + (s : ZMod n) :=
  ⟨(k - i).val, ZMod.val_lt _, by rw [ZMod.natCast_zmod_val]; ring⟩

theorem u4h_mem_polygonImage_iff_offset [NeZero n] (P : LabelledTuple n) (i : ZMod n) (x : Plane) :
    x ∈ polygonImage P ↔ ∃ s : ℕ, s < n ∧ x ∈ edgeSegment P (i + (s : ZMod n)) := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    obtain ⟨s, hs, rfl⟩ := u4h_index_offset i k
    exact ⟨s, hs, hk⟩
  · rintro ⟨s, -, hx⟩
    exact Set.mem_iUnion.mpr ⟨_, hx⟩

/-- Adjacency of `i + s` and `i + s'` for offsets `< n`, including the wrap-around. -/
theorem u4h_adjacent_offset' [NeZero n] {s s' : ℕ} (hs : s < n) (hs' : s' < n) (i : ZMod n)
    (h : adjacent (i + (s : ZMod n)) (i + (s' : ZMod n))) :
    s' = s + 1 ∨ s' = s ∨ s = s' + 1 ∨ (s = 0 ∧ s' + 1 = n) ∨ (s' = 0 ∧ s + 1 = n) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have key : ∀ x : ℤ, -(n : ℤ) ≤ x → x ≤ n → ((x : ℤ) : ZMod n) = 0 →
      x = 0 ∨ x = -n ∨ x = n := by
    intro x h1 h2 h0
    obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x n).mp h0
    have hc1 : c ≤ 1 := by
      by_contra hc'
      have : (2 : ℤ) ≤ c := by omega
      nlinarith
    have hc2 : -1 ≤ c := by
      by_contra hc'
      have : c ≤ -2 := by omega
      nlinarith
    interval_cases c
    · right; left; rw [hc]; ring
    · left; rw [hc]; ring
    · right; right; rw [hc]; ring
  rw [u4h_adjacent_iff] at h
  rcases h with h | h | h
  · have h' : (((s' : ℤ) - s + 1 : ℤ) : ZMod n) = 0 := by push_cast; linear_combination h
    rcases key _ (by omega) (by omega) h' with h'' | h'' | h'' <;> omega
  · have h' : (((s' : ℤ) - s : ℤ) : ZMod n) = 0 := by push_cast; linear_combination h
    rcases key _ (by omega) (by omega) h' with h'' | h'' | h'' <;> omega
  · have h' : (((s' : ℤ) - s - 1 : ℤ) : ZMod n) = 0 := by push_cast; linear_combination h
    rcases key _ (by omega) (by omega) h' with h'' | h'' | h'' <;> omega

/-- Edges of the two chains meet only at the diagonal endpoints. -/
theorem u4h_cross_chain_inter [NeZero n] {P : LabelledTuple n} (hP : Embedded P) (i : ZMod n)
    {m : ℕ} (hm : 2 ≤ m) (hmn : m + 2 ≤ n) {s s' : ℕ} (hs : s < m) (hs' : s' < n - m) :
    edgeSegment P (i + (s : ZMod n)) ∩ edgeSegment P (i + (m : ZMod n) + (s' : ZMod n)) ⊆
      {P i, P (i + (m : ZMod n))} := by
  rintro x ⟨hx1, hx2⟩
  have e2 : i + (m : ZMod n) + (s' : ZMod n) = i + ((m + s' : ℕ) : ZMod n) := by
    push_cast; ring
  rw [e2] at hx2
  by_cases hadj : adjacent (i + (s : ZMod n)) (i + ((m + s' : ℕ) : ZMod n))
  · rcases u4h_adjacent_offset' (by omega) (by omega) i hadj with h | h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- `m + s' = s + 1`: `s = m - 1`, `s' = 0`, shared vertex `P (i + m)`
      have hs0 : s' = 0 := by omega
      have hsm : s + 1 = m := by omega
      have hc := hP.consecutive (i + (s : ZMod n))
      have hmem : x ∈ edgeSegment P (i + (s : ZMod n)) ∩ edgeSegment P (i + (s : ZMod n) + 1) := by
        refine ⟨hx1, ?_⟩
        rw [add_assoc, ← Nat.cast_add_one, hsm]
        rw [hs0, add_zero] at hx2
        exact hx2
      rw [hc] at hmem
      right
      rw [add_assoc, ← Nat.cast_add_one, hsm] at hmem
      exact hmem
    · omega
    · omega
    · -- `s = 0`, `m + s' = n - 1`: shared vertex `P i`
      have hc := hP.consecutive (i + ((m + s' : ℕ) : ZMod n))
      have hnext : i + ((m + s' : ℕ) : ZMod n) + 1 = i := by
        rw [add_assoc, ← Nat.cast_add_one, h2, ZMod.natCast_self, add_zero]
      rw [hnext] at hc
      have hmem : x ∈ edgeSegment P (i + ((m + s' : ℕ) : ZMod n)) ∩ edgeSegment P i := by
        refine ⟨hx2, ?_⟩
        rw [h1, Nat.cast_zero, add_zero] at hx1
        exact hx1
      rw [hc] at hmem
      left
      exact hmem
    · omega
  · exact (Set.disjoint_left.mp (hP.remote_disjoint _ _ hadj) hx1 hx2).elim

/-- Membership in the polygon image of the second sub-polygon. -/
theorem u4h_mem_polygonImage_subPoly2 [NeZero n] (P : LabelledTuple n) (i : ZMod n) {m : ℕ}
    (hmn : m ≤ n) (x : Plane) :
    x ∈ polygonImage (u4h_subPoly P (i + (m : ZMod n)) (n - m)) ↔
      (∃ s : ℕ, s < n - m ∧ x ∈ edgeSegment P (i + (m : ZMod n) + (s : ZMod n))) ∨
        x ∈ segment ℝ (P i) (P (i + (m : ZMod n))) := by
  rw [u4h_mem_polygonImage_subPoly, u4h_split_second_start hmn]

/-- A point of the first chain off the diagonal endpoints avoids the second polygon image. -/
theorem u4h_chain1_avoid [NeZero n] {P : LabelledTuple n} (hP : Embedded P) (i : ZMod n) {m : ℕ}
    (hm : 2 ≤ m) (hmn : m + 2 ≤ n)
    (hclean : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P i) (P (i + (m : ZMod n)))))
    {s : ℕ} (hs : s < m) {x : Plane} (hx : x ∈ edgeSegment P (i + (s : ZMod n)))
    (hxe : x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane)) :
    x ∉ polygonImage (u4h_subPoly P (i + (m : ZMod n)) (n - m)) := by
  intro hmem
  rcases (u4h_mem_polygonImage_subPoly2 P i (by omega) x).mp hmem with ⟨s', hs', hx'⟩ | hD
  · exact hxe (u4h_cross_chain_inter hP i hm hmn hs hs' ⟨hx, hx'⟩)
  · rw [segment_symm] at hD
    rcases u4h_edge_inter_diag_subPoly hclean _ hx hD with h | h
    · exact hxe (Or.inl h)
    · exact hxe (Or.inr h)

/-- A point of the second chain off the diagonal endpoints avoids the first polygon image. -/
theorem u4h_chain2_avoid [NeZero n] {P : LabelledTuple n} (hP : Embedded P) (i : ZMod n) {m : ℕ}
    (hm : 2 ≤ m) (hmn : m + 2 ≤ n)
    (hclean : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P i) (P (i + (m : ZMod n)))))
    {s : ℕ} (hs : s < n - m) {x : Plane} (hx : x ∈ edgeSegment P (i + (m : ZMod n) + (s : ZMod n)))
    (hxe : x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane)) :
    x ∉ polygonImage (u4h_subPoly P i m) := by
  intro hmem
  rcases (u4h_mem_polygonImage_subPoly P i m x).mp hmem with ⟨s', hs', hx'⟩ | hD
  · exact hxe (u4h_cross_chain_inter hP i hm hmn hs' hs ⟨hx', hx⟩)
  · rcases u4h_edge_inter_diag_subPoly hclean _ hx hD with h | h
    · exact hxe (Or.inl h)
    · exact hxe (Or.inr h)

end U4U_block

section U4V_block

/-! Splitting along a clean diagonal, part 2 (U4 helpers): the chains lie outside the other
region, `U1 ∩ U2` is the diagonal, the faces at the diagonal lie on opposite sides. -/

/-- (V1) the first chain lies outside the second region. -/
theorem u4h_chain1_outside [NeZero n] {P : LabelledTuple n} (hP : Embedded P) (i : ZMod n)
    {m : ℕ} (hm : 2 ≤ m) (hmn : m + 2 ≤ n)
    (hclean : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P i) (P (i + (m : ZMod n)))))
    (R2 : u4h_Region (u4h_subPoly P (i + (m : ZMod n)) (n - m)))
    (X1 : ∃ s : ℕ, s < m ∧ ∃ x ∈ edgeSegment P (i + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) ∧ x ∉ R2.U) :
    ∀ s : ℕ, s < m → ∀ x ∈ edgeSegment P (i + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) → x ∉ R2.U := by
  have hside := u4h_chain_side hP (i := i) (m := m) hmn R2.isClosed (fun s hs x hx hxe => by
    rw [R2.frontier_eq]; exact u4h_chain1_avoid hP i hm hmn hclean hs hx hxe)
  rcases hside with h | h
  · exfalso
    obtain ⟨s, hs, x, hx, hxe, hxU⟩ := X1
    exact hxU (interior_subset (h s hs x hx hxe))
  · exact h

/-- (V2) the second chain lies outside the first region. -/
theorem u4h_chain2_outside [NeZero n] {P : LabelledTuple n} (hP : Embedded P) (i : ZMod n)
    {m : ℕ} (hm : 2 ≤ m) (hmn : m + 2 ≤ n)
    (hclean : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P i) (P (i + (m : ZMod n)))))
    (R1 : u4h_Region (u4h_subPoly P i m))
    (X2 : ∃ s : ℕ, s < n - m ∧ ∃ x ∈ edgeSegment P (i + (m : ZMod n) + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) ∧ x ∉ R1.U) :
    ∀ s : ℕ, s < n - m → ∀ x ∈ edgeSegment P (i + (m : ZMod n) + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) → x ∉ R1.U := by
  have hends : ({P (i + (m : ZMod n)), P (i + (m : ZMod n) + ((n - m : ℕ) : ZMod n))} : Set Plane)
      = {P i, P (i + (m : ZMod n))} := by
    rw [u4h_split_second_start (by omega), Set.pair_comm]
  have hside := u4h_chain_side hP (i := i + (m : ZMod n)) (m := n - m) (by omega) R1.isClosed
    (fun s hs x hx hxe => by
      rw [R1.frontier_eq]
      rw [hends] at hxe
      exact u4h_chain2_avoid hP i hm hmn hclean hs hx hxe)
  rcases hside with h | h
  · exfalso
    obtain ⟨s, hs, x, hx, hxe, hxU⟩ := X2
    rw [← hends] at hxe
    exact hxU (interior_subset (h s hs x hx hxe))
  · intro s hs x hx hxe
    rw [← hends] at hxe
    exact h s hs x hx hxe

/-- The diagonal lies in both regions. -/
theorem u4h_diag_subset_regions [NeZero n] {P : LabelledTuple n} (i : ZMod n) {m : ℕ}
    (hmn : m + 2 ≤ n) (R1 : u4h_Region (u4h_subPoly P i m))
    (R2 : u4h_Region (u4h_subPoly P (i + (m : ZMod n)) (n - m))) :
    segment ℝ (P i) (P (i + (m : ZMod n))) ⊆ R1.U ∧
      segment ℝ (P i) (P (i + (m : ZMod n))) ⊆ R2.U := by
  constructor
  · intro x hx
    have : x ∈ polygonImage (u4h_subPoly P i m) := by
      rw [u4h_mem_polygonImage_subPoly]; right; rw [segment_symm]; exact hx
    rw [← R1.frontier_eq] at this
    exact R1.isClosed.frontier_subset this
  · intro x hx
    have : x ∈ polygonImage (u4h_subPoly P (i + (m : ZMod n)) (n - m)) := by
      rw [u4h_mem_polygonImage_subPoly2 P i (by omega)]; right; exact hx
    rw [← R2.frontier_eq] at this
    exact R2.isClosed.frontier_subset this

/-- (V3) `U1 ∩ U2` is the diagonal. -/
theorem u4h_split_inter [NeZero n] {P : LabelledTuple n} (hP : Embedded P) (i : ZMod n)
    {m : ℕ} (hm : 2 ≤ m) (hmn : m + 2 ≤ n)
    (hclean : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P i) (P (i + (m : ZMod n)))))
    (R1 : u4h_Region (u4h_subPoly P i m))
    (R2 : u4h_Region (u4h_subPoly P (i + (m : ZMod n)) (n - m)))
    (X1 : ∃ s : ℕ, s < m ∧ ∃ x ∈ edgeSegment P (i + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) ∧ x ∉ R2.U)
    (X2 : ∃ s : ℕ, s < n - m ∧ ∃ x ∈ edgeSegment P (i + (m : ZMod n) + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) ∧ x ∉ R1.U) :
    R1.U ∩ R2.U = segment ℝ (P i) (P (i + (m : ZMod n))) := by
  have hout1 := u4h_chain1_outside hP i hm hmn hclean R2 X1
  have hout2 := u4h_chain2_outside hP i hm hmn hclean R1 X2
  obtain ⟨hD1, hD2⟩ := u4h_diag_subset_regions i hmn R1 R2
  have hendsD : ∀ x ∈ ({P i, P (i + (m : ZMod n))} : Set Plane),
      x ∈ segment ℝ (P i) (P (i + (m : ZMod n))) := by
    rintro x (rfl | rfl)
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  apply Set.Subset.antisymm
  · rintro x ⟨hx1, hx2⟩
    by_contra hxD
    -- `x` is interior to both regions
    have hxi1 : x ∈ interior R1.U := by
      by_contra h
      have hxf : x ∈ frontier R1.U := ⟨subset_closure hx1, h⟩
      rw [R1.frontier_eq, u4h_mem_polygonImage_subPoly] at hxf
      rcases hxf with ⟨s, hs, hx⟩ | hD
      · have hxe : x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) := fun h => hxD (hendsD x h)
        exact hout1 s hs x hx hxe hx2
      · rw [segment_symm] at hD; exact hxD hD
    have hxi2 : x ∈ interior R2.U := by
      by_contra h
      have hxf : x ∈ frontier R2.U := ⟨subset_closure hx2, h⟩
      rw [R2.frontier_eq, u4h_mem_polygonImage_subPoly2 P i (by omega)] at hxf
      rcases hxf with ⟨s, hs, hx⟩ | hD
      · have hxe : x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) := fun h => hxD (hendsD x h)
        exact hout2 s hs x hx hxe hx1
      · exact hxD hD
    -- `interior U1 ⊆ interior U2 ∪ U2ᶜ`
    have hsub : interior R1.U ⊆ interior R2.U ∪ R2.Uᶜ := by
      intro y hy
      by_cases hy2 : y ∈ R2.U
      · left
        by_contra hyi
        have hyf : y ∈ frontier R2.U := ⟨subset_closure hy2, hyi⟩
        rw [R2.frontier_eq, u4h_mem_polygonImage_subPoly2 P i (by omega)] at hyf
        have hy1 : y ∉ frontier R1.U := disjoint_interior_frontier.notMem_of_mem_left hy
        rcases hyf with ⟨s, hs, hyE⟩ | hD
        · have hye : y ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) := by
            intro h
            apply hy1
            rw [R1.frontier_eq, u4h_mem_polygonImage_subPoly]
            right; rw [segment_symm]; exact hendsD y h
          exact hout2 s hs y hyE hye (interior_subset hy)
        · apply hy1
          rw [R1.frontier_eq, u4h_mem_polygonImage_subPoly]
          right; rw [segment_symm]; exact hD
      · right; exact hy2
    rcases IsPreconnected.subset_or_subset isOpen_interior R2.isClosed.isOpen_compl
        (Set.disjoint_left.mpr fun y hy hy' => hy' (interior_subset hy)) hsub R1.int_conn
        with h | h
    · -- `U1 ⊆ U2`, contradicting `X1`
      have hU : R1.U ⊆ R2.U := by
        rw [← u4h_triangulation_closure_interior R1.K]
        exact (closure_mono h).trans
          (closure_minimal interior_subset R2.isClosed)
      obtain ⟨s, hs, y, hy, -, hyU⟩ := X1
      apply hyU
      apply hU
      have : y ∈ polygonImage (u4h_subPoly P i m) := by
        rw [u4h_mem_polygonImage_subPoly]; exact Or.inl ⟨s, hs, hy⟩
      rw [← R1.frontier_eq] at this
      exact R1.isClosed.frontier_subset this
    · exact h hxi1 hx2
  · intro x hx
    exact ⟨hD1 hx, hD2 hx⟩

/-- (V5) Half-disc lemma at an inner point of a face edge, in terms of the directed edge
`e1 → e2` and the apex. -/
theorem u4h_face_halfdisc (F : Triangle) (k : Fin 3) {e1 e2 : Plane}
    (hFk : F.edgeSeg k = segment ℝ e1 e2) {x : Plane} (hx : x ∈ openSegment ℝ e1 e2) :
    ∃ ε > 0, ∀ y, dist y x < ε →
      (y ∈ F.carrier ↔ 0 ≤ det (e2 - e1) (F.v (k + 2) - e1) * det (e2 - e1) (y - e1)) := by
  have hD : 0 < det (F.v (k + 2) - F.v (k + 1)) (F.v k - F.v (k + 1)) := by
    rw [u4h_det_rot1]; exact u4h_tri_pos F k
  have hcar : F.carrier = convexHull ℝ {F.v (k + 1), F.v (k + 2), F.v k} := by
    rw [u4h_tri_carrier_rot F k, u4h_hull3_rot]
  rcases u4h_face_edge_ends F k hFk with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hx' : x ∈ openSegment ℝ (F.v k) (F.v (k + 1)) := by rw [h0, h1]; exact hx
    obtain ⟨ε, hε, hball⟩ := u4h_halfdisc hD hx'
    refine ⟨ε, hε, fun y hy => ?_⟩
    rw [hcar, hball y hy, h0, h1]
    have hpos : 0 < det (e2 - e1) (F.v (k + 2) - e1) := by
      rw [← h0, ← h1]; exact u4h_tri_pos F k
    constructor
    · intro h; exact mul_nonneg hpos.le h
    · intro h; exact nonneg_of_mul_nonneg_right h hpos |> fun h' => by
        nlinarith
  · have hx' : x ∈ openSegment ℝ (F.v k) (F.v (k + 1)) := by
      rw [h0, h1, openSegment_symm]; exact hx
    obtain ⟨ε, hε, hball⟩ := u4h_halfdisc hD hx'
    refine ⟨ε, hε, fun y hy => ?_⟩
    rw [hcar, hball y hy, h0, h1]
    have hpos : 0 < det (e1 - e2) (F.v (k + 2) - e2) := by
      rw [← h0, ← h1]; exact u4h_tri_pos F k
    have e1' : det (e1 - e2) (y - e2) = -det (e2 - e1) (y - e1) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
    have e2' : det (e2 - e1) (F.v (k + 2) - e1) = -det (e1 - e2) (F.v (k + 2) - e2) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e1', e2']
    constructor
    · intro h; nlinarith
    · intro h; nlinarith

end U4V_block

section U4W_block

/-! Splitting along a clean diagonal, part 3 (U4 helpers): opposite sides at the diagonal, the
open diagonal is interior to the union, frontier and interior of the union. -/

/-- The apex of a face is off the line of any of its edges (signed). -/
theorem u4h_apex_det_ne_zero (F : Triangle) (k : Fin 3) {e1 e2 : Plane}
    (hFk : F.edgeSeg k = segment ℝ e1 e2) : det (e2 - e1) (F.v (k + 2) - e1) ≠ 0 := by
  rcases u4h_face_edge_ends F k hFk with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [← h0, ← h1]; exact (u4h_tri_pos F k).ne'
  · have e : det (e2 - e1) (F.v (k + 2) - e1) = -det (e1 - e2) (F.v (k + 2) - e2) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e, ← h0, ← h1]; exact neg_ne_zero.mpr (u4h_tri_pos F k).ne'

theorem u4h_midpoint_mem_openSegment (e1 e2 : Plane) :
    (1 / 2 : ℝ) • e1 + (1 / 2 : ℝ) • e2 ∈ openSegment ℝ e1 e2 :=
  ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩

/-- (V6) Two faces of the two regions at the common diagonal lie on opposite sides. -/
theorem u4h_split_opposite {U1 U2 : Set Plane} {e1 e2 : Plane}
    (hinter : U1 ∩ U2 = segment ℝ e1 e2) {F1 F2 : Triangle} (hF1U : F1.carrier ⊆ U1)
    (hF2U : F2.carrier ⊆ U2) {k1 k2 : Fin 3} (hk1 : F1.edgeSeg k1 = segment ℝ e1 e2)
    (hk2 : F2.edgeSeg k2 = segment ℝ e1 e2) :
    det (e2 - e1) (F1.v (k1 + 2) - e1) * det (e2 - e1) (F2.v (k2 + 2) - e1) < 0 := by
  set s1 := det (e2 - e1) (F1.v (k1 + 2) - e1) with hs1
  set s2 := det (e2 - e1) (F2.v (k2 + 2) - e1) with hs2
  have hs1ne : s1 ≠ 0 := u4h_apex_det_ne_zero F1 k1 hk1
  have hs2ne : s2 ≠ 0 := u4h_apex_det_ne_zero F2 k2 hk2
  by_contra hcon
  have hpos : 0 < s1 * s2 := lt_of_le_of_ne (not_lt.mp hcon) (Ne.symm (mul_ne_zero hs1ne hs2ne))
  set x : Plane := (1 / 2 : ℝ) • e1 + (1 / 2 : ℝ) • e2 with hx
  have hxo : x ∈ openSegment ℝ e1 e2 := u4h_midpoint_mem_openSegment _ _
  obtain ⟨ε1, hε1, h1⟩ := u4h_face_halfdisc F1 k1 hk1 hxo
  obtain ⟨ε2, hε2, h2⟩ := u4h_face_halfdisc F2 k2 hk2 hxo
  set w := F1.v (k1 + 2) - e1 with hw
  set η : ℝ := min ε1 ε2 / (2 * (‖w‖ + 1)) with hη
  have hηpos : 0 < η := by positivity
  set y := x + η • w with hy
  have hdist : dist y x < min ε1 ε2 := by
    rw [hy, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hηpos, hη,
      div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w, lt_min hε1 hε2]
  have hdet : det (e2 - e1) (y - e1) = η * s1 := by
    rw [hy, hx]
    simp only [hs1, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, hw]; ring
  have hy1 : y ∈ F1.carrier := by
    rw [h1 y (lt_of_lt_of_le hdist (min_le_left _ _)), hdet]
    nlinarith [mul_self_nonneg s1]
  have hy2 : y ∈ F2.carrier := by
    rw [h2 y (lt_of_lt_of_le hdist (min_le_right _ _)), hdet]
    nlinarith
  have hyD : y ∈ segment ℝ e1 e2 := by rw [← hinter]; exact ⟨hF1U hy1, hF2U hy2⟩
  have := u4h_det_segment_zero hyD
  rw [hdet] at this
  rcases mul_eq_zero.mp this with h | h
  · exact hηpos.ne' h
  · exact hs1ne h

/-- (V8) The open diagonal is interior to the union of the two regions. -/
theorem u4h_split_openDiag_interior {U1 U2 : Set Plane} {e1 e2 : Plane}
    (hinter : U1 ∩ U2 = segment ℝ e1 e2) {F1 F2 : Triangle} (hF1U : F1.carrier ⊆ U1)
    (hF2U : F2.carrier ⊆ U2) {k1 k2 : Fin 3} (hk1 : F1.edgeSeg k1 = segment ℝ e1 e2)
    (hk2 : F2.edgeSeg k2 = segment ℝ e1 e2) :
    openSegment ℝ e1 e2 ⊆ interior (U1 ∪ U2) := by
  intro x hx
  have hopp := u4h_split_opposite hinter hF1U hF2U hk1 hk2
  obtain ⟨ε1, hε1, h1⟩ := u4h_face_halfdisc F1 k1 hk1 hx
  obtain ⟨ε2, hε2, h2⟩ := u4h_face_halfdisc F2 k2 hk2 hx
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun y hy => ?_⟩
  rw [Metric.mem_ball] at hy
  by_cases hside : 0 ≤ det (e2 - e1) (F1.v (k1 + 2) - e1) * det (e2 - e1) (y - e1)
  · left
    exact hF1U ((h1 y (lt_of_lt_of_le hy (min_le_left _ _))).mpr hside)
  · right
    apply hF2U
    rw [h2 y (lt_of_lt_of_le hy (min_le_right _ _))]
    have hside' := not_le.mp hside
    nlinarith [mul_self_nonneg (det (e2 - e1) (F1.v (k1 + 2) - e1))]

/-- The frontier of a union lies in the union of the frontiers. -/
theorem u4h_frontier_union_subset {α : Type*} [TopologicalSpace α] (s t : Set α) :
    frontier (s ∪ t) ⊆ frontier s ∪ frontier t := by
  intro x hx
  rw [frontier, closure_union] at hx
  obtain ⟨hcl, hint⟩ := hx
  rcases hcl with h | h
  · exact Or.inl ⟨h, fun h' => hint (interior_mono Set.subset_union_left h')⟩
  · exact Or.inr ⟨h, fun h' => hint (interior_mono Set.subset_union_right h')⟩

/-- The midpoint of an edge is not a vertex. -/
theorem u4h_midpoint_not_vertex {P : LabelledTuple n} (hP : Embedded P) (k : ZMod n) :
    (1 / 2 : ℝ) • P k + (1 / 2 : ℝ) • P (k + 1) ∈ edgeSegment P k ∧
      ∀ j, P j ≠ (1 / 2 : ℝ) • P k + (1 / 2 : ℝ) • P (k + 1) := by
  have hne : P k ≠ P (k + 1) := fun h => hP.edge_ne_zero k (by rw [edge, ← h, sub_self])
  have hmem : (1 / 2 : ℝ) • P k + (1 / 2 : ℝ) • P (k + 1) ∈ edgeSegment P k := by
    rw [u4h_edgeSegment_eq_segment]
    exact openSegment_subset_segment ℝ _ _ (u4h_midpoint_mem_openSegment _ _)
  refine ⟨hmem, fun j hj => ?_⟩
  have hjmem : P j ∈ edgeSegment P k := hj ▸ hmem
  have hno := u4h_midpoint_mem_openSegment (P k) (P (k + 1))
  rw [← hj] at hno
  rcases u4h_incident_of_vertex_mem hP hjmem with h | h
  · rw [h] at hno; exact hne (left_mem_openSegment_iff.mp hno)
  · rw [h] at hno; exact hne (right_mem_openSegment_iff.mp hno)

/-- If all non-vertex points of an edge avoid `interior U`, so do all its points (approach a
vertex along the edge). -/
theorem u4h_edge_not_interior {P : LabelledTuple n} (hP : Embedded P) (k : ZMod n) {U : Set Plane}
    {S : Set Plane} (hS : ∀ x ∈ S, ∃ j, P j = x)
    (hA : ∀ y ∈ edgeSegment P k, y ∉ S → y ∉ interior U) {z : Plane} (hz : z ∈ edgeSegment P k) :
    z ∉ interior U := by
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hint)
  have hw0 : P (k + 1) - P k ≠ 0 := hP.edge_ne_zero k
  rw [u4h_edgeSegment_eq_segment, u4h_mem_segment_iff_lin] at hz
  obtain ⟨l, hl0, hl1, rfl⟩ := hz
  set w := P (k + 1) - P k with hw
  set δ : ℝ := min (1 / 4) (ε / (2 * (‖w‖ + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 4 := min_le_left _ _
  have hδε : δ * ‖w‖ < ε := by
    have h1 : δ ≤ ε / (2 * (‖w‖ + 1)) := min_le_right _ _
    have h2 : δ * ‖w‖ ≤ ε / (2 * (‖w‖ + 1)) * ‖w‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h3 : ε / (2 * (‖w‖ + 1)) * ‖w‖ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [norm_nonneg w]
    linarith
  -- a nearby parameter strictly inside `(0, 1)`
  obtain ⟨l', hl'0, hl'1, hl'd⟩ : ∃ l' : ℝ, 0 < l' ∧ l' < 1 ∧ |l' - l| ≤ δ := by
    by_cases hl : l ≤ 1 / 2
    · exact ⟨l + δ, by linarith, by linarith, by rw [add_sub_cancel_left, abs_of_pos hδ0]⟩
    · exact ⟨l - δ, by linarith, by linarith, by
        rw [sub_sub_cancel_left, abs_neg, abs_of_pos hδ0]⟩
  set y := P k + l' • w with hy
  have hymem : y ∈ edgeSegment P k := by
    rw [u4h_edgeSegment_eq_segment]; exact u4h_lin_mem_segment _ _ hl'0.le hl'1.le
  have hynot : y ∉ S := by
    intro hyS
    obtain ⟨j, hj⟩ := hS y hyS
    have hjmem : P j ∈ edgeSegment P k := hj ▸ hymem
    rcases u4h_incident_of_vertex_mem hP hjmem with h | h
    · rw [h] at hj
      have : l' • w = 0 := add_eq_left.mp hj.symm
      rcases smul_eq_zero.mp this with h' | h'
      · exact hl'0.ne' h'
      · exact hw0 h'
    · rw [h] at hj
      have e : P (k + 1) = P k + (1 : ℝ) • w := by rw [one_smul, hw]; abel
      rw [e] at hj
      have := smul_left_injective ℝ hw0 (add_left_cancel hj)
      linarith
  have hdist : dist y (P k + l • w) < ε := by
    rw [hy, dist_eq_norm]
    have e : P k + l' • w - (P k + l • w) = (l' - l) • w := by module
    rw [e, norm_smul, Real.norm_eq_abs]
    calc |l' - l| * ‖w‖ ≤ δ * ‖w‖ := mul_le_mul_of_nonneg_right hl'd (norm_nonneg _)
      _ < ε := hδε
  exact hA y hymem hynot (hball (Metric.mem_ball.mpr hdist))

end U4W_block

section U4X_block

/-! Splitting along a clean diagonal, part 4 (U4 helpers): the split context and the
frontier / interior / side facts of the union. -/

/-- All data of a split of `P` along the clean diagonal `P i — P (i+m)`. -/
structure u4h_SplitCtx [NeZero n] (P : LabelledTuple n) (i : ZMod n) (m : ℕ) where
  hP : Embedded P
  hm : 2 ≤ m
  hmn : m + 2 ≤ n
  hclean : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P i) (P (i + (m : ZMod n))))
  R1 : u4h_Region (u4h_subPoly P i m)
  R2 : u4h_Region (u4h_subPoly P (i + (m : ZMod n)) (n - m))
  X1 : ∃ s : ℕ, s < m ∧ ∃ x ∈ edgeSegment P (i + (s : ZMod n)),
    x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) ∧ x ∉ R2.U
  X2 : ∃ s : ℕ, s < n - m ∧ ∃ x ∈ edgeSegment P (i + (m : ZMod n) + (s : ZMod n)),
    x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) ∧ x ∉ R1.U

theorem u4h_ends_mem_polygonImage (P : LabelledTuple n) (i : ZMod n) (m : ℕ) :
    ∀ x ∈ ({P i, P (i + (m : ZMod n))} : Set Plane), x ∈ polygonImage P := by
  rintro x (rfl | rfl) <;> exact u4h_vertex_mem_polygonImage P _

/-- Offsets `≥ m` are second-chain offsets. -/
theorem u4h_offset_split (i : ZMod n) {m s : ℕ} (hs : s < n) (hsm : m ≤ s) :
    i + (s : ZMod n) = i + (m : ZMod n) + ((s - m : ℕ) : ZMod n) ∧ s - m < n - m := by
  constructor
  · rw [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' hsm]
  · omega

namespace u4h_SplitCtx

variable [NeZero n] {P : LabelledTuple n} {i : ZMod n} {m : ℕ} (C : u4h_SplitCtx P i m)

include C in
theorem hne : P i ≠ P (i + (m : ZMod n)) := by
  intro h
  have := u4h_vertex_injective C.hP h
  exact u4h_natCast_ne_zero (n := n) (k := m) (by have := C.hm; omega) (by have := C.hmn; omega)
    (by linear_combination -this)

theorem inter : C.R1.U ∩ C.R2.U = segment ℝ (P i) (P (i + (m : ZMod n))) :=
  u4h_split_inter C.hP i C.hm C.hmn C.hclean C.R1 C.R2 C.X1 C.X2

theorem out1 : ∀ s : ℕ, s < m → ∀ x ∈ edgeSegment P (i + (s : ZMod n)),
    x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) → x ∉ C.R2.U :=
  u4h_chain1_outside C.hP i C.hm C.hmn C.hclean C.R2 C.X1

theorem out2 : ∀ s : ℕ, s < n - m → ∀ x ∈ edgeSegment P (i + (m : ZMod n) + (s : ZMod n)),
    x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) → x ∉ C.R1.U :=
  u4h_chain2_outside C.hP i C.hm C.hmn C.hclean C.R1 C.X2

theorem faces1 : ∃ F1 ∈ C.R1.K.faces, ∃ k1 : Fin 3,
    F1.edgeSeg k1 = segment ℝ (P i) (P (i + (m : ZMod n))) := by
  obtain ⟨F1, hF1, k1, hk1⟩ := C.R1.edge_face (-1)
  rw [u4h_subPoly_edgeSegment_last, segment_symm] at hk1
  exact ⟨F1, hF1, k1, hk1⟩

theorem faces2 : ∃ F2 ∈ C.R2.K.faces, ∃ k2 : Fin 3,
    F2.edgeSeg k2 = segment ℝ (P i) (P (i + (m : ZMod n))) := by
  obtain ⟨F2, hF2, k2, hk2⟩ := C.R2.edge_face (-1)
  rw [u4h_subPoly_edgeSegment_last, u4h_split_second_start (by have := C.hmn; omega)] at hk2
  exact ⟨F2, hF2, k2, hk2⟩

/-- The open diagonal is interior to the union. -/
theorem openDiag_interior :
    openSegment ℝ (P i) (P (i + (m : ZMod n))) ⊆ interior (C.R1.U ∪ C.R2.U) := by
  obtain ⟨F1, hF1, k1, hk1⟩ := C.faces1
  obtain ⟨F2, hF2, k2, hk2⟩ := C.faces2
  exact u4h_split_openDiag_interior C.inter (C.R1.face_subset hF1) (C.R2.face_subset hF2) hk1 hk2

/-- Points of the first chain off the ends are not interior to the union. -/
theorem chain1_not_interior {s : ℕ} (hs : s < m) {y : Plane}
    (hy : y ∈ edgeSegment P (i + (s : ZMod n)))
    (hye : y ∉ ({P i, P (i + (m : ZMod n))} : Set Plane)) :
    y ∉ interior (C.R1.U ∪ C.R2.U) := by
  intro hint
  have hy1 : y ∈ frontier C.R1.U := by
    rw [C.R1.frontier_eq, u4h_mem_polygonImage_subPoly]; exact Or.inl ⟨s, hs, hy⟩
  have hy2 : y ∉ C.R2.U := C.out1 s hs y hy hye
  have h1 : C.R1.U ∪ C.R2.U ∈ nhds y := mem_interior_iff_mem_nhds.mp hint
  have h2 : C.R2.Uᶜ ∈ nhds y := C.R2.isClosed.isOpen_compl.mem_nhds hy2
  have h3 : C.R1.U ∈ nhds y := by
    apply Filter.mem_of_superset (Filter.inter_mem h1 h2)
    rintro z ⟨hz | hz, hz'⟩
    · exact hz
    · exact absurd hz hz'
  exact disjoint_interior_frontier.notMem_of_mem_left (mem_interior_iff_mem_nhds.mpr h3) hy1

theorem chain2_not_interior {s : ℕ} (hs : s < n - m) {y : Plane}
    (hy : y ∈ edgeSegment P (i + (m : ZMod n) + (s : ZMod n)))
    (hye : y ∉ ({P i, P (i + (m : ZMod n))} : Set Plane)) :
    y ∉ interior (C.R1.U ∪ C.R2.U) := by
  intro hint
  have hy2 : y ∈ frontier C.R2.U := by
    rw [C.R2.frontier_eq, u4h_mem_polygonImage_subPoly2 P i (by have := C.hmn; omega)]
    exact Or.inl ⟨s, hs, hy⟩
  have hy1 : y ∉ C.R1.U := C.out2 s hs y hy hye
  have h1 : C.R1.U ∪ C.R2.U ∈ nhds y := mem_interior_iff_mem_nhds.mp hint
  have h2 : C.R1.Uᶜ ∈ nhds y := C.R1.isClosed.isOpen_compl.mem_nhds hy1
  have h3 : C.R2.U ∈ nhds y := by
    apply Filter.mem_of_superset (Filter.inter_mem h1 h2)
    rintro z ⟨hz | hz, hz'⟩
    · exact absurd hz hz'
    · exact hz
  exact disjoint_interior_frontier.notMem_of_mem_left (mem_interior_iff_mem_nhds.mpr h3) hy2

/-- (X-a) The frontier of the union is the polygon image. -/
theorem frontier_eq : frontier (C.R1.U ∪ C.R2.U) = polygonImage P := by
  have hmn := C.hmn
  have hends := u4h_ends_mem_polygonImage P i m
  apply Set.Subset.antisymm
  · intro x hx
    have hxi : x ∉ interior (C.R1.U ∪ C.R2.U) :=
      disjoint_interior_frontier.notMem_of_mem_right hx
    rcases u4h_frontier_union_subset _ _ hx with h | h
    · rw [C.R1.frontier_eq, u4h_mem_polygonImage_subPoly] at h
      rcases h with ⟨s, -, hxs⟩ | hD
      · exact u4h_edgeSegment_subset_polygonImage P _ hxs
      · rw [segment_symm, ← insert_endpoints_openSegment] at hD
        rcases hD with h | h | h
        · exact h ▸ hends _ (Or.inl rfl)
        · exact h ▸ hends _ (Or.inr rfl)
        · exact absurd (C.openDiag_interior h) hxi
    · rw [C.R2.frontier_eq, u4h_mem_polygonImage_subPoly2 P i (by omega)] at h
      rcases h with ⟨s, -, hxs⟩ | hD
      · exact u4h_edgeSegment_subset_polygonImage P _ hxs
      · rw [← insert_endpoints_openSegment] at hD
        rcases hD with h | h | h
        · exact h ▸ hends _ (Or.inl rfl)
        · exact h ▸ hends _ (Or.inr rfl)
        · exact absurd (C.openDiag_interior h) hxi
  · intro z hz
    obtain ⟨s, hs, hzs⟩ := (u4h_mem_polygonImage_iff_offset P i z).mp hz
    have hSv : ∀ x ∈ ({P i, P (i + (m : ZMod n))} : Set Plane), ∃ j, P j = x := by
      rintro x (rfl | rfl)
      · exact ⟨i, rfl⟩
      · exact ⟨_, rfl⟩
    by_cases hsm : s < m
    · refine ⟨subset_closure (Or.inl ?_), ?_⟩
      · have : z ∈ polygonImage (u4h_subPoly P i m) := by
          rw [u4h_mem_polygonImage_subPoly]; exact Or.inl ⟨s, hsm, hzs⟩
        rw [← C.R1.frontier_eq] at this
        exact C.R1.isClosed.frontier_subset this
      · exact u4h_edge_not_interior C.hP _ hSv
          (fun y hy hye => C.chain1_not_interior hsm hy hye) hzs
    · obtain ⟨heq, hs'⟩ := u4h_offset_split i hs (not_lt.mp hsm)
      rw [heq] at hzs
      refine ⟨subset_closure (Or.inr ?_), ?_⟩
      · have : z ∈ polygonImage (u4h_subPoly P (i + (m : ZMod n)) (n - m)) := by
          rw [u4h_mem_polygonImage_subPoly2 P i (by omega)]; exact Or.inl ⟨_, hs', hzs⟩
        rw [← C.R2.frontier_eq] at this
        exact C.R2.isClosed.frontier_subset this
      · exact u4h_edge_not_interior C.hP _ hSv
          (fun y hy hye => C.chain2_not_interior hs' hy hye) hzs

/-- (X-e) The interior of the union is preconnected. -/
theorem int_conn : IsPreconnected (interior (C.R1.U ∪ C.R2.U)) := by
  have hmn := C.hmn
  obtain ⟨F1, hF1, k1, hk1⟩ := C.faces1
  obtain ⟨F2, hF2, k2, hk2⟩ := C.faces2
  set O := openSegment ℝ (P i) (P (i + (m : ZMod n))) with hO
  have hOsub : ∀ (F : Triangle) (k : Fin 3), F.edgeSeg k = segment ℝ (P i) (P (i + (m : ZMod n))) →
      O ⊆ closure (interior F.carrier) := by
    intro F k hk x hx
    have hconv : Convex ℝ F.carrier := convex_convexHull ℝ _
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior (u4h_tri_interior_nonempty F)]
    apply subset_closure
    apply u4h_tri_edgeSeg_subset F k
    rw [hk]; exact openSegment_subset_segment ℝ _ _ hx
  have hA : IsPreconnected (interior C.R1.U ∪ O) := by
    apply IsPreconnected.subset_closure C.R1.int_conn Set.subset_union_left
    rintro x (hx | hx)
    · exact subset_closure hx
    · exact closure_mono (interior_mono (C.R1.face_subset hF1)) (hOsub F1 k1 hk1 hx)
  have hB : IsPreconnected (interior C.R2.U ∪ O) := by
    apply IsPreconnected.subset_closure C.R2.int_conn Set.subset_union_left
    rintro x (hx | hx)
    · exact subset_closure hx
    · exact closure_mono (interior_mono (C.R2.face_subset hF2)) (hOsub F2 k2 hk2 hx)
  have hAB : IsPreconnected ((interior C.R1.U ∪ O) ∪ (interior C.R2.U ∪ O)) := by
    apply IsPreconnected.union' _ hA hB
    exact ⟨_, Or.inr (u4h_midpoint_mem_openSegment _ _), Or.inr (u4h_midpoint_mem_openSegment _ _)⟩
  have heq : interior (C.R1.U ∪ C.R2.U) = (interior C.R1.U ∪ O) ∪ (interior C.R2.U ∪ O) := by
    apply Set.Subset.antisymm
    · intro y hy
      have hyfr : y ∉ frontier (C.R1.U ∪ C.R2.U) :=
        disjoint_interior_frontier.notMem_of_mem_left hy
      rw [C.frontier_eq] at hyfr
      rcases interior_subset hy with hy1 | hy2
      · by_cases hyi : y ∈ interior C.R1.U
        · exact Or.inl (Or.inl hyi)
        · have hyf : y ∈ frontier C.R1.U := ⟨subset_closure hy1, hyi⟩
          rw [C.R1.frontier_eq, u4h_mem_polygonImage_subPoly] at hyf
          rcases hyf with ⟨s, -, hys⟩ | hD
          · exact absurd (u4h_edgeSegment_subset_polygonImage P _ hys) hyfr
          · rw [segment_symm, ← insert_endpoints_openSegment] at hD
            rcases hD with h | h | h
            · exact absurd (h ▸ u4h_ends_mem_polygonImage P i m _ (Or.inl rfl)) hyfr
            · exact absurd (h ▸ u4h_ends_mem_polygonImage P i m _ (Or.inr rfl)) hyfr
            · exact Or.inl (Or.inr h)
      · by_cases hyi : y ∈ interior C.R2.U
        · exact Or.inr (Or.inl hyi)
        · have hyf : y ∈ frontier C.R2.U := ⟨subset_closure hy2, hyi⟩
          rw [C.R2.frontier_eq, u4h_mem_polygonImage_subPoly2 P i (by omega)] at hyf
          rcases hyf with ⟨s, -, hys⟩ | hD
          · exact absurd (u4h_edgeSegment_subset_polygonImage P _ hys) hyfr
          · rw [← insert_endpoints_openSegment] at hD
            rcases hD with h | h | h
            · exact absurd (h ▸ u4h_ends_mem_polygonImage P i m _ (Or.inl rfl)) hyfr
            · exact absurd (h ▸ u4h_ends_mem_polygonImage P i m _ (Or.inr rfl)) hyfr
            · exact Or.inr (Or.inr h)
    · rintro y ((hy | hy) | (hy | hy))
      · exact interior_mono Set.subset_union_left hy
      · exact C.openDiag_interior hy
      · exact interior_mono Set.subset_union_right hy
      · exact C.openDiag_interior hy
  rw [heq]
  exact hAB

end u4h_SplitCtx

end U4X_block

section U4Y_block

/-! Splitting along a clean diagonal, part 5 (U4 helpers): the glued region. -/

namespace u4h_SplitCtx

variable [NeZero n] {P : LabelledTuple n} {i : ZMod n} {m : ℕ} (C : u4h_SplitCtx P i m)

/-- No face of `K2` contains a first-chain edge. -/
theorem no_face2_chain1 {s : ℕ} (hs : s < m) {T : Triangle} (hT : T ∈ C.R2.K.faces) :
    ¬ edgeSegment P (i + (s : ZMod n)) ⊆ T.carrier := by
  intro hsub
  obtain ⟨hmid, hnv⟩ := u4h_midpoint_not_vertex C.hP (i + (s : ZMod n))
  set mid : Plane := (1 / 2 : ℝ) • P (i + (s : ZMod n)) + (1 / 2 : ℝ) • P (i + (s : ZMod n) + 1)
    with hmiddef
  have h2 : mid ∈ C.R2.U := C.R2.face_subset hT (hsub hmid)
  have h1 : mid ∈ C.R1.U := by
    have : mid ∈ polygonImage (u4h_subPoly P i m) := by
      rw [u4h_mem_polygonImage_subPoly]; exact Or.inl ⟨s, hs, hmid⟩
    rw [← C.R1.frontier_eq] at this
    exact C.R1.isClosed.frontier_subset this
  have hD : mid ∈ segment ℝ (P i) (P (i + (m : ZMod n))) := by rw [← C.inter]; exact ⟨h1, h2⟩
  rw [segment_symm] at hD
  rcases u4h_edge_inter_diag_subPoly C.hclean _ hmid hD with h | h
  · exact hnv i h.symm
  · exact hnv _ h.symm

/-- No face of `K1` contains a second-chain edge. -/
theorem no_face1_chain2 {s : ℕ} (hs : s < n - m) {T : Triangle} (hT : T ∈ C.R1.K.faces) :
    ¬ edgeSegment P (i + (m : ZMod n) + (s : ZMod n)) ⊆ T.carrier := by
  intro hsub
  obtain ⟨hmid, hnv⟩ := u4h_midpoint_not_vertex C.hP (i + (m : ZMod n) + (s : ZMod n))
  set mid : Plane := (1 / 2 : ℝ) • P (i + (m : ZMod n) + (s : ZMod n)) +
    (1 / 2 : ℝ) • P (i + (m : ZMod n) + (s : ZMod n) + 1) with hmiddef
  have h1 : mid ∈ C.R1.U := C.R1.face_subset hT (hsub hmid)
  have h2 : mid ∈ C.R2.U := by
    have : mid ∈ polygonImage (u4h_subPoly P (i + (m : ZMod n)) (n - m)) := by
      rw [u4h_mem_polygonImage_subPoly2 P i (by have := C.hmn; omega)]
      exact Or.inl ⟨s, hs, hmid⟩
    rw [← C.R2.frontier_eq] at this
    exact C.R2.isClosed.frontier_subset this
  have hD : mid ∈ segment ℝ (P i) (P (i + (m : ZMod n))) := by rw [← C.inter]; exact ⟨h1, h2⟩
  rw [segment_symm] at hD
  rcases u4h_edge_inter_diag_subPoly C.hclean _ hmid hD with h | h
  · exact hnv i h.symm
  · exact hnv _ h.symm

end u4h_SplitCtx

/-- The sub-polygon edges as `P`-edges. -/
theorem u4h_subPoly1_edge (P : LabelledTuple n) (i : ZMod n) {m s : ℕ} (hs : s < m) :
    ∃ k : ZMod (m + 1), k ≠ -1 ∧
    edgeSegment (u4h_subPoly P i m) k = edgeSegment P (i + (s : ZMod n)) ∧
    u4h_subPoly P i m k = P (i + (s : ZMod n)) ∧
    u4h_subPoly P i m (k + 1) = P (i + (s : ZMod n) + 1) := by
  obtain ⟨k, hk1, hks⟩ := u4h_subPoly_index_exhaust m hs
  refine ⟨k, hk1, ?_, ?_, ?_⟩
  · rw [u4h_subPoly_edgeSegment P i m hk1, hks]
  · rw [u4h_subPoly_apply, hks]
  · rw [u4h_subPoly_apply, u4h_val_add_one hk1, hks, Nat.cast_add_one, add_assoc]

theorem u4h_subPoly2_edge (P : LabelledTuple n) (i : ZMod n) {m s : ℕ} (hs : s < n - m) :
    ∃ k : ZMod (n - m + 1), k ≠ -1 ∧
    edgeSegment (u4h_subPoly P (i + (m : ZMod n)) (n - m)) k =
      edgeSegment P (i + (m : ZMod n) + (s : ZMod n)) ∧
    u4h_subPoly P (i + (m : ZMod n)) (n - m) k = P (i + (m : ZMod n) + (s : ZMod n)) ∧
    u4h_subPoly P (i + (m : ZMod n)) (n - m) (k + 1) =
      P (i + (m : ZMod n) + (s : ZMod n) + 1) := by
  obtain ⟨k, hk1, hks⟩ := u4h_subPoly_index_exhaust (n - m) hs
  refine ⟨k, hk1, ?_, ?_, ?_⟩
  · rw [u4h_subPoly_edgeSegment P _ _ hk1, hks]
  · rw [u4h_subPoly_apply, hks]
  · rw [u4h_subPoly_apply, u4h_val_add_one hk1, hks, Nat.cast_add_one]
    congr 1; ring

namespace u4h_SplitCtx

variable [NeZero n] {P : LabelledTuple n} {i : ZMod n} {m : ℕ} (C : u4h_SplitCtx P i m)

/-- (X-b) every edge of `P` is a face-edge of the glued triangulation. -/
theorem edge_face (j : ZMod n) : ∃ T ∈ C.R1.K.faces ∪ C.R2.K.faces, ∃ k : Fin 3,
    T.edgeSeg k = edgeSegment P j := by
  obtain ⟨s, hs, rfl⟩ := u4h_index_offset i j
  by_cases hsm : s < m
  · obtain ⟨k', -, hk', -, -⟩ := u4h_subPoly1_edge P i hsm
    obtain ⟨T, hT, k, hk⟩ := C.R1.edge_face k'
    exact ⟨T, Or.inl hT, k, by rw [hk, hk']⟩
  · obtain ⟨heq, hs'⟩ := u4h_offset_split i hs (not_lt.mp hsm)
    obtain ⟨k', -, hk', -, -⟩ := u4h_subPoly2_edge P i hs'
    obtain ⟨T, hT, k, hk⟩ := C.R2.edge_face k'
    exact ⟨T, Or.inr hT, k, by rw [hk, hk', heq]⟩

/-- (X-c) uniqueness of the face at each edge of `P`. -/
theorem edge_unique (j : ZMod n) : ∀ T ∈ C.R1.K.faces ∪ C.R2.K.faces,
    ∀ T' ∈ C.R1.K.faces ∪ C.R2.K.faces, edgeSegment P j ⊆ T.carrier →
      edgeSegment P j ⊆ T'.carrier → T.carrier = T'.carrier := by
  intro T hT T' hT' hsub hsub'
  obtain ⟨s, hs, rfl⟩ := u4h_index_offset i j
  by_cases hsm : s < m
  · obtain ⟨k', -, hk', -, -⟩ := u4h_subPoly1_edge P i hsm
    rcases hT with hT | hT
    · rcases hT' with hT' | hT'
      · exact C.R1.edge_unique k' T hT T' hT' (hk' ▸ hsub) (hk' ▸ hsub')
      · exact absurd hsub' (C.no_face2_chain1 hsm hT')
    · exact absurd hsub (C.no_face2_chain1 hsm hT)
  · obtain ⟨heq, hs'⟩ := u4h_offset_split i hs (not_lt.mp hsm)
    rw [heq] at hsub hsub'
    obtain ⟨k', -, hk', -, -⟩ := u4h_subPoly2_edge P i hs'
    rcases hT with hT | hT
    · exact absurd hsub (C.no_face1_chain2 hs' hT)
    · rcases hT' with hT' | hT'
      · exact absurd hsub' (C.no_face1_chain2 hs' hT')
      · exact C.R2.edge_unique k' T hT T' hT' (hk' ▸ hsub) (hk' ▸ hsub')

/-- (X-g) the two regions have the same side. -/
theorem sigma_eq : C.R1.σ = C.R2.σ := by
  obtain ⟨F1, hF1, k1, hk1⟩ := C.faces1
  obtain ⟨F2, hF2, k2, hk2⟩ := C.faces2
  have hopp := u4h_split_opposite C.inter (C.R1.face_subset hF1) (C.R2.face_subset hF2) hk1 hk2
  -- side facts at the diagonal edge of each sub-polygon
  have hk1' : F1.edgeSeg k1 = edgeSegment (u4h_subPoly P i m) (-1) := by
    rw [u4h_subPoly_edgeSegment_last, segment_symm]; exact hk1
  have hk2' : F2.edgeSeg k2 = edgeSegment (u4h_subPoly P (i + (m : ZMod n)) (n - m)) (-1) := by
    rw [u4h_subPoly_edgeSegment_last, u4h_split_second_start (by have := C.hmn; omega)]; exact hk2
  have h1 := C.R1.side (-1) F1 hF1 k1 hk1'
  have h2 := C.R2.side (-1) F2 hF2 k2 hk2'
  rw [neg_add_cancel, u4h_subPoly_zero, u4h_subPoly_last] at h1 h2
  rw [u4h_split_second_start (by have := C.hmn; omega)] at h2
  have e1 : det (P i - P (i + (m : ZMod n))) (F1.v (k1 + 2) - P (i + (m : ZMod n))) =
      -det (P (i + (m : ZMod n)) - P i) (F1.v (k1 + 2) - P i) := by
    simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  rw [e1] at h1
  rcases C.R1.σ_pm with hσ1 | hσ1 <;> rcases C.R2.σ_pm with hσ2 | hσ2
  · rw [hσ1, hσ2]
  · exfalso; rw [hσ1] at h1; rw [hσ2] at h2; nlinarith
  · exfalso; rw [hσ1] at h1; rw [hσ2] at h2; nlinarith
  · rw [hσ1, hσ2]

/-- (X-f) the side condition for the glued triangulation. -/
theorem side (j : ZMod n) : ∀ T ∈ C.R1.K.faces ∪ C.R2.K.faces, ∀ k : Fin 3,
    T.edgeSeg k = edgeSegment P j → 0 < C.R1.σ * det (P (j + 1) - P j) (T.v (k + 2) - P j) := by
  intro T hT k hk
  obtain ⟨s, hs, rfl⟩ := u4h_index_offset i j
  by_cases hsm : s < m
  · obtain ⟨k', -, hk', hv0, hv1⟩ := u4h_subPoly1_edge P i hsm
    rcases hT with hT | hT
    · have := C.R1.side k' T hT k (by rw [hk, hk'])
      rwa [hv0, hv1] at this
    · exfalso
      exact C.no_face2_chain1 hsm hT (hk ▸ u4h_tri_edgeSeg_subset T k)
  · obtain ⟨heq, hs'⟩ := u4h_offset_split i hs (not_lt.mp hsm)
    rw [heq] at hk ⊢
    obtain ⟨k', -, hk', hv0, hv1⟩ := u4h_subPoly2_edge P i hs'
    rcases hT with hT | hT
    · exfalso
      exact C.no_face1_chain2 hs' hT (hk ▸ u4h_tri_edgeSeg_subset T k)
    · have := C.R2.side k' T hT k (by rw [hk, hk'])
      rw [hv0, hv1] at this
      rwa [C.sigma_eq]

include C in
/-- **The glued region of a split**, with its carrier. -/
theorem region' : ∃ G : u4h_Region P, G.U = C.R1.U ∪ C.R2.U := by
  obtain ⟨F1, hF1, k1, hk1⟩ := C.faces1
  obtain ⟨F2, hF2, k2, hk2⟩ := C.faces2
  have hedge : F2.edgeSeg k2 = F1.edgeSeg k1 := by rw [hk1, hk2]
  have hinter' : C.R1.U ∩ C.R2.U = F1.edgeSeg k1 := by rw [hk1]; exact C.inter
  refine ⟨{ U := C.R1.U ∪ C.R2.U
            K := u4h_glueTri C.R1.K C.R2.K hF1 k1 hF2 k2 hedge hinter'
            frontier_eq := C.frontier_eq
            edge_face := C.edge_face
            edge_unique := C.edge_unique
            hull := ?_
            int_conn := C.int_conn
            σ := C.R1.σ
            σ_pm := C.R1.σ_pm
            side := C.side
            count := ?_ }, rfl⟩
  · rintro x (hx | hx)
    · exact convexHull_mono (u4h_subPoly_range_subset P i m) (C.R1.hull hx)
    · exact convexHull_mono (u4h_subPoly_range_subset P _ _) (C.R2.hull hx)
  · show ((C.R1.K.faces ∪ C.R2.K.faces).image Triangle.carrier).ncard + 2 ≤ n
    rw [Set.image_union]
    have h := Set.ncard_union_le (C.R1.K.faces.image Triangle.carrier)
      (C.R2.K.faces.image Triangle.carrier)
    have h1 := C.R1.count
    have h2 := C.R2.count
    have hmn := C.hmn
    have hm := C.hm
    omega

include C in
theorem region : Nonempty (u4h_Region P) :=
  let ⟨G, _⟩ := C.region'; ⟨G⟩

end u4h_SplitCtx

end U4Y_block

section U4Za_block

/-! The region of an embedded triangle (U4 helpers). -/

/-- The side sign of a face at an edge `segment (P i) (P (i+1))`, by the order of its ends. -/
theorem u4h_tri_side_of_ends (T : Triangle) (k : Fin 3) {a b : Plane}
    (hk : T.edgeSeg k = segment ℝ a b) :
    (T.v k = a ∧ T.v (k + 1) = b → 0 < det (b - a) (T.v (k + 2) - a)) ∧
    (T.v k = b ∧ T.v (k + 1) = a → det (b - a) (T.v (k + 2) - a) < 0) := by
  have hpos := u4h_tri_pos T k
  constructor
  · rintro ⟨h0, h1⟩
    rw [← h0, ← h1]; exact hpos
  · rintro ⟨h0, h1⟩
    have e : det (b - a) (T.v (k + 2) - a) = -det (a - b) (T.v (k + 2) - b) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e, ← h0, ← h1]; linarith

theorem u4h_zmod3_add_one (i : ZMod 3) : (i = 0 → i + 1 = 1) ∧ (i = 1 → i + 1 = 2) ∧
    (i = 2 → i + 1 = 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> decide

/-- **The region of an embedded triangle** is its convex hull. -/
theorem u4h_triRegion' (P : LabelledTuple 3) (hP : Embedded P) :
    ∃ R : u4h_Region P, R.U = convexHull ℝ {P 0, P 1, P 2} := by
  have hD := u4h_tri3_det_ne_zero P hP
  have hinj := u4h_vertex_injective hP
  obtain ⟨hE0, hE1, hE2⟩ := u4h_edgeSegment_zmod3 P
  have hpoly := u4h_polygonImage_zmod3 P
  have h01 : (0 : ZMod 3) + 1 = 1 := by decide
  have h12 : (1 : ZMod 3) + 1 = 2 := by decide
  have h20 : (2 : ZMod 3) + 1 = 0 := by decide
  have hne01 : P 0 ≠ P 1 := fun h => absurd (hinj h) (by decide)
  have hne02 : P 0 ≠ P 2 := fun h => absurd (hinj h) (by decide)
  have hne12 : P 1 ≠ P 2 := fun h => absurd (hinj h) (by decide)
  -- the edge of `P` at index `i` as a segment
  have hEi : ∀ i : ZMod 3, edgeSegment P i = segment ℝ (P i) (P (i + 1)) :=
    fun i => u4h_edgeSegment_eq_segment P i
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · -- negative orientation: the positive triple is `(P 0, P 2, P 1)`
    have hD' : 0 < det (P 2 - P 0) (P 1 - P 0) := by rw [u4h_det_swap']; linarith
    refine ⟨u4h_triRegionOf P (u4h_mkTri (P 0) (P 2) (P 1) hD') ?_ ?_ ?_ (-1) (Or.inr rfl) ?_,
      by show (u4h_mkTri (P 0) (P 2) (P 1) hD').carrier = _
         rw [u4h_mkTri_carrier, u4h_hull3_comm]⟩
    · rw [u4h_mkTri_carrier, u4h_hull3_comm]
    · rw [u4h_mkTri_carrier, u4h_frontier_hull3 hD', hpoly, segment_symm ℝ (P 0) (P 2),
        segment_symm ℝ (P 2) (P 1), segment_symm ℝ (P 1) (P 0)]
      ext x; simp only [Set.mem_union]; tauto
    · intro i
      rcases u4h_zmod3_cases i with rfl | rfl | rfl
      · exact ⟨2, by rw [u4h_mkTri_edgeSeg2, hE0, segment_symm]⟩
      · exact ⟨1, by rw [u4h_mkTri_edgeSeg1, hE1, segment_symm]⟩
      · exact ⟨0, by rw [u4h_mkTri_edgeSeg0, hE2, segment_symm]⟩
    · intro i k hk
      rw [hEi] at hk
      obtain ⟨hdir, hrev⟩ := u4h_tri_side_of_ends _ k hk
      rcases u4h_face_edge_ends _ k hk with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · -- direct order is impossible for the reversed triangle
        exfalso
        rcases u4h_zmod3_cases i with rfl | rfl | rfl <;> fin_cases k <;>
          simp only [u4h_mkTri_v0, u4h_mkTri_v1, u4h_mkTri_v2, h01, h12, h20] at h0 h1 <;>
          first
          | exact hne01 h0 | exact hne02 h0 | exact hne12 h0
          | exact hne01 h0.symm | exact hne02 h0.symm | exact hne12 h0.symm
          | exact hne01 h1 | exact hne02 h1 | exact hne12 h1
          | exact hne01 h1.symm | exact hne02 h1.symm | exact hne12 h1.symm
      · have := hrev ⟨h0, h1⟩
        linarith
  · refine ⟨u4h_triRegionOf P (u4h_mkTri (P 0) (P 1) (P 2) hpos) ?_ ?_ ?_ 1 (Or.inl rfl) ?_,
      by show (u4h_mkTri (P 0) (P 1) (P 2) hpos).carrier = _
         rw [u4h_mkTri_carrier]⟩
    · rw [u4h_mkTri_carrier]
    · rw [u4h_mkTri_carrier, u4h_frontier_hull3 hpos, hpoly]
    · intro i
      rcases u4h_zmod3_cases i with rfl | rfl | rfl
      · exact ⟨0, by rw [u4h_mkTri_edgeSeg0, hE0]⟩
      · exact ⟨1, by rw [u4h_mkTri_edgeSeg1, hE1]⟩
      · exact ⟨2, by rw [u4h_mkTri_edgeSeg2, hE2]⟩
    · intro i k hk
      rw [hEi] at hk
      obtain ⟨hdir, hrev⟩ := u4h_tri_side_of_ends _ k hk
      rcases u4h_face_edge_ends _ k hk with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · have := hdir ⟨h0, h1⟩
        linarith
      · exfalso
        rcases u4h_zmod3_cases i with rfl | rfl | rfl <;> fin_cases k <;>
          simp only [u4h_mkTri_v0, u4h_mkTri_v1, u4h_mkTri_v2, h01, h12, h20] at h0 h1 <;>
          first
          | exact hne01 h0 | exact hne02 h0 | exact hne12 h0
          | exact hne01 h0.symm | exact hne02 h0.symm | exact hne12 h0.symm
          | exact hne01 h1 | exact hne02 h1 | exact hne12 h1
          | exact hne01 h1.symm | exact hne02 h1.symm | exact hne12 h1.symm

theorem u4h_triRegion (P : LabelledTuple 3) (hP : Embedded P) : Nonempty (u4h_Region P) :=
  let ⟨R, _⟩ := u4h_triRegion' P hP; ⟨R⟩

end U4Za_block

section U4Zb_block

/-! Strict lexicographic hull bound and the cone-direction conditions for (LL2) (U4 helpers). -/

/-- The open lexicographic half-plane above `p`. -/
def u4h_LexQs (p : Plane) : Set Plane := {x | p.1 < x.1 ∨ (p.1 = x.1 ∧ p.2 < x.2)}

theorem u4h_convex_LexQs (p : Plane) : Convex ℝ (u4h_LexQs p) := by
  intro x hx y hy s t hs ht hst
  simp only [u4h_LexQs, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hx hy ⊢
  have hp1 : s * p.1 + t * p.1 = p.1 := by rw [← add_mul, hst, one_mul]
  have hp2 : s * p.2 + t * p.2 = p.2 := by rw [← add_mul, hst, one_mul]
  have hx1 : s * p.1 ≤ s * x.1 :=
    mul_le_mul_of_nonneg_left (by rcases hx with h | ⟨h, -⟩ <;> linarith) hs
  have hy1 : t * p.1 ≤ t * y.1 :=
    mul_le_mul_of_nonneg_left (by rcases hy with h | ⟨h, -⟩ <;> linarith) ht
  by_cases hlt : p.1 < s * x.1 + t * y.1
  · exact Or.inl hlt
  · right
    have heq : p.1 = s * x.1 + t * y.1 := le_antisymm (by linarith) (not_lt.mp hlt)
    refine ⟨heq, ?_⟩
    have hx1' : s * p.1 = s * x.1 := by linarith
    have hy1' : t * p.1 = t * y.1 := by linarith
    -- at least one of `s, t` is positive; where positive the first coordinates agree
    have hsx : s * p.2 ≤ s * x.2 ∧ (0 < s → s * p.2 < s * x.2) := by
      rcases hs.lt_or_eq with hs' | hs'
      · have : p.1 = x.1 := mul_left_cancel₀ hs'.ne' hx1'
        rcases hx with h | ⟨-, h⟩
        · exact absurd this h.ne
        · exact ⟨(mul_lt_mul_of_pos_left h hs').le, fun _ => mul_lt_mul_of_pos_left h hs'⟩
      · rw [← hs']; simp
    have hty : t * p.2 ≤ t * y.2 ∧ (0 < t → t * p.2 < t * y.2) := by
      rcases ht.lt_or_eq with ht' | ht'
      · have : p.1 = y.1 := mul_left_cancel₀ ht'.ne' hy1'
        rcases hy with h | ⟨-, h⟩
        · exact absurd this h.ne
        · exact ⟨(mul_lt_mul_of_pos_left h ht').le, fun _ => mul_lt_mul_of_pos_left h ht'⟩
      · rw [← ht']; simp
    rcases hs.lt_or_eq with hs' | hs'
    · have := hsx.2 hs'; linarith [hty.1]
    · have ht' : 0 < t := by linarith
      have := hty.2 ht'; linarith [hsx.1]

/-- The lexmin vertex is not in the hull of the other vertices. -/
theorem u4h_lexmin_not_mem_hull {P : LabelledTuple n} {v : ZMod n}
    (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) {S : Set Plane}
    (hS : ∀ x ∈ S, ∃ k, k ≠ v ∧ P k = x) : P v ∉ convexHull ℝ S := by
  have hsub : convexHull ℝ S ⊆ u4h_LexQs (P v) := by
    apply convexHull_min _ (u4h_convex_LexQs _)
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hS x hx
    exact hv k hk
  intro h
  have := hsub h
  simp only [u4h_LexQs, Set.mem_ofPred_eq, lt_self_iff_false, false_or, and_false] at this

/-- Cone-direction condition for (LL2) applied to the second sub-polygon (edges `p, ω`,
direction `q`). -/
theorem u4h_dir_cond1 {p q ω : Plane} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hω : ω = α • p + β • q) (hpq : det p q ≠ 0) :
    (0 < det p ω ∧ (det p q < 0 ∨ 0 < det ω q)) ∨ (det p ω < 0 ∧ (det ω q < 0 ∨ 0 < det p q)) := by
  have e1 : det p ω = β * det p q := by
    rw [hω, u4h_det_add_right, u4h_det_smul_right, u4h_det_smul_right, u4h_det_self, mul_zero,
      zero_add]
  have e2 : det ω q = α * det p q := by
    rw [hω]
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rcases lt_or_gt_of_ne hpq with h | h
  · right; rw [e1, e2]; exact ⟨by nlinarith, Or.inl (by nlinarith)⟩
  · left; rw [e1, e2]; exact ⟨by nlinarith, Or.inr (by nlinarith)⟩

/-- Cone-direction condition for (LL2) applied to the first sub-polygon (edges `ω, q`,
direction `p`). -/
theorem u4h_dir_cond2 {p q ω : Plane} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hω : ω = α • p + β • q) (hpq : det p q ≠ 0) :
    (0 < det ω q ∧ (det ω p < 0 ∨ 0 < det q p)) ∨ (det ω q < 0 ∧ (det q p < 0 ∨ 0 < det ω p)) := by
  have e1 : det ω q = α * det p q := by
    rw [hω]
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have e2 : det ω p = -(β * det p q) := by
    rw [hω]
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have e3 : det q p = -det p q := by rw [u4h_det_swap']
  rcases lt_or_gt_of_ne hpq with h | h
  · right; rw [e1, e2, e3]; exact ⟨by nlinarith, Or.inr (by nlinarith)⟩
  · left; rw [e1, e2, e3]; exact ⟨by nlinarith, Or.inl (by nlinarith)⟩

end U4Zb_block

section U4Zc_block

/-! Ear extraction by counting faces (U4 helpers): a region triangulation of an `n`-gon with
`n ≥ 4` has a face carrying two consecutive polygon edges; that face is a convex, vertex-empty ear. -/

/-- Three distinct vertices of a triangle are not collinear. -/
theorem u4h_vertices_not_collinear (T : Triangle) {a b c : Plane} (ha : a ∈ Set.range T.v)
    (hb : b ∈ Set.range T.v) (hc : c ∈ Set.range T.v) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    det (b - a) (c - a) ≠ 0 := by
  intro hD
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  obtain ⟨r, hr⟩ : ∃ r : ℝ, c - a = r • (b - a) := ⟨_, scalar_of_det_zero hba hD⟩
  have hc' : c = a + r • (b - a) := by rw [← hr]; abel
  obtain ⟨ja, rfl⟩ := ha
  obtain ⟨jb, rfl⟩ := hb
  obtain ⟨jc, rfl⟩ := hc
  -- one of the three lies in the hull of the other two
  by_cases hr0 : r < 0
  · -- `a ∈ segment b c`
    have hmem : T.v ja ∈ convexHull ℝ {T.v jb, T.v jc} := by
      rw [convexHull_pair, u4h_mem_segment_iff_lin]
      refine ⟨1 / (1 - r), (one_div_pos.mpr (by linarith)).le, ?_, ?_⟩
      · rw [div_le_one (by linarith)]; linarith
      · rw [hc']
        have : T.v ja + r • (T.v jb - T.v ja) - T.v jb = (1 - r) • (T.v ja - T.v jb) := by module
        rw [this, smul_smul, one_div_mul_cancel (by linarith : (1 : ℝ) - r ≠ 0), one_smul]; abel
    have := (u4h_vertex_mem_hull_iff T (by rintro x (rfl | rfl) <;> exact ⟨_, rfl⟩) ja).mp hmem
    rcases this with h | h
    · exact hab h
    · exact hac h
  · by_cases hr1 : r ≤ 1
    · -- `c ∈ segment a b`
      have hmem : T.v jc ∈ convexHull ℝ {T.v ja, T.v jb} := by
        rw [convexHull_pair, u4h_mem_segment_iff_lin]
        exact ⟨r, not_lt.mp hr0, hr1, hc'⟩
      have := (u4h_vertex_mem_hull_iff T (by rintro x (rfl | rfl) <;> exact ⟨_, rfl⟩) jc).mp hmem
      rcases this with h | h
      · exact hac h.symm
      · exact hbc h.symm
    · -- `b ∈ segment a c`
      have hr1' : 1 < r := not_le.mp hr1
      have hmem : T.v jb ∈ convexHull ℝ {T.v ja, T.v jc} := by
        rw [convexHull_pair, u4h_mem_segment_iff_lin]
        refine ⟨1 / r, by positivity, ?_, ?_⟩
        · rw [div_le_one (by linarith)]; linarith
        · rw [hc', add_sub_cancel_left, smul_smul, one_div_mul_cancel (by linarith : r ≠ 0),
            one_smul]; abel
      have := (u4h_vertex_mem_hull_iff T (by rintro x (rfl | rfl) <;> exact ⟨_, rfl⟩) jb).mp hmem
      rcases this with h | h
      · exact hab h.symm
      · exact hbc h

theorem u4h_range_ncard_le (T : Triangle) : (Set.range T.v).ncard ≤ 3 := by
  rw [u4h_range_fin3]
  refine (Set.ncard_insert_le _ _).trans ?_
  refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
  rw [Set.ncard_singleton]

theorem u4h_range_finite (T : Triangle) : (Set.range T.v).Finite := Set.finite_range _

/-- Endpoints of a polygon edge that is a face-edge are vertices of the face. -/
theorem u4h_edge_ends_mem_range (T : Triangle) (k : Fin 3) {a b : Plane}
    (hk : T.edgeSeg k = segment ℝ a b) : a ∈ Set.range T.v ∧ b ∈ Set.range T.v := by
  rcases u4h_face_edge_ends T k hk with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact ⟨⟨k, h0⟩, ⟨k + 1, h1⟩⟩
  · exact ⟨⟨k + 1, h1⟩, ⟨k, h0⟩⟩

/-- Two faces with the same carrier have the same vertex set. -/
theorem u4h_range_eq_of_carrier_eq {X : Set Plane} (K : Triangulation X) {T T' : Triangle}
    (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) (h : T.carrier = T'.carrier) :
    Set.range T'.v ⊆ Set.range T.v := by
  rintro p ⟨j, rfl⟩
  have hp : T'.v j ∈ T.carrier ∩ T'.carrier := ⟨h ▸ subset_convexHull ℝ _ ⟨j, rfl⟩,
    subset_convexHull ℝ _ ⟨j, rfl⟩⟩
  rw [K.inter T hT T' hT'] at hp
  exact ((u4h_vertex_mem_hull_iff T' Set.inter_subset_right j).mp hp).1

/-- The ear at `j = i + 1` when the face at `E_i` also contains the vertex `P (i+2)`. -/
theorem u4h_ear_at [NeZero n] (hn : 4 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (R : u4h_Region P) (i : ZMod n) {T : Triangle} (hT : T ∈ R.K.faces) {k : Fin 3}
    (hk : T.edgeSeg k = edgeSegment P i) (hnext : P (i + 2) ∈ Set.range T.v) :
    det (P (i + 1) - P (i + 1 - 1)) (P (i + 1 + 1) - P (i + 1 - 1)) ≠ 0 ∧
      u4h_VertexEmpty P (i + 1) ∧
      0 < R.σ * det (P (i + 1) - P (i + 1 - 1)) (P (i + 1 + 1) - P (i + 1 - 1)) := by
  have hinj := u4h_vertex_injective hP
  have h1 : (1 : ZMod n) ≠ 0 := u4h_one_ne_zero hn
  have h2 : (2 : ZMod n) ≠ 0 := u4h_two_ne_zero hn
  have hi1 : i + 1 - 1 = i := by ring
  have hi2 : i + 1 + 1 = i + 2 := by ring
  rw [hi1, hi2]
  have hk' : T.edgeSeg k = segment ℝ (P i) (P (i + 1)) := by rw [hk, u4h_edgeSegment_eq_segment]
  obtain ⟨ha, hb⟩ := u4h_edge_ends_mem_range T k hk'
  have hab : P i ≠ P (i + 1) := fun h => h1 (by linear_combination -(hinj h))
  have hbc : P (i + 1) ≠ P (i + 2) := fun h => h1 (by linear_combination -(hinj h))
  have hac : P i ≠ P (i + 2) := fun h => h2 (by linear_combination -(hinj h))
  -- the vertex set of `T`
  have hrange : Set.range T.v = {P i, P (i + 1), P (i + 2)} := by
    symm
    apply Set.eq_of_subset_of_ncard_le
    · rintro x (rfl | rfl | rfl)
      · exact ha
      · exact hb
      · exact hnext
    · refine (u4h_range_ncard_le T).trans (le_of_eq ?_)
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair hbc]
      rintro (h | h)
      · exact hab h
      · exact hac h
    · exact u4h_range_finite T
  have hcar : T.carrier = earHull P (i + 1) := by
    rw [Triangle.carrier, hrange, earHull, hi1, hi2]
  refine ⟨u4h_vertices_not_collinear T ha hb hnext hab hbc hac, ?_, ?_⟩
  · -- vertex-empty
    intro m hm
    rw [← hcar] at hm
    obtain ⟨G, hG, kG, hkG⟩ := R.edge_face m
    have hkG' : G.edgeSeg kG = segment ℝ (P m) (P (m + 1)) := by
      rw [hkG, u4h_edgeSegment_eq_segment]
    have hmG : P m ∈ Set.range G.v := (u4h_edge_ends_mem_range G kG hkG').1
    have hmem : P m ∈ T.carrier ∩ G.carrier := ⟨hm, subset_convexHull ℝ _ hmG⟩
    rw [R.K.inter T hT G hG] at hmem
    obtain ⟨jm, hjm⟩ := hmG
    rw [← hjm] at hmem
    have := ((u4h_vertex_mem_hull_iff G Set.inter_subset_right jm).mp hmem).1
    rw [hjm, hrange] at this
    rcases this with h | h | h
    · left; rw [hi1]; exact hinj h
    · right; left; exact hinj h
    · right; right; rw [hi2]; exact hinj h
  · -- side
    have hside := R.side i T hT k hk
    have happ : T.v (k + 2) = P (i + 2) := by
      have hmem : T.v (k + 2) ∈ ({P i, P (i + 1), P (i + 2)} : Set Plane) := by
        rw [← hrange]; exact ⟨_, rfl⟩
      have hne0 : T.v (k + 2) ≠ T.v k := fun h => (u4h_tri_ne' T k) h.symm
      have hne1 : T.v (k + 2) ≠ T.v (k + 1) := fun h => by
        have := u4h_tri_ne T (k + 1)
        rw [show k + 1 + 1 = k + 2 by rw [add_assoc]; rfl] at this
        exact this h.symm
      rcases u4h_face_edge_ends T k hk' with ⟨h0, h1'⟩ | ⟨h0, h1'⟩ <;>
        rcases hmem with h | h | h
      · exact absurd (h.trans h0.symm) hne0
      · exact absurd (h.trans h1'.symm) hne1
      · exact h
      · exact absurd (h.trans h1'.symm) hne1
      · exact absurd (h.trans h0.symm) hne0
      · exact h
    rw [happ] at hside
    have e : det (P (i + 1) - P i) (P (i + 2) - P i) =
        det (P (i + 1) - P i) (P (i + 2) - P i) := rfl
    exact hside

/-- **Ear extraction.** A region of an embedded `n`-gon (`n ≥ 4`) has a convex vertex-empty ear. -/
theorem u4h_exists_ear_of_region [NeZero n] (hn : 4 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (R : u4h_Region P) :
    ∃ j : ZMod n, det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0 ∧ u4h_VertexEmpty P j ∧
      0 < R.σ * det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) := by
  classical
  have hinj := u4h_vertex_injective hP
  have h1 : (1 : ZMod n) ≠ 0 := u4h_one_ne_zero hn
  have h2 : (2 : ZMod n) ≠ 0 := u4h_two_ne_zero hn
  choose F hF k hk using R.edge_face
  -- the face-carrier map is not injective
  have hni : ¬ Function.Injective (fun i => (F i).carrier) := by
    intro hinjF
    have hsub : Set.range (fun i => (F i).carrier) ⊆ R.K.faces.image Triangle.carrier := by
      rintro x ⟨i, rfl⟩; exact ⟨F i, hF i, rfl⟩
    have hcard : (Set.range (fun i => (F i).carrier)).ncard = n := by
      rw [Set.ncard_range_of_injective hinjF, Nat.card_eq_fintype_card, ZMod.card]
    have hle := Set.ncard_le_ncard hsub (R.K.finite.image _)
    have := R.count
    omega
  simp only [Function.Injective, not_forall] at hni
  obtain ⟨i, i', heq, hne⟩ := hni
  have hrange : Set.range (F i').v = Set.range (F i).v :=
    Set.Subset.antisymm (u4h_range_eq_of_carrier_eq R.K (hF i) (hF i') heq)
      (u4h_range_eq_of_carrier_eq R.K (hF i') (hF i) heq.symm)
  have hki : (F i).edgeSeg (k i) = segment ℝ (P i) (P (i + 1)) := by
    rw [hk, u4h_edgeSegment_eq_segment]
  have hki' : (F i').edgeSeg (k i') = segment ℝ (P i') (P (i' + 1)) := by
    rw [hk, u4h_edgeSegment_eq_segment]
  obtain ⟨ha, hb⟩ := u4h_edge_ends_mem_range _ _ hki
  obtain ⟨ha', hb'⟩ := u4h_edge_ends_mem_range _ _ hki'
  rw [hrange] at ha' hb'
  -- `i` and `i'` are consecutive
  by_cases hc1 : i' = i + 1
  · subst hc1
    refine ⟨i + 1, u4h_ear_at hn hP R i (hF i) (hk i) ?_⟩
    rw [show i + 1 + 1 = i + 2 by ring] at hb'
    exact hb'
  by_cases hc2 : i = i' + 1
  · subst hc2
    refine ⟨i' + 1, u4h_ear_at hn hP R i' (hF i') (hk i') ?_⟩
    rw [← hrange, show i' + 1 + 1 = i' + 2 by ring] at hb
    exact hb
  · exfalso
    -- four distinct vertices in a 3-element set
    have hd : ∀ x y : ZMod n, x ≠ y → P x ≠ P y := fun x y hxy h => hxy (hinj h)
    have hne1 : i ≠ i + 1 := fun h => h1 (by linear_combination -h)
    have hne2 : i' ≠ i' + 1 := fun h => h1 (by linear_combination -h)
    have hne3 : i + 1 ≠ i' + 1 := fun h => hne (add_right_cancel h)
    have S4 : ({P i, P (i + 1), P i', P (i' + 1)} : Set Plane) ⊆ Set.range (F i).v := by
      rintro x (rfl | rfl | rfl | rfl)
      · exact ha
      · exact hb
      · exact ha'
      · exact hb'
    have hA : P i ∉ ({P (i + 1), P i', P (i' + 1)} : Set Plane) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hd _ _ hne1, hd _ _ hne, hd _ _ hc2⟩
    have hB : P (i + 1) ∉ ({P i', P (i' + 1)} : Set Plane) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hd _ _ (fun h' => hc1 h'.symm), hd _ _ hne3⟩
    have hcard : ({P i, P (i + 1), P i', P (i' + 1)} : Set Plane).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem hA, Set.ncard_insert_of_notMem hB, Set.ncard_pair (hd _ _ hne2)]
    have := Set.ncard_le_ncard S4 (u4h_range_finite _)
    have := u4h_range_ncard_le (F i)
    omega

end U4Zc_block

section U4Zd_block

/-! The main induction: every embedded polygon bounds a region (U4 helpers). -/

theorem u4h_subPoly_one (P : LabelledTuple n) (i : ZMod n) {m : ℕ} (hm : 1 ≤ m) :
    u4h_subPoly P i m 1 = P (i + 1) := by
  rw [u4h_subPoly_apply]
  have : (1 : ZMod (m + 1)).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
  rw [this, Nat.cast_one]

theorem u4h_subPoly_neg_two (P : LabelledTuple n) (i : ZMod n) {m : ℕ} (hm : 1 ≤ m) :
    u4h_subPoly P i m (-2) = P (i + ((m - 1 : ℕ) : ZMod n)) := by
  rw [u4h_subPoly_apply]
  have h2 : (-2 : ZMod (m + 1)) ≠ -1 := by
    intro h
    exact u4h_one_ne_zero' (n := m + 1) (by omega) (by linear_combination -h)
  have hv : (-2 : ZMod (m + 1)).val = m - 1 := by
    have := u4h_val_add_one h2
    rw [show (-2 : ZMod (m + 1)) + 1 = -1 by ring, u4h_val_neg_one'] at this
    omega
  rw [hv]

/-- General-size version of `u4h_edge_disjoint_openDiag`. -/
theorem u4h_edge_disjoint_openDiag' {P : LabelledTuple n} (hP : Embedded P) {j : ZMod n}
    (hac : P (j - 1) ≠ P (j + 1))
    (hstrict : earHull P j ∩ polygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j)
    {k : ZMod n} (hk1 : k ≠ j - 1) (hk2 : k ≠ j) {x : Plane} (hk : x ∈ edgeSegment P k) :
    x ∉ openSegment ℝ (P (j - 1)) (P (j + 1)) := by
  intro hxo
  have hxT : x ∈ earHull P j :=
    u4h_diag_subset_earHull P j (openSegment_subset_segment ℝ _ _ hxo)
  have hx' : x ∈ edgeSegment P (j - 1) ∪ edgeSegment P j := by
    rw [← hstrict]
    exact ⟨hxT, u4h_edgeSegment_subset_polygonImage P k hk⟩
  rcases u4h_edge_inter_ears hP hk1 hk2 ⟨hk, hx'⟩ with h | h
  · rw [h] at hxo
    exact hac (left_mem_openSegment_iff.mp hxo)
  · rw [h] at hxo
    exact hac (right_mem_openSegment_iff.mp hxo)

set_option maxHeartbeats 800000 in
/-- **Existence of the region** for every embedded polygon with at least three vertices. -/
theorem u4h_region_exists : ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ P : LabelledTuple N, Embedded P →
    Nonempty (u4h_Region P) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro _ hN P hP
  rcases Nat.lt_or_ge N 4 with h3 | h4
  · obtain rfl : N = 3 := by omega
    exact u4h_triRegion P hP
  obtain ⟨v, hv⟩ := u4h_exists_lexmin hP
  have hdet0 := u4h_lexmin_det_ne_zero (by omega) hP hv
  have hdet : det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) ≠ 0 := by
    have e : det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) =
        -det (P (v - 1) - P v) (P (v + 1) - P v) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e]; exact neg_ne_zero.mpr hdet0
  have hinj := u4h_vertex_injective hP
  have h1 : (1 : ZMod N) ≠ 0 := u4h_one_ne_zero h4
  have h2 : (2 : ZMod N) ≠ 0 := u4h_two_ne_zero h4
  have h3' : (3 : ZMod N) ≠ 0 := u4h_three_ne_zero h4
  by_cases hinv : ∃ k, k ∈ u4h_Inv P v
  · -- case (S): split along the clean diagonal to the farthest invader
    obtain ⟨w, ⟨hw1, hw2, hw3, -⟩, hclean, α, β, hα, hβ, hcone⟩ :=
      u4h_exists_clean_invader h4 hP v hdet hinv
    obtain ⟨m, hmN, hwm⟩ := u4h_index_offset v w
    have hm0 : m ≠ 0 := by rintro rfl; apply hw2; rw [hwm]; simp
    have hm1 : m ≠ 1 := by rintro rfl; apply hw3; rw [hwm]; simp
    have hmN1 : m + 1 ≠ N := by
      intro h
      apply hw1
      rw [hwm]
      have : ((m : ℕ) : ZMod N) + 1 = 0 := by
        rw [← Nat.cast_add_one, h, ZMod.natCast_self]
      linear_combination this
    have hm2 : 2 ≤ m := by omega
    have hmn : m + 2 ≤ N := by omega
    rw [hwm] at hclean hcone
    have hP1 : Embedded (u4h_subPoly P v m) := u4h_subPoly_embedded hP hm2 hmn hclean
    have hclean2 : ∀ k, Disjoint (edgeSegment P k)
        (openSegment ℝ (P (v + (m : ZMod N))) (P (v + (m : ZMod N) + ((N - m : ℕ) : ZMod N)))) := by
      intro k
      rw [u4h_split_second_start (by omega), openSegment_symm]
      exact hclean k
    have hP2 : Embedded (u4h_subPoly P (v + (m : ZMod N)) (N - m)) :=
      u4h_subPoly_embedded hP (by omega) (by omega) hclean2
    obtain ⟨R1⟩ := ih (m + 1) (by omega) (by omega) _ hP1
    obtain ⟨R2⟩ := ih (N - m + 1) (by omega) (by omega) _ hP2
    -- lexmin of the sub-polygons
    have hv1 : ∀ k : ZMod (m + 1), k ≠ 0 →
        u4h_Lex (u4h_subPoly P v m 0) (u4h_subPoly P v m k) := by
      intro k hk
      rw [u4h_subPoly_zero, u4h_subPoly_apply]
      apply hv
      intro h
      have := u4h_offset_injective (s := k.val) (s' := 0) (by have := ZMod.val_lt k; omega)
        (by omega) v (by rw [Nat.cast_zero, add_zero]; exact h)
      exact hk ((u4h_val_eq_zero_iff k).mp this)
    have hv2 : ∀ k : ZMod (N - m + 1), k ≠ -1 →
        u4h_Lex (u4h_subPoly P (v + (m : ZMod N)) (N - m) (-1))
          (u4h_subPoly P (v + (m : ZMod N)) (N - m) k) := by
      intro k hk
      rw [u4h_subPoly_last, u4h_split_second_start (by omega), u4h_subPoly_apply]
      apply hv
      intro h
      have hkv := u4h_val_lt_of_ne_neg_one hk
      have := u4h_offset_injective (s := m + k.val) (s' := 0) (by omega) (by omega) v
        (by rw [Nat.cast_zero, add_zero, Nat.cast_add, ← add_assoc]; exact h)
      omega
    have hq0 : P (v + 1) - P v ≠ 0 := hP.edge_ne_zero v
    have hp0 : P (v - 1) - P v ≠ 0 := by
      have := hP.edge_ne_zero (v - 1)
      rw [edge, sub_add_cancel] at this
      exact fun h => this (by rw [← neg_sub, h, neg_zero])
    -- X1: points of `E_v` near `P v` lie outside `R2.U` (LL2 for the second sub-polygon)
    have X1 : ∃ s : ℕ, s < m ∧ ∃ x ∈ edgeSegment P (v + (s : ZMod N)),
        x ∉ ({P v, P (v + (m : ZMod N))} : Set Plane) ∧ x ∉ R2.U := by
      have hw := u4h_dir_cond1 hα hβ hcone hdet0
      have hdir := u4h_lexmin_ray_outside (n := N - m + 1) (by omega) hP2 R2.isClosed
        R2.frontier_eq R2.hull hv2 (w := P (v + 1) - P v) (by
          rw [show (-1 : ZMod (N - m + 1)) - 1 = -2 by ring, neg_add_cancel,
            u4h_subPoly_neg_two _ _ (by omega), u4h_subPoly_last, u4h_subPoly_zero,
            u4h_split_second_start (by omega)]
          have e : v + (m : ZMod N) + ((N - m - 1 : ℕ) : ZMod N) = v - 1 := by
            rw [add_assoc, ← Nat.cast_add, show m + (N - m - 1) = N - 1 by omega,
              Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one]; ring
          rw [e]
          exact hw)
      obtain ⟨ρ, hρ, hray⟩ := hdir
      set t : ℝ := min (ρ / 2) (1 / 2) with ht
      have ht0 : 0 < t := lt_min (by positivity) (by norm_num)
      have htρ : t < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hx := hray t ht0 htρ
      rw [u4h_subPoly_last, u4h_split_second_start (by omega)] at hx
      refine ⟨0, by omega, P v + t • (P (v + 1) - P v), ?_, ?_, hx⟩
      · rw [Nat.cast_zero, add_zero, u4h_edgeSegment_eq_segment]
        exact u4h_lin_mem_segment _ _ ht0.le ht1.le
      · rintro (h | h)
        · have : t • (P (v + 1) - P v) = 0 := add_eq_left.mp h
          rcases smul_eq_zero.mp this with h' | h'
          · exact ht0.ne' h'
          · exact hq0 h'
        · have hmem : P (v + (m : ZMod N)) ∈ edgeSegment P v := by
            rw [← h, u4h_edgeSegment_eq_segment]
            exact u4h_lin_mem_segment _ _ ht0.le ht1.le
          rcases u4h_incident_of_vertex_mem hP hmem with h' | h'
          · exact hw2 (by rw [hwm, h'])
          · exact hw3 (by rw [hwm, h'])
    -- X2: points of `E_{v-1}` near `P v` lie outside `R1.U` (LL2 for the first sub-polygon)
    have X2 : ∃ s : ℕ, s < N - m ∧ ∃ x ∈ edgeSegment P (v + (m : ZMod N) + (s : ZMod N)),
        x ∉ ({P v, P (v + (m : ZMod N))} : Set Plane) ∧ x ∉ R1.U := by
      have hw := u4h_dir_cond2 hα hβ hcone hdet0
      have hdir := u4h_lexmin_ray_outside (n := m + 1) (by omega) hP1 R1.isClosed
        R1.frontier_eq R1.hull hv1 (w := P (v - 1) - P v) (by
          rw [zero_sub, zero_add, u4h_subPoly_last, u4h_subPoly_zero, u4h_subPoly_one _ _ (by omega)]
          exact hw)
      obtain ⟨ρ, hρ, hray⟩ := hdir
      set t : ℝ := min (ρ / 2) (1 / 2) with ht
      have ht0 : 0 < t := lt_min (by positivity) (by norm_num)
      have htρ : t < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hx := hray t ht0 htρ
      rw [u4h_subPoly_zero] at hx
      have e : v + (m : ZMod N) + ((N - m - 1 : ℕ) : ZMod N) = v - 1 := by
        rw [add_assoc, ← Nat.cast_add, show m + (N - m - 1) = N - 1 by omega,
          Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one]; ring
      refine ⟨N - m - 1, by omega, P v + t • (P (v - 1) - P v), ?_, ?_, hx⟩
      · rw [e, u4h_edgeSegment_prev, segment_symm]
        exact u4h_lin_mem_segment _ _ ht0.le ht1.le
      · rintro (h | h)
        · have : t • (P (v - 1) - P v) = 0 := add_eq_left.mp h
          rcases smul_eq_zero.mp this with h' | h'
          · exact ht0.ne' h'
          · exact hp0 h'
        · have hmem : P (v + (m : ZMod N)) ∈ edgeSegment P (v - 1) := by
            rw [← h, u4h_edgeSegment_prev, segment_symm]
            exact u4h_lin_mem_segment _ _ ht0.le ht1.le
          rcases u4h_incident_of_vertex_mem hP hmem with h' | h'
          · exact hw1 (by rw [hwm, h'])
          · exact hw2 (by rw [hwm, h', sub_add_cancel])
    exact (u4h_SplitCtx.mk hP hm2 hmn hclean R1 R2 X1 X2).region
  · -- case (E): the lexmin vertex is a strict ear; split off its triangle
    have hV : u4h_VertexEmpty P v := by
      intro k hk
      by_contra hne
      simp only [not_or] at hne
      exact hinv ⟨k, hne.1, hne.2.1, hne.2.2, hk⟩
    have hstrict := u4h_strict_ear_of_vertex_empty hP h4 hdet hV
    have hac : P (v - 1) ≠ P (v + 1) := fun h => h2 (by linear_combination -(hinj h))
    have hi2 : v - 1 + ((2 : ℕ) : ZMod N) = v + 1 := by push_cast; ring
    have hclean : ∀ k, Disjoint (edgeSegment P k)
        (openSegment ℝ (P (v - 1)) (P (v - 1 + ((2 : ℕ) : ZMod N)))) := by
      intro k
      rw [hi2, Set.disjoint_left]
      intro x hxk hxo
      by_cases hk1 : k = v - 1
      · rw [hk1, u4h_edgeSegment_prev] at hxk
        have hx' : x ∈ segment ℝ (P (v - 1)) (P v) ∩ segment ℝ (P (v - 1)) (P (v + 1)) :=
          ⟨hxk, openSegment_subset_segment ℝ _ _ hxo⟩
        rw [u4h_segment_inter_same_start hdet] at hx'
        have hx'' : x = P (v - 1) := hx'
        rw [hx''] at hxo
        exact hac (left_mem_openSegment_iff.mp hxo)
      by_cases hk2 : k = v
      · rw [hk2, u4h_edgeSegment_eq_segment, segment_symm] at hxk
        have hD' : det (P v - P (v + 1)) (P (v - 1) - P (v + 1)) ≠ 0 := by
          have e : det (P v - P (v + 1)) (P (v - 1) - P (v + 1)) =
              -det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) := by
            simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
          rw [e]; exact neg_ne_zero.mpr hdet
        have hx' : x ∈ segment ℝ (P (v + 1)) (P v) ∩ segment ℝ (P (v + 1)) (P (v - 1)) :=
          ⟨hxk, by rw [segment_symm]; exact openSegment_subset_segment ℝ _ _ hxo⟩
        rw [u4h_segment_inter_same_start hD'] at hx'
        have hx'' : x = P (v + 1) := hx'
        rw [hx''] at hxo
        exact hac (right_mem_openSegment_iff.mp hxo)
      exact u4h_edge_disjoint_openDiag' hP hac hstrict hk1 hk2 hxk hxo
    have hP1 : Embedded (u4h_subPoly P (v - 1) 2) :=
      u4h_subPoly_embedded hP (le_refl 2) (by omega) hclean
    have hclean2 : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P (v - 1 + ((2 : ℕ) : ZMod N)))
        (P (v - 1 + ((2 : ℕ) : ZMod N) + ((N - 2 : ℕ) : ZMod N)))) := by
      intro k
      rw [u4h_split_second_start (by omega), openSegment_symm]
      exact hclean k
    have hP2 : Embedded (u4h_subPoly P (v - 1 + ((2 : ℕ) : ZMod N)) (N - 2)) :=
      u4h_subPoly_embedded hP (by omega) (by omega) hclean2
    obtain ⟨R1, hR1U⟩ := u4h_triRegion' (u4h_subPoly P (v - 1) 2) hP1
    obtain ⟨R2⟩ := ih (N - 2 + 1) (by omega) (by omega) _ hP2
    -- the triangle's vertices
    have hP10 : u4h_subPoly P (v - 1) 2 0 = P (v - 1) := u4h_subPoly_zero P (v - 1) 2
    have hP11 : u4h_subPoly P (v - 1) 2 1 = P v := by
      rw [u4h_subPoly_one P (v - 1) (by norm_num), sub_add_cancel]
    have hP12 : u4h_subPoly P (v - 1) 2 2 = P (v + 1) := by
      rw [u4h_subPoly_apply]
      have : (2 : ZMod (2 + 1)).val = 2 := by
        rw [show (2 : ZMod (2 + 1)) = ((2 : ℕ) : ZMod (2 + 1)) from Nat.cast_ofNat.symm,
          ZMod.val_natCast_of_lt (by norm_num)]
      rw [this, ← hi2]
    have hR1 : R1.U = earHull P v := by rw [hR1U, hP10, hP11, hP12]; rfl
    -- X1: the apex `P v` is not in the region of the rest (lexmin not in the hull)
    have X1 : ∃ s : ℕ, s < 2 ∧ ∃ x ∈ edgeSegment P (v - 1 + (s : ZMod N)),
        x ∉ ({P (v - 1), P (v - 1 + ((2 : ℕ) : ZMod N))} : Set Plane) ∧ x ∉ R2.U := by
      refine ⟨0, by norm_num, P v, ?_, ?_, ?_⟩
      · rw [Nat.cast_zero, add_zero]
        have := u4h_end_mem_edgeSegment P (v - 1)
        rwa [sub_add_cancel] at this
      · rw [hi2]
        rintro (h | h)
        · exact h1 (by linear_combination (hinj h))
        · exact h1 (by linear_combination -(hinj (Set.mem_singleton_iff.mp h)))
      · intro hmem
        have hhull := R2.hull hmem
        refine u4h_lexmin_not_mem_hull hv ?_ hhull
        rintro x ⟨k, rfl⟩
        rw [u4h_subPoly_apply, hi2]
        refine ⟨v + 1 + (k.val : ZMod N), ?_, rfl⟩
        intro h
        have hkv := ZMod.val_lt k
        have : ((1 + k.val : ℕ) : ZMod N) = 0 := by
          push_cast; linear_combination h
        exact u4h_natCast_ne_zero (n := N) (k := 1 + k.val) (by omega) (by omega) this
    -- X2: the vertex `P (v+2)` of the rest is not in the triangle (vertex-empty)
    have X2 : ∃ s : ℕ, s < N - 2 ∧ ∃ x ∈ edgeSegment P (v - 1 + ((2 : ℕ) : ZMod N) + (s : ZMod N)),
        x ∉ ({P (v - 1), P (v - 1 + ((2 : ℕ) : ZMod N))} : Set Plane) ∧ x ∉ R1.U := by
      refine ⟨0, by omega, P (v + 2), ?_, ?_, ?_⟩
      · rw [Nat.cast_zero, add_zero, hi2]
        have := u4h_end_mem_edgeSegment P (v + 1)
        rwa [show v + 1 + 1 = v + 2 by ring] at this
      · rw [hi2]
        rintro (h | h)
        · exact h3' (by linear_combination (hinj h))
        · exact h1 (by linear_combination (hinj (Set.mem_singleton_iff.mp h)))
      · rw [hR1]
        intro hmem
        rcases hV (v + 2) hmem with h | h | h
        · exact h3' (by linear_combination h)
        · exact h2 (by linear_combination h)
        · exact h1 (by linear_combination h)
    exact (u4h_SplitCtx.mk hP (le_refl 2) (by omega) hclean R1 R2 X1 X2).region

end U4Zd_block

section U4Ze_block

/-! Uniqueness of the region and the canonical region (U4 helpers). -/

/-- All regions of an embedded polygon have the same side. -/
theorem u4h_sigma_unique [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (R R' : u4h_Region P) : R.σ = R'.σ := by
  obtain ⟨v, hv⟩ := u4h_exists_lexmin hP
  have h1 := u4h_region_lexmin_turn hn hP R hv
  have h2 := u4h_region_lexmin_turn hn hP R' hv
  rcases R.σ_pm with h | h <;> rcases R'.σ_pm with h' | h'
  · rw [h, h']
  · exfalso; rw [h] at h1; rw [h'] at h2; linarith
  · exfalso; rw [h] at h1; rw [h'] at h2; linarith
  · rw [h, h']

/-- Two regions of the same embedded polygon have a common interior point. -/
theorem u4h_regions_interior_inter [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Embedded P) (R R' : u4h_Region P) : (interior R.U ∩ interior R'.U).Nonempty := by
  obtain ⟨v, hv⟩ := u4h_exists_lexmin hP
  have hσ := u4h_sigma_unique hn hP R R'
  obtain ⟨F, hF, k, hk⟩ := R.edge_face (v - 1)
  obtain ⟨F', hF', k', hk'⟩ := R'.edge_face (v - 1)
  have hs := R.side (v - 1) F hF k hk
  have hs' := R'.side (v - 1) F' hF' k' hk'
  rw [sub_add_cancel] at hs hs'
  rw [u4h_edgeSegment_prev] at hk hk'
  set e1 := P (v - 1) with he1
  set e2 := P v with he2
  set x : Plane := (1 / 2 : ℝ) • e1 + (1 / 2 : ℝ) • e2 with hx
  have hxo : x ∈ openSegment ℝ e1 e2 := u4h_midpoint_mem_openSegment _ _
  obtain ⟨ε, hε, h⟩ := u4h_face_halfdisc F k hk hxo
  obtain ⟨ε', hε', h'⟩ := u4h_face_halfdisc F' k' hk' hxo
  -- the open half-disc on the `σ` side
  set B : Set Plane := Metric.ball x (min ε ε') ∩ {y | 0 < R.σ * det (e2 - e1) (y - e1)} with hB
  have hBopen : IsOpen B :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const (by
      have := u4h_continuous_det_sub (e2 - e1) e1
      exact continuous_const.mul this))
  have hBF : B ⊆ F.carrier := by
    rintro y ⟨hy1, hy2⟩
    rw [h y (lt_of_lt_of_le (Metric.mem_ball.mp hy1) (min_le_left _ _))]
    have hy2' : 0 < R.σ * det (e2 - e1) (y - e1) := hy2
    rcases R.σ_pm with hσ1 | hσ1 <;> rw [hσ1] at hs hy2' <;> nlinarith
  have hBF' : B ⊆ F'.carrier := by
    rintro y ⟨hy1, hy2⟩
    rw [h' y (lt_of_lt_of_le (Metric.mem_ball.mp hy1) (min_le_right _ _))]
    have hy2' : 0 < R.σ * det (e2 - e1) (y - e1) := hy2
    rw [hσ] at hy2'
    rcases R'.σ_pm with hσ1 | hσ1 <;> rw [hσ1] at hs' hy2' <;> nlinarith
  -- `B` is nonempty
  have hsne : det (e2 - e1) (F.v (k + 2) - e1) ≠ 0 := u4h_apex_det_ne_zero F k hk
  set w := F.v (k + 2) - e1 with hw
  set η : ℝ := min ε ε' / (2 * (‖w‖ + 1)) with hη
  have hηpos : 0 < η := by positivity
  have hy0ball : x + η • w ∈ Metric.ball x (min ε ε') := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hηpos, hη, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w, lt_min hε hε']
  have hy0 : x + η • w ∈ B := by
    refine ⟨hy0ball, ?_⟩
    show 0 < R.σ * det (e2 - e1) (x + η • w - e1)
    have e : det (e2 - e1) (x + η • w - e1) = η * det (e2 - e1) w := by
      rw [hx]
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]
    have : 0 < R.σ * det (e2 - e1) w := by
      have e2' : det (e2 - e1) w = det (P v - P (v - 1)) (F.v (k + 2) - P (v - 1)) := rfl
      rw [e2']; exact hs
    nlinarith
  exact ⟨_, interior_maximal (hBF.trans (R.face_subset hF)) hBopen hy0,
    interior_maximal (hBF'.trans (R'.face_subset hF')) hBopen hy0⟩

/-- **Uniqueness of the region.** -/
theorem u4h_region_unique [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (R R' : u4h_Region P) : R.U = R'.U := by
  have key : ∀ (R R' : u4h_Region P), R.U ⊆ R'.U := by
    intro R R'
    obtain ⟨y, hy, hy'⟩ := u4h_regions_interior_inter hn hP R R'
    have hsub : interior R.U ⊆ interior R'.U ∪ R'.Uᶜ := by
      intro z hz
      by_cases hz' : z ∈ R'.U
      · left
        by_contra hzi
        have hzf : z ∈ frontier R'.U := ⟨subset_closure hz', hzi⟩
        rw [R'.frontier_eq, ← R.frontier_eq] at hzf
        exact disjoint_interior_frontier.notMem_of_mem_left hz hzf
      · right; exact hz'
    rcases IsPreconnected.subset_or_subset isOpen_interior R'.isClosed.isOpen_compl
        (Set.disjoint_left.mpr fun z hz hz' => hz' (interior_subset hz)) hsub R.int_conn
        with h | h
    · rw [← u4h_triangulation_closure_interior R.K]
      exact (closure_mono h).trans (closure_minimal interior_subset R'.isClosed)
    · exact absurd (interior_subset hy') (h hy)
  exact Set.Subset.antisymm (key R R') (key R' R)

open Classical in
/-- The canonical region bounded by `P` (junk `∅` when no region exists). -/
noncomputable def u4h_regionOf [NeZero n] (P : LabelledTuple n) : Set Plane :=
  if h : Nonempty (u4h_Region P) then (Classical.choice h).U else ∅

theorem u4h_region_U_eq_regionOf [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (R : u4h_Region P) : R.U = u4h_regionOf P := by
  unfold u4h_regionOf
  rw [dif_pos ⟨R⟩]
  exact u4h_region_unique hn hP R _

end U4Ze_block

section U4Zf_block

/-! Downstream interface (U4 helpers): convex ears, the canonical region and its ear relation. -/

/-- `deleteVertex` is the sub-polygon starting after the deleted vertex. -/
theorem u4h_deleteVertex_eq_subPoly {n' : ℕ} (P : LabelledTuple (n' + 2)) (j : ZMod (n' + 2)) :
    deleteVertex P j = u4h_subPoly P (j + 1) n' := by
  funext k
  show P (((k.val : ℕ) : ZMod (n' + 2)) + (j + 1)) = P (j + 1 + (k.val : ZMod (n' + 2)))
  rw [add_comm]

/-- 2D Cramer decomposition of a vector in a nondegenerate basis. -/
theorem u4h_cone_decomp {a b c : Plane} (hΔ : det (b - a) (c - a) ≠ 0) (w : Plane) :
    w = (det w (c - a) / det (b - a) (c - a)) • (b - a) +
      (det (b - a) w / det (b - a) (c - a)) • (c - a) := by
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_sub]
    field_simp
    simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_sub]
    field_simp
    simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

/-- A point `a + t • w` with `w` strictly inside the cone at `a` of the triangle lies in the
triangle for small `t`. -/
theorem u4h_cone_point_mem {a b c w : Plane} {l m : ℝ} (hl : 0 < l) (hm : 0 < m)
    (hw : w = l • (b - a) + m • (c - a)) :
    a + (1 / (l + m + 1)) • w ∈ convexHull ℝ {a, b, c} := by
  rw [u4h_mem_hull3_iff]
  have hpos : 0 < l + m + 1 := by positivity
  refine ⟨1 - l / (l + m + 1) - m / (l + m + 1), l / (l + m + 1), m / (l + m + 1), ?_,
    by positivity, by positivity, by ring, ?_⟩
  · have h1 : l / (l + m + 1) + m / (l + m + 1) ≤ 1 := by
      rw [← add_div, div_le_one hpos]; linarith
    linarith
  · rw [hw]; module

/-- Vertices of the polygon other than `j-1, j, j+1` are the vertices of `deleteVertex P j`
other than the diagonal ends; the lexmin transfers. -/
theorem u4h_lexmin_deleteVertex {n' : ℕ} {P : LabelledTuple (n' + 2)} (hP : Embedded P)
    {j v : ZMod (n' + 2)} (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) {v' : ZMod (n' + 1)}
    (hv' : deletionIndex j v' = v) :
    ∀ k', k' ≠ v' → u4h_Lex (deleteVertex P j v') (deleteVertex P j k') := by
  intro k' hk'
  rw [deleteVertex_apply, deleteVertex_apply, hv']
  apply hv
  intro h
  rw [← hv'] at h
  exact hk' (deletionIndex_injective j h)

/-- **σ-transfer at an ear.** If the lexmin vertex `v` of `P` is not the apex `j`, the regions of
`P` and of `deleteVertex P j` have the same side (the ear being strict and convex). -/
theorem u4h_sigma_ear {n' : ℕ} (hn : 2 ≤ n') {P : LabelledTuple (n' + 2)} (hP : Embedded P)
    {j : ZMod (n' + 2)} (hdet : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0)
    (hstrict : earHull P j ∩ polygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j)
    (R : u4h_Region P) (R' : u4h_Region (deleteVertex P j))
    (hconv : 0 < R.σ * det (P j - P (j - 1)) (P (j + 1) - P (j - 1)))
    {v : ZMod (n' + 2)} (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) (hvj : v ≠ j) : R.σ = R'.σ := by
  have h4 : 4 ≤ n' + 2 := by omega
  have hinj := u4h_vertex_injective hP
  have h1 : (1 : ZMod (n' + 2)) ≠ 0 := u4h_one_ne_zero h4
  have h2 : (2 : ZMod (n' + 2)) ≠ 0 := u4h_two_ne_zero h4
  have h3 : (3 : ZMod (n' + 2)) ≠ 0 := u4h_three_ne_zero h4
  have h1' : (1 : ZMod (n' + 1)) ≠ 0 := u4h_one_ne_zero' (n := n' + 1) (by omega)
  have hσR := u4h_region_lexmin_turn (by omega) hP R hv
  have hP' : Embedded (deleteVertex P j) := by
    refine u4h_embedded_deleteVertex (n := n' + 1) (by omega) hP ?_ hstrict
    intro h; exact h2 (by linear_combination -(hinj h))
  obtain ⟨v', hv'⟩ := deletionIndex_exhaust j hvj
  have hlex' := u4h_lexmin_deleteVertex hP hv hv'
  have hσR' := u4h_region_lexmin_turn (n := n' + 1) (by omega) hP' R' hlex'
  rw [deleteVertex_apply, deleteVertex_apply, deleteVertex_apply, hv'] at hσR'
  -- the sign facts, and the two cases on `v` (general / adjacent to `j`)
  have hsq : ∀ x y : ℝ, (x = 1 ∨ x = -1) → (y = 1 ∨ y = -1) → x ≠ y → y = -x := by
    rintro x y (rfl | rfl) (rfl | rfl) hxy <;> first | rfl | exact absurd rfl hxy | norm_num
  by_contra hne
  have hσ' : R'.σ = -R.σ := hsq _ _ R.σ_pm R'.σ_pm hne
  rw [hσ'] at hσR'
  by_cases hv1 : v' = -1
  · -- `v = j - 1`
    subst hv1
    rw [deletionIndex_last] at hv'
    rw [show (-1 : ZMod (n' + 1)) - 1 = -2 by ring, neg_add_cancel, deletionIndex_zero,
      u4h_deletionIndex_neg_two (by omega)] at hσR'
    rw [← hv'] at hσR hσR'
    -- `w := P (j-2) - P (j-1)` lies strictly inside the cone at `P (j-1)`
    set a := P (j - 1) with ha
    set b := P j with hb
    set c := P (j + 1) with hc
    set w := P (j - 2) - a with hw
    have hΔ : det (b - a) (c - a) ≠ 0 := hdet
    have e1 : det (a - P (j - 1 - 1)) (P (j - 1 + 1) - a) = det (b - a) w := by
      rw [show j - 1 + 1 = j by ring, show j - 1 - 1 = j - 2 by ring]
      simp only [hb, hw, det, Prod.fst_sub, Prod.snd_sub]; ring
    have e2 : det (a - P (j - 2)) (c - a) = det (-w) (c - a) := by
      simp only [hw, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg]; ring
    rw [e1] at hσR
    rw [e2] at hσR'
    have hl : 0 < det w (c - a) / det (b - a) (c - a) := by
      rw [u4h_det_neg_left] at hσR'
      rcases R.σ_pm with hs | hs <;> rw [hs] at hσR' hconv <;>
        first | exact div_pos (by linarith) (by linarith)
              | exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hm : 0 < det (b - a) w / det (b - a) (c - a) := by
      rcases R.σ_pm with hs | hs <;> rw [hs] at hσR hconv <;>
        first | exact div_pos (by linarith) (by linarith)
              | exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hmem := u4h_cone_point_mem hl hm (u4h_cone_decomp hΔ w)
    set t := 1 / (det w (c - a) / det (b - a) (c - a) + det (b - a) w / det (b - a) (c - a) + 1)
      with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one (by positivity)]; linarith
    -- the point lies on `E_{j-2}` and in the ear triangle: contradiction with strictness
    have hE : a + t • w ∈ edgeSegment P (j - 2) := by
      rw [u4h_edgeSegment_eq_segment, show j - 2 + 1 = j - 1 by ring, segment_symm,
        u4h_mem_segment_iff_lin]
      exact ⟨t, ht0.le, ht1, rfl⟩
    have hT : a + t • w ∈ earHull P j := hmem
    have hk1 : j - 2 ≠ j - 1 := fun h => h1 (by linear_combination -h)
    have hk2 : j - 2 ≠ j := fun h => h2 (by linear_combination -h)
    have hx' : a + t • w ∈ edgeSegment P (j - 1) ∪ edgeSegment P j := by
      rw [← hstrict]; exact ⟨hT, u4h_edgeSegment_subset_polygonImage P _ hE⟩
    rcases u4h_edge_inter_ears hP hk1 hk2 ⟨hE, hx'⟩ with h | h
    · have : t • w = 0 := add_eq_left.mp h
      rcases smul_eq_zero.mp this with h' | h'
      · exact ht0.ne' h'
      · have := hinj (sub_eq_zero.mp h')
        exact h1 (by linear_combination -this)
    · have : P (j + 1) ∈ edgeSegment P (j - 2) := h ▸ hE
      rcases u4h_incident_of_vertex_mem hP this with h' | h'
      · exact h3 (by linear_combination h')
      · exact h2 (by linear_combination h')
  by_cases hv0 : v' = 0
  · -- `v = j + 1`
    subst hv0
    rw [deletionIndex_zero] at hv'
    have hd1 : deletionIndex j 1 = j + 1 + 1 := by
      have := deletionIndex_next j (i := 0) (by intro h; exact h1' (by linear_combination h))
      rwa [zero_add, deletionIndex_zero] at this
    rw [zero_sub, zero_add, deletionIndex_last, hd1] at hσR'
    rw [← hv'] at hσR hσR'
    set a := P (j - 1) with ha
    set b := P j with hb
    set c := P (j + 1) with hc
    set w := P (j + 1 + 1) - c with hw
    have hΔ : det (b - a) (c - a) ≠ 0 := hdet
    have hΔ' : det (a - c) (b - c) = det (b - a) (c - a) := u4h_det_rot2 a b c
    have e1 : det (c - P (j + 1 - 1)) (P (j + 1 + 1) - c) = det (c - b) w := by
      rw [show j + 1 - 1 = j by ring]
    have e2 : det (c - a) (P (j + 1 + 1) - c) = det (c - a) w := rfl
    rw [e1] at hσR
    rw [e2] at hσR'
    -- decompose `w` in the cone at `c` spanned by `a - c`, `b - c`
    have hl : 0 < det w (b - c) / det (a - c) (b - c) := by
      have : det w (b - c) = det (c - b) w := by simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
      rw [this, hΔ']
      rcases R.σ_pm with hs | hs <;> rw [hs] at hσR hconv <;>
        first | exact div_pos (by linarith) (by linarith)
              | exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hm : 0 < det (a - c) w / det (a - c) (b - c) := by
      have : det (a - c) w = -det (c - a) w := by simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
      rw [this, hΔ']
      rcases R.σ_pm with hs | hs <;> rw [hs] at hσR' hconv <;>
        first | exact div_pos (by linarith) (by linarith)
              | exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hΔ'' : det (a - c) (b - c) ≠ 0 := by rw [hΔ']; exact hΔ
    have hmem := u4h_cone_point_mem hl hm (u4h_cone_decomp hΔ'' w)
    set t := 1 / (det w (b - c) / det (a - c) (b - c) + det (a - c) w / det (a - c) (b - c) + 1)
      with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one (by positivity)]; linarith
    have hE : c + t • w ∈ edgeSegment P (j + 1) := by
      rw [u4h_edgeSegment_eq_segment, u4h_mem_segment_iff_lin]
      exact ⟨t, ht0.le, ht1, rfl⟩
    have hT : c + t • w ∈ earHull P j := by
      unfold earHull
      rw [u4h_hull3_rot, u4h_hull3_rot]
      exact hmem
    have hk1 : j + 1 ≠ j - 1 := fun h => h2 (by linear_combination h)
    have hk2 : j + 1 ≠ j := fun h => h1 (by linear_combination h)
    have hx' : c + t • w ∈ edgeSegment P (j - 1) ∪ edgeSegment P j := by
      rw [← hstrict]; exact ⟨hT, u4h_edgeSegment_subset_polygonImage P _ hE⟩
    rcases u4h_edge_inter_ears hP hk1 hk2 ⟨hE, hx'⟩ with h | h
    · have : P (j - 1) ∈ edgeSegment P (j + 1) := h ▸ hE
      rcases u4h_incident_of_vertex_mem hP this with h' | h'
      · exact h2 (by linear_combination -h')
      · exact h3 (by linear_combination -h')
    · have : t • w = 0 := add_eq_left.mp h
      rcases smul_eq_zero.mp this with h' | h'
      · exact ht0.ne' h'
      · have := hinj (sub_eq_zero.mp h')
        exact h1 (by linear_combination this)
  · -- `v` not adjacent to `j`: the turn at `v` is unchanged
    have hnext : deletionIndex j (v' + 1) = v + 1 := by rw [deletionIndex_next j hv1, hv']
    have hprev : deletionIndex j (v' - 1) = v - 1 := by
      have := deletionIndex_next j (i := v' - 1) (by
        intro h; exact hv0 (by linear_combination h))
      rw [sub_add_cancel, hv'] at this
      linear_combination -this
    rw [hnext, hprev] at hσR'
    rcases R.σ_pm with hs | hs <;> rw [hs] at hσR hσR' <;> linarith

end U4Zf_block

section U4Zg_block

/-! Downstream interface, part 2 (U4 helpers): convex ears, the canonical region of an embedded
polygon, and its ear relation; the leaf-level statements. -/

/-- Transport of a region along an equality of polygons. -/
theorem u4h_Region_transport {n : ℕ} {Q Q' : LabelledTuple n} (h : Q = Q') (R : u4h_Region Q) :
    ∃ R' : u4h_Region Q', R'.U = R.U ∧ R'.σ = R.σ := by
  subst h; exact ⟨R, rfl, rfl⟩

theorem u4h_ends_ne_of_det {P : LabelledTuple n} {j : ZMod n}
    (hdet : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0) : P (j - 1) ≠ P (j + 1) := by
  intro h
  apply hdet
  rw [h, sub_self]
  simp [det]

/-- The diagonal of a strict ear is clean (split form). -/
theorem u4h_ear_clean {n : ℕ} [NeZero n] (hn : 4 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    {j : ZMod n} (hdet : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0)
    (hstrict : earHull P j ∩ polygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j) :
    ∀ k, Disjoint (edgeSegment P k)
      (openSegment ℝ (P (j - 1)) (P (j - 1 + ((2 : ℕ) : ZMod n)))) := by
  have hac := u4h_ends_ne_of_det hdet
  have hi2 : j - 1 + ((2 : ℕ) : ZMod n) = j + 1 := by push_cast; ring
  intro k
  rw [hi2, Set.disjoint_left]
  intro x hxk hxo
  by_cases hk1 : k = j - 1
  · rw [hk1, u4h_edgeSegment_prev] at hxk
    have hx' : x ∈ segment ℝ (P (j - 1)) (P j) ∩ segment ℝ (P (j - 1)) (P (j + 1)) :=
      ⟨hxk, openSegment_subset_segment ℝ _ _ hxo⟩
    rw [u4h_segment_inter_same_start hdet] at hx'
    have hx'' : x = P (j - 1) := hx'
    rw [hx''] at hxo
    exact hac (left_mem_openSegment_iff.mp hxo)
  by_cases hk2 : k = j
  · rw [hk2, u4h_edgeSegment_eq_segment, segment_symm] at hxk
    have hD' : det (P j - P (j + 1)) (P (j - 1) - P (j + 1)) ≠ 0 := by
      have e : det (P j - P (j + 1)) (P (j - 1) - P (j + 1)) =
          -det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) := by
        simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
      rw [e]; exact neg_ne_zero.mpr hdet
    have hx' : x ∈ segment ℝ (P (j + 1)) (P j) ∩ segment ℝ (P (j + 1)) (P (j - 1)) :=
      ⟨hxk, by rw [segment_symm]; exact openSegment_subset_segment ℝ _ _ hxo⟩
    rw [u4h_segment_inter_same_start hD'] at hx'
    have hx'' : x = P (j + 1) := hx'
    rw [hx''] at hxo
    exact hac (right_mem_openSegment_iff.mp hxo)
  exact u4h_edge_disjoint_openDiag' hP hac hstrict hk1 hk2 hxk hxo

/-- **Convex ear existence** for embedded polygons with at least four vertices. -/
theorem u4h_exists_convex_ear {n' : ℕ} (hn : 2 ≤ n') {P : LabelledTuple (n' + 2)}
    (hP : Embedded P) :
    ∃ j : ZMod (n' + 2), det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0 ∧
      u4h_VertexEmpty P j ∧
      ∀ R : u4h_Region P, 0 < R.σ * det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) := by
  obtain ⟨R0⟩ := u4h_region_exists (n' + 2) (by omega) P hP
  obtain ⟨j, hdet, hV, hside⟩ := u4h_exists_ear_of_region (by omega) hP R0
  refine ⟨j, hdet, hV, fun R => ?_⟩
  rw [u4h_sigma_unique (by omega) hP R R0]
  exact hside

/-- The triangle region as a face carrier for the half-disc lemma: a positively oriented
`Triangle` with carrier the ear triangle and an edge equal to the diagonal. -/
theorem u4h_ear_triangle {n : ℕ} (P : LabelledTuple n) (j : ZMod n)
    (hdet : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0) :
    ∃ (TT : Triangle) (k : Fin 3), TT.carrier = earHull P j ∧
      TT.edgeSeg k = segment ℝ (P (j - 1)) (P (j + 1)) ∧ TT.v (k + 2) = P j := by
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · have hD' : 0 < det (P (j + 1) - P (j - 1)) (P j - P (j - 1)) := by rw [u4h_det_swap']; linarith
    refine ⟨u4h_mkTri (P (j - 1)) (P (j + 1)) (P j) hD', 0, ?_, ?_, rfl⟩
    · rw [u4h_mkTri_carrier, earHull, u4h_hull3_comm]
    · rfl
  · refine ⟨u4h_mkTri (P (j - 1)) (P j) (P (j + 1)) hpos, 2, ?_, ?_, rfl⟩
    · rw [u4h_mkTri_carrier]; rfl
    · rw [u4h_mkTri_edgeSeg2, segment_symm]

/-- **The canonical region and an ear.** For a strict convex vertex-empty ear `j` the canonical
region of `P` is the union of the region of `deleteVertex P j` and the ear triangle, and the ear
triangle meets that region exactly in the diagonal. -/
theorem u4h_regionOf_ear {n' : ℕ} (hn : 2 ≤ n') {P : LabelledTuple (n' + 2)} (hP : Embedded P)
    {j : ZMod (n' + 2)} (hdet : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0)
    (hV : u4h_VertexEmpty P j)
    (hconv : ∀ R : u4h_Region P, 0 < R.σ * det (P j - P (j - 1)) (P (j + 1) - P (j - 1))) :
    earHull P j ∩ u4h_regionOf (deleteVertex P j) = segment ℝ (P (j - 1)) (P (j + 1)) ∧
      u4h_regionOf P = u4h_regionOf (deleteVertex P j) ∪ earHull P j := by
  have h4 : 4 ≤ n' + 2 := by omega
  have hinj := u4h_vertex_injective hP
  have h1 : (1 : ZMod (n' + 2)) ≠ 0 := u4h_one_ne_zero h4
  have h2 : (2 : ZMod (n' + 2)) ≠ 0 := u4h_two_ne_zero h4
  have h3 : (3 : ZMod (n' + 2)) ≠ 0 := u4h_three_ne_zero h4
  have hstrict := u4h_strict_ear_of_vertex_empty hP h4 hdet hV
  have hac := u4h_ends_ne_of_det hdet
  have hP' : Embedded (deleteVertex P j) :=
    u4h_embedded_deleteVertex (n := n' + 1) (by omega) hP hac hstrict
  obtain ⟨R⟩ := u4h_region_exists (n' + 2) (by omega) P hP
  obtain ⟨R'⟩ := u4h_region_exists (n' + 1) (by omega) _ hP'
  have hi2 : j - 1 + ((2 : ℕ) : ZMod (n' + 2)) = j + 1 := by push_cast; ring
  have hsub : u4h_subPoly P (j - 1 + ((2 : ℕ) : ZMod (n' + 2))) (n' + 2 - 2) = deleteVertex P j := by
    rw [hi2, u4h_deleteVertex_eq_subPoly]
    rfl
  obtain ⟨R2, hR2U, hR2σ⟩ := u4h_Region_transport hsub.symm R'
  have hclean := u4h_ear_clean h4 hP hdet hstrict
  have hP1 : Embedded (u4h_subPoly P (j - 1) 2) :=
    u4h_subPoly_embedded hP (le_refl 2) (by omega) hclean
  obtain ⟨R1, hR1U⟩ := u4h_triRegion' (u4h_subPoly P (j - 1) 2) hP1
  have hP10 : u4h_subPoly P (j - 1) 2 0 = P (j - 1) := u4h_subPoly_zero P (j - 1) 2
  have hP11 : u4h_subPoly P (j - 1) 2 1 = P j := by
    rw [u4h_subPoly_one P (j - 1) (by norm_num), sub_add_cancel]
  have hP12 : u4h_subPoly P (j - 1) 2 2 = P (j + 1) := by
    rw [u4h_subPoly_apply]
    have : (2 : ZMod (2 + 1)).val = 2 := by
      rw [show (2 : ZMod (2 + 1)) = ((2 : ℕ) : ZMod (2 + 1)) from Nat.cast_ofNat.symm,
        ZMod.val_natCast_of_lt (by norm_num)]
    rw [this, ← hi2]
  have hR1 : R1.U = earHull P j := by rw [hR1U, hP10, hP11, hP12]; rfl
  have hPjD : P j ∉ segment ℝ (P (j - 1)) (P (j + 1)) := by
    intro h
    apply hdet
    have := u4h_det_segment_zero h
    rw [u4h_det_swap']; rw [this]; ring
  -- polygon image of the second sub-polygon
  have hpoly2 : polygonImage (u4h_subPoly P (j - 1 + ((2 : ℕ) : ZMod (n' + 2))) (n' + 2 - 2)) =
      polygonImage (deleteVertex P j) := by rw [hsub]
  have hTinter : earHull P j ∩ polygonImage (deleteVertex P j) =
      segment ℝ (P (j - 1)) (P (j + 1)) := u4h_earHull_inter_polygonImage_delete hP hstrict
  -- X1: the apex is outside the second region
  have X1 : ∃ s : ℕ, s < 2 ∧ ∃ x ∈ edgeSegment P (j - 1 + (s : ZMod (n' + 2))),
      x ∉ ({P (j - 1), P (j - 1 + ((2 : ℕ) : ZMod (n' + 2)))} : Set Plane) ∧ x ∉ R2.U := by
    refine ⟨0, by norm_num, P j, ?_, ?_, ?_⟩
    · rw [Nat.cast_zero, add_zero]
      have := u4h_end_mem_edgeSegment P (j - 1)
      rwa [sub_add_cancel] at this
    · rw [hi2]
      rintro (h | h)
      · exact h1 (by linear_combination (hinj h))
      · exact h1 (by linear_combination -(hinj (Set.mem_singleton_iff.mp h)))
    · intro hPj
      obtain ⟨v, hv⟩ := u4h_exists_lexmin hP
      by_cases hvj : v = j
      · -- the apex is the lexmin: not in the hull of the other vertices
        subst hvj
        apply u4h_lexmin_not_mem_hull hv ?_ (R2.hull hPj)
        rintro x ⟨k, rfl⟩
        rw [u4h_subPoly_apply, hi2]
        refine ⟨v + 1 + (k.val : ZMod (n' + 2)), ?_, rfl⟩
        intro h
        have hkv := ZMod.val_lt k
        have : ((1 + k.val : ℕ) : ZMod (n' + 2)) = 0 := by push_cast; linear_combination h
        exact u4h_natCast_ne_zero (n := n' + 2) (k := 1 + k.val) (by omega) (by omega) this
      · -- sides agree, so the ear triangle would be inside, forcing an interior diagonal point
        have hσ : R.σ = R2.σ := by
          rw [hR2σ]; exact u4h_sigma_ear hn hP hdet hstrict R R' (hconv R) hv hvj
        set a := P (j - 1) with ha
        set c := P (j + 1) with hc
        set D := segment ℝ a c with hD
        -- the ear triangle minus the diagonal lies in the interior of `R2.U`
        have hTD : earHull P j \ D ⊆ interior R2.U := by
          have hconvex : Convex ℝ (earHull P j \ D) := by
            rcases lt_or_gt_of_ne hdet with hneg | hpos
            · have hD' : 0 < det (P j - c) (a - c) := by
                have e : det (P j - c) (a - c) = -det (P j - a) (c - a) := by
                  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
                rw [e]; linarith
              have := u4h_convex_hull3_diff_edge hD'
              have e2 : earHull P j = convexHull ℝ {c, P j, a} := by
                unfold earHull; rw [u4h_hull3_rot, u4h_hull3_rot, u4h_hull3_comm]
              rw [hD, e2]; exact this
            · have := u4h_convex_hull3_diff_edge hpos
              rw [hD, segment_symm]; exact this
          have hsub' : earHull P j \ D ⊆ interior R2.U ∪ R2.Uᶜ := by
            rintro y ⟨hyT, hyD⟩
            by_cases hy : y ∈ R2.U
            · left
              by_contra hyi
              have hyf : y ∈ frontier R2.U := ⟨subset_closure hy, hyi⟩
              rw [R2.frontier_eq, hpoly2] at hyf
              exact hyD (hTinter ▸ ⟨hyT, hyf⟩)
            · right; exact hy
          rcases IsPreconnected.subset_or_subset isOpen_interior R2.isClosed.isOpen_compl
              (Set.disjoint_left.mpr fun y hy hy' => hy' (interior_subset hy)) hsub'
              hconvex.isPreconnected with h | h
          · exact h
          · exfalso
            exact h ⟨subset_convexHull ℝ _ (by simp), hPjD⟩ hPj
        have hTU : earHull P j ⊆ R2.U := by
          intro y hy
          by_cases hyD : y ∈ D
          · rw [hR2U]
            have hy' : y ∈ earHull P j ∩ polygonImage (deleteVertex P j) := by
              rw [hTinter]; exact hyD
            have := hy'.2
            rw [← R'.frontier_eq] at this
            exact R'.isClosed.frontier_subset this
          · exact interior_subset (hTD ⟨hy, hyD⟩)
        -- the face of `R2.K` at the diagonal and the ear triangle cover a ball at the midpoint
        obtain ⟨F2, hF2, k2, hk2⟩ := R2.edge_face (-1)
        rw [u4h_subPoly_edgeSegment_last, u4h_split_second_start (by omega), hi2] at hk2
        have hside := R2.side (-1) F2 hF2 k2 (by
          rw [u4h_subPoly_edgeSegment_last, u4h_split_second_start (by omega), hi2]; exact hk2)
        rw [neg_add_cancel, u4h_subPoly_zero, u4h_subPoly_last,
          u4h_split_second_start (by omega)] at hside
        have ePj : P (j - 1 + ((2 : ℕ) : ZMod (n' + 2))) = P (j + 1) := by rw [hi2]
        rw [ePj] at hside
        obtain ⟨TT, kT, hTTc, hTTk, hTTapex⟩ := u4h_ear_triangle P j hdet
        set x : Plane := (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • c with hx
        have hxo : x ∈ openSegment ℝ a c := u4h_midpoint_mem_openSegment _ _
        obtain ⟨ε1, hε1, hb1⟩ := u4h_face_halfdisc F2 k2 (by rw [hk2, segment_symm]) hxo
        obtain ⟨ε2, hε2, hb2⟩ := u4h_face_halfdisc TT kT hTTk hxo
        rw [hTTapex] at hb2
        have hxD : x ∈ D := openSegment_subset_segment ℝ _ _ hxo
        have hxfr : x ∈ frontier R2.U := by
          rw [R2.frontier_eq, hpoly2]
          have hx' : x ∈ earHull P j ∩ polygonImage (deleteVertex P j) := by
            rw [hTinter]; exact hxD
          exact hx'.2
        apply disjoint_interior_frontier.notMem_of_mem_right hxfr
        rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
        refine ⟨min ε1 ε2, lt_min hε1 hε2, fun y hy => ?_⟩
        rw [Metric.mem_ball] at hy
        -- signs of the two apexes
        have hs2 : 0 < R.σ * det (c - a) (F2.v (k2 + 2) - a) := by rw [hσ]; exact hside
        have hsT : 0 < R.σ * -det (c - a) (P j - a) := by
          have e : -det (c - a) (P j - a) = det (P j - a) (c - a) := by rw [u4h_det_swap']; ring
          rw [e]; exact hconv R
        by_cases hy1 : 0 ≤ det (c - a) (F2.v (k2 + 2) - a) * det (c - a) (y - a)
        · exact R2.face_subset hF2 ((hb1 y (lt_of_lt_of_le hy (min_le_left _ _))).mpr hy1)
        · apply hTU
          rw [← hTTc]
          rw [hb2 y (lt_of_lt_of_le hy (min_le_right _ _))]
          have hy1' := not_le.mp hy1
          rcases R.σ_pm with hs | hs <;> rw [hs] at hs2 hsT <;> nlinarith
  -- X2: the vertex `P (j+2)` of the rest is not in the ear triangle
  have X2 : ∃ s : ℕ, s < n' + 2 - 2 ∧
      ∃ x ∈ edgeSegment P (j - 1 + ((2 : ℕ) : ZMod (n' + 2)) + (s : ZMod (n' + 2))),
      x ∉ ({P (j - 1), P (j - 1 + ((2 : ℕ) : ZMod (n' + 2)))} : Set Plane) ∧ x ∉ R1.U := by
    refine ⟨0, by omega, P (j + 2), ?_, ?_, ?_⟩
    · rw [Nat.cast_zero, add_zero, hi2]
      have := u4h_end_mem_edgeSegment P (j + 1)
      rwa [show j + 1 + 1 = j + 2 by ring] at this
    · rw [hi2]
      rintro (h | h)
      · exact h3 (by linear_combination (hinj h))
      · exact h1 (by linear_combination (hinj (Set.mem_singleton_iff.mp h)))
    · rw [hR1]
      intro hmem
      rcases hV (j + 2) hmem with h | h | h
      · exact h3 (by linear_combination h)
      · exact h2 (by linear_combination h)
      · exact h1 (by linear_combination h)
  set C : u4h_SplitCtx P (j - 1) 2 := u4h_SplitCtx.mk hP (le_refl 2) (by omega) hclean R1 R2 X1 X2
    with hC
  obtain ⟨G, hG⟩ := C.region'
  have hinter : R1.U ∩ R2.U = segment ℝ (P (j - 1)) (P (j - 1 + ((2 : ℕ) : ZMod (n' + 2)))) :=
    C.inter
  have ePj : P (j - 1 + ((2 : ℕ) : ZMod (n' + 2))) = P (j + 1) := by rw [hi2]
  rw [ePj] at hinter
  have hG' : G.U = R1.U ∪ R2.U := hG
  have hregP : u4h_regionOf P = G.U := (u4h_region_U_eq_regionOf (by omega) hP G).symm
  have hreg' : u4h_regionOf (deleteVertex P j) = R'.U :=
    (u4h_region_U_eq_regionOf (n := n' + 1) (by omega) hP' R').symm
  refine ⟨?_, ?_⟩
  · rw [hreg', ← hR2U, ← hR1]
    exact hinter
  · rw [hregP, hG', hR1, hR2U, hreg', Set.union_comm]

/-- Leaf-level: `U4_exists_ear`. -/
theorem u4h_U4_exists_ear {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple (n + 1))
    (hP : Embedded P) :
    ∃ j : ZMod (n + 1), Embedded (deleteVertex P j) ∧
      det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0 ∧
      earHull P j ∩ polygonImage (deleteVertex P j) = segment ℝ (P (j - 1)) (P (j + 1)) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, hdet, hV, -⟩ := u4h_exists_convex_ear (n' := n') (by omega) hP
  have hstrict := u4h_strict_ear_of_vertex_empty hP (by omega) hdet hV
  have hac := u4h_ends_ne_of_det hdet
  exact ⟨j, u4h_embedded_deleteVertex (by omega) hP hac hstrict, hdet,
    u4h_earHull_inter_polygonImage_delete hP hstrict⟩

/-- Leaf-level: `U4_exists_triangulation`, with the canonical region as the set. -/
theorem u4h_U4_exists_triangulation {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) :
    ∃ K : Triangulation (u4h_regionOf P), frontier (u4h_regionOf P) = polygonImage P ∧
      (∀ i, ∃ T ∈ K.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment P i) ∧
      (∀ i, ∀ T ∈ K.faces, ∀ T' ∈ K.faces, edgeSegment P i ⊆ T.carrier →
        edgeSegment P i ⊆ T'.carrier → T.carrier = T'.carrier) ∧
      ∀ L, InsideModel L P → u4h_regionOf P ⊆ interior (square L) := by
  obtain ⟨R⟩ := u4h_region_exists n hn P hP
  have hU := u4h_region_U_eq_regionOf hn hP R
  rw [← hU]
  refine ⟨R.K, R.frontier_eq, R.edge_face, R.edge_unique, fun L hL x hx => ?_⟩
  have hsub : convexHull ℝ (Set.range P) ⊆ Metric.ball 0 L := by
    apply convexHull_min _ (convex_ball _ _)
    rintro y ⟨i, rfl⟩
    exact u4h_mem_ball_of_supNorm_lt (hL i)
  exact u4h_ball_subset_interior_square L (hsub (R.hull hx))

/-- Leaf-level: `U4_triangle_base`. -/
theorem u4h_U4_triangle_base (P : LabelledTuple 3) (hP : Embedded P) :
    det (P 1 - P 0) (P 2 - P 0) ≠ 0 ∧ polygonImage P = frontier (earHull P 1) := by
  have hD := u4h_tri3_det_ne_zero P hP
  refine ⟨hD, ?_⟩
  have h10 : (1 : ZMod 3) - 1 = 0 := by decide
  have h11 : (1 : ZMod 3) + 1 = 2 := by decide
  rw [earHull, h10, h11, u4h_polygonImage_zmod3]
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · have hD' : 0 < det (P 2 - P 0) (P 1 - P 0) := by rw [u4h_det_swap']; linarith
    rw [u4h_hull3_comm, u4h_frontier_hull3 hD', segment_symm ℝ (P 0) (P 2),
      segment_symm ℝ (P 2) (P 1), segment_symm ℝ (P 1) (P 0)]
    ext x; simp only [Set.mem_union]; tauto
  · rw [u4h_frontier_hull3 hpos]

/-- The canonical region of an embedded triangle is its hull (the base of the ear sequence). -/
theorem u4h_regionOf_triangle (P : LabelledTuple 3) (hP : Embedded P) :
    u4h_regionOf P = earHull P 1 := by
  obtain ⟨R, hRU⟩ := u4h_triRegion' P hP
  rw [← u4h_region_U_eq_regionOf (le_refl 3) hP R, hRU]
  have h10 : (1 : ZMod 3) - 1 = 0 := by decide
  have h11 : (1 : ZMod 3) + 1 = 2 := by decide
  rw [earHull, h10, h11]

/-- The canonical region: frontier, compactness, hull bound, model square. -/
theorem u4h_regionOf_spec {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    frontier (u4h_regionOf P) = polygonImage P ∧ IsCompact (u4h_regionOf P) ∧
      u4h_regionOf P ⊆ convexHull ℝ (Set.range P) ∧
      ∀ L, InsideModel L P → u4h_regionOf P ⊆ interior (square L) := by
  obtain ⟨R⟩ := u4h_region_exists n hn P hP
  have hU := u4h_region_U_eq_regionOf hn hP R
  rw [← hU]
  refine ⟨R.frontier_eq, u4h_triangulation_isCompact R.K, R.hull, fun L hL x hx => ?_⟩
  have hsub : convexHull ℝ (Set.range P) ⊆ Metric.ball 0 L := by
    apply convexHull_min _ (convex_ball _ _)
    rintro y ⟨i, rfl⟩
    exact u4h_mem_ball_of_supNorm_lt (hL i)
  exact u4h_ball_subset_interior_square L (hsub (R.hull hx))

end U4Zg_block


/-- U4: the polygon image is compact. -/
theorem U4_polygonImage_isCompact [NeZero n] (P : LabelledTuple n) : IsCompact (polygonImage P) := by
  exact u4h_polygonImage_isCompact P

/-- U4: the traversal image is the polygon image. -/
theorem U4_range_traversal [NeZero n] (P : LabelledTuple n) : range (traversal P) = polygonImage P := by
  exact u4h_range_traversal P

/-- U4 (sm-3:439 "inside a large rectangle"): some model square contains the polygon. -/
theorem U4_exists_insideModel [NeZero n] (P : LabelledTuple n) : ∃ L : ℝ, 0 < L ∧ InsideModel L P := by
  exact u4h_exists_insideModel P

/-- U4: `InsideModel L P` puts the polygon image strictly inside `Q_L`. -/
theorem U4_polygonImage_subset_interior_square [NeZero n] {L : ℝ} (P : LabelledTuple n)
    (hL : InsideModel L P) : polygonImage P ⊆ interior (square L) ∧ 0 < L := by
  exact u4h_polygonImage_subset_interior_square P hL

/-- U4: an embedded polygon has at least three vertices. -/
theorem U4_three_le_of_embedded [NeZero n] (P : LabelledTuple n) (hP : Embedded P) : 3 ≤ n := by
  exact u4h_three_le_of_embedded P hP

/-- U4 (base case): an embedded triangle bounds its convex hull. -/
theorem U4_triangle_base (P : LabelledTuple 3) (hP : Embedded P) :
    det (P 1 - P 0) (P 2 - P 0) ≠ 0 ∧ polygonImage P = frontier (earHull P 1) := by
  exact u4h_U4_triangle_base P hP

/-- U4 (Meisters' two ears, sm-3:437-439 spirit): an embedded polygon with at least four vertices has
an ear: a vertex `j` with nonzero turn whose ear triangle meets the rest of the polygon exactly in
the diagonal, and whose deletion is again embedded. -/
theorem U4_exists_ear [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple (n + 1)) (hP : Embedded P) :
    ∃ j : ZMod (n + 1), Embedded (deleteVertex P j) ∧
      det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0 ∧
      earHull P j ∩ polygonImage (deleteVertex P j) = segment ℝ (P (j - 1)) (P (j + 1)) := by
  exact u4h_U4_exists_ear hn P hP

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
  obtain ⟨K, h1, h2, h3, h4⟩ := u4h_U4_exists_triangulation hn P hP
  exact ⟨_, K, h1, h2, h3, h4⟩

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
