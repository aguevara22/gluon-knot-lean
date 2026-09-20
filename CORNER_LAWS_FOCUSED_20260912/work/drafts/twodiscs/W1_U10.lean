import SM.EmbeddedRotation
import SM.LinkMoves
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.SetTheory.Cardinal.Finite
import SM.DeletedTuple
import Mathlib.Analysis.Convex.Gauge

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

/-! #### U10 helpers for `U10_fan_extension` (radial gauge, sectors, marks, fan, cone) -/

/-- U10 helper: the translate of `D` bringing `z` to the origin. -/
def u10h_D0 (D : Set Plane) (z : Plane) : Set Plane := (Homeomorph.addRight z) ⁻¹' D

/-- U10 helper: the radial gauge of `D` about `z`. -/
noncomputable def u10h_rg (D : Set Plane) (z : Plane) (x : Plane) : ℝ := gauge (u10h_D0 D z) (x - z)

theorem u10h_mem_D0 {D : Set Plane} {z w : Plane} : w ∈ u10h_D0 D z ↔ w + z ∈ D := Iff.rfl

theorem u10h_D0_convex {D : Set Plane} (hD : Link.IsDisc D) (z : Plane) : Convex ℝ (u10h_D0 D z) := by
  have h : u10h_D0 D z = (fun x => x + z) ⁻¹' D := by ext w; simp [u10h_D0]
  rw [h]; exact hD.convex.translate_preimage_left z

theorem u10h_D0_isCompact {D : Set Plane} (hD : Link.IsDisc D) (z : Plane) : IsCompact (u10h_D0 D z) :=
  (Homeomorph.addRight z).isCompact_preimage.mpr hD.isCompact

theorem u10h_D0_interior {D : Set Plane} (z : Plane) :
    interior (u10h_D0 D z) = (Homeomorph.addRight z) ⁻¹' interior D :=
  ((Homeomorph.addRight z).preimage_interior D).symm

theorem u10h_D0_frontier {D : Set Plane} (z : Plane) :
    frontier (u10h_D0 D z) = (Homeomorph.addRight z) ⁻¹' frontier D :=
  ((Homeomorph.addRight z).preimage_frontier D).symm

theorem u10h_D0_closure {D : Set Plane} (z : Plane) :
    closure (u10h_D0 D z) = (Homeomorph.addRight z) ⁻¹' closure D :=
  ((Homeomorph.addRight z).preimage_closure D).symm

theorem u10h_D0_nhds {D : Set Plane} {z : Plane} (hz : z ∈ interior D) : u10h_D0 D z ∈ nhds (0 : Plane) := by
  rw [mem_nhds_iff]
  refine ⟨interior (u10h_D0 D z), interior_subset, isOpen_interior, ?_⟩
  rw [u10h_D0_interior]
  simpa using hz

theorem u10h_D0_absorbent {D : Set Plane} {z : Plane} (hz : z ∈ interior D) : Absorbent ℝ (u10h_D0 D z) :=
  absorbent_nhds_zero (u10h_D0_nhds hz)

theorem u10h_D0_bounded {D : Set Plane} (hD : Link.IsDisc D) (z : Plane) :
    Bornology.IsVonNBounded ℝ (u10h_D0 D z) :=
  (u10h_D0_isCompact hD z).isVonNBounded ℝ

theorem u10h_rg_nonneg (D : Set Plane) (z x : Plane) : 0 ≤ u10h_rg D z x := gauge_nonneg _

theorem u10h_rg_lt_one_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u10h_rg D z x < 1 ↔ x ∈ interior D := by
  unfold u10h_rg
  rw [gauge_lt_one_iff_mem_interior (u10h_D0_convex hD z) (u10h_D0_nhds hz), u10h_D0_interior]
  simp

theorem u10h_rg_le_one_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u10h_rg D z x ≤ 1 ↔ x ∈ D := by
  unfold u10h_rg
  rw [gauge_le_one_iff_mem_closure (u10h_D0_convex hD z) (u10h_D0_nhds hz), u10h_D0_closure,
    hD.isCompact.isClosed.closure_eq]
  simp

theorem u10h_rg_eq_one_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u10h_rg D z x = 1 ↔ x ∈ frontier D := by
  unfold u10h_rg
  rw [gauge_eq_one_iff_mem_frontier (u10h_D0_convex hD z) (u10h_D0_nhds hz), u10h_D0_frontier]
  simp

theorem u10h_rg_eq_zero_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u10h_rg D z x = 0 ↔ x = z := by
  unfold u10h_rg
  rw [gauge_eq_zero (u10h_D0_absorbent hz) (u10h_D0_bounded hD z), sub_eq_zero]

theorem u10h_rg_pos {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) {x : Plane}
    (hx : x ≠ z) : 0 < u10h_rg D z x :=
  lt_of_le_of_ne (u10h_rg_nonneg D z x) (fun h => hx ((u10h_rg_eq_zero_iff hD hz x).mp h.symm))

theorem u10h_rg_self (D : Set Plane) (z : Plane) : u10h_rg D z z = 0 := by
  simp [u10h_rg, gauge_zero]

theorem u10h_rg_smul (D : Set Plane) (z x : Plane) {t : ℝ} (ht : 0 ≤ t) :
    u10h_rg D z (z + t • (x - z)) = t * u10h_rg D z x := by
  unfold u10h_rg
  rw [add_sub_cancel_left, gauge_smul_of_nonneg ht, smul_eq_mul]

theorem u10h_rg_continuous {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) :
    Continuous (u10h_rg D z) :=
  (continuous_gauge (u10h_D0_convex hD z) (u10h_D0_nhds hz)).comp (continuous_id.sub continuous_const)

/-- The frontier point on the ray from `z` through `x ≠ z`. -/
noncomputable def u10h_ray (D : Set Plane) (z x : Plane) : Plane := z + (u10h_rg D z x)⁻¹ • (x - z)

theorem u10h_ray_mem_frontier {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ≠ z) : u10h_ray D z x ∈ frontier D := by
  rw [← u10h_rg_eq_one_iff hD hz, u10h_ray, u10h_rg_smul D z x (inv_nonneg.mpr (u10h_rg_nonneg D z x))]
  exact inv_mul_cancel₀ (u10h_rg_pos hD hz hx).ne'

theorem u10h_ray_spec {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ≠ z) : x = z + u10h_rg D z x • (u10h_ray D z x - z) := by
  rw [u10h_ray, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ (u10h_rg_pos hD hz hx).ne', one_smul,
    add_sub_cancel]

theorem u10h_ray_of_frontier {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {y : Plane} (hy : y ∈ frontier D) : u10h_ray D z y = y := by
  rw [u10h_ray, (u10h_rg_eq_one_iff hD hz y).mpr hy, inv_one, one_smul, add_sub_cancel]

theorem u10h_frontier_ne {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {y : Plane} (hy : y ∈ frontier D) : y ≠ z := by
  intro h; subst h
  have := (u10h_rg_eq_one_iff hD hz y).mpr hy
  rw [u10h_rg_self] at this; norm_num at this

theorem u10h_frontier_subset {D : Set Plane} (hD : Link.IsDisc D) : frontier D ⊆ D :=
  hD.isCompact.isClosed.frontier_subset

/-! ### det algebra -/

theorem u10h_det_add_right (u v w : Plane) : det u (v + w) = det u v + det u w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem u10h_det_smul_right (u v : Plane) (c : ℝ) : det u (c • v) = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u10h_det_add_left (u v w : Plane) : det (u + v) w = det u w + det v w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem u10h_det_smul_left' (u v : Plane) (c : ℝ) : det (c • u) v = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u10h_det_self (u : Plane) : det u u = 0 := by simp only [det]; ring

theorem u10h_det_zero_right (u : Plane) : det u 0 = 0 := by simp [det]

theorem u10h_det_zero_left (u : Plane) : det 0 u = 0 := by simp [det]

theorem u10h_det_swap' (u v : Plane) : det u v = -det v u := by simp only [det]; ring

theorem u10h_cramer {u v : Plane} (h : det u v ≠ 0) (w : Plane) :
    w = (det w v / det u v) • u + (det u w / det u v) • v := by
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, div_mul_eq_mul_div, ← add_div]
    rw [eq_div_iff h]; unfold det; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, div_mul_eq_mul_div, ← add_div]
    rw [eq_div_iff h]; unfold det; ring

theorem u10h_parallel_of_det_eq_zero {u v : Plane} (hu : u ≠ 0) (h : det u v = 0) :
    ∃ μ : ℝ, v = μ • u := by
  have hn : 0 < u.1 ^ 2 + u.2 ^ 2 := by
    rcases not_and_or.mp (fun hc : u.1 = 0 ∧ u.2 = 0 => hu (Prod.ext hc.1 hc.2)) with h1 | h2 <;>
      positivity
  refine ⟨(u.1 * v.1 + u.2 * v.2) / (u.1 ^ 2 + u.2 ^ 2), ?_⟩
  simp only [det] at h
  ext
  · simp only [Prod.smul_fst, smul_eq_mul]
    field_simp
    linear_combination (-u.2) * h
  · simp only [Prod.smul_snd, smul_eq_mul]
    field_simp
    linear_combination u.1 * h

/-! ### half-planes are convex -/

theorem u10h_convex_det_nonneg (z u : Plane) : Convex ℝ {x : Plane | 0 ≤ det u (x - z)} := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ det u (x - z) at hx
  change 0 ≤ det u (y - z) at hy
  change 0 ≤ det u (a • x + b • y - z)
  have hz' : z = a • z + b • z := by rw [← add_smul, hab, one_smul]
  have : a • x + b • y - z = a • (x - z) + b • (y - z) := by
    calc a • x + b • y - z = a • x + b • y - (a • z + b • z) := by rw [← hz']
      _ = a • (x - z) + b • (y - z) := by rw [smul_sub, smul_sub]; abel
  rw [this, u10h_det_add_right, u10h_det_smul_right, u10h_det_smul_right]
  positivity

theorem u10h_convex_det_nonneg' (z v : Plane) : Convex ℝ {x : Plane | 0 ≤ det (x - z) v} := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ det (x - z) v at hx
  change 0 ≤ det (y - z) v at hy
  change 0 ≤ det (a • x + b • y - z) v
  have hz' : z = a • z + b • z := by rw [← add_smul, hab, one_smul]
  have : a • x + b • y - z = a • (x - z) + b • (y - z) := by
    calc a • x + b • y - z = a • x + b • y - (a • z + b • z) := by rw [← hz']
      _ = a • (x - z) + b • (y - z) := by rw [smul_sub, smul_sub]; abel
  rw [this, u10h_det_add_left, u10h_det_smul_left', u10h_det_smul_left']
  positivity

/-! ### a straight frontier piece is not seen edge-on from `z` -/

theorem u10h_det_ne_zero_of_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hne : a ≠ b) (hseg : segment ℝ a b ⊆ frontier D) : det (a - z) (b - z) ≠ 0 := by
  intro h0
  have ha : a ∈ frontier D := hseg (left_mem_segment ℝ a b)
  have hb : b ∈ frontier D := hseg (right_mem_segment ℝ a b)
  have haz : a - z ≠ 0 := sub_ne_zero.mpr (u10h_frontier_ne hD hz ha)
  obtain ⟨μ, hμ⟩ := u10h_parallel_of_det_eq_zero haz h0
  have hb' : b = z + μ • (a - z) := by rw [← hμ]; abel
  rcases le_or_gt 0 μ with hμ0 | hμ0
  · have h1 := (u10h_rg_eq_one_iff hD hz b).mpr hb
    rw [hb', u10h_rg_smul D z a hμ0, (u10h_rg_eq_one_iff hD hz a).mpr ha, mul_one] at h1
    subst h1
    apply hne; rw [hb', one_smul, add_sub_cancel]
  · have h1μ : (1 - μ) ≠ 0 := by linarith
    have hzmem : z ∈ segment ℝ a b := by
      refine ⟨-μ / (1 - μ), 1 / (1 - μ), by
        apply div_nonneg <;> linarith, by
        apply div_nonneg <;> linarith, by
        rw [← add_div, div_eq_one_iff_eq h1μ]; ring, ?_⟩
      rw [hb']
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; field_simp; ring
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; field_simp; ring
    have := (u10h_rg_eq_one_iff hD hz z).mpr (hseg hzmem)
    rw [u10h_rg_self] at this; norm_num at this

/-! ### the sector lemma and the fan characterisation -/

/-- A frontier point in the closed sector spanned (from `z`) by a straight frontier piece `[a, b]`
lies on that piece. -/
theorem u10h_frontier_mem_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hab : 0 < det (a - z) (b - z)) (hseg : segment ℝ a b ⊆ frontier D) {y : Plane}
    (hy : y ∈ frontier D) (h1 : 0 ≤ det (a - z) (y - z)) (h2 : 0 ≤ det (y - z) (b - z)) :
    y ∈ segment ℝ a b := by
  set β := det (y - z) (b - z) / det (a - z) (b - z) with hβ
  set γ := det (a - z) (y - z) / det (a - z) (b - z) with hγ
  have hβ0 : 0 ≤ β := div_nonneg h2 hab.le
  have hγ0 : 0 ≤ γ := div_nonneg h1 hab.le
  have hdec : y - z = β • (a - z) + γ • (b - z) := u10h_cramer hab.ne' (y - z)
  have hs : 0 < β + γ := by
    rcases (add_nonneg hβ0 hγ0).lt_or_eq with h | h
    · exact h
    · exfalso
      have hβz : β = 0 := by linarith
      have hγz : γ = 0 := by linarith
      rw [hβz, hγz, zero_smul, zero_smul, add_zero] at hdec
      exact u10h_frontier_ne hD hz hy (sub_eq_zero.mp hdec)
  set s := β + γ with hs_def
  set w : Plane := (β / s) • a + (γ / s) • b with hw
  have hwseg : w ∈ segment ℝ a b :=
    ⟨β / s, γ / s, div_nonneg hβ0 hs.le, div_nonneg hγ0 hs.le, by rw [← add_div, div_self hs.ne'], rfl⟩
  have hyw : y = z + s • (w - z) := by
    have e1 := congrArg Prod.fst hdec
    have e2 := congrArg Prod.snd hdec
    simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.snd_sub, Prod.snd_add,
      Prod.smul_snd] at e1 e2
    ext
    · simp only [hw, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      field_simp
      linear_combination e1
    · simp only [hw, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      field_simp
      linear_combination e2
  have hrw : u10h_rg D z w = 1 := (u10h_rg_eq_one_iff hD hz w).mpr (hseg hwseg)
  have hry : u10h_rg D z y = 1 := (u10h_rg_eq_one_iff hD hz y).mpr hy
  rw [hyw, u10h_rg_smul D z w hs.le, hrw, mul_one] at hry
  rw [hyw, hry, one_smul, add_sub_cancel]
  exact hwseg

/-- The ray point of a point of the closed sector lies on the frontier piece. -/
theorem u10h_ray_mem_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hab : 0 < det (a - z) (b - z)) (hseg : segment ℝ a b ⊆ frontier D) {x : Plane}
    (hxz : x ≠ z) (h1 : 0 ≤ det (a - z) (x - z)) (h2 : 0 ≤ det (x - z) (b - z)) :
    u10h_ray D z x ∈ segment ℝ a b := by
  have hyz : u10h_ray D z x - z = (u10h_rg D z x)⁻¹ • (x - z) := by simp [u10h_ray]
  have hr0 : 0 ≤ (u10h_rg D z x)⁻¹ := inv_nonneg.mpr (u10h_rg_nonneg _ _ _)
  refine u10h_frontier_mem_segment hD hz hab hseg (u10h_ray_mem_frontier hD hz hxz) ?_ ?_
  · rw [hyz, u10h_det_smul_right]; exact mul_nonneg hr0 h1
  · rw [hyz, u10h_det_smul_left']; exact mul_nonneg hr0 h2

/-- The fan triangle `conv {z, a, b}` over a straight frontier piece is the closed sector cut off
by `D`. -/
theorem u10h_mem_fan_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hab : 0 < det (a - z) (b - z)) (hseg : segment ℝ a b ⊆ frontier D) (x : Plane) :
    x ∈ convexHull ℝ {z, a, b} ↔ 0 ≤ det (a - z) (x - z) ∧ 0 ≤ det (x - z) (b - z) ∧ x ∈ D := by
  constructor
  · intro hx
    have hsub : convexHull ℝ {z, a, b} ⊆
        ({x | 0 ≤ det (a - z) (x - z)} ∩ {x | 0 ≤ det (x - z) (b - z)}) ∩ D := by
      apply convexHull_min
      · intro p hp
        simp only [mem_insert_iff, mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨⟨by simp [u10h_det_zero_right], by simp [u10h_det_zero_left]⟩, interior_subset hz⟩
        · exact ⟨⟨by simp [u10h_det_self], hab.le⟩,
            u10h_frontier_subset hD (hseg (left_mem_segment ℝ _ _))⟩
        · exact ⟨⟨hab.le, by simp [u10h_det_self]⟩,
            u10h_frontier_subset hD (hseg (right_mem_segment ℝ _ _))⟩
      · exact ((u10h_convex_det_nonneg z (a - z)).inter (u10h_convex_det_nonneg' z (b - z))).inter
          hD.convex
    obtain ⟨⟨h1, h2⟩, h3⟩ := hsub hx
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    by_cases hxz : x = z
    · subst hxz; exact subset_convexHull ℝ _ (mem_insert _ _)
    · have hyseg := u10h_ray_mem_segment hD hz hab hseg hxz h1 h2
      have hxeq := u10h_ray_spec hD hz hxz
      have hr1 : u10h_rg D z x ≤ 1 := (u10h_rg_le_one_iff hD hz x).mpr h3
      have hr0 := u10h_rg_nonneg D z x
      have hzmem : z ∈ convexHull ℝ {z, a, b} := subset_convexHull ℝ _ (mem_insert _ _)
      have hymem : u10h_ray D z x ∈ convexHull ℝ {z, a, b} :=
        segment_subset_convexHull (by simp) (by simp) hyseg
      have := (convex_convexHull ℝ {z, a, b}) hzmem hymem (sub_nonneg.mpr hr1) hr0 (by ring)
      rw [hxeq]
      convert this using 1
      rw [sub_smul, one_smul, smul_sub]; abel

/-! ### marks and adjacent pairs -/

/-- `(a, b)` is an adjacent pair of marks of `V`: a straight frontier piece seen counterclockwise
from `z` with no mark strictly inside. -/
def u10h_Adj (D : Set Plane) (z : Plane) (V : Set Plane) (a b : Plane) : Prop :=
  a ∈ V ∧ b ∈ V ∧ 0 < det (a - z) (b - z) ∧ segment ℝ a b ⊆ frontier D ∧
    ∀ c ∈ V, c ∉ openSegment ℝ a b

theorem u10h_openSegment_sub {a b y : Plane} (h : y ∈ openSegment ℝ a b) (z : Plane) :
    ∃ β γ : ℝ, 0 < β ∧ 0 < γ ∧ β + γ = 1 ∧ y - z = β • (a - z) + γ • (b - z) := by
  obtain ⟨β, γ, hβ, hγ, hβγ, rfl⟩ := h
  refine ⟨β, γ, hβ, hγ, hβγ, ?_⟩
  have hz' : z = β • z + γ • z := by rw [← add_smul, hβγ, one_smul]
  calc β • a + γ • b - z = β • a + γ • b - (β • z + γ • z) := by rw [← hz']
    _ = β • (a - z) + γ • (b - z) := by rw [smul_sub, smul_sub]; abel

theorem u10h_det_comb_right (u v w : Plane) (β γ : ℝ) :
    det u (β • v + γ • w) = β * det u v + γ * det u w := by
  rw [u10h_det_add_right, u10h_det_smul_right, u10h_det_smul_right]

theorem u10h_det_comb_left (u v w : Plane) (β γ : ℝ) :
    det (β • v + γ • w) u = β * det v u + γ * det w u := by
  rw [u10h_det_add_left, u10h_det_smul_left', u10h_det_smul_left']

theorem u10h_mem_segment_cases {a b y : Plane} (h : y ∈ segment ℝ a b) :
    y = a ∨ y = b ∨ y ∈ openSegment ℝ a b := by
  rw [← insert_endpoints_openSegment] at h
  simpa using h

/-- Where a mark can lie relative to an adjacent pair. -/
theorem u10h_adj_trichotomy {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b : Plane} (hab : u10h_Adj D z V a b) {c : Plane}
    (hc : c ∈ V) : c = a ∨ c = b ∨ det (a - z) (c - z) < 0 ∨ det (c - z) (b - z) < 0 := by
  rcases lt_or_ge (det (a - z) (c - z)) 0 with h1 | h1
  · exact Or.inr (Or.inr (Or.inl h1))
  rcases lt_or_ge (det (c - z) (b - z)) 0 with h2 | h2
  · exact Or.inr (Or.inr (Or.inr h2))
  have hcseg := u10h_frontier_mem_segment hD hz hab.2.2.1 hab.2.2.2.1 (hV hc) h1 h2
  rcases u10h_mem_segment_cases hcseg with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd h (hab.2.2.2.2 c hc)

theorem u10h_adj_unique_right {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b d : Plane} (hab : u10h_Adj D z V a b)
    (had : u10h_Adj D z V a d) : b = d := by
  rcases u10h_adj_trichotomy hD hz hV hab had.2.1 with h | h | h | h
  · exfalso; subst h; exact lt_irrefl (0:ℝ) (by simpa [u10h_det_self] using had.2.2.1)
  · exact h.symm
  · exfalso; linarith [had.2.2.1]
  · exfalso
    have hbd : 0 < det (b - z) (d - z) := by rw [u10h_det_swap']; linarith
    have hbseg := u10h_frontier_mem_segment hD hz had.2.2.1 had.2.2.2.1 (hV hab.2.1) hab.2.2.1.le hbd.le
    rcases u10h_mem_segment_cases hbseg with h1 | h1 | h1
    · subst h1; exact lt_irrefl (0:ℝ) (by simpa [u10h_det_self] using hab.2.2.1)
    · subst h1; simp [u10h_det_self] at hbd
    · exact had.2.2.2.2 b hab.2.1 h1

theorem u10h_adj_unique_left {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b c : Plane} (hab : u10h_Adj D z V a b)
    (hcb : u10h_Adj D z V c b) : a = c := by
  rcases u10h_adj_trichotomy hD hz hV hab hcb.1 with h | h | h | h
  · exact h.symm
  · exfalso; subst h; exact lt_irrefl (0:ℝ) (by simpa [u10h_det_self] using hcb.2.2.1)
  · exfalso
    have hca : 0 < det (c - z) (a - z) := by rw [u10h_det_swap']; linarith
    have haseg := u10h_frontier_mem_segment hD hz hcb.2.2.1 hcb.2.2.2.1 (hV hab.1) hca.le hab.2.2.1.le
    rcases u10h_mem_segment_cases haseg with h1 | h1 | h1
    · subst h1; simp [u10h_det_self] at hca
    · subst h1; exact lt_irrefl (0:ℝ) (by simpa [u10h_det_self] using hab.2.2.1)
    · exact hcb.2.2.2.2 a hab.1 h1
  · exfalso; linarith [hcb.2.2.1]

/-- A point in the open frontier pieces of two adjacent pairs forces the pairs to coincide. -/
theorem u10h_adj_eq_of_openSegment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b c d y : Plane} (hab : u10h_Adj D z V a b)
    (hcd : u10h_Adj D z V c d) (h1 : y ∈ openSegment ℝ a b) (h2 : y ∈ openSegment ℝ c d) :
    a = c ∧ b = d := by
  obtain ⟨β, γ, hβ, hγ, -, hY1⟩ := u10h_openSegment_sub h1 z
  obtain ⟨β', δ, hβ', hδ, -, hY2⟩ := u10h_openSegment_sub h2 z
  have dAB := hab.2.2.1
  have dCD := hcd.2.2.1
  have eAY : det (a - z) (y - z) = γ * det (a - z) (b - z) := by
    rw [hY1, u10h_det_comb_right, u10h_det_self]; ring
  have eBY : det (b - z) (y - z) = -(β * det (a - z) (b - z)) := by
    rw [hY1, u10h_det_comb_right, u10h_det_self, u10h_det_swap' (b - z) (a - z)]; ring
  have eCY : det (c - z) (y - z) = δ * det (c - z) (d - z) := by
    rw [hY2, u10h_det_comb_right, u10h_det_self]; ring
  have eYD : det (y - z) (d - z) = β' * det (c - z) (d - z) := by
    rw [hY2, u10h_det_comb_left, u10h_det_self]; ring
  have eAY' : det (a - z) (y - z) = β' * det (a - z) (c - z) + δ * det (a - z) (d - z) := by
    rw [hY2, u10h_det_comb_right]
  have eBY' : det (b - z) (y - z) = β' * det (b - z) (c - z) + δ * det (b - z) (d - z) := by
    rw [hY2, u10h_det_comb_right]
  have eYD' : det (y - z) (d - z) = β * det (a - z) (d - z) + γ * det (b - z) (d - z) := by
    rw [hY1, u10h_det_comb_left]
  rcases u10h_adj_trichotomy hD hz hV hab hcd.1 with hc | hc | hc | hc
  · -- c = a
    subst hc
    refine ⟨rfl, ?_⟩
    rcases u10h_adj_trichotomy hD hz hV hab hcd.2.1 with hd | hd | hd | hd
    · exfalso; subst hd
      have := hcd.2.2.1; rw [u10h_det_self] at this; exact lt_irrefl _ this
    · exact hd.symm
    · exfalso; linarith [hcd.2.2.1]
    · exfalso
      have hbd : 0 < det (b - z) (d - z) := by rw [u10h_det_swap']; linarith
      have hbseg := u10h_frontier_mem_segment hD hz hcd.2.2.1 hcd.2.2.2.1 (hV hab.2.1) dAB.le hbd.le
      rcases u10h_mem_segment_cases hbseg with h | h | h
      · subst h; rw [u10h_det_self] at dAB; exact lt_irrefl _ dAB
      · subst h; rw [u10h_det_self] at hbd; exact lt_irrefl _ hbd
      · exact hcd.2.2.2.2 b hab.2.1 h
  · -- c = b
    exfalso; subst hc
    have : 0 < det (c - z) (y - z) := by rw [eCY]; positivity
    rw [eBY] at this
    have := mul_pos hβ dAB; linarith
  · -- det (a-z) (c-z) < 0 : `a` lies strictly inside the sector `(c, d)`
    exfalso
    have hAD : 0 < det (a - z) (d - z) := by
      have h0 : 0 < δ * det (a - z) (d - z) := by
        have := mul_pos hγ dAB
        have := mul_neg_of_pos_of_neg hβ' hc
        linarith
      exact (mul_pos_iff_of_pos_left hδ).mp h0
    have hCA : 0 < det (c - z) (a - z) := by rw [u10h_det_swap']; linarith
    have haseg := u10h_frontier_mem_segment hD hz dCD hcd.2.2.2.1 (hV hab.1) hCA.le hAD.le
    rcases u10h_mem_segment_cases haseg with h | h | h
    · subst h; rw [u10h_det_self] at hCA; exact lt_irrefl _ hCA
    · subst h; rw [u10h_det_self] at hAD; exact lt_irrefl _ hAD
    · exact hcd.2.2.2.2 a hab.1 h
  · -- det (c-z) (b-z) < 0 : `d` lies strictly inside the sector `(a, b)`
    exfalso
    have hBC : 0 < det (b - z) (c - z) := by rw [u10h_det_swap']; linarith
    have hBD : det (b - z) (d - z) < 0 := by
      have h0 : δ * det (b - z) (d - z) < 0 := by
        have := mul_pos hβ dAB
        have := mul_pos hβ' hBC
        linarith
      rcases lt_or_ge (det (b - z) (d - z)) 0 with h | h
      · exact h
      · exfalso; linarith [mul_nonneg hδ.le h]
    have hAD : 0 < det (a - z) (d - z) := by
      have h0 : 0 < β * det (a - z) (d - z) := by
        have := mul_pos hβ' dCD
        have := mul_neg_of_pos_of_neg hγ hBD
        linarith
      exact (mul_pos_iff_of_pos_left hβ).mp h0
    have hDB : 0 < det (d - z) (b - z) := by rw [u10h_det_swap']; linarith
    have hdseg := u10h_frontier_mem_segment hD hz dAB hab.2.2.2.1 (hV hcd.2.1) hAD.le hDB.le
    rcases u10h_mem_segment_cases hdseg with h | h | h
    · subst h; rw [u10h_det_self] at hAD; exact lt_irrefl _ hAD
    · subst h; rw [u10h_det_self] at hDB; exact lt_irrefl _ hDB
    · exact hab.2.2.2.2 d hcd.2.1 h


theorem u10h_range_three (z a b : Plane) : range ![z, a, b] = {z, a, b} := by
  ext p
  simp only [mem_range, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨2, by simp⟩]

/-- The fan faces: one triangle `z a b` per pair with `A a b`. -/
def u10h_fanFaces (z : Plane) (A : Plane → Plane → Prop) : Set Triangle :=
  {T | ∃ a b, A a b ∧ T.v = ![z, a, b]}

theorem u10h_fanTri_mem {z a b : Plane} {A : Plane → Plane → Prop} (h : A a b)
    (hpos : 0 < det (a - z) (b - z)) :
    (⟨![z, a, b], by simpa using hpos⟩ : Triangle) ∈ u10h_fanFaces z A := ⟨a, b, h, rfl⟩

theorem u10h_carrier_of_v {T : Triangle} {z a b : Plane} (h : T.v = ![z, a, b]) :
    T.carrier = convexHull ℝ {z, a, b} := by
  rw [Triangle.carrier, h, u10h_range_three]

theorem u10h_inter_cases {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b c d y : Plane} (hab : u10h_Adj D z V a b)
    (hcd : u10h_Adj D z V c d) (hy1 : y ∈ segment ℝ a b) (hy2 : y ∈ segment ℝ c d) :
    (a = c ∧ b = d) ∨ (y = a ∧ a = d) ∨ (y = b ∧ b = c) := by
  rcases u10h_mem_segment_cases hy1 with h1 | h1 | h1 <;>
    rcases u10h_mem_segment_cases hy2 with h2 | h2 | h2
  · subst h1; exact Or.inl ⟨h2, u10h_adj_unique_right hD hz hV hab (h2 ▸ hcd)⟩
  · exact Or.inr (Or.inl ⟨h1, h1 ▸ h2⟩)
  · exact absurd (h1 ▸ h2) (hcd.2.2.2.2 a hab.1)
  · exact Or.inr (Or.inr ⟨h1, h1 ▸ h2⟩)
  · subst h1; exact Or.inl ⟨u10h_adj_unique_left hD hz hV hab (h2 ▸ hcd), h2⟩
  · exact absurd (h1 ▸ h2) (hcd.2.2.2.2 b hab.2.1)
  · exact absurd (h2 ▸ h1) (hab.2.2.2.2 c hcd.1)
  · exact absurd (h2 ▸ h1) (hab.2.2.2.2 d hcd.2.1)
  · exact Or.inl (u10h_adj_eq_of_openSegment hD hz hV hab hcd h1 h2)

theorem u10h_fan_subset {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hseg : segment ℝ a b ⊆ frontier D) : convexHull ℝ {z, a, b} ⊆ D := by
  apply convexHull_min _ hD.convex
  intro p hp
  simp only [mem_insert_iff, mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact interior_subset hz
  · exact u10h_frontier_subset hD (hseg (left_mem_segment ℝ _ _))
  · exact u10h_frontier_subset hD (hseg (right_mem_segment ℝ _ _))

theorem u10h_frontier_nonempty {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) :
    (frontier D).Nonempty :=
  ⟨u10h_ray D z (z + (1, 0)), u10h_ray_mem_frontier hD hz (by simp)⟩

theorem u10h_mem_segment_ray {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ∈ D) (hxz : x ≠ z) : x ∈ segment ℝ z (u10h_ray D z x) := by
  have hr0 := u10h_rg_nonneg D z x
  have hr1 := (u10h_rg_le_one_iff hD hz x).mpr hx
  refine ⟨1 - u10h_rg D z x, u10h_rg D z x, by linarith, hr0, by ring, ?_⟩
  have := u10h_ray_spec hD hz hxz
  rw [smul_sub] at this
  rw [sub_smul, one_smul]
  conv_rhs => rw [this]
  abel

/-- The fan from `z` over the adjacent pairs is a straight triangulation of `D`. -/
theorem u10h_fan_triangulation {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hVfin : V.Finite) (hV : V ⊆ frontier D) {A : Plane → Plane → Prop}
    (hA : ∀ a b, A a b → u10h_Adj D z V a b)
    (hcov : ∀ y ∈ frontier D, ∃ a b, A a b ∧ y ∈ segment ℝ a b) :
    ∃ K : Triangulation D, K.faces = u10h_fanFaces z A := by
  have hface : ∀ T ∈ u10h_fanFaces z A, ∃ a b, u10h_Adj D z V a b ∧ T.v 0 = z ∧ T.v 1 = a ∧
      T.v 2 = b ∧ T.carrier = convexHull ℝ {z, a, b} := by
    rintro T ⟨a, b, hab, hv⟩
    exact ⟨a, b, hA a b hab, by simp [hv], by simp [hv], by simp [hv], u10h_carrier_of_v hv⟩
  refine ⟨⟨u10h_fanFaces z A, ?_, ?_, ?_⟩, rfl⟩
  · -- finite
    apply Set.Finite.of_finite_image (f := fun T => (T.v 1, T.v 2))
    · refine (hVfin.prod hVfin).subset ?_
      rintro _ ⟨T, hT, rfl⟩
      obtain ⟨a, b, hab, -, h1, h2, -⟩ := hface T hT
      show T.v 1 ∈ V ∧ T.v 2 ∈ V
      rw [h1, h2]; exact ⟨hab.1, hab.2.1⟩
    · intro T hT T' hT' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨a, b, -, h0, -, -, -⟩ := hface T hT
      obtain ⟨c, d, -, h0', -, -, -⟩ := hface T' hT'
      have : T.v = T'.v := by
        funext i
        fin_cases i
        · simpa using h0.trans h0'.symm
        · exact h.1
        · exact h.2
      cases T; cases T'; simp only at this; subst this; rfl
  · -- cover
    apply Set.Subset.antisymm
    · intro x hx
      simp only [mem_iUnion, exists_prop] at hx
      obtain ⟨T, hT, hxT⟩ := hx
      obtain ⟨a, b, hab, -, -, -, hc⟩ := hface T hT
      rw [hc] at hxT
      exact u10h_fan_subset hD hz hab.2.2.2.1 hxT
    · intro x hx
      simp only [mem_iUnion, exists_prop]
      by_cases hxz : x = z
      · subst hxz
        obtain ⟨y0, hy0⟩ := u10h_frontier_nonempty hD hz
        obtain ⟨a, b, hab, -⟩ := hcov y0 hy0
        refine ⟨_, u10h_fanTri_mem hab (hA a b hab).2.2.1, ?_⟩
        rw [u10h_carrier_of_v rfl]
        exact subset_convexHull ℝ _ (mem_insert _ _)
      · obtain ⟨a, b, hab, hyab⟩ := hcov _ (u10h_ray_mem_frontier hD hz hxz)
        refine ⟨_, u10h_fanTri_mem hab (hA a b hab).2.2.1, ?_⟩
        rw [u10h_carrier_of_v rfl]
        have hzmem : z ∈ convexHull ℝ {z, a, b} := subset_convexHull ℝ _ (mem_insert _ _)
        have hymem : u10h_ray D z x ∈ convexHull ℝ {z, a, b} :=
          segment_subset_convexHull (by simp) (by simp) hyab
        exact (convex_convexHull ℝ _).segment_subset hzmem hymem (u10h_mem_segment_ray hD hz hx hxz)
  · -- inter
    intro T hT T' hT'
    obtain ⟨a, b, hab, h0, h1, h2, hc⟩ := hface T hT
    obtain ⟨c, d, hcd, h0', h1', h2', hc'⟩ := hface T' hT'
    have hrT : range T.v = {z, a, b} := by
      rw [← u10h_range_three]; congr 1; funext i; fin_cases i <;> simp [h0, h1, h2]
    have hrT' : range T'.v = {z, c, d} := by
      rw [← u10h_range_three]; congr 1; funext i; fin_cases i <;> simp [h0', h1', h2']
    rw [hc, hc', hrT, hrT']
    apply Set.Subset.antisymm
    · rintro x ⟨hx1, hx2⟩
      by_cases hxz : x = z
      · subst hxz
        exact subset_convexHull ℝ _ ⟨mem_insert _ _, mem_insert _ _⟩
      · have hx1' := (u10h_mem_fan_iff hD hz hab.2.2.1 hab.2.2.2.1 x).mp hx1
        have hx2' := (u10h_mem_fan_iff hD hz hcd.2.2.1 hcd.2.2.2.1 x).mp hx2
        have hy1 := u10h_ray_mem_segment hD hz hab.2.2.1 hab.2.2.2.1 hxz hx1'.1 hx1'.2.1
        have hy2 := u10h_ray_mem_segment hD hz hcd.2.2.1 hcd.2.2.2.1 hxz hx2'.1 hx2'.2.1
        have hxseg := u10h_mem_segment_ray hD hz hx1'.2.2 hxz
        rcases u10h_inter_cases hD hz hV hab hcd hy1 hy2 with ⟨rfl, rfl⟩ | ⟨hy, rfl⟩ | ⟨hy, rfl⟩
        · rw [inter_self]; exact hx1
        · rw [hy] at hxseg
          exact segment_subset_convexHull (s := {z, a, b} ∩ {z, c, a}) ⟨mem_insert _ _, mem_insert _ _⟩
            ⟨by simp, by simp⟩ hxseg
        · rw [hy] at hxseg
          exact segment_subset_convexHull (s := {z, a, b} ∩ {z, b, d}) ⟨mem_insert _ _, mem_insert _ _⟩
            ⟨by simp, by simp⟩ hxseg
    · exact subset_inter (convexHull_mono inter_subset_left) (convexHull_mono inter_subset_right)

/-! ### the cone map -/


/-- The linear map sending `p ↦ p'`, `q ↦ q'` (for `det p q ≠ 0`), written in `det` coordinates. -/
noncomputable def u10h_linOfDet (p q p' q' : Plane) : Plane →ₗ[ℝ] Plane where
  toFun v := (det v q / det p q) • p' + (det p v / det p q) • q'
  map_add' v w := by
    rw [u10h_det_add_left, u10h_det_add_right, add_div, add_div, add_smul, add_smul]; abel
  map_smul' c v := by
    simp only [RingHom.id_apply]
    rw [u10h_det_smul_left', u10h_det_smul_right, mul_div_assoc, mul_div_assoc, mul_smul, mul_smul,
      smul_add]

theorem u10h_linOfDet_apply (p q p' q' v : Plane) :
    u10h_linOfDet p q p' q' v = (det v q / det p q) • p' + (det p v / det p q) • q' := rfl

theorem u10h_linOfDet_left {p q : Plane} (h : det p q ≠ 0) (p' q' : Plane) :
    u10h_linOfDet p q p' q' p = p' := by
  rw [u10h_linOfDet_apply, div_self h, u10h_det_self, zero_div, one_smul, zero_smul, add_zero]

theorem u10h_linOfDet_right {p q : Plane} (h : det p q ≠ 0) (p' q' : Plane) :
    u10h_linOfDet p q p' q' q = q' := by
  rw [u10h_linOfDet_apply, div_self h, u10h_det_self, zero_div, one_smul, zero_smul, zero_add]

/-- The cone extension of a frontier map `β`: `z ↦ z'`, `z + t (y - z) ↦ z' + t (β y - z')` for
`y ∈ frontier D`, `0 ≤ t ≤ 1`. -/
noncomputable def u10h_cone (D : Set Plane) (z z' : Plane) (β : Plane → Plane) (x : Plane) : Plane :=
  z' + u10h_rg D z x • (β (u10h_ray D z x) - z')

theorem u10h_cone_center (D : Set Plane) (z z' : Plane) (β : Plane → Plane) :
    u10h_cone D z z' β z = z' := by
  simp [u10h_cone, u10h_rg_self]

theorem u10h_cone_frontier {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    (z' : Plane) (β : Plane → Plane) {y : Plane} (hy : y ∈ frontier D) :
    u10h_cone D z z' β y = β y := by
  rw [u10h_cone, u10h_ray_of_frontier hD hz hy, (u10h_rg_eq_one_iff hD hz y).mpr hy, one_smul,
    add_sub_cancel]

/-- The radial coordinate is preserved by the cone map (for `β` into `frontier D'`). -/
theorem u10h_rg_cone {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D') {z z' : Plane}
    (hz : z ∈ interior D) (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβ : ∀ y ∈ frontier D, β y ∈ frontier D') {x : Plane} (hxz : x ≠ z) :
    u10h_rg D' z' (u10h_cone D z z' β x) = u10h_rg D z x := by
  rw [u10h_cone, u10h_rg_smul D' z' _ (u10h_rg_nonneg D z x),
    (u10h_rg_eq_one_iff hD' hz' _).mpr (hβ _ (u10h_ray_mem_frontier hD hz hxz)), mul_one]

theorem u10h_cone_ray_formula {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    (z' : Plane) (β : Plane → Plane) {y : Plane} (hy : y ∈ frontier D) {t : ℝ} (ht : 0 < t) :
    u10h_cone D z z' β (z + t • (y - z)) = z' + t • (β y - z') := by
  have hyz := u10h_frontier_ne hD hz hy
  have hrg : u10h_rg D z (z + t • (y - z)) = t := by
    rw [u10h_rg_smul D z y ht.le, (u10h_rg_eq_one_iff hD hz y).mpr hy, mul_one]
  have hray : u10h_ray D z (z + t • (y - z)) = y := by
    rw [u10h_ray, hrg, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_sub_cancel]
  rw [u10h_cone, hrg, hray]

theorem u10h_combo_sub {s t : ℝ} (hst : s + t = 1) (a b z : Plane) :
    s • a + t • b - z = s • (a - z) + t • (b - z) := by
  have hz' : z = s • z + t • z := by rw [← add_smul, hst, one_smul]
  calc s • a + t • b - z = s • a + t • b - (s • z + t • z) := by rw [← hz']
    _ = s • (a - z) + t • (b - z) := by rw [smul_sub, smul_sub]; abel

/-- On a fan triangle over a piece where `β` is affine, the cone map is affine. -/
theorem u10h_cone_eq_on_fan {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    (z' : Plane) {β : Plane → Plane} {a b : Plane} (hab : 0 < det (a - z) (b - z))
    (hseg : segment ℝ a b ⊆ frontier D) (haff : AffineOn β (segment ℝ a b)) {x : Plane}
    (hx : x ∈ convexHull ℝ {z, a, b}) :
    u10h_cone D z z' β x = u10h_linOfDet (a - z) (b - z) (β a - z') (β b - z') (x - z) + z' := by
  by_cases hxz : x = z
  · subst hxz; simp [u10h_cone_center]
  · obtain ⟨M, c, hM⟩ := haff
    have hx' := (u10h_mem_fan_iff hD hz hab hseg x).mp hx
    have hyseg := u10h_ray_mem_segment hD hz hab hseg hxz hx'.1 hx'.2.1
    obtain ⟨s, t, hs, ht, hst, hy⟩ := id hyseg
    have hβy : β (u10h_ray D z x) - z' = s • (β a - z') + t • (β b - z') := by
      rw [hM _ hyseg, hM a (left_mem_segment ℝ a b), hM b (right_mem_segment ℝ a b), ← hy, map_add,
        map_smul, map_smul]
      have hc : c = s • c + t • c := by rw [← add_smul, hst, one_smul]
      have hz' : z' = s • z' + t • z' := by rw [← add_smul, hst, one_smul]
      calc s • M a + t • M b + c - z' = s • M a + t • M b + (s • c + t • c) - (s • z' + t • z') := by
            rw [← hc, ← hz']
        _ = s • (M a + c - z') + t • (M b + c - z') := by
            rw [smul_sub, smul_sub, smul_add, smul_add]; abel
    have hyz : u10h_ray D z x - z = s • (a - z) + t • (b - z) := by
      rw [← hy, u10h_combo_sub hst]
    have hxz' : x - z = u10h_rg D z x • (s • (a - z) + t • (b - z)) := by
      rw [← hyz]
      have := u10h_ray_spec hD hz hxz
      conv_lhs => rw [this]
      rw [add_sub_cancel_left]
    rw [u10h_cone, hβy, hxz', map_smul, map_add, map_smul, map_smul,
      u10h_linOfDet_left hab.ne', u10h_linOfDet_right hab.ne', add_comm]

/-- The cone map is positive PL on the fan triangulation. -/
theorem u10h_cone_isPositivePLOn {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    (z' : Plane) {V : Set Plane} {A : Plane → Plane → Prop} (hA : ∀ a b, A a b → u10h_Adj D z V a b)
    {β : Plane → Plane} (haff : ∀ a b, A a b → AffineOn β (segment ℝ a b))
    (hpos : ∀ a b, A a b → 0 < det (β a - z') (β b - z')) (K : Triangulation D)
    (hK : K.faces = u10h_fanFaces z A) : IsPositivePLOn (u10h_cone D z z' β) K := by
  intro T hT
  rw [hK] at hT
  obtain ⟨a, b, hab, hv⟩ := hT
  have hadj := hA a b hab
  have hc := u10h_carrier_of_v hv
  refine ⟨⟨u10h_linOfDet (a - z) (b - z) (β a - z') (β b - z'),
    z' - u10h_linOfDet (a - z) (b - z) (β a - z') (β b - z') z, ?_⟩, ?_⟩
  · intro x hx
    rw [hc] at hx
    rw [u10h_cone_eq_on_fan hD hz z' hadj.2.2.1 hadj.2.2.2.1 (haff a b hab) hx, map_sub]; abel
  · have h0 : T.v 0 = z := by simp [hv]
    have h1 : T.v 1 = a := by simp [hv]
    have h2 : T.v 2 = b := by simp [hv]
    rw [h0, h1, h2, u10h_cone_center,
      u10h_cone_frontier hD hz z' β (hadj.2.2.2.1 (left_mem_segment ℝ a b)),
      u10h_cone_frontier hD hz z' β (hadj.2.2.2.1 (right_mem_segment ℝ a b))]
    exact hpos a b hab

/-- The cone map is injective on `D`. -/
theorem u10h_cone_injOn {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D') {z z' : Plane}
    (hz : z ∈ interior D) (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβ : ∀ y ∈ frontier D, β y ∈ frontier D') (hinj : InjOn β (frontier D)) :
    InjOn (u10h_cone D z z' β) D := by
  have key : ∀ x, x ≠ z → u10h_cone D z z' β x ≠ z' := by
    intro x hx h
    have := u10h_rg_cone hD hD' hz hz' hβ hx
    rw [h, u10h_rg_self] at this
    exact u10h_rg_pos hD hz hx |>.ne this
  intro x₁ hx₁ x₂ hx₂ heq
  by_cases h₁ : x₁ = z
  · subst h₁
    by_contra h₂
    exact key x₂ (Ne.symm h₂) (heq.symm.trans (u10h_cone_center D x₁ z' β))
  by_cases h₂ : x₂ = z
  · subst h₂
    exact absurd (heq.trans (u10h_cone_center D x₂ z' β)) (key x₁ h₁)
  have hr : u10h_rg D z x₁ = u10h_rg D z x₂ := by
    rw [← u10h_rg_cone hD hD' hz hz' hβ h₁, ← u10h_rg_cone hD hD' hz hz' hβ h₂, heq]
  have hrpos := u10h_rg_pos hD hz h₁
  have hβeq : β (u10h_ray D z x₁) = β (u10h_ray D z x₂) := by
    unfold u10h_cone at heq
    rw [hr] at heq
    have := smul_right_injective Plane (hr ▸ hrpos).ne' (add_left_cancel heq)
    exact sub_left_injective this
  have hyeq := hinj (u10h_ray_mem_frontier hD hz h₁) (u10h_ray_mem_frontier hD hz h₂) hβeq
  rw [u10h_ray_spec hD hz h₁, u10h_ray_spec hD hz h₂, hr, hyeq]

/-- The cone map carries `D` onto `D'`. -/
theorem u10h_cone_image {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D') {z z' : Plane}
    (hz : z ∈ interior D) (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβ : ∀ y ∈ frontier D, β y ∈ frontier D') (hsurj : frontier D' ⊆ β '' frontier D) :
    u10h_cone D z z' β '' D = D' := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    by_cases hxz : x = z
    · subst hxz; rw [u10h_cone_center]; exact interior_subset hz'
    · have hr0 := u10h_rg_nonneg D z x
      have hr1 := (u10h_rg_le_one_iff hD hz x).mpr hx
      have hy := u10h_frontier_subset hD' (hβ _ (u10h_ray_mem_frontier hD hz hxz))
      have := hD'.convex (interior_subset hz') hy (sub_nonneg.mpr hr1) hr0 (by ring)
      convert this using 1
      rw [u10h_cone, sub_smul, one_smul, smul_sub]; abel
  · intro x' hx'
    by_cases hx'z : x' = z'
    · exact ⟨z, interior_subset hz, by rw [u10h_cone_center, hx'z]⟩
    · obtain ⟨y, hy, hyβ⟩ := hsurj (u10h_ray_mem_frontier hD' hz' hx'z)
      have hr := u10h_rg_pos hD' hz' hx'z
      have hr1 := (u10h_rg_le_one_iff hD' hz' x').mpr hx'
      refine ⟨z + u10h_rg D' z' x' • (y - z), ?_, ?_⟩
      · rw [← u10h_rg_le_one_iff hD hz, u10h_rg_smul D z y hr.le, (u10h_rg_eq_one_iff hD hz y).mpr hy,
          mul_one]
        exact hr1
      · rw [u10h_cone_ray_formula hD hz z' β hy hr, hyβ]
        exact (u10h_ray_spec hD' hz' hx'z).symm

/-! ### the marks of a finite frontier cover -/

theorem u10h_gap {M : Set ℝ} (hM : M.Finite) (h0 : (0:ℝ) ∈ M) (h1 : (1:ℝ) ∈ M) {θ₀ : ℝ}
    (hθ : θ₀ ∈ Icc (0:ℝ) 1) :
    ∃ θa ∈ M, ∃ θb ∈ M, θa < θb ∧ θa ≤ θ₀ ∧ θ₀ ≤ θb ∧ ∀ θ ∈ M, θa < θ → θ < θb → False := by
  classical
  rcases hθ.2.lt_or_eq with hlt | heq
  · set Fa := hM.toFinset.filter (fun θ => θ ≤ θ₀) with hFa
    set Fb := hM.toFinset.filter (fun θ => θ₀ < θ) with hFb
    have hane : Fa.Nonempty := ⟨0, by simp [hFa, h0, hθ.1]⟩
    have hbne : Fb.Nonempty := ⟨1, by simp [hFb, h1, hlt]⟩
    have hamem := Finset.max'_mem Fa hane
    have hbmem := Finset.min'_mem Fb hbne
    simp only [hFa, Finset.mem_filter, Set.Finite.mem_toFinset] at hamem
    simp only [hFb, Finset.mem_filter, Set.Finite.mem_toFinset] at hbmem
    refine ⟨_, hamem.1, _, hbmem.1, by linarith [hamem.2, hbmem.2], hamem.2, hbmem.2.le, ?_⟩
    intro θ hθM hlo hhi
    rcases le_or_gt θ θ₀ with h | h
    · have hmem : θ ∈ Fa := by simp [hFa, hθM, h]
      have := Finset.le_max' Fa θ hmem
      exact absurd hlo (not_lt.mpr this)
    · have hmem : θ ∈ Fb := by simp [hFb, hθM, h]
      have := Finset.min'_le Fb θ hmem
      exact absurd hhi (not_lt.mpr this)
  · subst heq
    set Fa := hM.toFinset.filter (fun θ => θ < 1) with hFa
    have hane : Fa.Nonempty := ⟨0, by simp [hFa, h0]⟩
    have hamem := Finset.max'_mem Fa hane
    simp only [hFa, Finset.mem_filter, Set.Finite.mem_toFinset] at hamem
    refine ⟨_, hamem.1, 1, h1, hamem.2, hamem.2.le, le_rfl, ?_⟩
    intro θ hθM hlo hhi
    have hmem : θ ∈ Fa := by simp [hFa, hθM, hhi]
    have := Finset.le_max' Fa θ hmem
    exact absurd hlo (not_lt.mpr this)

/-- The marks: all endpoints of the segments of `S`. -/
noncomputable def u10h_marks (S : Finset (Plane × Plane)) : Set Plane :=
  ↑(S.image Prod.fst ∪ S.image Prod.snd)

theorem u10h_marks_finite (S : Finset (Plane × Plane)) : (u10h_marks S).Finite := Finset.finite_toSet _

theorem u10h_marks_left {S : Finset (Plane × Plane)} {p : Plane × Plane} (hp : p ∈ S) :
    p.1 ∈ u10h_marks S := by
  simp only [u10h_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
  exact Or.inl ⟨p, hp, rfl⟩

theorem u10h_marks_right {S : Finset (Plane × Plane)} {p : Plane × Plane} (hp : p ∈ S) :
    p.2 ∈ u10h_marks S := by
  simp only [u10h_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
  exact Or.inr ⟨p, hp, rfl⟩

theorem u10h_marks_subset_frontier {D : Set Plane} {S : Finset (Plane × Plane)}
    (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) : u10h_marks S ⊆ frontier D := by
  intro c hc
  simp only [u10h_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image,
    Finset.mem_coe] at hc
  rw [← hS]
  rcases hc with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact mem_iUnion₂.mpr ⟨p, hp, left_mem_segment ℝ _ _⟩
  · exact mem_iUnion₂.mpr ⟨p, hp, right_mem_segment ℝ _ _⟩

/-- The adjacent pairs actually used: adjacent marks lying in one segment of `S`. -/
def u10h_A (D : Set Plane) (z : Plane) (S : Finset (Plane × Plane)) (a b : Plane) : Prop :=
  u10h_Adj D z (u10h_marks S) a b ∧ ∃ p ∈ S, segment ℝ a b ⊆ segment ℝ p.1 p.2

theorem u10h_cover_of_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {p : Plane × Plane}
    (hp : p ∈ S) (hne : p.1 ≠ p.2) {y : Plane} (hy : y ∈ segment ℝ p.1 p.2) :
    ∃ a b, u10h_A D z S a b ∧ y ∈ segment ℝ a b := by
  have he : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hne.symm
  set f : ℝ → Plane := fun θ => p.1 + θ • (p.2 - p.1) with hf
  have hfinj : Function.Injective f := fun θ₁ θ₂ h => smul_left_injective ℝ he (add_left_cancel h)
  have hsegp : segment ℝ p.1 p.2 = f '' Icc 0 1 := segment_eq_image' ℝ p.1 p.2
  have hsegfr : segment ℝ p.1 p.2 ⊆ frontier D := hS ▸ subset_iUnion₂ (s := fun p _ => segment ℝ p.1 p.2) p hp
  set M : Set ℝ := f ⁻¹' u10h_marks S ∩ Icc 0 1 with hM
  have hMfin : M.Finite := ((u10h_marks_finite S).preimage hfinj.injOn).subset inter_subset_left
  have h0M : (0:ℝ) ∈ M := ⟨by simp [f, u10h_marks_left hp], by simp⟩
  have h1M : (1:ℝ) ∈ M := ⟨by simp [f, u10h_marks_right hp], by simp⟩
  rw [hsegp] at hy
  obtain ⟨θ₀, hθ₀, rfl⟩ := hy
  obtain ⟨θa, haM, θb, hbM, hlt, hle1, hle2, hgap⟩ := u10h_gap hMfin h0M h1M hθ₀
  have haV : f θa ∈ u10h_marks S := haM.1
  have hbV : f θb ∈ u10h_marks S := hbM.1
  have hap : f θa ∈ segment ℝ p.1 p.2 := hsegp ▸ ⟨θa, haM.2, rfl⟩
  have hbp : f θb ∈ segment ℝ p.1 p.2 := hsegp ▸ ⟨θb, hbM.2, rfl⟩
  have hsub : segment ℝ (f θa) (f θb) ⊆ segment ℝ p.1 p.2 := (convex_segment _ _).segment_subset hap hbp
  have hsegab : segment ℝ (f θa) (f θb) ⊆ frontier D := hsub.trans hsegfr
  have hneab : f θa ≠ f θb := fun h => hlt.ne (hfinj h)
  have hcomb : ∀ lam : ℝ, f θa + lam • (f θb - f θa) = f (θa + lam * (θb - θa)) := by
    intro lam
    simp only [hf]
    ext <;> simp <;> ring
  have hnomark : ∀ c ∈ u10h_marks S, c ∉ openSegment ℝ (f θa) (f θb) := by
    intro c hc hco
    rw [openSegment_eq_image'] at hco
    obtain ⟨lam, hlam, rfl⟩ := hco
    beta_reduce at hc
    rw [hcomb] at hc
    have hθc : θa + lam * (θb - θa) ∈ M := by
      refine ⟨hc, ?_, ?_⟩
      · nlinarith [haM.2.1, hlam.1.le, hlt.le]
      · nlinarith [hbM.2.2, hlam.2.le, hlt.le]
    exact hgap _ hθc (by nlinarith [hlam.1]) (by nlinarith [hlam.2])
  have hyab : f θ₀ ∈ segment ℝ (f θa) (f θb) := by
    rw [segment_eq_image']
    refine ⟨(θ₀ - θa) / (θb - θa), ⟨div_nonneg (by linarith) (by linarith),
      div_le_one_of_le₀ (by linarith) (by linarith)⟩, ?_⟩
    beta_reduce
    rw [hcomb]
    congr 1
    have hba : θb - θa ≠ 0 := by linarith
    field_simp
    ring
  have hdet := u10h_det_ne_zero_of_segment hD hz hneab hsegab
  rcases hdet.lt_or_gt with hneg | hpos
  · refine ⟨f θb, f θa, ⟨⟨hbV, haV, by rw [u10h_det_swap']; linarith, by rw [segment_symm]; exact hsegab,
      fun c hc => by rw [openSegment_symm]; exact hnomark c hc⟩, p, hp, by rw [segment_symm]; exact hsub⟩,
      by rw [segment_symm]; exact hyab⟩
  · exact ⟨f θa, f θb, ⟨⟨haV, hbV, hpos, hsegab, hnomark⟩, p, hp, hsub⟩, hyab⟩

/-! ### frontier points are not isolated; a nondegenerate segment through each -/

theorem u10h_ray_continuousAt {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ≠ z) : ContinuousAt (u10h_ray D z) x := by
  have : u10h_ray D z = fun x => z + (u10h_rg D z x)⁻¹ • (x - z) := rfl
  rw [this]
  exact continuousAt_const.add
    ((((u10h_rg_continuous hD hz).continuousAt).inv₀ (u10h_rg_pos hD hz hx).ne').smul
      (continuousAt_id.sub continuousAt_const))

theorem u10h_not_isolated {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {y : Plane} (hy : y ∈ frontier D) {ε : ℝ} (hε : 0 < ε) :
    ∃ w ∈ frontier D, w ≠ y ∧ dist w y < ε := by
  have hyz := u10h_frontier_ne hD hz hy
  have hu : y - z ≠ 0 := sub_ne_zero.mpr hyz
  set v : Plane := (-(y - z).2, (y - z).1) with hv
  have hdet : 0 < det (y - z) v := by
    have : det (y - z) v = (y - z).1 ^ 2 + (y - z).2 ^ 2 := by simp only [det, hv]; ring
    rw [this]
    rcases not_and_or.mp (fun hc : (y - z).1 = 0 ∧ (y - z).2 = 0 => hu (Prod.ext hc.1 hc.2)) with h1 | h2 <;>
      positivity
  set g : ℝ → Plane := fun t => u10h_ray D z (y + t • v) with hg
  have hg0 : g 0 = y := by simp [hg, u10h_ray_of_frontier hD hz hy]
  have hgc : ContinuousAt g 0 := by
    have h1 : ContinuousAt (fun t : ℝ => y + t • v) 0 := continuousAt_const.add (continuousAt_id.smul continuousAt_const)
    have h2 : ContinuousAt (u10h_ray D z) (y + (0:ℝ) • v) := by
      rw [zero_smul, add_zero]; exact u10h_ray_continuousAt hD hz hyz
    exact ContinuousAt.comp (f := fun t : ℝ => y + t • v) h2 h1
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.mp hgc ε hε
  have hpt : y + (δ / 2) • v ≠ z := by
    intro h
    have : det (y - z) (y + (δ / 2) • v - z) = 0 := by rw [h, sub_self, u10h_det_zero_right]
    rw [add_sub_right_comm, u10h_det_add_right, u10h_det_self, u10h_det_smul_right] at this
    have : 0 < δ / 2 * det (y - z) v := by positivity
    linarith
  refine ⟨g (δ / 2), u10h_ray_mem_frontier hD hz hpt, ?_, ?_⟩
  · intro h
    have h1 : det (y - z) (g (δ / 2) - z) = 0 := by rw [h, u10h_det_self]
    have h2 : g (δ / 2) - z = (u10h_rg D z (y + (δ / 2) • v))⁻¹ • ((δ / 2) • v + (y - z)) := by
      simp only [hg, u10h_ray, add_sub_cancel_left]; congr 1; abel
    rw [h2, u10h_det_smul_right, u10h_det_add_right, u10h_det_smul_right, u10h_det_self, add_zero] at h1
    have hr := u10h_rg_pos hD hz hpt
    have : 0 < (u10h_rg D z (y + (δ / 2) • v))⁻¹ * (δ / 2 * det (y - z) v) := by positivity
    linarith
  · have := hδε (x := δ / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
    rwa [hg0] at this

theorem u10h_isClosed_segment (a b : Plane) : IsClosed (segment ℝ a b) := by
  rw [segment_eq_image']
  exact (isCompact_Icc.image (by fun_prop)).isClosed

theorem u10h_exists_nondeg {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {y : Plane}
    (hy : y ∈ frontier D) : ∃ p ∈ S, p.1 ≠ p.2 ∧ y ∈ segment ℝ p.1 p.2 := by
  classical
  by_contra hcon
  have hdeg : ∀ p ∈ S, y ∈ segment ℝ p.1 p.2 → p.1 = p.2 := fun p hp hyp =>
    by_contra fun hne => hcon ⟨p, hp, hne, hyp⟩
  set U : Set Plane := ⋃ p ∈ S.filter (fun p => y ∉ segment ℝ p.1 p.2), segment ℝ p.1 p.2 with hU
  have hUc : IsClosed U := isClosed_biUnion_finset (fun p _ => u10h_isClosed_segment _ _)
  have hyU : y ∉ U := by
    intro h
    rw [hU, mem_iUnion₂] at h
    obtain ⟨p, hp, hyp⟩ := h
    exact (Finset.mem_filter.mp hp).2 hyp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUc.isOpen_compl y hyU
  obtain ⟨w, hw, hwy, hwd⟩ := u10h_not_isolated hD hz hy hε
  rw [← hS, mem_iUnion₂] at hw
  obtain ⟨p, hp, hwp⟩ := hw
  by_cases hyp : y ∈ segment ℝ p.1 p.2
  · have h12 := hdeg p hp hyp
    rw [h12, segment_same] at hyp hwp
    exact hwy (hwp.trans hyp.symm)
  · have hwU : w ∈ U := by
      rw [hU, mem_iUnion₂]
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, hyp⟩, hwp⟩
    exact hball (Metric.mem_ball.mpr hwd) hwU

/-! ### coverage, a third mark, positivity from the cyclic order -/

theorem u10h_cover {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {y : Plane}
    (hy : y ∈ frontier D) : ∃ a b, u10h_A D z S a b ∧ y ∈ segment ℝ a b := by
  obtain ⟨p, hp, hne, hyp⟩ := u10h_exists_nondeg hD hz hS hy
  exact u10h_cover_of_segment hD hz hS hp hne hyp

theorem u10h_det_neg_right (u v : Plane) : det u (-v) = -det u v := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

theorem u10h_affine_combo {β : Plane → Plane} {M : Plane →ₗ[ℝ] Plane} {c a b : Plane}
    (hM : ∀ x ∈ segment ℝ a b, β x = M x + c) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    β (s • a + t • b) = s • β a + t • β b := by
  rw [hM _ ⟨s, t, hs, ht, hst, rfl⟩, hM a (left_mem_segment ℝ a b), hM b (right_mem_segment ℝ a b),
    map_add, map_smul, map_smul, smul_add, smul_add]
  have hc : c = s • c + t • c := by rw [← add_smul, hst, one_smul]
  conv_lhs => rw [hc]
  abel

theorem u10h_affine_image_segment {β : Plane → Plane} {a b : Plane} (h : AffineOn β (segment ℝ a b)) :
    β '' segment ℝ a b = segment ℝ (β a) (β b) := by
  obtain ⟨M, c, hM⟩ := h
  ext w
  constructor
  · rintro ⟨x, ⟨s, t, hs, ht, hst, rfl⟩, rfl⟩
    exact ⟨s, t, hs, ht, hst, (u10h_affine_combo hM hs ht hst).symm⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨s • a + t • b, ⟨s, t, hs, ht, hst, rfl⟩, u10h_affine_combo hM hs ht hst⟩

theorem u10h_third_mark {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {a b : Plane}
    (hab : u10h_A D z S a b) : ∃ c ∈ u10h_marks S, c ≠ a ∧ c ≠ b := by
  have hadj := hab.1
  have hV := u10h_marks_subset_frontier hS
  have haz : a - z ≠ 0 := sub_ne_zero.mpr (u10h_frontier_ne hD hz (hV hadj.1))
  have hxz : z - (a - z) ≠ z := by
    intro h; apply haz; have := congrArg (fun w => z - w) h; simpa using this
  set y := u10h_ray D z (z - (a - z)) with hy_def
  have hy : y ∈ frontier D := u10h_ray_mem_frontier hD hz hxz
  have hyz' : y - z = (u10h_rg D z (z - (a - z)))⁻¹ • (-(a - z)) := by
    rw [hy_def, u10h_ray, add_sub_cancel_left]; congr 1; abel
  obtain ⟨c, d, hcd, hycd⟩ := u10h_cover hD hz hS hy
  have hynot : y ∉ segment ℝ a b := by
    rintro ⟨s, t, hs, ht, hst, hy'⟩
    have hyz : y - z = s • (a - z) + t • (b - z) := by rw [← hy', u10h_combo_sub hst]
    have h1 : det (a - z) (y - z) = t * det (a - z) (b - z) := by
      rw [hyz, u10h_det_comb_right, u10h_det_self]; ring
    have h2 : det (a - z) (y - z) = 0 := by
      rw [hyz', u10h_det_smul_right, u10h_det_neg_right, u10h_det_self]; ring
    have ht0 : t = 0 := (mul_eq_zero.mp (h1.symm.trans h2)).resolve_right hadj.2.2.1.ne'
    have hs1 : s = 1 := by linarith
    rw [ht0, hs1, one_smul, zero_smul, add_zero] at hy'
    rw [← hy', smul_neg] at hyz'
    have h3 : (1 + (u10h_rg D z (z - (a - z)))⁻¹) • (a - z) = 0 := by
      rw [add_smul, one_smul]
      nth_rewrite 1 [hyz']
      abel
    rcases smul_eq_zero.mp h3 with h | h
    · have := u10h_rg_pos hD hz hxz
      have : 0 < 1 + (u10h_rg D z (z - (a - z)))⁻¹ := by positivity
      linarith
    · exact haz h
  by_contra hcon
  have hall : ∀ c ∈ u10h_marks S, c = a ∨ c = b := by
    intro c hc
    by_contra h
    exact hcon ⟨c, hc, fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩
  have hsub : segment ℝ c d ⊆ segment ℝ a b := by
    rcases hall c hcd.1.1 with rfl | rfl <;> rcases hall d hcd.1.2.1 with rfl | rfl
    · rw [segment_same]; exact singleton_subset_iff.mpr (left_mem_segment ℝ _ _)
    · exact le_rfl
    · rw [segment_symm]
    · rw [segment_same]; exact singleton_subset_iff.mpr (right_mem_segment ℝ _ _)
  exact hynot (hsub hycd)


theorem u10h_pos_of_preserves {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    {z z' : Plane} (hz : z ∈ interior D) (hz' : z' ∈ interior D') {S : Finset (Plane × Plane)}
    (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {β : Plane → Plane}
    (hβmap : ∀ y ∈ frontier D, β y ∈ frontier D') (hinj : InjOn β (frontier D))
    (haffS : ∀ p ∈ S, AffineOn β (segment ℝ p.1 p.2)) (hpos : PreservesCyclicPos D z z' β)
    {a b : Plane} (hab : u10h_A D z S a b) : 0 < det (β a - z') (β b - z') := by
  obtain ⟨hadj, p, hp, hsub⟩ := hab
  have hV := u10h_marks_subset_frontier hS
  have haff : AffineOn β (segment ℝ a b) := by
    obtain ⟨M, c, hM⟩ := haffS p hp
    exact ⟨M, c, fun x hx => hM x (hsub hx)⟩
  have himg := u10h_affine_image_segment haff
  have hseg' : segment ℝ (β a) (β b) ⊆ frontier D' := by
    rw [← himg]; rintro _ ⟨w, hw, rfl⟩; exact hβmap w (hadj.2.2.2.1 hw)
  have hane : a ≠ b := by
    intro h; have := hadj.2.2.1; rw [h, u10h_det_self] at this; exact lt_irrefl _ this
  have hane' : β a ≠ β b := fun h => hane (hinj (hV hadj.1) (hV hadj.2.1) h)
  have hdet' := u10h_det_ne_zero_of_segment hD' hz' hane' hseg'
  rcases hdet'.lt_or_gt with hneg | hpos'
  · exfalso
    obtain ⟨c, hcV, hca, hcb⟩ := u10h_third_mark hD hz hS ⟨hadj, p, hp, hsub⟩
    have hcyc : CyclicPos z a b c := by
      rcases u10h_adj_trichotomy hD hz hV hadj hcV with h | h | h | h
      · exact absurd h hca
      · exact absurd h hcb
      · exact Or.inr (Or.inr ⟨by rw [u10h_det_swap']; linarith, hadj.2.2.1⟩)
      · exact Or.inl ⟨hadj.2.2.1, by rw [u10h_det_swap']; linarith⟩
    have hcyc' := hpos a (hV hadj.1) b (hV hadj.2.1) c (hV hcV) hcyc
    have hba' : 0 < det (β b - z') (β a - z') := by rw [u10h_det_swap']; linarith
    rcases hcyc' with ⟨h1, -⟩ | ⟨h1, h2⟩ | ⟨-, h2⟩
    · linarith
    · have hsegba : segment ℝ (β b) (β a) ⊆ frontier D' := by rw [segment_symm]; exact hseg'
      have hmem := u10h_frontier_mem_segment hD' hz' hba' hsegba (hβmap c (hV hcV)) h1.le h2.le
      rw [segment_symm, ← himg] at hmem
      obtain ⟨w, hw, hwc⟩ := hmem
      have hwc' : w = c := hinj (hadj.2.2.2.1 hw) (hV hcV) hwc
      subst hwc'
      rcases u10h_mem_segment_cases hw with h | h | h
      · exact hca h
      · exact hcb h
      · exact hadj.2.2.2.2 w hcV h
    · linarith
  · exact hpos'

/-- U10 (sm-3:535-537, the fan extension on convex models): a finite positive PL homeomorphism
between the boundaries of two convex discs, preserving the cyclic order around interior points
`z ↦ z'`, extends to a positive PL homeomorphism of the discs (cone from `z` to `z'`). -/
theorem U10_fan_extension {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    {z z' : Plane} (hz : z ∈ interior D) (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβ : IsHomeoOnto (frontier D) (frontier D') β) (hpl : IsFinitePLOnFrontier D β)
    (hpos : PreservesCyclicPos D z z' β) :
    ∃ (K : Triangulation D) (F : Plane → Plane), IsPositivePLOn F K ∧ IsHomeoOnto D D' F ∧
      ∀ x ∈ frontier D, F x = β x := by
  obtain ⟨e, he⟩ := hβ
  have hβmap : ∀ y ∈ frontier D, β y ∈ frontier D' := by
    intro y hy; have := (e ⟨y, hy⟩).2; rwa [he] at this
  have hinj : InjOn β (frontier D) := by
    intro y₁ h₁ y₂ h₂ heq
    have : e ⟨y₁, h₁⟩ = e ⟨y₂, h₂⟩ := Subtype.ext (by rw [he, he]; exact heq)
    exact congrArg Subtype.val (e.injective this)
  have hsurj : frontier D' ⊆ β '' frontier D := by
    intro w hw
    refine ⟨e.symm ⟨w, hw⟩, (e.symm ⟨w, hw⟩).2, ?_⟩
    rw [← he]; simp
  obtain ⟨S, hS, haffS⟩ := hpl
  have hV := u10h_marks_subset_frontier hS
  have hA : ∀ a b, u10h_A D z S a b → u10h_Adj D z (u10h_marks S) a b := fun a b h => h.1
  have hcov : ∀ y ∈ frontier D, ∃ a b, u10h_A D z S a b ∧ y ∈ segment ℝ a b :=
    fun y hy => u10h_cover hD hz hS hy
  obtain ⟨K, hK⟩ := u10h_fan_triangulation hD hz (u10h_marks_finite S) hV hA hcov
  have haff : ∀ a b, u10h_A D z S a b → AffineOn β (segment ℝ a b) := by
    rintro a b ⟨-, p, hp, hsub⟩
    obtain ⟨M, c, hM⟩ := haffS p hp
    exact ⟨M, c, fun x hx => hM x (hsub hx)⟩
  have hposdet : ∀ a b, u10h_A D z S a b → 0 < det (β a - z') (β b - z') :=
    fun a b h => u10h_pos_of_preserves hD hD' hz hz' hS hβmap hinj haffS hpos h
  have hPL := u10h_cone_isPositivePLOn hD hz z' hA haff hposdet K hK
  refine ⟨K, u10h_cone D z z' β, hPL, ?_, fun x hx => u10h_cone_frontier hD hz z' β hx⟩
  have := U2_isHomeoOnto_of_isPositivePLOn K hPL (u10h_cone_injOn hD hD' hz hz' hβmap hinj)
  rwa [u10h_cone_image hD hD' hz hz' hβmap hsurj] at this

/-! #### U10 helpers for `U10_boundary_map_of_lift` (circle in the closure, periodicity, the lift) -/

theorem u10h_coe_traversal_mem_circle [NeZero n] (P : LabelledTuple n) (x : ℝ) :
    ((traversal P x : Plane) : Sphere) ∈ sphereCircle P :=
  ⟨traversal P x, by rw [← U4_range_traversal P]; exact mem_range_self x, rfl⟩

/-! ### CyclicPos: rotation, antisymmetry, totality on a convex frontier -/

theorem u10h_cyclicPos_rotate {z a b c : Plane} (h : CyclicPos z a b c) : CyclicPos z b c a := by
  unfold CyclicPos at *; tauto

theorem u10h_cyclicPos_antisymm {z a b c : Plane} (h1 : CyclicPos z a b c) (h2 : CyclicPos z a c b) :
    False := by
  unfold CyclicPos at *
  have e1 := u10h_det_swap' (a - z) (b - z)
  have e2 := u10h_det_swap' (b - z) (c - z)
  have e3 := u10h_det_swap' (c - z) (a - z)
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith

theorem u10h_cyclicPos_ne {z a b c : Plane} (h : CyclicPos z a b c) : a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> unfold CyclicPos at h
  · have := u10h_det_self (a - z); have := u10h_det_swap' (a - z) (c - z)
    rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  · have := u10h_det_self (b - z); have := u10h_det_swap' (a - z) (b - z)
    rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  · have := u10h_det_self (a - z); have := u10h_det_swap' (a - z) (b - z)
    rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith

theorem u10h_eq_of_ray {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {p r : Plane} (hp : p ∈ frontier D) (hr : r ∈ frontier D) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : r - z = μ • (p - z)) : r = p := by
  have hr' : r = z + μ • (p - z) := by rw [← h]; abel
  have h1 := (u10h_rg_eq_one_iff hD hz r).mpr hr
  rw [hr', u10h_rg_smul D z p hμ, (u10h_rg_eq_one_iff hD hz p).mpr hp, mul_one] at h1
  rw [hr', h1, one_smul, add_sub_cancel]

theorem u10h_antipodal {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {p q : Plane} (hp : p ∈ frontier D) (hq : q ∈ frontier D) (hne : q ≠ p)
    (h0 : det (p - z) (q - z) = 0) : ∃ lam : ℝ, 0 < lam ∧ q - z = -(lam • (p - z)) := by
  obtain ⟨μ, hμ⟩ := u10h_parallel_of_det_eq_zero (sub_ne_zero.mpr (u10h_frontier_ne hD hz hp)) h0
  rcases le_or_gt 0 μ with hμ0 | hμ0
  · exact absurd (u10h_eq_of_ray hD hz hp hq hμ0 hμ) hne
  · exact ⟨-μ, by linarith, by rw [hμ, neg_smul, neg_neg]⟩

theorem u10h_det_prod_pos {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {p q r : Plane} (hp : p ∈ frontier D) (hq : q ∈ frontier D) (hr : r ∈ frontier D) (hqp : q ≠ p)
    (hrp : r ≠ p) (hrq : r ≠ q) (h0 : det (p - z) (q - z) = 0) :
    0 < det (q - z) (r - z) * det (r - z) (p - z) := by
  obtain ⟨lam, hlam, hq'⟩ := u10h_antipodal hD hz hp hq hqp h0
  have e : det (q - z) (r - z) = lam * det (r - z) (p - z) := by
    rw [hq', ← neg_smul, u10h_det_smul_left', u10h_det_swap' (p - z) (r - z)]; ring
  rw [e, mul_assoc]
  have hne : det (r - z) (p - z) ≠ 0 := by
    intro h
    have h' : det (p - z) (r - z) = 0 := by rw [u10h_det_swap']; linarith
    obtain ⟨μ, hμ⟩ := u10h_parallel_of_det_eq_zero (sub_ne_zero.mpr (u10h_frontier_ne hD hz hp)) h'
    rcases le_or_gt 0 μ with hμ0 | hμ0
    · exact hrp (u10h_eq_of_ray hD hz hp hr hμ0 hμ)
    · apply hrq
      refine u10h_eq_of_ray hD hz hq hr (μ := -μ / lam) (div_nonneg (by linarith) hlam.le) ?_
      rw [hμ, hq', smul_neg, smul_smul]
      have : -μ / lam * lam = -μ := div_mul_cancel₀ _ hlam.ne'
      rw [this, neg_smul, neg_neg]
  have : 0 < det (r - z) (p - z) * det (r - z) (p - z) := mul_self_pos.mpr hne
  positivity

theorem u10h_cyclicPos_total {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {p q r : Plane} (hp : p ∈ frontier D) (hq : q ∈ frontier D) (hr : r ∈ frontier D) (hpq : p ≠ q)
    (hqr : q ≠ r) (hpr : p ≠ r) : CyclicPos z p q r ∨ CyclicPos z p r q := by
  have e1 := u10h_det_swap' (q - z) (p - z)
  have e2 := u10h_det_swap' (r - z) (q - z)
  have e3 := u10h_det_swap' (p - z) (r - z)
  unfold CyclicPos
  by_cases hA : det (p - z) (q - z) = 0
  · have := u10h_det_prod_pos hD hz hp hq hr hpq.symm hpr.symm hqr.symm hA
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos this with ⟨hB, hC⟩ | ⟨hB, hC⟩
    · exact Or.inl (Or.inr (Or.inl ⟨hB, hC⟩))
    · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
  by_cases hB : det (q - z) (r - z) = 0
  · have := u10h_det_prod_pos hD hz hq hr hp hqr.symm hpq hpr hB
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos this with ⟨hC, hA'⟩ | ⟨hC, hA'⟩
    · exact Or.inl (Or.inr (Or.inr ⟨hC, hA'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
  by_cases hC : det (r - z) (p - z) = 0
  · have := u10h_det_prod_pos hD hz hr hp hq hpr hqr hpq.symm hC
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos this with ⟨hA', hB'⟩ | ⟨hA', hB'⟩
    · exact Or.inl (Or.inl ⟨hA', hB'⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
  rcases lt_or_gt_of_ne hA with hA | hA <;> rcases lt_or_gt_of_ne hB with hB | hB <;>
    rcases lt_or_gt_of_ne hC with hC | hC <;>
    first
    | exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inl (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact Or.inl (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))

/-! ### abstract refinement of finite interval covers -/

/-- `g : ℝ → Plane` is affine on `I`. -/
def u10h_AffOn (g : ℝ → Plane) (I : Set ℝ) : Prop := ∃ p u : Plane, ∀ t ∈ I, g t = p + t • u

theorem u10h_AffOn_mono {g : ℝ → Plane} {I J : Set ℝ} (h : u10h_AffOn g I) (hJ : J ⊆ I) :
    u10h_AffOn g J := by
  obtain ⟨p, u, h⟩ := h; exact ⟨p, u, fun t ht => h t (hJ ht)⟩

theorem u10h_gap' {B : Set ℝ} (hB : B.Finite) {lo hi : ℝ} (hlo : lo ∈ B) (hhi : hi ∈ B)
    (hlh : lo < hi) {t : ℝ} (ht : t ∈ Icc lo hi) :
    ∃ b ∈ B, ∃ b' ∈ B, b < b' ∧ b ≤ t ∧ t ≤ b' ∧ ∀ a ∈ B, b < a → a < b' → False := by
  classical
  rcases ht.2.lt_or_eq with hlt | heq
  · set Fa := hB.toFinset.filter (fun θ => θ ≤ t) with hFa
    set Fb := hB.toFinset.filter (fun θ => t < θ) with hFb
    have hane : Fa.Nonempty := ⟨lo, by simp [hFa, hlo, ht.1]⟩
    have hbne : Fb.Nonempty := ⟨hi, by simp [hFb, hhi, hlt]⟩
    have hamem := Finset.max'_mem Fa hane
    have hbmem := Finset.min'_mem Fb hbne
    simp only [hFa, Finset.mem_filter, Set.Finite.mem_toFinset] at hamem
    simp only [hFb, Finset.mem_filter, Set.Finite.mem_toFinset] at hbmem
    refine ⟨_, hamem.1, _, hbmem.1, by linarith [hamem.2, hbmem.2], hamem.2, hbmem.2.le, ?_⟩
    intro θ hθM hlo' hhi'
    rcases le_or_gt θ t with h | h
    · have hmem : θ ∈ Fa := by simp [hFa, hθM, h]
      exact absurd hlo' (not_lt.mpr (Finset.le_max' Fa θ hmem))
    · have hmem : θ ∈ Fb := by simp [hFb, hθM, h]
      exact absurd hhi' (not_lt.mpr (Finset.min'_le Fb θ hmem))
  · subst heq
    set Fa := hB.toFinset.filter (fun θ => θ < t) with hFa
    have hane : Fa.Nonempty := ⟨lo, by simp [hFa, hlo, hlh]⟩
    have hamem := Finset.max'_mem Fa hane
    simp only [hFa, Finset.mem_filter, Set.Finite.mem_toFinset] at hamem
    refine ⟨_, hamem.1, t, hhi, hamem.2, hamem.2.le, le_rfl, ?_⟩
    intro θ hθM hlo' hhi'
    have hmem : θ ∈ Fa := by simp [hFa, hθM, hhi']
    exact absurd hlo' (not_lt.mpr (Finset.le_max' Fa θ hmem))

/-- Midpoint argument: an interval with no breakpoint strictly inside lies in one covering piece. -/
theorem u10h_subset_piece {B : Set ℝ} {C : Set (ℝ × ℝ)} (hCB : ∀ c ∈ C, c.1 ∈ B ∧ c.2 ∈ B) {lo hi : ℝ}
    (hcov : ∀ t ∈ Icc lo hi, ∃ c ∈ C, t ∈ Icc c.1 c.2) {b b' : ℝ} (hb : lo ≤ b) (hb' : b' ≤ hi)
    (hlt : b < b') (hgap : ∀ a ∈ B, b < a → a < b' → False) : ∃ c ∈ C, Icc b b' ⊆ Icc c.1 c.2 := by
  obtain ⟨c, hc, hm⟩ := hcov ((b + b') / 2) ⟨by linarith, by linarith⟩
  refine ⟨c, hc, Icc_subset_Icc ?_ ?_⟩
  · rcases le_or_gt c.1 b with h | h
    · exact h
    · exact absurd (hgap c.1 (hCB c hc).1 h (by linarith [hm.1])) id
  · rcases le_or_gt b' c.2 with h | h
    · exact h
    · exact absurd (hgap c.2 (hCB c hc).2 (by linarith [hm.2]) h) id

/-- The linear map `w ↦ (⟪w, u⟫ / ⟪u, u⟫) • u''`. -/
noncomputable def u10h_dotLin (u u'' : Plane) : Plane →ₗ[ℝ] Plane where
  toFun w := (planeDot w u / planeDot u u) • u''
  map_add' v w := by
    have : planeDot (v + w) u = planeDot v u + planeDot w u := by
      simp only [planeDot, Prod.fst_add, Prod.snd_add]; ring
    rw [this, add_div, add_smul]
  map_smul' c w := by
    have : planeDot (c • w) u = c * planeDot w u := by
      simp only [planeDot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    simp only [RingHom.id_apply]
    rw [this, mul_div_assoc, mul_smul]

theorem u10h_planeDot_self_pos {u : Plane} (hu : u ≠ 0) : 0 < planeDot u u := by
  have : planeDot u u = u.1 ^ 2 + u.2 ^ 2 := by simp only [planeDot]; ring
  rw [this]
  rcases not_and_or.mp (fun hc : u.1 = 0 ∧ u.2 = 0 => hu (Prod.ext hc.1 hc.2)) with h1 | h2 <;>
    positivity

theorem u10h_planeDot_add_smul (p u : Plane) (t : ℝ) :
    planeDot (p + t • u) u = planeDot p u + t * planeDot u u := by
  simp only [planeDot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- A map that is affine in the parameter of an affinely parametrised segment is affine on it. -/
theorem u10h_affineOn_of_param {β : Plane → Plane} {c : ℝ → Plane} {b b' : ℝ} {p u p'' u'' : Plane}
    (hc : ∀ t ∈ Icc b b', c t = p + t • u) (hβ : ∀ t ∈ Icc b b', β (c t) = p'' + t • u'')
    (hbb : b ≤ b') : AffineOn β (c '' Icc b b') := by
  by_cases hu : u = 0
  · refine ⟨0, p'' + b • u'', ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have : c t = c b := by rw [hc t ht, hc b ⟨le_rfl, hbb⟩, hu, smul_zero, smul_zero]
    rw [this, hβ b ⟨le_rfl, hbb⟩, LinearMap.zero_apply, zero_add]
  · have hpos := u10h_planeDot_self_pos hu
    refine ⟨u10h_dotLin u u'', p'' - (planeDot p u / planeDot u u) • u'', ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    rw [hβ t ht]
    have : u10h_dotLin u u'' (c t) = (planeDot p u / planeDot u u) • u'' + t • u'' := by
      change (planeDot (c t) u / planeDot u u) • u'' = _
      rw [hc t ht, u10h_planeDot_add_smul, add_div, mul_div_assoc, div_self hpos.ne', mul_one, add_smul]
    rw [this]; abel

theorem u10h_image_Icc_eq_segment {c : ℝ → Plane} {b b' : ℝ} {p u : Plane}
    (hc : ∀ t ∈ Icc b b', c t = p + t • u) (hbb : b ≤ b') :
    c '' Icc b b' = segment ℝ (c b) (c b') := by
  rw [segment_eq_image']
  ext w
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases hbb.lt_or_eq with hlt | heq
    · refine ⟨(t - b) / (b' - b), ⟨div_nonneg (by linarith [ht.1]) (by linarith),
        div_le_one_of_le₀ (by linarith [ht.2]) (by linarith)⟩, ?_⟩
      rw [hc t ht, hc b ⟨le_rfl, hbb⟩, hc b' ⟨hbb, le_rfl⟩]
      have hne : b' - b ≠ 0 := by linarith
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; field_simp; ring
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; field_simp; ring
    · subst heq
      have : t = b := le_antisymm ht.2 ht.1
      subst this
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨b + θ * (b' - b), ⟨by nlinarith [hθ.1], by nlinarith [hθ.2]⟩, ?_⟩
    rw [hc _ ⟨by nlinarith [hθ.1], by nlinarith [hθ.2]⟩, hc b ⟨le_rfl, hbb⟩, hc b' ⟨hbb, le_rfl⟩]
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; ring
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; ring

theorem u10h_circle_subset_closure [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (s : Side) {L : ℝ} (hL : InsideModel L P) : sphereCircle P ⊆ closure (regionOf P s) := by
  obtain ⟨A⟩ := U6_exists_ambientParam hn P hP hL
  have hcl : IsClosed A.T₀.carrier := by
    show IsClosed (convexHull ℝ (range A.T₀.v))
    exact ((Set.finite_range A.T₀.v).isCompact_convexHull ℝ).isClosed
  cases s with
  | inner =>
    show sphereCircle P ⊆ closure (interiorRegion P)
    rw [U7_closure_interiorRegion_eq hn P hP A]
    rintro _ ⟨w, hw, rfl⟩
    rw [← A.boundary] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨A.H v, ⟨v, hcl.frontier_subset hv, rfl⟩, rfl⟩
  | outer =>
    show sphereCircle P ⊆ closure (exteriorRegion P)
    rw [U8_closure_exteriorRegion_eq hn P hP A]
    rintro _ ⟨w, hw, rfl⟩ ⟨_, ⟨v, hv, rfl⟩, hvw⟩
    rw [← A.boundary] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    have : v = u := A.H.injective (OnePoint.coe_eq_coe.mp hvw)
    subst this
    exact hu.2 hv

theorem u10h_traversal_add_int_mul [NeZero n] (P : LabelledTuple n) (x : ℝ) (m : ℤ) :
    traversal P (x + m * n) = traversal P x := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [show x + ((k : ℝ) + 1) * n = (x + k * n) + n by ring, traversal_add_nat, ih]
  | pred k ih =>
    push_cast at ih ⊢
    have := traversal_add_nat P (x + (-(k : ℝ) - 1) * n)
    rw [show x + (-(k : ℝ) - 1) * n + n = x + -(k : ℝ) * n by ring] at this
    rw [← this, ih]

theorem u10h_lift_shift_same {n n' : ℕ} {φ : ℝ → ℝ} (h : ∀ x, φ (x + n) = φ x + n') (x : ℝ) (m : ℤ) :
    φ (x + m * n) = φ x + m * n' := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [show x + ((k : ℝ) + 1) * n = (x + k * n) + n by ring, h, ih]; ring
  | pred k ih =>
    push_cast at ih ⊢
    have := h (x + (-(k : ℝ) - 1) * n)
    rw [show x + (-(k : ℝ) - 1) * n + n = x + -(k : ℝ) * n by ring, ih] at this
    linarith

theorem u10h_lift_shift_opp {n n' : ℕ} {φ : ℝ → ℝ} (h : ∀ x, φ (x + n) = φ x - n') (x : ℝ) (m : ℤ) :
    φ (x + m * n) = φ x - m * n' := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [show x + ((k : ℝ) + 1) * n = (x + k * n) + n by ring, h, ih]; ring
  | pred k ih =>
    push_cast at ih ⊢
    have := h (x + (-(k : ℝ) - 1) * n)
    rw [show x + (-(k : ℝ) - 1) * n + n = x + -(k : ℝ) * n by ring, ih] at this
    linarith

theorem u10h_isHomeoOnto_injOn {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {S : Set α}
    {S' : Set β} {f : α → β} (h : IsHomeoOnto S S' f) : InjOn f S := by
  obtain ⟨e, he⟩ := h
  intro x hx y hy hxy
  have : e ⟨x, hx⟩ = e ⟨y, hy⟩ := Subtype.ext (by rw [he, he]; exact hxy)
  exact congrArg Subtype.val (e.injective this)

/-- Two parameters give the same point of the parametrised frontier iff they differ by a multiple
of the period. -/
theorem u10h_param_eq_iff [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P) {s : Side}
    {D : Set Plane} {f : Sphere → Plane} (hf : IsHomeoOnto (closure (regionOf P s)) D f)
    (hBS : sphereCircle P ⊆ closure (regionOf P s)) (x y : ℝ) :
    f ((traversal P x : Plane) : Sphere) = f ((traversal P y : Plane) : Sphere) ↔
      ∃ m : ℤ, y = x + m * n := by
  constructor
  · intro h
    have h1 := u10h_isHomeoOnto_injOn hf (hBS (u10h_coe_traversal_mem_circle P x))
      (hBS (u10h_coe_traversal_mem_circle P y)) h
    exact hP.traversal_injective hn (OnePoint.coe_eq_coe.mp h1)
  · rintro ⟨m, rfl⟩
    rw [u10h_traversal_add_int_mul]

theorem u10h_reduce {n : ℕ} (hn : 0 < n) (x : ℝ) : ∃ x₀ ∈ Ico (0:ℝ) n, ∃ m : ℤ, x = x₀ + m * n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  refine ⟨x - ⌊x / n⌋ * n, ⟨?_, ?_⟩, ⌊x / n⌋, by ring⟩
  · have := Int.floor_le (x / n)
    have : (⌊x / n⌋ : ℝ) * n ≤ x / n * n := by nlinarith
    rw [div_mul_cancel₀ _ hn'.ne'] at this
    linarith
  · have := Int.lt_floor_add_one (x / n)
    have : x / n * n < ((⌊x / n⌋ : ℝ) + 1) * n := by nlinarith
    rw [div_mul_cancel₀ _ hn'.ne'] at this
    linarith

/-- A positive boundary lift is onto. -/
theorem u10h_lift_surj [NeZero n] {n' : ℕ} [NeZero n'] {P : LabelledTuple n} {s : Side}
    {P' : LabelledTuple n'} {s' : Side} {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    Function.Surjective φ := by
  have hn : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hn' : (0:ℝ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  intro v
  by_cases hsame : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
  · obtain ⟨-, hper⟩ := hφ.same hsame
    obtain ⟨m₁, hm₁⟩ := exists_int_lt ((v - φ 0) / n')
    obtain ⟨m₂, hm₂⟩ := exists_int_gt ((v - φ 0) / n')
    have h1 : φ (m₁ * n) ≤ v := by
      have := u10h_lift_shift_same hper 0 m₁; rw [zero_add] at this; rw [this]
      have : (m₁ : ℝ) * n' < v - φ 0 := by rwa [lt_div_iff₀ hn'] at hm₁
      linarith
    have h2 : v ≤ φ (m₂ * n) := by
      have := u10h_lift_shift_same hper 0 m₂; rw [zero_add] at this; rw [this]
      have : v - φ 0 < (m₂ : ℝ) * n' := by rwa [div_lt_iff₀ hn'] at hm₂
      linarith
    have hm : (m₁ : ℝ) * n ≤ m₂ * n := by
      have : (m₁ : ℝ) < m₂ := by linarith
      nlinarith
    obtain ⟨x, -, hx⟩ := intermediate_value_Icc hm hφ.continuous.continuousOn ⟨h1, h2⟩
    exact ⟨x, hx⟩
  · obtain ⟨-, hper⟩ := hφ.opposite hsame
    obtain ⟨m₁, hm₁⟩ := exists_int_lt ((φ 0 - v) / n')
    obtain ⟨m₂, hm₂⟩ := exists_int_gt ((φ 0 - v) / n')
    have h1 : v ≤ φ (m₁ * n) := by
      have := u10h_lift_shift_opp hper 0 m₁; rw [zero_add] at this; rw [this]
      have : (m₁ : ℝ) * n' < φ 0 - v := by rwa [lt_div_iff₀ hn'] at hm₁
      linarith
    have h2 : φ (m₂ * n) ≤ v := by
      have := u10h_lift_shift_opp hper 0 m₂; rw [zero_add] at this; rw [this]
      have : φ 0 - v < (m₂ : ℝ) * n' := by rwa [div_lt_iff₀ hn'] at hm₂
      linarith
    have hm : (m₁ : ℝ) * n ≤ m₂ * n := by
      have : (m₁ : ℝ) < m₂ := by linarith
      nlinarith
    obtain ⟨x, -, hx⟩ := intermediate_value_Icc' hm hφ.continuous.continuousOn ⟨h2, h1⟩
    exact ⟨x, hx⟩

/-- The parameter set of edge piece `[k, k+1]` inside a face `T`. -/
def u10h_J [NeZero n] (P : LabelledTuple n) (k : ℤ) (T : Triangle) : Set ℝ :=
  {t | t ∈ Icc (k : ℝ) (k + 1) ∧ traversal P t ∈ T.carrier}

theorem u10h_J_ordConnected [NeZero n] (P : LabelledTuple n) (k : ℤ) (T : Triangle) :
    (u10h_J P k T).OrdConnected := by
  refine ⟨fun t₁ h₁ t₂ h₂ t ht => ⟨⟨by linarith [h₁.1.1, ht.1], by linarith [h₂.1.2, ht.2]⟩, ?_⟩⟩
  have hconv : Convex ℝ T.carrier := convex_convexHull ℝ _
  have e1 := ea_traversal_eq_on_Icc P k h₁.1.1 h₁.1.2
  have e2 := ea_traversal_eq_on_Icc P k h₂.1.1 h₂.1.2
  have e := ea_traversal_eq_on_Icc P k (by linarith [h₁.1.1, ht.1] : (k:ℝ) ≤ t)
    (by linarith [h₂.1.2, ht.2] : t ≤ k + 1)
  rcases (ht.1.trans ht.2).lt_or_eq with hlt | heq
  · have hmem : traversal P t ∈ segment ℝ (traversal P t₁) (traversal P t₂) := by
      rw [segment_eq_image']
      refine ⟨(t - t₁) / (t₂ - t₁), ⟨div_nonneg (by linarith [ht.1]) (by linarith),
        div_le_one_of_le₀ (by linarith [ht.2]) (by linarith)⟩, ?_⟩
      rw [e1, e2, e]
      have hne : t₂ - t₁ ≠ 0 := by linarith
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; field_simp; ring
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; field_simp; ring
    exact hconv.segment_subset h₁.2 h₂.2 hmem
  · have : t = t₁ := le_antisymm (heq ▸ ht.2) ht.1
    rw [this]; exact h₁.2

theorem u10h_J_isCompact [NeZero n] (P : LabelledTuple n) (k : ℤ) (T : Triangle) :
    IsCompact (u10h_J P k T) := by
  have hT : IsClosed T.carrier := by
    show IsClosed (convexHull ℝ (range T.v))
    exact ((Set.finite_range T.v).isCompact_convexHull ℝ).isClosed
  exact isCompact_Icc.of_isClosed_subset (isClosed_Icc.inter (hT.preimage (continuous_traversal P)))
    (fun t ht => ht.1)

theorem u10h_J_eq_Icc [NeZero n] (P : LabelledTuple n) (k : ℤ) (T : Triangle)
    (hne : (u10h_J P k T).Nonempty) :
    u10h_J P k T = Icc (sInf (u10h_J P k T)) (sSup (u10h_J P k T)) :=
  eq_Icc_of_connected_compact ⟨hne, (u10h_J_ordConnected P k T).isPreconnected⟩ (u10h_J_isCompact P k T)

theorem u10h_modelChart_false (L : ℝ) (x : Plane) : modelChart L false x = (x : Sphere) := rfl

/-- On a piece, `f ∘ ↑ ∘ traversal` is affine in the parameter. -/
theorem u10h_affOn_J [NeZero n] (P : LabelledTuple n) {L : ℝ} {S : Set Sphere} {f : Sphere → Plane}
    {K : Triangulation (chartPart L false S)} (hK : IsPositivePLOn (f ∘ modelChart L false) K)
    (k : ℤ) {T : Triangle} (hT : T ∈ K.faces) :
    u10h_AffOn (fun t => f ((traversal P t : Plane) : Sphere)) (u10h_J P k T) := by
  obtain ⟨M, b₀, hM⟩ := (hK T hT).1
  refine ⟨M (P (k : ZMod n)) - (k : ℝ) • M (edge P (k : ZMod n)) + b₀, M (edge P (k : ZMod n)), ?_⟩
  intro t ht
  have := hM _ ht.2
  simp only [Function.comp, u10h_modelChart_false] at this
  show f ((traversal P t : Plane) : Sphere) = _
  rw [this, ea_traversal_eq_on_Icc P k ht.1.1 ht.1.2, map_add, map_smul]
  simp only [sub_smul]
  abel

theorem u10h_supNorm_combo {x y : Plane} {L a b : ℝ} (hx : supNorm x ≤ L) (hy : supNorm y ≤ L)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : supNorm (a • x + b • y) ≤ L := by
  have h1 : |x.1| ≤ L := le_trans (le_max_left _ _) hx
  have h2 : |x.2| ≤ L := le_trans (le_max_right _ _) hx
  have h3 : |y.1| ≤ L := le_trans (le_max_left _ _) hy
  have h4 : |y.2| ≤ L := le_trans (le_max_right _ _) hy
  unfold supNorm
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  apply max_le
  · calc |a * x.1 + b * y.1| ≤ |a * x.1| + |b * y.1| := abs_add_le _ _
      _ = a * |x.1| + b * |y.1| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * L + b * L := by gcongr
      _ = L := by rw [← add_mul, hab, one_mul]
  · calc |a * x.2 + b * y.2| ≤ |a * x.2| + |b * y.2| := abs_add_le _ _
      _ = a * |x.2| + b * |y.2| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * L + b * L := by gcongr
      _ = L := by rw [← add_mul, hab, one_mul]

/-- Every traversal point lies in the plane chart part of the closed region. -/
theorem u10h_traversal_mem_chartPart [NeZero n] (P : LabelledTuple n) {L : ℝ} (hL : InsideModel L P)
    {S : Set Sphere} (hBS : sphereCircle P ⊆ S) (t : ℝ) :
    traversal P t ∈ chartPart L false S := by
  refine ⟨?_, hBS (u10h_coe_traversal_mem_circle P t)⟩
  show supNorm (traversal P t) ≤ L
  have h0 : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
  have h1 : t ≤ ⌊t⌋ + 1 := (Int.lt_floor_add_one t).le
  rw [ea_traversal_eq_on_Icc P ⌊t⌋ h0 h1, edge]
  have : P (⌊t⌋ : ZMod n) + (t - ⌊t⌋) • (P ((⌊t⌋ : ZMod n) + 1) - P (⌊t⌋ : ZMod n)) =
      (1 - (t - ⌊t⌋)) • P (⌊t⌋ : ZMod n) + (t - ⌊t⌋) • P ((⌊t⌋ : ZMod n) + 1) := by
    simp only [sub_smul, one_smul, smul_sub]; abel
  rw [this]
  exact u10h_supNorm_combo (hL _).le (hL _).le (by linarith) (by linarith) (by ring)

/-- The P-side pieces: one parameter interval per edge `k < n` and face `T` meeting it. -/
def u10h_pieceSet [NeZero n] (P : LabelledTuple n) (K : Set Triangle) : Set (ℝ × ℝ) :=
  {c | ∃ k : ℕ, k < n ∧ ∃ T ∈ K, (u10h_J P k T).Nonempty ∧ c = (sInf (u10h_J P k T), sSup (u10h_J P k T))}

theorem u10h_pieceSet_finite [NeZero n] (P : LabelledTuple n) {K : Set Triangle} (hK : K.Finite) :
    (u10h_pieceSet P K).Finite := by
  have : u10h_pieceSet P K ⊆
      (fun q : ℕ × Triangle => (sInf (u10h_J P q.1 q.2), sSup (u10h_J P q.1 q.2))) ''
        ({k | k < n} ×ˢ K) := by
    rintro c ⟨k, hk, T, hT, -, rfl⟩
    exact ⟨(k, T), ⟨hk, hT⟩, rfl⟩
  exact ((Set.finite_lt_nat n).prod hK).image _ |>.subset this

theorem u10h_pieceSet_affOn [NeZero n] (P : LabelledTuple n) {L : ℝ} {S : Set Sphere}
    {f : Sphere → Plane} {K : Triangulation (chartPart L false S)}
    (hK : IsPositivePLOn (f ∘ modelChart L false) K) {c : ℝ × ℝ} (hc : c ∈ u10h_pieceSet P K.faces) :
    u10h_AffOn (fun t => f ((traversal P t : Plane) : Sphere)) (Icc c.1 c.2) := by
  obtain ⟨k, -, T, hT, hne, rfl⟩ := hc
  have := u10h_affOn_J P hK k hT
  rwa [u10h_J_eq_Icc P k T hne] at this

theorem u10h_pieceSet_cover [NeZero n] (P : LabelledTuple n) {L : ℝ} (hL : InsideModel L P)
    {S : Set Sphere} (hBS : sphereCircle P ⊆ S) (K : Triangulation (chartPart L false S)) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) n) : ∃ c ∈ u10h_pieceSet P K.faces, t ∈ Icc c.1 c.2 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  -- choose the edge index
  obtain ⟨k, hk, hkt⟩ : ∃ k : ℕ, k < n ∧ t ∈ Icc (k : ℝ) (k + 1) := by
    rcases ht.2.lt_or_eq with hlt | heq
    · refine ⟨⌊t⌋.toNat, ?_, ?_⟩
      · have h1 : ⌊t⌋ < n := Int.floor_lt.mpr hlt
        have h2 : (0:ℤ) ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht.1
        omega
      · have h2 : (0:ℤ) ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht.1
        have : ((⌊t⌋.toNat : ℤ) : ℝ) = (⌊t⌋ : ℝ) := by rw [Int.toNat_of_nonneg h2]
        push_cast at this
        rw [this]
        exact ⟨Int.floor_le t, (Int.lt_floor_add_one t).le⟩
    · refine ⟨n - 1, by omega, ?_⟩
      have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [this, heq]
      constructor <;> linarith
  have hmem := u10h_traversal_mem_chartPart P hL hBS t
  rw [← K.cover, mem_iUnion₂] at hmem
  obtain ⟨T, hT, hTt⟩ := hmem
  have hJ : t ∈ u10h_J P k T := ⟨by exact_mod_cast hkt, hTt⟩
  refine ⟨(sInf (u10h_J P k T), sSup (u10h_J P k T)), ⟨k, hk, T, hT, ⟨t, hJ⟩, rfl⟩, ?_⟩
  have := u10h_J_eq_Icc P k T ⟨t, hJ⟩
  rw [← this]; exact hJ

/-- The P′-side pieces pulled back through `φ`: parameters `t ∈ [lo, hi]` with `φ t` in the `m`-th
translate of the edge piece `[k', k'+1]` and `traversal P' (φ t)` in the face `T'`. -/
def u10h_J' {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (φ : ℝ → ℝ) (lo hi : ℝ) (k' m : ℤ)
    (T' : Triangle) : Set ℝ :=
  Icc lo hi ∩ φ ⁻¹' ((fun u => u - m * n') ⁻¹' u10h_J P' k' T')

theorem u10h_J'_ordConnected {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') {φ : ℝ → ℝ}
    (hφ : Monotone φ ∨ Antitone φ) (lo hi : ℝ) (k' m : ℤ) (T' : Triangle) :
    (u10h_J' P' φ lo hi k' m T').OrdConnected := by
  have hg : Monotone (fun u : ℝ => u - m * n') := fun a b h => sub_le_sub_right h _
  have h1 := (u10h_J_ordConnected P' k' T').preimage_mono hg
  rcases hφ with hφ | hφ
  · exact ordConnected_Icc.inter (h1.preimage_mono hφ)
  · exact ordConnected_Icc.inter (h1.preimage_anti hφ)

theorem u10h_J'_isCompact {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') {φ : ℝ → ℝ} (hφ : Continuous φ)
    (lo hi : ℝ) (k' m : ℤ) (T' : Triangle) : IsCompact (u10h_J' P' φ lo hi k' m T') := by
  have hcl : IsClosed ((fun u : ℝ => u - m * n') ⁻¹' u10h_J P' k' T') :=
    (u10h_J_isCompact P' k' T').isClosed.preimage (continuous_id.sub continuous_const)
  exact isCompact_Icc.of_isClosed_subset (isClosed_Icc.inter (hcl.preimage hφ)) inter_subset_left

theorem u10h_J'_eq_Icc {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ : Monotone φ ∨ Antitone φ) (lo hi : ℝ) (k' m : ℤ) (T' : Triangle)
    (hne : (u10h_J' P' φ lo hi k' m T').Nonempty) :
    u10h_J' P' φ lo hi k' m T' = Icc (sInf (u10h_J' P' φ lo hi k' m T')) (sSup (u10h_J' P' φ lo hi k' m T')) :=
  eq_Icc_of_connected_compact ⟨hne, (u10h_J'_ordConnected P' hφ lo hi k' m T').isPreconnected⟩
    (u10h_J'_isCompact P' hφc lo hi k' m T')

/-- On a P′-piece, `f' ∘ ↑ ∘ traversal P' ∘ φ` is affine in `φ t`. -/
theorem u10h_affOn_J' {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (φ : ℝ → ℝ) (lo hi : ℝ) {L' : ℝ}
    {S' : Set Sphere} {f' : Sphere → Plane} {K' : Triangulation (chartPart L' false S')}
    (hK' : IsPositivePLOn (f' ∘ modelChart L' false) K') (k' m : ℤ) {T' : Triangle} (hT' : T' ∈ K'.faces) :
    ∃ p'' u'' : Plane, ∀ t ∈ u10h_J' P' φ lo hi k' m T',
      f' ((traversal P' (φ t) : Plane) : Sphere) = p'' + φ t • u'' := by
  obtain ⟨M, b₀, hM⟩ := (hK' T' hT').1
  refine ⟨M (P' (k' : ZMod n')) - ((m : ℝ) * n' + k') • M (edge P' (k' : ZMod n')) + b₀,
    M (edge P' (k' : ZMod n')), ?_⟩
  rintro t ⟨-, ht⟩
  change (φ t - m * n') ∈ Icc (k' : ℝ) (k' + 1) ∧ traversal P' (φ t - m * n') ∈ T'.carrier at ht
  have hper : traversal P' (φ t) = traversal P' (φ t - m * n') := by
    have := u10h_traversal_add_int_mul P' (φ t - m * n') m
    rwa [sub_add_cancel] at this
  have := hM _ ht.2
  simp only [Function.comp, u10h_modelChart_false] at this
  rw [hper, this, ea_traversal_eq_on_Icc P' k' ht.1.1 ht.1.2, map_add, map_smul]
  simp only [sub_smul, add_smul]
  abel

theorem u10h_J'_cover {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (φ : ℝ → ℝ) (lo hi : ℝ) {L' : ℝ}
    (hL' : InsideModel L' P') {S' : Set Sphere} (hBS' : sphereCircle P' ⊆ S')
    (K' : Triangulation (chartPart L' false S')) {t : ℝ} (ht : t ∈ Icc lo hi) :
    ∃ k' m : ℤ, 0 ≤ k' ∧ k' < n' ∧ ∃ T' ∈ K'.faces, t ∈ u10h_J' P' φ lo hi k' m T' := by
  have hn' : (0:ℝ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  obtain ⟨v, hv, m, hvm⟩ := u10h_reduce (Nat.pos_of_ne_zero (NeZero.ne n')) (φ t)
  have hv' : φ t - m * n' = v := by linarith
  refine ⟨⌊v⌋, m, Int.floor_nonneg.mpr hv.1, ?_, ?_⟩
  · have : (⌊v⌋ : ℝ) < n' := by linarith [Int.floor_le v, hv.2]
    exact_mod_cast this
  · have hmem := u10h_traversal_mem_chartPart P' hL' hBS' v
    rw [← K'.cover, mem_iUnion₂] at hmem
    obtain ⟨T', hT', hTv⟩ := hmem
    refine ⟨T', hT', ht, ?_⟩
    change (φ t - m * n') ∈ Icc (⌊v⌋ : ℝ) (⌊v⌋ + 1) ∧ traversal P' (φ t - m * n') ∈ T'.carrier
    rw [hv']
    exact ⟨⟨Int.floor_le v, (Int.lt_floor_add_one v).le⟩, hTv⟩

/-- The P′-side piece set (endpoints of the nonempty pieces, `0 ≤ k' < n'`). -/
def u10h_pieceSet' {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (φ : ℝ → ℝ) (lo hi : ℝ)
    (K' : Set Triangle) : Set (ℝ × ℝ) :=
  {c | ∃ k' m : ℤ, 0 ≤ k' ∧ k' < n' ∧ ∃ T' ∈ K', (u10h_J' P' φ lo hi k' m T').Nonempty ∧
    c = (sInf (u10h_J' P' φ lo hi k' m T'), sSup (u10h_J' P' φ lo hi k' m T'))}

theorem u10h_pieceSet'_finite {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') {φ : ℝ → ℝ}
    (hφ : Monotone φ ∨ Antitone φ) (lo hi : ℝ) {K' : Set Triangle} (hK' : K'.Finite) :
    (u10h_pieceSet' P' φ lo hi K').Finite := by
  have hn' : (0:ℝ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  set A := min (φ lo) (φ hi)
  set B := max (φ lo) (φ hi)
  have hbound : ∀ t ∈ Icc lo hi, A ≤ φ t ∧ φ t ≤ B := by
    intro t ht
    rcases hφ with hφ | hφ
    · exact ⟨le_trans (min_le_left _ _) (hφ ht.1), le_trans (hφ ht.2) (le_max_right _ _)⟩
    · exact ⟨le_trans (min_le_right _ _) (hφ ht.2), le_trans (hφ ht.1) (le_max_left _ _)⟩
  set m₁ : ℤ := ⌈(A - n') / n'⌉
  set m₂ : ℤ := ⌊B / n'⌋
  have hsub : u10h_pieceSet' P' φ lo hi K' ⊆
      (fun q : (ℤ × ℤ) × Triangle => (sInf (u10h_J' P' φ lo hi q.1.1 q.1.2 q.2),
        sSup (u10h_J' P' φ lo hi q.1.1 q.1.2 q.2))) '' ((Ico 0 (n' : ℤ) ×ˢ Icc m₁ m₂) ×ˢ K') := by
    rintro c ⟨k', m, hk0, hk1, T', hT', ⟨t, ht⟩, rfl⟩
    refine ⟨((k', m), T'), ⟨⟨⟨hk0, hk1⟩, ?_, ?_⟩, hT'⟩, rfl⟩
    · obtain ⟨hA, -⟩ := hbound t ht.1
      have h2 : (k' : ℝ) + 1 ≤ n' := by
        have : k' + 1 ≤ (n' : ℤ) := hk1
        exact_mod_cast this
      have h3 : φ t - m * n' ≤ k' + 1 := ht.2.1.2
      apply Int.ceil_le.mpr
      rw [div_le_iff₀ hn']
      linarith
    · obtain ⟨-, hB⟩ := hbound t ht.1
      have h0 : (0:ℝ) ≤ k' := by exact_mod_cast hk0
      have h3 : (k' : ℝ) ≤ φ t - m * n' := ht.2.1.1
      apply Int.le_floor.mpr
      rw [le_div_iff₀ hn']
      linarith
  exact (((Set.finite_Ico _ _).prod (Set.finite_Icc _ _)).prod hK').image _ |>.subset hsub

theorem u10h_frontier_param [NeZero n] {P : LabelledTuple n} {D : Set Plane} {f : Sphere → Plane}
    (hB : f '' sphereCircle P = frontier D) {a : Plane} (ha : a ∈ frontier D) :
    ∃ x ∈ Ico (0:ℝ) n, f ((traversal P x : Plane) : Sphere) = a := by
  rw [← hB] at ha
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := ha
  rw [← U4_range_traversal P] at hw
  obtain ⟨x₁, rfl⟩ := hw
  obtain ⟨x₀, hx₀, m, rfl⟩ := u10h_reduce (Nat.pos_of_ne_zero (NeZero.ne n)) x₁
  exact ⟨x₀, hx₀, by rw [u10h_traversal_add_int_mul]⟩

theorem u10h_param_ne [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P) {s : Side}
    {D : Set Plane} {f : Sphere → Plane} (hf : IsHomeoOnto (closure (regionOf P s)) D f)
    (hBS : sphereCircle P ⊆ closure (regionOf P s)) {u v : ℝ} (huv : u < v) (hvu : v < u + n) :
    f ((traversal P u : Plane) : Sphere) ≠ f ((traversal P v : Plane) : Sphere) := by
  intro h
  obtain ⟨m, hm⟩ := (u10h_param_eq_iff hn hP hf hBS u v).mp h
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 : (0:ℝ) < m * n := by linarith
  have h2 : (m:ℝ) * n < 1 * n := by linarith
  have h3 : (0:ℝ) < m := by
    by_contra h
    have : (m:ℝ) * n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hn0.le
    linarith
  have h4 : (m:ℝ) < 1 := lt_of_mul_lt_mul_right h2 hn0.le
  have h5 : (0:ℤ) < m := by exact_mod_cast h3
  have h6 : m < (1:ℤ) := by exact_mod_cast h4
  omega

/-- The two ordered cases of cyclic-order preservation (parameters `x < y < w < x + n`). -/
theorem u10h_pres_ordered [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) {z z' : Plane} (hz : z ∈ interior D)
    (hz' : z' ∈ interior D') {x y w : ℝ} (hxy : x < y) (hyw : y < w) (hwx : w < x + n) :
    (CyclicPos z (f ((traversal P x : Plane) : Sphere)) (f ((traversal P y : Plane) : Sphere))
        (f ((traversal P w : Plane) : Sphere)) →
      CyclicPos z' (f' ((traversal P' (φ x) : Plane) : Sphere)) (f' ((traversal P' (φ y) : Plane) : Sphere))
        (f' ((traversal P' (φ w) : Plane) : Sphere))) ∧
    (CyclicPos z (f ((traversal P x : Plane) : Sphere)) (f ((traversal P w : Plane) : Sphere))
        (f ((traversal P y : Plane) : Sphere)) →
      CyclicPos z' (f' ((traversal P' (φ x) : Plane) : Sphere)) (f' ((traversal P' (φ w) : Plane) : Sphere))
        (f' ((traversal P' (φ y) : Plane) : Sphere))) := by
  have hBS' := u10h_circle_subset_closure hn' P' hP' s' hL'
  have hfr' : ∀ u, f' ((traversal P' u : Plane) : Sphere) ∈ frontier D' := fun u =>
    hB' ▸ mem_image_of_mem f' (u10h_coe_traversal_mem_circle P' u)
  have hiff := U9_traversalPositiveFor_iff_cyclicPos hn P hP s hL hD hf hB hpl hz hxy hyw hwx
  by_cases hsame : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
  · obtain ⟨hmono, hper⟩ := hφ.same hsame
    have h1 : φ x < φ y := hmono hxy
    have h2 : φ y < φ w := hmono hyw
    have h3 : φ w < φ x + n' := by have := hmono hwx; rwa [hper] at this
    have hiff' := U9_traversalPositiveFor_iff_cyclicPos hn' P' hP' s' hL' hD' hf' hB' hpl' hz' h1 h2 h3
    constructor
    · intro hc
      exact hiff'.mp (hsame.mp (hiff.mpr hc))
    · intro hc
      have hnot : ¬ traversalPositiveFor P s := fun ht => u10h_cyclicPos_antisymm (hiff.mp ht) hc
      have hnot' : ¬ CyclicPos z' _ _ _ := fun hc' => hnot (hsame.mpr (hiff'.mpr hc'))
      rcases u10h_cyclicPos_total hD' hz' (hfr' (φ x)) (hfr' (φ y)) (hfr' (φ w))
        (u10h_param_ne hn' hP' hf' hBS' h1 (by linarith)) (u10h_param_ne hn' hP' hf' hBS' h2 (by linarith))
        (u10h_param_ne hn' hP' hf' hBS' (h1.trans h2) h3) with h | h
      · exact absurd h hnot'
      · exact h
  · obtain ⟨hanti, hper⟩ := hφ.opposite hsame
    have h1 : φ y < φ x := hanti hxy
    have h2 : φ w < φ y := hanti hyw
    have h3 : φ x - n' < φ w := by have := hanti hwx; rwa [hper] at this
    have hiff' := U9_traversalPositiveFor_iff_cyclicPos hn' P' hP' s' hL' hD' hf' hB' hpl' hz' h2 h1
      (by linarith)
    have hopp : traversalPositiveFor P s ↔ ¬ traversalPositiveFor P' s' := by tauto
    constructor
    · intro hc
      have hnot' : ¬ CyclicPos z' _ _ _ := fun hc' => (hopp.mp (hiff.mpr hc)) (hiff'.mpr hc')
      rcases u10h_cyclicPos_total hD' hz' (hfr' (φ x)) (hfr' (φ y)) (hfr' (φ w))
        (u10h_param_ne hn' hP' hf' hBS' h1 (by linarith)).symm
        (u10h_param_ne hn' hP' hf' hBS' h2 (by linarith)).symm
        (u10h_param_ne hn' hP' hf' hBS' (h2.trans h1) (by linarith)).symm with h | h
      · exact h
      · exact absurd (u10h_cyclicPos_rotate h) hnot'
    · intro hc
      have hnot : ¬ traversalPositiveFor P s := fun ht => u10h_cyclicPos_antisymm (hiff.mp ht) hc
      have hpos' : traversalPositiveFor P' s' := by tauto
      exact u10h_cyclicPos_rotate (u10h_cyclicPos_rotate (hiff'.mp hpos'))

theorem u10h_preservesCyclicPos [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) {z z' : Plane} (hz : z ∈ interior D)
    (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβc : ∀ x, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere)) :
    PreservesCyclicPos D z z' β := by
  intro a ha b hb c hc habc
  obtain ⟨x, hx, rfl⟩ := u10h_frontier_param hB ha
  obtain ⟨y, hy, rfl⟩ := u10h_frontier_param hB hb
  obtain ⟨w, hw, rfl⟩ := u10h_frontier_param hB hc
  obtain ⟨hab, hbc, hac⟩ := u10h_cyclicPos_ne habc
  have hxy : x ≠ y := fun h => hab (by rw [h])
  have hyw : y ≠ w := fun h => hbc (by rw [h])
  have hxw : x ≠ w := fun h => hac (by rw [h])
  rw [hβc, hβc, hβc]
  have key := fun {x y w : ℝ} (hxy : x < y) (hyw : y < w) (hwx : w < x + n) =>
    u10h_pres_ordered hn P hP hn' P' hP' s s' hL hL' hD hD' hf hf' hB hB' hpl hpl' hφ hz hz' hxy hyw hwx
  have hn0 : (0:ℝ) ≤ n := by positivity
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hyw with h2 | h2 <;>
    rcases lt_or_gt_of_ne hxw with h3 | h3
  · exact (key h1 h2 (by linarith [hw.2, hx.1])).1 habc
  · exact absurd (h1.trans h2) (not_lt.mpr h3.le)
  · exact (key h3 h2 (by linarith [hy.2, hx.1])).2 habc
  · have := (key h3 h1 (by linarith [hy.2, hw.1])).1 (u10h_cyclicPos_rotate (u10h_cyclicPos_rotate habc))
    exact u10h_cyclicPos_rotate this
  · have := (key h1 h3 (by linarith [hw.2, hy.1])).2 (u10h_cyclicPos_rotate habc)
    exact u10h_cyclicPos_rotate (u10h_cyclicPos_rotate this)
  · have := (key h2 h3 (by linarith [hx.2, hy.1])).1 (u10h_cyclicPos_rotate habc)
    exact u10h_cyclicPos_rotate (u10h_cyclicPos_rotate this)
  · exact absurd (h2.trans h1) (not_lt.mpr h3.le)
  · have := (key h2 h1 (by linarith [hx.2, hw.1])).2 (u10h_cyclicPos_rotate (u10h_cyclicPos_rotate habc))
    exact u10h_cyclicPos_rotate this

theorem u10h_continuousOn_of_isHomeoOnto {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} (h : IsHomeoOnto S S' f) : ContinuousOn f S := by
  obtain ⟨e, he⟩ := h
  rw [continuousOn_iff_continuous_restrict]
  have : S.domRestrict f = fun x => (e x : β) := by funext x; exact (he x).symm
  rw [this]
  exact continuous_subtype_val.comp e.continuous

/-- The boundary map induced by a positive lift is a homeomorphism of the model frontiers. -/
theorem u10h_boundary_homeo [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) {β : Plane → Plane}
    (hβc : ∀ x, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere)) :
    IsHomeoOnto (frontier D) (frontier D') β := by
  have hBS := u10h_circle_subset_closure hn P hP s hL
  have hBS' := u10h_circle_subset_closure hn' P' hP' s' hL'
  have hfr : ∀ t, f ((traversal P t : Plane) : Sphere) ∈ frontier D := fun t =>
    hB ▸ mem_image_of_mem f (u10h_coe_traversal_mem_circle P t)
  have hfr' : ∀ u, f' ((traversal P' u : Plane) : Sphere) ∈ frontier D' := fun u =>
    hB' ▸ mem_image_of_mem f' (u10h_coe_traversal_mem_circle P' u)
  have hc : Continuous fun t => f ((traversal P t : Plane) : Sphere) :=
    (u10h_continuousOn_of_isHomeoOnto hf).comp_continuous
      (OnePoint.continuous_coe.comp (continuous_traversal P))
      (fun t => hBS (u10h_coe_traversal_mem_circle P t))
  have hc' : Continuous fun t => f' ((traversal P' (φ t) : Plane) : Sphere) :=
    (u10h_continuousOn_of_isHomeoOnto hf').comp_continuous
      (OnePoint.continuous_coe.comp ((continuous_traversal P').comp hφ.continuous))
      (fun t => hBS' (u10h_coe_traversal_mem_circle P' (φ t)))
  have hβfr : ∀ w ∈ frontier D, β w ∈ frontier D' := by
    intro w hw
    obtain ⟨x, -, rfl⟩ := u10h_frontier_param hB hw
    rw [hβc]; exact hfr' _
  -- the map on subtypes
  let e₀ : frontier D → frontier D' := fun w => ⟨β w, hβfr w w.2⟩
  have hinj : Function.Injective e₀ := by
    rintro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ h
    have h' : β w₁ = β w₂ := congrArg Subtype.val h
    obtain ⟨x, -, rfl⟩ := u10h_frontier_param hB hw₁
    obtain ⟨y, -, rfl⟩ := u10h_frontier_param hB hw₂
    rw [hβc, hβc] at h'
    obtain ⟨m, hm⟩ := (u10h_param_eq_iff hn' hP' hf' hBS' (φ x) (φ y)).mp h'
    apply Subtype.ext
    show f _ = f _
    rw [u10h_param_eq_iff hn hP hf hBS]
    by_cases hsame : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
    · obtain ⟨hmono, hper⟩ := hφ.same hsame
      refine ⟨m, hmono.injective ?_⟩
      rw [u10h_lift_shift_same hper, hm]
    · obtain ⟨hanti, hper⟩ := hφ.opposite hsame
      refine ⟨-m, hanti.injective ?_⟩
      rw [u10h_lift_shift_opp hper, hm]; push_cast; ring
  have hsurj : Function.Surjective e₀ := by
    rintro ⟨w', hw'⟩
    obtain ⟨u, -, rfl⟩ := u10h_frontier_param hB' hw'
    obtain ⟨x, rfl⟩ := u10h_lift_surj hφ u
    exact ⟨⟨_, hfr x⟩, Subtype.ext (hβc x)⟩
  have hcont : Continuous e₀ := by
    rw [continuous_iff_isClosed]
    intro C hC
    obtain ⟨C₀, hC₀, rfl⟩ := isClosed_induced_iff.mp hC
    have hKc : IsCompact ((fun t => f ((traversal P t : Plane) : Sphere)) ''
        ((fun t => f' ((traversal P' (φ t) : Plane) : Sphere)) ⁻¹' C₀ ∩ Icc (0:ℝ) n)) :=
      (isCompact_Icc.inter_left (hC₀.preimage hc')).image hc
    have : e₀ ⁻¹' (Subtype.val ⁻¹' C₀) = Subtype.val ⁻¹' ((fun t => f ((traversal P t : Plane) : Sphere)) ''
        ((fun t => f' ((traversal P' (φ t) : Plane) : Sphere)) ⁻¹' C₀ ∩ Icc (0:ℝ) n)) := by
      ext ⟨w, hw⟩
      simp only [mem_preimage, e₀]
      constructor
      · intro h
        obtain ⟨x, hx, rfl⟩ := u10h_frontier_param hB hw
        rw [hβc] at h
        exact ⟨x, ⟨h, hx.1, hx.2.le⟩, rfl⟩
      · rintro ⟨x, ⟨hx, -⟩, hxw⟩
        show β w ∈ C₀
        rw [← hxw, hβc]; exact hx
    rw [this]
    exact hKc.isClosed.preimage continuous_subtype_val
  have : CompactSpace (frontier D) :=
    isCompact_iff_compactSpace.mp (hD.isCompact.of_isClosed_subset isClosed_frontier (u10h_frontier_subset hD))
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective e₀ ⟨hinj, hsurj⟩) hcont, fun w => rfl⟩

theorem u10h_marks_mono {m : ℕ} {a : ℕ → ℝ} (hainc : ∀ j < m, a j < a (j + 1)) :
    ∀ i j, i ≤ j → j ≤ m → a i ≤ a j := by
  intro i j hij hjm
  induction j with
  | zero =>
    have : i = 0 := by omega
    rw [this]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact (ih (by omega) (by omega)).trans (hainc j (by omega)).le
    · have : i = j + 1 := by omega
      rw [this]

theorem u10h_marks_cover {m : ℕ} {a : ℕ → ℝ} (hainc : ∀ j < m, a j < a (j + 1)) (hm : 1 ≤ m) :
    ∀ t ∈ Icc (a 0) (a m), ∃ j < m, t ∈ Icc (a j) (a (j + 1)) := by
  suffices h : ∀ j, 1 ≤ j → j ≤ m → ∀ t ∈ Icc (a 0) (a j), ∃ i < j, t ∈ Icc (a i) (a (i + 1)) from
    h m hm le_rfl
  intro j hj1 hjm
  induction j with
  | zero => omega
  | succ j ih =>
    intro t ht
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; exact ⟨0, by omega, ht⟩
    · rcases le_or_gt t (a j) with h | h
      · obtain ⟨i, hi, hti⟩ := ih hj (by omega) t ⟨ht.1, h⟩
        exact ⟨i, by omega, hti⟩
      · exact ⟨j, by omega, h.le, ht.2⟩

/-- The induced boundary map is finite PL on the frontier of the model. -/
theorem u10h_finitePL [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D : Set Plane}
    {f f' : Sphere → Plane} (hB : f '' sphereCircle P = frontier D)
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) (hfin : IsFinitePL n φ) {β : Plane → Plane}
    (hβc : ∀ x, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere)) :
    IsFinitePLOnFrontier D β := by
  classical
  have hBS := u10h_circle_subset_closure hn P hP s hL
  have hBS' := u10h_circle_subset_closure hn' P' hP' s' hL'
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hfr : ∀ t, f ((traversal P t : Plane) : Sphere) ∈ frontier D := fun t =>
    hB ▸ mem_image_of_mem f (u10h_coe_traversal_mem_circle P t)
  obtain ⟨K, hK⟩ := hpl false
  obtain ⟨K', hK'⟩ := hpl' false
  obtain ⟨m, a, ha0, ham, hainc, haff⟩ := hfin
  have hmono : Monotone φ ∨ Antitone φ := by
    by_cases hsame : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
    · exact Or.inl (hφ.same hsame).1.monotone
    · exact Or.inr (hφ.opposite hsame).1.antitone
  have hφc : Continuous φ := hφ.continuous
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso; subst h; rw [ha0] at ham; linarith
    · exact h
  set c : ℝ → Plane := fun t => f ((traversal P t : Plane) : Sphere) with hc_def
  -- the three covers of `[0, n]`
  set C₁ := u10h_pieceSet P K.faces with hC₁
  set C₂ : Set (ℝ × ℝ) := (fun j : ℕ => (a j, a (j + 1))) '' {j | j < m} with hC₂
  set C₃ := u10h_pieceSet' P' φ 0 n K'.faces with hC₃
  have hC₁fin : C₁.Finite := u10h_pieceSet_finite P K.finite
  have hC₂fin : C₂.Finite := (Set.finite_lt_nat m).image _
  have hC₃fin : C₃.Finite := u10h_pieceSet'_finite P' hmono 0 n K'.finite
  have hC₁in : ∀ q ∈ C₁, 0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ n := by
    rintro q ⟨k, hk, T, hT, hne, rfl⟩
    have hcpt := u10h_J_isCompact P k T
    have h1 := hcpt.sInf_mem hne
    have h2 := hcpt.sSup_mem hne
    have h1' := h1.1.1
    have h2' := h2.1.2
    have h12 : sInf (u10h_J P k T) ≤ sSup (u10h_J P k T) :=
      csInf_le_csSup hne hcpt.bddBelow hcpt.bddAbove
    push_cast at h1' h2'
    have hk1 : (k:ℝ) + 1 ≤ n := by
      have : (k + 1 : ℕ) ≤ n := hk
      exact_mod_cast this
    exact ⟨(by positivity : (0:ℝ) ≤ k).trans h1', h12, h2'.trans hk1⟩
  have hC₂in : ∀ q ∈ C₂, 0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ n := by
    rintro q ⟨j, hj, rfl⟩
    have hmo := u10h_marks_mono hainc
    refine ⟨?_, (hainc j hj).le, ?_⟩
    · rw [← ha0]; exact hmo 0 j (Nat.zero_le _) hj.le
    · rw [← ham]; exact hmo (j + 1) m hj le_rfl
  have hC₃in : ∀ q ∈ C₃, 0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ n := by
    rintro q ⟨k', mm, hk0, hk1, T', hT', hne, rfl⟩
    have hcpt := u10h_J'_isCompact P' hφc 0 n k' mm T'
    have h1 := hcpt.sInf_mem hne
    have h2 := hcpt.sSup_mem hne
    exact ⟨h1.1.1, csInf_le_csSup hne hcpt.bddBelow hcpt.bddAbove, h2.1.2⟩
  have hC₁cov : ∀ t ∈ Icc (0:ℝ) n, ∃ q ∈ C₁, t ∈ Icc q.1 q.2 := fun t ht =>
    u10h_pieceSet_cover P hL hBS K ht
  have hC₂cov : ∀ t ∈ Icc (0:ℝ) n, ∃ q ∈ C₂, t ∈ Icc q.1 q.2 := by
    intro t ht
    obtain ⟨j, hj, htj⟩ := u10h_marks_cover hainc hm1 t (by rw [ha0, ham]; exact ht)
    exact ⟨(a j, a (j + 1)), ⟨j, hj, rfl⟩, htj⟩
  have hC₃cov : ∀ t ∈ Icc (0:ℝ) n, ∃ q ∈ C₃, t ∈ Icc q.1 q.2 := by
    intro t ht
    obtain ⟨k', mm, hk0, hk1, T', hT', htJ⟩ := u10h_J'_cover P' φ 0 n hL' hBS' K' ht
    refine ⟨_, ⟨k', mm, hk0, hk1, T', hT', ⟨t, htJ⟩, rfl⟩, ?_⟩
    have := u10h_J'_eq_Icc P' hφc hmono 0 n k' mm T' ⟨t, htJ⟩
    rw [← this]; exact htJ
  have hC₁aff : ∀ q ∈ C₁, u10h_AffOn c (Icc q.1 q.2) := fun q hq => u10h_pieceSet_affOn P hK hq
  have hC₂aff : ∀ q ∈ C₂, ∃ α δ : ℝ, ∀ t ∈ Icc q.1 q.2, φ t = α * t + δ := by
    rintro q ⟨j, hj, rfl⟩
    exact haff j hj
  have hC₃aff : ∀ q ∈ C₃, ∃ p'' u'' : Plane, ∀ t ∈ Icc q.1 q.2,
      f' ((traversal P' (φ t) : Plane) : Sphere) = p'' + φ t • u'' := by
    rintro q ⟨k', mm, hk0, hk1, T', hT', hne, rfl⟩
    obtain ⟨p'', u'', h⟩ := u10h_affOn_J' P' φ 0 n hK' k' mm hT'
    refine ⟨p'', u'', fun t ht => h t ?_⟩
    rwa [u10h_J'_eq_Icc P' hφc hmono 0 n k' mm T' hne]
  -- the breakpoints
  set B : Set ℝ := ({0, (n:ℝ)} ∪ (Prod.fst '' C₁ ∪ Prod.snd '' C₁)) ∪
    ((Prod.fst '' C₂ ∪ Prod.snd '' C₂) ∪ (Prod.fst '' C₃ ∪ Prod.snd '' C₃)) with hB_def
  have hBfin : B.Finite :=
    ((Set.toFinite _).union ((hC₁fin.image _).union (hC₁fin.image _))).union
      (((hC₂fin.image _).union (hC₂fin.image _)).union ((hC₃fin.image _).union (hC₃fin.image _)))
  have h0B : (0:ℝ) ∈ B := Or.inl (Or.inl (by simp))
  have hnB : (n:ℝ) ∈ B := Or.inl (Or.inl (by simp))
  have hC₁B : ∀ q ∈ C₁, q.1 ∈ B ∧ q.2 ∈ B := fun q hq =>
    ⟨Or.inl (Or.inr (Or.inl ⟨q, hq, rfl⟩)), Or.inl (Or.inr (Or.inr ⟨q, hq, rfl⟩))⟩
  have hC₂B : ∀ q ∈ C₂, q.1 ∈ B ∧ q.2 ∈ B := fun q hq =>
    ⟨Or.inr (Or.inl (Or.inl ⟨q, hq, rfl⟩)), Or.inr (Or.inl (Or.inr ⟨q, hq, rfl⟩))⟩
  have hC₃B : ∀ q ∈ C₃, q.1 ∈ B ∧ q.2 ∈ B := fun q hq =>
    ⟨Or.inr (Or.inr (Or.inl ⟨q, hq, rfl⟩)), Or.inr (Or.inr (Or.inr ⟨q, hq, rfl⟩))⟩
  have hBin : ∀ b ∈ B, 0 ≤ b ∧ b ≤ n := by
    intro b hb
    rcases hb with (hb | (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)) | ((⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩))
    · simp only [mem_insert_iff, mem_singleton_iff] at hb
      rcases hb with rfl | rfl <;> constructor <;> linarith
    · obtain ⟨h1, h2, h3⟩ := hC₁in q hq; exact ⟨h1, h2.trans h3⟩
    · obtain ⟨h1, h2, h3⟩ := hC₁in q hq; exact ⟨h1.trans h2, h3⟩
    · obtain ⟨h1, h2, h3⟩ := hC₂in q hq; exact ⟨h1, h2.trans h3⟩
    · obtain ⟨h1, h2, h3⟩ := hC₂in q hq; exact ⟨h1.trans h2, h3⟩
    · obtain ⟨h1, h2, h3⟩ := hC₃in q hq; exact ⟨h1, h2.trans h3⟩
    · obtain ⟨h1, h2, h3⟩ := hC₃in q hq; exact ⟨h1.trans h2, h3⟩
  -- the gap pairs
  set G : Set (ℝ × ℝ) := {g | g.1 ∈ B ∧ g.2 ∈ B ∧ g.1 < g.2 ∧ ∀ a ∈ B, g.1 < a → a < g.2 → False}
    with hG
  have hGfin : G.Finite := (hBfin.prod hBfin).subset (fun g hg => ⟨hg.1, hg.2.1⟩)
  have hgap : ∀ g ∈ G, (∃ p u : Plane, ∀ t ∈ Icc g.1 g.2, c t = p + t • u) ∧
      (∃ p'' u'' : Plane, ∀ t ∈ Icc g.1 g.2, β (c t) = p'' + t • u'') := by
    rintro g ⟨hg1, hg2, hlt, hnone⟩
    have hb0 : 0 ≤ g.1 := (hBin _ hg1).1
    have hbn : g.2 ≤ n := (hBin _ hg2).2
    obtain ⟨q₁, hq₁, hsub₁⟩ := u10h_subset_piece hC₁B hC₁cov hb0 hbn hlt hnone
    obtain ⟨q₂, hq₂, hsub₂⟩ := u10h_subset_piece hC₂B hC₂cov hb0 hbn hlt hnone
    obtain ⟨q₃, hq₃, hsub₃⟩ := u10h_subset_piece hC₃B hC₃cov hb0 hbn hlt hnone
    obtain ⟨p, u, hpu⟩ := hC₁aff q₁ hq₁
    obtain ⟨α, δ, hαδ⟩ := hC₂aff q₂ hq₂
    obtain ⟨p'', u'', hpu''⟩ := hC₃aff q₃ hq₃
    refine ⟨⟨p, u, fun t ht => hpu t (hsub₁ ht)⟩, ⟨p'' + δ • u'', α • u'', ?_⟩⟩
    intro t ht
    show β (f ((traversal P t : Plane) : Sphere)) = _
    rw [hβc, hpu'' t (hsub₃ ht), hαδ t (hsub₂ ht), add_smul, smul_smul, mul_comm t α]
    abel
  -- the segments
  set sF : Finset (Plane × Plane) := (hGfin.image (fun g : ℝ × ℝ => (c g.1, c g.2))).toFinset with hsF
  refine ⟨sF, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro w hw
      rw [mem_iUnion₂] at hw
      obtain ⟨p, hp, hwp⟩ := hw
      rw [hsF, Set.Finite.mem_toFinset] at hp
      obtain ⟨g, hg, rfl⟩ := hp
      obtain ⟨⟨pp, u, hpu⟩, -⟩ := hgap g hg
      rw [← u10h_image_Icc_eq_segment hpu hg.2.2.1.le] at hwp
      obtain ⟨t, -, rfl⟩ := hwp
      exact hfr t
    · intro w hw
      obtain ⟨x, hx, rfl⟩ := u10h_frontier_param hB hw
      obtain ⟨b, hb, b', hb', hlt, hbx, hxb, hnone⟩ := u10h_gap' hBfin h0B hnB hn0 ⟨hx.1, hx.2.le⟩
      have hgG : (b, b') ∈ G := ⟨hb, hb', hlt, hnone⟩
      rw [mem_iUnion₂]
      refine ⟨(c b, c b'), ?_, ?_⟩
      · rw [hsF, Set.Finite.mem_toFinset]; exact ⟨(b, b'), hgG, rfl⟩
      · obtain ⟨⟨pp, u, hpu⟩, -⟩ := hgap (b, b') hgG
        show f ((traversal P x : Plane) : Sphere) ∈ segment ℝ (c b) (c b')
        rw [← u10h_image_Icc_eq_segment hpu hlt.le]
        exact ⟨x, ⟨hbx, hxb⟩, rfl⟩
  · intro p hp
    rw [hsF, Set.Finite.mem_toFinset] at hp
    obtain ⟨g, hg, rfl⟩ := hp
    obtain ⟨⟨pp, u, hpu⟩, ⟨p'', u'', hβ⟩⟩ := hgap g hg
    show AffineOn β (segment ℝ (c g.1) (c g.2))
    rw [← u10h_image_Icc_eq_segment hpu hg.2.2.1.le]
    exact u10h_affineOn_of_param hpu hβ hg.2.2.1.le

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
  classical
  obtain ⟨z, hz⟩ := hD.interior_nonempty
  obtain ⟨z', hz'⟩ := hD'.interior_nonempty
  have hBS := u10h_circle_subset_closure hn P hP s hL
  let β : Plane → Plane := fun w =>
    if h : ∃ x : ℝ, f ((traversal P x : Plane) : Sphere) = w then
      f' ((traversal P' (φ h.choose) : Plane) : Sphere) else w
  have hβc : ∀ x, β (f ((traversal P x : Plane) : Sphere)) =
      f' ((traversal P' (φ x) : Plane) : Sphere) := by
    intro x
    have hex : ∃ x' : ℝ, f ((traversal P x' : Plane) : Sphere) = f ((traversal P x : Plane) : Sphere) :=
      ⟨x, rfl⟩
    show (if h : ∃ x' : ℝ, f ((traversal P x' : Plane) : Sphere) = f ((traversal P x : Plane) : Sphere) then
      f' ((traversal P' (φ h.choose) : Plane) : Sphere) else _) = _
    rw [dif_pos hex]
    have hspec := hex.choose_spec
    set x₀ := hex.choose with hx₀
    clear_value x₀
    obtain ⟨m, hm⟩ := (u10h_param_eq_iff hn hP hf hBS x₀ x).mp hspec
    rw [hm]
    by_cases hsame : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
    · rw [u10h_lift_shift_same (hφ.same hsame).2, u10h_traversal_add_int_mul]
    · rw [u10h_lift_shift_opp (hφ.opposite hsame).2, sub_eq_add_neg, ← neg_mul, ← Int.cast_neg,
        u10h_traversal_add_int_mul]
  exact ⟨β, z, z', hz, hz',
    u10h_boundary_homeo hn P hP hn' P' hP' s s' hL hL' hD hD' hf hf' hB hB' hφ hβc,
    u10h_finitePL hn P hP hn' P' hP' s s' hL hL' hB hpl hpl' hφ hfin hβc,
    u10h_preservesCyclicPos hn P hP hn' P' hP' s s' hL hL' hD hD' hf hf' hB hB' hpl hpl' hφ hz hz' hβc,
    hβc⟩

/-! #### U10 helpers for `U10_pl_extension` -/

theorem u10h_isHomeoOnto_image {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {S : Set α}
    {S' : Set β} {f : α → β} (h : IsHomeoOnto S S' f) : f '' S = S' := by
  obtain ⟨e, he⟩ := h
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← he ⟨x, hx⟩]; exact (e ⟨x, hx⟩).2
  · intro hw
    refine ⟨e.symm ⟨w, hw⟩, (e.symm ⟨w, hw⟩).2, ?_⟩
    rw [← he]; simp

theorem u10h_pl_discs [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (s : Side)
    (L : ℝ) (hL : InsideModel L P) :
    IsPLDiscSphere L (closure (regionOf P s)) (sphereCircle P) := by
  cases s with
  | inner => exact U7_pl_discs_inner hn P hP L hL
  | outer => exact U8_pl_discs_outer hn P hP L hL

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
  obtain ⟨D, f, hD, hBS, hf, hB, hpl⟩ := u10h_pl_discs hn P hP s L hL
  obtain ⟨D', f', hD', hBS', hf', hB', hpl'⟩ := u10h_pl_discs hn' P' hP' s' L' hL'
  obtain ⟨β, z, z', hz, hz', hβ, hβpl, hβpos, hβc⟩ :=
    U10_boundary_map_of_lift hn P hP hn' P' hP' s s' hL hL' hD hD' hf hf' hB hB' hpl hpl' hφ hfin
  obtain ⟨K, Fan, hFanK, hFan, hFanβ⟩ := U10_fan_extension hD hD' hz hz' hβ hβpl hβpos
  obtain ⟨g', hg'pl, hg'l, hg'r⟩ := U3_isPositivePLFromPlane_inv hD' hf' hpl'
  have hfS : f '' closure (regionOf P s) = D := u10h_isHomeoOnto_image hf
  have hFanD : Fan '' D = D' := u10h_isHomeoOnto_image hFan
  have hg' : IsHomeoOnto D' (closure (regionOf P' s')) g' := U1_isHomeoOnto_inv hf' hg'l
  refine ⟨g' ∘ (Fan ∘ f), ?_, ?_, ?_⟩
  · exact U1_isHomeoOnto_comp (U1_isHomeoOnto_comp hf hFan) hg'
  · have h1 : IsPositivePLToPlane L (closure (regionOf P s)) (Fan ∘ f) :=
      U3_isPositivePLToPlane_comp_plane K hpl hfS.le hFanK
    have h2 : (Fan ∘ f) '' closure (regionOf P s) ⊆ D' := by rw [image_comp, hfS, hFanD]
    exact U3_isPositivePLSphereMap_comp h1 h2 hg'pl
  · intro x
    have hfx : f ((traversal P x : Plane) : Sphere) ∈ frontier D :=
      hB ▸ mem_image_of_mem f (u10h_coe_traversal_mem_circle P x)
    have hx' : ((traversal P' (φ x) : Plane) : Sphere) ∈ closure (regionOf P' s') :=
      hBS' (u10h_coe_traversal_mem_circle P' (φ x))
    simp only [Function.comp]
    rw [hFanβ _ hfx, hβc x, hg'l _ hx']

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
