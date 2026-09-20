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

/-- a disc with `0` interior is a neighbourhood of `0`. -/
theorem u11h_mem_nhds_of_interior {D : Set Plane} (h0 : (0 : Plane) ∈ interior D) : D ∈ nhds 0 :=
  mem_interior_iff_mem_nhds.mp h0

theorem u11h_isVonNBounded {D : Set Plane} (hD : Link.IsDisc D) : Bornology.IsVonNBounded ℝ D :=
  hD.2.1.isVonNBounded ℝ

/-- U11 (gauge coordinates): for a convex disc with `0` in its interior, the frontier is the gauge
level `1` and the disc is the sublevel `≤ 1`. -/
theorem U11_frontier_eq_gauge_one {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D) :
    frontier D = {x | gauge D x = 1} ∧ D = {x | gauge D x ≤ 1} := by
  have hn : D ∈ nhds (0 : Plane) := u11h_mem_nhds_of_interior h0
  refine ⟨?_, ?_⟩
  · ext x
    simp only [mem_ofPred_eq]
    exact (gauge_eq_one_iff_mem_frontier hD.1 hn).symm
  · ext x
    simp only [mem_ofPred_eq]
    rw [gauge_le_one_iff_mem_closure hD.1 hn, hD.2.1.isClosed.closure_eq]
/-- gauge positivity off `0` for a disc with `0` interior. -/
theorem u11h_gauge_pos {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    {x : Plane} (hx : x ≠ 0) : 0 < gauge D x :=
  (gauge_pos (absorbent_nhds_zero (u11h_mem_nhds_of_interior h0)) (u11h_isVonNBounded hD)).mpr hx

/-- The radial projection onto the frontier: `x ↦ (gauge D x)⁻¹ • x`. -/
noncomputable def u11h_proj (D : Set Plane) (x : Plane) : Plane := (gauge D x)⁻¹ • x

/-- The radial map: `x ↦ gauge D x • b (proj D x)`. -/
noncomputable def u11h_rad (D : Set Plane) (b : Plane → Plane) (x : Plane) : Plane :=
  gauge D x • b (u11h_proj D x)

theorem u11h_gauge_proj {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    {x : Plane} (hx : x ≠ 0) : gauge D (u11h_proj D x) = 1 := by
  have hp := u11h_gauge_pos hD h0 hx
  unfold u11h_proj
  rw [gauge_smul_of_nonneg (inv_nonneg.mpr hp.le), smul_eq_mul, inv_mul_cancel₀ hp.ne']

theorem u11h_proj_mem_frontier {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    {x : Plane} (hx : x ≠ 0) : u11h_proj D x ∈ frontier D := by
  rw [(U11_frontier_eq_gauge_one hD h0).1]
  exact u11h_gauge_proj hD h0 hx

theorem u11h_rad_zero (D : Set Plane) (b : Plane → Plane) : u11h_rad D b 0 = 0 := by
  simp [u11h_rad]

theorem u11h_rad_of_mem_frontier {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (b : Plane → Plane) {x : Plane} (hx : x ∈ frontier D) : u11h_rad D b x = b x := by
  have h1 : gauge D x = 1 := by
    rw [(U11_frontier_eq_gauge_one hD h0).1] at hx; exact hx
  simp [u11h_rad, u11h_proj, h1]

theorem u11h_gauge_rad {D D' : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (hD' : Link.IsDisc D') (h0' : (0 : Plane) ∈ interior D') {b : Plane → Plane}
    (hb : MapsTo b (frontier D) (frontier D')) (x : Plane) :
    gauge D' (u11h_rad D b x) = gauge D x := by
  by_cases hx : x = 0
  · subst hx; simp [u11h_rad]
  · have h1 : gauge D' (b (u11h_proj D x)) = 1 := by
      have := hb (u11h_proj_mem_frontier hD h0 hx)
      rw [(U11_frontier_eq_gauge_one hD' h0').1] at this; exact this
    unfold u11h_rad
    rw [gauge_smul_of_nonneg (gauge_nonneg _), smul_eq_mul, h1, mul_one]

theorem u11h_proj_rad {D D' : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (hD' : Link.IsDisc D') (h0' : (0 : Plane) ∈ interior D') {b : Plane → Plane}
    (hb : MapsTo b (frontier D) (frontier D')) {x : Plane} (hx : x ≠ 0) :
    u11h_proj D' (u11h_rad D b x) = b (u11h_proj D x) := by
  have hp := u11h_gauge_pos hD h0 hx
  unfold u11h_proj
  rw [u11h_gauge_rad hD h0 hD' h0' hb x]
  unfold u11h_rad
  rw [smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
  rfl

theorem u11h_rad_mem {D D' : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (hD' : Link.IsDisc D') (h0' : (0 : Plane) ∈ interior D') {b : Plane → Plane}
    (hb : MapsTo b (frontier D) (frontier D')) {x : Plane} (hx : x ∈ D) : u11h_rad D b x ∈ D' := by
  rw [(U11_frontier_eq_gauge_one hD' h0').2]
  show gauge D' (u11h_rad D b x) ≤ 1
  rw [u11h_gauge_rad hD h0 hD' h0' hb x]
  exact gauge_le_one_of_mem hx

theorem u11h_rad_rad {D D' : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (hD' : Link.IsDisc D') (h0' : (0 : Plane) ∈ interior D') {b b' : Plane → Plane}
    (hb : MapsTo b (frontier D) (frontier D')) (hb' : ∀ u ∈ frontier D, b' (b u) = u) (x : Plane) :
    u11h_rad D' b' (u11h_rad D b x) = x := by
  by_cases hx : x = 0
  · subst hx; simp [u11h_rad]
  · have hp := u11h_gauge_pos hD h0 hx
    have h1 := u11h_gauge_rad hD h0 hD' h0' hb x
    have h2 := u11h_proj_rad hD h0 hD' h0' hb hx
    show gauge D' (u11h_rad D b x) • b' (u11h_proj D' (u11h_rad D b x)) = x
    rw [h1, h2, hb' _ (u11h_proj_mem_frontier hD h0 hx)]
    unfold u11h_proj
    rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]

theorem u11h_continuousOn_proj {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D) :
    ContinuousOn (u11h_proj D) {x | x ≠ 0} := by
  have hg : Continuous (gauge D) := continuous_gauge hD.1 (u11h_mem_nhds_of_interior h0)
  refine ContinuousOn.smul (hg.continuousOn.inv₀ ?_) continuousOn_id
  intro x hx
  exact (u11h_gauge_pos hD h0 hx).ne'

theorem u11h_continuous_rad {D D' : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (hD' : Link.IsDisc D') {b : Plane → Plane}
    (hb : ContinuousOn b (frontier D)) (hbm : MapsTo b (frontier D) (frontier D')) :
    Continuous (u11h_rad D b) := by
  have hg : Continuous (gauge D) := continuous_gauge hD.1 (u11h_mem_nhds_of_interior h0)
  have hmaps : MapsTo (u11h_proj D) {x | x ≠ 0} (frontier D) := fun x hx =>
    u11h_proj_mem_frontier hD h0 hx
  have hne : ContinuousOn (u11h_rad D b) {x | x ≠ 0} :=
    hg.continuousOn.smul (hb.comp (u11h_continuousOn_proj hD h0) hmaps)
  obtain ⟨M, hM⟩ := hD'.2.1.isBounded.subset_closedBall 0
  have hbound : ∀ x, ‖u11h_rad D b x‖ ≤ gauge D x * M := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [u11h_rad_zero]
    · have hmem : b (u11h_proj D x) ∈ D' :=
        hD'.2.1.isClosed.frontier_subset (hbm (u11h_proj_mem_frontier hD h0 hx))
      have hM' : ‖b (u11h_proj D x)‖ ≤ M := by simpa using hM hmem
      unfold u11h_rad
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (gauge_nonneg _)]
      exact mul_le_mul_of_nonneg_left hM' (gauge_nonneg _)
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : x = 0
  · subst hx
    rw [ContinuousAt, u11h_rad_zero]
    refine squeeze_zero_norm hbound ?_
    have : Filter.Tendsto (fun x => gauge D x * M) (nhds 0) (nhds (gauge D 0 * M)) :=
      (hg.tendsto 0).mul_const M
    simpa [gauge_zero] using this
  · exact hne.continuousAt (isOpen_ne.mem_nhds hx)

/-- Translating a disc so that an interior point `c` goes to `0`: the preimage under `x ↦ x + c`. -/
theorem u11h_translate {D : Set Plane} (hD : Link.IsDisc D) {c : Plane} (hc : c ∈ interior D) :
    Link.IsDisc ((fun x => x + c) ⁻¹' D) ∧ (0 : Plane) ∈ interior ((fun x => x + c) ⁻¹' D) ∧
      frontier ((fun x => x + c) ⁻¹' D) = (fun x => x + c) ⁻¹' frontier D := by
  have hint : interior ((fun x => x + c) ⁻¹' D) = (fun x => x + c) ⁻¹' interior D :=
    ((Homeomorph.addRight c).preimage_interior D).symm
  have hfr : frontier ((fun x => x + c) ⁻¹' D) = (fun x => x + c) ⁻¹' frontier D :=
    ((Homeomorph.addRight c).preimage_frontier D).symm
  have h0 : (0 : Plane) ∈ interior ((fun x => x + c) ⁻¹' D) := by
    rw [hint]; show (0 : Plane) + c ∈ interior D; simpa using hc
  refine ⟨⟨hD.1.translate_preimage_left c, ?_, ⟨0, h0⟩⟩, h0, hfr⟩
  exact (Homeomorph.addRight c).isCompact_preimage.mpr hD.2.1

open Classical in
/-- The inverse of a set homeomorphism, as a plane map (junk `0` off the target). -/
noncomputable def u11h_homeoInv {S S' : Set Plane} (e : S ≃ₜ S') (y : Plane) : Plane :=
  if h : y ∈ S' then (e.symm ⟨y, h⟩ : Plane) else 0

theorem u11h_isHomeoOnto_facts {S S' : Set Plane} {β : Plane → Plane}
    (hβ : IsHomeoOnto S S' β) :
    ∃ βi : Plane → Plane, ContinuousOn β S ∧ MapsTo β S S' ∧ ContinuousOn βi S' ∧ MapsTo βi S' S ∧
      (∀ u ∈ S, βi (β u) = u) ∧ (∀ u ∈ S', β (βi u) = u) := by
  obtain ⟨e, he⟩ := hβ
  refine ⟨u11h_homeoInv e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : domRestrict S β = fun z => (e z : Plane) := funext fun z => (he z).symm
    rw [this]; exact continuous_subtype_val.comp e.continuous
  · intro z hz; rw [← he ⟨z, hz⟩]; exact (e ⟨z, hz⟩).2
  · rw [continuousOn_iff_continuous_domRestrict]
    have : domRestrict S' (u11h_homeoInv e) = fun y => (e.symm y : Plane) := by
      funext y; simp only [domRestrict, u11h_homeoInv, y.2, ↓reduceDIte]
    rw [this]; exact continuous_subtype_val.comp e.symm.continuous
  · intro y hy; simp only [u11h_homeoInv, hy, ↓reduceDIte]; exact (e.symm ⟨y, hy⟩).2
  · intro u hu
    have h1 : β u ∈ S' := by rw [← he ⟨u, hu⟩]; exact (e ⟨u, hu⟩).2
    simp only [u11h_homeoInv, h1, ↓reduceDIte]
    have : (⟨β u, h1⟩ : S') = e ⟨u, hu⟩ := Subtype.ext (he ⟨u, hu⟩).symm
    rw [this, e.symm_apply_apply]
  · intro u hu
    simp only [u11h_homeoInv, hu, ↓reduceDIte]
    rw [← he (e.symm ⟨u, hu⟩), e.apply_symm_apply]

/-- U11 (sm-3:537-542, the radial / Alexander extension on convex models): a homeomorphism between
the frontiers of two convex discs extends to a homeomorphism of the discs. -/
theorem U11_radial_extension {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    {β : Plane → Plane} (hβ : IsHomeoOnto (frontier D) (frontier D') β) :
    ∃ F : Plane → Plane, IsHomeoOnto D D' F ∧ ∀ x ∈ frontier D, F x = β x := by
  obtain ⟨c, hc⟩ := hD.2.2
  obtain ⟨c', hc'⟩ := hD'.2.2
  obtain ⟨hA, h0, hfrA⟩ := u11h_translate hD hc
  obtain ⟨hA', h0', hfrA'⟩ := u11h_translate hD' hc'
  obtain ⟨βi, hβc, hβm, hβic, hβim, hβiβ, hββi⟩ := u11h_isHomeoOnto_facts hβ
  set A : Set Plane := (fun x => x + c) ⁻¹' D with hAdef
  set A' : Set Plane := (fun x => x + c') ⁻¹' D' with hA'def
  set b : Plane → Plane := fun y => β (y + c) - c' with hbdef
  set b' : Plane → Plane := fun y => βi (y + c') - c with hb'def
  have hmA : ∀ y, y ∈ frontier A ↔ y + c ∈ frontier D := fun y => by rw [hfrA]; rfl
  have hmA' : ∀ y, y ∈ frontier A' ↔ y + c' ∈ frontier D' := fun y => by rw [hfrA']; rfl
  have hbc : ContinuousOn b (frontier A) := by
    refine ContinuousOn.sub (hβc.comp (continuous_add_const c).continuousOn ?_) continuousOn_const
    intro y hy; exact (hmA y).mp hy
  have hbm : MapsTo b (frontier A) (frontier A') := by
    intro y hy; rw [hmA']; simp only [hbdef, sub_add_cancel]; exact hβm ((hmA y).mp hy)
  have hb'c : ContinuousOn b' (frontier A') := by
    refine ContinuousOn.sub (hβic.comp (continuous_add_const c').continuousOn ?_) continuousOn_const
    intro y hy; exact (hmA' y).mp hy
  have hb'm : MapsTo b' (frontier A') (frontier A) := by
    intro y hy; rw [hmA]; simp only [hb'def, sub_add_cancel]; exact hβim ((hmA' y).mp hy)
  have hb'b : ∀ u ∈ frontier A, b' (b u) = u := by
    intro u hu; simp only [hbdef, hb'def, sub_add_cancel]
    rw [hβiβ _ ((hmA u).mp hu), add_sub_cancel_right]
  have hbb' : ∀ u ∈ frontier A', b (b' u) = u := by
    intro u hu; simp only [hbdef, hb'def, sub_add_cancel]
    rw [hββi _ ((hmA' u).mp hu), add_sub_cancel_right]
  have hcont : Continuous (u11h_rad A b) := u11h_continuous_rad hA h0 hA' hbc hbm
  have hcont' : Continuous (u11h_rad A' b') := u11h_continuous_rad hA' h0' hA hb'c hb'm
  have hmemA : ∀ x, x ∈ D → x - c ∈ A := fun x hx => by
    show x - c + c ∈ D; rwa [sub_add_cancel]
  have hmemA' : ∀ x, x ∈ D' → x - c' ∈ A' := fun x hx => by
    show x - c' + c' ∈ D'; rwa [sub_add_cancel]
  refine ⟨fun x => u11h_rad A b (x - c) + c', ⟨?_, ?_⟩, ?_⟩
  · exact
      { toFun := fun x => ⟨u11h_rad A b (x.1 - c) + c', u11h_rad_mem hA h0 hA' h0' hbm (hmemA _ x.2)⟩
        invFun := fun y => ⟨u11h_rad A' b' (y.1 - c') + c,
          u11h_rad_mem hA' h0' hA h0 hb'm (hmemA' _ y.2)⟩
        left_inv := fun x => by
          apply Subtype.ext
          simp only [add_sub_cancel_right]
          rw [u11h_rad_rad hA h0 hA' h0' hbm hb'b, sub_add_cancel]
        right_inv := fun y => by
          apply Subtype.ext
          simp only [add_sub_cancel_right]
          rw [u11h_rad_rad hA' h0' hA h0 hb'm hbb', sub_add_cancel]
        continuous_toFun := by
          exact ((hcont.comp (continuous_subtype_val.sub continuous_const)).add
            continuous_const).subtype_mk _
        continuous_invFun := by
          exact ((hcont'.comp (continuous_subtype_val.sub continuous_const)).add
            continuous_const).subtype_mk _ }
  · intro z; rfl
  · intro x hx
    have hxA : x - c ∈ frontier A := by rw [hmA, sub_add_cancel]; exact hx
    show u11h_rad A b (x - c) + c' = β x
    rw [u11h_rad_of_mem_frontier hA h0 b hxA]
    simp only [hbdef, sub_add_cancel]
/-- integer periodicity of the traversal. -/
theorem u11h_traversal_add_int (P : LabelledTuple n) (x : ℝ) (m : ℤ) :
    traversal P (x + m * n) = traversal P x := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have : x + (((k : ℤ) + 1 : ℤ) : ℝ) * n = (x + ((k : ℤ) : ℝ) * n) + n := by push_cast; ring
    rw [this, traversal_add_nat, ih]
  | pred k ih =>
    have : x + ((-(k : ℤ) : ℤ) : ℝ) * n = (x + ((-(k : ℤ) - 1 : ℤ) : ℝ) * n) + n := by
      push_cast; ring
    rw [this, traversal_add_nat] at ih
    exact ih

/-- a lift with `φ (x + n) = φ x + a` satisfies `φ (x + m n) = φ x + m a`. -/
theorem u11h_lift_add_int {φ : ℝ → ℝ} {a : ℝ} (hper : ∀ x, φ (x + n) = φ x + a) (x : ℝ) (m : ℤ) :
    φ (x + m * n) = φ x + m * a := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have : x + (((k : ℤ) + 1 : ℤ) : ℝ) * n = (x + ((k : ℤ) : ℝ) * n) + n := by push_cast; ring
    rw [this, hper, ih]; push_cast; ring
  | pred k ih =>
    have h1 : x + ((-(k : ℤ) : ℤ) : ℝ) * n = (x + ((-(k : ℤ) - 1 : ℤ) : ℝ) * n) + n := by
      push_cast; ring
    rw [h1, hper] at ih
    have : φ (x + ((-(k : ℤ) - 1 : ℤ) : ℝ) * n) = φ x + ((-(k : ℤ) : ℤ) : ℝ) * a - a := by linarith
    rw [this]; push_cast; ring

/-- surjectivity of a continuous map with `φ (x + n) = φ x + a`, `a > 0` (IVT). -/
theorem u11h_surj_of_period {φ : ℝ → ℝ} (hc : Continuous φ) {a : ℝ} (ha : 0 < a)
    (hper : ∀ x, φ (x + n) = φ x + a) : Function.Surjective φ := by
  intro y
  set m : ℤ := ⌊(y - φ 0) / a⌋ with hm
  have h1 : (m : ℝ) ≤ (y - φ 0) / a := Int.floor_le _
  have h2 : (y - φ 0) / a < m + 1 := Int.lt_floor_add_one _
  have hlo : φ ((m : ℝ) * n) ≤ y := by
    have := u11h_lift_add_int hper 0 m
    rw [zero_add] at this; rw [this]
    have := (le_div_iff₀ ha).mp h1; linarith
  have hhi : y ≤ φ (((m + 1 : ℤ) : ℝ) * n) := by
    have := u11h_lift_add_int hper 0 (m + 1)
    rw [zero_add] at this; rw [this]
    have := (div_lt_iff₀ ha).mp h2; push_cast; linarith
  have hab : (m : ℝ) * n ≤ ((m + 1 : ℤ) : ℝ) * n := by
    push_cast; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc hab hc.continuousOn ⟨hlo, hhi⟩
  exact ⟨x, hx⟩

/-- Packaging of a positive boundary lift: a sign `ε = ±1` with `φ (x + n) = φ x + ε n'`,
injectivity and surjectivity. -/
theorem u11h_lift_facts [NeZero n] {n' : ℕ} [NeZero n'] (hn' : 3 ≤ n') (P : LabelledTuple n)
    (P' : LabelledTuple n') (s s' : Side) {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ (∀ x, φ (x + n) = φ x + ε * n') ∧
      Function.Injective φ ∧ Function.Surjective φ := by
  have hn'0 : (0 : ℝ) < n' := by exact_mod_cast (show 0 < n' by omega)
  by_cases h : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
  · obtain ⟨hmono, hper⟩ := hφ.same h
    refine ⟨1, Or.inl rfl, fun x => by rw [hper, one_mul], hmono.injective, ?_⟩
    exact u11h_surj_of_period hφ.continuous hn'0 hper
  · obtain ⟨hanti, hper⟩ := hφ.opposite h
    refine ⟨-1, Or.inr rfl, fun x => by rw [hper]; ring, hanti.injective, ?_⟩
    have hneg : ∀ x, (fun t => -φ t) (x + n) = (fun t => -φ t) x + n' := fun x => by
      simp only; rw [hper]; ring
    have hs := u11h_surj_of_period hφ.continuous.neg hn'0 hneg
    intro y
    obtain ⟨x, hx⟩ := hs (-y)
    exact ⟨x, by simpa using congrArg Neg.neg hx⟩

/-- the boundary lift respects the traversal identifications. -/
theorem u11h_traversal_congr [NeZero n] {n' : ℕ} (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Embedded P) (P' : LabelledTuple n') {φ : ℝ → ℝ} {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hper : ∀ x, φ (x + n) = φ x + ε * n') {x y : ℝ} (hxy : traversal P x = traversal P y) :
    traversal P' (φ x) = traversal P' (φ y) := by
  obtain ⟨m, hm⟩ := hP.traversal_injective hn hxy
  rcases hε with rfl | rfl
  · have h1 : φ y = φ x + m * n' := by rw [hm, u11h_lift_add_int hper x m]; ring
    rw [h1, u11h_traversal_add_int]
  · have h1 : φ y = φ x + ((-m : ℤ) : ℝ) * n' := by
      rw [hm, u11h_lift_add_int hper x m]; push_cast; ring
    rw [h1, u11h_traversal_add_int]

/-- and conversely (injectivity of the induced circle map). -/
theorem u11h_traversal_congr_inv [NeZero n] {n' : ℕ} [NeZero n'] (hn' : 3 ≤ n') (P : LabelledTuple n)
    {P' : LabelledTuple n'} (hP' : Embedded P') {φ : ℝ → ℝ} {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hper : ∀ x, φ (x + n) = φ x + ε * n') (hinj : Function.Injective φ) {x y : ℝ}
    (hxy : traversal P' (φ x) = traversal P' (φ y)) : traversal P x = traversal P y := by
  obtain ⟨m, hm⟩ := hP'.traversal_injective hn' hxy
  rcases hε with rfl | rfl
  · have h1 : φ y = φ (x + m * n) := by rw [u11h_lift_add_int hper x m, hm]; ring
    rw [hinj h1, u11h_traversal_add_int]
  · have h1 : φ y = φ (x + ((-m : ℤ) : ℝ) * n) := by
      rw [u11h_lift_add_int hper x (-m), hm]; push_cast; ring
    rw [hinj h1, u11h_traversal_add_int]

/-- the traversal image is the polygon image. -/
theorem u11h_range_traversal [NeZero n] (P : LabelledTuple n) : range (traversal P) = polygonImage P := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine mem_iUnion.mpr ⟨((⌊x⌋ : ℤ) : ZMod n), Int.fract x, Int.fract_nonneg x, (Int.fract_lt_one x).le, rfl⟩
  · intro hz
    obtain ⟨i, t, ht0, ht1, rfl⟩ := mem_iUnion.mp hz
    refine ⟨((i.val : ℕ) : ℝ) + t, ?_⟩
    have := ea_traversal_eq_on_Icc P (i.val : ℤ) (y := ((i.val : ℕ) : ℝ) + t) (by push_cast; linarith)
      (by push_cast; linarith)
    rw [this]
    simp [edgePoint]

/-- every traversal point is reached from `[0, n]`. -/
theorem u11h_exists_reduce [NeZero n] (P : LabelledTuple n) (x : ℝ) :
    ∃ t ∈ Icc (0 : ℝ) n, traversal P t = traversal P x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set m : ℤ := ⌊x / n⌋ with hm
  refine ⟨x + (-m : ℤ) * n, ⟨?_, ?_⟩, u11h_traversal_add_int P x (-m)⟩
  · have := Int.floor_le (x / n)
    have := (le_div_iff₀ hn0).mp this
    push_cast; linarith
  · have := Int.lt_floor_add_one (x / n)
    have := (div_lt_iff₀ hn0).mp this
    push_cast; linarith

/-- continuity, image and injectivity of a set homeomorphism. -/
theorem u11h_isHomeoOnto_cont_inj {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} (hf : IsHomeoOnto S S' f) :
    ContinuousOn f S ∧ MapsTo f S S' ∧ InjOn f S := by
  obtain ⟨e, he⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : domRestrict S f = fun z => (e z : β) := funext fun z => (he z).symm
    rw [this]; exact continuous_subtype_val.comp e.continuous
  · intro z hz; rw [← he ⟨z, hz⟩]; exact (e ⟨z, hz⟩).2
  · intro z hz w hw hzw
    have : e ⟨z, hz⟩ = e ⟨w, hw⟩ := Subtype.ext (by rw [he, he]; exact hzw)
    exact congrArg Subtype.val (e.injective this)

/-- The traversal parametrisation of the frontier through a disc parametrisation `f`:
`q x = f ↑(traversal P x)` is continuous, lands in the frontier, covers it, and identifies exactly
the traversal identifications. -/
theorem u11h_param_facts [NeZero n] (P : LabelledTuple n) {S : Set Sphere}
    (hCS : sphereCircle P ⊆ S) {D : Set Plane} {f : Sphere → Plane} (hf : IsHomeoOnto S D f)
    (hB : f '' sphereCircle P = frontier D) :
    Continuous (fun x : ℝ => f ((traversal P x : Plane) : Sphere)) ∧
      (∀ x : ℝ, f ((traversal P x : Plane) : Sphere) ∈ frontier D) ∧
      (∀ y ∈ frontier D, ∃ x : ℝ, f ((traversal P x : Plane) : Sphere) = y) ∧
      (∀ x y : ℝ, f ((traversal P x : Plane) : Sphere) = f ((traversal P y : Plane) : Sphere) ↔
        traversal P x = traversal P y) := by
  obtain ⟨hfc, -, hfi⟩ := u11h_isHomeoOnto_cont_inj hf
  have hcirc : ∀ x : ℝ, ((traversal P x : Plane) : Sphere) ∈ sphereCircle P := fun x =>
    ⟨traversal P x, (u11h_range_traversal P) ▸ mem_range_self x, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hfc.comp_continuous (continuous_coe.comp (continuous_traversal P)) fun x => hCS (hcirc x)
  · intro x; rw [← hB]; exact ⟨_, hcirc x, rfl⟩
  · intro y hy
    rw [← hB] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨w, hw, rfl⟩ := hz
    rw [← u11h_range_traversal P] at hw
    obtain ⟨x, rfl⟩ := hw
    exact ⟨x, rfl⟩
  · intro x y
    refine ⟨fun h => ?_, fun h => by rw [h]⟩
    have := hfi (hCS (hcirc x)) (hCS (hcirc y)) h
    exact coe_eq_coe.mp this

open Classical Topology in
/-- Abstract form of `U11_boundary_homeo_of_lift`: the closed regions are replaced by any sets
`S ⊇ sphereCircle P`, `S' ⊇ sphereCircle P'`. -/
theorem u11h_boundary_homeo_aux [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {S S' : Set Sphere} (hCS : sphereCircle P ⊆ S) (hCS' : sphereCircle P' ⊆ S')
    {D D' : Set Plane} {f f' : Sphere → Plane} (hD : Link.IsDisc D)
    (hf : IsHomeoOnto S D f) (hf' : IsHomeoOnto S' D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    ∃ β : Plane → Plane, IsHomeoOnto (frontier D) (frontier D') β ∧
      ∀ x : ℝ, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere) := by
  obtain ⟨ε, hε, hper, hinj, hsurj⟩ := u11h_lift_facts hn' P P' s s' hφ
  obtain ⟨hqc, hqf, hqs, hqi⟩ := u11h_param_facts P hCS hf hB
  obtain ⟨hqc', hqf', hqs', hqi'⟩ := u11h_param_facts P' hCS' hf' hB'
  set q : ℝ → Plane := fun x => f ((traversal P x : Plane) : Sphere) with hq
  set q' : ℝ → Plane := fun x => f' ((traversal P' x : Plane) : Sphere) with hq'
  -- the induced map on the frontier
  let β₀ : frontier D → frontier D' := fun y => ⟨q' (φ (choose (hqs y.1 y.2))), hqf' _⟩
  have key : ∀ x : ℝ, β₀ ⟨q x, hqf x⟩ = ⟨q' (φ x), hqf' _⟩ := by
    intro x
    apply Subtype.ext
    show q' (φ (choose (hqs (q x) (hqf x)))) = q' (φ x)
    have h1 : q (choose (hqs (q x) (hqf x))) = q x := choose_spec (hqs (q x) (hqf x))
    have h2 := (hqi _ _).mp h1
    show f' _ = f' _
    rw [u11h_traversal_congr hn hP P' hε hper h2]
  -- continuity via the quotient map from `[0, n]`
  have : CompactSpace (Icc (0 : ℝ) n) := isCompact_iff_compactSpace.mp isCompact_Icc
  let Q : Icc (0 : ℝ) n → frontier D := fun t => ⟨q t.1, hqf t.1⟩
  have hQc : Continuous Q := (hqc.comp continuous_subtype_val).subtype_mk _
  have hQs : Function.Surjective Q := by
    intro y
    obtain ⟨x, hx⟩ := hqs y.1 y.2
    obtain ⟨t, ht, htx⟩ := u11h_exists_reduce P x
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    show q t = y.1
    rw [← hx]; show f _ = f _; rw [htx]
  have hQq : IsQuotientMap Q := hQc.isClosedMap.isQuotientMap hQc hQs
  have hβc : Continuous β₀ := by
    rw [hQq.continuous_iff]
    have : β₀ ∘ Q = fun t => ⟨q' (φ t.1), hqf' _⟩ := funext fun t => key t.1
    rw [this]
    exact ((hqc'.comp hφ.continuous).comp continuous_subtype_val).subtype_mk _
  have hβbij : Function.Bijective β₀ := by
    constructor
    · intro y₁ y₂ h
      obtain ⟨x₁, hx₁⟩ := hqs y₁.1 y₁.2
      obtain ⟨x₂, hx₂⟩ := hqs y₂.1 y₂.2
      have e₁ : y₁ = ⟨q x₁, hqf x₁⟩ := Subtype.ext hx₁.symm
      have e₂ : y₂ = ⟨q x₂, hqf x₂⟩ := Subtype.ext hx₂.symm
      rw [e₁, e₂, key, key] at h
      have h3 : q' (φ x₁) = q' (φ x₂) := congrArg Subtype.val h
      have h4 := (hqi' _ _).mp h3
      have h5 := u11h_traversal_congr_inv hn' P hP' hε hper hinj h4
      rw [e₁, e₂]
      exact Subtype.ext ((hqi _ _).mpr h5)
    · intro y'
      obtain ⟨x', hx'⟩ := hqs' y'.1 y'.2
      obtain ⟨x, rfl⟩ := hsurj x'
      exact ⟨⟨q x, hqf x⟩, by rw [key]; exact Subtype.ext hx'⟩
  have : CompactSpace (frontier D) := isCompact_iff_compactSpace.mp
    (hD.2.1.of_isClosed_subset isClosed_frontier hD.2.1.isClosed.frontier_subset)
  let E : frontier D ≃ₜ frontier D' :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective β₀ hβbij) hβc
  refine ⟨fun y => if h : y ∈ frontier D then (β₀ ⟨y, h⟩ : Plane) else 0, ⟨E, ?_⟩, ?_⟩
  · intro z; simp only [z.2, ↓reduceDIte]; rfl
  · intro x
    simp only [hqf x, ↓reduceDIte]
    have := congrArg Subtype.val (key x)
    exact this

/-- 57b for either side (consumes `U7_pl_discs_inner` / `U8_pl_discs_outer`). -/
theorem u11h_pl_disc [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (L : ℝ)
    (hL : InsideModel L P) (s : Side) :
    IsPLDiscSphere L (closure (regionOf P s)) (sphereCircle P) := by
  cases s with
  | inner => exact U7_pl_discs_inner hn P hP L hL
  | outer => exact U8_pl_discs_outer hn P hP L hL

/-- The circle lies in the closure of each region (the `B ⊆ S` clause of 57b, via
`U4_exists_insideModel`). -/
theorem u11h_circle_subset_closure [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (s : Side) : sphereCircle P ⊆ closure (regionOf P s) := by
  obtain ⟨L, -, hL⟩ := U4_exists_insideModel P
  obtain ⟨D, f, -, h, -⟩ := u11h_pl_disc hn P hP L hL s
  exact h

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
  exact u11h_boundary_homeo_aux hn P hP hn' P' hP' s s' (u11h_circle_subset_closure hn P hP s)
    (u11h_circle_subset_closure hn' P' hP' s') hD hf hf' hB hB' hφ

/-- U11 (57d, sm-3:433-434 / 537-542): a continuous positive boundary map extends to a topological
disc map `F = Φ'⁻¹ ∘ A ∘ Φ` (the positivity hypothesis is kept as printed and unused, FR-TD-5). -/
theorem U11_top_extension [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (hn' : 3 ≤ n') (hP' : Embedded P')
    (s s' : Side) (φ : ℝ → ℝ) (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    ∃ F : Sphere → Sphere,
      IsHomeoOnto (closure (regionOf P s)) (closure (regionOf P' s')) F ∧
      ∀ x : ℝ, F ((traversal P x : Plane) : Sphere) = ((traversal P' (φ x) : Plane) : Sphere) := by
  classical
  obtain ⟨L, -, hL⟩ := U4_exists_insideModel P
  obtain ⟨L', -, hL'⟩ := U4_exists_insideModel P'
  obtain ⟨D, f, hD, -, hf, hB, -⟩ := u11h_pl_disc hn P hP L hL s
  obtain ⟨D', f', hD', hCS', hf', hB', -⟩ := u11h_pl_disc hn' P' hP' L' hL' s'
  obtain ⟨β, hβ, hβφ⟩ := U11_boundary_homeo_of_lift hn P hP hn' P' hP' s s' hD hD' hf hf' hB hB' hφ
  obtain ⟨A, hA, hAβ⟩ := U11_radial_extension hD hD' hβ
  obtain ⟨e, he⟩ := hf
  obtain ⟨e', he'⟩ := hf'
  obtain ⟨eA, heA⟩ := hA
  let finv' : Plane → Sphere := fun y => if h : y ∈ D' then (e'.symm ⟨y, h⟩ : Sphere) else ∞
  refine ⟨fun z => finv' (A (f z)), ⟨e.trans (eA.trans e'.symm), ?_⟩, ?_⟩
  · intro z
    show (e'.symm (eA (e z)) : Sphere) = finv' (A (f z))
    have h1 : (eA (e z) : Plane) = A (f z) := by rw [heA, he]
    have h2 : A (f z) ∈ D' := h1 ▸ (eA (e z)).2
    simp only [finv', h2, ↓reduceDIte]
    have h3 : (⟨A (f z), h2⟩ : D') = eA (e z) := Subtype.ext h1.symm
    rw [h3]
  · intro x
    have hz : ((traversal P x : Plane) : Sphere) ∈ sphereCircle P :=
      ⟨_, (u11h_range_traversal P) ▸ mem_range_self x, rfl⟩
    have hfz : f ((traversal P x : Plane) : Sphere) ∈ frontier D := hB ▸ ⟨_, hz, rfl⟩
    show finv' (A (f _)) = _
    rw [hAβ _ hfz, hβφ x]
    have hz' : ((traversal P' (φ x) : Plane) : Sphere) ∈ closure (regionOf P' s') :=
      hCS' ⟨_, (u11h_range_traversal P') ▸ mem_range_self (φ x), rfl⟩
    have hmem : f' ((traversal P' (φ x) : Plane) : Sphere) ∈ D' := by
      rw [← he' ⟨_, hz'⟩]; exact (e' ⟨_, hz'⟩).2
    simp only [finv', hmem, ↓reduceDIte]
    have : (⟨f' ((traversal P' (φ x) : Plane) : Sphere), hmem⟩ : D') = e' ⟨_, hz'⟩ :=
      Subtype.ext (he' ⟨_, hz'⟩).symm
    rw [this, e'.symm_apply_apply]
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
